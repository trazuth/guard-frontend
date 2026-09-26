(function (global) {
  'use strict';

  function createWorkerSource() {
    return `
      self.onmessage = async function(e) {
        const { challenge, wasmUrl, maxCounter } = e.data;
        const params = challenge.parameters || challenge || {};
        const target = String(challenge.challenge || params.target || '').trim().toLowerCase();
        const cost = Number(params.cost) || 1;
        const actualMemoryCost = Number(params.memoryCost) || 4096;
        const parallelism = Number(params.parallelism) || 2;
        const keyLength = Number(params.keyLength) || 32;
        const salt = String(params.salt || challenge.salt || '').trim();
        const nonce = String(params.nonce || challenge.nonce || '').trim();

        try {
          if (!self.hashwasm || !self.hashwasm.argon2id) {
            importScripts(wasmUrl);
          }
          if (!self.hashwasm || !self.hashwasm.argon2id) {
            throw new Error('Worker load hash-wasm failed');
          }
          const argon2idFn = self.hashwasm.argon2id;

          function hexToBuffer(hex) {
            const bytes = new Uint8Array(hex.length / 2);
            for (let i = 0; i < bytes.length; i++) {
              bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
            }
            return bytes;
          }

          function bufferToHex(buf) {
            return Array.from(new Uint8Array(buf))
              .map(b => b.toString(16).padStart(2, '0'))
              .join('');
          }

          function sha256Pure(ascii) {
            function rr(v, a) { return (v >>> a) | (v << (32 - a)); }
            const mathPow = Math.pow;
            const maxWord = mathPow(2, 32);
            let i, j;
            let result = '';
            const words = [];
            const asciiBitLength = ascii.length * 8;
            const hash = [];
            const k = [];
            let primeCounter = 0;
            const isComposite = {};
            for (let candidate = 2; primeCounter < 64; candidate++) {
              if (!isComposite[candidate]) {
                for (i = 0; i < 312; i += candidate) {
                  isComposite[i] = candidate;
                }
                hash[primeCounter] = (mathPow(candidate, 0.5) * maxWord) | 0;
                k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
              }
            }
            for (i = 0; i < ascii.length; i++) {
              j = ascii.charCodeAt(i);
              words[i >> 2] = (words[i >> 2] || 0) | (j << ((3 - (i % 4)) * 8));
            }
            words[asciiBitLength >> 5] = (words[asciiBitLength >> 5] || 0) | (0x80 << (24 - (asciiBitLength % 32)));
            const totalWords = (((asciiBitLength + 64) >> 9) << 4) + 16;
            for (let idx = 0; idx < totalWords; idx++) {
              if (words[idx] === undefined) words[idx] = 0;
            }
            words[totalWords - 1] = asciiBitLength;

            for (let j = 0; j < words.length; j += 16) {
              const w = words.slice(j, j + 16);
              const oldHash = hash.slice(0, 8);
              for (i = 0; i < 64; i++) {
                let s0, s1;
                if (i >= 16) {
                  const w15 = w[i - 15];
                  const w2 = w[i - 2];
                  s0 = rr(w15, 7) ^ rr(w15, 18) ^ (w15 >>> 3);
                  s1 = rr(w2, 17) ^ rr(w2, 19) ^ (w2 >>> 10);
                  w[i] = (((w[i - 16] + s0) | 0) + ((w[i - 7] + s1) | 0)) | 0;
                }
                const s1_ch = rr(hash[4], 6) ^ rr(hash[4], 11) ^ rr(hash[4], 25);
                const ch = (hash[4] & hash[5]) ^ (~hash[4] & hash[6]);
                const temp1 = (((hash[7] + s1_ch) | 0) + ((ch + k[i]) | 0) + w[i]) | 0;
                const s0_maj = rr(hash[0], 2) ^ rr(hash[0], 13) ^ rr(hash[0], 22);
                const maj = (hash[0] & hash[1]) ^ (hash[0] & hash[2]) ^ (hash[1] & hash[2]);
                const temp2 = (s0_maj + maj) | 0;
                hash[7] = hash[6];
                hash[6] = hash[5];
                hash[5] = hash[4];
                hash[4] = (hash[3] + temp1) | 0;
                hash[3] = hash[2];
                hash[2] = hash[1];
                hash[1] = hash[0];
                hash[0] = (temp1 + temp2) | 0;
              }
              for (i = 0; i < 8; i++) {
                hash[i] = (hash[i] + oldHash[i]) | 0;
              }
            }
            for (i = 0; i < 8; i++) {
              for (j = 3; j >= 0; j--) {
                const b = (hash[i] >> (8 * j)) & 255;
                result += (b < 16 ? '0' : '') + b.toString(16);
              }
            }
            return result;
          }

          async function sha256(str) {
            try {
              if (self.crypto && self.crypto.subtle && typeof self.crypto.subtle.digest === 'function') {
                const enc = new TextEncoder();
                const digest = await self.crypto.subtle.digest('SHA-256', enc.encode(str));
                return bufferToHex(digest);
              }
            } catch (e) {}
            return sha256Pure(str);
          }

          const nonceBuf = hexToBuffer(nonce);
          const saltBuf = hexToBuffer(salt);
          const pwBuf = new Uint8Array(nonceBuf.length + 4);
          pwBuf.set(nonceBuf, 0);
          const dv = new DataView(pwBuf.buffer);

          let foundSolution = null;

          for (let c = 0; c <= maxCounter; c++) {
            dv.setUint32(nonceBuf.length, c, false);

            const derivedKey = await argon2idFn({
              password: pwBuf,
              salt: saltBuf,
              parallelism,
              iterations: cost,
              memorySize: actualMemoryCost,
              hashLength: keyLength,
              outputType: 'hex',
            });

            if (c % 10 === 0) {
              self.postMessage({ type: 'progress', counter: c });
            }

            const currentDigest = (await sha256(salt + ':' + nonce + ':' + c)).toLowerCase();
            if (currentDigest === target) {
              foundSolution = { counter: c, derivedKey };
              self.postMessage({ type: 'progress', counter: c });
              break;
            }
          }

          if (foundSolution) {
            self.postMessage({ type: 'success', solution: foundSolution });
          } else {
            self.postMessage({ type: 'error', message: 'PoW 求解失败：未在预设范围内匹配到 counter' });
          }
        } catch (err) {
          self.postMessage({ type: 'error', message: err.message || String(err) });
        }
      };
    `;
  }

  function solveInWebWorker(challenge, wasmUrl, onProgress) {
    return new Promise((resolve, reject) => {
      if (typeof Worker === 'undefined') {
        return reject(new Error('This browser doesn\'t support web worker'));
      }

      const blob = new Blob([createWorkerSource()], { type: 'application/javascript' });
      const workerUrl = URL.createObjectURL(blob);
      const worker = new Worker(workerUrl);

      worker.onmessage = function (e) {
        const data = e.data;
        if (data.type === 'progress') {
          if (typeof onProgress === 'function') {
            onProgress(data.counter);
          }
        } else if (data.type === 'success') {
          cleanup();
          resolve(data.solution);
        } else if (data.type === 'error') {
          cleanup();
          reject(new Error(data.message));
        }
      };

      worker.onerror = function (err) {
        cleanup();
        reject(new Error('Worker error: ' + (err.message || '')));
      };

      function cleanup() {
        worker.terminate();
        URL.revokeObjectURL(workerUrl);
      }

      worker.postMessage({
        challenge,
        wasmUrl,
        maxCounter: 350,
      });
    });
  }

  async function solvePoW(options = {}) {
    const memoryCost = options.memoryCost || 6388;
    const apiBase123 = 'https://guard.trazuth.com/client/v0.1.0';
    const startTime = performance.now();

    const challengeUrl = `${apiBase123}/api/challenge?memorycost=${encodeURIComponent(memoryCost)}`;
    const challengeRes = await fetch(challengeUrl, {
      method: 'GET',
      headers: { Accept: 'application/json' },
    });

    if (!challengeRes.ok) {
      let errMsg = `HTTP ${challengeRes.status}`;
      try {
        const errJson = await challengeRes.json();
        if (errJson && errJson.message) errMsg += ` (${errJson.message})`;
      } catch (e) {}
      throw new Error(`[Trazuth Guard] pow challenge error: ${errMsg}`);
    }

    const { challenge, challenge_token, wasmUrl } = await challengeRes.json();
    if (!challenge || !challenge.parameters) {
      throw new Error('[Trazuth Guard] challenge structure error');
    }

    let resolvedWasmUrl = options.wasmUrl || wasmUrl;
    if (resolvedWasmUrl.startsWith('/')) {
      resolvedWasmUrl = (apiBase123 || window.location.origin) + resolvedWasmUrl;
    }

    const foundSolution = await solveInWebWorker(challenge, resolvedWasmUrl, options.onProgress);

    const verifyUrl = `${apiBase123}/api/verify`;
    const verifyRes = await fetch(verifyUrl, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        Accept: 'application/json',
      },
      body: JSON.stringify({
        solution: foundSolution,
        challenge,
        challenge_token,
      }),
    });

    if (!verifyRes.ok) {
      let errMsg = `HTTP ${verifyRes.status}`;
      try {
        const errJson = await verifyRes.json();
        if (errJson && errJson.message) errMsg += ` (${errJson.message})`;
      } catch (e) {}
      throw new Error(`[Trazuth Guard] verify answer error: ${errMsg}`);
    }

    const verifyData = await verifyRes.json();
    const tookMs = Math.round(performance.now() - startTime);

    return {
      token: verifyData.token,
      tookMs,
      counter: foundSolution.counter,
    };
  }

  const guardAdapter = {
    solvePoW,
    solveAndVerify: solvePoW,
  };

  global.guardAdapter = guardAdapter;
  global.solveGuardPoW = solvePoW;
})(typeof window !== 'undefined' ? window : this);
