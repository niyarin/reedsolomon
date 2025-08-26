#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <stdio.h>

static uint8_t gf_exp_table[512];
static uint8_t gf_log_table[256];
// x^8+x^4+x^3+x^2+1
#define GF_PRIMITIVE 0x11d
void gf_init() {
    int x = 1;
    for (int i = 0; i < 255; i++) {
        gf_exp_table[i] = (uint8_t)x;
        gf_log_table[x] = (uint8_t)i;
        x <<= 1;
        if (x & 0x100) {
            x ^= GF_PRIMITIVE;
        }
    }

    for (int i = 255; i < 512; i++) {
        gf_exp_table[i] = gf_exp_table[i - 255];
    }
    gf_log_table[0] = 0;
}

static uint8_t gf_mul(uint8_t a, uint8_t b) {
    if (a == 0 || b == 0) {
        return 0;
    }
    return gf_exp_table[gf_log_table[a] + gf_log_table[b]];
}

static uint8_t gf_alpha_pow(uint8_t x) {
    int m = x % 255;
    return gf_exp_table[m];
}

static uint8_t gf_pow(uint8_t a, uint8_t n) {
    if (n == 0) {
        return 1;
    }
    if (a == 0) {
        return 0;
    }

    int r = (gf_log_table[a] * n) % 255;
    if (r < 0) {
        r += 255;
    }
    return gf_exp_table[r];
}

static uint8_t gf_div(uint8_t a, uint8_t b) {
    if (!a) {
        return 0;
    }

    if (!b) {
        // error
        return 0;
    }

    int16_t diff = gf_log_table[a] - gf_log_table[b];
    if (diff < 0) {
        diff += 255;
    }
    return gf_exp_table[diff];
}

static uint8_t gf_poly_eval_r(const uint8_t *coeffs1, uint16_t len1,
                              const uint8_t *coeffs2, uint16_t len2,
                              uint8_t x) {

    // calculate coef1[0] + coef1[1] * x + coef1[2] * x^2 + ... coef1[k] * x^k +
    // coef2[0] * k^(k+l) + coef2[1] * k^(k+l+1) ... coef2[n] * k^(k+n)
    uint8_t y = coeffs1[len1 - 1];
    for (int16_t i = len1 - 2; i >= 0; i--) {
        y = gf_mul(y, x) ^ coeffs1[i];
    }
    for (int16_t i = len2 - 1; i >= 0; i--) {
        y = gf_mul(y, x) ^ coeffs2[i];
    }
    return y;
}

static uint8_t gf_poly_eval(const uint8_t *coeffs1, size_t len1,
                            const uint8_t *coeffs2, size_t len2, uint8_t x) {

    // calculate coef1[0] + coef1[1] * x + coef1[2] * x^2 + ... coef1[k] * x^k +
    // coef2[0] * k^(k+l) + coef2[1] * k^(k+l+1) ... coef2[n] * k^(k+n)
    uint8_t y = coeffs1[0];
    for (size_t i = 1; i < len1; i++) {
        y = gf_mul(y, x) ^ coeffs1[i];
    }
    for (size_t i = 0; i < len2; i++) {
        y = gf_mul(y, x) ^ coeffs2[i];
    }
    return y;
}

// ENCODER

void calc_generator_polynomial(uint8_t *poly, uint8_t nsym) {
    poly[0] = 1;
    uint8_t poly_len = 1;
    for (int i = 0; i < nsym; i++) {
        uint8_t root = gf_pow(2, i);
        poly[poly_len] = gf_mul(poly[poly_len - 1], root);
        for (int j = poly_len - 1; j > 0; j--) {
            poly[j] = gf_mul(poly[j - 1], root) ^ poly[j];
        }
        poly_len++;
    }
}

void encode_rs(const uint8_t *message, uint8_t n_msg, uint8_t *parity,
               uint8_t n_parity, const uint8_t *poly) {
    for (int i = 0; i < n_parity; i++) {
        parity[i] = 0;
    }

    for (int i = 0; i < n_msg; i++) {
        uint8_t feedback = message[i] ^ parity[0];
        if (feedback != 0) {
            for (int j = 0; j < n_parity - 1; j++) {
                parity[j] = parity[j + 1] ^ gf_mul(feedback, poly[j + 1]);
            }
        }
        parity[n_parity - 1] = gf_mul(feedback, poly[n_parity]);
    }
}

// DECODER

void compute_syndromes(const uint8_t *message, uint8_t n_message,
                       const uint8_t *parity, uint8_t n_parity,
                       uint8_t *syndrome) {
    for (int i = 0; i < n_parity; i++) {
        uint8_t a_i = gf_alpha_pow(i);
        syndrome[i] = gf_poly_eval(message, n_message, parity, n_parity, a_i);
    }
}

uint8_t berlekamp_massey(const uint8_t *syndrome, uint16_t n_syndrome,
                         uint8_t *sigma, uint8_t *B) {
    for (int i = 1; i < n_syndrome; i++) {
        B[i] = 0;
        sigma[i] = 0;
    }
    sigma[0] = 1;
    B[0] = 1;
    uint8_t b = 1;
    uint8_t L = 0;
    uint16_t m = 1;

    for (int i = 0; i < n_syndrome; i++) {
        uint8_t delta = syndrome[i];
        for (int j = 1; j <= L; j++) {
            delta ^= gf_mul(sigma[j], syndrome[i - j]);
        }

        if (delta == 0) {
            m++;
        } else {
            if (2 * L <= n_syndrome) {
                for (int16_t j = n_syndrome - m + 1; j <= n_syndrome; j++) {
                    B[j] = sigma[j];
                }
            }
            uint8_t factor = gf_div(delta, b);
            for (int16_t j = n_syndrome - m; j >= 0; j--) {
                if (B[j]) {
                    sigma[j + m] ^= gf_mul(factor, B[j]);
                }
                if (2 * L <= n_syndrome) {
                    B[j] = sigma[j];
                }
            }

            if (2 * L <= n_syndrome) {
                L = i + 1 - L;
                b = delta;
                m = 1;
            } else {
                m++;
            }
        }
    }
    return L + 1;
}

uint8_t chien_search(const uint8_t *lambda, uint8_t n_lambda, uint8_t n_code,
                     uint8_t *errs) {
    uint32_t n_err = 0;
    for (int i = 0; i < n_code; i++) {
        uint8_t xinv = gf_exp_table[i];
        if (gf_poly_eval(lambda, n_lambda + 1, NULL, 0, xinv) == 0) {
            errs[n_err] = n_code - i - 1;
            n_err++;
        } else {
        }
    }
    return n_err;
}

void calc_omega(const uint8_t *sigma, uint8_t n_sigma, const uint8_t *s,
                uint8_t s_len, uint8_t *omega) {
    for (int i = 0; i < s_len + n_sigma; i++) {
        omega[i] = 0;
    }
    for (int i = 0; i < s_len; i++) {
        if (s[i]) {
            for (int j = 0; j < n_sigma; j++) {
                if (i + j + 1 <= s_len) {
                    omega[i + j + 1] ^= gf_mul(s[i], sigma[j]);
                }
            }
        }
    }
}

void correct(uint8_t *message, uint8_t n_message, uint8_t *parity,
             uint8_t n_parity, const uint8_t *err_pos, uint8_t err_count,
             const uint8_t *omega, uint8_t n_omega) {
    uint8_t n_code = n_parity + n_message;
    for (int i = 0; i < err_count; i++) {
        uint8_t pos = err_pos[i];
        uint8_t xpos = n_code - 1 - pos;
        uint8_t xi = gf_alpha_pow(xpos);
        uint8_t inv_xi = gf_exp_table[255 - gf_log_table[xi]];
        uint8_t nume = gf_poly_eval_r(omega, n_omega, NULL, 0, inv_xi);
        nume = gf_mul(xi, nume);

        uint8_t sigma_prime = 1;
        for (int j = 0; j < err_count; j++) {
            if (i != j) {
                uint8_t posj = err_pos[j];
                uint8_t xposj = n_code - posj - 1;
                uint8_t xj = gf_alpha_pow(xposj);

                sigma_prime = gf_mul(sigma_prime, 1 ^ gf_mul(inv_xi, xj));
            }
        }

        uint8_t mag = gf_div(nume, sigma_prime);
        if (pos < n_message) {
            message[pos] ^= mag;
        } else if (pos - n_message < n_parity) {
            parity[pos - n_message] ^= mag;
        }
    }
}

static uint8_t is_syndrome_all_zero_p(const uint8_t *syndrome,
                                      uint8_t n_syndrome) {
    for (int i = 0; i < n_syndrome; i++) {
        if (syndrome[i] != 0) {
            return 0;
        }
    }
    return 1;
}

int decode_rs(uint8_t *message, uint8_t n_message, uint8_t *parity,
              uint8_t n_parity) {
    // return 1 if has error else 0
    uint8_t syndrome[n_parity];
    compute_syndromes(message, n_message, parity, n_parity, syndrome);

    if (is_syndrome_all_zero_p(syndrome, n_parity)) {
        return 0;
    }

    uint8_t cb[n_parity], sigma[n_parity];
    uint8_t omega[n_parity];
    uint8_t n_sigma = berlekamp_massey(syndrome, n_parity, sigma, cb);

    calc_omega(sigma, n_sigma, syndrome, n_parity, omega);

    uint8_t errs[n_parity];
    uint8_t n_errs = chien_search(sigma, n_sigma, n_message + n_parity, errs);
    correct(message, n_message, parity, n_parity, errs, n_errs, omega,
            n_parity + 1);
    return 1;
}
