import math
from .ring import find_ntt_prime

LEVELS = (128, 192, 256)


def _q(bits, phi):
    return find_ntt_prime(bits, phi)


THIMZA = {
    128: dict(phi=512, logq=49, ell=4, k=5, omega=19, log_sigma_t=20.0, log_sigma_w=37.0,
              nu_t=37, nu_w=40, nu_c=36, Tmax=1024, logQ=60),
    192: dict(phi=512, logq=49, ell=6, k=7, omega=31, log_sigma_t=20.0, log_sigma_w=37.0,
              nu_t=36, nu_w=40, nu_c=36, Tmax=1024, logQ=64),
    256: dict(phi=512, logq=49, ell=7, k=8, omega=44, log_sigma_t=20.0, log_sigma_w=36.0,
              nu_t=35, nu_w=41, nu_c=35, Tmax=1024, logQ=60),
}

TRACCOON = {
    128: dict(phi=512, logq=49, ell=4, k=5, omega=19, log_sigma_t=20.0, log_sigma_w=37.0,
              nu_t=37, nu_w=40, Tmax=1024, logQ=60),
    192: dict(phi=512, logq=49, ell=6, k=7, omega=31, log_sigma_t=20.0, log_sigma_w=37.0,
              nu_t=36, nu_w=40, Tmax=1024, logQ=64),
    256: dict(phi=512, logq=49, ell=7, k=8, omega=44, log_sigma_t=20.0, log_sigma_w=36.0,
              nu_t=35, nu_w=41, Tmax=1024, logQ=60),
}

RINGTAIL = {
    128: dict(phi=256, logq=48, ell=7, k=8, dbar=48, omega=23, log_sigma_e=math.log2(6.1),
              log_sigma_u=27.2, log_sigma_w=37.3, nu_w=29, nu_t=30, Tmax=1024, logQ=60),
    192: dict(phi=512, logq=46, ell=5, k=6, dbar=42, omega=31, log_sigma_e=math.log2(6.2),
              log_sigma_u=23.5, log_sigma_w=36.4, nu_w=25, nu_t=29, Tmax=1024, logQ=60),
    256: dict(phi=512, logq=48, ell=7, k=8, dbar=48, omega=44, log_sigma_e=math.log2(9.9),
              log_sigma_u=27.8, log_sigma_w=38.6, nu_w=29, nu_t=31, Tmax=1024, logQ=60),
}

TANUKI = {
    128: dict(phi=256, logq=50, ell=9, k=11, rep=15, omega=23, log_sigma_t=5.0,
              log_sigma_w=34.5, nu_t=38, nu_w=38, Tmax=1024, logQ=59),
    192: dict(phi=512, logq=50, ell=6, k=7, rep=15, omega=31, log_sigma_t=10.0,
              log_sigma_w=35.0, nu_t=34, nu_w=38, Tmax=1024, logQ=59),
    256: dict(phi=512, logq=51, ell=7, k=10, rep=17, omega=44, log_sigma_t=15.0,
              log_sigma_w=37.0, nu_t=35, nu_w=40, Tmax=1024, logQ=59),
}

TALONG = {
    128: dict(phi=2048, logq=43, ell=1, k=1, omega=14, log_sigma_1=36.0, log_sigma_2=6.0,
              log_sigma_r=24.2, p1=35, p2=38, Tmax=1024, logQ=60),
    256: dict(phi=4096, logq=43, ell=1, k=1, omega=27, log_sigma_1=36.0, log_sigma_2=6.0,
              log_sigma_r=24.6, p1=36, p2=39, Tmax=1024, logQ=60),
}

CTZ = {
    128: dict(phi=256, logq=50, ell=8, k=8, rep=8, omega=23, log_sigma_t=8.0,
              log_sigma_w=40.0, nu_t=0, nu_w=0, Tmax=5, logQ=64, lsss_blowup=None),
}

DOTT = {
    128: dict(phi=256, logq=44, ell=8, k=9, omega=23, log_sigma_t=6.0, log_sigma_w=32.0,
              nu_t=0, nu_w=0, Tmax=7, logQ=60, com_cols=24),
}

DPN = {
    128: dict(phi=512, logq=27, ell=4, k=4, omega=25, log_sigma_t=3.0, log_sigma_w=15.5,
              nu_t=12, nu_w=13, Tmax=8, logQ=60),
}


def instantiate(logq, phi):
    return _q(logq, phi)


def sigma(logs):
    return 2.0 ** logs


HERMINE = {
    128: dict(phi=512, logq=48, ell=4, k=4, rep=13, omega=19, log_sigma_s=13.0,
              log_sigma_w=36.0, nu_t=37, nu_w=40, nu_wp=32, Tmax=8, Nmax=64, logQ=60),
    192: dict(phi=512, logq=48, ell=6, k=6, rep=20, omega=31, log_sigma_s=13.0,
              log_sigma_w=36.0, nu_t=37, nu_w=40, nu_wp=32, Tmax=8, Nmax=64, logQ=64),
    256: dict(phi=512, logq=48, ell=8, k=7, rep=26, omega=44, log_sigma_s=13.0,
              log_sigma_w=35.0, nu_t=37, nu_w=40, nu_wp=32, Tmax=8, Nmax=64, logQ=64),
}
