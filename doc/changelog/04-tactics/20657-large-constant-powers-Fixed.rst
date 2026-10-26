- **Fixed:**
  Excessive normalization and proof-checking costs for large constant powers in
  :tacn:`lia` and the integer Micromega tactics. Constant powers are folded
  during reification, large power-of-two coefficients are quoted compactly,
  and integer normalization uses stack-safe subtraction. The certificate
  format, verified checker, and arithmetic reasoning rules are unchanged
  (fixes `#20657 <https://github.com/rocq-prover/rocq/issues/20657>`_).
