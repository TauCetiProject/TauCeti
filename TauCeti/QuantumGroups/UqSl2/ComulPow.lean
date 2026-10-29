/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import TauCeti.QuantumGroups.UqSl2.Hopf

/-!
# Coproducts of powers of the root generators of `U_q(sl₂)`

In `UqSl2 q ⊗ UqSl2 q`, the two summands of `ΔE = E ⊗ 1 + K ⊗ E` satisfy
`(K ⊗ E) (E ⊗ 1) = q² (E ⊗ 1) (K ⊗ E)`, and the two summands of `ΔF = F ⊗ K⁻¹ + 1 ⊗ F` satisfy
`(F ⊗ K⁻¹) (1 ⊗ F) = q² (1 ⊗ F) (F ⊗ K⁻¹)`. The `q`-binomial theorem therefore expands the
coproducts of their powers, with the symmetric quantum binomial coefficients `[r choose s]_q`:

* `Δ(E^r) = ∑_(s=0)^r q^(s(r-s)) [r choose s]_q E^s K^(r-s) ⊗ E^(r-s)`;
* `Δ(F^r) = ∑_(s=0)^r q^(s(r-s)) [r choose s]_q F^(r-s) ⊗ F^s K^(-(r-s))`.

These formulas give the action of `E^r` and `F^r` on tensor products of modules.

## Main results

* `TauCeti.UqSl2.comul_e_pow`: the coproduct of `E^r`.
* `TauCeti.UqSl2.comul_f_pow`: the coproduct of `F^r`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section IV.2, for the
  `q`-binomial formula.
* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the coproduct conventions.
-/

public section

open scoped TensorProduct

open Algebra.TensorProduct

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-- The coproduct of a power of the raising generator:
`Δ(E^r) = ∑_(s=0)^r q^(s(r-s)) [r choose s]_q E^s K^(r-s) ⊗ E^(r-s)`. -/
theorem comul_e_pow (r : ℕ) :
    Coalgebra.comul (R := ℂ) (e q ^ r) = ∑ s ∈ Finset.range (r + 1),
      (q ^ (s * (r - s)) * quantumBinomial q r s) •
        ((e q ^ s * k q ^ (r - s)) ⊗ₜ[ℂ] (e q ^ (r - s))) := by
  rw [← comul_apply, map_pow, comul_apply, comul_e,
    add_pow_of_mul_eq_smul_mul (Fact.out : q ≠ 0)]
  · simp [tmul_pow, tmul_mul_tmul]
  · simp [tmul_mul_tmul, k_mul_e, TensorProduct.smul_tmul']

/-- The coproduct of a power of the lowering generator:
`Δ(F^r) = ∑_(s=0)^r q^(s(r-s)) [r choose s]_q F^(r-s) ⊗ F^s K^(-(r-s))`. -/
theorem comul_f_pow (r : ℕ) :
    Coalgebra.comul (R := ℂ) (f q ^ r) = ∑ s ∈ Finset.range (r + 1),
      (q ^ (s * (r - s)) * quantumBinomial q r s) •
        ((f q ^ (r - s)) ⊗ₜ[ℂ] (f q ^ s * kInv q ^ (r - s))) := by
  rw [← comul_apply, map_pow, comul_apply, comul_f, add_comm,
    add_pow_of_mul_eq_smul_mul (Fact.out : q ≠ 0)]
  · simp [tmul_pow, tmul_mul_tmul]
  · simp [tmul_mul_tmul, kInv_mul_f, TensorProduct.tmul_smul]

end TauCeti.UqSl2
