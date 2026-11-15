/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Automorphism
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Heisenberg

/-!
# The diagonal power map is not peripheral in rank at least three

Let `F` be a free pro-`p` group of rank `r` with basis `x_0, …, x_{r-1}` and cusp
`z = (x_0 ⋯ x_{r-1})⁻¹`. For a unit `u ∈ ℤ_pˣ`, the *diagonal power map* is the continuous
automorphism `x_i ↦ x_i ^ u` of `F`, where `^ u` is the `p`-adic power; it exists by the
automorphism criterion for conjugated unit powers
(`TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow_const`). It carries every basis
element to a conjugate of its `u`-th power, trivially. This file shows that for `r ≥ 3` and
`u ≠ 1` it does not do so on the cusp: the peripheral condition on the basis alone does not imply
it on the cusp.

The obstruction is the value `x_0 ^ u ⋯ x_{r-1} ^ u` of the diagonal power map on the product
`x_0 ⋯ x_{r-1}`, which is not conjugate to any `p`-adic power of `x_0 ⋯ x_{r-1}` once
`u ≠ 0, 1`. To see this, map `F` to the Heisenberg group over `ℤ_p` by
`x_0 ↦ a = (1, 0, 0)`, `x_1 ↦ b = (0, 1, 0)`, `x_2 ↦ (a b)⁻¹` and `x_i ↦ 1` for `i ≥ 3`. This
kills `x_0 ⋯ x_{r-1}`, hence all its powers and their conjugates, but sends
`x_0 ^ u ⋯ x_{r-1} ^ u` to `a ^ u b ^ u ((a b)⁻¹) ^ u = (0, 0, u choose 2)`, by the power formula
`TauCeti.HeisenbergGroup.padicPow_eq`, and `u choose 2 = u (u - 1) / 2` is nonzero for
`u ≠ 0, 1`. This adapts the Heisenberg detection argument of
`TauCeti.Peripheral.not_isPeripheralAut_of_apply_basis_eq_inv` (in `Peripheral/Reflection.lean`)
from the Heisenberg group over `𝔽_p` to the one over `ℤ_p`, so that it also detects
`u ≡ 1 mod p`.

In rank two the analogous statement is false: at `u = -1` the diagonal power map is the inversion
of `TauCeti.Peripheral.exists_inversion_two`, which is peripheral.

## Main results

* `TauCeti.Peripheral.not_isConj_diagonalPow`: for `r ≥ 3` and `u ≠ 0, 1`, the product
  `x_0 ^ u ⋯ x_{r-1} ^ u` is not conjugate to any `p`-adic power of `x_0 ⋯ x_{r-1}`.
* `TauCeti.Peripheral.not_isPeripheralAut_of_apply_basis_eq_padicPow`: for `r ≥ 3` and a unit
  `u ≠ 1`, an automorphism with `x_i ↦ x_i ^ u` for every `i` is peripheral of no exponent.
* `TauCeti.Peripheral.exists_diagonalPow_not_isPeripheralAut`: for `r ≥ 3` and a unit `u ≠ 1`,
  the diagonal power map exists and is peripheral of no exponent.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for peripheral automorphisms of free pro-`p` groups and the role of the cusp.
-/

public section

namespace TauCeti

namespace Peripheral

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

/-- **The diagonal power is not conjugate to a power of the product.** For a free pro-`p` group
of rank at least three and `u ∈ ℤ_p` other than `0` and `1`, the product
`x_0 ^ u ⋯ x_{r-1} ^ u` of the `u`-th powers of the basis is not conjugate to any `p`-adic power
`(x_0 ⋯ x_{r-1}) ^ v`. -/
theorem not_isConj_diagonalPow {n : ℕ} (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin (n + 3)))
    {u : ℤ_[p]} (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) (v : ℤ_[p]) :
    ¬ IsConj (hF.padicPow (List.ofFn (basis e)).prod v)
      (List.ofFn fun i ↦ hF.padicPow (basis e i) u).prod := by
  intro hconj
  -- Map `F` to the Heisenberg group over `ℤ_p`, sending `x_0, x_1, x_2` to `a`, `b`, `(a b)⁻¹`,
  -- where `a` and `b` do not commute, and the remaining basis elements to `1`.
  have hH := HeisenbergGroup.isProP_padicInt p
  let a : HeisenbergGroup ℤ_[p] := ⟨1, 0, 0⟩
  let b : HeisenbergGroup ℤ_[p] := ⟨0, 1, 0⟩
  let w : Fin (n + 3) → HeisenbergGroup ℤ_[p] :=
    Fin.cons a (Fin.cons b (Fin.cons (a * b)⁻¹ 1))
  let f : F →ₜ* HeisenbergGroup ℤ_[p] :=
    (freeProP.lift hH w).comp (e : F →ₜ* freeProP p (Fin (n + 3)))
  have hf : ∀ i, f (basis e i) = w i := fun i ↦ by
    simp [f, ContinuousMonoidHom.comp_toFun]
  have hfpow : ∀ i, f (hF.padicPow (basis e i) u) = hH.padicPow (w i) u := fun i ↦ by
    rw [← hf]
    exact hF.map_padicPow hH (f : F →* HeisenbergGroup ℤ_[p]) f.continuous _ _
  -- The product of the basis maps to `a * (b * (a b)⁻¹) = 1`, so all its powers and their
  -- conjugates do too.
  have hprod : f (List.ofFn (basis e)).prod = 1 := by
    rw [map_list_prod, List.map_ofFn, Function.comp_def]
    simp [hf, w, List.ofFn_succ]
  have hmap := (f : F →* HeisenbergGroup ℤ_[p]).map_isConj hconj
  have hpow : f (hF.padicPow (List.ofFn (basis e)).prod v) =
      hH.padicPow (f (List.ofFn (basis e)).prod) v :=
    hF.map_padicPow hH (f : F →* HeisenbergGroup ℤ_[p]) f.continuous _ _
  rw [MonoidHom.coe_ofClass, hpow, hprod, hH.one_padicPow, isConj_one_right, map_list_prod,
    List.map_ofFn, Function.comp_def] at hmap
  simp only [hfpow, w, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Pi.one_apply,
    hH.one_padicPow, List.ofFn_const, List.prod_cons, List.prod_replicate, one_pow,
    mul_one] at hmap
  -- The `z`-coordinate of `a ^ u * b ^ u * ((a b)⁻¹) ^ u` is `u choose 2`, which is nonzero.
  have hz := congrArg HeisenbergGroup.z hmap
  simp [a, b, HeisenbergGroup.padicPow_eq] at hz
  -- `2 * (u choose 2) = u * (u - 1)`, which is nonzero.
  have hchoose := Ring.descPochhammer_eq_factorial_smul_choose u 2
  simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_X,
    Polynomial.smeval_sub, Polynomial.smeval_one, hz, sub_eq_zero, hu₀, hu₁] at hchoose

/-- **The diagonal power map is not peripheral in rank at least three.** For a free pro-`p` group
of rank at least three and a unit `u ≠ 1`, a continuous automorphism sending every basis element
`x_i` to `x_i ^ u` is peripheral of no exponent: it sends the cusp to
`(x_0 ^ u ⋯ x_{r-1} ^ u)⁻¹`, which is not conjugate to any `p`-adic power of the cusp. -/
theorem not_isPeripheralAut_of_apply_basis_eq_padicPow {n : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (n + 3))) {u : ℤ_[p]ˣ} (hu : u ≠ 1) {φ : ContinuousAut F}
    (hφ : ∀ i, φ (basis e i) = hF.padicPow (basis e i) u) (v : ℤ_[p]ˣ) :
    ¬ IsPeripheralAut hF (basis e) v φ := by
  intro hper
  obtain ⟨c, hc⟩ := isConj_iff.mp ((isPeripheralAut_iff hF (basis e) v φ).mp hper).2
  rw [map_cusp, cusp_def, cusp_def, hF.inv_padicPow] at hc
  simp only [Function.comp_def, hφ] at hc
  refine not_isConj_diagonalPow hF e u.ne_zero (Units.val_eq_one.not.mpr hu) v
    (isConj_iff.mpr ⟨c, ?_⟩)
  rw [← inv_inj, ← hc]
  group

/-- **The diagonal power map.** For a free pro-`p` group of rank at least three and a unit
`u ≠ 1`, some continuous automorphism sends every basis element `x_i` to its `u`-th power
`x_i ^ u`, and it is peripheral of no exponent. So an automorphism carrying every basis element
to a conjugate of its `u`-th power need not do so on the cusp. -/
theorem exists_diagonalPow_not_isPeripheralAut {n : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (n + 3))) {u : ℤ_[p]ˣ} (hu : u ≠ 1) :
    ∃ φ : ContinuousAut F, (∀ i, φ (basis e i) = hF.padicPow (basis e i) u) ∧
      ∀ v, ¬ IsPeripheralAut hF (basis e) v φ := by
  obtain ⟨φ, hφ⟩ := hF.exists_continuousAut_apply_eq_conj_padicPow_const e u 1
  have hφ' : ∀ i, φ (basis e i) = hF.padicPow (basis e i) u := fun i ↦ by
    simpa [← basis_apply] using hφ i
  exact ⟨φ, hφ', not_isPeripheralAut_of_apply_basis_eq_padicPow hF e hu hφ'⟩

end Peripheral

end TauCeti
