/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic

/-!
# Symbols homogeneous at large frequencies are classical

A symbol `a` of order `m` which is homogeneous of degree `m` at large frequencies,
`a(x, t ξ) = t ^ m a(x, ξ)` for `t ≥ 1` and `‖ξ‖ ≥ R` (`TauCeti.Symbol.IsHomogeneousAbove`), is a
classical symbol with a single homogeneous term (`TauCeti.ClassicalSymbol.ofIsHomogeneousAbove`).
Its principal symbol is the homogeneous extension of the values of `a` on a sphere `‖ξ‖ = R'` with
`R' ≥ R`. More generally, the principal symbol of every classical symbol whose full symbol is
homogeneous above the radius `R` agrees with the full symbol at the nonzero frequencies of norm at
least `R` (`TauCeti.ClassicalSymbol.coefficient_principal_of_isHomogeneousAbove`).

Symbols of this kind arise from constructions that commute with the dilations of the frequency
only away from the origin, where smoothness has to be restored by a cutoff, for instance the
integrals of quasi-homogeneous parameter-dependent symbols along the spectral parameter that give
the complex powers of elliptic operators (`TauCeti.ParameterSymbol.classicalBalakrishnanIntegral`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
-/

public section

noncomputable section

namespace TauCeti

namespace ClassicalSymbol

open Filter HomogeneousSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m R : ℝ}

/-- **The principal symbol of a symbol homogeneous at large frequencies.** If the full symbol of a
classical symbol `a` of order `m` is homogeneous of degree `m` above the radius `R`, its principal
symbol agrees with it at every nonzero frequency of norm at least `R`. -/
theorem coefficient_principal_of_isHomogeneousAbove (a : ClassicalSymbol n V W m)
    (ha : a.toSymbol.IsHomogeneousAbove m R) {x ξ : CoordinateSpace n} (hξ : R ≤ ‖ξ‖)
    (hξ0 : ξ ≠ 0) : a.principal.coefficient (x, ξ) = a.toSymbol.coefficient (x, ξ) := by
  refine tendsto_nhds_unique ((a.tendsto_rpow_neg_smul_coefficient_smul hξ0).comp
    (tendsto_id.prodMk (tendsto_const_nhds (x := (x, ξ))))) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  dsimp only [Function.comp_apply, _root_.id]
  rw [Symbol.isHomogeneousAbove_iff.1 ha x ξ hξ t ht, smul_smul,
    ← Real.rpow_add (zero_lt_one.trans_le ht), neg_add_cancel, Real.rpow_zero, one_smul]

/-- The homogeneous symbol of degree `m` whose values on the sphere `‖ξ‖ = r` are those of `a`:
the homogeneous extension of `η ↦ r ^ (-m) a(x, r η)` from the unit sphere. -/
private def sphereExtension (a : Symbol n V W m) (r : ℝ) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  ofSphere m (fun p ↦ (r ^ m)⁻¹ • a.coefficient (p.1, r • p.2))
    ((a.contDiff_coefficient.comp (contDiff_fst.prodMk (contDiff_snd.const_smul r))).const_smul
      _).contDiffOn

/-- For `r > 0`, the extension of the values of a symbol homogeneous of degree `m` above a radius
`R ≤ r` agrees with the symbol at the frequencies of norm at least `r`. -/
private theorem coefficient_sphereExtension {a : Symbol n V W m} (ha : a.IsHomogeneousAbove m R)
    {r : ℝ} (hr : 0 < r) (hRr : R ≤ r) {x ξ : CoordinateSpace n} (hξ : r ≤ ‖ξ‖) :
    (sphereExtension a r).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  have hξ0 : 0 < ‖ξ‖ := hr.trans_le hξ
  -- `ξ = t • η` with `‖η‖ = r` and `t = ‖ξ‖ / r ≥ 1`.
  have hη : ‖(r * ‖ξ‖⁻¹) • ξ‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ hξ0.ne',
      mul_one]
  have htη : (‖ξ‖ / r) • (r * ‖ξ‖⁻¹) • ξ = ξ := by
    rw [smul_smul, show ‖ξ‖ / r * (r * ‖ξ‖⁻¹) = 1 by field_simp, one_smul]
  have h := Symbol.isHomogeneousAbove_iff.1 ha x _ (hRr.trans hη.ge) (‖ξ‖ / r)
    ((one_le_div hr).2 hξ)
  rw [htη] at h
  rw [sphereExtension, coefficient_ofSphere_of_ne_zero _ _ (norm_pos_iff.1 hξ0), smul_smul,
    smul_smul, h, Real.div_rpow hξ0.le hr.le, div_eq_mul_inv, mul_comm r]

/-- **A symbol homogeneous at large frequencies is classical.** A symbol `a` of order `m` which is
homogeneous of degree `m` above some radius is a classical symbol, whose principal symbol agrees
with `a` at large frequencies
(`TauCeti.ClassicalSymbol.coefficient_principal_of_isHomogeneousAbove`) and whose other
homogeneous terms vanish. -/
def ofIsHomogeneousAbove (a : Symbol n V W m) (ha : ∃ R, a.IsHomogeneousAbove m R) :
    ClassicalSymbol n V W m :=
  ofEqHomogeneous a (sphereExtension a (max ha.choose 1))
    ⟨max ha.choose 1, fun _ _ hξ ↦ (coefficient_sphereExtension ha.choose_spec
      (lt_max_of_lt_right one_pos) (le_max_left _ _) hξ).symm⟩

variable (a : Symbol n V W m) (ha : ∃ R, a.IsHomogeneousAbove m R)

@[simp]
theorem toSymbol_ofIsHomogeneousAbove : (ofIsHomogeneousAbove a ha).toSymbol = a :=
  toSymbol_ofEqHomogeneous _ _ _

@[simp]
theorem term_ofIsHomogeneousAbove_succ (j : ℕ) : (ofIsHomogeneousAbove a ha).term (j + 1) = 0 :=
  term_ofEqHomogeneous_succ _ _ _ j

end ClassicalSymbol

end TauCeti
