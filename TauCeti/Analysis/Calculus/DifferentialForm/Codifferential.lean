/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.Integral

/-!
# The codifferential of differential forms on an oriented inner product space

On an oriented finite-dimensional real inner product space `V` of dimension `n`, a differential
`j`-form is a map `ω : V → V [⋀^Fin j]→L[ℝ] ℝ`, with Mathlib's exterior derivative `extDeriv`.
The codifferential of `(k + 1)`-forms is

`δ = (-1) ^ (n (k + 2) + 1) ⋆ d ⋆`,

built from the Hodge star of forms `Orientation.formHodgeStar`, applied pointwise, and `extDeriv`.
For forms of degree `j = k + 1` the sign is `(-1) ^ (n (j + 1) + 1)`, the sign that makes `δ` the
formal adjoint of `d` for the Gram inner product of forms integrated against Lebesgue measure.
It is equivalently characterized by `⋆δω = (-1) ^ (k + 1) d⋆ω`
(`Orientation.formHodgeStar_codifferential`).

The codifferential does not depend on the orientation, since reversing it negates both stars, and
it squares to zero on forms of class `C²`, since `⋆⋆` is a sign and `d d = 0`.

The codifferential is the formal adjoint of the exterior derivative for the Gram inner product of
forms integrated against the volume measure: `∫ ⟪dφ, ψ⟫ = ∫ ⟪φ, δψ⟫` for a `C¹` form `φ` and a
compactly supported `C¹` form `ψ`. Both integrands are top-degree wedges on a positively oriented
orthonormal basis, `dφ ∧ ⋆ψ` and `φ ∧ ⋆δψ = ± φ ∧ d⋆ψ`, so this is integration by parts for forms,
`Module.Basis.integral_extDeriv_wedge_eq_integral_wedge_extDeriv`.

This is the Euclidean, chart-level counterpart of the codifferential of smooth forms on an oriented
Riemannian manifold, `TauCeti.SmoothForm.codifferential`; it acts on the same maps
`V → V [⋀^Fin j]→L[ℝ] ℝ` as `extDeriv` and the exterior derivative of test forms.

## Main definitions

* `Orientation.codifferential`: the codifferential `(-1) ^ (n (k + 2) + 1) ⋆ d ⋆` of
  `(k + 1)`-forms.

## Main results

* `Orientation.formHodgeStar_codifferential`: `⋆δω = (-1) ^ (k + 1) d⋆ω`.
* `Orientation.codifferential_neg_orientation`: `δ` does not depend on the orientation.
* `Orientation.codifferential_add`, `Orientation.codifferential_const_smul`: linearity.
* `Orientation.codifferential_codifferential_apply`, `Orientation.codifferential_codifferential`:
  `δ δ ω = 0` for forms of class `C²`.
* `Orientation.integral_alternatingFormInner_extDeriv_eq_codifferential`:
  `∫ ⟪dφ, ψ⟫ = ∫ ⟪φ, δψ⟫` when `ψ` has compact support.

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §2, (2.7) and (2.8).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module MeasureTheory TauCeti

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n)) {k l : ℕ}

/-- The codifferential `δ = (-1) ^ (n (k + 2) + 1) ⋆ d ⋆` of differential `(k + 1)`-forms on an
oriented inner product space of dimension `n = k + 1 + l`. For forms of degree `j = k + 1` the sign
is `(-1) ^ (n (j + 1) + 1)`. -/
def codifferential (hkl : k + 1 + l = finrank ℝ V) (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) :
    V [⋀^Fin k]→L[ℝ] ℝ :=
  (-1 : ℝ) ^ (n * (k + 2) + 1) • o.formHodgeStar (show l + 1 + k = finrank ℝ V by omega)
    (extDeriv (fun y ↦ o.formHodgeStar hkl (ω y)) x)

/-- The codifferential is `(-1) ^ (n (k + 2) + 1) ⋆ d ⋆`. -/
theorem codifferential_apply (hkl : k + 1 + l = finrank ℝ V) (hlk : l + 1 + k = finrank ℝ V)
    (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) :
    o.codifferential hkl ω x = (-1 : ℝ) ^ (n * (k + 2) + 1) •
      o.formHodgeStar hlk (extDeriv (fun y ↦ o.formHodgeStar hkl (ω y)) x) :=
  (rfl)

/-- **The Hodge star of the codifferential**: `⋆δω = (-1) ^ (k + 1) d⋆ω` for a `(k + 1)`-form
`ω`. -/
theorem formHodgeStar_codifferential (hkl : k + 1 + l = finrank ℝ V)
    (hkl' : k + (l + 1) = finrank ℝ V) (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) :
    o.formHodgeStar hkl' (o.codifferential hkl ω x) =
      (-1 : ℝ) ^ (k + 1) • extDeriv (fun y ↦ o.formHodgeStar hkl (ω y)) x := by
  have hn : n = k + 1 + l := (Fact.out : finrank ℝ V = n).symm.trans hkl.symm
  -- `⋆⋆ = (-1) ^ ((l + 1) k)` on `(l + 1)`-forms, and the two signs combine to `(-1) ^ (k + 1)`.
  have hsign : (-1 : ℝ) ^ (n * (k + 2) + 1) * (-1) ^ ((l + 1) * k) = (-1) ^ (k + 1) := by
    subst hn
    rw [← pow_add]
    refine neg_one_pow_congr ?_
    simp only [Nat.even_add, Nat.even_mul, Nat.even_add_one]
    tauto
  rw [o.codifferential_apply hkl (by omega), map_smul, formHodgeStar_formHodgeStar, smul_smul,
    hsign]

/-- Reversing the orientation does not change the codifferential, since it negates both Hodge
stars. -/
@[simp]
theorem codifferential_neg_orientation (hkl : k + 1 + l = finrank ℝ V) :
    (-o).codifferential hkl = o.codifferential hkl := by
  ext1 ω
  ext1 x
  have hlk : l + 1 + k = finrank ℝ V := by omega
  have hneg : (fun y ↦ (-o).formHodgeStar hkl (ω y)) =
      (-1 : ℝ) • fun y ↦ o.formHodgeStar hkl (ω y) := by
    funext y
    rw [formHodgeStar_neg_orientation, Pi.smul_apply]
    exact (neg_one_smul ℝ _).symm
  rw [codifferential_apply _ hkl hlk, codifferential_apply _ hkl hlk, hneg, extDeriv_smul]
  simp

/-- The codifferential is additive on forms differentiable at the point. -/
theorem codifferential_add (hkl : k + 1 + l = finrank ℝ V) {ω₁ ω₂ : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    {x : V} (hω₁ : DifferentiableAt ℝ ω₁ x) (hω₂ : DifferentiableAt ℝ ω₂ x) :
    o.codifferential hkl (ω₁ + ω₂) x = o.codifferential hkl ω₁ x + o.codifferential hkl ω₂ x := by
  have hlk : l + 1 + k = finrank ℝ V := by omega
  simp only [codifferential_apply _ hkl hlk, Pi.add_apply, map_add]
  rw [extDeriv_fun_add (o.differentiableAt_formHodgeStar_comp hkl hω₁)
    (o.differentiableAt_formHodgeStar_comp hkl hω₂), map_add, smul_add]

/-- The codifferential commutes with multiplication by a constant. -/
theorem codifferential_const_smul (hkl : k + 1 + l = finrank ℝ V) (c : ℝ)
    (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    o.codifferential hkl (c • ω) = c • o.codifferential hkl ω := by
  ext1 x
  have hlk : l + 1 + k = finrank ℝ V := by omega
  have h : (fun y ↦ o.formHodgeStar hkl ((c • ω) y)) = c • fun y ↦ o.formHodgeStar hkl (ω y) := by
    funext y
    simp
  rw [codifferential_apply _ hkl hlk, Pi.smul_apply, codifferential_apply _ hkl hlk, h,
    extDeriv_smul, map_smul, smul_comm]

/-- **The codifferential squares to zero** at every point near which the form is of class `C²`:
`δ δ ω = 0`, since `⋆⋆` is a sign and `d d = 0`. -/
theorem codifferential_codifferential_apply {l' : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hkl' : k + 1 + 1 + l' = finrank ℝ V) {r : WithTop ℕ∞}
    {ω : V → V [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ} {x : V} (hω : ContDiffAt ℝ r ω x)
    (hr : minSmoothness ℝ 2 ≤ r) :
    o.codifferential hkl (o.codifferential hkl' ω) x = 0 := by
  obtain rfl : l = l' + 1 := by omega
  -- `⋆δω = ± d⋆ω` as forms, so `d⋆δω = ± dd⋆ω = 0`, and `δδω = ± ⋆d⋆δω = 0`.
  have hstar : (fun y ↦ o.formHodgeStar hkl (o.codifferential hkl' ω y)) =
      (-1 : ℝ) ^ (k + 1 + 1) • extDeriv fun y ↦ o.formHodgeStar hkl' (ω y) := by
    funext y
    exact o.formHodgeStar_codifferential hkl' hkl ω y
  rw [codifferential_apply _ hkl (by omega), hstar, extDeriv_smul,
    extDeriv_extDeriv_apply (o.contDiffAt_formHodgeStar_comp hkl' hω) hr, smul_zero, map_zero,
    smul_zero]

/-- **The codifferential squares to zero** on forms of class `C²`: `δ δ ω = 0`. -/
theorem codifferential_codifferential {l' : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hkl' : k + 1 + 1 + l' = finrank ℝ V) {r : WithTop ℕ∞}
    {ω : V → V [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ} (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r) :
    o.codifferential hkl (o.codifferential hkl' ω) = 0 :=
  funext fun _ ↦ o.codifferential_codifferential_apply hkl hkl' hω.contDiffAt hr

/-! ### Adjointness of the exterior derivative and the codifferential -/

section Adjoint

variable [MeasurableSpace V] [BorelSpace V]

/-- **The codifferential is the formal adjoint of the exterior derivative**:
`∫ ⟪dφ, ψ⟫ = ∫ ⟪φ, δψ⟫` for a `C¹` form `φ` of degree `k` and a compactly supported `C¹` form `ψ`
of degree `k + 1`, with the Gram inner product of forms integrated against the volume measure. -/
theorem integral_alternatingFormInner_extDeriv_eq_codifferential
    (hkl : k + 1 + l = finrank ℝ V) {φ : V → V [⋀^Fin k]→L[ℝ] ℝ}
    {ψ : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, alternatingFormInner V (k + 1) (extDeriv φ x) (ψ x) =
      ∫ x, alternatingFormInner V k (φ x) (o.codifferential hkl ψ x) := by
  have hn : finrank ℝ V = n := Fact.out
  have hkl' : k + (l + 1) = finrank ℝ V := by omega
  -- Evaluate top-degree forms on a positively oriented orthonormal basis, where `vol = 1`.
  let b := o.finOrthonormalBasis (by omega) hn
  have hvol (m : ℕ) (h₁ : m = n) (h₂ : n = m) :
      o.volumeForm ((⇑b.toBasis ∘ Fin.cast h₁) ∘ finCongr h₂) = 1 := by
    have hb : (⇑b.toBasis ∘ Fin.cast h₁) ∘ finCongr h₂ = b.toBasis := by
      funext i
      simp
    rw [hb, o.volumeForm_robust b (o.finOrthonormalBasis_orientation _ hn), Basis.det_self]
  -- Integration by parts for `φ ∧ ⋆ψ`.
  have hparts := b.toBasis.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (k := k) (l := l)
    (by omega) hφ (o.contDiff_formHodgeStar_comp hkl hψ) (hc.comp_left (map_zero _))
  rw [b.addHaar_eq_volume] at hparts
  -- The left side is `∫ dφ ∧ ⋆ψ`.
  have hleft (x : V) : (extDeriv φ x).wedge (o.formHodgeStar hkl (ψ x))
      (⇑b.toBasis ∘ Fin.cast (by omega)) = alternatingFormInner V (k + 1) (extDeriv φ x) (ψ x) := by
    rw [o.wedge_formHodgeStar_apply hkl, hvol, mul_one]
  -- The right side is `± ∫ φ ∧ d⋆ψ`, since `⋆δψ = (-1) ^ (k + 1) d⋆ψ`.
  have hright (x : V) : (φ x).wedge (extDeriv (fun y ↦ o.formHodgeStar hkl (ψ y)) x)
      (⇑b.toBasis ∘ Fin.cast (by omega)) =
        (-1 : ℝ) ^ (k + 1) * alternatingFormInner V k (φ x) (o.codifferential hkl ψ x) := by
    have h := o.wedge_formHodgeStar_apply hkl' (φ x) (o.codifferential hkl ψ x)
      (⇑b.toBasis ∘ Fin.cast (by omega))
    rw [hvol, mul_one, o.formHodgeStar_codifferential hkl hkl',
      ContinuousAlternatingMap.wedge_smul_right, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    simp [← h, ← mul_assoc, ← pow_add]
  simp_rw [hleft, hright, integral_const_mul] at hparts
  simp [hparts, ← mul_assoc, ← pow_add]

end Adjoint

end Orientation
