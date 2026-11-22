/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm

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

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §2, (2.7).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module

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
    rw [formHodgeStar_neg_orientation, Pi.smul_apply, neg_one_smul ℝ (o.formHodgeStar hkl (ω y))]
  rw [codifferential_apply _ hkl hlk, codifferential_apply _ hkl hlk, hneg, extDeriv_smul,
    formHodgeStar_neg_orientation, map_smul,
    neg_one_smul ℝ (o.formHodgeStar hlk (extDeriv (fun y ↦ o.formHodgeStar hkl (ω y)) x)),
    neg_neg]

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = n)] in
/-- Applying a Hodge star pointwise preserves differentiability of forms. -/
private theorem differentiableAt_formHodgeStar_comp [FiniteDimensional ℝ V]
    [Fact (finrank ℝ V = n)] {j m : ℕ} (hjm : j + m = finrank ℝ V)
    {ω : V → V [⋀^Fin j]→L[ℝ] ℝ} {x : V} (hω : DifferentiableAt ℝ ω x) :
    DifferentiableAt ℝ (fun y ↦ o.formHodgeStar hjm (ω y)) x :=
  (LinearMap.toContinuousLinearMap (o.formHodgeStar hjm).toLinearMap).differentiableAt.comp x hω

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
  have hω' : ContDiffAt ℝ r (fun y ↦ o.formHodgeStar hkl' (ω y)) x :=
    (LinearMap.toContinuousLinearMap (o.formHodgeStar hkl').toLinearMap).contDiff.contDiffAt.comp
      x hω
  rw [codifferential_apply _ hkl (by omega), hstar, extDeriv_smul,
    extDeriv_extDeriv_apply hω' hr, smul_zero, map_zero, smul_zero]

/-- **The codifferential squares to zero** on forms of class `C²`: `δ δ ω = 0`. -/
theorem codifferential_codifferential {l' : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hkl' : k + 1 + 1 + l' = finrank ℝ V) {r : WithTop ℕ∞}
    {ω : V → V [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ} (hω : ContDiff ℝ r ω) (hr : minSmoothness ℝ 2 ≤ r) :
    o.codifferential hkl (o.codifferential hkl' ω) = 0 :=
  funext fun _ ↦ o.codifferential_codifferential_apply hkl hkl' hω.contDiffAt hr

end Orientation
