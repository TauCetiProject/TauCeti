/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Converse
import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
import TauCeti.Analysis.Complex.UpperHalfPlane.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Inversion covariance of Schwarz--Christoffel maps

The upper-half-plane automorphism `z ↦ p - 1 / z` exchanges the real prevertex `p`
with parameter infinity. The other prevertices `a i` become `-1 / (a i - p)` and
retain their exponents. The old parameter infinity becomes the prevertex `0`, with
exponent `-2 - (t + ∑ i, e i)`, where `t` is the exponent at `p`.

This file computes the pre-Schwarzian after this change of coordinates, integrates
it to an explicit affine identity between normalized primitives, and proves that
the represented domain is preserved. No integrability or univalence assumptions
are needed for the identity. In particular, logarithmic finite prevertices can be
moved to parameter infinity when studying polygonal domains with several ends.

The distinguished prevertex is indexed by `none`, and all other prevertices by
`some i`. Only separation from the distinguished prevertex is required; the other
prevertices may coincide. The new total exponent is `-2 - t`, so a logarithmic
prevertex (`t = -1`) becomes a logarithmic end at parameter infinity.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Finset Function Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

private theorem hasDerivAt_primitive_const_sub_inv (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (p : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (fun w => schwarzChristoffelPrimitive a e z₀ ((p : ℂ) - w⁻¹))
      (schwarzChristoffelIntegrand a e ((p : ℂ) - z⁻¹) / z ^ 2) z := by
  have hz0 : z ≠ 0 := ne_of_mem_of_not_mem hz (by simp)
  have hφ := ((hasDerivAt_id z).inv hz0).const_sub (p : ℂ)
  simpa only [neg_one_mul, neg_neg, id_eq, Pi.inv_apply, div_eq_mul_inv, Function.comp_def] using
    (hasDerivAt_schwarzChristoffelPrimitive a e z₀
      ((bijOn_const_sub_inv_upperHalfPlaneSet p).mapsTo hz)).comp z hφ

/-- **The pre-Schwarzian under inversion at a prevertex.** The exponent at the
new prevertex `0` is the old exponent at parameter infinity, `-2 - (t + ∑ i, e i)`.
All other exponents are unchanged. -/
theorem logDeriv_deriv_schwarzChristoffelPrimitive_const_sub_inv
    (a e : ι → ℝ) (p t : ℝ) (ha : ∀ i, a i ≠ p) (z₀ : UpperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    logDeriv (deriv (fun w =>
      schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) z₀
        ((p : ℂ) - w⁻¹))) z =
      ∑ i : Option ι,
        ((Option.elim' (-2 - (t + ∑ j, e j)) e i : ℝ) : ℂ) /
          (z - (Option.elim' 0 (fun j => -(a j - p)⁻¹) i : ℝ)) := by
  let F := schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) z₀
  let φ : ℂ → ℂ := fun w => (p : ℂ) - w⁻¹
  have hz0 : z ≠ 0 := ne_of_mem_of_not_mem hz (by simp)
  have hφz := (bijOn_const_sub_inv_upperHalfPlaneSet p).mapsTo hz
  have hFd := differentiableOn_schwarzChristoffelPrimitive
    (Option.elim' p a) (Option.elim' t e) z₀
  have hFan : AnalyticAt ℂ F (φ z) := hFd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hφz)
  have hφan : AnalyticAt ℂ φ z := analyticAt_const.sub (analyticAt_id.inv hz0)
  have hdφ : deriv φ = fun w => (w ^ 2)⁻¹ := by
    ext w
    simp [φ, deriv_inv]
  have hnF : deriv F (φ z) ≠ 0 := by
    rw [deriv_schwarzChristoffelPrimitive _ _ _ hφz]
    exact schwarzChristoffelIntegrand_ne_zero _ _ hφz
  -- The chain rule contributes the pole `-2 / z` from the inverse coordinate.
  have hchain := logDeriv_deriv_comp hFan hφan hnF (by simp [hdφ, hz0])
  have hlog : logDeriv (deriv φ) z = -(2 : ℂ) / z := by
    rw [hdφ]
    simpa using logDeriv_zpow z (-2)
  rw [hlog, hdφ, logDeriv_deriv_schwarzChristoffelPrimitive _ _ _ hφz] at hchain
  simp only [Fintype.sum_option, Option.elim'_none, Option.elim'_some] at hchain ⊢
  have hfraction (i : ι) :
      (e i : ℂ) / ((p : ℂ) - z⁻¹ - (a i : ℂ)) / z ^ 2 =
        (e i : ℂ) / (z - (-(a i - p)⁻¹ : ℝ)) - (e i : ℂ) / z := by
    have hgap : (a i : ℂ) - (p : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (ha i)
    have hden : (p : ℂ) - z⁻¹ - (a i : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (UpperHalfPlane.ne_ofReal ⟨_, hφz⟩ _)
    have hleft : -1 + (p : ℂ) * z - z * (a i : ℂ) ≠ 0 := by
      convert mul_ne_zero hden hz0 using 1
      field_simp
      ring
    have hright : 1 - (p : ℂ) * z + z * (a i : ℂ) ≠ 0 := by
      intro h
      apply hleft
      linear_combination -h
    push_cast
    field_simp
    ring_nf at hleft hright ⊢
    field_simp
    ring
  have hsum := Finset.sum_congr (s₁ := univ) (s₂ := univ) rfl (fun i _ => hfraction i)
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_div] at hsum
  have hpterm : (t : ℂ) / ((p : ℂ) - z⁻¹ - p) / z ^ 2 = -(t : ℂ) / z := by
    field_simp
    ring
  -- Separate the distinguished pole, then combine the contributions at the new origin.
  calc
    _ = ((t : ℂ) / ((p : ℂ) - z⁻¹ - p) +
        ∑ i, (e i : ℂ) / ((p : ℂ) - z⁻¹ - a i)) / z ^ 2 - 2 / z := by
      simpa only [F, φ, comp_def, div_eq_mul_inv, neg_mul, sub_eq_add_neg] using hchain
    _ = -(t : ℂ) / z +
        ((∑ i, (e i : ℂ) / (z - (-(a i - p)⁻¹ : ℝ))) - (∑ i, (e i : ℂ)) / z) - 2 / z := by
      rw [add_div, hpterm, hsum]
    _ = _ := by push_cast; ring

/-- **Normalized Schwarz--Christoffel covariance under inversion.** The value and
derivative at the new base point determine the affine constants explicitly. The
formula holds for arbitrary real exponents, including logarithmic prevertices. -/
theorem schwarzChristoffelPrimitive_const_sub_inv
    (a e : ι → ℝ) (p t : ℝ) (ha : ∀ i, a i ≠ p) (b c : UpperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) b
        ((p : ℂ) - z⁻¹) =
      (schwarzChristoffelIntegrand (Option.elim' p a) (Option.elim' t e)
          ((p : ℂ) - (c : ℂ)⁻¹) /
        ((c : ℂ) ^ 2 * schwarzChristoffelIntegrand
          (Option.elim' 0 (fun i => -(a i - p)⁻¹))
          (Option.elim' (-2 - (t + ∑ i, e i)) e) c)) *
        schwarzChristoffelPrimitive (Option.elim' 0 (fun i => -(a i - p)⁻¹))
          (Option.elim' (-2 - (t + ∑ i, e i)) e) c z +
      schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) b
        ((p : ℂ) - (c : ℂ)⁻¹) := by
  let f : ℂ → ℂ := fun w =>
    schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) b ((p : ℂ) - w⁻¹)
  have hd (w : ℂ) (hw : w ∈ upperHalfPlaneSet) :=
    hasDerivAt_primitive_const_sub_inv (Option.elim' p a) (Option.elim' t e) b p hw
  have hn (w : ℂ) (hw : w ∈ upperHalfPlaneSet) : deriv f w ≠ 0 := by
    rw [(hd w hw).deriv]
    exact div_ne_zero (schwarzChristoffelIntegrand_ne_zero _ _
      ((bijOn_const_sub_inv_upperHalfPlaneSet p).mapsTo hw))
      (pow_ne_zero _ (ne_of_mem_of_not_mem hw (by simp)))
  have h := eqOn_const_mul_schwarzChristoffelPrimitive_add_of_logDeriv_deriv_eqOn
    (Option.elim' 0 (fun i => -(a i - p)⁻¹)) (Option.elim' (-2 - (t + ∑ i, e i)) e) c
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt) hn
    (fun _ hw => logDeriv_deriv_schwarzChristoffelPrimitive_const_sub_inv a e p t ha b hw) hz
  simpa only [(hd c c.im_pos).deriv, div_div, f] using h

/-- **Inversion preserves the Schwarz--Christoffel represented domain.** Moving the
distinguished prevertex `p` to parameter infinity changes only the affine constants
in the target and replaces the old parameter infinity by the finite prevertex `0`.
The total exponent of the new data is `-2 - t`. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_inverted_prevertices
    (a e : ι → ℝ) (p t : ℝ) (ha : ∀ i, a i ≠ p) (b c : UpperHalfPlane)
    {A B : ℂ} {U : Set ℂ}
    (hbij : BijOn (fun z => A *
      schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) b z + B)
      upperHalfPlaneSet U) :
    ∃ A' : ℂ, A' ≠ 0 ∧ ∃ B' : ℂ,
      BijOn (fun z => A' *
        schwarzChristoffelPrimitive (Option.elim' 0 (fun i => -(a i - p)⁻¹))
          (Option.elim' (-2 - (t + ∑ i, e i)) e) c z + B') upperHalfPlaneSet U := by
  let a' := Option.elim' 0 (fun i => -(a i - p)⁻¹)
  let e' := Option.elim' (-2 - (t + ∑ i, e i)) e
  let C := schwarzChristoffelIntegrand (Option.elim' p a) (Option.elim' t e)
    ((p : ℂ) - (c : ℂ)⁻¹) / ((c : ℂ) ^ 2 * schwarzChristoffelIntegrand a' e' c)
  have hC : C ≠ 0 := div_ne_zero (schwarzChristoffelIntegrand_ne_zero _ _
    ((bijOn_const_sub_inv_upperHalfPlaneSet p).mapsTo c.im_pos))
    (mul_ne_zero (pow_ne_zero _ c.ne_zero) (schwarzChristoffelIntegrand_ne_zero a' e' c.im_pos))
  have hA : A ≠ 0 := ne_zero_of_injOn_const_mul_add hbij.injOn
  refine ⟨A * C, mul_ne_zero hA hC,
    A * schwarzChristoffelPrimitive (Option.elim' p a) (Option.elim' t e) b
      ((p : ℂ) - (c : ℂ)⁻¹) + B, ?_⟩
  apply (hbij.comp (bijOn_const_sub_inv_upperHalfPlaneSet p)).congr
  intro z hz
  simp only [comp_apply, schwarzChristoffelPrimitive_const_sub_inv a e p t ha b c hz]
  dsimp only [C, a', e']
  ring

end TauCeti
