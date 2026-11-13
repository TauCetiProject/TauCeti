/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath

/-!
# Smooth Cayley paths from a compatible to a tame almost complex structure

Let `σ` be a smooth two-form on a finite-dimensional manifold `M`, let `J₀` be a smooth almost
complex structure compatible with `σ` and let `J₁` be a smooth almost complex structure tamed by
`σ`. At each point `x`, the Cayley chart based at the compatible structure `J₀ x` identifies the
`σ_x`-tame complex structures on `T_x M` with a balanced convex ball containing `0`. Scaling the
Cayley coordinate of `J₁ x` by `smoothTransition t` therefore stays in that ball, and this file
assembles the resulting pointwise tame structures into the family of smooth almost complex
structures

`J_t = TauCeti.SmoothTwoForm.Compatible.tameCayleyPath h₀ h₁ t`

on `M`, where `h₀ : σ.Compatible J₀` and `h₁ : σ.Tames J₁`. Each `J_t` is tamed by `σ`,
`J_t = J₀` for `t ≤ 0` and `J_t = J₁` for `t ≥ 1`, and the family is jointly smooth on `ℝ × M`
as a section of the endomorphism bundle of the tangent bundle along `(t, x) ↦ x`. When `J₁` is
itself compatible, `J_t` is the compatible Cayley path
`TauCeti.SmoothTwoForm.Compatible.cayleyPath`, so it is compatible for every `t`.

Read with the time reversed, `(t, J) ↦ J_{1 - t}` deforms every tame structure onto `J₀` through
tame structures, keeps compatible structures compatible and fixes `J₀`. This is the bundlewise
assembly of the linear contraction `TauCeti.SymplecticForm.Compatible.cayleyContraction` of the
tame complex structures on a symplectic vector space, and pointwise it is the linear tame Cayley
path `TauCeti.SymplecticForm.Compatible.tameCayleyPath`. Tameness and compatibility of `J₁` are kept
as distinct hypotheses throughout.

The value of `J_t` at `x` is the rational expression `J₀ (1 + β C) (1 - β C)⁻¹` in `J₀ x` and
`J₁ x`, where `C = -(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` is the Cayley coordinate of `J₁ x` and
`β = smoothTransition t`. Both inverses exist because `J₀ x` is compatible and `J₁ x` is tame, so
smoothness follows from `TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPathFormula_family`.
No compactness of `M` and no closedness of `σ` is used.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.tameCayleyPath h₀ h₁ t`: the smooth almost complex structure
  which at every point is the tame structure whose Cayley coordinate relative to `J₀` is
  `smoothTransition t` times that of `J₁`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.cayley_almostComplexStructureAt_tameCayleyPath`: the Cayley
  coordinate of `J_t` relative to `J₀` at each point.
* `TauCeti.SmoothTwoForm.Compatible.tames_tameCayleyPath`: every `J_t` is tamed by `σ`.
* `TauCeti.SmoothTwoForm.Compatible.tameCayleyPath_eq_cayleyPath` and
  `TauCeti.SmoothTwoForm.Compatible.compatible_tameCayleyPath`: for compatible `J₁` the path is
  the compatible Cayley path, and every `J_t` is compatible with `σ`.
* `TauCeti.SmoothTwoForm.Compatible.tameCayleyPath_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.tameCayleyPath_of_one_le`: the path is `J₀` for `t ≤ 0` and
  `J₁` for `1 ≤ t`.
* `TauCeti.SmoothTwoForm.Compatible.tameCayleyPath_self`: the path from `J₀` to itself is constant.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_tameCayleyPath`: the family is jointly smooth in
  `(t, x)`.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_tameCayleyPath_family`: for endpoints and a time
  depending smoothly on a parameter, the paths depend smoothly on the parameter and the point.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Proposition 2.5.13 and Section 4.1 (the Cayley chart on tame complex
  structures, and the contractibility of the space of tame almost complex structures on a
  symplectic manifold).
-/

public section

open Bundle Real

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ J₁ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (h₁ : σ.Tames J₁)

/-- The pointwise linear tame Cayley path at `x`. It is formed on the model space `E = T_x M`,
which carries the norm required by the linear Cayley chart. -/
private def tameCayleyPathAt (h₀ : σ.Compatible J₀) (h₁ : σ.Tames J₁) (t : ℝ) (x : M) :
    AlmostComplexStructure (TangentSpace I x) :=
  SymplecticForm.Compatible.tameCayleyPath (V := E) (h₀.compatibleAt x)
    (h₀.isNondegenerate.tames_iff.mp h₁ x) t

/-- The pointwise structure is tamed by the tangent-space form. -/
private theorem tames_tameCayleyPathAt (t : ℝ) (x : M) :
    (h₀.isNondegenerate.symplecticFormAt x).Tames (tameCayleyPathAt h₀ h₁ t x) :=
  SymplecticForm.Compatible.tames_tameCayleyPath (V := E) _ _ t

/-- The Cayley coordinate of the pointwise structure is the scaled coordinate of `J₁ x`. -/
private theorem cayley_tameCayleyPathAt (t : ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley (tameCayleyPathAt h₀ h₁ t x) =
      smoothTransition t •
        (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) :=
  SymplecticForm.Compatible.cayley_tameCayleyPath (V := E) _ _ t

/-- In operator-norm coordinates the pointwise structure is the Cayley path expression in the
fibre values of `J₀` and `J₁`. -/
private theorem toContinuousLinearMap_tameCayleyPathAt (t : ℝ) (x : M) :
    LinearMap.toContinuousLinearMap (tameCayleyPathAt h₀ h₁ t x).toLinearMap =
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) :=
  SymplecticForm.Compatible.toContinuousLinearMap_tameCayleyPath (V := E) _ _ t
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    (J₁.almostComplexStructureAt_toLinearMap x).symm

/-- The Cayley path from the compatible structure `J₀` to the tame structure `J₁` at time `t`,
as a smooth almost complex structure on `M`: at each point `x` it is the tame structure whose
Cayley coordinate relative to `J₀ x` is `smoothTransition t` times that of `J₁ x`. It is `J₀` for
`t ≤ 0` and `J₁` for `1 ≤ t`. -/
def tameCayleyPath (t : ℝ) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨fun x ↦
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x),
    (h₀.contMDiff_cayleyPathFormula h₁).comp (contMDiff_const.prodMk contMDiff_id)⟩
  square_neg x := by
    ext v
    -- The value at `x` is the continuous version of the pointwise tame structure.
    change cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x)
      (cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) v) = -v
    rw [← toContinuousLinearMap_tameCayleyPathAt h₀ h₁]
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of `T_x M` underlying the path is the Cayley path expression in the fibre
values of `J₀` and `J₁`. -/
theorem tameCayleyPath_toEndomorphism (t : ℝ) (x : M) :
    (h₀.tameCayleyPath h₁ t).toEndomorphism x =
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) :=
  (rfl)

/-- At each point, the path is the pointwise tame structure. -/
private theorem almostComplexStructureAt_tameCayleyPath (t : ℝ) (x : M) :
    (h₀.tameCayleyPath h₁ t).almostComplexStructureAt x = tameCayleyPathAt h₀ h₁ t x :=
  AlmostComplexStructure.toLinearMap_injective <| by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      tameCayleyPath_toEndomorphism, ← toContinuousLinearMap_tameCayleyPathAt h₀ h₁]
    exact LinearMap.coe_toContinuousLinearMap _

/-- At every point, the Cayley coordinate of `J_t` relative to `J₀` is the Cayley coordinate of
`J₁` scaled by `smoothTransition t`. Since tame structures are determined by their Cayley
coordinate relative to a compatible structure, this characterizes the path. -/
@[simp]
theorem cayley_almostComplexStructureAt_tameCayleyPath (t : ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.tameCayleyPath h₁ t).almostComplexStructureAt x) =
      smoothTransition t •
        (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_tameCayleyPath]
  exact cayley_tameCayleyPathAt h₀ h₁ t x

/-- Every structure on the path is tamed by `σ`. -/
theorem tames_tameCayleyPath (t : ℝ) : σ.Tames (h₀.tameCayleyPath h₁ t) :=
  h₀.isNondegenerate.tames_iff.2 fun x ↦ by
    rw [almostComplexStructureAt_tameCayleyPath]
    exact tames_tameCayleyPathAt h₀ h₁ t x

/-- A tame smooth almost complex structure with the prescribed Cayley coordinate at every point
is the path at time `t`. -/
theorem eq_tameCayleyPath_of_cayley_eq {t : ℝ} {J : SmoothAlmostComplexStructure I M}
    (hJ : σ.Tames J)
    (h : ∀ x, (J₀.almostComplexStructureAt x).cayley (J.almostComplexStructureAt x) =
      smoothTransition t •
        (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x)) :
    J = h₀.tameCayleyPath h₁ t := by
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x ↦ ?_
  rw [almostComplexStructureAt_tameCayleyPath]
  refine SymplecticForm.Compatible.eq_of_cayley_eq (h₀.compatibleAt x)
    (h₀.isNondegenerate.tames_iff.mp hJ x) (tames_tameCayleyPathAt h₀ h₁ t x) ?_
  exact (h x).trans (cayley_tameCayleyPathAt h₀ h₁ t x).symm

/-- For a compatible endpoint, the path is the compatible Cayley path. -/
theorem tameCayleyPath_eq_cayleyPath (h₁' : σ.Compatible J₁) (t : ℝ) :
    h₀.tameCayleyPath h₁ t = h₀.cayleyPath h₁' t :=
  (h₀.eq_tameCayleyPath_of_cayley_eq h₁ (h₀.compatible_cayleyPath h₁' t).tames fun x ↦
    cayley_almostComplexStructureAt_cayleyPath h₀ h₁' t x).symm

/-- For a compatible endpoint, every structure on the path is compatible with `σ`. -/
theorem compatible_tameCayleyPath (h₁' : σ.Compatible J₁) (t : ℝ) :
    σ.Compatible (h₀.tameCayleyPath h₁ t) := by
  rw [h₀.tameCayleyPath_eq_cayleyPath h₁ h₁' t]
  exact h₀.compatible_cayleyPath h₁' t

/-- The path agrees with `J₀` on the whole incoming collar `t ≤ 0`. -/
@[simp]
theorem tameCayleyPath_of_nonpos {t : ℝ} (ht : t ≤ 0) : h₀.tameCayleyPath h₁ t = J₀ :=
  (h₀.eq_tameCayleyPath_of_cayley_eq h₁ h₀.tames fun x ↦ by
    rw [smoothTransition.zero_of_nonpos ht, zero_smul, AlmostComplexStructure.cayley_self]).symm

/-- The path agrees with `J₁` on the whole outgoing collar `1 ≤ t`. -/
@[simp]
theorem tameCayleyPath_of_one_le {t : ℝ} (ht : 1 ≤ t) : h₀.tameCayleyPath h₁ t = J₁ :=
  (h₀.eq_tameCayleyPath_of_cayley_eq h₁ h₁ fun x ↦ by
    rw [smoothTransition.one_of_one_le ht, one_smul]).symm

/-- The path from a compatible structure to itself is constant. -/
@[simp]
theorem tameCayleyPath_self (t : ℝ) : h₀.tameCayleyPath h₀.tames t = J₀ :=
  (h₀.eq_tameCayleyPath_of_cayley_eq h₀.tames h₀.tames fun x ↦ by
    rw [AlmostComplexStructure.cayley_self, smul_zero]).symm

/-- The path is jointly smooth in time and space: `(t, x) ↦ J_t x` is a smooth section of the
tangent endomorphism bundle along the projection `ℝ × M → M`. -/
theorem contMDiff_tameCayleyPath :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((h₀.tameCayleyPath h₁ p.1).toEndomorphism p.2)) :=
  h₀.contMDiff_cayleyPathFormula h₁

/-- For a compatible endpoint family `K₀ p` and a tame endpoint family `K₁ p` depending smoothly
on a parameter `p` in a manifold `P`, and a smooth time `τ p`, the paths
`(p, x) ↦ tameCayleyPath (K₀ p) (K₁ p) (τ p) x` form a smooth section of the tangent endomorphism
bundle along the projection `P × M → M`. -/
theorem contMDiff_tameCayleyPath_family {EP HP P : Type*} [NormedAddCommGroup EP]
    [NormedSpace ℝ EP] [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P]
    [ChartedSpace HP P] {K₀ K₁ : P → SmoothAlmostComplexStructure I M}
    (hc₀ : ∀ p, σ.Compatible (K₀ p)) (hc₁ : ∀ p, σ.Tames (K₁ p))
    (hs₀ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hs₁ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₁ q.1).toEndomorphism q.2)))
    {τ : P → ℝ} (hτ : ContMDiff IP 𝓘(ℝ) ∞ τ) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (((hc₀ q.1).tameCayleyPath (hc₁ q.1) (τ q.1)).toEndomorphism q.2)) :=
  contMDiff_cayleyPathFormula_family hc₀ hc₁ hs₀ hs₁ hτ

end TauCeti.SmoothTwoForm.Compatible
