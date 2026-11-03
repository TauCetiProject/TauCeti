/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback

/-!
# Smooth Cayley paths of compatible almost complex structures

Let `σ` be a smooth two-form on a finite-dimensional manifold `M` and let `J₀`, `J₁` be smooth
almost complex structures compatible with `σ`. At each point `x`, the compatible Cayley chart
based at `J₀ x` identifies the `σ_x`-compatible complex structures on `T_x M` with a convex set
containing `0`, and `TauCeti.SymplecticForm.Compatible.cayleyPath` joins `J₀ x` to `J₁ x` by
scaling the Cayley coordinate of `J₁ x` with `smoothTransition t`. This file assembles these
pointwise paths into the family of smooth almost complex structures

`J_t = TauCeti.SmoothTwoForm.Compatible.cayleyPath h₀ h₁ t`

on `M`, where `h₀ : σ.Compatible J₀` and `h₁ : σ.Compatible J₁`. Each `J_t` is compatible with
`σ`, `J_t = J₀` for `t ≤ 0` and `J_t = J₁` for `t ≥ 1`, and the family is jointly smooth on
`ℝ × M` as a section of the endomorphism bundle of the tangent bundle along `(t, x) ↦ x`. So the
path is smooth across both endpoints and constant in `t` outside `(0, 1)`.

Smoothness is checked in the trivializations of the tangent bundle. The value of `J_t` at `x` is
the rational expression `J₀ (1 + β C) (1 - β C)⁻¹` in `J₀ x` and `J₁ x`, where
`C = -(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` is the Cayley coordinate of `J₁ x` and `β = smoothTransition t`.
Reading a fibre endomorphism in a trivialization is conjugation by a continuous linear
equivalence, an algebra isomorphism, so it commutes with this expression; and inversion is
smooth at invertible operators. No compactness of `M` and no closedness of `σ` is used.

Such collar-constant families are the input for extending prescribed almost complex structures
across collars, for instance for building a structure on a mapping torus out of `J₀` and its
pullback by the monodromy. Since the path is a rational expression in `J₀` and `J₁`, it depends
only on the two endpoints and is natural: pulling it back along a diffeomorphism gives the path
between the pulled-back structures, for the pulled-back form.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.cayleyPath h₀ h₁ t`: the smooth almost complex structure
  that is the compatible Cayley path from `J₀` to `J₁` at time `t` at every point.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cayleyPath`: at each point, `J_t`
  is the linear compatible Cayley path from `J₀ x` to `J₁ x`.
* `TauCeti.SmoothTwoForm.Compatible.compatible_cayleyPath`: every `J_t` is compatible with `σ`.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_one_le`: the path is `J₀` for `t ≤ 0` and `J₁`
  for `1 ≤ t`.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPath`: the family is jointly smooth in
  `(t, x)`.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_congr`: the path depends only on its endpoints.
* `TauCeti.SmoothTwoForm.Compatible.pullback_cayleyPath`: naturality under diffeomorphisms.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Sections 2.5 and 4.1 (the Cayley chart on compatible complex
  structures, and the contractibility of the space of compatible almost complex structures on a
  symplectic manifold).
-/

public section

open Bundle Real
open scoped Manifold

noncomputable section

namespace TauCeti

/-! ### The Cayley path of smooth compatible structures -/

namespace SmoothTwoForm.Compatible

open scoped ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ J₁ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (h₁ : σ.Compatible J₁)

/-- The pointwise compatible Cayley path at `x`, as a continuous endomorphism of `T_x M`. The
tangent space `T_x M` is the model space `E`, which carries the norm required by the linear
Cayley path; `TangentSpace I x` itself has no norm instance, so the path is formed on `E`. -/
private def cayleyPathEnd (t : ℝ) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x) (h₁.compatibleAt x)
      t).toLinearMap

/-- The pointwise path is the Cayley path expression in the fibre values of `J₀` and `J₁`. -/
private theorem cayleyPathEnd_eq (t : ℝ) (x : M) :
    cayleyPathEnd h₀ h₁ t x =
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) :=
  SymplecticForm.Compatible.toContinuousLinearMap_cayleyPath (V := E) (h₀.compatibleAt x)
    (h₁.compatibleAt x) t (J₀.almostComplexStructureAt_toLinearMap x).symm
    (J₁.almostComplexStructureAt_toLinearMap x).symm

include h₁ in
/-- The pointwise compatible Cayley paths at all points form a jointly smooth family of tangent
endomorphisms over `ℝ × M`. -/
private theorem contMDiff_cayleyPathEnd :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (cayleyPathEnd h₀ h₁ p.1 p.2)) := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  -- Read every fibre endomorphism in the tangent trivialization at `p₀.2`.
  set x₀ := p₀.2
  let e := trivializationAt E (TangentSpace I) x₀
  let coord : (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x) → E →L[ℝ] E :=
    fun x A ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x A
  -- On the base set, reading in coordinates is conjugation by an algebra isomorphism.
  have hconj {x : M} (hx : x ∈ e.baseSet) (A : TangentSpace I x →L[ℝ] TangentSpace I x) :
      coord x A = (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv A := by
    simp only [coord, e, ContinuousLinearMap.inCoordinates_eq hx hx,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hJ (J : SmoothAlmostComplexStructure I M) :
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun x ↦ coord x (J.toEndomorphism x)) x₀ :=
    ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff x₀)).2
  have hinner : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, ℝ × (E →L[ℝ] E) × (E →L[ℝ] E)) ∞
      (fun p : ℝ × M ↦ (smoothTransition p.1, coord p.2 (J₀.toEndomorphism p.2),
        coord p.2 (J₁.toEndomorphism p.2))) p₀ :=
    (smoothTransition.contDiff.contMDiff.comp contMDiff_fst).contMDiffAt.prodMk_space
      (((hJ J₀).comp p₀ contMDiffAt_snd).prodMk_space ((hJ J₁).comp p₀ contMDiffAt_snd))
  -- The two denominators are invertible at `p₀`, since conjugation preserves units.
  let φ₀ := (e.continuousLinearEquivAt ℝ x₀ hx₀).conjContinuousAlgEquiv
  have hu₁ : IsUnit (1 - coord x₀ (J₀.toEndomorphism x₀) * coord x₀ (J₁.toEndomorphism x₀)) := by
    rw [hconj hx₀, hconj hx₀, ← map_mul, ← map_one φ₀, ← map_sub]
    exact (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E)
      (h₀.compatibleAt x₀).tames (h₁.compatibleAt x₀).tames
      (J₀.almostComplexStructureAt_toLinearMap x₀).symm
      (J₁.almostComplexStructureAt_toLinearMap x₀).symm).map φ₀
  have hu₂ : IsUnit (1 - smoothTransition p₀.1 • cayleyFormula (coord x₀ (J₀.toEndomorphism x₀))
      (coord x₀ (J₁.toEndomorphism x₀))) := by
    rw [hconj hx₀, hconj hx₀, ← map_cayleyFormula, ← map_smul, ← map_one φ₀, ← map_sub]
    exact (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E)
      (h₀.compatibleAt x₀) (h₁.compatibleAt x₀).tames
      ⟨smoothTransition.nonneg p₀.1, smoothTransition.le_one p₀.1⟩
      (J₀.almostComplexStructureAt_toLinearMap x₀).symm
      (J₁.almostComplexStructureAt_toLinearMap x₀).symm).map φ₀
  -- Near `p₀`, the path in coordinates is the Cayley path expression of `J₀` and `J₁` in
  -- coordinates, which is smooth.
  refine ((contDiffAt_cayleyPathFormula hu₁ hu₂).comp_contMDiffAt (f := fun p : ℝ × M ↦
    (smoothTransition p.1, coord p.2 (J₀.toEndomorphism p.2), coord p.2 (J₁.toEndomorphism p.2)))
    hinner).congr_of_eventuallyEq ?_
  filter_upwards [(e.open_baseSet.preimage continuous_snd).mem_nhds hx₀] with p hp
  rw [Function.comp_apply, cayleyPathEnd_eq, hconj hp, hconj hp]
  exact (hconj hp _).trans (map_cayleyPathFormula _ _ _ _)

/-- The compatible Cayley path from `J₀` to `J₁` at time `t`, as a smooth almost complex structure
on `M`: at each point `x` it is the compatible Cayley path from `J₀ x` to `J₁ x` at time `t`,
obtained by scaling the Cayley coordinate of `J₁ x` relative to `J₀ x` by `smoothTransition t`.
It is `J₀` for `t ≤ 0` and `J₁` for `1 ≤ t`. -/
def cayleyPath (t : ℝ) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨cayleyPathEnd h₀ h₁ t,
    (contMDiff_cayleyPathEnd h₀ h₁).comp (contMDiff_const.prodMk contMDiff_id)⟩
  square_neg x := by
    ext v
    -- The section's value at `x` is `cayleyPathEnd h₀ h₁ t x`, the continuous version of the
    -- pointwise path `J`, an almost complex structure on `E = T_x M`. Evaluating
    -- `LinearMap.toContinuousLinearMap J.toLinearMap` is evaluating `J` by definition, but
    -- `simp` cannot rewrite it across `TangentSpace I x = E`, so `J (J v) = -v` closes the goal.
    change cayleyPathEnd h₀ h₁ t x (cayleyPathEnd h₀ h₁ t x v) = -v
    simp only [cayleyPathEnd]
    exact AlmostComplexStructure.apply_apply _ v

/-- At each point, the path is the pointwise compatible Cayley path. -/
-- This is not a `simp` lemma: its right-hand side is a structure on the model space `E`, so
-- rewriting with it turns `TangentSpace I x` terms into `E` terms that later `simp` lemmas, such
-- as `cayley_almostComplexStructureAt_cayleyPath`, no longer match.
theorem almostComplexStructureAt_cayleyPath (t : ℝ) (x : M) :
    (h₀.cayleyPath h₁ t).almostComplexStructureAt x =
      SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x) (h₁.compatibleAt x) t :=
  AlmostComplexStructure.toLinearMap_injective <| by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    -- The endomorphism of `cayleyPath` at `x` is `cayleyPathEnd` by definition.
    change (cayleyPathEnd h₀ h₁ t x).toLinearMap = _
    -- Unfolding it leaves `LinearMap.coe_toContinuousLinearMap` for the pointwise path, read
    -- on `TangentSpace I x = E`.
    rw [cayleyPathEnd]
    exact LinearMap.coe_toContinuousLinearMap _

/-- At each point, applying the path to a tangent vector applies the pointwise compatible Cayley
path. -/
-- This is not a `simp` lemma, for the same reason as `almostComplexStructureAt_cayleyPath`.
theorem cayleyPath_apply (t : ℝ) (x : M) (v : TangentSpace I x) :
    h₀.cayleyPath h₁ t x v =
      SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x) (h₁.compatibleAt x)
        t v := by
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_cayleyPath]
  rfl

/-- A smooth almost complex structure agreeing with the pointwise path at every point is the
path. -/
private theorem cayleyPath_eq_of_forall {t : ℝ} {J : SmoothAlmostComplexStructure I M}
    (h : ∀ x, SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x)
      (h₁.compatibleAt x) t = J.almostComplexStructureAt x) :
    h₀.cayleyPath h₁ t = J := by
  ext x v
  rw [← (h₀.cayleyPath h₁ t).almostComplexStructureAt_apply x v,
    ← J.almostComplexStructureAt_apply x v, almostComplexStructureAt_cayleyPath, h x]

/-- At every point, the Cayley coordinate of `J_t` relative to `J₀` is the Cayley coordinate of
`J₁` scaled by `smoothTransition t`. Since compatible structures are determined by their Cayley
coordinate, this characterizes the path. -/
@[simp]
theorem cayley_almostComplexStructureAt_cayleyPath (t : ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley ((h₀.cayleyPath h₁ t).almostComplexStructureAt x) =
      smoothTransition t •
        (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_cayleyPath]
  exact SymplecticForm.Compatible.cayley_cayleyPath (V := E) (h₀.compatibleAt x)
    (h₁.compatibleAt x) t

/-- Every structure on the path is compatible with `σ`. -/
theorem compatible_cayleyPath (t : ℝ) : σ.Compatible (h₀.cayleyPath h₁ t) :=
  h₀.isNondegenerate.compatible_iff.2 fun x ↦ by
    rw [almostComplexStructureAt_cayleyPath]
    exact SymplecticForm.Compatible.compatible_cayleyPath (V := E) (h₀.compatibleAt x)
      (h₁.compatibleAt x) t

/-- The path agrees with `J₀` on the whole incoming collar `t ≤ 0`. -/
@[simp]
theorem cayleyPath_of_nonpos {t : ℝ} (ht : t ≤ 0) : h₀.cayleyPath h₁ t = J₀ :=
  cayleyPath_eq_of_forall h₀ h₁ fun x ↦
    SymplecticForm.Compatible.cayleyPath_of_nonpos (V := E) (h₀.compatibleAt x)
      (h₁.compatibleAt x) ht

/-- The path agrees with `J₁` on the whole outgoing collar `1 ≤ t`. -/
@[simp]
theorem cayleyPath_of_one_le {t : ℝ} (ht : 1 ≤ t) : h₀.cayleyPath h₁ t = J₁ :=
  cayleyPath_eq_of_forall h₀ h₁ fun x ↦
    SymplecticForm.Compatible.cayleyPath_of_one_le (V := E) (h₀.compatibleAt x)
      (h₁.compatibleAt x) ht

/-- The Cayley path from a compatible structure to itself is constant. -/
@[simp]
theorem cayleyPath_self (t : ℝ) : h₀.cayleyPath h₀ t = J₀ :=
  cayleyPath_eq_of_forall h₀ h₀ fun x ↦
    SymplecticForm.Compatible.cayleyPath_self (V := E) (h₀.compatibleAt x) t

/-- The Cayley path is jointly smooth in time and space: `(t, x) ↦ J_t x` is a smooth section of
the tangent endomorphism bundle along the projection `ℝ × M → M`. -/
theorem contMDiff_cayleyPath :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((h₀.cayleyPath h₁ p.1).toEndomorphism p.2)) :=
  contMDiff_cayleyPathEnd h₀ h₁

/-- The endomorphism of `T_x M` underlying the path is the Cayley path expression in the fibre
values of `J₀` and `J₁`. -/
private theorem cayleyPath_toEndomorphism (t : ℝ) (x : M) :
    (h₀.cayleyPath h₁ t).toEndomorphism x =
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) :=
  cayleyPathEnd_eq h₀ h₁ t x

/-- The Cayley path depends only on its endpoints, not on the form they are compatible with. -/
theorem cayleyPath_congr {σ' : SmoothTwoForm I M} {J₀' J₁' : SmoothAlmostComplexStructure I M}
    (h₀' : σ'.Compatible J₀') (h₁' : σ'.Compatible J₁') (hJ₀ : J₀ = J₀') (hJ₁ : J₁ = J₁')
    (t : ℝ) : h₀.cayleyPath h₁ t = h₀'.cayleyPath h₁' t := by
  subst hJ₀ hJ₁
  apply SmoothAlmostComplexStructure.toEndomorphism_injective
  ext x : 1
  rw [cayleyPath_toEndomorphism, cayleyPath_toEndomorphism]

/-- Pulling the Cayley path back along a diffeomorphism gives the Cayley path between the
pulled-back structures, for the pulled-back form. -/
theorem pullback_cayleyPath {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] {σ' : SmoothTwoForm I' M'}
    {J₀' J₁' : SmoothAlmostComplexStructure I' M'} (h₀' : σ'.Compatible J₀')
    (h₁' : σ'.Compatible J₁') (h : M ≃ₘ⟮I, I'⟯ M') (t : ℝ) :
    (h₀'.cayleyPath h₁' t).pullback h = (h₀'.pullback h).cayleyPath (h₁'.pullback h) t := by
  apply SmoothAlmostComplexStructure.toEndomorphism_injective
  ext x : 1
  -- Both sides are the Cayley path expression, and pulling back is a conjugation.
  rw [SmoothAlmostComplexStructure.pullback_toEndomorphism, cayleyPath_toEndomorphism,
    cayleyPath_toEndomorphism, map_cayleyPathFormula,
    SmoothAlmostComplexStructure.pullback_toEndomorphism,
    SmoothAlmostComplexStructure.pullback_toEndomorphism]

end SmoothTwoForm.Compatible

end TauCeti
