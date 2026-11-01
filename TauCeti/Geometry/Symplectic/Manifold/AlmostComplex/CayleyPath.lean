/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Analysis.Normed.Operator.Banach

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
pullback by the monodromy.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.cayleyPath h₀ h₁ t`: the smooth almost complex structure
  that is the compatible Cayley path from `J₀` to `J₁` at time `t` at every point.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.compatible_cayleyPath`: every `J_t` is compatible with `σ`.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_one_le`: the path is `J₀` for `t ≤ 0` and `J₁`
  for `1 ≤ t`.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPath`: the family is jointly smooth in
  `(t, x)`.

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

/-! ### The Cayley path as a rational expression -/

section Formula

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The Cayley coordinate `-(1 + A B)(1 - A B)⁻¹` of `B` relative to `A`, in any real algebra. -/
private def cayleyFormula (A B : R) : R :=
  -((1 + A * B) * Ring.inverse (1 - A * B))

/-- The point at parameter `b` of the Cayley segment from `A` to `B`, that is
`A (1 + b C)(1 - b C)⁻¹` for the Cayley coordinate `C` of `B` relative to `A`. -/
private def cayleyPathFormula (b : ℝ) (A B : R) : R :=
  A * (1 + b • cayleyFormula A B) * Ring.inverse (1 - b • cayleyFormula A B)

/-- Algebra isomorphisms commute with the Cayley coordinate expression. -/
private theorem map_cayleyFormula {S F : Type*} [Ring S] [Algebra ℝ S] [EquivLike F R S]
    [AlgEquivClass F ℝ R S] (f : F) (A B : R) :
    f (cayleyFormula A B) = cayleyFormula (f A) (f B) := by
  simp only [cayleyFormula, map_mul, map_add, map_one, map_neg, map_sub, map_ringInverse]

/-- Algebra isomorphisms commute with the Cayley path expression. -/
private theorem map_cayleyPathFormula {S F : Type*} [Ring S] [Algebra ℝ S] [EquivLike F R S]
    [AlgEquivClass F ℝ R S] (f : F) (b : ℝ) (A B : R) :
    f (cayleyPathFormula b A B) = cayleyPathFormula b (f A) (f B) := by
  simp only [cayleyPathFormula, map_mul, map_add, map_one, map_smul, map_sub, map_ringInverse,
    map_cayleyFormula]

/-- The Cayley path expression is smooth in its parameter and both endpoints at any point where
its two denominators are invertible. -/
private theorem contDiffAt_cayleyPathFormula {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] {n : WithTop ℕ∞} {b : ℝ} {A B : R} (h₁ : IsUnit (1 - A * B))
    (h₂ : IsUnit (1 - b • cayleyFormula A B)) :
    ContDiffAt ℝ n (fun q : ℝ × R × R ↦ cayleyPathFormula q.1 q.2.1 q.2.2) (b, A, B) := by
  have hinv {g : ℝ × R × R → R} (hg : ContDiffAt ℝ n g (b, A, B)) (hu : IsUnit (g (b, A, B))) :
      ContDiffAt ℝ n (fun q ↦ Ring.inverse (g q)) (b, A, B) := by
    obtain ⟨u, hu⟩ := hu
    have hi := contDiffAt_ringInverse (n := n) ℝ u
    rw [hu] at hi
    exact hi.comp _ hg
  have hA : ContDiffAt ℝ n (fun q : ℝ × R × R ↦ q.2.1) (b, A, B) :=
    contDiffAt_fst.comp _ contDiffAt_snd
  have hB : ContDiffAt ℝ n (fun q : ℝ × R × R ↦ q.2.2) (b, A, B) :=
    contDiffAt_snd.comp _ contDiffAt_snd
  have hAB := hA.mul hB
  have hC : ContDiffAt ℝ n (fun q : ℝ × R × R ↦ cayleyFormula q.2.1 q.2.2) (b, A, B) :=
    ((contDiffAt_const.add hAB).mul (hinv (contDiffAt_const.sub hAB) h₁)).neg
  have hbC := contDiffAt_fst.smul hC
  exact (hA.mul (contDiffAt_const.add hbC)).mul (hinv (contDiffAt_const.sub hbC) h₂)

end Formula

/-! ### The linear Cayley path in operator-norm coordinates -/

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ J₁ : AlmostComplexStructure V} {A B : V →L[ℝ] V}

/-- For two tame structures, `1 - J₀ J₁` is invertible among continuous endomorphisms. -/
private theorem Tames.isUnit_one_sub_mul_of_toLinearMap (h₀ : ω.Tames J₀) (h₁ : ω.Tames J₁)
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J₁.toLinearMap) :
    IsUnit (1 - A * B) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  simpa [hA, hB] using h₀.isUnit_one_sub_mul h₁

/-- In operator-norm coordinates, the Cayley transform is the rational expression
`-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` of the continuous endomorphisms `J₀` and `J₁`. -/
private theorem Tames.toContinuousLinearMap_cayley (h₀ : ω.Tames J₀) (h₁ : ω.Tames J₁)
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap (J₀.cayley J₁) = cayleyFormula A B := by
  apply ContinuousLinearMap.coe_injective
  have hinv := (h₀.isUnit_one_sub_mul_of_toLinearMap h₁ hA hB).map_ringInverse
    (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ))
  simp only [ContinuousLinearMap.toLinearMapRingHom_apply, map_sub, map_one, map_mul] at hinv
  rw [cayleyFormula, ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_mul,
    hinv]
  simp [AlmostComplexStructure.cayley_def, hA, hB]

/-- In operator-norm coordinates, the compatible Cayley path from `J₀` to `J₁` at time `t` is
`J₀ (1 + β C)(1 - β C)⁻¹`, where `C` is the Cayley coordinate of `J₁` and
`β = smoothTransition t`. -/
private theorem Compatible.toContinuousLinearMap_cayleyPath (h₀ : ω.Compatible J₀)
    (h₁ : ω.Compatible J₁) (t : ℝ) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap (h₀.cayleyPath h₁ t).toLinearMap =
      cayleyPathFormula (smoothTransition t) A B := by
  let C : V →L[ℝ] V := smoothTransition t • LinearMap.toContinuousLinearMap (J₀.cayley J₁)
  have hC : C.toLinearMap ∈ ω.compatibleCayleyBall J₀ := by
    simpa only [C, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]
      using h₀.smul_cayley_mem_compatibleCayleyBall h₁
        ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩
  have hpath : h₀.cayleyPath h₁ t = (h₀.compatibleCayleyEquiv.symm ⟨C.toLinearMap, hC⟩).val := by
    rw [h₀.cayleyPath_eq_compatibleCayleyEquiv_symm h₁ t]
    simp only [C, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]
  have hA' : LinearMap.toContinuousLinearMap J₀.toLinearMap = A :=
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hA])
  rw [hpath, h₀.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap C hC, cayleyPathFormula,
    ← h₀.tames.toContinuousLinearMap_cayley h₁.tames hA hB, hA']

/-- At every time, the denominator `1 - β C` of the compatible Cayley path is invertible. -/
private theorem Compatible.isUnit_one_sub_smul_cayleyFormula (h₀ : ω.Compatible J₀)
    (h₁ : ω.Compatible J₁) (t : ℝ) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J₁.toLinearMap) :
    IsUnit (1 - smoothTransition t • cayleyFormula A B) := by
  rw [← h₀.tames.toContinuousLinearMap_cayley h₁.tames hA hB]
  refine isUnit_one_sub_of_toLinearMap_mem_cayleyBall (ω := ω) (J₀ := J₀)
    (compatibleCayleyBall_subset_cayleyBall ?_)
  simpa only [ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap] using
    h₀.smul_cayley_mem_compatibleCayleyBall h₁
      ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩

end SymplecticForm

/-! ### The Cayley path of smooth compatible structures -/

namespace SmoothTwoForm.Compatible

open scoped ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ J₁ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (h₁ : σ.Compatible J₁)

/-- The pointwise compatible Cayley path at `x`. The tangent space `T_x M` is the model space
`E`, which carries the norm required by the linear Cayley path; `TangentSpace I x` itself has no
norm instance, so the path is formed on `E`. -/
private def cayleyPathAt (t : ℝ) (x : M) : AlmostComplexStructure E :=
  SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x) (h₁.compatibleAt x) t

/-- The pointwise compatible Cayley path at `x`, as a continuous endomorphism of `T_x M`. -/
private def cayleyPathEnd (t : ℝ) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap (cayleyPathAt h₀ h₁ t x).toLinearMap

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
      (h₀.compatibleAt x₀) (h₁.compatibleAt x₀) p₀.1
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
    -- The endomorphism at `x` is the pointwise path `cayleyPathAt`, which squares to `-1`.
    exact (cayleyPathAt h₀ h₁ t x).apply_apply v

/-- At each point, the path is the pointwise compatible Cayley path. -/
private theorem almostComplexStructureAt_cayleyPath (t : ℝ) (x : M) :
    (h₀.cayleyPath h₁ t).almostComplexStructureAt x = cayleyPathAt h₀ h₁ t x :=
  AlmostComplexStructure.toLinearMap_injective <| by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    exact LinearMap.coe_toContinuousLinearMap _

/-- A smooth almost complex structure agreeing with the pointwise path at every point is the
path. -/
private theorem cayleyPath_eq_of_forall {t : ℝ} {J : SmoothAlmostComplexStructure I M}
    (h : ∀ x, cayleyPathAt h₀ h₁ t x = J.almostComplexStructureAt x) :
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

end SmoothTwoForm.Compatible

end TauCeti
