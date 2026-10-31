/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.AlmostComplexType
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.Topology.Algebra.Module.Alternating.BaseChange
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The `(p,q)` type of complex-valued smooth forms on an almost complex manifold

Let `J` be a smooth almost complex structure on a manifold `M` and let `F` be a complex normed
space. This file decomposes the complex-valued smooth forms `SmoothForm I M F k` into their
components of type `(p,q)`, `p + q = k`, by applying the fibrewise type decomposition of
`TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType` in every tangent space.

A smooth endomorphism field `A` of the tangent bundle acts on complex-valued forms as the
derivation `ContMDiffSection.alternatingDerivation A`, which is
`ContinuousLinearMap.alternatingDerivation (A x)` in the fibre at `x`. In bundle coordinates this
derivation is a continuous bilinear expression in the coordinates of `A` and of the form, namely
Mathlib's derivative `ContinuousAlternatingMap.fderivCompContinuousLinearMap` of pullback at the
identity, so it preserves smoothness. A form has type `(p,q)` for `J`
(`TauCeti.SmoothForm.IsOfType`) when `p + q = k` and the derivation of `J` acts on it as
multiplication by `(p - q) * I`; equivalently, `p + q = k` and its value at every point has type
`(p,q)` for the almost complex structure of that tangent space. A one-form has type `(1,0)`
exactly when its complex-linear extension to the complexified tangent space vanishes on the vectors
of type `(0,1)` (the `-i`-eigenvectors of the complexification of `J`) at every point, and type
`(0,1)` exactly when it vanishes on the vectors of type `(1,0)`.

The type projections `TauCeti.SmoothAlmostComplexStructure.typeProjection J p q` are the fibrewise
type polynomials evaluated at the derivation of `J`. Hence they are complex-linear endomorphisms
of the space of smooth forms, given at every point by the fibrewise type projections. They are
complementary idempotents summing to the identity, whose ranges are the forms of each type.
They commute with complex-linear coefficient maps and with pullback along pseudoholomorphic smooth
maps, while conjugate-linear coefficient maps, such as complex conjugation of complex-valued
forms, exchange the types `(p,q)` and `(q,p)`.

The exterior derivative of a form of type `(p,q)` has components of the four types `(p+2,q-1)`,
`(p+1,q)`, `(p,q+1)` and `(p-1,q+2)` only. This is the pointwise statement
`ContinuousAlternatingMap.IsOfType.typeProjection_alternatizeUncurryFin_eq_zero` applied in charts,
and it holds at boundary and corner points as well.

## Main declarations

* `IsSmoothForm.alternatingDerivation`: the derivation along a `C^n` endomorphism field preserves
  `C^n` forms.
* `ContMDiffSection.alternatingDerivation`: the derivation of smooth forms along a smooth
  endomorphism field of the tangent bundle.
* `TauCeti.SmoothForm.IsOfType`: a smooth form has type `(p,q)`.
* `TauCeti.SmoothAlmostComplexStructure.typeProjection`: the projection onto smooth forms of type
  `(p,q)`.
* `TauCeti.SmoothAlmostComplexStructure.sum_typeProjection`,
  `TauCeti.SmoothAlmostComplexStructure.typeProjection_eq_of_sum_eq`: existence and uniqueness of
  the type decomposition.
* `TauCeti.SmoothForm.isOfType_one_zero_iff_eigenspace_le_ker`,
  `TauCeti.SmoothForm.isOfType_zero_one_iff_eigenspace_le_ker`: one-forms of type `(1,0)` and
  `(0,1)` through their complex-linear extensions to the complexified tangent spaces.
* `TauCeti.SmoothAlmostComplexStructure.mapCoeff_typeProjection_of_map_smul_conj`: conjugation.
* `TauCeti.SmoothAlmostComplexStructure.mpullback_typeProjection`: pullback along
  pseudoholomorphic maps.
* `TauCeti.SmoothForm.IsOfType.typeProjection_mextDerivₗ_eq_zero`,
  `TauCeti.SmoothForm.IsOfType.mextDerivₗ_eq_typeProjection_add`: the exterior derivative of a form
  of type `(p,q)` splits into its four bidegrees.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.2 and 2.6.
-/

public section

noncomputable section

open Bundle Polynomial
open scoped ContDiff Manifold Topology ComplexConjugate

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

namespace TauCeti

variable [IsManifold I 1 M]

/-- In the trivialization of the tangent bundle at `x₀`, the coordinates of the derivation of a
form along an endomorphism field are the derivative of pullback at the identity, applied to the
coordinates of the form in the direction of the coordinates of the endomorphism. -/
theorem inCoordinates_alternatingDerivation
    (A : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x) (φ : RoughForm I M F k) (x₀ y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F x₀ y x₀ y ((A y).alternatingDerivation (φ y)) =
      (ContinuousAlternatingMap.inCoordinates E F x₀ y x₀ y (φ y)).fderivCompContinuousLinearMap
        (.id ℝ E) (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          x₀ y x₀ y (A y)) := by
  rw [← ContinuousLinearMap.alternatingDerivation_eq_fderivCompContinuousLinearMap]
  simp only [ContinuousAlternatingMap.inCoordinates]
  rw [← ContinuousLinearMap.alternatingDerivation_compContinuousAlternatingMap]
  refine (ContinuousLinearMap.alternatingDerivation_compContinuousLinearMap (fun w ↦ ?_) _).symm
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact (Trivialization.symmL_continuousLinearMapAt _ hy _).symm

/-- The derivation of a `C^n` form along a `C^n` endomorphism field of the tangent bundle is
`C^n`, within an arbitrary set. -/
theorem _root_.ContMDiffWithinAt.alternatingDerivation_form {n : WithTop ℕ∞} {s : Set M} {x : M}
    {A : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x} {φ : RoughForm I M F k}
    (hA : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) s x)
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y ((A y).alternatingDerivation (φ y))) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hA
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ ⊢
  refine ⟨hφ.1, ?_⟩
  have h := ((ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM F
    (ContinuousLinearMap.id ℝ E) (ι := Fin k)).contDiff.comp_contMDiffWithinAt hφ.2).clm_apply hA.2
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates E F x y x y
      ((A y).alternatingDerivation (φ y))) =ᶠ[𝓝 x]
      (fun y ↦ (ContinuousAlternatingMap.inCoordinates E F x y x y
        (φ y)).fderivCompContinuousLinearMap (.id ℝ E)
          (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
            x y x y (A y))) := by
    filter_upwards [(trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
    exact inCoordinates_alternatingDerivation A φ x y hy
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- The derivation of a `C^n` form along a `C^n` endomorphism field of the tangent bundle is a
`C^n` form. -/
theorem IsSmoothForm.alternatingDerivation {n : WithTop ℕ∞}
    {A : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)))
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) :
    IsSmoothForm I n (fun y ↦ (A y).alternatingDerivation (φ y)) := by
  rw [isSmoothForm_def] at hφ ⊢
  exact fun y ↦ contMDiffWithinAt_univ.mp
    ((hA y).contMDiffWithinAt.alternatingDerivation_form (hφ y).contMDiffWithinAt)

end TauCeti

namespace ContMDiffSection

open TauCeti

variable [IsManifold I 1 M]

/-- A smooth endomorphism field `A` of the tangent bundle acts on complex-valued smooth forms as a
derivation, by `ContinuousLinearMap.alternatingDerivation` of `A x` in the fibre at each `x`. -/
def alternatingDerivation
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) :
    Module.End ℂ (SmoothForm I M F k) where
  toFun φ := ⟨fun x ↦ (A x).alternatingDerivation (φ.1 x),
    (φ.isSmoothForm.alternatingDerivation A.contMDiff).mem_smoothBundleForms⟩
  map_add' φ ψ := Subtype.ext <| funext fun x ↦ map_add _ (φ.1 x) (ψ.1 x)
  map_smul' c φ := Subtype.ext <| funext fun x ↦ map_smul _ c (φ.1 x)

variable (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)

/-- At every point, the derivation of smooth forms is the fibrewise derivation. -/
@[simp]
theorem coe_alternatingDerivation (φ : SmoothForm I M F k) :
    (A.alternatingDerivation φ).1 = fun x ↦ (A x).alternatingDerivation (φ.1 x) :=
  (rfl)

/-- Evaluation at a point intertwines every polynomial in the derivation of smooth forms with the
same polynomial in the fibrewise derivation. -/
theorem aeval_alternatingDerivation_apply (g : ℂ[X]) (φ : SmoothForm I M F k) (x : M) :
    (aeval A.alternatingDerivation g φ).1 x = aeval (A x).alternatingDerivation g (φ.1 x) := by
  let ev : SmoothForm I M F k →ₗ[ℂ] TangentSpace I x [⋀^Fin k]→L[ℝ] F :=
    { toFun φ := φ.1 x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (LinearMap.congr_fun (Polynomial.aeval_comp_eq_comp_aeval (σ := ev)
    (f := A.alternatingDerivation) (g := (A x).alternatingDerivation) (LinearMap.ext
    fun φ ↦ rfl) g) φ).symm

end ContMDiffSection

namespace TauCeti

variable [IsManifold I ∞ M]

/-! ### Forms of type `(p,q)` -/

namespace SmoothForm

variable {φ ψ : SmoothForm I M F k} {J : SmoothAlmostComplexStructure I M} {p q : ℕ}

/-- A complex-valued smooth `k`-form `φ` has type `(p,q)` for a smooth almost complex structure
`J` when `p + q = k` and the derivation induced by `J` acts on `φ` as multiplication by
`(p - q) * I`. -/
def IsOfType (φ : SmoothForm I M F k) (J : SmoothAlmostComplexStructure I M) (p q : ℕ) : Prop :=
  p + q = k ∧ J.toEndomorphism.alternatingDerivation φ = (((p : ℂ) - q) * Complex.I) • φ

theorem isOfType_iff : φ.IsOfType J p q ↔
    p + q = k ∧ J.toEndomorphism.alternatingDerivation φ = (((p : ℂ) - q) * Complex.I) • φ :=
  Iff.rfl

/-- A smooth form has type `(p,q)` exactly when `p + q = k` and its value at every point has
type `(p,q)` for the almost complex structure of that tangent space. -/
theorem isOfType_iff_forall : φ.IsOfType J p q ↔
    p + q = k ∧ ∀ x, (φ.1 x).IsOfType (J.toEndomorphism x) p q := by
  simp only [ContinuousAlternatingMap.isOfType_iff]
  refine ⟨fun h ↦ ⟨h.1, fun x ↦ ⟨h.1, congrArg (fun ψ : SmoothForm I M F k ↦ ψ.1 x) h.2⟩⟩,
    fun h ↦ ⟨h.1, Subtype.ext <| funext fun x ↦ (h.2 x).2⟩⟩

theorem IsOfType.add_eq (h : φ.IsOfType J p q) : p + q = k :=
  h.1

/-- The value of a form of type `(p,q)` at a point has type `(p,q)`. -/
theorem IsOfType.apply (h : φ.IsOfType J p q) (x : M) :
    (φ.1 x).IsOfType (J.toEndomorphism x) p q :=
  (isOfType_iff_forall.1 h).2 x

@[simp]
theorem isOfType_zero_iff : (0 : SmoothForm I M F k).IsOfType J p q ↔ p + q = k := by
  simp [isOfType_iff]

theorem IsOfType.add (h : φ.IsOfType J p q) (h' : ψ.IsOfType J p q) :
    (φ + ψ).IsOfType J p q :=
  ⟨h.1, by rw [map_add, h.2, h'.2, smul_add]⟩

theorem IsOfType.smul (h : φ.IsOfType J p q) (c : ℂ) : (c • φ).IsOfType J p q :=
  ⟨h.1, by rw [map_smul, h.2, smul_comm]⟩

/-- Every complex-valued smooth function, as a `0`-form, has type `(0,0)`. -/
theorem isOfType_zero_zero (φ : SmoothForm I M F 0) (J : SmoothAlmostComplexStructure I M) :
    φ.IsOfType J 0 0 :=
  isOfType_iff_forall.2 ⟨rfl, fun x ↦ (φ.1 x).isOfType_zero_zero _⟩

/-- A smooth one-form has type `(1,0)` exactly when it is complex-linear for `J` at every point. -/
theorem isOfType_one_zero_iff {α : SmoothForm I M F 1} :
    α.IsOfType J 1 0 ↔ ∀ x v, α.1 x ![J x v] = Complex.I • α.1 x ![v] := by
  simp only [isOfType_iff_forall, ContinuousAlternatingMap.isOfType_one_zero_iff, true_and]

/-- A smooth one-form has type `(0,1)` exactly when it is conjugate-linear for `J` at every
point. -/
theorem isOfType_zero_one_iff {α : SmoothForm I M F 1} :
    α.IsOfType J 0 1 ↔ ∀ x v, α.1 x ![J x v] = -Complex.I • α.1 x ![v] := by
  simp only [isOfType_iff_forall, ContinuousAlternatingMap.isOfType_zero_one_iff, true_and]

/-- A smooth one-form has type `(1,0)` exactly when, at every point, its complex-linear extension
vanishes on the complexified tangent vectors of type `(0,1)`. -/
theorem isOfType_one_zero_iff_eigenspace_le_ker {α : SmoothForm I M F 1} :
    α.IsOfType J 1 0 ↔ ∀ x, Module.End.eigenspace
      ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I) ≤
        LinearMap.ker ((α.1 x).liftBaseChangeFinOne ℂ) := by
  simp_rw [isOfType_one_zero_iff, ContinuousAlternatingMap.liftBaseChangeFinOne_def,
    AlmostComplexStructure.eigenspace_neg_I_le_ker_liftBaseChange_iff]
  simp [Matrix.vec_single_eq_const]

/-- A smooth one-form has type `(0,1)` exactly when, at every point, its complex-linear extension
vanishes on the complexified tangent vectors of type `(1,0)`. -/
theorem isOfType_zero_one_iff_eigenspace_le_ker {α : SmoothForm I M F 1} :
    α.IsOfType J 0 1 ↔ ∀ x, Module.End.eigenspace
      ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I ≤
        LinearMap.ker ((α.1 x).liftBaseChangeFinOne ℂ) := by
  simp_rw [isOfType_zero_one_iff, ContinuousAlternatingMap.liftBaseChangeFinOne_def,
    AlmostComplexStructure.eigenspace_I_le_ker_liftBaseChange_iff]
  simp [Matrix.vec_single_eq_const]

end SmoothForm

/-! ### The type projections -/

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M) {φ : SmoothForm I M F k} {p q p' q' : ℕ}

/-- The projection of complex-valued smooth `k`-forms onto the forms of type `(p,q)` for `J`. It
is the fibrewise type polynomial evaluated at the derivation induced by `J`, and it vanishes
unless `p + q = k`. -/
def typeProjection (p q : ℕ) : Module.End ℂ (SmoothForm I M F k) :=
  aeval J.toEndomorphism.alternatingDerivation (ContinuousLinearMap.typePolynomial k p q)

/-- At every point, the type projection of smooth forms is the fibrewise type projection. -/
@[simp]
theorem coe_typeProjection (p q : ℕ) (φ : SmoothForm I M F k) :
    (J.typeProjection p q φ).1 = fun x ↦ (J.toEndomorphism x).typeProjection p q (φ.1 x) := by
  funext x
  rw [typeProjection, ContMDiffSection.aeval_alternatingDerivation_apply,
    ContinuousLinearMap.typeProjection_eq_aeval]

private theorem square_neg_apply (x : M) (v : TangentSpace I x) :
    J.toEndomorphism x (J.toEndomorphism x v) = -v :=
  J.apply_apply x v

/-- Every complex-valued smooth form is the sum of its components of each type. -/
theorem sum_typeProjection (φ : SmoothForm I M F k) :
    ∑ pq ∈ Finset.antidiagonal k, J.typeProjection pq.1 pq.2 φ = φ := by
  refine Subtype.ext <| funext fun x ↦ ?_
  simp only [Submodule.coe_sum, Finset.sum_apply, coe_typeProjection,
    ContinuousLinearMap.sum_typeProjection]

/-- The type-`(p,q)` component of a smooth form has type `(p,q)`. -/
theorem isOfType_typeProjection (hpq : p + q = k) (φ : SmoothForm I M F k) :
    (J.typeProjection p q φ).IsOfType J p q :=
  SmoothForm.isOfType_iff_forall.2 ⟨hpq, fun x ↦ by
    simpa only [coe_typeProjection] using
      ContinuousLinearMap.isOfType_typeProjection (J.square_neg_apply x) hpq (φ.1 x)⟩

/-- The type-`(p,q)` projection of smooth `k`-forms vanishes unless `p + q = k`. -/
@[simp]
theorem typeProjection_eq_zero (hpq : p + q ≠ k) :
    (J.typeProjection p q : Module.End ℂ (SmoothForm I M F k)) = 0 := by
  ext φ x : 3
  simp [ContinuousLinearMap.typeProjection_eq_zero (J.square_neg_apply x) hpq]

/-- The type projections of smooth forms are complementary idempotents. -/
@[simp]
theorem typeProjection_typeProjection (φ : SmoothForm I M F k) :
    J.typeProjection p' q' (J.typeProjection p q φ) =
      if (p', q') = (p, q) then J.typeProjection p q φ else 0 := by
  refine Subtype.ext <| funext fun x ↦ ?_
  split_ifs with h <;>
  simp [ContinuousLinearMap.typeProjection_typeProjection (J.square_neg_apply x), h]

end SmoothAlmostComplexStructure

namespace SmoothForm

open SmoothAlmostComplexStructure

variable {φ : SmoothForm I M F k} {J : SmoothAlmostComplexStructure I M} {p q p' q' : ℕ}

/-- The projection onto type `(p,q)` fixes the smooth forms of type `(p,q)`. -/
@[simp]
theorem IsOfType.typeProjection_self (h : φ.IsOfType J p q) : J.typeProjection p q φ = φ :=
  Subtype.ext <| funext fun x ↦ by simp [(h.apply x).typeProjection_self]

/-- The projection onto any other type annihilates the smooth forms of type `(p,q)`. -/
theorem IsOfType.typeProjection_of_ne (h : φ.IsOfType J p q) (hne : (p', q') ≠ (p, q)) :
    J.typeProjection p' q' φ = 0 :=
  Subtype.ext <| funext fun x ↦ by simp [(h.apply x).typeProjection_of_ne hne]

/-- A smooth form of two different types vanishes. -/
theorem IsOfType.eq_zero_of_ne (h : φ.IsOfType J p q) (h' : φ.IsOfType J p' q')
    (hne : (p, q) ≠ (p', q')) : φ = 0 := by
  rw [← h.typeProjection_self, h'.typeProjection_of_ne hne]

/-- A smooth form has type `(p,q)` exactly when `p + q = k` and its type-`(p,q)` component is the
whole form. -/
theorem isOfType_iff_typeProjection_eq :
    φ.IsOfType J p q ↔ p + q = k ∧ J.typeProjection p q φ = φ :=
  ⟨fun h ↦ ⟨h.1, h.typeProjection_self⟩,
    fun ⟨hpq, h⟩ ↦ h ▸ J.isOfType_typeProjection hpq φ⟩

/-- The components of a sum of smooth forms of each type are its type components. -/
theorem typeProjection_eq_of_sum_eq {η : ℕ × ℕ → SmoothForm I M F k}
    (hη : ∀ pq ∈ Finset.antidiagonal k, (η pq).IsOfType J pq.1 pq.2)
    (hφ : ∑ pq ∈ Finset.antidiagonal k, η pq = φ) (hpq : p + q = k) :
    J.typeProjection p q φ = η (p, q) := by
  rw [← hφ, map_sum, Finset.sum_eq_single (p, q)]
  · exact (hη (p, q) (by simpa using hpq)).typeProjection_self
  · intro pq hpq' hne
    exact (hη pq hpq').typeProjection_of_ne (Ne.symm hne)
  · intro h
    exact absurd (by simpa using hpq) h

/-- For a form `φ` of type `(p,q)` and a family `f` vanishing at `0`, the sum over all types of `f`
applied to the type components of `φ` reduces to its `(p,q)` term. -/
theorem IsOfType.sum_typeProjection_eq {G : Type*} [AddCommMonoid G]
    (h : φ.IsOfType J p q) (f : ℕ × ℕ → SmoothForm I M F k → G)
    (hf : ∀ pq, f pq 0 = 0) :
    ∑ pq ∈ Finset.antidiagonal k, f pq (J.typeProjection pq.1 pq.2 φ) = f (p, q) φ := by
  rw [Finset.sum_eq_single (p, q), h.typeProjection_self]
  · intro pq _ hne
    rw [h.typeProjection_of_ne hne, hf]
  · intro hpq
    exact absurd (by simpa using h.add_eq) hpq

end SmoothForm

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-- Type projection commutes with transport across an equality of form degrees. -/
theorem typeProjection_cast {l : ℕ} (h : k = l) (p q : ℕ) (φ : SmoothForm I M F k) :
    J.typeProjection p q
        (LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F n) h φ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F n) h
        (J.typeProjection p q φ) := by
  subst l
  rfl

/-- On one-forms, the type-`(1,0)` projection sends `α` to `(α - I • α ∘ J) / 2`. -/
theorem typeProjection_one_zero :
    (J.typeProjection 1 0 : Module.End ℂ (SmoothForm I M F 1)) =
      (2 : ℂ)⁻¹ • (1 - Complex.I • J.toEndomorphism.alternatingDerivation) := by
  ext α x : 3
  simp [ContinuousLinearMap.typeProjection_one_zero]

/-- On one-forms, the type-`(0,1)` projection sends `α` to `(α + I • α ∘ J) / 2`. -/
theorem typeProjection_zero_one :
    (J.typeProjection 0 1 : Module.End ℂ (SmoothForm I M F 1)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • J.toEndomorphism.alternatingDerivation) := by
  ext α x : 3
  simp [ContinuousLinearMap.typeProjection_zero_one]

/-- A smooth one-form is the sum of its components of types `(1,0)` and `(0,1)`. -/
theorem typeProjection_one_zero_add_zero_one (α : SmoothForm I M F 1) :
    J.typeProjection 1 0 α + J.typeProjection 0 1 α = α := by
  conv_rhs => rw [← J.sum_typeProjection α]
  simp [Finset.Nat.sum_antidiagonal_succ, add_comm]

end SmoothAlmostComplexStructure

/-! ### Coefficient maps and pullback -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [IsManifold I ∞ M] in
/-- At every point, a coefficient map of a rough form composes its value with the map. -/
private theorem mapCoeff_eq_compContinuousAlternatingMap (L : F →L[ℝ] G) (φ : RoughForm I M F k)
    (x : M) : RoughForm.mapCoeff L φ x = L.compContinuousAlternatingMap (φ x) := by
  ext v
  simp

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M) {p q : ℕ}

/-- A complex-linear coefficient map commutes with the type projections of smooth forms. -/
theorem mapCoeff_typeProjection {L : F →L[ℝ] G} (hL : ∀ (c : ℂ) v, L (c • v) = c • L v)
    (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.typeProjection p q φ) =
      J.typeProjection p q (SmoothForm.mapCoeff L φ) :=
  Subtype.ext <| funext fun x ↦ by
    simp [mapCoeff_eq_compContinuousAlternatingMap,
      ContinuousLinearMap.typeProjection_compContinuousAlternatingMap hL]

/-- A conjugate-linear coefficient map, such as complex conjugation, sends the type-`(p,q)`
component of a smooth form to the type-`(q,p)` component of its image. -/
theorem mapCoeff_typeProjection_of_map_smul_conj {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) v, L (c • v) = conj c • L v) (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.typeProjection p q φ) =
      J.typeProjection q p (SmoothForm.mapCoeff L φ) :=
  Subtype.ext <| funext fun x ↦ by
    simp [mapCoeff_eq_compContinuousAlternatingMap,
      ContinuousLinearMap.typeProjection_compContinuousAlternatingMap_of_map_smul_conj hL]

end SmoothAlmostComplexStructure

namespace SmoothForm

variable {φ : SmoothForm I M F k} {J : SmoothAlmostComplexStructure I M} {p q : ℕ}

/-- A complex-linear coefficient map preserves the type of smooth forms. -/
theorem IsOfType.mapCoeff {L : F →L[ℝ] G} (hL : ∀ (c : ℂ) v, L (c • v) = c • L v)
    (h : φ.IsOfType J p q) : (mapCoeff L φ).IsOfType J p q :=
  isOfType_iff_forall.2 ⟨h.1, fun x ↦ by
    rw [coe_mapCoeff, mapCoeff_eq_compContinuousAlternatingMap]
    exact (h.apply x).compContinuousAlternatingMap hL⟩

/-- A conjugate-linear coefficient map, such as complex conjugation, exchanges the types `(p,q)`
and `(q,p)` of smooth forms. -/
theorem IsOfType.mapCoeff_of_map_smul_conj {L : F →L[ℝ] G}
    (hL : ∀ (c : ℂ) v, L (c • v) = conj c • L v) (h : φ.IsOfType J p q) :
    (SmoothForm.mapCoeff L φ).IsOfType J q p :=
  isOfType_iff_forall.2 ⟨by rw [add_comm, h.1], fun x ↦ by
    rw [coe_mapCoeff, mapCoeff_eq_compContinuousAlternatingMap]
    exact (h.apply x).compContinuousAlternatingMap_of_map_smul_conj hL⟩

end SmoothForm

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {J : SmoothAlmostComplexStructure I M} {J' : SmoothAlmostComplexStructure I' M'} {u : M → M'}
  {p q : ℕ}

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- At every point, the pullback of a rough form composes its value with the derivative. -/
private theorem mpullback_eq_compContinuousLinearMap (φ : RoughForm I' M' F k) (x : M) :
    mpullback I I' u φ x = (φ (u x)).compContinuousLinearMap (mfderiv I I' u x) := by
  ext v
  simp [Function.comp_def]

/-- Pullback of smooth forms along a smooth pseudoholomorphic map commutes with the type
projections. -/
theorem SmoothAlmostComplexStructure.mpullback_typeProjection (hu : ContMDiff I I' ∞ u)
    (hJ : IsPseudoholomorphic J J' u) (φ : SmoothForm I' M' F k) :
    SmoothForm.mpullback u hu (J'.typeProjection p q φ) =
      J.typeProjection p q (SmoothForm.mpullback u hu φ) :=
  Subtype.ext <| funext fun x ↦ by
    simp only [SmoothForm.coe_mpullback, coe_typeProjection, mpullback_eq_compContinuousLinearMap]
    exact (ContinuousLinearMap.typeProjection_compContinuousLinearMap
      (fun w ↦ ((isPseudoholomorphic_iff.1 hJ x).mfderiv_apply_commute w).symm) _).symm

/-- Pullback along a smooth pseudoholomorphic map preserves the type of smooth forms. -/
theorem SmoothForm.IsOfType.mpullback {φ : SmoothForm I' M' F k} (hu : ContMDiff I I' ∞ u)
    (hJ : IsPseudoholomorphic J J' u) (h : φ.IsOfType J' p q) :
    (SmoothForm.mpullback u hu φ).IsOfType J p q :=
  SmoothForm.isOfType_iff_forall.2 ⟨h.1, fun x ↦ by
    rw [SmoothForm.coe_mpullback, mpullback_eq_compContinuousLinearMap]
    exact (h.apply (u x)).compContinuousLinearMap fun w ↦
      ((isPseudoholomorphic_iff.1 hJ x).mfderiv_apply_commute w).symm⟩

/-! ### The four bidegrees of the exterior derivative -/

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M) (x : M)

/-- The almost complex structure read in the trivialization of the tangent bundle at `x`, along
the inverse of the extended chart at `x`. -/
private def inChart (z : E) : E →L[ℝ] E :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x
    ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
      (J.toEndomorphism ((extChartAt I x).symm z))

private theorem mem_baseSet_of_mem_target {z : E} (hz : z ∈ (extChartAt I x).target) :
    (extChartAt I x).symm z ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  exact (extChartAt I x).map_target hz

/-- In the chart, the almost complex structure still squares to `-1`. -/
private theorem inChart_inChart {z : E} (hz : z ∈ (extChartAt I x).target) (w : E) :
    J.inChart x z (J.inChart x z w) = -w := by
  simp only [inChart, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt _ (mem_baseSet_of_mem_target x hz),
    J.square_neg_apply, map_neg,
    Trivialization.continuousLinearMapAt_symmL _ (mem_baseSet_of_mem_target x hz)]

/-- At the chart point, the almost complex structure read in the chart is `J x`. -/
private theorem inChart_extChartAt_self : J.inChart x (extChartAt I x x) = J.toEndomorphism x := by
  simp only [inChart]
  rw [extChartAt_to_inv]
  ext w
  simp only [ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source H x),
    TangentBundle.symmL_trivializationAt (mem_chart_source H x), mfderiv_extChartAt_self,
    mfderivWithin_range_extChartAt_symm]
  -- Both chart derivatives are identities of tangent spaces that are definitionally `E`.
  rfl

private theorem differentiableWithinAt_inChart :
    DifferentiableWithinAt ℝ (J.inChart x) (Set.range I) (extChartAt I x x) := by
  have h := ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff x)).2
  have h' := h.comp_contMDiffWithinAt_of_eq (contMDiffWithinAt_extChartAt_symm_range_self x)
    (extChartAt_to_inv x)
  exact (contMDiffWithinAt_iff_contDiffWithinAt.1 h').differentiableWithinAt (by simp)

/-- Differentiating `J² = -1` in the chart at `x`: the derivative of the almost complex structure
read in the chart anticommutes with its value at the chart point. -/
private theorem fderivWithin_inChart_apply_apply (v w : E) :
    fderivWithin ℝ (J.inChart x) (Set.range I) (extChartAt I x x) v
        (J.inChart x (extChartAt I x x) w) =
      -J.inChart x (extChartAt I x x)
        (fderivWithin ℝ (J.inChart x) (Set.range I) (extChartAt I x x) v w) := by
  have hd := (J.differentiableWithinAt_inChart x).hasFDerivWithinAt
  have heq : (fun z ↦ J.inChart x z ∘L J.inChart x z) =ᶠ[𝓝[Set.range I] extChartAt I x x]
      fun _ ↦ -ContinuousLinearMap.id ℝ E := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    ext w
    simp [J.inChart_inChart x hz]
  have h := (I.uniqueDiffOn.uniqueDiffWithinAt (Set.mem_range_self _)).eq
    ((hd.clm_comp hd).congr_of_eventuallyEq heq.symm
      (heq.symm.eq_of_nhdsWithin (Set.mem_range_self _))) (hasFDerivWithinAt_const _ _ _)
  have hvw := congrArg (fun L ↦ L v w) h
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    zero_apply] at hvw
  exact eq_neg_of_add_eq_zero_right hvw

end SmoothAlmostComplexStructure

namespace SmoothForm

variable {J : SmoothAlmostComplexStructure I M} {φ : SmoothForm I M F k} {p q P Q : ℕ}

/-- In the chart at `x`, the coordinate expression of a form of type `(p,q)` satisfies the type
equation for the almost complex structure read in the chart. -/
private theorem IsOfType.fderivCompContinuousLinearMap_inChartAt (hφ : φ.IsOfType J p q)
    (x : M) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (RoughForm.inChartAt φ.1 x z).fderivCompContinuousLinearMap (.id ℝ E) (J.inChart x z) =
      (((p : ℂ) - q) * Complex.I) • RoughForm.inChartAt φ.1 x z := by
  have hy := (extChartAt I x).map_target hz
  have h₁ := inCoordinates_alternatingDerivation (fun y ↦ J.toEndomorphism y) φ.1 x _
    (SmoothAlmostComplexStructure.mem_baseSet_of_mem_target x hz)
  have h₂ := RoughForm.inCoordinates_eq_inChartAt ((((p : ℂ) - q) * Complex.I) • φ.1) hy
  have h₃ := RoughForm.inCoordinates_eq_inChartAt φ.1 hy
  rw [(hφ.apply _).alternatingDerivation_eq] at h₁
  rw [RoughForm.inChartAt_smul] at h₂
  simp only [Pi.smul_apply, (extChartAt I x).right_inv hz] at h₂
  rw [(extChartAt I x).right_inv hz] at h₃
  rw [h₃] at h₁
  exact h₁.symm.trans h₂

/-- At each point `x`, the exterior derivative of a smooth form of type `(p,q)` has no component
of type `(P,Q)` for `J x` unless `P - p ∈ {-1, 0, 1, 2}`. -/
private theorem IsOfType.typeProjection_mextDeriv_apply_eq_zero (hφ : φ.IsOfType J p q)
    (x : M) (hP : P + 1 < p ∨ p + 2 < P) :
    (J.toEndomorphism x).typeProjection P Q (mextDeriv φ.1 x) = 0 := by
  -- Differentiating the type equation of `φ` in the chart at `x`, and differentiating `J² = -1`,
  -- gives a first-order variation of the pair `(φ x, J x)` preserving type. Its alternation is
  -- the exterior derivative of `φ` at `x`, so the fibrewise theorem applies.
  set z₀ := extChartAt I x x
  have hd : DifferentiableWithinAt ℝ (RoughForm.inChartAt φ.1 x) (Set.range I) z₀ :=
    (φ.isSmoothForm.contDiffWithinAt_inChartAt_self x).differentiableWithinAt (by simp)
  set η := fderivWithin ℝ (RoughForm.inChartAt φ.1 x) (Set.range I) z₀
  set A := fderivWithin ℝ (J.inChart x) (Set.range I) z₀
  have hη (v : E) : (J.inChart x z₀).alternatingDerivation (η v) +
      (A v).alternatingDerivation (RoughForm.inChartAt φ.1 x z₀) =
        (((p : ℂ) - q) * Complex.I) • η v := by
    let G := ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM F
      (ContinuousLinearMap.id ℝ E) (ι := Fin k)
    have heq : (fun z ↦ G (RoughForm.inChartAt φ.1 x z) (J.inChart x z)) =ᶠ[𝓝[Set.range I] z₀]
        fun z ↦ (((p : ℂ) - q) * Complex.I) • RoughForm.inChartAt φ.1 x z := by
      filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz using
        hφ.fderivCompContinuousLinearMap_inChartAt x hz
    have h := (I.uniqueDiffOn.uniqueDiffWithinAt (Set.mem_range_self _)).eq
      ((G.hasFDerivWithinAt_of_bilinear hd.hasFDerivWithinAt
        (J.differentiableWithinAt_inChart x).hasFDerivWithinAt).congr_of_eventuallyEq heq.symm
          (heq.symm.eq_of_nhdsWithin (Set.mem_range_self _)))
        (hd.hasFDerivWithinAt.const_smul (((p : ℂ) - q) * Complex.I))
    have hv := congrArg (fun L ↦ L v) h
    simp only [add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, smul_apply, G,
      ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM_apply,
      ← ContinuousLinearMap.alternatingDerivation_eq_fderivCompContinuousLinearMap] at hv
    rw [add_comm]
    exact hv
  have hφ₀ : (RoughForm.inChartAt φ.1 x z₀).IsOfType (J.inChart x z₀) p q := by
    rw [RoughForm.inChartAt_extChartAt_self, J.inChart_extChartAt_self]
    exact hφ.apply x
  rw [mextDeriv_def, extDerivWithin, ← J.inChart_extChartAt_self x]
  exact hφ₀.typeProjection_alternatizeUncurryFin_eq_zero
    (J.inChart_inChart x (mem_extChartAt_target x)) (J.fderivWithin_inChart_apply_apply x) hη hP

/-- The exterior derivative of a smooth form of type `(p,q)` has no component of type `(P,Q)`
unless `P - p ∈ {-1, 0, 1, 2}`. -/
theorem IsOfType.typeProjection_mextDerivₗ_eq_zero (hφ : φ.IsOfType J p q)
    (hP : P + 1 < p ∨ p + 2 < P) : J.typeProjection P Q (mextDerivₗ I k φ) = 0 :=
  Subtype.ext <| funext fun x ↦ by
    simpa only [SmoothAlmostComplexStructure.coe_typeProjection, mextDerivₗ_apply,
      ZeroMemClass.coe_zero, Pi.zero_apply] using
      hφ.typeProjection_mextDeriv_apply_eq_zero x hP

/-- **The four bidegrees of `d`.** The exterior derivative of a smooth form of type `(p,q)` is
the sum of its components of types `(p+2,q-1)`, `(p+1,q)`, `(p,q+1)` and `(p-1,q+2)`. When
`q = 0` (respectively `p = 0`) the first (respectively last) of these types has the wrong degree,
and the corresponding projection vanishes. -/
theorem IsOfType.mextDerivₗ_eq_typeProjection_add (hφ : φ.IsOfType J p q) :
    mextDerivₗ I k φ =
      J.typeProjection (p + 2) (q - 1) (mextDerivₗ I k φ) +
        J.typeProjection (p + 1) q (mextDerivₗ I k φ) +
          J.typeProjection p (q + 1) (mextDerivₗ I k φ) +
            J.typeProjection (p - 1) (q + 2) (mextDerivₗ I k φ) := by
  have hk := hφ.add_eq
  set S : Finset (ℕ × ℕ) := {(p + 2, q - 1), (p + 1, q), (p, q + 1), (p - 1, q + 2)}
  have hS : ∑ x ∈ S, J.typeProjection x.1 x.2 (mextDerivₗ I k φ) =
      J.typeProjection (p + 2) (q - 1) (mextDerivₗ I k φ) +
        J.typeProjection (p + 1) q (mextDerivₗ I k φ) +
          J.typeProjection p (q + 1) (mextDerivₗ I k φ) +
            J.typeProjection (p - 1) (q + 2) (mextDerivₗ I k φ) := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
      Finset.sum_pair (by simp)]
    abel
  rw [← hS]
  conv_lhs => rw [← J.sum_typeProjection (mextDerivₗ I k φ)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := S)),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := Finset.antidiagonal (k + 1)))]
  · rintro ⟨P, Q⟩ hx hxS
    simp only [S, Finset.mem_union, Finset.mem_antidiagonal, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq] at hx hxS
    exact hφ.typeProjection_mextDerivₗ_eq_zero (by omega)
  · rintro ⟨P, Q⟩ _ hx
    rw [Finset.mem_antidiagonal] at hx
    simp [J.typeProjection_eq_zero hx]

end SmoothForm

end TauCeti
