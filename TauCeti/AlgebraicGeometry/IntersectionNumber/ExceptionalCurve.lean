/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Weight
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Exceptional curves of the first kind

An **exceptional curve of the first kind** on a scheme `X` is a closed subscheme `E ⊆ X` such that

* `E` is an effective Cartier divisor on `X`,
* `E` is isomorphic to the projective line `ℙ¹_κ` over some field `κ`, and
* the normal bundle `𝒪_X(E)|_E` is `𝒪_{ℙ¹_κ}(-1)`; equivalently, the conormal bundle
  `𝒪_X(-E)|_E`, the restriction of the ideal sheaf of `E`, is `𝒪_{ℙ¹_κ}(1)`.

These are the curves that Castelnuovo's criterion contracts to a regular point, and a regular
model of a curve over a discrete valuation ring is relatively minimal when its special fibre
contains none of them. The field `κ` is not part of the data: it is recovered as the field
`Γ(E, 𝒪_E)` of global functions on `E`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.isField_globalSections`).
The normal bundle condition is stated with the conormal bundle, the pullback of the invertible
sheaf `I` itself, because that is how Tau Ceti represents an effective Cartier divisor
(`AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf`). In terms of
intersection numbers it says `(E · E) = -1` over `κ`
(`AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_intersectionNumber`).

The numerical invariants of an exceptional curve do not depend on the chosen field: whenever `E`
is regarded as a scheme over a field `k`, for instance the residue field of a discrete valuation
ring through the special fibre of a model, then

* `E` has genus zero over its constant field, `dim_{Γ(E, 𝒪_E)} H¹(E, 𝒪_E) = 0`, and so
  `dim_k H¹(E, 𝒪_E) = 0`;
* its self-intersection over `k` is minus its weight, `(E · E) = -dim_k H⁰(E, 𝒪_E)`.

For a component `Cⱼ` of the special fibre of a regular model, these say that `j` is a
`(-1)`-index of the numerical type (`TauCeti.NumericalType.IsMinusOneIndex`): its genus over the
constant field is zero and its diagonal entry `aⱼⱼ` of the intersection matrix is `-wⱼ`
(`Scheme.Hom.specialFiberIntersectionMatrix_self_eq_neg_specialFiberWeight`).
This is the numerical shadow of an exceptional curve on which the combinatorial theory of minimal
numerical types rests.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`: the closed subscheme
  cut out by `I` is an exceptional curve of the first kind.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_intersectionNumber`:
  the normal bundle condition is the self-intersection `(E · E) = -1` over `κ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.isField_globalSections`:
  the global functions on `E` form a field.
* `IsExceptionalCurveOfFirstKind.finrank_globalSections_cohomology_one_trivial_eq_zero` and
  `IsExceptionalCurveOfFirstKind.finrank_cohomology_one_trivial_eq_zero`: `E` has genus zero.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.intersectionNumber_self`:
  `(E · E) = -dim_k H⁰(E, 𝒪_E)` over every field `k` over which `E` lies.
* `Scheme.Hom.specialFiberIntersectionMatrix_self_eq_neg_specialFiberWeight`: the
  corresponding diagonal entry of the intersection matrix of a regular model.

## References

* The Stacks Project, Chapter *Resolution of Surfaces*, the definition of exceptional curves of
  the first kind and Castelnuovo's contractibility criterion.
* [The Stacks Project, Tag 0C76](https://stacks.math.columbia.edu/tag/0C76): `(-1)`-indices of
  numerical types, the numerical counterpart of exceptional curves.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.3, on exceptional divisors and
  Castelnuovo's criterion on regular fibred surfaces.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open Module (finrank)

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The closed subscheme `E` cut out by the ideal sheaf `I` is an **exceptional curve of the first
kind**: `E` is an effective Cartier divisor, there is an isomorphism `e : ℙ¹_κ ≅ E` for some field
`κ`, and the conormal bundle `𝒪_X(-E)|_E` pulls back along `e` to the twisting sheaf `𝒪(1)`.
Dually, the normal bundle `𝒪_X(E)|_E` is `𝒪(-1)`. -/
structure IsExceptionalCurveOfFirstKind (I : X.IdealSheafData) : Prop where
  /-- An exceptional curve of the first kind is an effective Cartier divisor. -/
  isEffectiveCartier : I.IsEffectiveCartier
  /-- An exceptional curve of the first kind is a projective line whose conormal bundle is
  `𝒪(1)`. -/
  exists_iso : ∃ (κ : Type u) (_ : Field κ) (e : projectiveLine κ ≅ I.subscheme),
    Nonempty (((InvertibleSheaf.pullback (e.hom ≫ I.subschemeι)).obj
      isEffectiveCartier.toInvertibleSheaf).obj ≅
        Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)) 1)

/-- The conormal bundle of `E` is `𝒪(1)` along an isomorphism `e : ℙ¹_κ ≅ E` exactly when the
self-intersection of `E`, computed on `ℙ¹_κ` over `κ`, is `-1`. -/
private lemma nonempty_iso_twistingSheaf_iff_intersectionNumber {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) {κ : Type u} [Field κ] (e : projectiveLine κ ≅ I.subscheme) :
    Nonempty (((InvertibleSheaf.pullback (e.hom ≫ I.subschemeι)).obj
      hI.toInvertibleSheaf).obj ≅
        Proj.twistingSheaf (SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)) 1) ↔
      LineBundleClass.intersectionNumber κ (e.hom ≫ I.subschemeι)
        (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = -1 := by
  -- Degree is an additive isomorphism `Pic(ℙ¹_κ) ≃ ℤ`, so inverting a class negates its degree.
  have hinv (a : LineBundleClass (projectiveLine κ)) :
      LineBundleClass.eulerDegree κ a⁻¹ = -LineBundleClass.eulerDegree κ a := by
    simpa using map_neg (projectiveLine.picardDegreeEquiv κ) (Additive.ofMul a)
  rw [projectiveLine.nonempty_iso_twistingSheaf_iff, LineBundleClass.intersectionNumber_def,
    LineBundleClass.pullback_inv, LineBundleClass.pullback_mk, hinv,
    LineBundleClass.eulerDegree_mk, neg_inj]

/-- **Exceptional curves of the first kind by their self-intersection.** The closed subscheme `E`
cut out by `I` is an exceptional curve of the first kind exactly when it is an effective Cartier
divisor isomorphic, by some `e : ℙ¹_κ ≅ E`, to a projective line over a field `κ` on which the
normal bundle `𝒪_X(E)|_E` has degree `-1`, that is, `(E · E) = -1` over `κ`. -/
theorem isExceptionalCurveOfFirstKind_iff_intersectionNumber {I : X.IdealSheafData} :
    I.IsExceptionalCurveOfFirstKind ↔
      ∃ hI : I.IsEffectiveCartier, ∃ (κ : Type u) (_ : Field κ)
        (e : projectiveLine κ ≅ I.subscheme),
        LineBundleClass.intersectionNumber κ (e.hom ≫ I.subschemeι)
          (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = -1 := by
  refine ⟨fun ⟨hI, κ, _, e, he⟩ ↦ ⟨hI, κ, _, e, ?_⟩, fun ⟨hI, κ, _, e, he⟩ ↦ ⟨hI, κ, _, e, ?_⟩⟩
  · exact (nonempty_iso_twistingSheaf_iff_intersectionNumber hI e).mp he
  · exact (nonempty_iso_twistingSheaf_iff_intersectionNumber hI e).mpr he

namespace IsExceptionalCurveOfFirstKind

variable {I : X.IdealSheafData} (hE : I.IsExceptionalCurveOfFirstKind)
include hE

/-- **The constant field of an exceptional curve.** The global functions on an exceptional curve
of the first kind `E ≅ ℙ¹_κ` form a field, isomorphic to `κ`. -/
theorem isField_globalSections : IsField Γ(I.subscheme, ⊤) := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  have hκ : IsField Γ(projectiveLine κ, ⊤) :=
    MulEquiv.isField (Field.toIsField κ)
      (RingEquiv.ofBijective _
        (projectiveLine.bijective_baseRingToGlobalSections κ)).symm.toMulEquiv
  exact MulEquiv.isField hκ (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.toMulEquiv

/-- An exceptional curve of the first kind is quasi-compact. -/
theorem compactSpace : CompactSpace I.subscheme := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  exact QuasiCompact.compactSpace_of_compactSpace (e.inv ≫ (projectiveLine κ ↘ Spec (.of κ)))

/-- An exceptional curve of the first kind is quasi-separated. -/
theorem quasiSeparatedSpace : QuasiSeparatedSpace I.subscheme := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  exact quasiSeparatedSpace_of_quasiSeparated (e.inv ≫ (projectiveLine κ ↘ Spec (.of κ)))

/-- **An exceptional curve has genus zero over its constant field**:
`dim_{Γ(E, 𝒪_E)} H¹(E, 𝒪_E) = 0`. This is the genus `gᵢ` of a component of the numerical type of
a regular model. -/
theorem finrank_globalSections_cohomology_one_trivial_eq_zero :
    finrank Γ(I.subscheme, ⊤) (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  -- Regard `E` as a curve over `κ` through `e`, and compare with `ℙ¹_κ` over `κ`.
  let : I.subscheme.Over (Spec (.of κ)) := ⟨e.inv ≫ (projectiveLine κ ↘ Spec (.of κ))⟩
  -- This holds by the choice of the structure morphism.
  have he : e.inv ≫ (projectiveLine κ ↘ Spec (.of κ)) = I.subscheme ↘ Spec (.of κ) := rfl
  have h₀ : finrank κ (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) = 1 := by
    rw [finrank_cohomology_trivial_eq_of_isIso (k := κ) e.inv he 0,
      (projectiveLine.cohomologyZeroTrivialLinearEquiv κ).finrank_eq, Module.finrank_self]
  have h₁ : finrank κ (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 := by
    rw [finrank_cohomology_trivial_eq_of_isIso (k := κ) e.inv he 1]
    exact Module.finrank_zero_of_subsingleton
  have h := Scheme.Modules.finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul κ
    hE.isField_globalSections (InvertibleSheaf.trivial I.subscheme).obj 1
  rwa [h₀, h₁, one_mul, eq_comm] at h

variable (k : Type u) [Field k] [I.subscheme.Over (Spec (.of k))]

/-- **An exceptional curve has genus zero**: `dim_k H¹(E, 𝒪_E) = 0` over every field `k` over which
`E` lies. -/
theorem finrank_cohomology_one_trivial_eq_zero :
    finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 := by
  rw [Scheme.Modules.finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul k
    hE.isField_globalSections, hE.finrank_globalSections_cohomology_one_trivial_eq_zero, mul_zero]

/-- **The self-intersection of an exceptional curve is minus its weight.** Over every field `k`
over which an exceptional curve of the first kind `E` lies,
`(E · E) = deg_k 𝒪_X(E)|_E = -dim_k H⁰(E, 𝒪_E)`. -/
theorem intersectionNumber_self :
    LineBundleClass.intersectionNumber k I.subschemeι
        (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
      -(finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) : ℤ) := by
  obtain ⟨_, κ, _, e, he⟩ := isExceptionalCurveOfFirstKind_iff_intersectionNumber.mp hE
  rw [LineBundleClass.intersectionNumber_def] at he
  have := hE.compactSpace
  have := hE.quasiSeparatedSpace
  -- Regard `ℙ¹_κ` as a scheme over `k` through `e`, and compute there.
  let : (projectiveLine κ).Over (Spec (.of k)) := ⟨e.hom ≫ (I.subscheme ↘ Spec (.of k))⟩
  -- This holds by the choice of the structure morphism.
  have hek : e.hom ≫ (I.subscheme ↘ Spec (.of k)) = projectiveLine κ ↘ Spec (.of k) := rfl
  have hκ : IsField Γ(projectiveLine κ, ⊤) := MulEquiv.isField hE.isField_globalSections
    (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.symm.toMulEquiv
  have h := LineBundleClass.eulerDegree_mul_finrank_cohomology_zero_trivial (κ := κ) k hκ
    (LineBundleClass.pullback (e.hom ≫ I.subschemeι)
      (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf)⁻¹)
  rw [(projectiveLine.cohomologyZeroTrivialLinearEquiv κ).finrank_eq, Module.finrank_self,
    Nat.cast_one, mul_one, he, finrank_cohomology_trivial_eq_of_isIso (k := k) e.hom hek 0,
    ← LineBundleClass.pullback_comp,
    LineBundleClass.eulerDegree_pullback_of_isIso (k := k) e.hom hek] at h
  rw [LineBundleClass.intersectionNumber_def, h, mul_neg_one]

end IsExceptionalCurveOfFirstKind

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal
  isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular)

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]
  [TauCeti.AlgebraicGeometry.IsRegular X]

/-- **An exceptional component of the special fibre is a `(-1)`-component.** Let `X` be a regular
Noetherian integral scheme over a local ring `R` of dimension at most one, with all points of
codimension at most two and generic point away from the closed point. If the component `Cⱼ` of
the special fibre, with its reduced structure, is an exceptional curve of the first kind, then the
diagonal entry `aⱼⱼ = (Cⱼ · Cⱼ)` of the intersection matrix of the special fibre is minus the
weight `wⱼ = dim_k H⁰(Cⱼ, 𝒪_{Cⱼ})` over the residue field `k` of `R`. Together with
`IsExceptionalCurveOfFirstKind.finrank_globalSections_cohomology_one_trivial_eq_zero`, which
makes the genus of `Cⱼ` over its constant field zero, this is the condition of a `(-1)`-index of
the numerical type. -/
theorem specialFiberIntersectionMatrix_self_eq_neg_specialFiberWeight
    (hX : ∀ x : X, coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R)
    (j : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset)
    (hj : (vanishingIdeal ⟨closure {((j : CodimensionOnePoint X) : X)},
      isClosed_closure⟩).IsExceptionalCurveOfFirstKind) :
    toBase.specialFiberIntersectionMatrix hX hη j j =
      -(toBase.specialFiberWeight ((Set.Finite.mem_toFinset _).mp j.2) : ℤ) := by
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
    ((Set.Finite.mem_toFinset _).mp j.2))
  rw [specialFiberIntersectionMatrix_apply, specialFiberWeight_def]
  exact hj.intersectionNumber_self (ResidueField R)

end AlgebraicGeometry.Scheme.Hom
