/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
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

The cohomological and numerical invariants of an exceptional curve do not depend on the chosen
field:

* `E` is an integral curve, and its structure sheaf has no higher cohomology, `Hⁿ(E, 𝒪_E) = 0` for
  `n ≥ 1`; in particular `E` has genus zero over its constant field and over every field `k` over
  which `E` lies;
* whenever `E` is regarded as a scheme over a field `k`, for instance the residue field of a
  discrete valuation ring through the special fibre of a model, its self-intersection over `k` is
  minus its weight, `(E · E) = -dim_k H⁰(E, 𝒪_E)`, and the conormal bundle has degree
  `dim_k H⁰(E, 𝒪_E)`.

For a component `Cⱼ` of the special fibre of a regular model, these say that `j` is a
`(-1)`-index of the numerical type (`TauCeti.NumericalType.IsMinusOneIndex`); see
`TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SpecialFiber`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`: the closed subscheme
  cut out by `I` is an exceptional curve of the first kind.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_intersectionNumber`:
  the normal bundle condition is the self-intersection `(E · E) = -1` over `κ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.isField_globalSections`:
  the global functions on `E` form a field.
* `IsExceptionalCurveOfFirstKind.isIntegral_subscheme` and
  `IsExceptionalCurveOfFirstKind.topologicalKrullDim_subscheme`: `E` is an integral curve, so in
  particular `I ≠ ⊤` (`not_isExceptionalCurveOfFirstKind_top`).
* `AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_comap_iff_of_isIso`:
  being an exceptional curve of the first kind is invariant under isomorphisms of schemes.
* `IsExceptionalCurveOfFirstKind.subsingleton_cohomology_succ_trivial`: `Hⁿ(E, 𝒪_E) = 0` for
  `n ≥ 1`, with the genus-zero consequences
  `IsExceptionalCurveOfFirstKind.finrank_globalSections_cohomology_one_trivial_eq_zero` and
  `IsExceptionalCurveOfFirstKind.finrank_cohomology_one_trivial_eq_zero`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.intersectionNumber_self`:
  `(E · E) = -dim_k H⁰(E, 𝒪_E)` over every field `k` over which `E` lies, and
  `IsExceptionalCurveOfFirstKind.intersectionNumber_mk_toInvertibleSheaf`: the conormal bundle
  has degree `dim_k H⁰(E, 𝒪_E)`.

## References

* The Stacks Project, Chapter *Resolution of Surfaces*, the definition of exceptional curves of
  the first kind and Castelnuovo's contractibility criterion.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.3, on exceptional divisors and
  Castelnuovo's criterion on regular fibred surfaces.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry
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
  rw [projectiveLine.nonempty_iso_twistingSheaf_iff, LineBundleClass.intersectionNumber_def,
    LineBundleClass.pullback_inv, LineBundleClass.pullback_mk, projectiveLine.eulerDegree_inv,
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

/-- An exceptional curve of the first kind is quasi-compact. -/
theorem compactSpace : CompactSpace I.subscheme := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  exact QuasiCompact.compactSpace_of_compactSpace (e.inv ≫ (projectiveLine κ ↘ Spec (.of κ)))

/-- An exceptional curve of the first kind is quasi-separated. -/
theorem quasiSeparatedSpace : QuasiSeparatedSpace I.subscheme := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  exact quasiSeparatedSpace_of_quasiSeparated (e.inv ≫ (projectiveLine κ ↘ Spec (.of κ)))

/-- An exceptional curve of the first kind is integral, as the projective line is. -/
theorem isIntegral_subscheme : IsIntegral I.subscheme := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  exact .of_isIso e.hom

/-- **The constant field of an exceptional curve.** The global functions on an exceptional curve
of the first kind `E ≅ ℙ¹_κ` form a field, isomorphic to `κ`. -/
theorem isField_globalSections : IsField Γ(I.subscheme, ⊤) := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  have := hE.isIntegral_subscheme
  exact isField_of_universallyClosed κ (e.inv ≫ (projectiveLine κ ↘ Spec (.of κ)))

/-- An exceptional curve of the first kind is one-dimensional, as the projective line is. -/
theorem topologicalKrullDim_subscheme : topologicalKrullDim I.subscheme = 1 := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
  exact (projectiveLine.isCurveOver κ).topologicalKrullDim_eq_one

/-- **An exceptional curve has no higher cohomology of the structure sheaf**: `Hⁿ(E, 𝒪_E) = 0`
for `n ≥ 1`, as on the projective line. In particular `E` has genus zero, and its higher
cohomology is finite-dimensional over every field over which `E` lies. -/
theorem subsingleton_cohomology_succ_trivial (n : ℕ) :
    Subsingleton (Cohomology (InvertibleSheaf.trivial I.subscheme).obj (n + 1)) := by
  obtain ⟨κ, _, e, -⟩ := hE.exists_iso
  -- Regard `E` as a curve over `κ` through `e`, and compare with `ℙ¹_κ` over `κ`.
  let : I.subscheme.Over (Spec (.of κ)) := ⟨e.inv ≫ (projectiveLine κ ↘ Spec (.of κ))⟩
  have : e.inv.IsOver (Spec (.of κ)) := ⟨rfl⟩
  exact (e.inv.cohomologyTrivialBaseLinearEquivOfIsIso κ (n + 1)).toEquiv.subsingleton

/-- **An exceptional curve has genus zero over its constant field**:
`dim_{Γ(E, 𝒪_E)} H¹(E, 𝒪_E) = 0`. This is the genus `gᵢ` of a component of the numerical type of
a regular model. -/
theorem finrank_globalSections_cohomology_one_trivial_eq_zero :
    finrank Γ(I.subscheme, ⊤) (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 :=
  have := hE.subsingleton_cohomology_succ_trivial 0
  have : Nontrivial Γ(I.subscheme, ⊤) := ⟨hE.isField_globalSections.exists_pair_ne⟩
  Module.finrank_zero_of_subsingleton

variable (k : Type u) [Field k] [I.subscheme.Over (Spec (.of k))]

/-- **An exceptional curve has genus zero**: `dim_k H¹(E, 𝒪_E) = 0` over every field `k` over which
`E` lies. -/
theorem finrank_cohomology_one_trivial_eq_zero :
    finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) = 0 :=
  have := hE.subsingleton_cohomology_succ_trivial 0
  Module.finrank_zero_of_subsingleton

omit hE in
/-- Intersection numbers with a closed subscheme `E` over a field `k` are those computed over
`κ` on `ℙ¹_κ` through an isomorphism `e : ℙ¹_κ ≅ E`, scaled by `dim_k H⁰(E, 𝒪_E)`. -/
private lemma intersectionNumber_eq_mul {κ : Type u} [Field κ]
    (e : projectiveLine κ ≅ I.subscheme) (a : LineBundleClass X) :
    LineBundleClass.intersectionNumber k I.subschemeι a =
      LineBundleClass.intersectionNumber κ (e.hom ≫ I.subschemeι) a *
        finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) := by
  -- Regard `ℙ¹_κ` as a scheme over `k` through `e`, and compute there.
  let : (projectiveLine κ).Over (Spec (.of k)) := ⟨e.hom ≫ (I.subscheme ↘ Spec (.of k))⟩
  have : e.hom.IsOver (Spec (.of k)) := ⟨rfl⟩
  have h := LineBundleClass.eulerDegree_mul_finrank_cohomology_zero_trivial k κ
    (isField_of_universallyClosed κ (projectiveLine κ ↘ Spec (.of κ)))
    (LineBundleClass.pullback (e.hom ≫ I.subschemeι) a)
  rw [projectiveLine.finrank_cohomology_zero_trivial, Nat.cast_one, mul_one,
    Scheme.Hom.finrank_cohomology_trivial_of_isIso e.hom k 0,
    ← LineBundleClass.pullback_comp, LineBundleClass.eulerDegree_pullback_of_isIso e.hom rfl] at h
  rw [LineBundleClass.intersectionNumber_def, LineBundleClass.intersectionNumber_def, h, mul_comm,
    LineBundleClass.pullback_comp]

/-- **The self-intersection of an exceptional curve is minus its weight.** Over every field `k`
over which an exceptional curve of the first kind `E` lies,
`(E · E) = deg_k 𝒪_X(E)|_E = -dim_k H⁰(E, 𝒪_E)`. -/
theorem intersectionNumber_self :
    LineBundleClass.intersectionNumber k I.subschemeι
        (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
      -(finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) : ℤ) := by
  obtain ⟨_, κ, _, e, he⟩ := isExceptionalCurveOfFirstKind_iff_intersectionNumber.mp hE
  rw [intersectionNumber_eq_mul k e, he, neg_one_mul]

/-- **The conormal bundle of an exceptional curve has degree its weight.** Over every field `k`
over which an exceptional curve of the first kind `E` lies,
`(-E · E) = deg_k 𝒪_X(-E)|_E = dim_k H⁰(E, 𝒪_E)`. -/
theorem intersectionNumber_mk_toInvertibleSheaf :
    LineBundleClass.intersectionNumber k I.subschemeι
        (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf) =
      finrank k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 0) := by
  obtain ⟨κ, _, e, he⟩ := hE.exists_iso
  rw [intersectionNumber_eq_mul k e, LineBundleClass.intersectionNumber_mk,
    (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp he, one_mul]

/-- **Exceptional curves are invariant under isomorphisms.** The inverse image of an exceptional
curve of the first kind along an isomorphism of schemes `g : Y ⟶ X` is an exceptional curve of
the first kind. -/
theorem comap_of_isIso {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso g] :
    (I.comap g).IsExceptionalCurveOfFirstKind := by
  obtain ⟨hI, κ, _, e, he⟩ := isExceptionalCurveOfFirstKind_iff_intersectionNumber.mp hE
  have hI' := hI.comap g
  -- The inverse image of `E` is the fibre product `Y ×_X E`, isomorphic to `E` since `g` is.
  let ψ : (I.comap g).subscheme ≅ I.subscheme :=
    I.comapIso g ≪≫ asIso (Limits.pullback.snd g I.subschemeι)
  have hψ : ψ.inv ≫ (I.comap g).subschemeι ≫ g = I.subschemeι := by
    simp [ψ, Limits.pullback.condition]
  refine isExceptionalCurveOfFirstKind_iff_intersectionNumber.mpr
    ⟨hI', κ, _, e ≪≫ ψ.symm, ?_⟩
  rw [← hI.pullback_mk_toInvertibleSheaf hI', ← LineBundleClass.pullback_inv,
    LineBundleClass.intersectionNumber_def, LineBundleClass.pullback_comp, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Category.assoc, hψ, ← LineBundleClass.intersectionNumber_def, he]

end IsExceptionalCurveOfFirstKind

/-- Being an exceptional curve of the first kind is invariant under isomorphisms of schemes. -/
@[simp]
theorem isExceptionalCurveOfFirstKind_comap_iff_of_isIso {Y : Scheme.{u}} {I : X.IdealSheafData}
    (g : Y ⟶ X) [IsIso g] :
    (I.comap g).IsExceptionalCurveOfFirstKind ↔ I.IsExceptionalCurveOfFirstKind := by
  refine ⟨fun hE ↦ ?_, fun hE ↦ hE.comap_of_isIso g⟩
  simpa only [← comap_comp, IsIso.inv_hom_id, comap_id] using hE.comap_of_isIso (inv g)

/-- The empty closed subscheme is not an exceptional curve of the first kind: the unit ideal
sheaf `⊤` cuts out the empty subscheme. -/
@[simp]
theorem not_isExceptionalCurveOfFirstKind_top :
    ¬ (⊤ : X.IdealSheafData).IsExceptionalCurveOfFirstKind := fun hE ↦
  have := hE.isIntegral_subscheme
  IsEmpty.false (α := (⊤ : X.IdealSheafData).subscheme) (Classical.arbitrary _)

end AlgebraicGeometry.Scheme.IdealSheafData
