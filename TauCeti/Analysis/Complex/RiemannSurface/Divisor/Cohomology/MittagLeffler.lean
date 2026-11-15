/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.PrincipalParts
public import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction
import TauCeti.Data.DFinsupp.Basic
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# The Mittag-Leffler connecting map

Let `X` be a compact Hausdorff Riemann surface and `D` a divisor on `X`. This file constructs the
**Mittag-Leffler connecting map** `PrincipalParts D → H¹(X, 𝒪_D)`, which sends a Mittag-Leffler
distribution relative to `D` to its obstruction to being the family of principal parts of a
meromorphic function (Forster, §17).

The finite-level connecting maps `principalPartsConnecting (h : D ≤ E)` of the principal-parts
sequences `0 → 𝒪_D → 𝒪_E → 𝒫_{D,E} → 0` are defined on the families of principal parts with
poles bounded by `E`. A Mittag-Leffler distribution `μ` has a *least bounding divisor*
`PrincipalParts.boundingDivisor μ ≥ D`, whose coefficient at `x` is the least pole bound
`LocalPrincipalPart.poleBound (μ x)` of the local principal part `μ x`. The connecting map is
defined as the finite-level connecting map at this divisor. It is computed by the finite-level
connecting map at every bounding divisor (`mittagLefflerConnecting_eq`), by naturality of the
Čech connecting map along the morphisms of principal-parts sequences
(`principalPartsConnecting_naturality`). No colimit over divisors and no choice of a bounding
divisor are involved.

## Main declarations

* `TauCeti.RiemannSurface.LocalPrincipalPart.poleBound` and
  `TauCeti.RiemannSurface.PrincipalParts.boundingDivisor`: least pole bounds.
* `TauCeti.RiemannSurface.principalPartsSequenceMap`: the morphism of principal-parts sequences
  induced by `D ≤ D'` and `E ≤ E'`, and `principalPartsConnecting_naturality`.
* `TauCeti.RiemannSurface.mittagLefflerConnecting`: the connecting map
  `PrincipalParts D →ₗ[ℂ] H¹(X, 𝒪_D)`, with `mittagLefflerConnecting_eq`.
* `TauCeti.RiemannSurface.exact_principalParts_mittagLefflerConnecting`: on a connected surface,
  `𝓜(X) → PrincipalParts D → H¹(X, 𝒪_D)` is exact.
* `TauCeti.RiemannSurface.range_mittagLefflerConnecting`: the image is the union of the kernels of
  the maps `H¹(𝒪_D) → H¹(𝒪_E)` for `D ≤ E`.
* `TauCeti.RiemannSurface.mittagLefflerConnecting_mapOfLE`: naturality in the divisor, and
  `mittagLefflerConnecting_mapOfLE_add_ofPoint`: its form for a point twist `D ≤ D + x`.
* `TauCeti.RiemannSurface.mittagLefflerConnecting_principalParts_coordinate_inv`: on `ℙ¹`, the
  nonzero principal part of `1/z` has zero obstruction.

Forster's Theorem 17.3, the surjectivity of the connecting map, is not proved here: it needs the
vanishing of `H¹(X, 𝒪_E)` for divisors `E` of large degree.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§16-17.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

section Bounds

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace LocalPrincipalPart

variable {D D' E E' : WeilDivisor X} {x : X}

/-- Principal parts bounded by `E` are bounded by every `E'` permitting more poles at `x`. -/
theorem boundedBy_mono (h : E x ≤ E' x) : boundedBy D E x ≤ boundedBy D E' x := fun _ hp ↦ by
  obtain ⟨φ, hφ, rfl⟩ := mem_boundedBy_iff.1 hp
  exact mk_mem_boundedBy (meromorphicGerms.orderGE_antitone _ (neg_le_neg h) hφ)

/-- The projection to a larger divisor `D'` maps principal parts bounded by `E` to principal parts
bounded by every `E'` permitting more poles at `x`. -/
theorem mapOfLE_mem_boundedBy (hD : D ≤ D') (hE : E x ≤ E' x) {p : LocalPrincipalPart D x}
    (hp : p ∈ boundedBy D E x) : mapOfLE hD x p ∈ boundedBy D' E' x := by
  obtain ⟨φ, hφ, rfl⟩ := mem_boundedBy_iff.1 hp
  rw [mapOfLE_mk]
  exact mk_mem_boundedBy (meromorphicGerms.orderGE_antitone _ (neg_le_neg hE) hφ)

@[simp]
theorem mapOfLE_refl_apply (p : LocalPrincipalPart D x) : mapOfLE (le_refl D) x p = p := by
  induction p using Submodule.Quotient.induction_on with
  | _ φ => rw [mapOfLE_mk]

/-- A principal part relative to `D` at `x` whose poles are bounded by the integer `n`. -/
private def BoundedAt (p : LocalPrincipalPart D x) (n : ℤ) : Prop :=
  ∃ φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-n), Submodule.Quotient.mk φ = p

private theorem mem_boundedBy_iff_boundedAt {p : LocalPrincipalPart D x} :
    p ∈ boundedBy D E x ↔ BoundedAt p (E x) :=
  mem_boundedBy_iff

/-- Every local principal part has some pole bound. -/
private theorem exists_boundedAt (p : LocalPrincipalPart D x) :
    ∃ n, D x ≤ n ∧ BoundedAt p n := by
  induction p using Submodule.Quotient.induction_on with
  | _ φ =>
    cases h : meromorphicGerms.order φ with
    | top =>
      refine ⟨D x, le_rfl, φ, ?_, rfl⟩
      rw [meromorphicGerms.mem_orderGE, h]
      exact le_top
    | coe m =>
      refine ⟨max (D x) (-m), le_max_left _ _, φ, ?_, rfl⟩
      rw [meromorphicGerms.mem_orderGE, h, WithTop.coe_le_coe]
      have := le_max_right (D x) (-m)
      omega

variable (D) in
/-- The **pole bound** of a local principal part relative to `D` at `x`: the least integer
`n ≥ D x` such that the principal part is the class of a germ of order at least `-n`. -/
def poleBound (p : LocalPrincipalPart D x) : ℤ :=
  sInf {n | D x ≤ n ∧ BoundedAt p n}

private theorem poleBound_mem (p : LocalPrincipalPart D x) :
    poleBound D p ∈ {n | D x ≤ n ∧ BoundedAt p n} :=
  Int.csInf_mem (exists_boundedAt p) ⟨D x, fun _ hn ↦ hn.1⟩

theorem le_poleBound (p : LocalPrincipalPart D x) : D x ≤ poleBound D p :=
  (poleBound_mem p).1

/-- A principal part is bounded by every divisor whose coefficient at `x` is its pole bound. -/
theorem mem_boundedBy_of_poleBound_le {p : LocalPrincipalPart D x} (h : poleBound D p ≤ E x) :
    p ∈ boundedBy D E x :=
  boundedBy_mono (E := Finsupp.single x (poleBound D p)) (by simpa using h)
    (mem_boundedBy_iff_boundedAt.2 (by simpa using (poleBound_mem p).2))

/-- The pole bound is least among the bounds `E x ≥ D x`. -/
theorem poleBound_le {p : LocalPrincipalPart D x} (hD : D x ≤ E x) (hp : p ∈ boundedBy D E x) :
    poleBound D p ≤ E x :=
  csInf_le ⟨D x, fun _ hn ↦ hn.1⟩ ⟨hD, mem_boundedBy_iff_boundedAt.1 hp⟩

/-- A principal part is bounded by `E ≥ D` exactly when its pole bound is at most `E x`. -/
theorem mem_boundedBy_iff_poleBound_le {p : LocalPrincipalPart D x} (hD : D x ≤ E x) :
    p ∈ boundedBy D E x ↔ poleBound D p ≤ E x :=
  ⟨poleBound_le hD, mem_boundedBy_of_poleBound_le⟩

@[simp]
theorem poleBound_zero : poleBound D (0 : LocalPrincipalPart D x) = D x :=
  le_antisymm (csInf_le ⟨D x, fun _ hn ↦ hn.1⟩ ⟨le_rfl, 0, Submodule.zero_mem _, rfl⟩)
    (le_poleBound _)

end LocalPrincipalPart

namespace PrincipalParts

variable {D D' E E' : WeilDivisor X}

variable (D E) in
/-- The **Mittag-Leffler distributions relative to `D` with poles bounded by `E`**: those whose
local principal parts all lie in `LocalPrincipalPart.boundedBy D E x`. -/
def boundedBy : Submodule ℂ (PrincipalParts D) :=
  ⨅ x, (LocalPrincipalPart.boundedBy D E x).comap (DFinsupp.lapply x)

theorem mem_boundedBy {μ : PrincipalParts D} :
    μ ∈ boundedBy D E ↔ ∀ x, μ x ∈ LocalPrincipalPart.boundedBy D E x := by
  simp only [boundedBy, Submodule.mem_iInf, Submodule.mem_comap, DFinsupp.lapply_apply]

theorem boundedBy_mono (h : E ≤ E') : boundedBy D E ≤ boundedBy D E' := fun _ hμ ↦
  mem_boundedBy.2 fun x ↦ LocalPrincipalPart.boundedBy_mono (h x) (mem_boundedBy.1 hμ x)

theorem mapOfLE_mem_boundedBy (hD : D ≤ D') (hE : E ≤ E') {μ : PrincipalParts D}
    (hμ : μ ∈ boundedBy D E) : mapOfLE hD μ ∈ boundedBy D' E' :=
  mem_boundedBy.2 fun x ↦ by
    rw [mapOfLE_apply]
    exact LocalPrincipalPart.mapOfLE_mem_boundedBy hD (hE x) (mem_boundedBy.1 hμ x)

variable (D E) in
/-- A Mittag-Leffler distribution bounded by `E`, read as a family of bounded local principal
parts. -/
def toBoundedFamily : boundedBy D E →ₗ[ℂ] ∀ x, LocalPrincipalPart.boundedBy D E x :=
  LinearMap.pi fun x ↦ ((DFinsupp.lapply x).comp (boundedBy D E).subtype).codRestrict _
    fun μ ↦ mem_boundedBy.1 μ.2 x

@[simp]
theorem coe_toBoundedFamily_apply (μ : boundedBy D E) (x : X) :
    (toBoundedFamily D E μ x : LocalPrincipalPart D x) = (μ : PrincipalParts D) x := (rfl)

/-- Every family of principal parts bounded by `E` is a Mittag-Leffler distribution: it vanishes
off the finite support of `E - D`. -/
theorem toBoundedFamily_surjective : Function.Surjective (toBoundedFamily D E) := by
  classical
  intro c
  have hfin : {x | (c x : LocalPrincipalPart D x) ≠ 0}.Finite := by
    refine (E - D).support.finite_toSet.subset fun x hx ↦ ?_
    by_contra hmem
    have hED : E x ≤ D x := by
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.coe_sub, Pi.sub_apply,
        not_not, sub_eq_zero] at hmem
      exact hmem.le
    exact hx (by
      simpa using (Submodule.eq_bot_iff _).1 (LocalPrincipalPart.boundedBy_eq_bot hED) _ (c x).2)
  refine ⟨⟨DFinsupp.ofSupportFinite (fun x ↦ (c x : LocalPrincipalPart D x)) hfin,
    mem_boundedBy.2 fun x ↦ by simp [DFinsupp.ofSupportFinite_apply]⟩, ?_⟩
  funext x
  exact Subtype.ext (DFinsupp.ofSupportFinite_apply _ _ x)

/-- The **least bounding divisor** of a Mittag-Leffler distribution relative to `D`: its
coefficient at `x` is the pole bound of the local principal part at `x`. -/
def boundingDivisor (μ : PrincipalParts D) : WeilDivisor X :=
  D + Finsupp.ofSupportFinite (fun x ↦ LocalPrincipalPart.poleBound D (μ x) - D x) (by
    classical
    refine (μ.support.finite_toSet).subset fun x hx ↦ ?_
    by_contra hmem
    simp only [Finset.mem_coe, DFinsupp.mem_support_toFun, not_not] at hmem
    simp [hmem] at hx)

@[simp]
theorem boundingDivisor_apply (μ : PrincipalParts D) (x : X) :
    boundingDivisor μ x = LocalPrincipalPart.poleBound D (μ x) := by
  rw [boundingDivisor, Finsupp.add_apply, Finsupp.ofSupportFinite_coe]
  omega

theorem le_boundingDivisor (μ : PrincipalParts D) : D ≤ boundingDivisor μ := fun x ↦ by
  simpa using LocalPrincipalPart.le_poleBound (μ x)

theorem mem_boundedBy_boundingDivisor (μ : PrincipalParts D) :
    μ ∈ boundedBy D (boundingDivisor μ) :=
  mem_boundedBy.2 fun x ↦ LocalPrincipalPart.mem_boundedBy_of_poleBound_le (by simp)

/-- The bounding divisor is least among the divisors `E ≥ D` bounding the distribution. -/
theorem boundingDivisor_le {μ : PrincipalParts D} (hD : D ≤ E) (hμ : μ ∈ boundedBy D E) :
    boundingDivisor μ ≤ E := fun x ↦ by
  simpa using LocalPrincipalPart.poleBound_le (hD x) (mem_boundedBy.1 hμ x)

/-- A distribution is bounded by `E ≥ D` exactly when its least bounding divisor is at most `E`. -/
theorem mem_boundedBy_iff_boundingDivisor_le {μ : PrincipalParts D} (hD : D ≤ E) :
    μ ∈ boundedBy D E ↔ boundingDivisor μ ≤ E :=
  ⟨boundingDivisor_le hD, fun h ↦ boundedBy_mono h (mem_boundedBy_boundingDivisor μ)⟩

@[simp]
theorem boundingDivisor_zero : boundingDivisor (0 : PrincipalParts D) = D :=
  Finsupp.ext fun x ↦ by
    rw [boundingDivisor_apply, DFinsupp.zero_apply, LocalPrincipalPart.poleBound_zero]

end PrincipalParts

end Bounds

section Sheaf

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {D D' E E' : WeilDivisor X}

/-- For `D ≤ D'` and `E ≤ E'`, the map from principal parts relative to `D` bounded by `E` to
principal parts relative to `D'` bounded by `E'`, pointwise by `LocalPrincipalPart.mapOfLE`. -/
def boundedFamilyMap (hD : D ≤ D') (hE : E ≤ E') :
    (∀ x : X, LocalPrincipalPart.boundedBy D E x) →ₗ[ℂ]
      ∀ x : X, LocalPrincipalPart.boundedBy D' E' x :=
  LinearMap.pi fun x ↦ (((LocalPrincipalPart.mapOfLE hD x).comp
    (LocalPrincipalPart.boundedBy D E x).subtype).codRestrict _
      fun p ↦ LocalPrincipalPart.mapOfLE_mem_boundedBy hD (hE x) p.2).comp (LinearMap.proj x)

@[simp]
theorem coe_boundedFamilyMap_apply (hD : D ≤ D') (hE : E ≤ E')
    (c : ∀ x : X, LocalPrincipalPart.boundedBy D E x) (x : X) :
    (boundedFamilyMap hD hE c x : LocalPrincipalPart D' x) =
      LocalPrincipalPart.mapOfLE hD x (c x) := (rfl)

theorem boundedFamilyMap_toBoundedFamily (hD : D ≤ D') (hE : E ≤ E')
    (μ : PrincipalParts.boundedBy D E) :
    boundedFamilyMap hD hE (PrincipalParts.toBoundedFamily D E μ) =
      PrincipalParts.toBoundedFamily D' E'
        ⟨PrincipalParts.mapOfLE hD μ, PrincipalParts.mapOfLE_mem_boundedBy hD hE μ.2⟩ :=
  funext fun x ↦ Subtype.ext (PrincipalParts.mapOfLE_apply hD μ x).symm

/-- The map of sections over `U` underlying `principalPartsSheafMap`. -/
private def principalPartsSheafMapApp (hD : D ≤ D') (hE : E ≤ E') (U : Opens X) :
    (principalPartsSheaf D E).obj.obj (op U) →ₗ[ℂ] (principalPartsSheaf D' E').obj.obj (op U) :=
  (principalPartsSheafSectionsEquiv D' E' U).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun x : U ↦ (((LocalPrincipalPart.mapOfLE hD x.1).comp
      (LocalPrincipalPart.boundedBy D E x.1).subtype).codRestrict _
        fun p ↦ LocalPrincipalPart.mapOfLE_mem_boundedBy hD (hE x.1) (by exact p.2)).comp
          (LinearMap.proj x)) ∘ₗ (principalPartsSheafSectionsEquiv D E U).toLinearMap

private theorem principalPartsSheafMapApp_apply (hD : D ≤ D') (hE : E ≤ E') (U : Opens X)
    (s : (principalPartsSheaf D E).obj.obj (op U)) (x : U) :
    (principalPartsSheafSectionsEquiv D' E' U (principalPartsSheafMapApp hD hE U s) x :
        LocalPrincipalPart D' x.1) =
      LocalPrincipalPart.mapOfLE hD x.1 (principalPartsSheafSectionsEquiv D E U s x) := by
  simp [principalPartsSheafMapApp]

/-- The morphism of principal-parts sheaves `𝒫_{D,E} ⟶ 𝒫_{D',E'}` for `D ≤ D'` and `E ≤ E'`,
projecting each local principal part from `D` to `D'`. -/
def principalPartsSheafMap (hD : D ≤ D') (hE : E ≤ E') :
    principalPartsSheaf D E ⟶ principalPartsSheaf D' E' where
  hom.app U := ModuleCat.ofHom (principalPartsSheafMapApp hD hE U.unop)
  hom.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply (principalPartsSheafSectionsEquiv D' E' V.unop).injective
    funext x
    apply Subtype.ext
    have h₁ := principalPartsSheafSectionsEquiv_map D E h.unop s x
    have h₂ := principalPartsSheafSectionsEquiv_map D' E' h.unop
      (principalPartsSheafMapApp hD hE U.unop s) x
    -- Restriction and the projection both act pointwise.
    change (principalPartsSheafSectionsEquiv D' E' V.unop (principalPartsSheafMapApp hD hE V.unop
        ((principalPartsSheaf D E).obj.map h.unop.op s)) x : LocalPrincipalPart D' x.1) =
      principalPartsSheafSectionsEquiv D' E' V.unop ((principalPartsSheaf D' E').obj.map h.unop.op
        (principalPartsSheafMapApp hD hE U.unop s)) x
    rw [h₂, principalPartsSheafMapApp_apply, principalPartsSheafMapApp_apply, h₁]

@[simp]
theorem principalPartsSheafMap_app_apply (hD : D ≤ D') (hE : E ≤ E') (U : Opens X)
    (s : (principalPartsSheaf D E).obj.obj (op U)) (x : U) :
    (principalPartsSheafSectionsEquiv D' E' U ((principalPartsSheafMap hD hE).hom.app (op U) s) x :
        LocalPrincipalPart D' x.1) =
      LocalPrincipalPart.mapOfLE hD x.1 (principalPartsSheafSectionsEquiv D E U s x) :=
  principalPartsSheafMapApp_apply hD hE U s x

/-- The principal parts of a section of `𝒪_E`, projected to `D'`, are the principal parts of its
image in `𝒪_{E'}`. -/
@[reassoc]
theorem principalPartsMap_comp_principalPartsSheafMap (hD : D ≤ D') (hE : E ≤ E') :
    principalPartsMap D E ≫ principalPartsSheafMap hD hE =
      divisorSheafMapOfLE hE ≫ principalPartsMap D' E' := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (principalPartsSheafSectionsEquiv D' E' U.unop).injective
  funext x
  apply Subtype.ext
  -- Both sides are the class of the same coordinate germ.
  change (principalPartsSheafSectionsEquiv D' E' U.unop ((principalPartsSheafMap hD hE).hom.app
      (op U.unop) ((principalPartsMap D E).hom.app (op U.unop) f)) x : LocalPrincipalPart D' x.1) =
    principalPartsSheafSectionsEquiv D' E' U.unop ((principalPartsMap D' E').hom.app (op U.unop)
      ((divisorSheafMapOfLE hE).hom.app (op U.unop) f)) x
  rw [principalPartsSheafMap_app_apply, principalPartsMap_app_apply, principalPartsMap_app_apply,
    LocalPrincipalPart.mapOfLE_mk, divisorSections.toChartGerm_mapOfLE]

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The **morphism of principal-parts sequences** induced by `D ≤ D'` and `E ≤ E'`: the divisor
inclusions on `𝒪_D` and `𝒪_E`, and the projection of principal parts. -/
def principalPartsSequenceMap (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D') (hE : E ≤ E') :
    principalPartsSequence hDE ⟶ principalPartsSequence hDE' where
  τ₁ := divisorSheafMapOfLE hD
  τ₂ := divisorSheafMapOfLE hE
  τ₃ := principalPartsSheafMap hD hE
  comm₁₂ := (divisorSheafMapOfLE_comp hD hDE').trans (divisorSheafMapOfLE_comp hDE hE).symm
  comm₂₃ := (principalPartsMap_comp_principalPartsSheafMap hD hE).symm

end Sheaf

section Cohomology

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {D D' E E' : WeilDivisor X}

private theorem principalPartsCechIso_naturality (hD : D ≤ D') (hE : E ≤ E')
    (c : ∀ x : X, LocalPrincipalPart.boundedBy D E x) :
    ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).map
        (principalPartsSheafMap hD hE).hom).hom ((principalPartsCechIso D E).hom.hom c) =
      (principalPartsCechIso D' E').hom.hom (boundedFamilyMap hD hE c) := by
  obtain ⟨s, hs⟩ := (principalPartsSheafSectionsEquiv D E ⊤).surjective
    ((principalPartsTopEquiv D E).symm c)
  rw [principalPartsCechIso_hom_apply c s fun x ↦ by rw [hs, principalPartsTopEquiv_symm_apply],
    principalPartsCechIso_hom_apply _ ((principalPartsSheafMap hD hE).hom.app (op ⊤) s)
      fun x ↦ Subtype.ext (by
        rw [principalPartsSheafMap_app_apply, hs, principalPartsTopEquiv_symm_apply,
          coe_boundedFamilyMap_apply])]
  exact (congrArg (fun g ↦ g.hom s) (cechCohomologyZeroIso_hom_naturality _
    (principalPartsSheafMap hD hE))).symm

variable [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X]

/-- **Naturality of the principal-parts connecting maps** in `D ≤ D'` and `E ≤ E'`. -/
theorem principalPartsConnecting_naturality (hDE : D ≤ E) (hDE' : D' ≤ E') (hD : D ≤ D')
    (hE : E ≤ E') (c : ∀ x : X, LocalPrincipalPart.boundedBy D E x) :
    principalPartsConnecting hDE' (boundedFamilyMap hD hE c) =
      divisorCechCohomologyMapOfLE hD 1 (principalPartsConnecting hDE c) := by
  have h := congrArg (fun g ↦ g.hom ((principalPartsCechIso D E).hom.hom c))
    ((principalPartsSequence_shortExact hDE).cechCohomologyδ_naturality
      (principalPartsSequence_shortExact hDE') (principalPartsSequenceMap hDE hDE' hD hE) 0)
  rw [principalPartsConnecting_def, principalPartsConnecting_def, divisorCechCohomologyMapOfLE_def]
  exact (congrArg ((principalPartsSequence_shortExact hDE').cechCohomologyδ 0).hom
    (principalPartsCechIso_naturality hD hE c).symm).trans h.symm

/-- The finite-level connecting map does not depend on the bounding divisor. -/
theorem principalPartsConnecting_boundedFamilyMap_refl (hDE : D ≤ E) (hEE' : E ≤ E')
    (c : ∀ x : X, LocalPrincipalPart.boundedBy D E x) :
    principalPartsConnecting (hDE.trans hEE') (boundedFamilyMap le_rfl hEE' c) =
      principalPartsConnecting hDE c := by
  rw [principalPartsConnecting_naturality hDE (hDE.trans hEE') le_rfl hEE',
    divisorCechCohomologyMapOfLE_refl, LinearMap.id_apply]

/-- The connecting map of a Mittag-Leffler distribution, before linearity is established. -/
private def mittagLefflerConnectingFun (μ : PrincipalParts D) : divisorCechCohomology D 1 :=
  principalPartsConnecting (PrincipalParts.le_boundingDivisor μ)
    (PrincipalParts.toBoundedFamily D _ ⟨μ, PrincipalParts.mem_boundedBy_boundingDivisor μ⟩)

private theorem mittagLefflerConnectingFun_eq (hDE : D ≤ E) (μ : PrincipalParts.boundedBy D E) :
    mittagLefflerConnectingFun (μ : PrincipalParts D) =
      principalPartsConnecting hDE (PrincipalParts.toBoundedFamily D E μ) := by
  obtain ⟨μ, hμ⟩ := μ
  have hle := PrincipalParts.boundingDivisor_le hDE hμ
  have h := principalPartsConnecting_boundedFamilyMap_refl (PrincipalParts.le_boundingDivisor μ) hle
    (PrincipalParts.toBoundedFamily D _ ⟨μ, PrincipalParts.mem_boundedBy_boundingDivisor μ⟩)
  have hc : boundedFamilyMap le_rfl hle
      (PrincipalParts.toBoundedFamily D _ ⟨μ, PrincipalParts.mem_boundedBy_boundingDivisor μ⟩) =
      PrincipalParts.toBoundedFamily D E ⟨μ, hμ⟩ :=
    funext fun x ↦ Subtype.ext (by
      rw [coe_boundedFamilyMap_apply, LocalPrincipalPart.mapOfLE_refl_apply,
        PrincipalParts.coe_toBoundedFamily_apply, PrincipalParts.coe_toBoundedFamily_apply])
  rw [hc] at h
  exact h.symm

variable (D) in
/-- The **Mittag-Leffler connecting map** `PrincipalParts D → H¹(X, 𝒪_D)`: a Mittag-Leffler
distribution relative to `D` is sent to the connecting obstruction of the principal-parts sequence
of its least bounding divisor. -/
def mittagLefflerConnecting : PrincipalParts D →ₗ[ℂ] divisorCechCohomology D 1 where
  toFun := mittagLefflerConnectingFun
  map_add' μ ν := by
    have hDE : D ≤ PrincipalParts.boundingDivisor μ ⊔ PrincipalParts.boundingDivisor ν :=
      (PrincipalParts.le_boundingDivisor μ).trans le_sup_left
    have hμ := PrincipalParts.boundedBy_mono (le_sup_left (b := PrincipalParts.boundingDivisor ν))
      (PrincipalParts.mem_boundedBy_boundingDivisor μ)
    have hν := PrincipalParts.boundedBy_mono (le_sup_right (a := PrincipalParts.boundingDivisor μ))
      (PrincipalParts.mem_boundedBy_boundingDivisor ν)
    have := mittagLefflerConnectingFun_eq hDE (⟨μ, hμ⟩ + ⟨ν, hν⟩ : PrincipalParts.boundedBy D _)
    rw [map_add, map_add, ← mittagLefflerConnectingFun_eq hDE ⟨μ, hμ⟩,
      ← mittagLefflerConnectingFun_eq hDE ⟨ν, hν⟩] at this
    exact this
  map_smul' a μ := by
    have hDE := PrincipalParts.le_boundingDivisor μ
    have hμ := PrincipalParts.mem_boundedBy_boundingDivisor μ
    have := mittagLefflerConnectingFun_eq hDE (a • ⟨μ, hμ⟩ : PrincipalParts.boundedBy D _)
    rw [map_smul, map_smul, ← mittagLefflerConnectingFun_eq hDE ⟨μ, hμ⟩] at this
    exact this

/-- The Mittag-Leffler connecting map is computed by the principal-parts connecting map of every
bounding divisor `E ≥ D`. -/
theorem mittagLefflerConnecting_eq (hDE : D ≤ E) (μ : PrincipalParts.boundedBy D E) :
    mittagLefflerConnecting D μ =
      principalPartsConnecting hDE (PrincipalParts.toBoundedFamily D E μ) :=
  mittagLefflerConnectingFun_eq hDE μ

/-- **Naturality of the Mittag-Leffler connecting map** in the divisor: projecting principal parts
to `D' ≥ D` corresponds to the map `H¹(𝒪_D) → H¹(𝒪_{D'})`. -/
theorem mittagLefflerConnecting_mapOfLE (h : D ≤ D') (μ : PrincipalParts D) :
    mittagLefflerConnecting D' (PrincipalParts.mapOfLE h μ) =
      divisorCechCohomologyMapOfLE h 1 (mittagLefflerConnecting D μ) := by
  have hDE : D ≤ PrincipalParts.boundingDivisor μ ⊔ D' :=
    (PrincipalParts.le_boundingDivisor μ).trans le_sup_left
  have hμ : μ ∈ PrincipalParts.boundedBy D (PrincipalParts.boundingDivisor μ ⊔ D') :=
    PrincipalParts.boundedBy_mono le_sup_left (PrincipalParts.mem_boundedBy_boundingDivisor μ)
  rw [mittagLefflerConnecting_eq hDE ⟨μ, hμ⟩,
    ← principalPartsConnecting_naturality hDE le_sup_right h le_rfl,
    boundedFamilyMap_toBoundedFamily, ← mittagLefflerConnecting_eq]

/-- Linear-map form of `mittagLefflerConnecting_mapOfLE`. -/
theorem mittagLefflerConnecting_comp_mapOfLE (h : D ≤ D') :
    mittagLefflerConnecting D' ∘ₗ PrincipalParts.mapOfLE h =
      divisorCechCohomologyMapOfLE h 1 ∘ₗ mittagLefflerConnecting D :=
  LinearMap.ext (mittagLefflerConnecting_mapOfLE h)

/-- **Point-twist check.** For the inclusion `D ≤ D + x`, projecting principal parts to `D + x`
corresponds to the point-twist cohomology map `H¹(𝒪_D) → H¹(𝒪_{D+x})`. -/
theorem mittagLefflerConnecting_mapOfLE_add_ofPoint (x : X) (μ : PrincipalParts D) :
    mittagLefflerConnecting (D + WeilDivisor.ofPoint x)
        (PrincipalParts.mapOfLE (WeilDivisor.le_add_ofPoint D x) μ) =
      pointTwistCohomologyMap D x 1 (mittagLefflerConnecting D μ) := by
  rw [mittagLefflerConnecting_mapOfLE, pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE]

/-- The **image of the Mittag-Leffler connecting map** is the union of the kernels of the maps
`H¹(𝒪_D) → H¹(𝒪_E)` for `D ≤ E`: a class is a Mittag-Leffler obstruction exactly when it dies
after allowing enough poles. -/
theorem range_mittagLefflerConnecting (D : WeilDivisor X) :
    LinearMap.range (mittagLefflerConnecting D) =
      ⨆ (E : WeilDivisor X) (h : D ≤ E), LinearMap.ker (divisorCechCohomologyMapOfLE h 1) := by
  apply le_antisymm
  · rintro _ ⟨μ, rfl⟩
    have hDE := PrincipalParts.le_boundingDivisor μ
    refine Submodule.mem_iSup_of_mem (PrincipalParts.boundingDivisor μ) <|
      Submodule.mem_iSup_of_mem hDE ?_
    rw [LinearMap.exact_iff.1 (exact_principalPartsConnecting_cohomologyMap hDE),
      mittagLefflerConnecting_eq hDE ⟨μ, PrincipalParts.mem_boundedBy_boundingDivisor μ⟩]
    exact LinearMap.mem_range_self _ _
  · refine iSup₂_le fun E hDE ↦ ?_
    rw [LinearMap.exact_iff.1 (exact_principalPartsConnecting_cohomologyMap hDE)]
    rintro _ ⟨c, rfl⟩
    obtain ⟨μ, rfl⟩ := PrincipalParts.toBoundedFamily_surjective c
    exact mittagLefflerConnecting_eq hDE μ ▸ LinearMap.mem_range_self _ _

section Exactness

variable [ConnectedSpace X]

omit [CompactSpace X] [T2Space X] in
/-- The coordinate germ of the meromorphic function of a global section of `𝒪_E` is the coordinate
germ of the section. -/
theorem MeromorphicFunction.toChartGerm_toMeromorphic (s : divisorSections E ⊤) (x : X) :
    MeromorphicFunction.toChartGerm x (divisorSections.toMeromorphic E s) =
      divisorSections.toChartGerm E ⊤ ⟨x, trivial⟩ s := by
  apply Subtype.ext
  rw [MeromorphicFunction.coe_toChartGerm, divisorSections.coe_toChartGerm]
  apply Filter.Germ.coe_eq.2
  filter_upwards [(tendsto_chartAt_symm_nhdsNE x).eventually
    (divisorSections.finitePart_toMeromorphic_eventuallyEq s x)] with z hz
  exact hz.trans (Subtype.val_injective.extend_apply s.1 (0 : X → ℂ) ⟨_, trivial⟩).symm

omit [T2Space X] in
/-- The principal parts of the meromorphic function of a global section of `𝒪_E` are its principal
parts as a section. -/
private theorem principalParts_toMeromorphic (s : (divisorSheaf E).obj.obj (op ⊤)) (x : X) :
    MeromorphicFunction.principalParts D
        (divisorSections.toMeromorphic E (divisorSheafSectionsEquiv E ⊤ s)) x =
      (globalPrincipalParts D E s x : LocalPrincipalPart D x) := by
  rw [MeromorphicFunction.principalParts_apply, coe_globalPrincipalParts_apply,
    MeromorphicFunction.toChartGerm_toMeromorphic]

omit [T2Space X] in
/-- If the principal parts of `f` relative to `D` are bounded by `E ≥ D`, then `f` is a global
section of `𝒪_E` and they are its principal parts as a section. -/
private theorem toBoundedFamily_principalParts_mem_range (hDE : D ≤ E) (f : MeromorphicFunction X)
    (hf : MeromorphicFunction.principalParts D f ∈ PrincipalParts.boundedBy D E) :
    PrincipalParts.toBoundedFamily D E ⟨_, hf⟩ ∈ LinearMap.range (globalPrincipalParts D E) := by
  have hker : f ∈ LinearMap.ker (MeromorphicFunction.principalParts E) := by
    rw [LinearMap.mem_ker, ← MeromorphicFunction.mapOfLE_principalParts hDE]
    refine DFinsupp.ext fun x ↦ ?_
    rw [PrincipalParts.mapOfLE_apply, DFinsupp.zero_apply, ← LinearMap.mem_ker,
      ← LocalPrincipalPart.boundedBy_eq_ker_mapOfLE]
    exact PrincipalParts.mem_boundedBy.1 hf x
  rw [MeromorphicFunction.ker_principalParts] at hker
  obtain ⟨s, hs⟩ := hker
  obtain ⟨t, rfl⟩ := (divisorSheafSectionsEquiv E ⊤).surjective s
  refine ⟨t, funext fun x ↦ Subtype.ext ?_⟩
  rw [PrincipalParts.coe_toBoundedFamily_apply]
  change _ = MeromorphicFunction.principalParts D f x
  rw [← hs, principalParts_toMeromorphic]

/-- **Exactness of the Mittag-Leffler sequence at the principal parts.** On a compact connected
Riemann surface, a Mittag-Leffler distribution is the family of principal parts of a meromorphic
function if and only if its Mittag-Leffler obstruction in `H¹(X, 𝒪_D)` vanishes. -/
theorem exact_principalParts_mittagLefflerConnecting (D : WeilDivisor X) :
    Function.Exact (MeromorphicFunction.principalParts D) (mittagLefflerConnecting D) := by
  intro μ
  have hDE := PrincipalParts.le_boundingDivisor μ
  have hμ := PrincipalParts.mem_boundedBy_boundingDivisor μ
  rw [mittagLefflerConnecting_eq hDE ⟨μ, hμ⟩, exact_principalParts_connecting hDE]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨divisorSections.toMeromorphic _ (divisorSheafSectionsEquiv _ ⊤ s),
      DFinsupp.ext fun x ↦ ?_⟩
    rw [principalParts_toMeromorphic, hs, PrincipalParts.coe_toBoundedFamily_apply]
  · rintro ⟨f, rfl⟩
    exact toBoundedFamily_principalParts_mem_range hDE f hμ

/-- The Mittag-Leffler obstruction of the principal parts of a meromorphic function vanishes. -/
@[simp]
theorem mittagLefflerConnecting_principalParts (f : MeromorphicFunction X) :
    mittagLefflerConnecting D (MeromorphicFunction.principalParts D f) = 0 :=
  (exact_principalParts_mittagLefflerConnecting D).apply_apply_eq_zero f

end Exactness

end Cohomology

section Sphere

open MeromorphicFunction in
/-- **Check on `ℙ¹`.** The principal part of `1/z` at the origin is not zero, but its
Mittag-Leffler obstruction vanishes, since `1/z` is a global meromorphic function realizing it. -/
theorem mittagLefflerConnecting_principalParts_coordinate_inv :
    principalParts (0 : WeilDivisor (OnePoint ℂ)) coordinate⁻¹ ≠ 0 ∧
      mittagLefflerConnecting 0 (principalParts (0 : WeilDivisor (OnePoint ℂ)) coordinate⁻¹) =
        0 := by
  refine ⟨fun h ↦ ?_, mittagLefflerConnecting_principalParts _⟩
  have h0 := principalParts_apply_eq_zero_iff.1 (DFinsupp.ext_iff.1 h ((0 : ℂ) : OnePoint ℂ))
  rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero, WithTop.coe_zero, order_nonneg_iff,
    OnePoint.ne_infty_iff_exists] at h0
  obtain ⟨a, ha⟩ := h0
  have h1 := mul_apply_of_eq_coe (x := ((0 : ℂ) : OnePoint ℂ)) (coordinate_apply _) ha.symm
  rw [mul_inv_cancel₀ coordinate_ne_zero, coe_one, zero_mul] at h1
  exact one_ne_zero (OnePoint.coe_injective h1)

end Sphere

end TauCeti.RiemannSurface
