/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.RingTheory.RegularLocalRing.Retraction

/-!
# Sections through regular points lie in the smooth locus

Let `f : X ⟶ S` be locally of finite presentation and let `σ : S ⟶ X` be a section of `f`. If
`s` is a point of `S` such that the local rings of `S` at `s` and of `X` at `σ s` are both regular,
then `f` is smooth at `σ s`. No flatness of `f` is assumed: the regularity of both local rings
forces it at `σ s`.

The local statement is `Algebra.IsSmoothAt.of_isRegularLocalRing`: the stalk map
`𝒪_{S,s} → 𝒪_{X,σ s}` has the left inverse induced by `σ`, and a regular local algebra over a
regular local ring with such a retraction is flat, with regular closed fibre whose residue field
is that of the base.

The main application is to a regular model `X` of a curve over a discrete valuation ring `R`:
every section of `X ⟶ Spec R`, for instance the extension of a rational point of the generic
fibre, lies in the smooth locus of the structure morphism, so the special fibre is smooth along
it. Regularity of `X` cannot be dropped: the section `x = y = π` of the node `xy = π²` over `R`
passes through its singular point.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing`: a section passes through
  the smooth locus at every point where the base and the source are regular.
* `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_valuationRing`: a section passes through the
  smooth locus at every point where the base is a valuation ring and the source is regular.
* `AlgebraicGeometry.Scheme.Hom.range_subset_smoothLocus_of_isRegularLocalRing`: if the base and
  the source have regular local rings, the image of every section lies in the smooth locus.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1 (sections of regular fibred
  surfaces).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- **A section passes through the smooth locus at its regular points.** Let `f : X ⟶ S` be
locally of finite presentation with a section `σ`. If the local rings of `S` at `s` and of `X` at
`σ s` are regular, then `σ s` lies in the smooth locus of `f`. -/
theorem mem_smoothLocus_of_isRegularLocalRing (f : X ⟶ S) [LocallyOfFinitePresentation f]
    {σ : S ⟶ X} (hσ : σ ≫ f = 𝟙 S) (s : S) [IsRegularLocalRing (S.presheaf.stalk s)]
    [IsRegularLocalRing (X.presheaf.stalk (σ s))] : σ s ∈ f.smoothLocus := by
  have hfs : f (σ s) = s := by simp [← Scheme.Hom.comp_apply, hσ]
  have : IsRegularLocalRing (S.presheaf.stalk (f (σ s))) := by rw [hfs]; infer_instance
  -- the stalk map of `f` at `σ s` has a left inverse, induced by `σ`; `stalkMap_congr_hom`
  -- transports `hσ` across the dependent stalk types via `stalkCongr`
  have : IsIso (f.stalkMap (σ s) ≫ σ.stalkMap s) := by
    rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ hσ, Scheme.Hom.stalkMap_id]
    exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.id _)
  have hr : f.stalkMap (σ s) ≫ σ.stalkMap s ≫ inv (f.stalkMap (σ s) ≫ σ.stalkMap s) = 𝟙 _ := by
    simp only [← Category.assoc, IsIso.hom_inv_id]
  -- pass to affine charts around `s` and `σ s`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (σ s))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.is_open'.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  let p := (hU.primeIdealOf ⟨f (σ s), hVU hxV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨σ s, hxV⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).asIdeal).symm⟩
  let e := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV
  have : IsRegularLocalRing (Localization.AtPrime p) :=
    .of_ringEquiv (R := S.presheaf.stalk (f (σ s)))
      (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    .of_ringEquiv (R := X.presheaf.stalk (σ s))
      (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
  -- transport the left inverse along the identification of the stalk map with `R_p → S_q`
  have hg := e.inv.w =≫ (σ.stalkMap s ≫ inv (f.stalkMap (σ s) ≫ σ.stalkMap s) ≫ e.hom.left)
  simp only [Arrow.mk_hom, Category.assoc] at hg
  rw [reassoc_of% hr, ← Arrow.comp_left, e.inv_hom_id, Arrow.id_left] at hg
  exact Algebra.IsSmoothAt.of_isRegularLocalRing p q _ congr(($hg.symm).hom)

/-- **A section passes through the smooth locus over a valuation ring.** Let `f : X ⟶ S` be
locally of finite presentation with a section `σ`. If the local ring of `S` at `s` is a valuation
ring and the local ring of `X` at `σ s` is regular, then `σ s` lies in the smooth locus of `f`.
No Noetherian hypothesis on `S` is needed: the local ring of `S` at `s` is a quotient of the
Noetherian local ring of `X` at `σ s`, so it is a Noetherian valuation ring and hence regular. -/
theorem mem_smoothLocus_of_valuationRing (f : X ⟶ S) [LocallyOfFinitePresentation f]
    {σ : S ⟶ X} (hσ : σ ≫ f = 𝟙 S) (s : S) [IsDomain (S.presheaf.stalk s)]
    [ValuationRing (S.presheaf.stalk s)] [IsRegularLocalRing (X.presheaf.stalk (σ s))] :
    σ s ∈ f.smoothLocus := by
  have : SurjectiveOnStalks (σ ≫ f) := by rw [hσ]; infer_instance
  have := SurjectiveOnStalks.of_comp σ f
  have := isNoetherianRing_of_surjective _ _ _ (σ.stalkMap_surjective s)
  exact f.mem_smoothLocus_of_isRegularLocalRing hσ s

/-- **Sections of a regular scheme over a regular base lie in the smooth locus.** If `f : X ⟶ S`
is locally of finite presentation and all local rings of `S` and of `X` are regular, then the
image of every section of `f` is contained in the smooth locus of `f`. -/
theorem range_subset_smoothLocus_of_isRegularLocalRing (f : X ⟶ S)
    [LocallyOfFinitePresentation f] {σ : S ⟶ X} (hσ : σ ≫ f = 𝟙 S)
    [∀ s : S, IsRegularLocalRing (S.presheaf.stalk s)]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)] :
    Set.range σ ⊆ f.smoothLocus := by
  rintro _ ⟨s, rfl⟩
  exact f.mem_smoothLocus_of_isRegularLocalRing hσ s

end AlgebraicGeometry.Scheme.Hom
