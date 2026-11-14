/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The reduced induced closed subscheme

For a closed subset `Z` of a scheme `X`, Mathlib's vanishing ideal sheaf
`Scheme.IdealSheafData.vanishingIdeal Z` cuts out the reduced induced closed subscheme structure
on `Z`. On an affine open `U` its ideal is the vanishing ideal of a set of primes of `Γ(X, U)`,
hence radical, so this closed subscheme is reduced. When `Z` is irreducible it is therefore an
integral scheme, and its generic point is the generic point of `Z`. In particular, the closure of
a point `η`, with its reduced induced structure, is an integral scheme whose generic point maps
to `η`.

These facts let a prime divisor `closure {η}` be used as an integral curve on a surface, for
instance an irreducible component of the special fibre of a regular model of a curve over a
discrete valuation ring.

## Main results

* `Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`: the reduced induced closed
  subscheme is reduced.
* `Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal`: on an irreducible closed subset it
  is integral.
* `Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure_singleton`: the generic
  point of the reduced closure of `η` maps to `η`.
* `Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset`: a morphism from a reduced scheme
  with image in `Z` kills the vanishing ideal of `Z`, so it factors through the reduced induced
  closed subscheme.
* `Scheme.isReduced_subscheme_nilradical`, `Scheme.Hom.nilradical_le_ker`: the case `Z = ⊤`. The
  reduction `X.nilradical.subscheme` is reduced, and every morphism from a reduced scheme kills
  the nilradical, so it factors through the reduction.
* `Scheme.isOpenImmersion_of_comp_nilradical_subschemeι`: over an affine open `Spec A → X`, the
  lift of `Spec (A ⧸ nilradical A) → X` to the reduction is an open immersion.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Example II.3.2.6: the reduced
  induced closed subscheme structure.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The reduced induced closed subscheme structure on a closed subset is reduced. -/
instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have (U : X.affineOpens) : IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := by
    have : _root_.IsReduced (Γ(X, U) ⧸ (vanishingIdeal Z).ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (by
        rw [vanishingIdeal_ideal]
        exact PrimeSpectrum.isRadical_vanishingIdeal _)
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, U) ⧸ (vanishingIdeal Z).ideal U))))
  -- The cover is indexed by the affine opens of `X`, with charts `Spec (Γ(X, U) ⧸ I(U))`; the
  -- instance argument is passed explicitly because its index type is not unfolded by search.
  exact @IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover this

/-- The reduced induced closed subscheme on an irreducible closed subset is irreducible. -/
theorem irreducibleSpace_subscheme_vanishingIdeal {Z : Closeds X}
    (hZ : IsIrreducible (Z : Set X)) : IrreducibleSpace (vanishingIdeal Z).subscheme :=
  -- The points of `I.subscheme` are those of the support of `I` (`subschemeι_apply`), here `Z`.
  Subtype.irreducibleSpace hZ

/-- The reduced induced closed subscheme on an irreducible closed subset is integral. -/
theorem isIntegral_subscheme_vanishingIdeal {Z : Closeds X} (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (vanishingIdeal Z).subscheme :=
  have := irreducibleSpace_subscheme_vanishingIdeal hZ
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The closure of a point, with its reduced induced closed subscheme structure, is integral. -/
instance isIntegral_subscheme_vanishingIdeal_closure_singleton (η : X) :
    IsIntegral (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subscheme :=
  isIntegral_subscheme_vanishingIdeal isIrreducible_singleton.closure

/-- The generic point of the closure of a point `η`, with its reduced induced closed subscheme
structure, maps to `η`. -/
@[simp]
theorem subschemeι_genericPoint_vanishingIdeal_closure_singleton (η : X) :
    (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subschemeι
      (genericPoint (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subscheme) = η := by
  have h := (genericPoint_spec (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subscheme).image
    (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).subschemeι.continuous
  rw [Set.image_univ, range_subschemeι, coe_support_vanishingIdeal, Closeds.coe_mk,
    closure_closure] at h
  exact h.eq isGenericPoint_closure

/-- A morphism `f` from a reduced scheme whose image lies in a closed subset `Z` kills the
vanishing ideal of `Z`, so it factors through the reduced induced closed subscheme on `Z`
(`IsClosedImmersion.lift` along `subschemeι`): a section vanishing on `Z` pulls back to a section
with empty nonvanishing locus, which is zero on a reduced scheme. -/
theorem vanishingIdeal_le_ker_of_range_subset {Y : Scheme.{u}} [IsReduced Y] (f : Y ⟶ X)
    {Z : Closeds X} (h : Set.range f ⊆ Z) : vanishingIdeal Z ≤ f.ker := by
  refine le_ofIdeals_iff.mpr fun U s hs ↦ RingHom.mem_ker.mpr (eq_zero_of_basicOpen_eq_bot _ ?_)
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  rintro y hy
  have hZ : f y ∈ X.zeroLocus (U := U.1) ((vanishingIdeal Z).ideal U) :=
    (mem_support_iff_of_mem (X.basicOpen_le s hy)).mp <| by
      rw [← SetLike.mem_coe, coe_support_vanishingIdeal]
      exact h ⟨y, rfl⟩
  exact (X.mem_zeroLocus_iff _ _).mp hZ s hs hy

/-- The reduction `X.nilradical.subscheme` of a scheme is reduced. -/
instance _root_.AlgebraicGeometry.Scheme.isReduced_subscheme_nilradical (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme := by
  rw [← vanishingIdeal_top]
  infer_instance

/-- A morphism from a reduced scheme kills the nilradical of its target, so it factors
through the reduction `X.nilradical.subscheme` (`IsClosedImmersion.lift` along `subschemeι`). -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.nilradical_le_ker {Y : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) : X.nilradical ≤ f.ker := by
  rw [← vanishingIdeal_top]
  exact vanishingIdeal_le_ker_of_range_subset f (by simp)

/-- Over an affine open `i : Spec A ⟶ X`, a lift `j` of `Spec (A ⧸ nilradical A) ⟶ Spec A ⟶ X`
to the reduction `X.nilradical.subscheme` is an open immersion: it identifies
`Spec (A ⧸ nilradical A)` with the pullback of `i` along `X.nilradical.subschemeι`. -/
theorem _root_.AlgebraicGeometry.Scheme.isOpenImmersion_of_comp_nilradical_subschemeι
    {A : CommRingCat.{u}} (i : Spec A ⟶ X) [IsOpenImmersion i]
    (j : Spec (.of (A ⧸ _root_.nilradical A)) ⟶ X.nilradical.subscheme)
    (hj : j ≫ X.nilradical.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (_root_.nilradical A))) ≫ i) :
    IsOpenImmersion j := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (_root_.nilradical A)))
  -- `j` is the composite of the comparison map `l` into the pullback with its second projection.
  let l := Limits.pullback.lift q j hj.symm
  have hl : l ≫ Limits.pullback.fst i X.nilradical.subschemeι = q :=
    Limits.pullback.lift_fst _ _ _
  have : IsClosedImmersion (l ≫ Limits.pullback.fst i X.nilradical.subschemeι) := by
    rw [hl]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have := IsClosedImmersion.of_comp_isClosedImmersion l
    (Limits.pullback.fst i X.nilradical.subschemeι)
  have : Surjective l := by
    -- Every prime of `A` contains the nilradical, so `q` is surjective.
    have hq : Function.Surjective q := by
      rw [funext (Spec.map_apply _)]
      exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).2
    refine ⟨fun p ↦ ?_⟩
    obtain ⟨y, hy⟩ := hq (Limits.pullback.fst i X.nilradical.subschemeι p)
    refine ⟨y, (Limits.pullback.fst i X.nilradical.subschemeι).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hy]
  -- The pullback is reduced, being open in the reduction, so the surjective closed immersion `l`
  -- is an isomorphism.
  have : IsReduced (Limits.pullback i X.nilradical.subschemeι) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd i X.nilradical.subschemeι)
  have := isIso_of_isClosedImmersion_of_surjective l
  rw [← Limits.pullback.lift_snd q j hj.symm]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
