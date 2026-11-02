/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration
public import TauCeti.AlgebraicGeometry.LineBundle.LocalBasis
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic

/-!
# Line bundles on local and discrete schemes are trivial

If every point of a scheme `X` specializes to a single point `x`, then the only open subset of
`X` containing `x` is `X` itself. A line bundle is trivial on some open neighbourhood of `x`, so it
is trivial on `X`, and the Picard group of `X` is trivial. This applies to the spectrum of a local
ring, and in particular to the spectrum of a field.

If instead the underlying space of `X` is discrete, as for a scheme finite over a field, each point
is an open subset on which a line bundle has a basis, and these bases glue to a global basis; so
the Picard group of `X` is again trivial.

The triviality of `Pic(Spec K)` for a field `K` is what makes invariants of line bundles computed
on the fibres `Spec K ×_T X_T` of a base change insensitive to line bundles pulled back from the
base `T`.

## Main declarations

* `TauCeti.AlgebraicGeometry.LineBundleClass.eq_one_of_forall_specializes`: on a scheme in which
  every point specializes to a fixed point, every line-bundle class is trivial;
* `TauCeti.AlgebraicGeometry.LineBundleClass.subsingleton_spec_of_isLocalRing`: the Picard group
  of the spectrum of a local ring is trivial;
* `TauCeti.AlgebraicGeometry.LineBundleClass.eq_one_of_discreteTopology` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.subsingleton_of_discreteTopology`: the Picard group
  of a scheme with discrete underlying space is trivial.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- **Line bundles on a local scheme are trivial.** If every point of `X` specializes to `x`, then
every line-bundle class on `X` is the identity. -/
theorem eq_one_of_forall_specializes {x : X} (hx : ∀ y : X, y ⤳ x) (a : LineBundleClass X) :
    a = 1 := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  obtain ⟨V, e, hxV⟩ := Scheme.Modules.exists_mem_trivialization L.obj x
  -- An open subset containing `x` contains every point, since every point generalizes `x`.
  obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ ↦ (hx y).mem_open V.isOpen hxV
  have h : pullback (⊤ : X.Opens).ι (mk L) = 1 := by
    rw [pullback_mk, mk_eq_one_iff]
    exact ⟨((Scheme.Modules.restrictFunctorIsoPullback _).app L.obj).symm ≪≫
      (TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict e).symm⟩
  calc mk L = pullback X.topIso.inv (pullback (⊤ : X.Opens).ι (mk L)) := by
        rw [pullback_comp, Scheme.toIso_inv_ι, pullback_id]
    _ = 1 := by rw [h, pullback_one]

/-- **The Picard group of the spectrum of a local ring is trivial.** In particular every line
bundle on the spectrum of a field is trivial. -/
instance subsingleton_spec_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    Subsingleton (LineBundleClass (Spec (.of R))) :=
  ⟨fun a b ↦ (eq_one_of_forall_specializes IsLocalRing.specializes_closedPoint a).trans
    (eq_one_of_forall_specializes IsLocalRing.specializes_closedPoint b).symm⟩

/-- **Line bundles on a discrete scheme are trivial.** If the underlying space of `X` is discrete,
as it is for a locally Artinian scheme such as a scheme finite over a field, then every
line-bundle class on `X` is the identity. -/
theorem eq_one_of_discreteTopology [DiscreteTopology X] (a : LineBundleClass X) : a = 1 := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  choose V t hxV using fun x : X ↦ Scheme.Modules.exists_mem_trivialization L.obj x
  let U (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩
  have hUV (x : X) : U x ≤ V x := Set.singleton_subset_iff.mpr (hxV x)
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.obj.presheaf, L.obj.isSheaf⟩
  let e (x : X) : Γ(L.obj, U x) := L.obj.presheaf.map (homOfLE (hUV x)).op
    (Scheme.Modules.trivializationGenerator L.obj (t x))
  -- Distinct points are disjoint open subsets, so these local bases agree on overlaps.
  have hcompat : TopCat.Presheaf.IsCompatible L.obj.presheaf U e := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rfl
    · exact TopCat.Presheaf.section_ext F _ _ _ fun z hz ↦
        (hxy ((hz.1 : z = x).symm.trans hz.2)).elim
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U ⊤ (fun x ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, rfl⟩) e hcompat
  -- The glued section `s` restricts to a local basis near every point, so it vanishes nowhere.
  have h : ⊤ ≤ L.obj.nonvanishingLocus s := fun x _ ↦ by
    have hx := congrArg L.obj.nonvanishingLocus (hs x)
    rw [Scheme.Modules.nonvanishingLocus_map, Scheme.Modules.nonvanishingLocus_map,
      Scheme.Modules.nonvanishingLocus_trivializationGenerator] at hx
    exact (hx ▸ ⟨rfl, hxV x⟩ : x ∈ U x ⊓ L.obj.nonvanishingLocus s).2
  have := TauCeti.SheafOfModules.isIso_unitHomEquiv_symm (L.compatibleSection s) fun W ↦ by
    rw [PresheafOfModules.sections.eval, InvertibleSheaf.compatibleSection_val]
    exact (Scheme.Modules.le_nonvanishingLocus_iff s (𝟙 ⊤)).mp h W.unop W.unop.leTop
  exact mk_eq_one_iff.mpr ⟨(asIso (L.obj.unitHomEquiv.symm (L.compatibleSection s))).symm⟩

/-- **The Picard group of a discrete scheme is trivial.** -/
instance subsingleton_of_discreteTopology [DiscreteTopology X] :
    Subsingleton (LineBundleClass X) :=
  ⟨fun a b ↦ (eq_one_of_discreteTopology a).trans (eq_one_of_discreteTopology b).symm⟩

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
