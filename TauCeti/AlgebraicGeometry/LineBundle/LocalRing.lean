/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
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
line-bundle class on `X` is the identity. Each point `x` is an open subset on which a line bundle
`L` has a basis, the restriction of a local basis near `x`; these bases glue to a global section
of `L` that is a basis near every point. -/
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
    · refine F.eq_of_locally_eq' (U x ⊓ U y) (U := (PEmpty.elim : PEmpty.{u + 1} → X.Opens))
        (fun i ↦ i.elim) (fun z hz ↦ (hxy ((hz.1 : z = x).symm.trans hz.2)).elim) _ _ fun i ↦ i.elim
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U ⊤ (fun x ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, rfl⟩) e hcompat
  -- The glued section `s` is a global basis of `L`.
  let σ : L.obj.sections := PresheafOfModules.sectionsMk
    (fun W ↦ L.obj.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op s) fun W W' f ↦ by
      -- The restriction maps of the underlying presheaf of modules are those of `L.obj.presheaf`,
      -- which `rw` does not see through.
      change L.obj.presheaf.map f (L.obj.presheaf.map _ s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      -- Morphisms between two opens are unique.
      rfl
  let φ := L.obj.unitHomEquiv.symm σ
  -- The unit section of `𝒪_X` over `U x`.
  let one (x : X) : Γ(SheafOfModules.unit X.ringCatSheaf, U x) := (1 : Γ(X, U x))
  have hφ (x : X) : Scheme.Modules.Hom.app φ (U x) (one x) = e x := by
    -- The components of `φ` are those of the underlying morphism of presheaves of modules, and
    -- the sections of `𝒪_X` are those of the unit sheaf of modules; `rw` does not see through
    -- either presentation.
    erw [TauCeti.SheafOfModules.unitHomEquiv_symm_val_app, one_smul]
    exact hs x
  have : IsIso φ := by
    refine Scheme.Modules.isIso_of_forall_exists_bijective_smul φ fun x ↦
      ⟨U x, rfl, one x, fun W i ↦ ?_⟩
    have hg (r : Γ(X, W)) : r • L.obj.presheaf.map i.op (Scheme.Modules.Hom.app φ (U x) (one x)) =
        r • L.obj.presheaf.map (i ≫ homOfLE (hUV x)).op
          (Scheme.Modules.trivializationGenerator L.obj (t x)) := by
      rw [hφ, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    simp only [hg]
    refine ⟨fun r₁ r₂ h ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨r, -, hr⟩ := Scheme.Modules.existsUnique_eq_smul_map_trivializationGenerator
        L.obj (t x) (i ≫ homOfLE (hUV x)) (r₁ • L.obj.presheaf.map (i ≫ homOfLE (hUV x)).op
          (Scheme.Modules.trivializationGenerator L.obj (t x)))
      exact (hr r₁ rfl).trans (hr r₂ h).symm
    · obtain ⟨r, hr, -⟩ := Scheme.Modules.existsUnique_eq_smul_map_trivializationGenerator
        L.obj (t x) (i ≫ homOfLE (hUV x)) y
      exact ⟨r, hr.symm⟩
  exact mk_eq_one_iff.mpr ⟨(asIso φ).symm⟩

/-- **The Picard group of a discrete scheme is trivial.** -/
instance subsingleton_of_discreteTopology [DiscreteTopology X] :
    Subsingleton (LineBundleClass X) :=
  ⟨fun a b ↦ (eq_one_of_discreteTopology a).trans (eq_one_of_discreteTopology b).symm⟩

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
