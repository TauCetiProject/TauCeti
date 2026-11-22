/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import TauCeti.Topology.Category.TopCat.Limits.Compact

/-!
# Continuous homomorphisms out of cofiltered limits of profinite groups

Let `c` be a limit cone over a cofiltered diagram `F : J ⥤ ProfiniteGrp`. A continuous
homomorphism from the limit `c.pt` to a discrete group factors through a stage, and two
continuous homomorphisms out of a stage that agree on the limit already agree at a later stage.
For a finite target `A` this says that the hom-sets into `A` turn the cofiltered limit into a
filtered colimit:

`Hom_cont(lim_j F_j, A) ≃ colim_j Hom_cont(F_j, A)`.

Neither surjective transition maps nor a countable or directed index are needed. This is the
group version of `Profinite.exists_locallyConstant`, and it is the finite-target half of the
universal property of the profinite completion of a pro-group.

The proof that a homomorphism factors runs as follows. Its kernel is an open subgroup of the
limit, so it contains the preimage of an open normal subgroup `N` of some stage `F_j`
(`ProfiniteGrp.exists_openNormalSubgroup_preimage_subset_of_isLimit`), and the homomorphism
factors through the image of the limit in the finite group `F_j ⧸ N`. That image is the image of
some later stage `F_k`, because open subgroups containing the image of the limit already contain
the image of a later stage (`ProfiniteGrp.exists_range_map_subset_of_isLimit`); both statements
are compactness arguments.

## Main results

* `ProfiniteGrp.exists_comp_eq_of_isLimit`: a continuous homomorphism from the limit to a
  discrete group factors through a stage.
* `ProfiniteGrp.exists_comp_map_eq_of_isLimit`: two continuous homomorphisms out of a stage that
  agree on the limit agree at a later stage.
* `ProfiniteGrp.isColimitMapCoconeOpYonedaObj`: for a finite profinite group `A`, the hom-sets
  into `A` turn a cofiltered limit cone into a filtered colimit cocone of types.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 1.1.
* A. Schmidt and J. Stix, *Anabelian geometry with étale homotopy types*, Ann. of Math. 184
  (2016), discussion before Corollary 2.5.
-/

public section

open CategoryTheory Limits

namespace ProfiniteGrp

universe u v

variable {J : Type v} [SmallCategory J] [IsCofiltered J] {F : J ⥤ ProfiniteGrp.{max u v}}
  {c : Cone F}

/-- The underlying cone of profinite spaces of a limit cone of profinite groups is a limit cone. -/
private noncomputable def isLimitMapConeForget₂ (hc : IsLimit c) :
    IsLimit ((forget₂ ProfiniteGrp Profinite).mapCone c) :=
  have : PreservesLimitsOfSize.{v, v} (forget₂ ProfiniteGrp.{max u v} Profinite) :=
    preservesLimitsOfSize_shrink.{v, u, v, u} _
  isLimitOfPreserves _ hc

/-- A closed subset of a stage that misses the image of the limit already misses the image of a
later stage: `TopCat.exists_preimage_eq_empty_of_isLimit` for the underlying topological spaces. -/
private theorem exists_preimage_map_eq_empty_of_isLimit (hc : IsLimit c) {j : J}
    {s : Set (F.obj j)} (hs : IsClosed s) (h : c.π.app j ⁻¹' s = ∅) :
    ∃ (k : J) (a : k ⟶ j), F.map a ⁻¹' s = ∅ := by
  let G : J ⥤ TopCat.{max u v} := (F ⋙ forget₂ ProfiniteGrp Profinite) ⋙ Profinite.toTopCat
  have : ∀ j, CompactSpace (G.obj j) := fun j ↦ inferInstanceAs (CompactSpace (F.obj j))
  have : ∀ j, T2Space (G.obj j) := fun j ↦ inferInstanceAs (T2Space (F.obj j))
  exact TopCat.exists_preimage_eq_empty_of_isLimit G _
    (isLimitOfPreserves Profinite.toTopCat (isLimitMapConeForget₂ hc)) hs h

/-- If an open subgroup of a stage contains the image of the limit, then it contains the image of
some later stage. The transition maps need not be surjective. -/
theorem exists_range_map_subset_of_isLimit (hc : IsLimit c) {j : J} (H : OpenSubgroup (F.obj j))
    (hH : Set.range (c.π.app j) ⊆ H) :
    ∃ (k : J) (a : k ⟶ j), Set.range (F.map a) ⊆ H := by
  obtain ⟨k, a, hk⟩ := exists_preimage_map_eq_empty_of_isLimit hc
    (s := (H : Set (F.obj j))ᶜ) H.isOpen.isClosed_compl
    (Set.eq_empty_of_forall_notMem fun x hx ↦ hx (hH ⟨x, rfl⟩))
  refine ⟨k, a, ?_⟩
  rintro _ ⟨y, rfl⟩
  by_contra hy
  exact (Set.eq_empty_iff_forall_notMem.mp hk) y hy

/-- Every open subgroup of the limit contains the preimage of an open normal subgroup of some
stage. -/
theorem exists_openNormalSubgroup_preimage_subset_of_isLimit (hc : IsLimit c)
    (U : OpenSubgroup c.pt) :
    ∃ (j : J) (N : OpenNormalSubgroup (F.obj j)),
      c.π.app j ⁻¹' (N : Set (F.obj j)) ⊆ (U : Set c.pt) := by
  obtain ⟨j, V, hV, hUV⟩ := Profinite.exists_isClopen_of_cofiltered
    ((forget₂ ProfiniteGrp Profinite).mapCone c) (isLimitMapConeForget₂ hc) U.isClopen
  let V' : Set (F.obj j) := V
  have h1 : (1 : F.obj j) ∈ V' := by
    have h : (1 : c.pt) ∈ (U : Set c.pt) := U.one_mem
    rw [hUV] at h
    -- The underlying map of profinite spaces is `c.π.app j` itself.
    have h' : (c.π.app j).hom 1 ∈ V' := h
    rwa [map_one] at h'
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    (W := V') hV h1
  refine ⟨j, N, fun x hx ↦ ?_⟩
  rw [hUV]
  exact hN hx

variable {A : Type*} [Group A] [TopologicalSpace A] [DiscreteTopology A]

/-- A continuous homomorphism from a cofiltered limit of profinite groups to a discrete group
factors through one of the stages. -/
theorem exists_comp_eq_of_isLimit (hc : IsLimit c) (f : c.pt →ₜ* A) :
    ∃ (j : J) (g : F.obj j →ₜ* A), g.comp (c.π.app j).hom = f := by
  -- The kernel of `f` contains the preimage of an open normal subgroup `N` of a stage `F_j`.
  let U : OpenSubgroup c.pt :=
    { toSubgroup := (f : c.pt →* A).ker
      isOpen' := (isOpen_discrete {1}).preimage f.continuous }
  obtain ⟨j, N, hN⟩ := exists_openNormalSubgroup_preimage_subset_of_isLimit hc U
  -- So `f` factors through the image of the limit in the finite group `F_j ⧸ N`.
  let p : c.pt →* F.obj j ⧸ N.toSubgroup :=
    (QuotientGroup.mk' N.toSubgroup).comp (c.π.app j).hom.toMonoidHom
  have hker : p.rangeRestrict.ker ≤ (f : c.pt →* A).ker := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    exact hN ((QuotientGroup.eq_one_iff _).mp hx)
  let φ : p.range →* A :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  -- The preimage of that image is an open subgroup of `F_j`, as it contains `N`.
  let H : OpenSubgroup (F.obj j) :=
    { toSubgroup := p.range.comap (QuotientGroup.mk' N.toSubgroup)
      isOpen' := Subgroup.isOpen_mono (H₁ := N.toSubgroup) (fun y hy ↦ by
        simp [Subgroup.mem_comap, (QuotientGroup.eq_one_iff y).mpr hy]) N.isOpen }
  -- A later stage `F_k` maps into it.
  obtain ⟨k, a, hk⟩ := exists_range_map_subset_of_isLimit hc H (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)
  let g₀ : F.obj k →* p.range :=
    ((QuotientGroup.mk' N.toSubgroup).comp (F.map a).hom.toMonoidHom).codRestrict p.range
      fun y ↦ hk ⟨y, rfl⟩
  have hg₀ : ∀ y ∈ (F.map a) ⁻¹' (N : Set (F.obj j)), g₀ y = 1 := fun y hy ↦
    Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hy)
  refine ⟨k, ⟨φ.comp g₀, ?_⟩, ?_⟩
  · -- The kernel of `φ ∘ g₀` contains the open subgroup `(F.map a)⁻¹ N`, so it is open.
    refine continuous_of_continuousAt_one (φ.comp g₀) ?_
    refine continuousAt_def.mpr fun s hs ↦ Filter.mem_of_superset
      (((N.isOpen).preimage (F.map a).hom.continuous).mem_nhds (by simp)) fun y hy ↦ ?_
    simpa [hg₀ y hy] using mem_of_mem_nhds hs
  · ext x
    have hx : g₀ (c.π.app k x) = p.rangeRestrict x :=
      Subtype.ext (congrArg (QuotientGroup.mk' N.toSubgroup) (c.w_apply a x))
    have hφ : (φ.comp g₀) (c.π.app k x) = f x := by
      rw [MonoidHom.comp_apply, hx]
      exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
    exact hφ

/-- Two continuous homomorphisms from a stage of a cofiltered limit of profinite groups to a
discrete group that agree on the limit already agree after a transition map. -/
theorem exists_comp_map_eq_of_isLimit (hc : IsLimit c) {j : J} {g g' : F.obj j →ₜ* A}
    (h : g.comp (c.π.app j).hom = g'.comp (c.π.app j).hom) :
    ∃ (k : J) (a : k ⟶ j), g.comp (F.map a).hom = g'.comp (F.map a).hom := by
  obtain ⟨k, a, hk⟩ := exists_preimage_map_eq_empty_of_isLimit hc
    (s := {y : F.obj j | g y ≠ g' y})
    ((isClosed_discrete {q : A × A | q.1 ≠ q.2}).preimage (g.continuous.prodMk g'.continuous))
    (Set.eq_empty_of_forall_notMem fun x hx ↦ hx (DFunLike.congr_fun h x))
  refine ⟨k, a, ContinuousMonoidHom.ext fun y ↦ ?_⟩
  by_contra hy
  exact (Set.eq_empty_iff_forall_notMem.mp hk) y hy

/-- For a finite profinite group `A`, the functor of morphisms into `A` sends a limit cone over a
cofiltered diagram of profinite groups to a colimit cocone of types: every morphism from the
limit to `A` factors through a stage, uniquely up to a later transition map. -/
noncomputable def isColimitMapCoconeOpYonedaObj (hc : IsLimit c) (A : ProfiniteGrp.{max u v})
    [Finite A] : IsColimit ((yoneda.obj A).mapCocone c.op) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun f ↦ by
      obtain ⟨j, g, hg⟩ := exists_comp_eq_of_isLimit hc f.hom
      exact ⟨Opposite.op j, ofHom g, hom_ext hg.symm⟩)
    (fun j g g' h ↦ by
      obtain ⟨k, a, hk⟩ := exists_comp_map_eq_of_isLimit hc (g := g.hom) (g' := g'.hom)
        (congrArg Hom.hom h)
      exact ⟨Opposite.op k, a.op, hom_ext hk⟩)

end ProfiniteGrp
