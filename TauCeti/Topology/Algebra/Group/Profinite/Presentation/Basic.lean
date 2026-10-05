/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Profinite groups defined by generators and relators

This file constructs profinite and pro-`p` groups from generators and relators. In each case the
relators are quotiented by their **closed** normal closure, so the result remains profinite. The
quotient maps and factorisation theorems let maps out of a presented group be specified on its
generators together with the condition that they kill its relators.

The profinite construction allows finite quotients of any order. The pro-`p` construction starts
with the free pro-`p` group and therefore retains only finite `p`-group quotients.
Both universal properties are used to describe groups by finite sets of generators and relators.

The generators generate a presented group topologically, so a group presented on a finite type is
topologically finitely generated. With no relators the presented group is the free group of the
same kind (`presentedProfiniteGroup.equivFreeProfiniteGroup`, `presentedProP.equivFreeProP`).
Every Hausdorff group that is a continuous image of `freeProfiniteGroup X` or of `freeProP p X`
is presented on `X`, with the kernel as its set of relators
(`presentedProfiniteGroup.equivOfSurjective`, `presentedProP.equivOfSurjective`). Combined with
`IsProP.exists_surjective_freeProP`, a
topologically finitely generated pro-`p` group `G` has a presentation on any finite type with at
least `topologicalGeneratorRankNat G` elements; a presentation on exactly that many generators is
what is called a **minimal presentation** of `G`.

A presented group is functorial in its presentation: a continuous homomorphism of the underlying
free groups that sends the relators of the source into the closed normal closure of the relators
of the target induces a continuous homomorphism of the presented groups, and a topological
isomorphism of the free groups matching the two closed normal closures induces a topological
isomorphism of the presented groups. In particular a presented group depends on its relators only
through their closed normal closure. Finally, the pro-`p` group presented by the images of a set
of profinite relators is a quotient of the profinite group they present.

## Main results

* `TauCeti.presentedProfiniteGroup.existsUnique_lift`, `TauCeti.presentedProP.existsUnique_lift`:
  the universal properties.
* `TauCeti.presentedProfiniteGroup.dense_closure_range_of`,
  `TauCeti.presentedProP.dense_closure_range_of`: the generators generate topologically.
* `TauCeti.presentedProfiniteGroup.isTopologicallyFinitelyGenerated`,
  `TauCeti.presentedProP.isTopologicallyFinitelyGenerated`: a group presented on a finite type is
  topologically finitely generated.
* `TauCeti.presentedProfiniteGroup.equivFreeProfiniteGroup`, `TauCeti.presentedProP.equivFreeProP`:
  with no relators, the presented group is free.
* `TauCeti.presentedProfiniteGroup.equivOfSurjective`, `TauCeti.presentedProP.equivOfSurjective`:
  a continuous image of the free group is presented on `X` by the kernel.
* `TauCeti.IsProP.exists_continuousMulEquiv_presentedProP`: a topologically finitely generated
  pro-`p` group has a presentation on any finite type with at least `topologicalGeneratorRankNat`
  elements.
* `TauCeti.presentedProfiniteGroup.map`, `TauCeti.presentedProP.map`: functoriality in the
  generators and the relators.
* `TauCeti.presentedProfiniteGroup.congr`, `TauCeti.presentedProP.congr`: an isomorphism of the
  free groups matching the relators induces an isomorphism of the presented groups;
  `TauCeti.presentedProP.congrSingleton` is the one-relator case, for an isomorphism carrying the
  relator to the relator.
* `TauCeti.presentedProfiniteGroup.congrOfClosureEq`, `TauCeti.presentedProP.congrOfClosureEq`:
  relators with the same closed normal closure present the same group.
* `TauCeti.presentedProfiniteGroup.toPresentedProP_surjective`: a presented profinite group maps
  onto the pro-`p` group presented by the images of its relators.
* `TauCeti.presentedProPGen`: the generators of a pro-`p` group presented on `Fin n`, indexed by
  `ℕ` with value `1` out of range, as the images of `TauCeti.freeProPGen`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Chapter 3 and Section 7.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Section III.9.
* `Mathlib.GroupTheory.PresentedGroup`, whose discrete analogues `PresentedGroup.map` and
  `PresentedGroup.equivPresentedGroup` are the model for the shape of the functoriality API here.
-/

public section

namespace TauCeti

universe u v w

/-- The profinite group presented by generators `X` and relators `rels`, obtained by quotienting
the free profinite group by the closed normal closure of the relators. -/
noncomputable abbrev presentedProfiniteGroup (X : Type u)
    (rels : Set (freeProfiniteGroup X)) : Type u :=
  freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure

namespace presentedProfiniteGroup

/-- The canonical quotient map from the free profinite group to the presented profinite group. -/
noncomputable def mk {X : Type u} (rels : Set (freeProfiniteGroup X)) :
    freeProfiniteGroup X →ₜ* presentedProfiniteGroup X rels :=
  ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

/-- The canonical quotient map onto a presented profinite group is surjective. -/
theorem mk_surjective {X : Type u} (rels : Set (freeProfiniteGroup X)) :
    Function.Surjective (mk rels) :=
  QuotientGroup.mk'_surjective _

/-- The canonical generator in a presented profinite group. -/
noncomputable def of {X : Type u} (rels : Set (freeProfiniteGroup X)) (x : X) :
    presentedProfiniteGroup X rels :=
  mk rels (freeProfiniteGroup.of x)

/-- The canonical generators of a presented profinite group are the images of the free
generators under the quotient map. -/
@[simp]
theorem mk_of {X : Type u} (rels : Set (freeProfiniteGroup X)) (x : X) :
    mk rels (freeProfiniteGroup.of x) = of rels x :=
  (rfl)

variable {X : Type u} {rels : Set (freeProfiniteGroup X)}

/-- The quotient map kills every relator. -/
@[simp]
theorem mk_relator (r : freeProfiniteGroup X) (hr : r ∈ rels) : mk rels r = 1 := by
  -- Reduce the named presentation carrier and map to the quotient form accepted by Mathlib's
  -- quotient kernel criterion.
  change (r : freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1
  exact (QuotientGroup.eq_one_iff r).mpr
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr))

/-- The kernel of the presentation map consists exactly of the closed normal closure of the
relators. -/
@[simp]
theorem mk_eq_one_iff (r : freeProfiniteGroup X) :
    mk rels r = 1 ↔ r ∈ (Subgroup.normalClosure rels).topologicalClosure := by
  -- Expose the quotient representation so Mathlib's general criterion applies.
  change (r : freeProfiniteGroup X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1 ↔ _
  exact QuotientGroup.eq_one_iff r

/-- The generators generate the presented profinite group topologically. -/
theorem dense_closure_range_of :
    Dense ((Subgroup.closure (Set.range (of rels)) : Subgroup (presentedProfiniteGroup X rels)) :
      Set (presentedProfiniteGroup X rels)) := by
  -- The generators are the image of the free generators under the continuous surjection `mk`.
  have hfree : (Subgroup.closure
      (Set.range (freeProfiniteGroup.of : X → freeProfiniteGroup X))).topologicalClosure = ⊤ := by
    rw [← SetLike.coe_set_eq, Subgroup.topologicalClosure_coe, Subgroup.coe_top,
      ← dense_iff_closure_eq]
    exact freeProfiniteGroup.dense_closure_range_of X
  have h := topologicalClosure_closure_image_eq_top hfree
    (f := (mk rels : freeProfiniteGroup X →* presentedProfiniteGroup X rels))
    (map_continuous (mk rels)) (mk_surjective rels).denseRange
  rw [← Set.range_comp, ← SetLike.coe_set_eq, Subgroup.topologicalClosure_coe, Subgroup.coe_top,
    ← dense_iff_closure_eq] at h
  exact h

/-- A continuous homomorphism from the free profinite group that kills the relators factors through
the presented profinite group. -/
noncomputable def lift {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    presentedProfiniteGroup X rels →ₜ* G := by
  let R : Subgroup (freeProfiniteGroup X) := (Subgroup.normalClosure rels).topologicalClosure
  exact ContinuousMonoidHom.quotientLift R ψ
    (topologicalClosure_normalClosure_le_ker hψ)

/-- The factorisation through a presented profinite group recovers the original map after the
canonical quotient projection. -/
@[simp]
theorem lift_comp_mk {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    (lift ψ hψ).comp (mk rels) = ψ := by
  -- Unfold the presentation's lift and map only far enough to apply Mathlib's quotient
  -- factorization equation.
  change (ContinuousMonoidHom.quotientLift (Subgroup.normalClosure rels).topologicalClosure ψ
    (topologicalClosure_normalClosure_le_ker hψ)).comp
      (ContinuousMonoidHom.quotientMk (Subgroup.normalClosure rels).topologicalClosure) = ψ
  exact ContinuousMonoidHom.quotientLift_comp_quotientMk _ _ _

/-- The factorisation through a presented profinite group computes on classes as the original
map. -/
@[simp]
theorem lift_mk {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) (x : freeProfiniteGroup X) :
    lift ψ hψ (mk rels x) = ψ x :=
  DFunLike.congr_fun (lift_comp_mk ψ hψ) x

/-- The factorisation from a presented profinite group evaluates on its generators as the original
map does on the free generators. -/
@[simp]
theorem lift_of {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) (x : X) :
    lift ψ hψ (of rels x) = ψ (freeProfiniteGroup.of x) := by
  -- Reduce the named generator and lift to the quotient-map composite characterized by
  -- `lift_comp_mk`; these definitions compute by unfolding to the corresponding quotient maps.
  change (lift ψ hψ).comp (mk rels) (freeProfiniteGroup.of x) = _
  exact DFunLike.congr_fun (lift_comp_mk ψ hψ) (freeProfiniteGroup.of x)

/-- Two continuous homomorphisms out of a presented profinite group are equal if they agree after
precomposition with its quotient map. -/
theorem hom_ext {G : Type v} [Group G] [TopologicalSpace G]
    {φ ψ : presentedProfiniteGroup X rels →ₜ* G}
    (h : φ.comp (mk rels) = ψ.comp (mk rels)) : φ = ψ := by
  let R : Subgroup (freeProfiniteGroup X) :=
    (Subgroup.normalClosure rels).topologicalClosure
  let f := ψ.comp (mk rels)
  have hR : R ≤ f.ker := ContinuousMonoidHom.le_ker_comp_quotientMk R ψ
  have hφ := ContinuousMonoidHom.quotientLift_unique R f hR φ (fun x => by
    exact DFunLike.congr_fun h x)
  have hψ := ContinuousMonoidHom.quotientLift_unique R f hR ψ (fun _ => rfl)
  exact hφ.trans hψ.symm

/-- Two continuous homomorphisms out of a presented profinite group are equal if they agree on
the canonical generators. -/
@[ext]
theorem hom_ext_of {G : Type v} [Group G] [TopologicalSpace G] [T2Space G]
    {φ ψ : presentedProfiniteGroup X rels →ₜ* G}
    (h : ∀ x : X, φ (of rels x) = ψ (of rels x)) : φ = ψ := by
  apply hom_ext
  apply freeProfiniteGroup.hom_ext
  exact h

/-- A continuous homomorphism out of the free profinite group that kills the relators factors
uniquely through the presented profinite group. -/
theorem existsUnique_lift {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (ψ : freeProfiniteGroup X →ₜ* G) (hψ : ∀ r ∈ rels, ψ r = 1) :
    ∃! φ : presentedProfiniteGroup X rels →ₜ* G, φ.comp (mk rels) = ψ := by
  refine ⟨lift ψ hψ, lift_comp_mk ψ hψ, ?_⟩
  intro φ hφ
  exact hom_ext (hφ.trans (lift_comp_mk ψ hψ).symm)

/-- The factorisation through a presented profinite group is natural in the target. -/
@[simp]
theorem comp_lift {G : Type v} [Group G] [TopologicalSpace G] [T1Space G] {H : Type w} [Group H]
    [TopologicalSpace H] [T1Space H] (g : G →ₜ* H) (ψ : freeProfiniteGroup X →ₜ* G)
    (hψ : ∀ r ∈ rels, ψ r = 1) :
    g.comp (lift ψ hψ) = lift (g.comp ψ) fun r hr ↦ by
      rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, hψ r hr, map_one] :=
  hom_ext <| ContinuousMonoidHom.ext fun x ↦ by
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_mk]

/-- The factorisation through a presented profinite group of a surjection is surjective. -/
theorem lift_surjective {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    {ψ : freeProfiniteGroup X →ₜ* G} (hψ : ∀ r ∈ rels, ψ r = 1) (hs : Function.Surjective ψ) :
    Function.Surjective (lift ψ hψ) := by
  have hcomp : ⇑ψ = lift ψ hψ ∘ mk rels := funext fun x ↦ (lift_mk ψ hψ x).symm
  exact Function.Surjective.of_comp (hcomp ▸ hs)

/-- A profinite group presented on a finite type is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated [Finite X] :
    IsTopologicallyFinitelyGenerated (presentedProfiniteGroup X rels) :=
  (Set.finite_range (of rels)).isTopologicallyFinitelyGenerated <|
    SetLike.coe_injective <| by
      rw [Subgroup.topologicalClosure_coe, dense_closure_range_of.closure_eq, Subgroup.coe_top]

/-! ## Functoriality in the generators and the relators

The shape of this API follows Mathlib's discrete analogues `PresentedGroup.map` and
`PresentedGroup.equivPresentedGroup` in `Mathlib.GroupTheory.PresentedGroup`.
-/

section Map

variable {Y : Type v} {rels' : Set (freeProfiniteGroup Y)}

/-- The continuous homomorphism of presented profinite groups induced by a continuous
homomorphism of the underlying free profinite groups that sends every relator into the closed
normal closure of the target relators. -/
noncomputable def map (φ : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y)
    (hφ : ∀ r ∈ rels, mk rels' (φ r) = 1) :
    presentedProfiniteGroup X rels →ₜ* presentedProfiniteGroup Y rels' :=
  lift ((mk rels').comp φ) hφ

/-- The induced homomorphism computes on classes as the homomorphism of free profinite groups. -/
@[simp]
theorem map_mk (φ : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y)
    (hφ : ∀ r ∈ rels, mk rels' (φ r) = 1) (x : freeProfiniteGroup X) :
    map φ hφ (mk rels x) = mk rels' (φ x) :=
  lift_mk _ hφ x

/-- The induced homomorphism sends a generator to the class of its image. -/
@[simp]
theorem map_of (φ : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y)
    (hφ : ∀ r ∈ rels, mk rels' (φ r) = 1) (x : X) :
    map φ hφ (of rels x) = mk rels' (φ (freeProfiniteGroup.of x)) :=
  lift_of _ hφ x

/-- A continuous homomorphism of free profinite groups that sends the relators into the closed
normal closure of the target relators sends the whole closed normal closure into it. -/
theorem mk_eq_one_of_mk_eq_one (φ : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y)
    (hφ : ∀ r ∈ rels, mk rels' (φ r) = 1) {x : freeProfiniteGroup X} (hx : mk rels x = 1) :
    mk rels' (φ x) = 1 := by
  rw [← map_mk φ hφ x, hx, map_one]

/-- The identity of the free profinite group induces the identity of a presented group. -/
@[simp]
theorem map_id :
    map (ContinuousMonoidHom.id (freeProfiniteGroup X)) (fun _ hr ↦ mk_relator _ hr) =
      ContinuousMonoidHom.id (presentedProfiniteGroup X rels) :=
  hom_ext <| ContinuousMonoidHom.ext fun x ↦ by simp

/-- The homomorphisms induced by a composite are the composite of the induced homomorphisms. -/
theorem map_comp {Z : Type w} {rels'' : Set (freeProfiniteGroup Z)}
    (φ : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y) (hφ : ∀ r ∈ rels, mk rels' (φ r) = 1)
    (ψ : freeProfiniteGroup Y →ₜ* freeProfiniteGroup Z) (hψ : ∀ r ∈ rels', mk rels'' (ψ r) = 1) :
    (map ψ hψ).comp (map φ hφ) =
      map (ψ.comp φ) fun r hr ↦ mk_eq_one_of_mk_eq_one ψ hψ (hφ r hr) :=
  hom_ext <| ContinuousMonoidHom.ext fun x ↦ by
    -- `simp` rewrites the left-hand side; on the right the relator hypothesis carried by `map`
    -- is stated through `ψ (φ ·)` rather than `(ψ.comp φ) ·`, so the rewrite does not match
    -- there and the equation is closed by `exact` instead.
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, map_mk]
    exact (map_mk (ψ.comp φ) _ x).symm

/-- A surjection of free profinite groups induces a surjection of presented profinite groups. -/
theorem map_surjective {φ : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y}
    (hφ : ∀ r ∈ rels, mk rels' (φ r) = 1) (hs : Function.Surjective φ) :
    Function.Surjective (map φ hφ) :=
  lift_surjective hφ ((mk_surjective rels').comp hs)

/-- A topological isomorphism of the free profinite groups sending each set of relators into the
closed normal closure of the other induces a topological isomorphism of the presented profinite
groups. -/
noncomputable def congr (e : freeProfiniteGroup X ≃ₜ* freeProfiniteGroup Y)
    (h : ∀ r ∈ rels, mk rels' (e r) = 1) (h' : ∀ r ∈ rels', mk rels (e.symm r) = 1) :
    presentedProfiniteGroup X rels ≃ₜ* presentedProfiniteGroup Y rels' where
  toFun := map (e : freeProfiniteGroup X →ₜ* freeProfiniteGroup Y) fun r hr ↦ by
    simpa using h r hr
  invFun := map (e.symm : freeProfiniteGroup Y →ₜ* freeProfiniteGroup X) fun r hr ↦ by
    simpa using h' r hr
  left_inv y := by
    obtain ⟨x, rfl⟩ := mk_surjective rels y
    simp
  right_inv y := by
    obtain ⟨x, rfl⟩ := mk_surjective rels' y
    simp
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- The induced isomorphism computes on classes as the isomorphism of free profinite groups. -/
@[simp]
theorem congr_mk (e : freeProfiniteGroup X ≃ₜ* freeProfiniteGroup Y)
    (h : ∀ r ∈ rels, mk rels' (e r) = 1) (h' : ∀ r ∈ rels', mk rels (e.symm r) = 1)
    (x : freeProfiniteGroup X) : congr e h h' (mk rels x) = mk rels' (e x) :=
  map_mk _ _ x

/-- The inverse of the induced isomorphism computes on classes as the inverse isomorphism of free
profinite groups. -/
@[simp]
theorem congr_symm_mk (e : freeProfiniteGroup X ≃ₜ* freeProfiniteGroup Y)
    (h : ∀ r ∈ rels, mk rels' (e r) = 1) (h' : ∀ r ∈ rels', mk rels (e.symm r) = 1)
    (y : freeProfiniteGroup Y) : (congr e h h').symm (mk rels' y) = mk rels (e.symm y) :=
  map_mk _ _ y

end Map

/-- **Two sets of relators with the same closed normal closure present the same profinite
group**, by an isomorphism matching the classes of every element of the free profinite group. -/
noncomputable def congrOfClosureEq {rels₂ : Set (freeProfiniteGroup X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) :
    presentedProfiniteGroup X rels ≃ₜ* presentedProfiniteGroup X rels₂ :=
  congr (ContinuousMulEquiv.refl (freeProfiniteGroup X))
    (fun r hr ↦ by
      have hmem : r ∈ (Subgroup.normalClosure rels).topologicalClosure :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr)
      rw [mk_eq_one_iff, ← h]
      exact hmem)
    (fun r hr ↦ by
      have hmem : r ∈ (Subgroup.normalClosure rels₂).topologicalClosure :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr)
      rw [mk_eq_one_iff, h]
      exact hmem)

/-- The isomorphism between presentations with the same closed normal closure fixes the class of
every element of the free profinite group. -/
@[simp]
theorem congrOfClosureEq_mk {rels₂ : Set (freeProfiniteGroup X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) (x : freeProfiniteGroup X) :
    congrOfClosureEq h (mk rels x) = mk rels₂ x :=
  congr_mk _ _ _ x

/-- The inverse of the isomorphism between presentations with the same closed normal closure also
fixes the class of every element of the free profinite group. -/
@[simp]
theorem congrOfClosureEq_symm_mk {rels₂ : Set (freeProfiniteGroup X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) (x : freeProfiniteGroup X) :
    (congrOfClosureEq h).symm (mk rels₂ x) = mk rels x :=
  congr_symm_mk _ _ _ x

/-! ## The empty set of relators -/

section Empty

/-- With no relators, the presented profinite group is the free profinite group: the canonical
quotient map is a topological isomorphism. -/
noncomputable def equivFreeProfiniteGroup :
    presentedProfiniteGroup X (∅ : Set (freeProfiniteGroup X)) ≃ₜ* freeProfiniteGroup X where
  toFun := lift (ContinuousMonoidHom.id (freeProfiniteGroup X)) fun _ hr ↦ hr.elim
  invFun := mk ∅
  left_inv y := by
    have h : (mk ∅).comp (lift (ContinuousMonoidHom.id (freeProfiniteGroup X)) fun _ hr ↦ hr.elim) =
        ContinuousMonoidHom.id (presentedProfiniteGroup X ∅) :=
      hom_ext <| ContinuousMonoidHom.ext fun x ↦ by
        simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_mk,
          ContinuousMonoidHom.coe_id, id_eq]
    exact DFunLike.congr_fun h y
  right_inv y := DFunLike.congr_fun (lift_comp_mk _ _) y
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- The inverse of the isomorphism with the free profinite group is the canonical quotient map. -/
@[simp]
theorem equivFreeProfiniteGroup_symm_apply (x : freeProfiniteGroup X) :
    equivFreeProfiniteGroup.symm x = mk (∅ : Set (freeProfiniteGroup X)) x :=
  (rfl)

/-- The isomorphism with the free profinite group sends the class of an element to that
element. -/
@[simp]
theorem equivFreeProfiniteGroup_mk (x : freeProfiniteGroup X) :
    equivFreeProfiniteGroup (mk (∅ : Set (freeProfiniteGroup X)) x) = x := by
  rw [← equivFreeProfiniteGroup_symm_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The isomorphism with the free profinite group matches the generators. -/
@[simp]
theorem equivFreeProfiniteGroup_of (x : X) :
    equivFreeProfiniteGroup (of (∅ : Set (freeProfiniteGroup X)) x) = freeProfiniteGroup.of x := by
  rw [← mk_of, equivFreeProfiniteGroup_mk]

end Empty

/-! ## Continuous images of free profinite groups are presented -/

section OfSurjective

variable {G : Type v} [Group G] [TopologicalSpace G] [T2Space G]

/-- A Hausdorff group that is a continuous image of the free profinite group on `X` is presented
on `X`, with the kernel as its set of relators. Algebraically this is the first isomorphism
theorem, `QuotientGroup.liftEquiv`. -/
noncomputable def equivOfSurjective (φ : freeProfiniteGroup X →ₜ* G)
    (hφ : Function.Surjective φ) :
    presentedProfiniteGroup X ((φ : freeProfiniteGroup X →* G).ker : Set (freeProfiniteGroup X))
      ≃ₜ* G :=
  have hcont : Continuous (QuotientGroup.liftEquiv _ hφ φ.topologicalClosure_normalClosure_ker) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (map_continuous φ)
  ContinuousMulEquiv.mk (QuotientGroup.liftEquiv _ hφ φ.topologicalClosure_normalClosure_ker)
    hcont (hcont.continuous_symm_of_equiv_compact_to_t2
      (f := (QuotientGroup.liftEquiv _ hφ φ.topologicalClosure_normalClosure_ker).toEquiv))

/-- The presentation isomorphism of a continuous image sends the class of an element to its
image. -/
@[simp]
theorem equivOfSurjective_mk (φ : freeProfiniteGroup X →ₜ* G) (hφ : Function.Surjective φ)
    (x : freeProfiniteGroup X) : equivOfSurjective φ hφ (mk _ x) = φ x :=
  QuotientGroup.liftEquiv_mk _ hφ φ.topologicalClosure_normalClosure_ker x

/-- The presentation isomorphism of a continuous image matches the generators. -/
@[simp]
theorem equivOfSurjective_of (φ : freeProfiniteGroup X →ₜ* G) (hφ : Function.Surjective φ)
    (x : X) : equivOfSurjective φ hφ (of _ x) = φ (freeProfiniteGroup.of x) := by
  rw [← mk_of, equivOfSurjective_mk]

end OfSurjective

end presentedProfiniteGroup

/-- The pro-`p` group presented by generators `X` and relators `rels`, obtained by quotienting the
free pro-`p` group by the closed normal closure of the relators. -/
noncomputable abbrev presentedProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) : Type u :=
  freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure

namespace presentedProP

/-- The canonical quotient map from the free pro-`p` group to the presented pro-`p` group. -/
noncomputable def mk (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) :
    freeProP p X →ₜ* presentedProP p X rels :=
  ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

/-- The canonical quotient map onto a presented pro-`p` group is surjective. -/
theorem mk_surjective (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) :
    Function.Surjective (mk p rels) :=
  QuotientGroup.mk'_surjective _

/-- The canonical generator in a presented pro-`p` group. -/
noncomputable def of (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) (x : X) :
    presentedProP p X rels :=
  mk p rels (freeProP.of x)

/-- The canonical generators of a presented pro-`p` group are the images of the free generators
under the quotient map. -/
@[simp]
theorem mk_of (p : ℕ) {X : Type u} (rels : Set (freeProP p X)) (x : X) :
    mk p rels (freeProP.of x) = of p rels x :=
  (rfl)

/-- A presented pro-`p` group is pro-`p`, since it is a quotient of a free pro-`p` group. -/
theorem isProP (p : ℕ) (X : Type u) (rels : Set (freeProP p X)) :
    IsProP p (presentedProP p X rels) :=
  (isProP_freeProP p X).quotient ((Subgroup.normalClosure rels).topologicalClosure)

variable {p : ℕ} {X : Type u} {rels : Set (freeProP p X)}

/-- The quotient map kills every relator. -/
@[simp]
theorem mk_relator (r : freeProP p X) (hr : r ∈ rels) : mk p rels r = 1 := by
  -- Reduce the named presentation carrier and map to the quotient form accepted by Mathlib's
  -- quotient kernel criterion.
  change (r : freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1
  exact (QuotientGroup.eq_one_iff r).mpr
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr))

/-- The kernel of the presentation map consists exactly of the closed normal closure of the
relators. -/
@[simp]
theorem mk_eq_one_iff (r : freeProP p X) :
    mk p rels r = 1 ↔ r ∈ (Subgroup.normalClosure rels).topologicalClosure := by
  -- Expose the quotient representation so Mathlib's general criterion applies.
  change (r : freeProP p X ⧸ (Subgroup.normalClosure rels).topologicalClosure) = 1 ↔ _
  exact QuotientGroup.eq_one_iff r

/-- The kernel of the quotient map onto a presented pro-`p` group is the closed normal closure of
the relators. -/
@[simp] theorem ker_mk :
    (mk p rels : freeProP p X →* presentedProP p X rels).ker =
      (Subgroup.normalClosure rels).topologicalClosure :=
  Subgroup.ext fun r ↦ MonoidHom.mem_ker.trans (mk_eq_one_iff r)

/-- The generators generate the presented pro-`p` group topologically. -/
theorem dense_closure_range_of :
    Dense ((Subgroup.closure (Set.range (of p rels)) : Subgroup (presentedProP p X rels)) :
      Set (presentedProP p X rels)) := by
  -- The generators are the image of the free generators under the continuous surjection `mk`.
  have h := topologicalClosure_closure_image_eq_top
    (freeProP.topologicalClosure_closure_range_of_eq_top p X)
    (f := (mk p rels : freeProP p X →* presentedProP p X rels))
    (map_continuous (mk p rels)) (mk_surjective p rels).denseRange
  rw [← Set.range_comp, ← SetLike.coe_set_eq, Subgroup.topologicalClosure_coe, Subgroup.coe_top,
    ← dense_iff_closure_eq] at h
  exact h

/-- The generators generate the presented pro-`p` group topologically, as an equation of
subgroups. -/
theorem topologicalClosure_closure_range_of_eq_top :
    (Subgroup.closure (Set.range (of p rels))).topologicalClosure = ⊤ :=
  SetLike.coe_injective <| by
    rw [Subgroup.topologicalClosure_coe, dense_closure_range_of.closure_eq, Subgroup.coe_top]

/-- A pro-`p` group presented on a finite type is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated [Finite X] :
    IsTopologicallyFinitelyGenerated (presentedProP p X rels) :=
  (Set.finite_range (of p rels)).isTopologicallyFinitelyGenerated
    topologicalClosure_closure_range_of_eq_top

/-- A continuous homomorphism from the free pro-`p` group that kills the relators factors through
the presented pro-`p` group. -/
noncomputable def lift {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    presentedProP p X rels →ₜ* P := by
  let R : Subgroup (freeProP p X) := (Subgroup.normalClosure rels).topologicalClosure
  exact ContinuousMonoidHom.quotientLift R ψ
    (topologicalClosure_normalClosure_le_ker hψ)

/-- The factorisation through a presented pro-`p` group recovers the original map after the
canonical quotient projection. -/
@[simp]
theorem lift_comp_mk {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    (lift ψ hψ).comp (mk p rels) = ψ := by
  -- Unfold the presentation's lift and map only far enough to apply Mathlib's quotient
  -- factorization equation.
  change (ContinuousMonoidHom.quotientLift (Subgroup.normalClosure rels).topologicalClosure ψ
    (topologicalClosure_normalClosure_le_ker hψ)).comp
      (ContinuousMonoidHom.quotientMk (Subgroup.normalClosure rels).topologicalClosure) = ψ
  exact ContinuousMonoidHom.quotientLift_comp_quotientMk _ _ _

/-- The factorisation through a presented pro-`p` group computes on classes as the original
map. -/
@[simp]
theorem lift_mk {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) (x : freeProP p X) :
    lift ψ hψ (mk p rels x) = ψ x :=
  DFunLike.congr_fun (lift_comp_mk ψ hψ) x

/-- The factorisation from a presented pro-`p` group evaluates on its generators as the original
map does on the free generators. -/
@[simp]
theorem lift_of {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) (x : X) :
    lift ψ hψ (of p rels x) = ψ (freeProP.of x) := by
  -- Reduce the named generator and lift to the quotient-map composite characterized by
  -- `lift_comp_mk`; these definitions compute by unfolding to the corresponding quotient maps.
  change (lift ψ hψ).comp (mk p rels) (freeProP.of x) = _
  exact DFunLike.congr_fun (lift_comp_mk ψ hψ) (freeProP.of x)

/-- Two continuous homomorphisms out of a presented pro-`p` group are equal if they agree after
precomposition with its quotient map. -/
theorem hom_ext {P : Type v} [Group P] [TopologicalSpace P]
    {φ ψ : presentedProP p X rels →ₜ* P}
    (h : φ.comp (mk p rels) = ψ.comp (mk p rels)) : φ = ψ := by
  let R : Subgroup (freeProP p X) := (Subgroup.normalClosure rels).topologicalClosure
  let f := ψ.comp (mk p rels)
  have hR : R ≤ f.ker := ContinuousMonoidHom.le_ker_comp_quotientMk R ψ
  have hφ := ContinuousMonoidHom.quotientLift_unique R f hR φ (fun x => by
    exact DFunLike.congr_fun h x)
  have hψ := ContinuousMonoidHom.quotientLift_unique R f hR ψ (fun _ => rfl)
  exact hφ.trans hψ.symm

/-- Two continuous homomorphisms out of a presented pro-`p` group are equal if they agree on
the canonical generators. -/
@[ext]
theorem hom_ext_of {P : Type v} [Group P] [TopologicalSpace P] [T2Space P]
    {φ ψ : presentedProP p X rels →ₜ* P}
    (h : ∀ x : X, φ (of p rels x) = ψ (of p rels x)) : φ = ψ := by
  apply hom_ext
  apply freeProP.hom_ext
  exact h

/-- A continuous homomorphism out of the free pro-`p` group that kills the relators factors
uniquely through the presented pro-`p` group. -/
theorem existsUnique_lift {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    (ψ : freeProP p X →ₜ* P) (hψ : ∀ r ∈ rels, ψ r = 1) :
    ∃! φ : presentedProP p X rels →ₜ* P, φ.comp (mk p rels) = ψ := by
  refine ⟨lift ψ hψ, lift_comp_mk ψ hψ, ?_⟩
  intro φ hφ
  exact hom_ext (hφ.trans (lift_comp_mk ψ hψ).symm)

/-- The factorisation through a presented pro-`p` group is natural in the target. -/
@[simp]
theorem comp_lift {P : Type v} [Group P] [TopologicalSpace P] [T1Space P] {Q : Type w} [Group Q]
    [TopologicalSpace Q] [T1Space Q] (g : P →ₜ* Q) (ψ : freeProP p X →ₜ* P)
    (hψ : ∀ r ∈ rels, ψ r = 1) :
    g.comp (lift ψ hψ) = lift (g.comp ψ) fun r hr ↦ by
      rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, hψ r hr, map_one] :=
  hom_ext <| ContinuousMonoidHom.ext fun x ↦ by
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_mk]

/-- The factorisation through a presented pro-`p` group of a surjection is surjective. -/
theorem lift_surjective {P : Type v} [Group P] [TopologicalSpace P] [T1Space P]
    {ψ : freeProP p X →ₜ* P} (hψ : ∀ r ∈ rels, ψ r = 1) (hs : Function.Surjective ψ) :
    Function.Surjective (lift ψ hψ) := by
  have hcomp : ⇑ψ = lift ψ hψ ∘ mk p rels := funext fun x ↦ (lift_mk ψ hψ x).symm
  exact Function.Surjective.of_comp (hcomp ▸ hs)

/-! ## Functoriality in the generators and the relators

The shape of this API follows Mathlib's discrete analogues `PresentedGroup.map` and
`PresentedGroup.equivPresentedGroup` in `Mathlib.GroupTheory.PresentedGroup`.
-/

section Map

variable {Y : Type v} {rels' : Set (freeProP p Y)}

/-- The continuous homomorphism of presented pro-`p` groups induced by a continuous homomorphism
of the underlying free pro-`p` groups that sends every relator into the closed normal closure of
the target relators. -/
noncomputable def map (φ : freeProP p X →ₜ* freeProP p Y)
    (hφ : ∀ r ∈ rels, mk p rels' (φ r) = 1) :
    presentedProP p X rels →ₜ* presentedProP p Y rels' :=
  lift ((mk p rels').comp φ) hφ

/-- The induced homomorphism computes on classes as the homomorphism of free pro-`p` groups. -/
@[simp]
theorem map_mk (φ : freeProP p X →ₜ* freeProP p Y) (hφ : ∀ r ∈ rels, mk p rels' (φ r) = 1)
    (x : freeProP p X) : map φ hφ (mk p rels x) = mk p rels' (φ x) :=
  lift_mk _ hφ x

/-- The induced homomorphism sends a generator to the class of its image. -/
@[simp]
theorem map_of (φ : freeProP p X →ₜ* freeProP p Y) (hφ : ∀ r ∈ rels, mk p rels' (φ r) = 1)
    (x : X) : map φ hφ (of p rels x) = mk p rels' (φ (freeProP.of x)) :=
  lift_of _ hφ x

/-- A continuous homomorphism of free pro-`p` groups that sends the relators into the closed
normal closure of the target relators sends the whole closed normal closure into it. -/
theorem mk_eq_one_of_mk_eq_one (φ : freeProP p X →ₜ* freeProP p Y)
    (hφ : ∀ r ∈ rels, mk p rels' (φ r) = 1) {x : freeProP p X} (hx : mk p rels x = 1) :
    mk p rels' (φ x) = 1 := by
  rw [← map_mk φ hφ x, hx, map_one]

/-- The identity of the free pro-`p` group induces the identity of a presented group. -/
@[simp]
theorem map_id :
    map (ContinuousMonoidHom.id (freeProP p X)) (fun _ hr ↦ mk_relator _ hr) =
      ContinuousMonoidHom.id (presentedProP p X rels) :=
  hom_ext <| ContinuousMonoidHom.ext fun x ↦ by simp

/-- The homomorphisms induced by a composite are the composite of the induced homomorphisms. -/
theorem map_comp {Z : Type w} {rels'' : Set (freeProP p Z)} (φ : freeProP p X →ₜ* freeProP p Y)
    (hφ : ∀ r ∈ rels, mk p rels' (φ r) = 1) (ψ : freeProP p Y →ₜ* freeProP p Z)
    (hψ : ∀ r ∈ rels', mk p rels'' (ψ r) = 1) :
    (map ψ hψ).comp (map φ hφ) =
      map (ψ.comp φ) fun r hr ↦ mk_eq_one_of_mk_eq_one ψ hψ (hφ r hr) :=
  hom_ext <| ContinuousMonoidHom.ext fun x ↦ by
    -- `simp` rewrites the left-hand side; on the right the relator hypothesis carried by `map`
    -- is stated through `ψ (φ ·)` rather than `(ψ.comp φ) ·`, so the rewrite does not match
    -- there and the equation is closed by `exact` instead.
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, map_mk]
    exact (map_mk (ψ.comp φ) _ x).symm

/-- A surjection of free pro-`p` groups induces a surjection of presented pro-`p` groups. -/
theorem map_surjective {φ : freeProP p X →ₜ* freeProP p Y}
    (hφ : ∀ r ∈ rels, mk p rels' (φ r) = 1) (hs : Function.Surjective φ) :
    Function.Surjective (map φ hφ) :=
  lift_surjective hφ ((mk_surjective p rels').comp hs)

/-- A topological isomorphism of the free pro-`p` groups sending each set of relators into the
closed normal closure of the other induces a topological isomorphism of the presented pro-`p`
groups. -/
noncomputable def congr (e : freeProP p X ≃ₜ* freeProP p Y)
    (h : ∀ r ∈ rels, mk p rels' (e r) = 1) (h' : ∀ r ∈ rels', mk p rels (e.symm r) = 1) :
    presentedProP p X rels ≃ₜ* presentedProP p Y rels' where
  toFun := map (e : freeProP p X →ₜ* freeProP p Y) fun r hr ↦ by
    simpa using h r hr
  invFun := map (e.symm : freeProP p Y →ₜ* freeProP p X) fun r hr ↦ by
    simpa using h' r hr
  left_inv y := by
    obtain ⟨x, rfl⟩ := mk_surjective p rels y
    simp
  right_inv y := by
    obtain ⟨x, rfl⟩ := mk_surjective p rels' y
    simp
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- The induced isomorphism computes on classes as the isomorphism of free pro-`p` groups. -/
@[simp]
theorem congr_mk (e : freeProP p X ≃ₜ* freeProP p Y) (h : ∀ r ∈ rels, mk p rels' (e r) = 1)
    (h' : ∀ r ∈ rels', mk p rels (e.symm r) = 1) (x : freeProP p X) :
    congr e h h' (mk p rels x) = mk p rels' (e x) :=
  map_mk _ _ x

/-- The inverse of the induced isomorphism computes on classes as the inverse isomorphism of free
pro-`p` groups. -/
@[simp]
theorem congr_symm_mk (e : freeProP p X ≃ₜ* freeProP p Y) (h : ∀ r ∈ rels, mk p rels' (e r) = 1)
    (h' : ∀ r ∈ rels', mk p rels (e.symm r) = 1) (y : freeProP p Y) :
    (congr e h h').symm (mk p rels' y) = mk p rels (e.symm y) :=
  map_mk _ _ y

/-- A topological isomorphism of the free pro-`p` groups carrying the relator `r` to the relator
`r'` induces a topological isomorphism of the one-relator presented pro-`p` groups
`⟨X ∣ r⟩ ≃ₜ* ⟨Y ∣ r'⟩`. -/
noncomputable def congrSingleton (e : freeProP p X ≃ₜ* freeProP p Y) {r : freeProP p X}
    {r' : freeProP p Y} (h : e r = r') : presentedProP p X {r} ≃ₜ* presentedProP p Y {r'} :=
  congr e
    (fun x hx ↦ by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [h]
      exact mk_relator _ (Set.mem_singleton _))
    fun x hx ↦ by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [← h, e.symm_apply_apply]
      exact mk_relator _ (Set.mem_singleton _)

/-- The isomorphism of one-relator presented groups induced by `e` computes on classes as `e`. -/
@[simp]
theorem congrSingleton_mk (e : freeProP p X ≃ₜ* freeProP p Y) {r : freeProP p X}
    {r' : freeProP p Y} (h : e r = r') (x : freeProP p X) :
    congrSingleton e h (mk p {r} x) = mk p {r'} (e x) :=
  congr_mk _ _ _ x

/-- The inverse of the isomorphism of one-relator presented groups induced by `e` computes on
classes as `e⁻¹`. -/
@[simp]
theorem congrSingleton_symm_mk (e : freeProP p X ≃ₜ* freeProP p Y) {r : freeProP p X}
    {r' : freeProP p Y} (h : e r = r') (y : freeProP p Y) :
    (congrSingleton e h).symm (mk p {r'} y) = mk p {r} (e.symm y) :=
  congr_symm_mk _ _ _ y

end Map

/-- **Two sets of relators with the same closed normal closure present the same pro-`p` group**,
by an isomorphism matching the classes of every element of the free pro-`p` group. -/
noncomputable def congrOfClosureEq {rels₂ : Set (freeProP p X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) :
    presentedProP p X rels ≃ₜ* presentedProP p X rels₂ :=
  congr (ContinuousMulEquiv.refl (freeProP p X))
    (fun r hr ↦ by
      have hmem : r ∈ (Subgroup.normalClosure rels).topologicalClosure :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr)
      rw [mk_eq_one_iff, ← h]
      exact hmem)
    (fun r hr ↦ by
      have hmem : r ∈ (Subgroup.normalClosure rels₂).topologicalClosure :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr)
      rw [mk_eq_one_iff, h]
      exact hmem)

/-- The isomorphism between presentations with the same closed normal closure fixes the class of
every element of the free pro-`p` group. -/
@[simp]
theorem congrOfClosureEq_mk {rels₂ : Set (freeProP p X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) (x : freeProP p X) :
    congrOfClosureEq h (mk p rels x) = mk p rels₂ x :=
  congr_mk _ _ _ x

/-- The inverse of the isomorphism between presentations with the same closed normal closure also
fixes the class of every element of the free pro-`p` group. -/
@[simp]
theorem congrOfClosureEq_symm_mk {rels₂ : Set (freeProP p X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) (x : freeProP p X) :
    (congrOfClosureEq h).symm (mk p rels₂ x) = mk p rels x :=
  congr_symm_mk _ _ _ x

/-! ## The empty set of relators -/

section Empty

/-- With no relators, the presented pro-`p` group is the free pro-`p` group: the canonical
quotient map is a topological isomorphism. -/
noncomputable def equivFreeProP : presentedProP p X (∅ : Set (freeProP p X)) ≃ₜ* freeProP p X where
  toFun := lift (ContinuousMonoidHom.id (freeProP p X)) fun _ hr ↦ hr.elim
  invFun := mk p ∅
  left_inv y := by
    have h : (mk p ∅).comp (lift (ContinuousMonoidHom.id (freeProP p X)) fun _ hr ↦ hr.elim) =
        ContinuousMonoidHom.id (presentedProP p X ∅) :=
      hom_ext <| ContinuousMonoidHom.ext fun x ↦ by
        simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_mk,
          ContinuousMonoidHom.coe_id, id_eq]
    exact DFunLike.congr_fun h y
  right_inv y := DFunLike.congr_fun (lift_comp_mk _ _) y
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- The inverse of the isomorphism with the free pro-`p` group is the canonical quotient map. -/
@[simp]
theorem equivFreeProP_symm_apply (x : freeProP p X) :
    equivFreeProP.symm x = mk p (∅ : Set (freeProP p X)) x :=
  (rfl)

/-- The isomorphism with the free pro-`p` group sends the class of an element to that element. -/
@[simp]
theorem equivFreeProP_mk (x : freeProP p X) :
    equivFreeProP (mk p (∅ : Set (freeProP p X)) x) = x := by
  rw [← equivFreeProP_symm_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The isomorphism with the free pro-`p` group matches the generators. -/
@[simp]
theorem equivFreeProP_of (x : X) :
    equivFreeProP (of p (∅ : Set (freeProP p X)) x) = freeProP.of x := by
  rw [← mk_of, equivFreeProP_mk]

end Empty

/-! ## Continuous images of free pro-`p` groups are presented -/

section OfSurjective

variable {G : Type v} [Group G] [TopologicalSpace G] [T2Space G]

/-- A Hausdorff group that is a continuous image of the free pro-`p` group on `X` is presented on
`X`, with the kernel as its set of relators. Algebraically this is the first isomorphism theorem,
`QuotientGroup.liftEquiv`. -/
noncomputable def equivOfSurjective (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ) :
    presentedProP p X ((φ : freeProP p X →* G).ker : Set (freeProP p X)) ≃ₜ* G :=
  have hcont : Continuous (QuotientGroup.liftEquiv _ hφ φ.topologicalClosure_normalClosure_ker) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (map_continuous φ)
  ContinuousMulEquiv.mk (QuotientGroup.liftEquiv _ hφ φ.topologicalClosure_normalClosure_ker)
    hcont (hcont.continuous_symm_of_equiv_compact_to_t2
      (f := (QuotientGroup.liftEquiv _ hφ φ.topologicalClosure_normalClosure_ker).toEquiv))

/-- The presentation isomorphism of a continuous image sends the class of an element to its
image. -/
@[simp]
theorem equivOfSurjective_mk (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ)
    (x : freeProP p X) : equivOfSurjective φ hφ (mk p _ x) = φ x :=
  QuotientGroup.liftEquiv_mk _ hφ φ.topologicalClosure_normalClosure_ker x

/-- The presentation isomorphism of a continuous image matches the generators. -/
@[simp]
theorem equivOfSurjective_of (φ : freeProP p X →ₜ* G) (hφ : Function.Surjective φ) (x : X) :
    equivOfSurjective φ hφ (of p _ x) = φ (freeProP.of x) := by
  rw [← mk_of, equivOfSurjective_mk]

end OfSurjective

end presentedProP

/-! ## From a profinite presentation to a pro-`p` presentation -/

namespace presentedProfiniteGroup

variable {X : Type u}

/-- The canonical continuous homomorphism from a presented profinite group to the pro-`p` group
presented on the same generators by the images of the relators in the free pro-`p` group. -/
noncomputable def toPresentedProP (p : ℕ) (rels : Set (freeProfiniteGroup X)) :
    presentedProfiniteGroup X rels →ₜ*
      presentedProP p X (freeProP.fromFreeProfiniteGroup p X '' rels) :=
  lift ((presentedProP.mk p _).comp (freeProP.fromFreeProfiniteGroup p X))
    fun _ hr ↦ presentedProP.mk_relator _ ⟨_, hr, rfl⟩

/-- The comparison homomorphism computes on classes through the canonical map to the free pro-`p`
group. -/
@[simp]
theorem toPresentedProP_mk (p : ℕ) (rels : Set (freeProfiniteGroup X))
    (x : freeProfiniteGroup X) :
    toPresentedProP p rels (mk rels x) =
      presentedProP.mk p _ (freeProP.fromFreeProfiniteGroup p X x) :=
  lift_mk _ _ x

/-- The comparison homomorphism matches the canonical generators. -/
@[simp]
theorem toPresentedProP_of (p : ℕ) (rels : Set (freeProfiniteGroup X)) (x : X) :
    toPresentedProP p rels (of rels x) = presentedProP.of p _ x := by
  rw [← mk_of, toPresentedProP_mk, freeProP.fromFreeProfiniteGroup_of, presentedProP.mk_of]

/-- **A presented profinite group maps onto the pro-`p` group presented by the images of its
relators.** -/
theorem toPresentedProP_surjective (p : ℕ) (rels : Set (freeProfiniteGroup X)) :
    Function.Surjective (toPresentedProP p rels) :=
  lift_surjective _ ((presentedProP.mk_surjective p _).comp
    freeProP.fromFreeProfiniteGroup_surjective)

end presentedProfiniteGroup

/-! ## Presentations of topologically finitely generated pro-`p` groups -/

section Existence

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Every topologically finitely generated pro-`p` group has a presentation** on any finite type
with at least `topologicalGeneratorRankNat G` elements, in particular on a type with exactly
`topologicalGeneratorRankNat G` elements, which is what a *minimal presentation* means. -/
theorem IsProP.exists_continuousMulEquiv_presentedProP (hG : IsProP p G)
    (h : IsTopologicallyFinitelyGenerated G) (X : Type u) [Finite X]
    (hX : topologicalGeneratorRankNat G h ≤ Nat.card X) :
    ∃ rels : Set (freeProP p X), Nonempty (presentedProP p X rels ≃ₜ* G) := by
  obtain ⟨φ, hφ⟩ := hG.exists_surjective_freeProP h X hX
  exact ⟨_, ⟨presentedProP.equivOfSurjective φ hφ⟩⟩

end Existence

/-! ## The generators of a presentation on `Fin n`, indexed by `ℕ` -/

section NatIndexed

variable (p n : ℕ) (rels : Set (freeProP p (Fin n)))

/-- The generators of a pro-`p` group presented on `Fin n`, indexed by `ℕ` with value `1` out of
range: the images of `TauCeti.freeProPGen`. -/
noncomputable def presentedProPGen (i : ℕ) : presentedProP p (Fin n) rels :=
  presentedProP.mk p rels (freeProPGen p n i)

/-- The quotient map carries `freeProPGen` to `presentedProPGen`. -/
@[simp]
theorem presentedProP.mk_freeProPGen (i : ℕ) :
    presentedProP.mk p rels (freeProPGen p n i) = presentedProPGen p n rels i :=
  (rfl)

/-- In range, `presentedProPGen p n rels i` is the `i`-th canonical generator. -/
@[simp]
theorem presentedProPGen_of_lt {i : ℕ} (h : i < n) :
    presentedProPGen p n rels i = presentedProP.of p rels ⟨i, h⟩ := by
  rw [← presentedProP.mk_freeProPGen, freeProPGen_of_lt p h, presentedProP.mk_of]

/-- Out of range, `presentedProPGen p n rels i` is `1`. -/
@[simp]
theorem presentedProPGen_eq_one_of_le {i : ℕ} (h : n ≤ i) : presentedProPGen p n rels i = 1 := by
  rw [← presentedProP.mk_freeProPGen, freeProPGen_eq_one_of_le p h, map_one]

/-- On the values of `Fin n`, `presentedProPGen p n rels` is the canonical generator. -/
theorem presentedProPGen_val (i : Fin n) :
    presentedProPGen p n rels i = presentedProP.of p rels i := by
  rw [← presentedProP.mk_freeProPGen, freeProPGen_val, presentedProP.mk_of]

/-- The value of a homomorphism on the `ℕ`-indexed generators of a presented group. -/
theorem map_presentedProPGen {K F : Type*} [Group K] [FunLike F (presentedProP p (Fin n) rels) K]
    [MonoidHomClass F (presentedProP p (Fin n) rels) K] (φ : F) (i : ℕ) :
    φ (presentedProPGen p n rels i) =
      if h : i < n then φ (presentedProP.of p rels ⟨i, h⟩) else 1 := by
  split_ifs with h
  · rw [presentedProPGen_of_lt p n rels h]
  · rw [presentedProPGen_eq_one_of_le p n rels (not_lt.mp h), map_one]

/-- The quotient map carries the tuple `freeProPGen` to the tuple `presentedProPGen`: the
function-level form of `TauCeti.presentedProP.mk_freeProPGen`, which lets a word read on
`presentedProPGen` be pulled back along the quotient map to the same word on `freeProPGen`. -/
@[simp]
theorem presentedProP.mk_comp_freeProPGen :
    ⇑(presentedProP.mk p rels) ∘ freeProPGen p n = presentedProPGen p n rels :=
  funext (presentedProP.mk_freeProPGen p n rels)

/-- A continuous homomorphism of the presented group, pulled back to the free group along the
quotient map, takes on the `ℕ`-indexed free generators its values on `presentedProPGen`. -/
theorem presentedProP.comp_mk_freeProPGen {K : Type*} [Monoid K] [TopologicalSpace K]
    (φ : presentedProP p (Fin n) rels →ₜ* K) (i : ℕ) :
    (φ.comp (presentedProP.mk p rels)) (freeProPGen p n i) = φ (presentedProPGen p n rels i) := by
  rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, presentedProP.mk_freeProPGen]

end NatIndexed

end TauCeti
