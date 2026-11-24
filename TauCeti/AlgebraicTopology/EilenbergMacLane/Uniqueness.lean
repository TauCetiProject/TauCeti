/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Extension

/-!
# Maps out of the presentation model of `K(A, n + 2)`, and its uniqueness

Let `Y = TauCeti.EilenbergMacLane.presentation A n ψ` be the presentation complex of an abelian
group `A`, built from the wedge `W` of `(n + 2)`-spheres indexed by `A` and a homomorphism
`ψ : Hₙ₊₂(W; ℤ) → A` by attaching an `(n + 3)`-cell along every map `Sⁿ⁺² → W` whose class lies in
the kernel of `ψ`. Killing its homotopy groups above dimension `n + 2` gives the `K(A, n + 2)`
space `K = TauCeti.killHomotopyGroups (n + 3) Y y` of `TauCeti.exists_isEilenbergMacLaneSpace`.

This file maps this model into other spaces, following Hatcher's Lemma 4.31 and
Proposition 4.30, by constructing maps on the wedge and extending them with the results of
`TauCeti.AlgebraicTopology.EilenbergMacLane.Extension`.

* **Skeletal extension.** For an `(n + 1)`-connected space `Z` and a homomorphism
  `θ : A → Hₙ₊₂(Z; ℤ)`, there is a based map `f : Y ⟶ Z` whose restriction to the wedge induces
  `θ ∘ ψ` on `Hₙ₊₂`
  (`TauCeti.EilenbergMacLane.exists_singularHomologyMap_cellAttachmentIncl_comp_eq`).
  The generator spheres are sent to representatives of the prescribed classes
  (`TauCeti.exists_sphereWedge_singularHomologyMap_eq`). The induced map on `Hₙ₊₂` kills the
  kernel of `ψ`, so the map extends over the relation cells
  (`TauCeti.EilenbergMacLane.exists_cellAttachmentIncl_comp_eq_iff`).
* **Uniqueness.** If moreover `ψ` is surjective, `θ` is bijective and `Z` is a `K(G, n + 2)`
  space, the map on the wedge induces on `Hₙ₊₂` a surjection with kernel the kernel of `ψ`, so it
  extends to a weak homotopy equivalence `K ⟶ Z`
  (`TauCeti.EilenbergMacLane.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation`,
  through `exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence` in the namespace
  `TauCeti.EilenbergMacLane`).
  Every `K(A, n + 2)` space therefore receives a weak homotopy equivalence from the presentation
  model realizing any prescribed isomorphism `πₙ₊₂(Z) ≃ A`
  (`TauCeti.IsEilenbergMacLaneSpace.exists_isWeakHomotopyEquivalence_killHomotopyGroups`), so
  any two `K(A, n + 2)` spaces have the same weak homotopy type.
* **Homomorphisms on `πₙ₊₂`.** Into any based space `Z`, every homomorphism out of `πₙ₊₂(Y)` is
  induced by a based map (`TauCeti.EilenbergMacLane.exists_presentation_mapHom_eq`). A
  homomorphism `φ` is first realized on the wedge after the surjection `πₙ₊₂(W) → πₙ₊₂(Y)`
  (`TauCeti.exists_sphereWedge_mapHom_eq`); each relation sphere dies in `πₙ₊₂(Y)`, hence under
  that map, so the map extends over the relation cells
  (`TopCat.Hom.nullhomotopic_comp_of_ker_le`). If the homotopy groups of `Z` vanish above
  dimension `n + 2`, the map extends further over `K`
  (`TauCeti.EilenbergMacLane.exists_killHomotopyGroups_presentation_mapHom_eq`), and when `Z` is
  a `K(G, n + 2)` space every isomorphism `πₙ₊₂(K) ≃* πₙ₊₂(Z, z)` is induced by a weak homotopy
  equivalence `K ⟶ Z`
  (`exists_killHomotopyGroups_presentation_mapHom_eq_and_isWeakHomotopyEquivalence`,
  in the namespace `TauCeti.EilenbergMacLane`).

The identification of `πₙ₊₂(K)` with `A` is the one through which the presentation complex is
built: the Hurewicz isomorphism of the wedge followed by `ψ`. The map realizes the prescribed
homomorphism `θ` in this sense, on the homology of the wedge.

## Main results

* `TauCeti.EilenbergMacLane.exists_singularHomologyMap_cellAttachmentIncl_comp_eq`: Hatcher's
  Lemma 4.31 for the presentation complex.
* `TauCeti.EilenbergMacLane.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation`:
  for a bijection `θ : A → Hₙ₊₂(Z; ℤ)` into a `K(G, n + 2)` space `Z`, there is a weak homotopy
  equivalence from the presentation model to `Z` whose restriction to the wedge induces `θ ∘ ψ`.
* `TauCeti.IsEilenbergMacLaneSpace.exists_isWeakHomotopyEquivalence_killHomotopyGroups`: every
  `K(A, n + 2)` space receives a weak homotopy equivalence from the presentation model, realizing
  a prescribed isomorphism `πₙ₊₂(Z) ≃ A`.
* `TauCeti.EilenbergMacLane.exists_presentation_mapHom_eq`: Hatcher's Lemma 4.31 on `πₙ₊₂` for
  the presentation complex, into any based space.
* `TauCeti.EilenbergMacLane.exists_killHomotopyGroups_presentation_mapHom_eq`: every
  homomorphism out of `πₙ₊₂(K)` into `πₙ₊₂(Z, z)` is induced by a based map when the homotopy
  groups of `Z` vanish above dimension `n + 2`.
* `exists_killHomotopyGroups_presentation_mapHom_eq_and_isWeakHomotopyEquivalence`
  (in `TauCeti.EilenbergMacLane`): every isomorphism of `πₙ₊₂(K)` with `πₙ₊₂` of a
  `K(G, n + 2)` space `Z` is induced by a weak homotopy equivalence `K ⟶ Z`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Lemma 4.31 and Proposition 4.30.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Topology

namespace TauCeti

namespace EilenbergMacLane

variable {A : Type} [AddCommGroup A] {n : ℕ}
  {ψ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
    (sphereWedge A (n + 2)) →ₗ[ℤ] A}
  {Z : TopCat.{0}} {z : Z}

/-- **Maps out of the presentation complex** (Hatcher, Lemma 4.31). Let `Z` be a space whose
homotopy groups `πₖ(Z, z)` vanish for `k < n + 2`. For every homomorphism
`θ : A → Hₙ₊₂(Z; ℤ)` there is a map `f` from the presentation complex to `Z`, sending its base
point to `z`, whose restriction to the wedge of spheres induces `θ ∘ ψ` on `Hₙ₊₂`. -/
theorem exists_singularHomologyMap_cellAttachmentIncl_comp_eq
    (hZ : ∀ k < n + 2, Subsingleton (π_ k Z z))
    (θ : A →ₗ[ℤ] ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).obj Z) :
    ∃ f : presentation A n ψ ⟶ Z, f (presentationBase A n ψ) = z ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).map
        (cellAttachmentIncl (relationAttach A n ψ) ≫ f)).hom = θ ∘ₗ ψ := by
  -- Send the generator spheres to representatives of the prescribed classes.
  obtain ⟨g, hg, hgθ⟩ := exists_sphereWedge_singularHomologyMap_eq hZ (θ ∘ₗ ψ)
  -- The map induced by `g` kills the kernel of `ψ`, so `g` extends over the relation cells.
  obtain ⟨f, hf⟩ := (exists_cellAttachmentIncl_comp_eq_iff hZ g).2 fun h hh ↦ by
    rw [hgθ, LinearMap.comp_apply, LinearMap.mem_ker.1 hh, map_zero]
  refine ⟨f, ?_, ?_⟩
  · rw [presentationBase, ← ConcreteCategory.comp_apply, hf, hg]
  · rw [hf, hgθ]

/-- **Uniqueness of `K(A, n + 2)`** (Hatcher, Proposition 4.30). Let `ψ` be surjective, let `Z` be
a `K(G, n + 2)` space and let `θ : A → Hₙ₊₂(Z; ℤ)` be bijective. There is a weak homotopy
equivalence `F` from the presentation model `killHomotopyGroups (n + 3) (presentation A n ψ)` of
`K(A, n + 2)` to `Z`, sending the base point to `z`, whose restriction to the wedge of spheres
induces `θ ∘ ψ` on `Hₙ₊₂`. -/
theorem exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation
    (hψ : Function.Surjective ψ) {G : Type*} [Group G]
    (hZ : IsEilenbergMacLaneSpace G (n + 2) Z z)
    {θ : A →ₗ[ℤ] ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).obj Z} (hθ : Function.Bijective θ) :
    ∃ F : killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ) ⟶ Z,
      F (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
        (presentationBase A n ψ)) = z ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).map
        (cellAttachmentIncl (relationAttach A n ψ) ≫
          killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ) ≫ F)).hom =
        θ ∘ₗ ψ ∧
      F.hom.IsWeakHomotopyEquivalence := by
  -- Send the generator spheres to representatives of the prescribed classes.
  obtain ⟨g, hg, hgθ⟩ := exists_sphereWedge_singularHomologyMap_eq
    (fun k hk ↦ hZ.subsingleton_homotopyGroup hk.ne) (θ ∘ₗ ψ)
  -- Since `θ` is bijective, the map induced by `g` is onto with kernel the kernel of `ψ`.
  obtain ⟨F, hF, hFw⟩ := exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence g
    (hg ▸ hZ) (by rw [hgθ, LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hθ.injective,
      Submodule.comap_bot]) (by rw [hgθ, LinearMap.coe_comp]; exact hθ.surjective.comp hψ)
  refine ⟨F, ?_, ?_, hFw⟩
  · -- The base point of the presentation complex is the image of that of the wedge.
    have h := ConcreteCategory.congr_hom hF (sphereWedgeBase A (n + 2))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hg] at h
    exact h
  · rw [hF, hgθ]

/-! ### Realizing homomorphisms on `πₙ₊₂` -/

/-- **Every homomorphism out of `πₙ₊₂` of the presentation complex is induced by a based map**
(Hatcher, Lemma 4.31). For every homomorphism `φ : πₙ₊₂(Y) → πₙ₊₂(Z, z)` out of the homotopy group
of the presentation complex `Y = TauCeti.EilenbergMacLane.presentation A n ψ`, into any based
space, there is a based map `Y ⟶ Z` inducing `φ`. -/
theorem exists_presentation_mapHom_eq
    (φ : HomotopyGroup (Fin (n + 2)) (presentation A n ψ) (presentationBase A n ψ) →*
      HomotopyGroup (Fin (n + 2)) Z z) :
    ∃ (g : presentation A n ψ ⟶ Z) (hg : g (presentationBase A n ψ) = z),
      HomotopyGroup.mapHom g.hom hg = φ := by
  let i := cellAttachmentIncl (relationAttach A n ψ)
  -- Realize `φ` on the wedge, after the surjection `πₙ₊₂(W) → πₙ₊₂(Y)`.
  obtain ⟨gW, hgW, hφ⟩ := exists_sphereWedge_mapHom_eq (ι := A) (n := n)
    (φ.comp (HomotopyGroup.mapHom (N := Fin (n + 2)) i.hom rfl))
  -- The realizing map kills every class that dies in `Y`, so it extends over the relation cells.
  have hker : (HomotopyGroup.mapHom (N := Fin (n + 2)) i.hom rfl).ker ≤
      (HomotopyGroup.mapHom gW.hom hgW).ker := by
    rw [hφ, ← MonoidHom.comap_ker]
    exact fun a ha ↦ by rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 ha]; exact one_mem _
  have hnull (r : Relation A n ψ) : (relationAttach A n ψ r ≫ gW).hom.Nullhomotopic :=
    i.nullhomotopic_comp_of_ker_le gW rfl hgW hker _ <| by
      rw [TopCat.hom_comp]
      exact cellAttachment_attachingMap_nullhomotopic _ r
  obtain ⟨g, hig⟩ := (exists_cellAttachmentIncl_comp_eq_iff_nullhomotopic _ gW).2 hnull
  have hg : g (presentationBase A n ψ) = z := by
    rw [presentationBase, ← ConcreteCategory.comp_apply, hig]
    exact hgW
  refine ⟨g, hg, MonoidHom.ext fun a ↦ ?_⟩
  -- Both sides agree after the surjection `πₙ₊₂(W) → πₙ₊₂(Y)`.
  obtain ⟨b, rfl⟩ := surjective_homotopyGroupMap_cellAttachmentIncl (relationAttach A n ψ)
    (N := Fin (n + 2)) (by simp) (sphereWedgeBase A (n + 2)) a
  have := congrArg (· b) hφ
  simp only [HomotopyGroup.mapHom_apply, MonoidHom.comp_apply] at this ⊢
  rw [← this]
  exact congrFun (HomotopyGroup.map_comp_map_of_comp_eq (by rw [← TopCat.hom_comp, hig]) hg rfl
    hgW) b

/-- **Maps out of the presentation model of `K(A, n + 2)` realize every homomorphism on `πₙ₊₂`.**
Let `K` be the presentation complex with its homotopy groups above dimension `n + 2` killed. If the
homotopy groups `πₖ(Z, z)` vanish for every `k ≥ n + 3`, every homomorphism
`πₙ₊₂(K) → πₙ₊₂(Z, z)` is induced by a based map `K ⟶ Z`. -/
theorem exists_killHomotopyGroups_presentation_mapHom_eq
    (hZ : ∀ k, n + 3 ≤ k → Subsingleton (π_ k Z z))
    (φ : HomotopyGroup (Fin (n + 2))
        (killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ))
        (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
          (presentationBase A n ψ)) →*
      HomotopyGroup (Fin (n + 2)) Z z) :
    ∃ (F : killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ) ⟶ Z)
      (hF : F (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
        (presentationBase A n ψ)) = z),
      HomotopyGroup.mapHom F.hom hF = φ := by
  let j := killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
  -- Realize `φ` on the presentation complex, after the isomorphism induced by its inclusion, and
  -- extend over the higher cells.
  obtain ⟨g, hg, hgφ⟩ := exists_presentation_mapHom_eq
    (φ.comp (HomotopyGroup.mapHom (N := Fin (n + 2)) j.hom rfl))
  obtain ⟨F, hF⟩ := g.exists_killHomotopyGroupsIncl_comp_eq (by rw [hg]; exact hZ)
  have hFz : F (j (presentationBase A n ψ)) = z := by
    rw [← ConcreteCategory.comp_apply, hF, hg]
  refine ⟨F, hFz, MonoidHom.ext fun a ↦ ?_⟩
  obtain ⟨b, rfl⟩ := (bijective_homotopyGroupMap_killHomotopyGroupsIncl (n + 3)
    (presentation A n ψ) (presentationBase A n ψ) (N := Fin (n + 2)) (by simp)).2 a
  have := congrArg (· b) hgφ
  simp only [HomotopyGroup.mapHom_apply, MonoidHom.comp_apply] at this ⊢
  rw [← this]
  exact congrFun (HomotopyGroup.map_comp_map_of_comp_eq (by rw [← TopCat.hom_comp, hF]) hFz rfl
    hg) b

/-- **The presentation model maps to every `K(G, n + 2)` space by a weak homotopy equivalence
realizing any isomorphism on `πₙ₊₂`.** Let `K` be the space obtained from the presentation complex
by killing its homotopy groups above dimension `n + 2`. For a `K(G, n + 2)` space `Z` and an
isomorphism `φ : πₙ₊₂(K) ≃* πₙ₊₂(Z, z)`, there is a based weak homotopy equivalence `K ⟶ Z`
inducing `φ`. Here `ψ` need not be surjective. -/
theorem exists_killHomotopyGroups_presentation_mapHom_eq_and_isWeakHomotopyEquivalence
    {G : Type*} [Group G] (hZ : IsEilenbergMacLaneSpace G (n + 2) Z z)
    (φ : HomotopyGroup (Fin (n + 2))
        (killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ))
        (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
          (presentationBase A n ψ)) ≃*
      HomotopyGroup (Fin (n + 2)) Z z) :
    ∃ (F : killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ) ⟶ Z)
      (hF : F (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
        (presentationBase A n ψ)) = z),
      HomotopyGroup.mapHom F.hom hF = φ.toMonoidHom ∧ F.hom.IsWeakHomotopyEquivalence := by
  obtain ⟨F, hF, hFφ⟩ := exists_killHomotopyGroups_presentation_mapHom_eq
    (fun _ hk ↦ hZ.subsingleton_homotopyGroup (by omega)) φ.toMonoidHom
  -- The space `K` is a `K(πₙ₊₂(Y), n + 2)`, whether or not `ψ` is surjective.
  have hK := isEilenbergMacLaneSpace_killHomotopyGroups (n + 2) (presentation A n ψ)
    (presentationBase A n ψ) fun k _ hk ↦ subsingleton_homotopyGroup_presentation A n ψ k hk
  refine ⟨F, hF, hFφ, (hK.isWeakHomotopyEquivalence_iff hZ hF).2 ?_⟩
  have h : HomotopyGroup.map (N := Fin (n + 2)) F.hom hF = φ := congrArg (⇑) hFφ
  rw [h]
  exact φ.bijective

end EilenbergMacLane

open EilenbergMacLane in
/-- **Every `K(A, n + 2)` space receives a weak homotopy equivalence from the presentation
model.** For a surjection `ψ : Hₙ₊₂(W; ℤ) → A` from the homology of the wedge of spheres, a
`K(G, n + 2)` space `Z` and an isomorphism `e : πₙ₊₂(Z, z) ≃ A` (making `Z` a `K(A, n + 2)`
space), there is a weak homotopy equivalence `F` from
`killHomotopyGroups (n + 3) (presentation A n ψ)` to `Z` sending the base point to `z` and
realizing `e`: its restriction to the wedge induces `θ ∘ ψ` on `Hₙ₊₂`, where
`θ : A ≃ πₙ₊₂(Z, z) ≃ Hₙ₊₂(Z; ℤ)` is `e⁻¹` followed by the Hurewicz isomorphism. So any two
`K(A, n + 2)` spaces have the same weak homotopy type. -/
theorem IsEilenbergMacLaneSpace.exists_isWeakHomotopyEquivalence_killHomotopyGroups
    {A : Type} [AddCommGroup A] {n : ℕ}
    {Z : TopCat.{0}} {z : Z} {G : Type*} [Group G] (hZ : IsEilenbergMacLaneSpace G (n + 2) Z z)
    (e : π_ (n + 2) Z z ≃* Multiplicative A)
    {ψ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
      (sphereWedge A (n + 2)) →ₗ[ℤ] A} (hψ : Function.Surjective ψ) :
    ∃ F : killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ) ⟶ Z,
      F (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
        (presentationBase A n ψ)) = z ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).map
        (cellAttachmentIncl (relationAttach A n ψ) ≫
          killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ) ≫ F)).hom =
        ((MulEquiv.toAdditive e.symm).trans (HomotopyGroup.hurewiczAddEquiv fun _ hk ↦
          hZ.subsingleton_homotopyGroup hk.ne)).toIntLinearEquiv.toLinearMap ∘ₗ ψ ∧
      F.hom.IsWeakHomotopyEquivalence :=
  exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation hψ hZ
    ((MulEquiv.toAdditive e.symm).trans _).bijective

end TauCeti
