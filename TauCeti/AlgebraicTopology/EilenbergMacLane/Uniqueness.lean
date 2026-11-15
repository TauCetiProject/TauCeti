/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Existence
public import TauCeti.AlgebraicTopology.Homotopy.SphereWedge

/-!
# Uniqueness of the Eilenberg--Mac Lane spaces `K(A, n + 2)`

Let `A` be an abelian group, `ψ : Hₙ₊₂(W; ℤ) → A` a homomorphism out of the homology of the wedge
`W` of `(n + 2)`-spheres indexed by `A`, `Y = TauCeti.EilenbergMacLane.presentation A n ψ` the
presentation complex, and `K = TauCeti.killHomotopyGroups (n + 3) Y y` the space obtained from it by
killing the homotopy groups above dimension `n + 2`; for surjective `ψ` this `K` is a `K(A, n + 2)`
(`TauCeti.EilenbergMacLane.isEilenbergMacLaneSpace_killHomotopyGroups_presentation`).

This file proves that maps out of `K` realize every homomorphism on `πₙ₊₂`, following Hatcher's
Lemma 4.31:

1. On the wedge `W`, the classes of the spheres form a basis of `πₙ₊₂(W)`, so any homomorphism is
   realized by sending each sphere onto a representative of the image of its class
   (`TauCeti.exists_sphereWedge_mapHom_eq`).
2. A homomorphism `φ` out of `πₙ₊₂(Y)` is realized on `W` after composition with the surjection
   `πₙ₊₂(W) → πₙ₊₂(Y)`. Every relation cell is attached along a map `r : Sⁿ⁺² → W` that becomes
   null-homotopic in `Y`, so its class dies in `πₙ₊₂(Y)`, hence under the map realizing `φ`. That
   map therefore extends over the cell (`TopCat.Hom.nullhomotopic_comp_of_ker_le`), and the
   extension realizes `φ` (`TauCeti.EilenbergMacLane.exists_presentation_mapHom_eq`).
3. If the homotopy groups of the target vanish above dimension `n + 2`, the map extends over the
   higher cells of `K` (`TopCat.Hom.exists_killHomotopyGroupsIncl_comp_eq`), still realizing `φ`
   (`TauCeti.EilenbergMacLane.exists_killHomotopyGroups_presentation_mapHom_eq`).

If the target `Z` is itself a `K(G, n + 2)` and `φ` is an isomorphism, the resulting map `K ⟶ Z` is
a weak homotopy equivalence, since a map between Eilenberg--Mac Lane spaces in the same degree is
one exactly when it is bijective on that homotopy group
(`TauCeti.IsEilenbergMacLaneSpace.isWeakHomotopyEquivalence_iff`). So `K` maps by a weak homotopy
equivalence to every `K(A, n + 2)` space, of any kind
(`IsEilenbergMacLaneSpace.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation`):
the Eilenberg--Mac Lane spaces of type `K(A, n + 2)` are unique up to weak homotopy equivalence
(Hatcher, Proposition 4.30). The case of `K(G, 1)` spaces is
`TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace`.

## Main results

* `TauCeti.EilenbergMacLane.exists_presentation_mapHom_eq`: every homomorphism out of `πₙ₊₂` of
  the presentation complex is induced by a based map.
* `TauCeti.EilenbergMacLane.exists_killHomotopyGroups_presentation_mapHom_eq`: every homomorphism
  out of `πₙ₊₂(K)` into `πₙ₊₂(Z, z)` is induced by a based map when the homotopy groups of `Z`
  vanish above dimension `n + 2` (Hatcher, Lemma 4.31).
* `TauCeti.EilenbergMacLane.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation`:
  every isomorphism of `πₙ₊₂(K)` with `πₙ₊₂` of a `K(G, n + 2)` space `Z` is induced by a weak
  homotopy equivalence `K ⟶ Z`.
* `IsEilenbergMacLaneSpace.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation`:
  every `K(A, n + 2)` space receives a weak homotopy equivalence from `K` (Hatcher,
  Proposition 4.30).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Lemma 4.31 and Proposition 4.30.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology
open scoped Topology.Homotopy

namespace TauCeti

namespace EilenbergMacLane

variable {A : Type} [AddCommGroup A] {n : ℕ}
  (ψ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
    (wedge A n) →ₗ[ℤ] A)
  {Z : TopCat.{0}} {z : Z}

/-- **Every homomorphism out of `πₙ₊₂` of the presentation complex is induced by a based map.**
For every homomorphism `φ : πₙ₊₂(Y) → πₙ₊₂(Z, z)` out of the homotopy group of the presentation
complex `Y = TauCeti.EilenbergMacLane.presentation A n ψ`, into any based space, there is a based
map `Y ⟶ Z` inducing `φ`. -/
theorem exists_presentation_mapHom_eq
    (φ : HomotopyGroup (Fin (n + 2)) (presentation A n ψ) (presentationBase A n ψ) →*
      HomotopyGroup (Fin (n + 2)) Z z) :
    ∃ (g : presentation A n ψ ⟶ Z) (hg : g (presentationBase A n ψ) = z),
      HomotopyGroup.mapHom g.hom hg = φ := by
  let i := cellAttachmentIncl (relationAttach A n ψ)
  -- Work at the base point `i x₀` of the presentation complex, with `x₀` the base point of the
  -- wedge of spheres.
  let x₀ := sphereWedgeBase A (n + 2)
  have hx₀ : i x₀ = presentationBase A n ψ := congrArg i (sphereWedgeBase_def A (n + 2))
  generalize presentationBase A n ψ = y at φ hx₀ ⊢
  subst hx₀
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
  choose F hF using fun r ↦
    (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq _).1 (hnull r)
  let g := cellAttachmentLift (relationAttach A n ψ) gW F fun r ↦ (hF r).symm
  have hig : i ≫ g = gW := cellAttachmentIncl_lift _ _ _ _
  have hg : g (i x₀) = z := by
    rw [← ConcreteCategory.comp_apply, hig]
    exact hgW
  refine ⟨g, hg, MonoidHom.ext fun a ↦ ?_⟩
  -- Both sides agree after the surjection `πₙ₊₂(W) → πₙ₊₂(Y)`.
  obtain ⟨b, rfl⟩ := surjective_homotopyGroupMap_cellAttachmentIncl (relationAttach A n ψ)
    (N := Fin (n + 2)) (by simp) x₀ a
  have := congrArg (· b) hφ
  simp only [HomotopyGroup.mapHom_apply, MonoidHom.comp_apply] at this ⊢
  rw [← this]
  exact congrFun (HomotopyGroup.map_comp_map_of_comp_eq (by rw [← TopCat.hom_comp, hig]) hg rfl
    hgW) b

/-- **Maps out of the presentation model of `K(A, n + 2)` realize every homomorphism on `πₙ₊₂`**
(Hatcher, Lemma 4.31). Let `K` be the presentation complex with its homotopy groups above
dimension `n + 2` killed. If the homotopy groups `πₖ(Z, z)` vanish for every `k ≥ n + 3`, every
homomorphism `πₙ₊₂(K) → πₙ₊₂(Z, z)` is induced by a based map `K ⟶ Z`. -/
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
  obtain ⟨g, hg, hgφ⟩ := exists_presentation_mapHom_eq ψ
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

/-- **The presentation model maps by a weak homotopy equivalence to every `K(G, n + 2)` space,
realizing any isomorphism on `πₙ₊₂`.** Let `K` be the space obtained from the presentation complex
by killing its homotopy groups above dimension `n + 2`. For a `K(G, n + 2)` space `Z` and an
isomorphism `φ : πₙ₊₂(K) ≃* πₙ₊₂(Z, z)`, there is a based weak homotopy equivalence `K ⟶ Z`
inducing `φ`. -/
theorem exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation
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
  obtain ⟨F, hF, hFφ⟩ := exists_killHomotopyGroups_presentation_mapHom_eq ψ
    (fun _ hk ↦ hZ.subsingleton_homotopyGroup (by omega)) φ.toMonoidHom
  -- The space `K` is a `K(πₙ₊₂(Y), n + 2)`, whether or not `ψ` is surjective.
  have : PathConnectedSpace (presentation A n ψ) :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (presentationBase A n ψ)).2
      (subsingleton_homotopyGroup_presentation A n ψ 0 (by omega))
  have hK := isEilenbergMacLaneSpace_killHomotopyGroups (n + 2) (presentation A n ψ)
    (presentationBase A n ψ) fun k _ hk ↦ subsingleton_homotopyGroup_presentation A n ψ k hk
  refine ⟨F, hF, hFφ, (hK.isWeakHomotopyEquivalence_iff hZ hF).2 ?_⟩
  have h : HomotopyGroup.map (N := Fin (n + 2)) F.hom hF = φ := congrArg (⇑) hFφ
  rw [h]
  exact φ.bijective

end EilenbergMacLane

open EilenbergMacLane in
/-- **Uniqueness of `K(A, n + 2)` up to weak homotopy equivalence** (Hatcher, Proposition 4.30).
For a surjection `ψ`, the `K(A, n + 2)` space obtained from the presentation complex by killing its
homotopy groups above dimension `n + 2` maps by a based weak homotopy equivalence to every
`K(A, n + 2)` space `Z`. -/
theorem IsEilenbergMacLaneSpace.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation
    {A : Type} [AddCommGroup A] {n : ℕ} {Z : TopCat.{0}} {z : Z}
    (hZ : IsEilenbergMacLaneSpace (Multiplicative A) (n + 2) Z z)
    (ψ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
      (wedge A n) →ₗ[ℤ] A) (hψ : Function.Surjective ψ) :
    ∃ (F : killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ) ⟶ Z),
      F (killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ)
        (presentationBase A n ψ)) = z ∧ F.hom.IsWeakHomotopyEquivalence := by
  obtain ⟨eK⟩ := (isEilenbergMacLaneSpace_killHomotopyGroups_presentation A n ψ
    hψ).nonempty_homotopyGroupMulEquiv
  obtain ⟨eZ⟩ := hZ.nonempty_homotopyGroupMulEquiv
  obtain ⟨F, hF, -, hFw⟩ :=
    EilenbergMacLane.exists_isWeakHomotopyEquivalence_killHomotopyGroups_presentation ψ hZ
      (eK.trans eZ.symm)
  exact ⟨F, hF, hFw⟩

end TauCeti
