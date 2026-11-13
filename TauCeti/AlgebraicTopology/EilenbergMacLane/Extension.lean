/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Existence

/-!
# Maps out of the presentation model of `K(A, n + 2)`

Let `W = TauCeti.EilenbergMacLane.wedge A n` be the wedge of `(n + 2)`-spheres indexed by an
abelian group `A`, let `ψ : Hₙ₊₂(W; ℤ) → A` be linear, and let
`Y = TauCeti.EilenbergMacLane.presentation A n ψ` be the presentation complex, obtained by
attaching an `(n + 3)`-cell along every map `g : Sⁿ⁺² → W` whose class `g_*[Sⁿ⁺²]` lies in the
kernel of `ψ`. Killing the homotopy groups of `Y` above dimension `n + 2` gives a
`K(im ψ, n + 2)`, since `πₙ₊₂(Y) ≅ Hₙ₊₂(W; ℤ) ⧸ ker ψ`; when `ψ` is surjective this is the model
`K(A, n + 2)` (`TauCeti.EilenbergMacLane.isEilenbergMacLaneSpace_killHomotopyGroups_presentation`).
This file proves the extension half of Hatcher's Lemma 4.31 and Proposition 4.30 for this model,
without assuming that `ψ` is surjective.

* **Extension over the relation cells.** A map `f : W → Z` into a space whose homotopy groups
  vanish below dimension `n + 2` at every point extends over `Y` exactly when the induced map
  `f_* : Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` kills the kernel of `ψ`
  (`TauCeti.EilenbergMacLane.exists_cellAttachmentIncl_comp_eq_iff`). Indeed, a relation `g`
  is the attaching sphere of a generalized loop `p` of `W`, whose Hurewicz class is, up to sign,
  `g_*[Sⁿ⁺²]`; so `f_*` kills it, and by the Hurewicz theorem in `Z` the class of `f ∘ p` is
  trivial, that is, `f ∘ g` is null-homotopic and extends over the disk. Conversely the kernel of
  `ψ` dies in `Hₙ₊₂(Y; ℤ)` (`TauCeti.EilenbergMacLane.ker_singularHomologyMap_presentation`).
* **Extension to a weak equivalence.** If moreover `Z` is a `K(G, n + 2)` space and `f_*` is
  surjective with kernel exactly the kernel of `ψ`, then the extension induces a bijection on
  `πₙ₊₂`, by the Hurewicz theorem in `Y` and in `Z`. Since `Z` has no homotopy above dimension
  `n + 2`, it then extends further, over the cells killing the higher homotopy groups of `Y`, to a
  weak homotopy equivalence from `killHomotopyGroups (n + 3) Y`, the model `K(A, n + 2)` when `ψ`
  is surjective
  (`TauCeti.EilenbergMacLane.exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence`).

So every `K(G, n + 2)` space receiving such a map from the wedge is weakly equivalent to the
model. What these statements leave to the caller is the map `f` itself, built sphere by sphere
from representatives of the homotopy classes of `Z`.

## Main results

* `TauCeti.EilenbergMacLane.nullhomotopic_relationAttach_comp`: a map whose homology kills the
  kernel of `ψ` makes every relation sphere null-homotopic.
* `TauCeti.EilenbergMacLane.exists_cellAttachmentIncl_comp_eq_iff`: a map from the wedge extends
  over the presentation complex exactly when its homology kills the kernel of `ψ`.
* `TauCeti.EilenbergMacLane.bijective_homotopyGroupMap_of_ker_eq`: an extension whose homology on
  the wedge is surjective with kernel the kernel of `ψ` is bijective on `πₙ₊₂`.
* `TauCeti.EilenbergMacLane.exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence`:
  such a map into a `K(G, n + 2)` extends to a weak homotopy equivalence out of the model.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Lemma 4.31 and Proposition 4.30.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti

namespace EilenbergMacLane

variable {A : Type} [AddCommGroup A] {n : ℕ}
  {ψ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
    (wedge A n) →ₗ[ℤ] A}
  {Z : TopCat.{0}}

/-- **The relation spheres die under a map killing the kernel of `ψ`.** If the homotopy groups of
`Z` vanish below dimension `n + 2` at every point and `f : W → Z` induces on `Hₙ₊₂(-; ℤ)` a map
vanishing on the kernel of `ψ`, then `f` composed with the attaching map of every relation cell of
the presentation complex is null-homotopic. -/
theorem nullhomotopic_relationAttach_comp
    (hZ : ∀ z : Z, ∀ k < n + 2, Subsingleton (π_ k Z z)) (f : wedge A n ⟶ Z)
    (hf : ∀ h ∈ LinearMap.ker ψ, (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map f).hom h = 0) (r : Relation A n ψ) :
    (relationAttach A n ψ r ≫ f).hom.Nullhomotopic := by
  -- Read the relation `g` as the attaching sphere of a generalized loop `p` of the wedge, based at
  -- the image of the north pole.
  obtain ⟨g, hr⟩ := r
  -- The attaching map `relationAttach A n ψ ⟨g, hr⟩` is `g` by definition.
  change (g ≫ f).hom.Nullhomotopic
  let p : Ω^ (Fin (n + 2)) (wedge A n) (g ⟨sphereNorthPole (n + 2)⟩) :=
    (GenLoop.sphereEquiv (n + 2) _ _).symm ⟨g.hom.comp ⟨ULift.up, continuous_uliftUp⟩, rfl⟩
  have hp : GenLoop.diskBoundaryMap p = g := GenLoop.diskBoundaryMap_sphereEquiv_symm g
  -- The Hurewicz class of `p` is, up to sign, the class of the relation, so it lies in `ker ψ`.
  obtain ⟨ε, hε⟩ := exists_singularHomologyMap_diskBoundaryMap_eq_units_smul_hurewicz (n + 1)
  have hker : (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 ∈ LinearMap.ker ψ := by
    rw [← hp, hε (wedge A n) _ p, map_zsmul] at hr
    rw [LinearMap.mem_ker]
    simpa using congrArg (((ε⁻¹ : ℤˣ) : ℤ) • ·) hr
  -- So the class of `f ∘ p` has trivial Hurewicz class, and is trivial by the Hurewicz theorem.
  rw [← hp, ← HomotopyGroup.map_mk_eq_one_iff_nullhomotopic_diskBoundaryMap_comp f rfl]
  refine (HomotopyGroup.bijective_hurewicz (hZ _)).1 ?_
  refine (congrArg (fun t ↦ ModuleCat.Hom.hom t (1 : ℤ)) (HomotopyGroup.hurewicz_map
    (ModuleCat.of ℤ ℤ) (n + 1) f.hom rfl
      (⟦p⟧ : HomotopyGroup (Fin (n + 2)) (wedge A n) _))).trans ?_
  rw [HomotopyGroup.hurewicz_mk, ModuleCat.hom_comp, LinearMap.comp_apply]
  simpa using hf _ hker

/-- **Extension over the presentation complex.** If the homotopy groups of `Z` vanish below
dimension `n + 2` at every point, a map `f : W → Z` from the wedge of spheres extends over the
presentation complex exactly when the induced map `Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` vanishes on the kernel
of `ψ`. -/
theorem exists_cellAttachmentIncl_comp_eq_iff
    (hZ : ∀ z : Z, ∀ k < n + 2, Subsingleton (π_ k Z z)) (f : wedge A n ⟶ Z) :
    (∃ F : presentation A n ψ ⟶ Z, cellAttachmentIncl (relationAttach A n ψ) ≫ F = f) ↔
      ∀ h ∈ LinearMap.ker ψ, (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ ℤ)).map f).hom h = 0 := by
  refine ⟨?_, fun hf ↦ (exists_cellAttachmentIncl_comp_eq_iff_nullhomotopic _ f).2
    (nullhomotopic_relationAttach_comp hZ f hf)⟩
  -- Conversely, the kernel of `ψ` already dies in the presentation complex.
  rintro ⟨F, rfl⟩ h hh
  rw [← ker_singularHomologyMap_presentation A n ψ] at hh
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.1 hh,
    map_zero]

/-- **The extension is bijective on `πₙ₊₂`.** Let `F : Y → Z` extend `f : W → Z` over the
presentation complex, where the homotopy groups of `Z` at the image `z` of the base point vanish
below dimension `n + 2`. If
the map `Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` induced by `f` is surjective with kernel the kernel of `ψ`, then
`F` induces a bijection `πₙ₊₂(Y) → πₙ₊₂(Z)`. -/
theorem bijective_homotopyGroupMap_of_ker_eq {z : Z}
    (hZ : ∀ k < n + 2, Subsingleton (π_ k Z z)) (F : presentation A n ψ ⟶ Z)
    (hFz : F (presentationBase A n ψ) = z)
    (hker : LinearMap.ker (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map (cellAttachmentIncl (relationAttach A n ψ) ≫ F)).hom =
        LinearMap.ker ψ)
    (hsurj : Function.Surjective (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map (cellAttachmentIncl (relationAttach A n ψ) ≫ F)).hom) :
    Function.Bijective (HomotopyGroup.map (N := Fin (n + 2)) F.hom hFz) := by
  let H := (singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)
  let ι := cellAttachmentIncl (relationAttach A n ψ)
  rw [Functor.map_comp, ModuleCat.hom_comp] at hker hsurj
  -- On `Hₙ₊₂`, the map induced by `F` is bijective: the inclusion of the wedge is onto, with
  -- kernel the kernel of `ψ`.
  have hH : Function.Bijective (H.map F).hom := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_,
      Function.Surjective.of_comp (g := (H.map ι).hom) hsurj⟩
    obtain ⟨w, rfl⟩ := surjective_singularHomologyMap_cellAttachmentIncl (relationAttach A n ψ) ℤ y
    have hw : w ∈ LinearMap.ker ((H.map F).hom ∘ₗ (H.map ι).hom) := hy
    rw [hker, ← ker_singularHomologyMap_presentation A n ψ] at hw
    exact hw
  -- The Hurewicz isomorphisms of `Y` and `Z` intertwine the maps induced by `F`.
  let hY := HomotopyGroup.hurewiczAddEquiv (subsingleton_homotopyGroup_presentation A n ψ)
  let hZ' := HomotopyGroup.hurewiczAddEquiv hZ
  have hcomm : (hZ' ∘ Additive.ofMul) ∘ HomotopyGroup.map (N := Fin (n + 2)) F.hom hFz =
      (H.map F).hom ∘ (hY ∘ Additive.ofMul) := by
    funext a
    simp only [Function.comp_apply, HomotopyGroup.hurewiczAddEquiv_apply,
      HomotopyGroup.hurewiczHom_apply, toMul_ofMul, HomotopyGroup.hurewicz_map,
      ModuleCat.hom_comp, LinearMap.comp_apply, hY, hZ', TopCat.ofHom_hom]
    -- The Hurewicz naturality is stated in degree `n + 1 + 1`, which is `n + 2` by definition.
    rfl
  have h := (hH.comp (hY.bijective.comp Additive.ofMul.bijective))
  rw [← hcomm] at h
  exact (Function.Bijective.of_comp_iff' (hZ'.bijective.comp Additive.ofMul.bijective) _).1 h

/-- **Maps out of the wedge into a `K(G, n + 2)` extend to weak equivalences out of the model.**
Let `Z` be an Eilenberg--Mac Lane space of type `K(G, n + 2)` and `f : W → Z` a map from the wedge
of `(n + 2)`-spheres, sending its base point to the base point of `Z`. If the induced map
`Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` is surjective with kernel the kernel of `ψ`, then `f` extends to a weak
homotopy equivalence from the presentation complex with its homotopy groups above dimension `n + 2`
killed. In general this source is a `K(im ψ, n + 2)`; it is the model `K(A, n + 2)` when `ψ` is
surjective. -/
theorem exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence {G : Type*} [Group G]
    {z : Z} (hZ : IsEilenbergMacLaneSpace G (n + 2) Z z) (f : wedge A n ⟶ Z)
    (hfz : f (wedgeBase A n) = z)
    (hker : LinearMap.ker (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map f).hom = LinearMap.ker ψ)
    (hsurj : Function.Surjective (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map f).hom) :
    ∃ F : killHomotopyGroups (n + 3) (presentation A n ψ) (presentationBase A n ψ) ⟶ Z,
      cellAttachmentIncl (relationAttach A n ψ) ≫
          killHomotopyGroupsIncl (n + 3) (presentation A n ψ) (presentationBase A n ψ) ≫ F = f ∧
        F.hom.IsWeakHomotopyEquivalence := by
  have hZ' (z' : Z) (k : ℕ) (hk : k < n + 2) : Subsingleton (π_ k Z z') :=
    (hZ.of_basepoint z').subsingleton_homotopyGroup hk.ne
  -- First extend over the relation cells.
  obtain ⟨F₁, hF₁⟩ := (exists_cellAttachmentIncl_comp_eq_iff hZ' f).2 fun h hh ↦ by
    rw [← hker] at hh
    exact hh
  have hF₁z : F₁ (presentationBase A n ψ) = z := by
    rw [← hfz, ← hF₁, ConcreteCategory.comp_apply]
  subst hF₁z
  -- The extension is bijective on `πₙ₊₂`, so it extends to a weak equivalence out of the model.
  have : PathConnectedSpace (presentation A n ψ) :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (presentationBase A n ψ)).2
      (subsingleton_homotopyGroup_presentation A n ψ 0 (by omega))
  obtain ⟨F, hF, hweq⟩ := F₁.exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence
    (fun k _ hk ↦ subsingleton_homotopyGroup_presentation A n ψ k hk) hZ
    (bijective_homotopyGroupMap_of_ker_eq (hZ' _) F₁ rfl (hF₁ ▸ hker) (hF₁ ▸ hsurj))
  exact ⟨F, by rw [hF, hF₁], hweq⟩

end EilenbergMacLane

end TauCeti
