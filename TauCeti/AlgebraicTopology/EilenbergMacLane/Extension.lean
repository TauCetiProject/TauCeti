/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Existence

/-!
# Maps out of the presentation model of `K(A, n + 2)`

Let `W = TauCeti.sphereWedge A (n + 2)` be the wedge of `(n + 2)`-spheres indexed by an
abelian group `A`, let `ψ : Hₙ₊₂(W; ℤ) → A` be linear, and let
`Y = TauCeti.EilenbergMacLane.presentation A n ψ` be the presentation complex, obtained by
attaching an `(n + 3)`-cell along every map `g : Sⁿ⁺² → W` whose class `g_*[Sⁿ⁺²]` lies in the
kernel of `ψ`. Killing the homotopy groups of `Y` above dimension `n + 2` gives a
`K(im ψ, n + 2)`, since `πₙ₊₂(Y) ≅ Hₙ₊₂(W; ℤ) ⧸ ker ψ`; when `ψ` is surjective this is the model
`K(A, n + 2)` (`TauCeti.EilenbergMacLane.isEilenbergMacLaneSpace_killHomotopyGroups_presentation`).
This file proves the extension half of Hatcher's Lemma 4.31 and Proposition 4.30 for this model,
without assuming that `ψ` is surjective.

* **Extension over the relation cells.** A map `f : W → Z` into a space whose homotopy groups
  vanish below dimension `n + 2` extends over `Y` exactly when the induced map
  `f_* : Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` kills the kernel of `ψ`
  (`TauCeti.EilenbergMacLane.exists_cellAttachmentIncl_comp_eq_iff`). Indeed, `f_*` then kills
  the class `g_*[Sⁿ⁺²]` of every relation `g`, so `f ∘ g` is null-homologous, hence null-homotopic
  (`TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero`), and extends over the disk.
  Conversely the kernel of `ψ` dies in `Hₙ₊₂(Y; ℤ)`
  (`TauCeti.EilenbergMacLane.ker_singularHomologyMap_presentation`).
* **Extension to a weak equivalence.** If moreover `Z` is a `K(G, n + 2)` space and `f_*` is
  surjective with kernel exactly the kernel of `ψ`, then the extension induces a bijection on
  `πₙ₊₂`, by the Hurewicz theorem in `Y` and in `Z`. Since `Z` has no homotopy above dimension
  `n + 2`, it then extends further, over the cells killing the higher homotopy groups of `Y`, to a
  weak homotopy equivalence from `killHomotopyGroups (n + 3) Y`, the model `K(A, n + 2)` when `ψ`
  is surjective
  (`TauCeti.EilenbergMacLane.exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence`).

So every `K(G, n + 2)` space receiving such a map from the wedge is weakly equivalent to the
model. These statements extend a prescribed map `f`; the uniqueness theorems of
`TauCeti.AlgebraicTopology.EilenbergMacLane.Uniqueness` apply them to a map on the wedge that they
construct.

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
    (sphereWedge A (n + 2)) →ₗ[ℤ] A}
  {Z : TopCat.{0}}

/-- **The relation spheres die under a map killing the kernel of `ψ`.** If the homotopy groups
`πₖ(Z, z)` vanish for every `k < n + 2` and `f : W → Z` induces on `Hₙ₊₂(-; ℤ)` a map vanishing on
the kernel of `ψ`, then `f` composed with the attaching map of every relation cell of the
presentation complex is null-homotopic. -/
theorem nullhomotopic_relationAttach_comp {z : Z}
    (hZ : ∀ k < n + 2, Subsingleton (π_ k Z z)) (f : sphereWedge A (n + 2) ⟶ Z)
    (hf : ∀ h ∈ LinearMap.ker ψ, (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map f).hom h = 0) (r : Relation A n ψ) :
    (relationAttach A n ψ r ≫ f).hom.Nullhomotopic :=
  -- The relation sphere is null-homologous after `f`, hence null-homotopic.
  (TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero hZ _).2 <| by
    rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hf _ (LinearMap.mem_ker.2 r.property)

/-- **Extension over the presentation complex.** If the homotopy groups `πₖ(Z, z)` vanish for every
`k < n + 2`, a map `f : W → Z` from the wedge of spheres extends over the presentation complex
exactly when the induced map `Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` vanishes on the kernel of `ψ`. -/
theorem exists_cellAttachmentIncl_comp_eq_iff {z : Z}
    (hZ : ∀ k < n + 2, Subsingleton (π_ k Z z)) (f : sphereWedge A (n + 2) ⟶ Z) :
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
    have hw : w ∈ LinearMap.ker ((H.map F).hom ∘ₗ (H.map ι).hom) :=
      LinearMap.mem_ker.2 (by rw [LinearMap.comp_apply]; exact hy)
    rw [hker, ← ker_singularHomologyMap_presentation A n ψ] at hw
    exact LinearMap.mem_ker.1 hw
  -- The Hurewicz isomorphisms of `Y` and `Z` intertwine the maps induced by `F`.
  let hY := HomotopyGroup.hurewiczAddEquiv (subsingleton_homotopyGroup_presentation A n ψ)
  let hZ' := HomotopyGroup.hurewiczAddEquiv hZ
  have hcomm : (hZ' ∘ Additive.ofMul) ∘ HomotopyGroup.map (N := Fin (n + 2)) F.hom hFz =
      (H.map F).hom ∘ (hY ∘ Additive.ofMul) := by
    funext a
    have h := HomotopyGroup.hurewiczAddEquiv_naturality
      (subsingleton_homotopyGroup_presentation A n ψ) hZ F.hom hFz (Additive.ofMul a)
    rw [TopCat.ofHom_hom, toMul_ofMul] at h
    exact h.symm
  have h := (hH.comp (hY.bijective.comp Additive.ofMul.bijective))
  rw [← hcomm] at h
  exact (Function.Bijective.of_comp_iff' (hZ'.bijective.comp Additive.ofMul.bijective) _).1 h

/-- **Maps out of the wedge into a `K(G, n + 2)` extend to weak equivalences out of the model.**
Let `f : W → Z` be a map from the wedge of `(n + 2)`-spheres to an Eilenberg--Mac Lane space `Z` of
type `K(G, n + 2)`, based at the image of the base point of the wedge. If the induced map
`Hₙ₊₂(W; ℤ) → Hₙ₊₂(Z; ℤ)` is surjective with kernel the kernel of `ψ`, then `f` extends to a weak
homotopy equivalence from the presentation complex with its homotopy groups above dimension `n + 2`
killed. In general this source is a `K(im ψ, n + 2)`; it is the model `K(A, n + 2)` when `ψ` is
surjective. -/
theorem exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence {G : Type*} [Group G]
    (f : sphereWedge A (n + 2) ⟶ Z)
    (hZ : IsEilenbergMacLaneSpace G (n + 2) Z (f (sphereWedgeBase A (n + 2))))
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
  obtain ⟨F₁, hF₁⟩ :=
    (exists_cellAttachmentIncl_comp_eq_iff (hZ' (f (sphereWedgeBase A (n + 2)))) f).2 fun h hh ↦ by
      rw [← hker] at hh
      exact LinearMap.mem_ker.1 hh
  -- The extension is bijective on `πₙ₊₂`, so it extends to a weak equivalence out of the model.
  obtain ⟨F, hF, hweq⟩ := F₁.exists_killHomotopyGroupsIncl_comp_eq_and_isWeakHomotopyEquivalence
    (fun k _ hk ↦ subsingleton_homotopyGroup_presentation A n ψ k hk) (hZ.of_basepoint _)
    (bijective_homotopyGroupMap_of_ker_eq (hZ' _) F₁ rfl (hF₁ ▸ hker) (hF₁ ▸ hsurj))
  exact ⟨F, by rw [hF, hF₁], hweq⟩

end EilenbergMacLane

end TauCeti
