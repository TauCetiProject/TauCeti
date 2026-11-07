/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# Colimits of towers of cofibrations

A tower of cofibrations is a sequence of spaces `X 0 → X 1 → X 2 → ⋯`, a functor `ℕ ⥤ TopCat`,
whose bonding maps `X n → X (n + 1)` are embeddings with images having the homotopy extension
property. This file shows that the colimit of such towers is homotopy invariant: if `f : X ⟶ Y`
is a map of towers of cofibrations which is a homotopy equivalence `X n ≃ₕ Y n` at every stage,
then the induced map of colimits is a homotopy equivalence
(`TauCeti.cofibrationTowerHomotopyEquiv`). No homotopy inverses or homotopies are
given as input, and none of them need be compatible with the bonding maps; only `f` commutes
strictly with them. The colimit is any colimit cocone in `TopCat`, so it carries the final
topology of its stages.

This is how a homotopy equivalence between an infinite CW complex, built as the union of a tower
of finite subcomplexes, and a space exhausted by a tower of subspaces, such as the sublevel
sets of a proper function, is assembled from homotopy equivalences at the finite stages.

The proof has three steps.

* **Compatible left inverses.** Extending homotopy inverses one stage at a time along the
  cofibrations, by
  `TauCeti.HasHomotopyExtensionProperty.exists_inverse_extending_homotopy_of_isEmbedding`,
  gives a map of towers `g : Y ⟶ X` together with homotopies `g ∘ f ≃ id` at every stage that
  are compatible with the bonding maps (`TauCeti.exists_natTrans_homotopy_comp_id`).
* **Gluing homotopies.** Compatible homotopies at the stages glue to a homotopy on the colimit
  (`CategoryTheory.Limits.IsColimit.homotopic_map`). Read as maps into the path space
  `C(I, Z)`, compatible homotopies form a cocone, and since `I` is locally compact the induced
  map out of the colimit uncurries to a continuous homotopy. So the colimit of `g` is a left
  homotopy inverse of the colimit of `f`
  (`CategoryTheory.Limits.IsColimit.map_comp_map_homotopic_id`).
* **Two-sided inverse.** The stages of `g` are homotopy equivalences, so `g` in turn has a left
  homotopy inverse `k` on the colimits. A map with a left homotopy inverse `k` and a right
  homotopy inverse `f` is a homotopy equivalence, as `f ≃ k ∘ g ∘ f ≃ k`
  (`ContinuousMap.Homotopic.comp_homotopic_id_of_comp_homotopic_id`).

## Main results

* `CategoryTheory.Limits.IsColimit.homotopic_map`: compatible homotopies between two maps of
  towers give homotopic maps of colimits.
* `CategoryTheory.Limits.IsColimit.map_comp_map_homotopic_id`: a map of towers with a left
  homotopy inverse, through compatible homotopies, has the same property on colimits.
* `TauCeti.exists_natTrans_homotopy_comp_id`: a levelwise homotopy equivalence of towers of
  cofibrations has a left homotopy inverse which is a map of towers, with compatible homotopies.
* `TauCeti.cofibrationTowerHomotopyEquiv`: **a levelwise homotopy equivalence of towers of
  cofibrations induces a homotopy equivalence of colimits**, whose underlying map is the induced
  map (`TauCeti.cofibrationTowerHomotopyEquiv_toFun`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19, for extending homotopy inverses along cofibrations.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Chapter 5, for
  cofibrations and the homotopy invariance of their colimits.
-/

public section

noncomputable section

open CategoryTheory Limits ContinuousMap unitInterval Topology Set

universe u

namespace CategoryTheory.Limits.IsColimit

open TauCeti

variable {X Z : ℕ ⥤ TopCat.{u}}

/-- **Gluing homotopies on a colimit of a tower.** Let `φ ψ : X ⟶ Z` be maps of sequences of
spaces, and let `H n` be homotopies from `φ.app n` to `ψ.app n` which are compatible with the
bonding maps. Then for a colimit cocone `cX` of `X` and any cocone `cZ` of `Z`, the induced maps
`cX.pt → cZ.pt` are homotopic. -/
theorem homotopic_map {cX : Cocone X} (hcX : IsColimit cX) (cZ : Cocone Z) {φ ψ : X ⟶ Z}
    (H : ∀ n, (φ.app n).hom.Homotopy (ψ.app n).hom)
    (hH : ∀ n (t : I) (x : X.obj n),
      H (n + 1) (t, X.map (homOfLE n.le_succ) x) = Z.map (homOfLE n.le_succ) (H n (t, x))) :
    (hcX.map cZ φ).hom.Homotopic (hcX.map cZ ψ).hom := by
  -- The stagewise homotopies, read as maps into the path space `C(I, cZ.pt)`, form a cocone.
  let ι (n : ℕ) : X.obj n ⟶ TopCat.of C(I, cZ.pt) :=
    TopCat.ofHom (((cZ.ι.app n).hom.comp (H n).toContinuousMap).comp prodSwap).curry
  have hι (n : ℕ) (x : X.obj n) (t : I) : (ι n).hom x t = cZ.ι.app n (H n (t, x)) := rfl
  let c : Cocone X :=
    { pt := TopCat.of C(I, cZ.pt)
      ι := NatTrans.ofSequence (G := (Functor.const ℕ).obj (TopCat.of C(I, cZ.pt))) ι
        fun n => by
          ext x
          refine ContinuousMap.ext fun t => ?_
          exact (congrArg (cZ.ι.app (n + 1)) (hH n t x)).trans
            (ConcreteCategory.congr_hom (cZ.w (homOfLE n.le_succ)) (H n (t, x))) }
  let D := hcX.desc c
  have hD (n : ℕ) (x : X.obj n) (t : I) : D (cX.ι.app n x) t = cZ.ι.app n (H n (t, x)) := by
    rw [← ConcreteCategory.comp_apply, hcX.fac c n]
    exact hι n x t
  have hmap (α : X ⟶ Z) (n : ℕ) (x : X.obj n) :
      hcX.map cZ α (cX.ι.app n x) = cZ.ι.app n (α.app n x) := by
    rw [← ConcreteCategory.comp_apply, hcX.ι_map, ConcreteCategory.comp_apply]
  refine ⟨{ toContinuousMap := D.hom.uncurry.comp prodSwap
            map_zero_left := fun x => ?_
            map_one_left := fun x => ?_ }⟩ <;>
  obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep X hcX x <;>
  simp [hD, hmap]

/-- **Left homotopy inverses on a colimit of a tower.** Let `φ : X ⟶ Z` and `ψ : Z ⟶ X` be maps of
sequences of spaces, and let `H n : ψ.app n ∘ φ.app n ≃ id` be homotopies which are compatible
with the bonding maps. Then for colimit cocones `cX` of `X` and `cZ` of `Z`, the map induced by
`ψ` is a left homotopy inverse of the map induced by `φ`. -/
theorem map_comp_map_homotopic_id {cX : Cocone X} (hcX : IsColimit cX) {cZ : Cocone Z}
    (hcZ : IsColimit cZ) {φ : X ⟶ Z} {ψ : Z ⟶ X}
    (H : ∀ n, ((ψ.app n).hom.comp (φ.app n).hom).Homotopy (ContinuousMap.id (X.obj n)))
    (hH : ∀ n (t : I) (x : X.obj n),
      H (n + 1) (t, X.map (homOfLE n.le_succ) x) = X.map (homOfLE n.le_succ) (H n (t, x))) :
    ((hcZ.map cX ψ).hom.comp (hcX.map cZ φ).hom).Homotopic (ContinuousMap.id cX.pt) := by
  -- The components of `φ ≫ ψ` and `𝟙 X` are by definition the composites and identities that
  -- the homotopies `H n` connect.
  have h := hcX.homotopic_map cX (φ := φ ≫ ψ) (ψ := 𝟙 X) H hH
  rwa [show hcX.map cX (φ ≫ ψ) = hcX.map cZ φ ≫ hcZ.map cX ψ from hcX.hom_ext fun n => by simp,
    show hcX.map cX (𝟙 X) = 𝟙 cX.pt from hcX.hom_ext fun n => by simp] at h

end CategoryTheory.Limits.IsColimit

namespace TauCeti

variable {X Y : ℕ ⥤ TopCat.{u}}

/-- **Compatible left homotopy inverses of a map of towers.** Let `X` and `Y` be sequences of
spaces whose bonding maps are embeddings with images having the homotopy extension property, and
let `f : X ⟶ Y` be a homotopy equivalence at every stage. Then there is a map of sequences
`g : Y ⟶ X` with homotopies `H n : g.app n ∘ f.app n ≃ id` which are compatible with the bonding
maps. -/
theorem exists_natTrans_homotopy_comp_id
    (hX : ∀ n : ℕ, IsEmbedding (X.map (homOfLE n.le_succ)))
    (hXh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (X.map (homOfLE n.le_succ))))
    (hY : ∀ n : ℕ, IsEmbedding (Y.map (homOfLE n.le_succ)))
    (hYh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (Y.map (homOfLE n.le_succ))))
    (f : X ⟶ Y) (hf : ∀ n, ∃ e : X.obj n ≃ₕ Y.obj n, e.toFun = (f.app n).hom) :
    ∃ (g : Y ⟶ X) (H : ∀ n,
        ((g.app n).hom.comp (f.app n).hom).Homotopy (ContinuousMap.id (X.obj n))),
      ∀ n (t : I) (x : X.obj n),
        H (n + 1) (t, X.map (homOfLE n.le_succ) x) = X.map (homOfLE n.le_succ) (H n (t, x)) := by
  choose e he using hf
  -- A left homotopy inverse of `f` at stage `n`, with its homotopy.
  let S (n : ℕ) := Σ g : C(Y.obj n, X.obj n),
    (g.comp (f.app n).hom).Homotopy (ContinuousMap.id (X.obj n))
  have step (n : ℕ) (s : S n) : ∃ s' : S (n + 1),
      (∀ y, s'.1 (Y.map (homOfLE n.le_succ) y) = X.map (homOfLE n.le_succ) (s.1 y)) ∧
      ∀ (t : I) (x : X.obj n),
        s'.2 (t, X.map (homOfLE n.le_succ) x) = X.map (homOfLE n.le_succ) (s.2 (t, x)) := by
    obtain ⟨g, H, hg, hH, -⟩ :=
      HasHomotopyExtensionProperty.exists_inverse_extending_homotopy_of_isEmbedding
        (i := (X.map (homOfLE n.le_succ)).hom) (j := (Y.map (homOfLE n.le_succ)).hom)
        (hX n) (hY n) (hXh n) (hYh n) (e n) (e (n + 1))
        (fun x => by
          rw [← ContinuousMap.toFun_eq_coe, he, he]
          exact (ConcreteCategory.congr_hom (f.naturality (homOfLE n.le_succ)) x).symm)
        s.1 (s.2.cast (by rw [he]) rfl)
    exact ⟨⟨g, H.cast (by rw [he]) rfl⟩, hg, hH⟩
  choose next hnext using step
  let s : ∀ n, S n := fun n => Nat.rec ⟨(e 0).invFun, (e 0).left_inv.some.cast (by rw [he]) rfl⟩
    next n
  -- The defining equation of `Nat.rec` at a successor.
  have hs (n : ℕ) : s (n + 1) = next n (s n) := rfl
  -- The components of `NatTrans.ofSequence` are by definition the maps `(s n).1`
  -- (see `NatTrans.ofSequence_app`), so `(s n).2` are homotopies of the required type. The
  -- compatibility of these homotopies is `(hnext n (s n)).2`, using `hs` by `rfl`: the homotopy
  -- types depend on `s (n + 1)`, so it cannot be rewritten.
  refine ⟨NatTrans.ofSequence (fun n => TopCat.ofHom (s n).1) fun n => ?_,
    fun n => (s n).2, fun n => (hnext n (s n)).2⟩
  ext y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hs]
  exact (hnext n (s n)).1 y

/-- **Homotopy invariance of colimits of towers of cofibrations.** Let `X` and `Y` be sequences of
spaces whose bonding maps are embeddings with images having the homotopy extension property, and
let `f : X ⟶ Y` be a homotopy equivalence at every stage. Then the map induced by `f` from a
colimit of `X` to a colimit of `Y` is a homotopy equivalence. Its homotopy inverse is induced by
a left homotopy inverse `g : Y ⟶ X` of `f` chosen by `TauCeti.exists_natTrans_homotopy_comp_id`. -/
def cofibrationTowerHomotopyEquiv
    (hX : ∀ n : ℕ, IsEmbedding (X.map (homOfLE n.le_succ)))
    (hXh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (X.map (homOfLE n.le_succ))))
    (hY : ∀ n : ℕ, IsEmbedding (Y.map (homOfLE n.le_succ)))
    (hYh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (Y.map (homOfLE n.le_succ))))
    (f : X ⟶ Y) (hf : ∀ n, ∃ e : X.obj n ≃ₕ Y.obj n, e.toFun = (f.app n).hom)
    {cX : Cocone X} (hcX : IsColimit cX) {cY : Cocone Y} (hcY : IsColimit cY) :
    cX.pt ≃ₕ cY.pt :=
  have hg := exists_natTrans_homotopy_comp_id hX hXh hY hYh f hf
  { toFun := (hcX.map cY f).hom
    invFun := (hcY.map cX hg.choose).hom
    left_inv := by
      obtain ⟨H, hH⟩ := hg.choose_spec
      exact hcX.map_comp_map_homotopic_id hcY H hH
    right_inv := by
      -- `g` is a levelwise homotopy equivalence, so it has a left homotopy inverse `k` too.
      obtain ⟨H, hH⟩ := hg.choose_spec
      have hg' (n : ℕ) : ∃ e : Y.obj n ≃ₕ X.obj n, e.toFun = (hg.choose.app n).hom := by
        obtain ⟨e, he⟩ := hf n
        have := e.toFun_comp_homotopic_id_of_comp_toFun_homotopic_id
          (g := (hg.choose.app n).hom) (by rw [he]; exact ⟨H n⟩)
        rw [he] at this
        exact ⟨⟨(hg.choose.app n).hom, (f.app n).hom, this, ⟨H n⟩⟩, rfl⟩
      obtain ⟨k, K, hK⟩ := exists_natTrans_homotopy_comp_id hY hYh hX hXh hg.choose hg'
      exact (hcX.map_comp_map_homotopic_id hcY H hH).comp_homotopic_id_of_comp_homotopic_id
        (hcY.map_comp_map_homotopic_id hcX K hK) }

/-- The homotopy equivalence of colimits of towers of cofibrations induced by `f` is the map
induced by `f`. -/
@[simp]
theorem cofibrationTowerHomotopyEquiv_toFun
    (hX : ∀ n : ℕ, IsEmbedding (X.map (homOfLE n.le_succ)))
    (hXh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (X.map (homOfLE n.le_succ))))
    (hY : ∀ n : ℕ, IsEmbedding (Y.map (homOfLE n.le_succ)))
    (hYh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (Y.map (homOfLE n.le_succ))))
    (f : X ⟶ Y) (hf : ∀ n, ∃ e : X.obj n ≃ₕ Y.obj n, e.toFun = (f.app n).hom)
    {cX : Cocone X} (hcX : IsColimit cX) {cY : Cocone Y} (hcY : IsColimit cY) :
    (cofibrationTowerHomotopyEquiv hX hXh hY hYh f hf hcX hcY).toFun = (hcX.map cY f).hom :=
  (rfl)

end TauCeti
