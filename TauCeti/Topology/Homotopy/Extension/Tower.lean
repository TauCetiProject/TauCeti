/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Topology.Category.TopCat.Limits.Homotopy
public import TauCeti.Topology.Coherent
public import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# Homotopy equivalences of towers of cofibrations

A tower of cofibrations is an increasing sequence of spaces `X 0 → X 1 → X 2 → ⋯`, each of which
has the homotopy extension property in the next. This file shows that a map of towers which is a
homotopy equivalence at every stage induces a homotopy equivalence of the unions, in two forms.
In both, the map commutes strictly with the inclusions, and no homotopy inverse of the stages is
part of the data.

* **Unions of subsets.** Let `X` be the union of subsets `A 0 ⊆ A 1 ⊆ ⋯`, carrying the topology
  coherent with the `A n`, and let `Y` be such a union of `B 0 ⊆ B 1 ⊆ ⋯`. The union of the
  skeleta of a CW complex is of this kind, and so is a manifold exhausted by the regular sublevels
  of a proper function, whose inclusions are closed cofibrations thanks to collars of the regular
  levels. If `f : X → Y` restricts, for every `n`, to a homotopy equivalence `A n ≃ₕ B n`, then
  `f` is a homotopy equivalence, with a homotopy inverse mapping each `B n` into `A n`
  (`TauCeti.exists_homotopyEquiv_of_isCoherentWith`).
* **Colimits of sequences.** Let `X, Y : ℕ ⥤ TopCat` be sequences whose bonding maps
  `X n → X (n + 1)` are embeddings with images having the homotopy extension property. If
  `f : X ⟶ Y` is a homotopy equivalence at every stage, then the induced map between any colimit
  cocones of `X` and `Y` is a homotopy equivalence (`TauCeti.cofibrationTowerHomotopyEquiv`).

The proofs have three steps.

* **Compatible left inverses.** A homotopy inverse of a stage, together with a homotopy
  `g ∘ f ≃ id`, extends to the next stage without changing either on the earlier one
  (`TauCeti.HasHomotopyExtensionProperty.exists_inverse_extending_homotopy_of_isEmbedding`).
  Inductively this gives inverses and homotopies at all stages which are compatible with the
  inclusions (`TauCeti.exists_natTrans_homotopy_comp_id` for sequences).
* **Gluing.** The compatible maps and homotopies glue to a left homotopy inverse `g` of `f` on
  the union. For unions of subsets they glue by `ContinuousMap.liftCoherent`
  (`TauCeti.exists_leftInverse_homotopy_of_isCoherentWith`): the homotopy is glued over the
  products `I × A n`, which carry the topology of `I × X` as the unit interval is locally compact
  (`Topology.IsCoherentWith.univ_prod`). For colimits they glue by
  `CategoryTheory.Limits.IsColimit.map_comp_map_homotopic_id`, for colimits of any shape.
* **Two-sided inverse.** The stages of `g` are homotopy equivalences, so `g` in turn has a left
  homotopy inverse `k`. A map with a left homotopy inverse `k` and a right homotopy inverse `f` is
  a homotopy equivalence, as `f ≃ k ∘ g ∘ f ≃ k`, so `f ∘ g ≃ id`
  (`ContinuousMap.Homotopic.comp_homotopic_id_of_comp_homotopic_id`).

## Main results

* `TauCeti.exists_leftInverse_homotopy_of_isCoherentWith`: a left homotopy inverse `g` of `f`,
  together with a homotopy `g ∘ f ≃ id`, both preserving the stages.
* `TauCeti.exists_homotopyEquiv_of_isCoherentWith`: `f` is a homotopy equivalence, with a homotopy
  inverse preserving the stages.
* `TauCeti.exists_natTrans_homotopy_comp_id`: a levelwise homotopy equivalence of sequences of
  cofibrations has a left homotopy inverse which is a map of sequences, with compatible homotopies.
* `TauCeti.cofibrationTowerHomotopyEquiv`: **a levelwise homotopy equivalence of sequences of
  cofibrations induces a homotopy equivalence of colimits**, whose underlying map is the induced
  map (`TauCeti.cofibrationTowerHomotopyEquiv_toFun`).

## References

* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Chapter 5, for
  cofibrations, homotopy equivalences of pairs and the homotopy invariance of their colimits.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19 and its proof, for the extension of inverses over a cofibration.
-/

public section

noncomputable section

open Set Topology ContinuousMap unitInterval

universe u

namespace TauCeti

section Coherent

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- One stage of the induction: a homotopy inverse `g : T → S` of a homotopy equivalence
`e : S ≃ₕ T`, with a homotopy `g ∘ e ≃ id`, extends to a homotopy inverse of a homotopy
equivalence `e' : S' ≃ₕ T'` of larger subsets agreeing with `e` on `S`, with a homotopy which is
the given one on `S`. -/
private theorem exists_stage_extension {S S' : Set X} {T T' : Set Y} (hS : S ⊆ S') (hT : T ⊆ T')
    (hSH : HasHomotopyExtensionProperty ((↑) ⁻¹' S : Set S'))
    (hTH : HasHomotopyExtensionProperty ((↑) ⁻¹' T : Set T')) {f : X → Y}
    (e : S ≃ₕ T) (he : ∀ a : S, (e a : Y) = f a) (e' : S' ≃ₕ T')
    (he' : ∀ a : S', (e' a : Y) = f a) (g : C(T, S))
    (H : (g.comp e.toFun).Homotopy (ContinuousMap.id S)) :
    ∃ (g' : C(T', S')) (H' : (g'.comp e'.toFun).Homotopy (ContinuousMap.id S')),
      (∀ b : T, (g' (Set.inclusion hT b) : X) = g b) ∧
        ∀ (t : I) (a : S), (H' (t, Set.inclusion hS a) : X) = H (t, a) := by
  obtain ⟨g', H', hg', hH', -⟩ :=
    HasHomotopyExtensionProperty.exists_inverse_extending_homotopy_of_isEmbedding
      (i := ⟨Set.inclusion hS, continuous_inclusion hS⟩)
      (j := ⟨Set.inclusion hT, continuous_inclusion hT⟩) (IsEmbedding.inclusion hS)
      (IsEmbedding.inclusion hT) (by rw [ContinuousMap.coe_mk, range_inclusion]; exact hSH)
      (by rw [ContinuousMap.coe_mk, range_inclusion]; exact hTH) e e'
      (fun a => Subtype.ext <| by simp [he, he']) g H
  exact ⟨g', H', fun b => congrArg Subtype.val (hg' b), fun t a => congrArg Subtype.val (hH' t a)⟩

variable {A : ℕ → Set X} {B : ℕ → Set Y}

/-- **Left homotopy inverses of maps of towers.** Let `X` be the union of an increasing sequence
`A n`, each with the homotopy extension property in the next, carrying the topology coherent with
it, and likewise `Y` with `B n`. If `f : X → Y` restricts to homotopy equivalences
`e n : A n ≃ₕ B n`, then there are a map `g : Y → X` carrying each `B n` into `A n` and a
homotopy `g ∘ f ≃ id` keeping each `A n` in itself. -/
theorem exists_leftInverse_homotopy_of_isCoherentWith (hA : Monotone A) (hB : Monotone B)
    (hAX : ⋃ n, A n = univ) (hBY : ⋃ n, B n = univ) (hAc : IsCoherentWith (range A))
    (hBc : IsCoherentWith (range B))
    (hAH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1))))
    (hBH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' B n : Set (B (n + 1))))
    (f : C(X, Y)) (e : ∀ n, A n ≃ₕ B n) (he : ∀ n (a : A n), (e n a : Y) = f a) :
    ∃ (g : C(Y, X)) (H : (g.comp f).Homotopy (ContinuousMap.id X)),
      (∀ n, MapsTo g (B n) (A n)) ∧ ∀ n (t : I), ∀ x ∈ A n, H (t, x) ∈ A n := by
  choose G K hG hK using fun n ↦
    exists_stage_extension (hA n.le_succ) (hB n.le_succ) (hAH n) (hBH n) (e n) (he n) (e (n + 1))
      (he (n + 1))
  -- The inverses and homotopies of all stages, built inductively.
  let P (n : ℕ) : Type u :=
    Σ g : C(B n, A n), (g.comp (e n).toFun).Homotopy (ContinuousMap.id (A n))
  let s (n : ℕ) : P n := Nat.rec (motive := P) ⟨(e 0).invFun, (e 0).left_inv.some⟩
    (fun n p ↦ ⟨G n p.1 p.2, K n p.1 p.2⟩) n
  -- They agree on the earlier stages. Inclusions of stages compose definitionally, as
  -- `Set.inclusion` only changes the membership proof.
  have hs_g {m n : ℕ} (hmn : m ≤ n) (b : B m) :
      ((s n).1 (Set.inclusion (hB hmn) b) : X) = (s m).1 b := by
    induction hmn with
    | refl => rfl
    | step _ ih => exact (hG _ (s _).1 (s _).2 _).trans ih
  have hs_H {m n : ℕ} (hmn : m ≤ n) (t : I) (a : A m) :
      ((s n).2 (t, Set.inclusion (hA hmn) a) : X) = (s m).2 (t, a) := by
    induction hmn with
    | refl => rfl
    | step _ ih => exact (hK _ (s _).1 (s _).2 t _).trans ih
  -- Glue the inverses over the cover of `Y` by the `B n`.
  let g : C(Y, X) := liftCoherent B (fun n ↦ (subtypeVal (A n)).comp (s n).1)
    (fun i j y hi hj ↦ (hs_g (le_max_left i j) ⟨y, hi⟩).symm.trans
      (hs_g (le_max_right i j) ⟨y, hj⟩)) hBc hBY
  have hg (n : ℕ) (b : B n) : g b = (s n).1 b := liftCoherent_coe b
  -- Glue the homotopies over the cover of `I × X` by the `I × A n`.
  have hIX : ⋃ n, (univ : Set I) ×ˢ A n = univ := by simp [← prod_iUnion, hAX]
  let Hs (n : ℕ) : C((univ : Set I) ×ˢ A n, X) :=
    (subtypeVal (A n)).comp <| (s n).2.toContinuousMap.comp
      ⟨fun p ↦ (p.1.1, ⟨p.1.2, p.2.2⟩), by fun_prop⟩
  let HX : C(I × X, X) := liftCoherent (fun n ↦ (univ : Set I) ×ˢ A n) Hs
    (fun i j p hi hj ↦ (hs_H (le_max_left i j) p.1 ⟨p.2, hi.2⟩).symm.trans
      (hs_H (le_max_right i j) p.1 ⟨p.2, hj.2⟩)) (hAc.univ_prod hAX) hIX
  have hHX (n : ℕ) (t : I) (a : A n) : HX (t, a) = (s n).2 (t, a) :=
    liftCoherent_coe (S := fun n ↦ (univ : Set I) ×ˢ A n) ⟨(t, a), mem_univ t, a.2⟩
  have hmem (x : X) : ∃ n, x ∈ A n := mem_iUnion.1 (hAX ▸ mem_univ x)
  refine ⟨g, ⟨HX, fun x ↦ ?_, fun x ↦ ?_⟩, fun n y hy ↦ ?_, fun n t x hx ↦ ?_⟩
  · obtain ⟨n, hx⟩ := hmem x
    simp [hHX n 0 ⟨x, hx⟩, ← he n ⟨x, hx⟩, hg n]
  · obtain ⟨n, hx⟩ := hmem x
    simp [hHX n 1 ⟨x, hx⟩]
  · simp [hg n ⟨y, hy⟩]
  · -- The glued homotopy is `HX` as a function.
    have hH := ((s n).2 (t, ⟨x, hx⟩)).2
    rw [← hHX n t ⟨x, hx⟩] at hH
    exact hH

/-- **Maps of towers of cofibrations which are homotopy equivalences on every stage are homotopy
equivalences.** Let `X` be the union of an increasing sequence `A n`, each with the homotopy
extension property in the next, carrying the topology coherent with it, and likewise `Y` with
`B n`. If `f : X → Y` restricts to homotopy equivalences `e n : A n ≃ₕ B n`, then `f` is a
homotopy equivalence, with a homotopy inverse carrying each `B n` into `A n`. -/
theorem exists_homotopyEquiv_of_isCoherentWith (hA : Monotone A) (hB : Monotone B)
    (hAX : ⋃ n, A n = univ) (hBY : ⋃ n, B n = univ) (hAc : IsCoherentWith (range A))
    (hBc : IsCoherentWith (range B))
    (hAH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1))))
    (hBH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' B n : Set (B (n + 1))))
    (f : C(X, Y)) (e : ∀ n, A n ≃ₕ B n) (he : ∀ n (a : A n), (e n a : Y) = f a) :
    ∃ h : X ≃ₕ Y, ⇑h = f ∧ ∀ n, MapsTo h.symm (B n) (A n) := by
  obtain ⟨g, H, hgB, hHA⟩ :=
    exists_leftInverse_homotopy_of_isCoherentWith hA hB hAX hBY hAc hBc hAH hBH f e he
  -- On each stage, `g` is a left homotopy inverse of `e n`, hence a homotopy equivalence.
  let e' (n : ℕ) : B n ≃ₕ A n :=
    have Hn : (ContinuousMap.comp ⟨fun b ↦ ⟨g b, hgB n b.2⟩, by fun_prop⟩ (e n).toFun).Homotopy
        (ContinuousMap.id (A n)) :=
      { toFun p := ⟨H (p.1, p.2), hHA n p.1 p.2 p.2.2⟩
        map_zero_left a := Subtype.ext <| by simp [he]
        map_one_left a := Subtype.ext <| by simp }
    { toFun := ⟨fun b ↦ ⟨g b, hgB n b.2⟩, by fun_prop⟩
      invFun := (e n).toFun
      left_inv := (e n).toFun_comp_homotopic_id_of_comp_toFun_homotopic_id ⟨Hn⟩
      right_inv := ⟨Hn⟩ }
  -- The same construction gives a left homotopy inverse `k` of `g`.
  obtain ⟨k, K, -, -⟩ :=
    exists_leftInverse_homotopy_of_isCoherentWith hB hA hBY hAX hBc hAc hBH hAH g e' fun _ _ ↦ rfl
  -- Since `f` is a right homotopy inverse of `g`, so is `k`, and `f ∘ g ≃ k ∘ g ≃ id`.
  exact ⟨⟨f, g, ⟨H⟩, Homotopic.comp_homotopic_id_of_comp_homotopic_id ⟨H⟩ ⟨K⟩⟩, rfl, hgB⟩

end Coherent

section Colimit

open CategoryTheory Limits

variable {X Y : ℕ ⥤ TopCat.{u}}

/-- **Compatible left homotopy inverses of a map of towers.** Let `X` and `Y` be sequences of
spaces whose bonding maps are embeddings with images having the homotopy extension property, and
let `f : X ⟶ Y` be a homotopy equivalence at every stage. Then there is a map of sequences
`g : Y ⟶ X` with homotopies `H n : g.app n ∘ f.app n ≃ id` which are compatible with all maps
`X.map u` of the sequence. -/
theorem exists_natTrans_homotopy_comp_id
    (hX : ∀ n : ℕ, IsEmbedding (X.map (homOfLE n.le_succ)))
    (hXh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (X.map (homOfLE n.le_succ))))
    (hY : ∀ n : ℕ, IsEmbedding (Y.map (homOfLE n.le_succ)))
    (hYh : ∀ n : ℕ, HasHomotopyExtensionProperty (range (Y.map (homOfLE n.le_succ))))
    (f : X ⟶ Y) (hf : ∀ n, ∃ e : X.obj n ≃ₕ Y.obj n, e.toFun = (f.app n).hom) :
    ∃ (g : Y ⟶ X) (H : ∀ n,
        ((g.app n).hom.comp (f.app n).hom).Homotopy (ContinuousMap.id (X.obj n))),
      ∀ ⦃i j : ℕ⦄ (u : i ⟶ j) (t : I) (x : X.obj i), H j (t, X.map u x) = X.map u (H i (t, x)) := by
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
  -- (see `NatTrans.ofSequence_app`), so `(s n).2` are homotopies of the required type.
  refine ⟨NatTrans.ofSequence (fun n => TopCat.ofHom (s n).1) fun n => ?_,
    fun n => (s n).2, fun i j u t x => ?_⟩
  · ext y
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hs]
    exact (hnext n (s n)).1 y
  -- Compatibility along `i ⟶ i + k` follows by induction on `k` from compatibility along the
  -- bonding maps, which is `(hnext n (s n)).2`, using `hs` by `rfl`: the homotopy types depend
  -- on `s (n + 1)`, so it cannot be rewritten.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom u)
  induction k generalizing x with
  | zero =>
    obtain rfl : u = 𝟙 i := Subsingleton.elim _ _
    simp
  | succ k ih =>
    obtain rfl : u = homOfLE (i.le_add_right k) ≫ homOfLE (i + k).le_succ :=
      Subsingleton.elim _ _
    rw [Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact ((hnext (i + k) (s (i + k))).2 t _).trans (congrArg _ (ih x _))

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

end Colimit

end TauCeti
