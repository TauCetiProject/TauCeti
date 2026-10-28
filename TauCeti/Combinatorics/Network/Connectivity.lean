/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Network.Menger.Vertex
public import TauCeti.Data.ENat.Lattice
import Mathlib.Tactic.Linarith

/-!
# Arc connectivity and vertex strong connectivity of arrow families

Let `Q` be an arrow family on a vertex type `V`. A vertex `t` is `k`-arc-reachable from `s`,
`IsArcReachable Q k s t`, when `t` stays reachable from `s` after deleting any set of fewer than
`k` arrows; arrows are deleted as identities, so parallel arrows count separately. The family is
`k`-arc-strong, `IsArcStrong Q k`, when every vertex is `k`-arc-reachable from every vertex, and
`k`-vertex-strong, `IsVertexStrong Q k`, when it has more than `k` vertices and any two vertices
outside a set of fewer than `k` deleted vertices remain reachable from each other. The invariants
`arcConnectivity Q` and `vertexStrongConnectivity Q` are the suprema in `ℕ∞` of the thresholds at
which these predicates hold. As for undirected graphs, on at most one vertex the arc connectivity
is `⊤` and the vertex strong connectivity is `0`.

The threshold `1` for arc strength is strong connectivity in the sense of Mathlib's
`Quiver.IsStronglyConnected`; for vertex strength it additionally requires at least two vertices.
The predicates are the directed counterparts of the undirected edge and vertex connectivity
predicates. The arrow-disjoint path form of `IsArcReachable` is obtained by applying
`TauCeti.forall_reachableWithout_iff_exists_paths` from `Menger/Edge` through
`TauCeti.isArcReachable_def`.

## Main results

* `TauCeti.isVertexStrong_iff_exists_paths`: an arrow family on a finite vertex type is
  `k`-vertex-strong exactly when it has more than `k` vertices and any two distinct vertices are
  joined by `k` distinct, pairwise internally vertex-disjoint directed paths. Arrows `s → t` are
  allowed, and then contribute one-arrow paths.
* `TauCeti.IsVertexStrong.isArcStrong` and `TauCeti.vertexStrongConnectivity_le_arcConnectivity`:
  the directed Whitney inequality.
* `TauCeti.arcConnectivity_le_card_out` and `TauCeti.arcConnectivity_le_card_in`: on at least two
  vertices, arc connectivity is at most every out-degree and every in-degree.
* `TauCeti.isArcStrong_iff_le_arcConnectivity` and
  `TauCeti.isVertexStrong_iff_le_vertexStrongConnectivity`: the invariants record exactly the
  thresholds at which the predicates hold, the latter on a nonempty vertex type. On the empty type
  the vertex strong connectivity is `0` although no family on it is `0`-vertex-strong.

## Implementation notes

The Whitney inequality follows the standard argument: if fewer than `k` arrows leave a set `C`
containing `s` but not `t`, and some `u ∈ C` has no arrow to some `w ∉ C`, deleting one endpoint of
each of these arrows, other than `u` and `w`, separates `w` from `u`. Otherwise every pair in
`C × Cᶜ` is joined by a leaving arrow, which forces at least `|V| - 1` of them.

For global vertex Menger between adjacent vertices `s` and `t`, delete the arrows from `s` to `t`.
After further deleting fewer than `k - 1` vertices, some third vertex `w` survives, and the
`k`-vertex-strong family supplies walks from `s` to `w` avoiding `t` and from `w` to `t` avoiding
`s`, neither of which uses an arrow from `s` to `t`. Local vertex Menger then gives `k - 1` paths,
to which one arrow from `s` to `t` is added.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Sections 5.1 and 5.4.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v} {k l : ℕ} {s t x : V}

/-! ### Arc reachability -/

variable (Q) in
/-- The vertex `t` is `k`-arc-reachable from `s` when it stays reachable from `s` after deleting any
set of fewer than `k` arrows. -/
def IsArcReachable (k : ℕ) (s t : V) : Prop :=
  ∀ F : Finset (Σ x y, Q x y), #F < k → ReachableWithout (F : Set (Σ x y, Q x y)) s t

theorem isArcReachable_def : IsArcReachable Q k s t ↔
    ∀ F : Finset (Σ x y, Q x y), #F < k → ReachableWithout (F : Set (Σ x y, Q x y)) s t :=
  Iff.rfl

@[simp]
protected theorem IsArcReachable.zero : IsArcReachable Q 0 s t :=
  fun _ hF ↦ absurd hF (Nat.not_lt_zero _)

/-- Reachability is `1`-arc-reachability. -/
@[simp]
theorem isArcReachable_one : IsArcReachable Q 1 s t ↔ Nonempty (ArrowWalk Q s t) := by
  refine ⟨fun h ↦ by simpa using h ∅ (by simp), fun h F hF ↦ ?_⟩
  rw [Nat.lt_one_iff, card_eq_zero] at hF
  simpa [hF] using h

theorem IsArcReachable.anti (hkl : k ≤ l) (h : IsArcReachable Q l s t) : IsArcReachable Q k s t :=
  fun F hF ↦ h F (hF.trans_le hkl)

@[refl, simp]
protected theorem IsArcReachable.refl (k : ℕ) (s : V) : IsArcReachable Q k s s :=
  fun _ _ ↦ .refl _ s

@[trans]
protected theorem IsArcReachable.trans (h : IsArcReachable Q k s t)
    (h' : IsArcReachable Q k t x) : IsArcReachable Q k s x :=
  fun F hF ↦ (h F hF).trans (h' F hF)

theorem IsArcReachable.nonempty_arrowWalk (hk : k ≠ 0) (h : IsArcReachable Q k s t) :
    Nonempty (ArrowWalk Q s t) :=
  isArcReachable_one.1 (h.anti (Nat.one_le_iff_ne_zero.2 hk))

/-- If `t` is `k`-arc-reachable from `s`, then every finite set of arrows containing all arrows
that leave a vertex set `C` with `s ∈ C` and `t ∉ C` has at least `k` members. -/
theorem IsArcReachable.le_card {C : Set V} (h : IsArcReachable Q k s t) (hs : s ∈ C) (ht : t ∉ C)
    {F : Finset (Σ x y, Q x y)}
    (hF : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → w ∉ C → ⟨v, w, e⟩ ∈ F) : k ≤ #F := by
  by_contra! hlt
  exact ht ((h F hlt).mem_of_mem hs fun v w e hv he ↦
    by_contra fun hw ↦ he (mem_coe.2 (hF e hv hw)))

/-! ### Arc-strong arrow families -/

variable (Q) in
/-- An arrow family is `k`-arc-strong when every vertex is `k`-arc-reachable from every vertex. -/
def IsArcStrong (k : ℕ) : Prop :=
  ∀ s t, IsArcReachable Q k s t

theorem isArcStrong_def : IsArcStrong Q k ↔ ∀ s t, IsArcReachable Q k s t :=
  Iff.rfl

theorem IsArcStrong.isArcReachable (h : IsArcStrong Q k) (s t : V) : IsArcReachable Q k s t :=
  h s t

@[simp]
protected theorem IsArcStrong.zero : IsArcStrong Q 0 :=
  fun _ _ ↦ .zero

/-- An arrow family is `1`-arc-strong exactly when it is strongly connected. -/
@[simp]
theorem isArcStrong_one : IsArcStrong Q 1 ↔ @Quiver.IsStronglyConnected V ⟨Q⟩ :=
  forall₂_congr fun _ _ ↦ isArcReachable_one

theorem IsArcStrong.anti (hkl : k ≤ l) (h : IsArcStrong Q l) : IsArcStrong Q k :=
  fun s t ↦ (h s t).anti hkl

/-- An arrow family on at most one vertex is `k`-arc-strong for every `k`. -/
theorem IsArcStrong.of_subsingleton [Subsingleton V] : IsArcStrong Q k :=
  fun s t ↦ Subsingleton.elim s t ▸ .refl k s

/-! ### Vertex-strong arrow families -/

variable (Q) in
/-- An arrow family is `k`-vertex-strong when it has more than `k` vertices, and after deleting any
set of fewer than `k` vertices, every remaining vertex is reachable from every other. -/
def IsVertexStrong (k : ℕ) : Prop :=
  (k : ℕ∞) < ENat.card V ∧
    ∀ X : Finset V, #X < k → ∀ ⦃s⦄, s ∉ X → ∀ ⦃t⦄, t ∉ X → ReachableAvoiding Q (X : Set V) s t

theorem isVertexStrong_def : IsVertexStrong Q k ↔ (k : ℕ∞) < ENat.card V ∧
    ∀ X : Finset V, #X < k → ∀ ⦃s⦄, s ∉ X → ∀ ⦃t⦄, t ∉ X → ReachableAvoiding Q (X : Set V) s t :=
  Iff.rfl

theorem IsVertexStrong.lt_card (h : IsVertexStrong Q k) : (k : ℕ∞) < ENat.card V :=
  h.1

theorem IsVertexStrong.reachableAvoiding (h : IsVertexStrong Q k) {X : Finset V} (hX : #X < k)
    (hs : s ∉ X) (ht : t ∉ X) : ReachableAvoiding Q (X : Set V) s t :=
  h.2 X hX hs ht

/-- An arrow family is `0`-vertex-strong exactly when it has a vertex. -/
@[simp]
theorem isVertexStrong_zero : IsVertexStrong Q 0 ↔ Nonempty V := by
  simp [isVertexStrong_def, ENat.card_pos_iff_nonempty]

/-- An arrow family is `1`-vertex-strong exactly when it has two distinct vertices and is
strongly connected. -/
@[simp]
theorem isVertexStrong_one :
    IsVertexStrong Q 1 ↔ Nontrivial V ∧ @Quiver.IsStronglyConnected V ⟨Q⟩ := by
  simp [isVertexStrong_def, ENat.one_lt_card_iff_nontrivial, Quiver.isStronglyConnected_iff]

theorem IsVertexStrong.anti (hkl : k ≤ l) (h : IsVertexStrong Q l) : IsVertexStrong Q k :=
  ⟨(Nat.cast_le.2 hkl).trans_lt h.lt_card, fun _ hX _ hs _ ht ↦
    h.reachableAvoiding (hX.trans_le hkl) hs ht⟩

/-- A vertex `u ∈ C` with no arrow to some `w ∉ C` forces at least `k` arrows out of `C` in a
`k`-vertex-strong family: deleting one endpoint of each, other than `u` and `w`, would separate `w`
from `u`. -/
private theorem IsVertexStrong.le_card_of_isEmpty {C : Set V} (h : IsVertexStrong Q k) {u w : V}
    (hu : u ∈ C) (hw : w ∉ C) (huw : IsEmpty (Q u w)) {F : Finset (Σ x y, Q x y)}
    (hF : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → w ∉ C → ⟨v, w, e⟩ ∈ F) : k ≤ #F := by
  classical
  by_contra! hFk
  -- Delete the source of each arrow leaving `C`, or its target if the source is `u`.
  set X : Finset V := ({a ∈ F | a.1 ∈ C ∧ a.2.1 ∉ C}).image
    fun a ↦ if a.1 = u then a.2.1 else a.1
  have huX : u ∉ X := by
    simp only [X, mem_image, mem_filter, not_exists, not_and]
    rintro a ⟨-, ha⟩ hau
    split_ifs at hau with h1
    exacts [ha.2 (hau ▸ hu), h1 hau]
  have hwX : w ∉ X := by
    simp only [X, mem_image, mem_filter, not_exists, not_and]
    rintro ⟨a, b, e⟩ ⟨-, ha⟩ hab
    split_ifs at hab with h1
    · subst h1 hab
      exact huw.false e
    · exact hw (hab ▸ ha.1)
  have hXk : #X < k := (card_image_le.trans (card_filter_le _ _)).trans_lt hFk
  refine hw ((h.reachableAvoiding hXk huX hwX).mem_of_mem hu fun v x e hv hvX hxX ↦ ?_)
  by_contra hx
  have ha : (⟨v, x, e⟩ : Σ x y, Q x y) ∈ {a ∈ F | a.1 ∈ C ∧ a.2.1 ∉ C} :=
    mem_filter.2 ⟨hF e hv hx, hv, hx⟩
  have hmem := mem_image_of_mem (fun a ↦ if a.1 = u then a.2.1 else a.1) ha
  split_ifs at hmem
  exacts [hxX (mem_coe.2 hmem), hvX (mem_coe.2 hmem)]

/-- If every vertex of `C` has an arrow to every vertex outside `C`, then at least `|V| - 1`
arrows leave `C`, when `C` and its complement are nonempty. -/
private theorem le_card_of_forall_nonempty [Finite V] {C : Set V} (hs : s ∈ C) (ht : t ∉ C)
    (hk : (k : ℕ∞) < ENat.card V) (hC : ∀ u ∈ C, ∀ w ∉ C, Nonempty (Q u w))
    {F : Finset (Σ x y, Q x y)}
    (hF : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → w ∉ C → ⟨v, w, e⟩ ∈ F) : k ≤ #F := by
  classical
  have := Fintype.ofFinite V
  set D : Finset V := {v | v ∈ C}
  have hsub : D ×ˢ Dᶜ ⊆ ({a ∈ F | a.1 ∈ C ∧ a.2.1 ∉ C}).image fun a ↦ (a.1, a.2.1) := by
    rintro ⟨v, w⟩ hvw
    simp only [D, mem_product, mem_compl, mem_filter, mem_univ, true_and] at hvw
    obtain ⟨e⟩ := hC v hvw.1 w hvw.2
    exact mem_image.2 ⟨⟨v, w, e⟩, mem_filter.2 ⟨hF e hvw.1 hvw.2, hvw.1, hvw.2⟩, rfl⟩
  have hcard := (card_le_card hsub).trans (card_image_le.trans (card_filter_le _ _))
  rw [card_product] at hcard
  have hD : 1 ≤ #D := card_pos.2 ⟨s, by simpa [D] using hs⟩
  have hDc : 1 ≤ #Dᶜ := card_pos.2 ⟨t, by simpa [D] using ht⟩
  have hV : k < #D + #Dᶜ := by
    rw [card_add_card_compl, ← Nat.cast_lt (α := ℕ∞), ← ENat.card_eq_coe_fintype_card]
    exact hk
  nlinarith

/-- In a `k`-vertex-strong arrow family, at least `k` arrows leave every vertex set `C` containing
`s` but not `t`: every finite set of arrows containing them all has at least `k` members. -/
theorem IsVertexStrong.le_card {C : Set V} (h : IsVertexStrong Q k) (hs : s ∈ C)
    (ht : t ∉ C) {F : Finset (Σ x y, Q x y)}
    (hF : ∀ ⦃v w : V⦄ (e : Q v w), v ∈ C → w ∉ C → ⟨v, w, e⟩ ∈ F) : k ≤ #F := by
  by_cases hpair : ∃ u ∈ C, ∃ w ∉ C, IsEmpty (Q u w)
  · obtain ⟨u, hu, w, hw, huw⟩ := hpair
    exact h.le_card_of_isEmpty hu hw huw hF
  · simp only [not_exists, not_and, not_isEmpty_iff] at hpair
    classical
    let D := F.image (fun a ↦ a.1) ∪ F.image fun a ↦ a.2.1
    have hD (v : V) : v ∈ D := by
      by_cases hv : v ∈ C
      · obtain ⟨e⟩ := hpair v hv t ht
        exact mem_union_left _ (mem_image.2 ⟨⟨v, t, e⟩, hF e hv ht, rfl⟩)
      · obtain ⟨e⟩ := hpair s hs v hv
        exact mem_union_right _ (mem_image.2 ⟨⟨s, v, e⟩, hF e hs hv, rfl⟩)
    let _ : Finite V := Finite.of_surjective (fun v : {v // v ∈ D} ↦ v.1) fun v ↦
      ⟨⟨v, hD v⟩, rfl⟩
    exact le_card_of_forall_nonempty hs ht h.lt_card hpair hF

/-- **The directed Whitney inequality.** A `k`-vertex-strong arrow family is `k`-arc-strong. -/
theorem IsVertexStrong.isArcStrong (h : IsVertexStrong Q k) : IsArcStrong Q k :=
  fun s t F hF ↦ by_contra fun hst ↦
    (h.le_card (C := {v | ReachableWithout (F : Set (Σ x y, Q x y)) s v}) (.refl _ s) hst
      fun _ _ e hv hw ↦ by_contra fun he ↦ hw (hv.tail e (by simpa using he))).not_gt hF

/-- Pairwise internally disjoint walks from `s` to `t` along the arrows outside those from `s` to
`t`, pushed into `Q`, together with one arrow from `s` to `t`. -/
private theorem exists_paths_of_withoutHom {m : ℕ} (e : Q s t)
    {F : Set (Σ x y, Q x y)} (hF : ∀ e' : Q s t, ⟨s, t, e'⟩ ∈ F) (hst : s ≠ t)
    (P : Fin m → ArrowWalk (WithoutHom F) s t) (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) :
    ∃ R : Fin (m + 1) → ArrowWalk Q s t, Function.Injective R ∧ (∀ i, (R i).IsPath) ∧
      Pairwise fun i j ↦ (R i).InternallyDisjoint (R j) := by
  have hadj : IsEmpty (WithoutHom F s t) := ⟨fun e' ↦ e'.2 (hF e'.1)⟩
  let φ := WithoutHom.incl F
  let P' (i : Fin m) : ArrowWalk Q s t := @Prefunctor.mapPath V ⟨WithoutHom F⟩ V ⟨Q⟩ φ s t (P i)
  have hv (i : Fin m) : (P' i).vertices = (P i).vertices :=
    ArrowWalk.vertices_mapPath_of_obj_eq_id φ rfl (P i)
  let d : ArrowWalk Q s t := (ArrowWalk.nil s).cons e
  have hd : d.vertices = [s, t] := by simp [d, ArrowWalk.vertices, Quiver.Path.vertices_cons]
  have hdP (i : Fin m) : d.InternallyDisjoint (P' i) :=
    ArrowWalk.internallyDisjoint_def.2 fun v hv _ ↦ by simpa [hd] using hv
  have hint (i : Fin m) : ∃ v ∈ (P' i).vertices, v ≠ s ∧ v ≠ t :=
    hv i ▸ (P i).exists_mem_vertices_ne_ne hst hadj
  have hdisj' : Pairwise fun i j ↦ (P' i).InternallyDisjoint (P' j) := fun i j hij ↦
    ArrowWalk.internallyDisjoint_def.2 fun v hvi hvj ↦
      ArrowWalk.internallyDisjoint_def.1 (hdisj hij) v (hv i ▸ hvi) (hv j ▸ hvj)
  refine ⟨Fin.cons d P', Fin.cons_injective_iff.2 ⟨?_, ?_⟩, fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨v, hvi, hvs, hvt⟩ := hint i
    rw [hi, hd] at hvi
    simp_all
  · exact injective_of_pairwise_internallyDisjoint hdisj' hint
  · induction i using Fin.cases with
    | zero => simp [ArrowWalk.isPath_def, hd, hst]
    | succ i => simpa [ArrowWalk.isPath_def, hv] using (ArrowWalk.isPath_def _).1 (hP i)
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simpa using hdP j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using (hdP i).symm
      | succ j => simpa using hdisj' (fun h ↦ hij (congrArg _ h))

/-- In a `(m + 1)`-vertex-strong arrow family, after deleting the arrows from `s` to `t` and fewer
than `m` further vertices, `t` stays reachable from `s` through a remaining third vertex. -/
private theorem IsVertexStrong.reachableAvoiding_withoutHom [Finite V] {m : ℕ}
    (h : IsVertexStrong Q (m + 1)) (hst : s ≠ t) {X : Finset V} (hs : s ∉ X) (ht : t ∉ X)
    (hX : #X < m) :
    ReachableAvoiding (WithoutHom {a : Σ x y, Q x y | a.1 = s ∧ a.2.1 = t}) (X : Set V) s t := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨w, hw⟩ : ∃ w, w ∉ insert s (insert t X) := by
    by_contra! hall
    have hcard : #(insert s (insert t X)) ≤ #X + 2 :=
      (card_insert_le _ _).trans (by have := card_insert_le t X; omega)
    have huniv := card_le_card (s := univ) fun v _ ↦ hall v
    rw [card_univ] at huniv
    have := h.lt_card
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_lt] at this
    omega
  simp only [mem_insert, not_or] at hw
  obtain ⟨hws, hwt, hwX⟩ := hw
  have hsw : ReachableAvoiding Q (insert t X : Finset V) s w :=
    h.reachableAvoiding ((card_insert_le _ _).trans_lt (by omega))
      (by simp [hst, hs]) (by simp [hwt, hwX])
  have hwt' : ReachableAvoiding Q (insert s X : Finset V) w t :=
    h.reachableAvoiding ((card_insert_le _ _).trans_lt (by omega))
      (by simp [hws, hwX]) (by simp [Ne.symm hst, ht])
  exact ((hsw.withoutHom fun a ha ↦ .inr (by simp [ha.2])).mono (by simp)).trans
    ((hwt'.withoutHom fun a ha ↦ .inl (by simp [ha.1])).mono (by simp))

/-- **Menger's theorem for vertex-strong arrow families.** An arrow family on a finite vertex type
is `k`-vertex-strong exactly when it has more than `k` vertices and any two distinct vertices `s`
and `t` are joined by `k` distinct directed paths pairwise sharing no vertex other than `s` and
`t`. When there are arrows from `s` to `t`, one of these paths may be a single arrow. -/
theorem isVertexStrong_iff_exists_paths [Finite V] :
    IsVertexStrong Q k ↔ (k : ℕ∞) < ENat.card V ∧ ∀ ⦃s t : V⦄, s ≠ t →
      ∃ P : Fin k → ArrowWalk Q s t, Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨fun h ↦ ⟨h.lt_card, fun s t hst ↦ ?_⟩, fun ⟨hk, h⟩ ↦ ⟨hk, fun X hX s hs t ht ↦ ?_⟩⟩
  · rcases isEmpty_or_nonempty (Q s t) with hadj | hne
    · obtain ⟨P, hP, hdisj⟩ := (forall_reachableAvoiding_iff_exists_paths hst hadj k).1
        fun X hs ht hX ↦ h.reachableAvoiding hX hs ht
      exact ⟨P, injective_of_pairwise_internallyDisjoint hdisj
        fun i ↦ (P i).exists_mem_vertices_ne_ne hst hadj, hP, hdisj⟩
    obtain ⟨e⟩ := hne
    obtain _ | m := k
    · exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
    -- Delete the arrows from `s` to `t`, find `m` paths, and add the arrow `e`.
    set F : Set (Σ x y, Q x y) := {a | a.1 = s ∧ a.2.1 = t}
    have hadj : IsEmpty (WithoutHom F s t) := ⟨fun e' ↦ e'.2 ⟨rfl, rfl⟩⟩
    obtain ⟨P, hP, hdisj⟩ := (forall_reachableAvoiding_iff_exists_paths hst hadj m).1
      fun X hs ht hX ↦ h.reachableAvoiding_withoutHom hst hs ht hX
    exact exists_paths_of_withoutHom e (F := F) (fun _ ↦ ⟨rfl, rfl⟩) hst P hP hdisj
  · obtain rfl | hst := eq_or_ne s t
    · exact .refl hs
    obtain ⟨P, -, -, hdisj⟩ := h hst
    by_contra hreach
    simpa using (card_le_card_of_not_reachableAvoiding hdisj hs ht hreach).trans_lt hX

/-! ### Numerical invariants -/

variable (Q) in
/-- The arc connectivity of an arrow family: the supremum in `ℕ∞` of the natural thresholds `k` at
which it is `k`-arc-strong. It is `⊤` when there is at most one vertex. -/
noncomputable def arcConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : IsArcStrong Q k), (k : ℕ∞)

variable (Q) in
/-- The vertex strong connectivity of an arrow family: the supremum in `ℕ∞` of the natural
thresholds `k` at which it is `k`-vertex-strong. It is `0` when there is at most one vertex. -/
noncomputable def vertexStrongConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : IsVertexStrong Q k), (k : ℕ∞)

/-- Arc connectivity records exactly the thresholds at which the arrow family is arc-strong. -/
theorem isArcStrong_iff_le_arcConnectivity (k : ℕ) : IsArcStrong Q k ↔ k ≤ arcConnectivity Q :=
  (Antitone.natCast_le_iSup_iff (fun _ _ hkl (h : IsArcStrong Q _) ↦ h.anti hkl)
    IsArcStrong.zero).symm

/-- On a nonempty vertex type, vertex strong connectivity records exactly the thresholds at which
the arrow family is vertex-strong. -/
theorem isVertexStrong_iff_le_vertexStrongConnectivity [Nonempty V] (k : ℕ) :
    IsVertexStrong Q k ↔ k ≤ vertexStrongConnectivity Q :=
  (Antitone.natCast_le_iSup_iff (fun _ _ hkl (h : IsVertexStrong Q _) ↦ h.anti hkl)
    (isVertexStrong_zero.2 ‹_›)).symm

/-- An arrow family on at most one vertex has arc connectivity `⊤`. -/
theorem arcConnectivity_eq_top_of_subsingleton [Subsingleton V] : arcConnectivity Q = ⊤ :=
  ENat.eq_top_iff_forall_ge.2 fun _ ↦
    (isArcStrong_iff_le_arcConnectivity _).1 .of_subsingleton

/-- An arrow family on at most one vertex has vertex strong connectivity `0`. -/
theorem vertexStrongConnectivity_eq_zero_of_subsingleton [Subsingleton V] :
    vertexStrongConnectivity Q = 0 := by
  refine nonpos_iff_eq_zero.1 (iSup₂_le fun k hk ↦ ?_)
  have := hk.lt_card.trans_le ENat.card_le_one
  rw [Nat.cast_lt_one] at this
  simp [this]

/-- On a finite nonempty vertex type, the vertex strong connectivity is less than the number of
vertices; in particular it is finite. -/
theorem vertexStrongConnectivity_lt_card [Finite V] [Nonempty V] :
    vertexStrongConnectivity Q < ENat.card V := by
  have := Fintype.ofFinite V
  rw [ENat.card_eq_coe_fintype_card]
  refine (iSup₂_le fun k (hk : IsVertexStrong Q k) ↦ ?_).trans_lt
    (Nat.cast_lt.2 (Nat.sub_one_lt Fintype.card_ne_zero))
  have := hk.lt_card
  rw [ENat.card_eq_coe_fintype_card, Nat.cast_lt] at this
  exact Nat.cast_le.2 (Nat.le_sub_one_of_lt this)

/-- **The directed Whitney inequality**, numerical form: the vertex strong connectivity is at most
the arc connectivity. -/
theorem vertexStrongConnectivity_le_arcConnectivity :
    vertexStrongConnectivity Q ≤ arcConnectivity Q :=
  iSup₂_le fun k hk ↦ (isArcStrong_iff_le_arcConnectivity k).1 hk.isArcStrong

/-- On at least two vertices, the arc connectivity is at most the number of arrows leaving any
vertex, loops included. -/
theorem arcConnectivity_le_card_out [Nontrivial V] (v : V) [Fintype (Σ w, Q v w)] :
    arcConnectivity Q ≤ Fintype.card (Σ w, Q v w) := by
  obtain ⟨w, hwv⟩ := exists_ne v
  refine iSup₂_le fun k hk ↦ Nat.cast_le.2 ?_
  have := (hk.isArcReachable v w).le_card (C := {v}) rfl hwv
    (F := univ.map ⟨Sigma.mk v, sigma_mk_injective⟩) fun x y e hx _ ↦ by
      subst hx
      exact mem_map.2 ⟨⟨y, e⟩, mem_univ _, rfl⟩
  simpa using this

/-- On at least two vertices, the arc connectivity is at most the number of arrows entering any
vertex, loops included. -/
theorem arcConnectivity_le_card_in [Nontrivial V] (v : V) [Fintype (Σ w, Q w v)] :
    arcConnectivity Q ≤ Fintype.card (Σ w, Q w v) := by
  obtain ⟨w, hwv⟩ := exists_ne v
  refine iSup₂_le fun k hk ↦ Nat.cast_le.2 ?_
  have hinj : Function.Injective fun a : Σ w, Q w v ↦ (⟨a.1, v, a.2⟩ : Σ x y, Q x y) := by
    rintro ⟨a, e⟩ ⟨b, f⟩ ⟨⟩
    rfl
  have := (hk.isArcReachable w v).le_card (C := {v}ᶜ) hwv (by simp)
    (F := univ.map ⟨_, hinj⟩) fun x y e _ hy ↦ by
      rw [Set.mem_compl_iff, not_not, Set.mem_singleton_iff] at hy
      subst hy
      exact mem_map.2 ⟨⟨x, e⟩, mem_univ _, rfl⟩
  simpa using this

end TauCeti
