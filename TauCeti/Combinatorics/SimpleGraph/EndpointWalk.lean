/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.WalkFrom
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
/-! # Walks of fixed length with prescribed start and endpoint

`SimpleGraph.EndpointWalk G v₀ m v` records an `m`-step walk in `G` from `v₀` to `v`. On locally
finite `G`, `walkEndpoints G v₀ m` is the `Finset` of `m`-step endpoints, `EndpointWalk.succEquiv`
decomposes `(m + 1)`-step walks along `neighborSet v`, and `forall_eq_or_exists_endpointWalk` gives
the step-back dichotomy under an injective unit-step height function. -/
public section
open Function
namespace SimpleGraph
variable {V : Type*}
/-- An `m`-step walk in `G` from `v₀` to `v`, recorded as a sequence of `m + 1` vertices. -/
structure EndpointWalk (G : SimpleGraph V) (v₀ : V) (m : ℕ) (v : V) where
  /-- The sequence of `m + 1` vertices visited along the walk. -/
  toFun : Fin (m + 1) → V
  isWalkFrom : G.IsWalkFrom v₀ toFun
  apply_last : toFun (Fin.last m) = v
namespace EndpointWalk
variable {G : SimpleGraph V} {v₀ u v : V} {m : ℕ}
instance : DFunLike (G.EndpointWalk v₀ m v) (Fin (m + 1)) (fun _ ↦ V) where
  coe w := w.toFun
  coe_injective w₁ w₂ h := by cases w₁; cases w₂; congr
@[ext] theorem ext {w₁ w₂ : G.EndpointWalk v₀ m v} (h : ∀ i, w₁ i = w₂ i) : w₁ = w₂ :=
  DFunLike.ext w₁ w₂ h
@[simp] theorem coe_mk (s : Fin (m + 1) → V) (hs : G.IsWalkFrom v₀ s) (hl : s (Fin.last m) = v) :
    ⇑(⟨s, hs, hl⟩ : G.EndpointWalk v₀ m v) = s := (rfl)
@[simp] theorem mk_apply (s : Fin (m + 1) → V) (hs : G.IsWalkFrom v₀ s) (hl : s (Fin.last m) = v)
    (i : Fin (m + 1)) : (⟨s, hs, hl⟩ : G.EndpointWalk v₀ m v) i = s i := (rfl)
@[simp] theorem apply_zero (w : G.EndpointWalk v₀ m v) : w 0 = v₀ := w.isWalkFrom.apply_zero
@[simp] theorem apply_last_eq (w : G.EndpointWalk v₀ m v) : w (Fin.last m) = v := w.apply_last
theorem adj (w : G.EndpointWalk v₀ m v) {a b : Fin (m + 1)} (hab : a.val + 1 = b.val) :
    G.Adj (w a) (w b) := w.isWalkFrom.adj hab
instance [DecidableEq V] : DecidableEq (G.EndpointWalk v₀ m v) := DFunLike.coe_injective.decidableEq
/-- The trivial `0`-step walk from `v₀` to `v₀`. -/
def zero (G : SimpleGraph V) (v₀ : V) : G.EndpointWalk v₀ 0 v₀ :=
  ⟨fun _ ↦ v₀, (isWalkFrom_zero _).2 rfl, rfl⟩
@[simp] theorem zero_apply (i : Fin 1) : zero G v₀ i = v₀ := (rfl)
theorem eq_of_zero (w : G.EndpointWalk v₀ 0 v) : v₀ = v := by
  have hl := w.apply_last_eq; rwa [Fin.last_zero, w.apply_zero] at hl
instance : Unique (G.EndpointWalk v₀ 0 v₀) where
  default := zero G v₀
  uniq w := ext fun i ↦ by rw [Fin.fin_one_eq_zero i, w.apply_zero, zero_apply]
theorem isEmpty_zero_of_ne (h : v₀ ≠ v) : IsEmpty (G.EndpointWalk v₀ 0 v) :=
  ⟨fun w ↦ h w.eq_of_zero⟩
/-- Reindex the endpoint of an `EndpointWalk` along an equality of vertices. -/
def cast (h : u = v) (w : G.EndpointWalk v₀ m u) : G.EndpointWalk v₀ m v :=
  ⟨w, w.isWalkFrom, w.apply_last_eq.trans h⟩
@[simp] theorem coe_cast (h : u = v) (w : G.EndpointWalk v₀ m u) : ⇑(w.cast h) = ⇑w := (rfl)
@[simp] theorem cast_rfl (w : G.EndpointWalk v₀ m v) : w.cast rfl = w := (rfl)
/-- Extend an `m`-step walk ending at `u` by an adjacent vertex `v`. -/
def snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) : G.EndpointWalk v₀ (m + 1) v :=
  ⟨Fin.snoc (⇑w) v, (isWalkFrom_snoc _ _).2 ⟨w.isWalkFrom, w.apply_last_eq.symm ▸ h⟩,
    Fin.snoc_last (α := fun _ ↦ V) v ⇑w⟩
@[simp] theorem coe_snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    ⇑(w.snoc h) = (Fin.snoc (⇑w) v : Fin (m + 2) → V) := (rfl)
@[simp] theorem snoc_castSucc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) (i : Fin (m + 1)) :
    w.snoc h i.castSucc = w i := Fin.snoc_castSucc (α := fun _ ↦ V) v ⇑w i
/-- Drop the last step of an `(m + 1)`-step walk. -/
def init (w : G.EndpointWalk v₀ (m + 1) v) : G.EndpointWalk v₀ m (w (Fin.last m).castSucc) :=
  ⟨Fin.init w, ((isWalkFrom_iff_init w).1 w.isWalkFrom).1, rfl⟩
@[simp] theorem coe_init (w : G.EndpointWalk v₀ (m + 1) v) : ⇑w.init = Fin.init (⇑w) := (rfl)
@[simp] theorem init_apply (w : G.EndpointWalk v₀ (m + 1) v) (i : Fin (m + 1)) :
    w.init i = w i.castSucc := (rfl)
theorem adj_init_last (w : G.EndpointWalk v₀ (m + 1) v) : G.Adj (w (Fin.last m).castSucc) v := by
  have h := ((isWalkFrom_iff_init w).1 w.isWalkFrom).2; rwa [Fin.init, w.apply_last_eq] at h
@[simp] theorem snoc_init (w : G.EndpointWalk v₀ (m + 1) v) : w.init.snoc w.adj_init_last = w :=
  ext fun i ↦ by simpa [w.apply_last_eq] using congrFun (Fin.snoc_init_self ⇑w) i
/-- Update an interior position `b` whose neighbours `a, c` carry the same vertex. -/
def update (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V} (hx : G.Adj (w a) x) :
    G.EndpointWalk v₀ m v :=
  ⟨Function.update (⇑w) b x, w.isWalkFrom.update hab hbc hac hx, by
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp; omega))]; exact w.apply_last_eq⟩
@[simp] theorem coe_update (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V}
    (hx : G.Adj (w a) x) : ⇑(w.update hab hbc hac hx) = Function.update (⇑w) b x := (rfl)
private theorem sigma_heq_of_coe_eq {u₁ u₂ : G.neighborSet v} (hu : u₁.1 = u₂.1)
    {q : G.EndpointWalk v₀ m u₁.1} {p : G.EndpointWalk v₀ m u₂.1} (hqp : ∀ i, q i = p i) :
    (⟨u₁, q⟩ : Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.1) = ⟨u₂, p⟩ := by
  rcases u₁ with ⟨u₁, h₁⟩; rcases u₂ with ⟨u₂, h₂⟩; dsimp only at hu; subst hu
  exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (ext hqp))
/-- Decompose an `(m + 1)`-step walk ending at `v` along its penultimate neighbour `u` of `v`. -/
def succEquiv (G : SimpleGraph V) (v₀ : V) (m : ℕ) (v : V) :
    G.EndpointWalk v₀ (m + 1) v ≃ Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.1 where
  toFun w := ⟨⟨w (Fin.last m).castSucc, (G.mem_neighborSet _ _).2 w.adj_init_last.symm⟩, w.init⟩
  invFun p := p.2.snoc ((G.mem_neighborSet _ _).1 p.1.2).symm
  left_inv w := w.snoc_init
  right_inv := fun ⟨_, p⟩ ↦ sigma_heq_of_coe_eq (by simp) fun _ ↦ by simp
@[simp] theorem succEquiv_symm_apply (p : Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.1) :
    (succEquiv G v₀ m v).symm p = p.2.snoc ((G.mem_neighborSet _ _).1 p.1.2).symm := (rfl)
@[simp] theorem succEquiv_snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    succEquiv G v₀ m v (w.snoc h) = ⟨⟨u, (G.mem_neighborSet v u).2 h.symm⟩, w⟩ :=
  (succEquiv G v₀ m v).eq_symm_apply.1 rfl
instance instFintype [DecidableEq V] [LocallyFinite G] :
    ∀ {m : ℕ} {v : V}, Fintype (G.EndpointWalk v₀ m v)
  | 0, v => if h : v₀ = v then h ▸ inferInstance else @Fintype.ofIsEmpty _ (isEmpty_zero_of_ne h)
  | m + 1, v =>
    haveI : ∀ u : G.neighborSet v, Fintype (G.EndpointWalk v₀ m u.1) := fun _ ↦ instFintype
    Fintype.ofEquiv _ (succEquiv G v₀ m v).symm
section Height
variable {f : V → ℕ}
theorem apply_le (hf₀ : f v₀ = 0) (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) (i : Fin (m + 1)) : f (w i) ≤ i.val := by
  obtain ⟨k, hk⟩ := i; induction k with
  | zero => exact (congrArg f (w.apply_zero : w ⟨0, hk⟩ = v₀)).trans_le (by omega)
  | succ k ih =>
    have := hadj (w.adj (a := ⟨k, by omega⟩) (b := ⟨k + 1, hk⟩) rfl)
    have := ih (by omega); dsimp only at *; omega
private theorem last_le_apply_add (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) (i : Fin (m + 1)) : f v ≤ f (w i) + (m - i.val) := by
  obtain ⟨k, hk⟩ := i; induction hrem : m - k generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    simp [show (⟨k, hk⟩ : Fin (k + 1)) = Fin.last k from rfl, w.apply_last_eq]
  | succ d ih =>
    have := hadj (w.adj (a := ⟨k, hk⟩) (b := ⟨k + 1, by omega⟩) rfl)
    have := ih (k + 1) (by omega) (by omega); omega
theorem apply_eq_val_of_last_eq (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) (hv : f v = m) (i : Fin (m + 1)) : f (w i) = i.val := by
  have := w.apply_le hf₀ hadj i; have := w.last_le_apply_add hadj i; omega
theorem subsingleton_of_last_eq (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) (hv : f v = m) :
    Subsingleton (G.EndpointWalk v₀ m v) :=
  ⟨fun w₁ w₂ ↦ ext fun i ↦ hf <| (w₁.apply_eq_val_of_last_eq hf₀ hadj hv i).trans
    (w₂.apply_eq_val_of_last_eq hf₀ hadj hv i).symm⟩
instance subsingleton_one : Subsingleton (G.EndpointWalk v₀ 1 v) :=
  ⟨fun w₁ w₂ ↦ ext fun i ↦ by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact w₁.apply_zero.trans w₂.apply_zero.symm
    · rw [Fin.fin_one_eq_zero j]; exact w₁.apply_last_eq.trans w₂.apply_last_eq.symm⟩
theorem forall_eq_or_exists_endpointWalk (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    {m : ℕ} {v : V} (w : G.EndpointWalk v₀ (m + 2) v) :
    (∀ i : Fin (m + 3), f (w i) = i.val) ∨ Nonempty (G.EndpointWalk v₀ m v) := by
  induction m generalizing v with
  | zero =>
    have h01 := hadj (w.adj (a := 0) (b := 1) rfl); have h12 := hadj (w.adj (a := 1) (b := 2) rfl)
    rw [w.apply_zero, hf₀] at h01
    rw [show f (w 1) = 1 by omega, show w 2 = v from w.apply_last_eq] at h12
    rcases h12 with hv2 | hv0
    · exact Or.inl (w.apply_eq_val_of_last_eq hf₀ hadj hv2.symm)
    · obtain rfl : v = v₀ := hf (by omega); exact Or.inr ⟨zero G v⟩
  | succ m ih =>
    rcases ih w.init with hfwd | hp
    · have hadj_last := hadj w.adj_init_last
      rw [show f (w (Fin.last (m + 2)).castSucc) = m + 2 by simpa using hfwd (Fin.last (m + 2))]
        at hadj_last
      rcases hadj_last with hup | hdown
      · exact Or.inl (w.apply_eq_val_of_last_eq hf₀ hadj hup.symm)
      · have hvisit : w.init (Fin.last (m + 1)).castSucc = v := hf <| by
          have : f (w.init (Fin.last (m + 1)).castSucc) = m + 1 := by
            simpa using hfwd (Fin.last (m + 1)).castSucc
          omega
        exact Or.inr (hvisit ▸ ⟨w.init.init⟩)
    · exact let ⟨p⟩ := hp; Or.inr ⟨p.snoc w.adj_init_last⟩
end Height
end EndpointWalk
@[simp] theorem card_endpointWalk_zero (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ v : V) : Fintype.card (G.EndpointWalk v₀ 0 v) = if v₀ = v then 1 else 0 := by
  split_ifs with h; · subst h; exact Fintype.card_unique
  have := EndpointWalk.isEmpty_zero_of_ne (G := G) h; exact Fintype.card_eq_zero
theorem sum_endpointWalk_succ (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) (m : ℕ) (v : V) {M : Type*} [AddCommMonoid M] (F : G.EndpointWalk v₀ (m + 1) v → M) :
    ∑ w : G.EndpointWalk v₀ (m + 1) v, F w =
      ∑ u ∈ (G.neighborFinset v).attach, ∑ p : G.EndpointWalk v₀ m u.1,
        F (p.snoc ((G.mem_neighborFinset v u.1).1 u.2).symm) := by
  rw [← (EndpointWalk.succEquiv G v₀ m v).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_bij (fun u _ ↦ ⟨u.1, (G.mem_neighborFinset v u.1).2 u.2⟩)
    (fun _ _ ↦ Finset.mem_attach _ _) (fun _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
    (fun u _ ↦ ⟨⟨u.1, (G.mem_neighborFinset v u.1).1 u.2⟩, Finset.mem_univ _, rfl⟩) (fun _ _ ↦ rfl)
theorem card_endpointWalk_succ (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) (m : ℕ) (v : V) : Fintype.card (G.EndpointWalk v₀ (m + 1) v) =
      ∑ u ∈ G.neighborFinset v, Fintype.card (G.EndpointWalk v₀ m u) := by
  simp_rw [Fintype.card_eq_sum_ones, G.sum_endpointWalk_succ v₀ m v]
  exact (G.neighborFinset v).sum_attach fun u ↦ ∑ _ : G.EndpointWalk v₀ m u, 1
/-- The finite set of vertices reachable from `v₀` by an `m`-step walk in a locally finite graph. -/
def walkEndpoints (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V) : ℕ → Finset V
  | 0 => {v₀}
  | m + 1 => (G.walkEndpoints v₀ m).biUnion fun u ↦ G.neighborFinset u
@[simp] theorem walkEndpoints_zero (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V) :
    G.walkEndpoints v₀ 0 = {v₀} := (rfl)
theorem walkEndpoints_succ (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V) (m : ℕ) :
    G.walkEndpoints v₀ (m + 1) = (G.walkEndpoints v₀ m).biUnion fun u ↦ G.neighborFinset u := (rfl)
@[simp] theorem mem_walkEndpoints_iff (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
    {m : ℕ} {v : V} : v ∈ G.walkEndpoints v₀ m ↔ Nonempty (G.EndpointWalk v₀ m v) := by
  induction m generalizing v with
  | zero =>
    simp only [walkEndpoints_zero, Finset.mem_singleton]
    exact ⟨fun h ↦ h ▸ ⟨EndpointWalk.zero G _⟩, fun ⟨w⟩ ↦ w.eq_of_zero.symm⟩
  | succ m ih =>
    simp only [walkEndpoints_succ, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨fun ⟨u, hu, huv⟩ ↦ let ⟨p⟩ := ih.1 hu; ⟨p.snoc huv⟩,
      fun ⟨w⟩ ↦ ⟨w (Fin.last m).castSucc, ih.2 ⟨w.init⟩, w.adj_init_last⟩⟩
instance instNonemptyEndpointWalk (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) (m : ℕ) (u : G.walkEndpoints v₀ m) : Nonempty (G.EndpointWalk v₀ m u.1) :=
  (G.mem_walkEndpoints_iff v₀).1 u.2
theorem sum_walkEndpoints_succ (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
    (m : ℕ) {M : Type*} [AddCommMonoid M] (g : V → V → M)
    (hg : ∀ v u, u ∉ G.walkEndpoints v₀ m → g v u = 0) :
    ∑ v ∈ G.walkEndpoints v₀ (m + 1), ∑ u ∈ G.neighborFinset v, g v u =
      ∑ u ∈ G.walkEndpoints v₀ m, ∑ v ∈ G.neighborFinset u, g v u := by
  have hrestrict (v : V) : ∑ u ∈ G.neighborFinset v, g v u =
      ∑ u ∈ G.neighborFinset v ∩ G.walkEndpoints v₀ m, g v u :=
    (Finset.sum_subset Finset.inter_subset_left fun u hu hnu ↦
      hg v u fun hm ↦ hnu (Finset.mem_inter.2 ⟨hu, hm⟩)).symm
  simp_rw [hrestrict]; rw [Finset.sum_sigma',
    Finset.sum_sigma' (G.walkEndpoints v₀ m) (fun u ↦ G.neighborFinset u) (fun u v ↦ g v u)]
  refine Finset.sum_bij (fun p _ ↦ ⟨p.2, p.1⟩) (fun p hp ↦ ?_) (fun _ _ _ _ h ↦ ?_)
    (fun q hq ↦ ?_) (fun _ _ ↦ rfl)
  · rcases Finset.mem_sigma.1 hp with ⟨_, h2⟩; rcases Finset.mem_inter.1 h2 with ⟨hadj, hm⟩
    exact Finset.mem_sigma.2
      ⟨hm, (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm⟩
  · rcases Sigma.mk.inj_iff.1 h with ⟨h1, h2⟩; exact Sigma.ext (eq_of_heq h2) (heq_of_eq h1)
  · rcases Finset.mem_sigma.1 hq with ⟨hm, hadj⟩
    refine ⟨⟨q.2, q.1⟩, Finset.mem_sigma.2 ⟨?_, Finset.mem_inter.2 ⟨?_, hm⟩⟩, rfl⟩
    · rw [walkEndpoints_succ]; exact Finset.mem_biUnion.2 ⟨q.1, hm, hadj⟩
    · exact (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm
theorem card_walkEndpoints_one_le_one (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    (G.walkEndpoints v₀ 1).card ≤ 1 := by
  have h1 {u : V} (hu : u ∈ G.walkEndpoints v₀ 1) : f u = 1 := by
    obtain ⟨w⟩ := (G.mem_walkEndpoints_iff v₀).1 hu
    have h := hadj w.adj_init_last; rw [Fin.last_zero, Fin.castSucc_zero, w.apply_zero, hf₀] at h
    omega
  exact Finset.card_le_one.2 fun _ hu _ hv ↦ hf ((h1 hu).trans (h1 hv).symm)
end SimpleGraph
