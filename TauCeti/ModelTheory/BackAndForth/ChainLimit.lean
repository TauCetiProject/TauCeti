/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Range

/-!
# Limits of back-and-forth chains

Let `M 0, M 1, …` be countably infinite structures in a relational language and let `α` be a
monotone sequence of ordinals such that consecutive structures are back-and-forth equivalent at
depth `α i + ω`. Then there is a single structure on `ℕ` that is back-and-forth equivalent to
each `M i` at depth `α i`, with no loss in the ordinal.

This is the limit step in the Harnik–Makkai construction of minimal counterexamples to
Vaught's conjecture: a branch through a tree of models whose levels approximate one another
ever more closely has a limit model approximating every model on the branch.

## Implementation notes

The limit is assembled from finite injective tuples `a k` in `M k`, of nondecreasing lengths
`n k`. Consecutive tuples are linked: the first `n k` entries of `a (k + 1)` are back-and-forth
equivalent to `a k` at depth `α k + 1`. Since `M k` and `M (k + 1)` are equivalent at
`α k + 1 + n k < α k + ω`, a link is found by `n k` forth steps from the empty tuples
(`TauCeti.BFEquiv.exists_bfEquiv_append`). Each pair
`(j, x)`, with `x` in `M j`, is scheduled at the stage after `Nat.pair j m`, where `x` is the
`m`-th element of `M j`: composing the links from `j` on gives an equivalence at depth
`α j + 1` between `a j` and an initial segment of the new tuple, and one more forth step finds a
partner of `x`, appended unless it already occurs. The positions of the tuples exhaust `ℕ`
because every `M j` is infinite. The limit structure on `ℕ` reads each relation on a list of
positions from any tuple long enough to contain them; the links preserve atomic types, so the
reading does not depend on the tuple. An induction on the depth `γ` then shows that, whenever
`γ ≤ α i`, the tuple `a i` is equivalent at depth `γ` to the first `n i` positions of the limit:
forth uses the scheduled partner, and back uses a link from `a i` to a tuple containing the
given position.

## Main results

* `TauCeti.exists_structure_bfEquiv_of_bfEquiv_chain` — the limit of a chain of countably
  infinite structures, as a structure on `ℕ`.

The form for configurations on `ℕ` is
`TauCeti.RelationalConfiguration.exists_limit_of_bfEquiv_chain`.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §2 (the limit model in the proof of the Harnik–Makkai theorem, there stated for a different
  back-and-forth hierarchy).
* Victor Harnik and Michael Makkai, *A tree argument in infinitary model theory*, Proc. Amer.
  Math. Soc. 67 (1977).
-/

public section

universe u v w o

open FirstOrder FirstOrder.Language Fin
open scoped Ordinal

namespace TauCeti

variable {L : Language.{u, v}} [L.IsRelational]

namespace ChainLimit

/-! ### The construction -/

/-- A stage of the construction: a finite tuple, stored as its length and a sequence whose first
`len` entries are the tuple. -/
private structure Stage (X : Type w) where
  len : ℕ
  pt : ℕ → X

/-- The tuple of a stage, restricted to its first `m` positions. -/
private abbrev Stage.tuple {X : Type w} (s : Stage X) (m : ℕ) : Fin m → X := s.pt ∘ Fin.val

/-- Restricting a tuple further is restriction to fewer positions. -/
private theorem Stage.tuple_comp_castLE {X : Type w} (s : Stage X) {m n : ℕ} (h : m ≤ n) :
    s.tuple n ∘ Fin.castLE h = s.tuple m :=
  funext fun _ => (rfl)

/-- Append `y` to the first `n` entries of `b`, unless it already occurs among them. -/
private noncomputable def extend {X : Type w} (n : ℕ) (b : ℕ → X) (y : X) : Stage X :=
  open Classical in
  if ∃ p < n, b p = y then ⟨n, b⟩ else ⟨n + 1, Function.update b n y⟩

private theorem extend_of_exists {X : Type w} {n : ℕ} {b : ℕ → X} {y : X}
    (h : ∃ p < n, b p = y) : extend n b y = ⟨n, b⟩ := by
  simp [extend, h]

private theorem extend_of_not_exists {X : Type w} {n : ℕ} {b : ℕ → X} {y : X}
    (h : ¬∃ p < n, b p = y) : extend n b y = ⟨n + 1, Function.update b n y⟩ := by
  simp [extend, h]

private theorem le_extend_len {X : Type w} (n : ℕ) (b : ℕ → X) (y : X) :
    n ≤ (extend n b y).len := by
  by_cases h : ∃ p < n, b p = y
  · rw [extend_of_exists h]
  · rw [extend_of_not_exists h]
    exact Nat.le_succ n

private theorem extend_pt_of_lt {X : Type w} {n p : ℕ} (b : ℕ → X) (y : X) (hp : p < n) :
    (extend n b y).pt p = b p := by
  by_cases h : ∃ p < n, b p = y
  · rw [extend_of_exists h]
  · rw [extend_of_not_exists h]
    exact Function.update_of_ne hp.ne _ _

private theorem extend_tuple_of_le {X : Type w} {n m : ℕ} (b : ℕ → X) (y : X) (hm : m ≤ n) :
    (extend n b y).tuple m = b ∘ Fin.val :=
  funext fun q => extend_pt_of_lt b y (q.isLt.trans_le hm)

private theorem exists_extend_pt_eq {X : Type w} (n : ℕ) (b : ℕ → X) (y : X) :
    ∃ p < (extend n b y).len, (extend n b y).pt p = y := by
  by_cases h : ∃ p < n, b p = y
  · rw [extend_of_exists h]
    exact h
  · rw [extend_of_not_exists h]
    exact ⟨n, Nat.lt_succ_self n, Function.update_self _ _ _⟩

private theorem injective_extend_tuple {X : Type w} {n : ℕ} {b : ℕ → X} (y : X)
    (hb : Function.Injective (b ∘ Fin.val : Fin n → X)) :
    Function.Injective ((extend n b y).tuple (extend n b y).len) := by
  by_cases h : ∃ p < n, b p = y
  · rw [extend_of_exists h]
    exact hb
  · rw [extend_of_not_exists h]
    push Not at h
    intro p q hpq
    have hp := Nat.lt_succ_iff.mp p.isLt
    have hq := Nat.lt_succ_iff.mp q.isLt
    simp only [Stage.tuple, Function.comp_apply, Function.update_apply] at hpq
    ext
    split_ifs at hpq with h₁ h₂ h₂
    · omega
    · exact absurd hpq.symm (h q (lt_of_le_of_ne hq h₂))
    · exact absurd hpq (h p (lt_of_le_of_ne hp h₁))
    · exact Fin.mk.inj (@hb ⟨p, lt_of_le_of_ne hp h₁⟩ ⟨q, lt_of_le_of_ne hq h₂⟩ hpq)

variable (L)
variable {M : ℕ → Type w} [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]

/-- A tuple in `M (k + 1)` equivalent to the tuple of `s` at depth `α k + 1`, when there is one. -/
private noncomputable def linkPt (α : ℕ → Ordinal.{o}) (k : ℕ) (s : Stage (M k)) :
    ℕ → M (k + 1) :=
  Classical.epsilon fun b : ℕ → M (k + 1) =>
    BFEquiv (L := L) (α k + 1) s.len (s.tuple s.len) (b ∘ Fin.val)

/-- A partner in `M (k + 1)` for `x`, extending the restriction of `b` to the length of `s`, at
depth `α j`, when there is one. -/
private noncomputable def matchPt (α : ℕ → Ordinal.{o}) {j : ℕ} (s : Stage (M j)) (x : M j)
    {k : ℕ} (b : ℕ → M (k + 1)) : M (k + 1) :=
  Classical.epsilon fun y : M (k + 1) =>
    BFEquiv (L := L) (α j) (s.len + 1) (snoc (s.tuple s.len) x) (snoc (b ∘ Fin.val) y)

/-- One step of the construction. The stage `s` at `k` is linked to `M (k + 1)`, and the element
of `M j` with index `(Nat.unpair k).2`, where `j = (Nat.unpair k).1`, receives a partner relative
to the stage `s'` at `j`. -/
private noncomputable def step (α : ℕ → Ordinal.{o}) (e : ∀ i, ℕ → M i) (k : ℕ) (s : Stage (M k))
    (s' : Stage (M (Nat.unpair k).1)) : Stage (M (k + 1)) :=
  extend s.len (linkPt L α k s)
    (matchPt L α s' (e _ (Nat.unpair k).2) (linkPt L α k s))

/-- The stages of the construction. -/
private noncomputable def stage (α : ℕ → Ordinal.{o}) (e : ∀ i, ℕ → M i) :
    (k : ℕ) → Stage (M k)
  | 0 => ⟨0, fun _ => Classical.arbitrary _⟩
  | k + 1 => step L α e k (stage α e k) (stage α e (Nat.unpair k).1)
termination_by k => k
decreasing_by
  all_goals first | omega | exact Nat.lt_succ_of_le (Nat.unpair_left_le k)

private theorem stage_zero_len (α : ℕ → Ordinal.{o}) (e : ∀ i, ℕ → M i) :
    (stage L α e 0).len = 0 := by
  rw [stage]

private theorem stage_succ (α : ℕ → Ordinal.{o}) (e : ∀ i, ℕ → M i) (k : ℕ) :
    stage L α e (k + 1) = step L α e k (stage L α e k) (stage L α e (Nat.unpair k).1) := by
  rw [stage]

/-- The limit structure on `ℕ`: a relation holds on a list of positions when it holds on their
entries in some tuple containing all of them. -/
@[instance_reducible]
private noncomputable def limitStructure (α : ℕ → Ordinal.{o}) (e : ∀ i, ℕ → M i) :
    L.Structure ℕ where
  funMap f := isEmptyElim f
  RelMap R p := ∃ k, (∀ q, p q < (stage L α e k).len) ∧
    Structure.RelMap R ((stage L α e k).pt ∘ p)

variable {L}
variable {α : ℕ → Ordinal.{o}} (e : ∀ i, ℕ → M i)

/-! ### The links -/

section Links

variable (hchain : ∀ i, BFEquiv (L := L) (α i + ω) 0 (Fin.elim0 : Fin 0 → M i)
  (Fin.elim0 : Fin 0 → M (i + 1)))
include hchain

private theorem linkPt_spec (k : ℕ) (s : Stage (M k)) :
    BFEquiv (L := L) (α k + 1) s.len (s.tuple s.len) (linkPt L α k s ∘ Fin.val) := by
  refine Classical.epsilon_spec (p := fun b : ℕ → M (k + 1) =>
    BFEquiv (L := L) (α k + 1) s.len (s.tuple s.len) (b ∘ Fin.val)) ?_
  have hle : α k + 1 + (s.len : Ordinal.{o}) ≤ α k + ω := by
    rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add]
    gcongr
    exact (Ordinal.natCast_lt_omega0 _).le
  obtain ⟨y, hy⟩ := ((hchain k).mono hle).exists_bfEquiv_append s.len (s.tuple s.len)
  have hy' := hy.comp (Fin.cast (Nat.zero_add s.len).symm)
  rw [elim0_append, elim0_append] at hy'
  refine ⟨fun p => if hp : p < s.len then y ⟨p, hp⟩ else Classical.arbitrary _, ?_⟩
  convert hy' using 1 <;> funext q <;> simp [q.isLt]

/-- Consecutive stages are linked at depth `α k + 1`, and the lengths do not decrease. -/
private theorem link (k : ℕ) :
    (stage L α e k).len ≤ (stage L α e (k + 1)).len ∧
      BFEquiv (L := L) (α k + 1) (stage L α e k).len ((stage L α e k).tuple _)
        ((stage L α e (k + 1)).tuple _) := by
  rw [stage_succ, step]
  refine ⟨le_extend_len _ _ _, ?_⟩
  rw [extend_tuple_of_le _ _ le_rfl]
  exact linkPt_spec hchain k _

/-- Every stage is linked to each later one at the depth of the earlier stage, plus one. -/
private theorem chain (hα : Monotone α) {j k : ℕ} (hjk : j ≤ k) :
    (stage L α e j).len ≤ (stage L α e k).len ∧
      BFEquiv (L := L) (α j + 1) (stage L α e j).len ((stage L α e j).tuple _)
        ((stage L α e k).tuple _) := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨le_rfl, BFEquiv.refl _ _⟩
  | succ k hjk ih =>
    obtain ⟨hlen, hlink⟩ := link e hchain k
    refine ⟨ih.1.trans hlen, ih.2.trans ?_⟩
    have h := (hlink.mono (add_le_add_left (hα hjk) 1)).comp (Fin.castLE ih.1)
    rwa [Stage.tuple_comp_castLE, Stage.tuple_comp_castLE] at h

/-- The tuple of every stage is injective. -/
private theorem injective_tuple (k : ℕ) :
    Function.Injective ((stage L α e k).tuple (stage L α e k).len) := by
  induction k with
  | zero =>
    intro p
    exact absurd p.isLt (by simp [stage_zero_len])
  | succ k ih =>
    rw [stage_succ, step]
    refine injective_extend_tuple _ fun p q hpq => ih ?_
    exact ((linkPt_spec hchain k _).sameAtomicType.eq_iff p q).mpr hpq

/-- The element of `M j` scheduled at stage `k + 1` has a partner in the tuple of that stage. -/
private theorem exists_partner (hα : Monotone α) {k j t : ℕ} (hk : Nat.unpair k = (j, t)) :
    ∃ p < (stage L α e (k + 1)).len,
      BFEquiv (L := L) (α j) ((stage L α e j).len + 1)
        (snoc ((stage L α e j).tuple _) (e j t))
        (snoc ((stage L α e (k + 1)).tuple _) ((stage L α e (k + 1)).pt p)) := by
  have hj : (Nat.unpair k).1 = j := congrArg Prod.fst hk
  have ht : (Nat.unpair k).2 = t := congrArg Prod.snd hk
  subst hj ht
  have hjk := Nat.unpair_left_le k
  obtain ⟨hlen, hjk'⟩ := chain e hchain hα hjk
  -- The stage at `j` is linked at depth `α j + 1` to the link tuple chosen at stage `k`.
  have hb : BFEquiv (L := L) (α (Nat.unpair k).1 + 1) (stage L α e (Nat.unpair k).1).len
      ((stage L α e (Nat.unpair k).1).tuple _) (linkPt L α k (stage L α e k) ∘ Fin.val) := by
    refine hjk'.trans ?_
    have h := ((linkPt_spec hchain k _).mono (add_le_add_left (hα hjk) 1)).comp
      (Fin.castLE hlen)
    rwa [Stage.tuple_comp_castLE] at h
  have hy := Classical.epsilon_spec (p := fun y : M (k + 1) =>
    BFEquiv (L := L) (α (Nat.unpair k).1) _
      (snoc ((stage L α e (Nat.unpair k).1).tuple _) (e _ (Nat.unpair k).2))
      (snoc (linkPt L α k (stage L α e k) ∘ Fin.val) y))
    (((BFEquiv.add_one _ _ _).mp hb).2.1 _)
  rw [stage_succ, step]
  obtain ⟨p, hp, hpy⟩ := exists_extend_pt_eq (stage L α e k).len
    (linkPt L α k (stage L α e k))
    (matchPt L α (stage L α e (Nat.unpair k).1) (e _ (Nat.unpair k).2)
      (linkPt L α k (stage L α e k)))
  refine ⟨p, hp, ?_⟩
  rw [hpy, extend_tuple_of_le _ _ hlen]
  exact hy

/-- The lengths of the stages are unbounded. -/
private theorem exists_lt_len [∀ i, Infinite (M i)] (hα : Monotone α)
    (he : ∀ i, Function.Surjective (e i)) (N : ℕ) : ∃ k, N < (stage L α e k).len := by
  -- Every stage is outgrown: a new element of `M j` gets a partner outside the tuple at `j`.
  have grow : ∀ j, ∃ k, (stage L α e j).len < (stage L α e k).len := by
    intro j
    obtain ⟨x, hx⟩ := (Set.finite_range ((stage L α e j).tuple (stage L α e j).len)).infinite_compl
      |>.nonempty
    obtain ⟨t, rfl⟩ := he j x
    obtain ⟨p, hp, hpx⟩ := exists_partner e hchain hα (Nat.unpair_pair j t)
    refine ⟨Nat.pair j t + 1, lt_of_le_of_lt (not_lt.mp fun hpj => hx ⟨⟨p, hpj⟩, ?_⟩) hp⟩
    have h := hpx.sameAtomicType.eq_iff (last _) (castSucc ⟨p, hpj⟩)
    simp only [snoc_last, snoc_castSucc] at h
    -- The entry of a tuple at position `p` is `pt p` by definition of `Stage.tuple`.
    exact (h.mpr rfl).symm
  induction N with
  | zero => simpa [stage_zero_len] using grow 0
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', hk'⟩ := grow k
    exact ⟨k', by omega⟩

end Links

/-! ### The limit structure -/

section Limit

variable (hchain : ∀ i, BFEquiv (L := L) (α i + ω) 0 (Fin.elim0 : Fin 0 → M i)
  (Fin.elim0 : Fin 0 → M (i + 1))) (hα : Monotone α)
include hchain hα

/-- A relation holds in the limit at positions inside the tuple of a stage exactly when it holds
there. -/
private theorem relMap_limit_iff {k l : ℕ} (R : L.Relations l) (p : Fin l → ℕ)
    (hp : ∀ q, p q < (stage L α e k).len) :
    @Structure.RelMap L ℕ (limitStructure L α e) l R p ↔
      Structure.RelMap R ((stage L α e k).pt ∘ p) := by
  -- Two stages containing the positions agree on them, by the atomic part of a link.
  have agree : ∀ {k k'}, k ≤ k' → (hp : ∀ q, p q < (stage L α e k).len) →
      (Structure.RelMap R ((stage L α e k).pt ∘ p) ↔
        Structure.RelMap R ((stage L α e k').pt ∘ p)) :=
    fun hkk' hp => ((chain e hchain hα hkk').2.sameAtomicType.rel_iff R
      fun q => ⟨p q, hp q⟩)
  refine ⟨fun ⟨k', hk', h⟩ => ?_, fun h => ⟨k, hp, h⟩⟩
  exact (agree (le_max_left k k') hp).mpr ((agree (le_max_right k k') hk').mp h)

/-- Matching an element of `M i` with a position of the limit, through a stage `k ≥ i` that the
position lies in. -/
private theorem bfEquiv_snoc {i k : ℕ} (hik : i ≤ k) {γ : Ordinal.{o}} (hγ : γ ≤ α i)
    (hk : @BFEquiv L _ (M _) ℕ _ (limitStructure L α e) γ (stage L α e k).len
      ((stage L α e k).tuple _) Fin.val)
    {x : M i} {p : ℕ} (hp : p < (stage L α e k).len)
    (hx : BFEquiv (L := L) (α i) ((stage L α e i).len + 1) (snoc ((stage L α e i).tuple _) x)
      (snoc ((stage L α e k).tuple _) ((stage L α e k).pt p))) :
    @BFEquiv L _ (M _) ℕ _ (limitStructure L α e) γ ((stage L α e i).len + 1)
      (snoc ((stage L α e i).tuple _) x) (snoc Fin.val p) := by
  let _ : L.Structure ℕ := limitStructure L α e
  have hlen := (chain e hchain hα hik).1
  have h := hk.comp (snoc (Fin.castLE hlen) ⟨p, hp⟩)
  rw [comp_snoc, comp_snoc, Stage.tuple_comp_castLE] at h
  -- `h` matches the goal up to unfolding `Fin.val ∘ Fin.castLE hlen` to `Fin.val` and the entry
  -- `(stage L α e k).tuple _ ⟨p, hp⟩` to `(stage L α e k).pt p`.
  exact (hx.mono hγ).trans h

/-- Whenever `γ ≤ α i`, the tuple of stage `i` is equivalent at depth `γ` to the first positions
of the limit. -/
private theorem bfEquiv_limit [∀ i, Infinite (M i)] (he : ∀ i, Function.Surjective (e i))
    (γ : Ordinal.{o}) :
    ∀ i, γ ≤ α i → @BFEquiv L _ (M _) ℕ _ (limitStructure L α e) γ (stage L α e i).len
      ((stage L α e i).tuple _) Fin.val := by
  let _ : L.Structure ℕ := limitStructure L α e
  induction γ using Ordinal.limitRecOn with
  | zero =>
    intro i _
    refine BFEquiv.zero.mpr ((sameAtomicType_iff _ _).mpr ⟨fun p q => ?_, fun R f => ?_⟩)
    · exact (injective_tuple e hchain i).eq_iff.trans Fin.val_inj.symm
    · exact (relMap_limit_iff e hchain hα R _ fun q => (f q).isLt).symm
  | add_one γ ih =>
    intro i hi
    have hγ : γ ≤ α i := (Order.le_succ γ).trans hi
    refine (BFEquiv.add_one γ _ _).mpr ⟨ih i hγ, fun x => ?_, fun p => ?_⟩
    · -- Forth: the partner of `x`, scheduled at the stage after `Nat.pair i t`.
      obtain ⟨t, rfl⟩ := he i x
      have hik : i ≤ Nat.pair i t + 1 := (Nat.left_le_pair i t).trans (Nat.le_succ _)
      obtain ⟨p, hp, hpx⟩ := exists_partner e hchain hα (Nat.unpair_pair i t)
      exact ⟨p, bfEquiv_snoc e hchain hα hik hγ (ih _ (hγ.trans (hα hik))) hp hpx⟩
    · -- Back: a stage `k ≥ i` containing the position `p`, linked to stage `i`.
      obtain ⟨k₀, hk₀⟩ := exists_lt_len e hchain hα he p
      have hik : i ≤ max i k₀ := le_max_left _ _
      have hp : p < (stage L α e (max i k₀)).len :=
        hk₀.trans_le (chain e hchain hα (le_max_right i k₀)).1
      obtain ⟨x, hx⟩ := ((BFEquiv.add_one _ _ _).mp (chain e hchain hα hik).2).2.2
        ((stage L α e (max i k₀)).pt p)
      exact ⟨x, bfEquiv_snoc e hchain hα hik hγ (ih _ (hγ.trans (hα hik))) hp hx⟩
  | limit γ hγ ih =>
    intro i hi
    exact (BFEquiv.limit hγ _ _).mpr fun β hβ => ih β hβ i (hβ.le.trans hi)

end Limit

end ChainLimit

open ChainLimit in
/-- **The limit of a back-and-forth chain.** Let `M i` be countably infinite structures and `α` a
monotone sequence of ordinals such that `M i` and `M (i + 1)` are back-and-forth equivalent at
depth `α i + ω`. Then some structure on `ℕ` is back-and-forth equivalent to every `M i` at depth
`α i`. -/
theorem exists_structure_bfEquiv_of_bfEquiv_chain {M : ℕ → Type w}
    [hM : ∀ i, L.Structure (M i)] [∀ i, Countable (M i)] [∀ i, Infinite (M i)]
    {α : ℕ → Ordinal.{o}} (hα : Monotone α)
    (h : ∀ i, BFEquiv (L := L) (α i + ω) 0 (Fin.elim0 : Fin 0 → M i)
      (Fin.elim0 : Fin 0 → M (i + 1))) :
    ∃ S : L.Structure ℕ, ∀ i,
      @BFEquiv L _ ℕ (M i) S _ (α i) 0 Fin.elim0 Fin.elim0 := by
  choose e he using fun i => exists_surjective_nat (M i)
  let _ : L.Structure ℕ := limitStructure L α e
  refine ⟨limitStructure L α e, fun i => ?_⟩
  have hi := (bfEquiv_limit e h hα he (α i) i le_rfl).comp Fin.elim0
  rw [Subsingleton.elim (_ ∘ Fin.elim0) Fin.elim0,
    Subsingleton.elim (_ ∘ Fin.elim0) Fin.elim0] at hi
  exact hi.symm

end TauCeti
