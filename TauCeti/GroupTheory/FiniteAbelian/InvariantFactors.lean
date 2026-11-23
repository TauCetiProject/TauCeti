/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Data.ZMod.ChineseRemainder
import TauCeti.Data.ZMod.Torsion
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Invariant factors of a finite abelian group

A finite abelian group `A` is isomorphic to `ZMod d₁ × ⋯ × ZMod dₖ` for exactly one list
`d₁ ∣ d₂ ∣ ⋯ ∣ dₖ` of integers `> 1`, its *invariant factors*; the list is empty exactly for the
trivial group. Mathlib's structure theorem `AddCommGroup.equiv_directSum_zmod_of_finite` gives the
decomposition into prime-power cyclic groups, which is unique only up to reordering; the
divisibility-chain form is a canonical list, and it is the form in which group databases display
a finite abelian group.

The product over a list `l` is written `(i : Fin l.length) → ZMod l[i]`, indexed by the positions
of `l`.

## Main results

* `TauCeti.AddCommGroup.existsUnique_invariantFactors`: existence and uniqueness of the
  divisibility chain.
* `TauCeti.AddCommGroup.invariantFactors`: the chain itself, characterized by
  `invariantFactors_eq_iff`.
* `TauCeti.AddCommGroup.nonempty_addEquiv_iff_invariantFactors_eq`: two finite abelian groups are
  isomorphic exactly when they have the same invariant factors.
* `TauCeti.AddCommGroup.card_torsionBy_eq_prod_map_gcd`: the number of elements killed by `m` is
  `∏ gcd m dᵢ`.
* `TauCeti.AddCommGroup.prod_invariantFactors` and `getLast_invariantFactors`: the invariant
  factors multiply to the order, and the last one is the exponent.
* `TauCeti.AddCommGroup.invariantFactors_zmod`, `invariantFactors_zmod_prod`: the invariant factors
  of `ZMod n` and of `ZMod a × ZMod b` with `a ∣ b`.

## Proof

Existence: starting from the prime-power decomposition, the cyclic factors are inserted one at a
time into a divisibility chain, merging `ZMod a × ZMod c` into `ZMod (gcd a c) × ZMod (lcm a c)`
(`ZMod.nonempty_ringEquiv_gcd_lcm`) down the chain; factors `ZMod 1` are dropped at the end.
Uniqueness: in `∏ ZMod dᵢ` exactly `∏ gcd m dᵢ` elements are killed by `m`
(`ZMod.card_torsionBy`), so isomorphic products have the same gcd profile `m ↦ ∏ gcd m dᵢ`. For a
divisibility chain, evaluating the profile at the largest entry recovers that entry, and
cancelling its factor `gcd m dₖ` leaves the profile of the rest of the chain.

## References

* D. S. Dummit and R. M. Foote, *Abstract Algebra*, third edition, Wiley (2004), §5.2, the
  Fundamental Theorem of Finitely Generated Abelian Groups in its invariant-factor form.
-/

public section

namespace TauCeti.AddCommGroup

/-- The product `∏ ZMod dᵢ` over the entries of a list `l`, indexed by the positions of `l`. -/
private abbrev ZModPi (l : List ℕ) : Type := (i : Fin l.length) → ZMod l[i]

/-- Splitting off the first factor of `ZModPi (d :: l)`. Both `(d :: l)[0]` and
`(d :: l)[i.succ]` reduce to `d` and `l[i]`, so `Fin.consLinearEquiv` applies directly. -/
private def consAddEquiv (d : ℕ) (l : List ℕ) : ZModPi (d :: l) ≃+ ZMod d × ZModPi l :=
  (Fin.consLinearEquiv ℤ fun i : Fin (l.length + 1) ↦ ZMod (d :: l)[i]).toAddEquiv.symm

/-- The empty product `ZModPi []` is trivial: `[].length` reduces to `0`, so it is indexed by
`Fin 0`. -/
private instance : Unique (ZModPi []) :=
  have : IsEmpty (Fin ([] : List ℕ).length) := inferInstanceAs (IsEmpty (Fin 0))
  Pi.uniqueOfIsEmpty _

/-- `ZModPi [n]` is `ZMod n`. -/
private def singletonAddEquiv (n : ℕ) : ZMod n ≃+ ZModPi [n] :=
  AddEquiv.prodUnique.symm.trans (consAddEquiv n []).symm

/-- Insert `a` into a divisibility chain: replace the head `c` by `gcd a c` and insert
`lcm a c` into the tail. -/
private def insertChain (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | c :: t => a.gcd c :: insertChain (a.lcm c) t

/-- A common divisor of `a` and of the entries of `t` divides every entry of `insertChain a t`. -/
private theorem dvd_of_mem_insertChain {x a : ℕ} {t : List ℕ} (ha : x ∣ a) (ht : ∀ y ∈ t, x ∣ y) :
    ∀ z ∈ insertChain a t, x ∣ z := by
  induction t generalizing a with
  | nil => simpa [insertChain]
  | cons c t ih =>
    simp only [insertChain, List.mem_cons, forall_eq_or_imp] at ht ⊢
    exact ⟨Nat.dvd_gcd ha ht.1, ih (ha.trans (Nat.dvd_lcm_left a c)) ht.2⟩

/-- Inserting into a divisibility chain gives a divisibility chain. -/
private theorem pairwise_insertChain (a : ℕ) {t : List ℕ} (ht : t.Pairwise (· ∣ ·)) :
    (insertChain a t).Pairwise (· ∣ ·) := by
  induction t generalizing a with
  | nil => simp [insertChain]
  | cons c t ih =>
    rw [List.pairwise_cons] at ht
    exact List.pairwise_cons.2 ⟨dvd_of_mem_insertChain
      ((Nat.gcd_dvd_left a c).trans (Nat.dvd_lcm_left a c))
      fun y hy ↦ (Nat.gcd_dvd_right a c).trans (ht.1 y hy), ih _ ht.2⟩

/-- Inserting a nonzero entry into a list of nonzero entries gives nonzero entries. -/
private theorem ne_zero_of_mem_insertChain {a : ℕ} {t : List ℕ} (ha : a ≠ 0)
    (ht : ∀ y ∈ t, y ≠ 0) : ∀ z ∈ insertChain a t, z ≠ 0 := by
  induction t generalizing a with
  | nil => simpa [insertChain]
  | cons c t ih =>
    simp only [insertChain, List.mem_cons, forall_eq_or_imp] at ht ⊢
    exact ⟨Nat.gcd_ne_zero_left ha, ih (Nat.lcm_ne_zero ha ht.1) ht.2⟩

/-- Inserting `a` into `t` multiplies the product of cyclic groups by `ZMod a`. -/
private theorem nonempty_addEquiv_insertChain (a : ℕ) (t : List ℕ) :
    Nonempty (ZMod a × ZModPi t ≃+ ZModPi (insertChain a t)) := by
  induction t generalizing a with
  | nil => exact ⟨(consAddEquiv a []).symm⟩
  | cons c t ih =>
    obtain ⟨e⟩ := ZMod.nonempty_ringEquiv_gcd_lcm a c
    obtain ⟨f⟩ := ih (a.lcm c)
    exact ⟨((AddEquiv.refl _).prodCongr (consAddEquiv c t)).trans <|
      AddEquiv.prodAssoc.symm.trans <| (e.toAddEquiv.prodCongr (AddEquiv.refl _)).trans <|
      AddEquiv.prodAssoc.trans <| ((AddEquiv.refl _).prodCongr f).trans
      (consAddEquiv _ _).symm⟩

/-- Factors `ZMod 1` are trivial, so they can be dropped. -/
private theorem nonempty_addEquiv_filter (l : List ℕ) :
    Nonempty (ZModPi l ≃+ ZModPi (l.filter (· ≠ 1))) := by
  induction l with
  | nil => exact ⟨AddEquiv.refl _⟩
  | cons d l ih =>
    obtain ⟨e⟩ := ih
    by_cases hd : d = 1
    · subst hd
      rw [List.filter_cons_of_neg (by simp)]
      exact ⟨(consAddEquiv 1 l).trans (AddEquiv.uniqueProd.trans e)⟩
    · rw [List.filter_cons_of_pos (by simpa)]
      exact ⟨(consAddEquiv d l).trans (((AddEquiv.refl _).prodCongr e).trans
        (consAddEquiv d _).symm)⟩

/-- A finite product of nonzero cyclic factors is a product over a divisibility chain. -/
private theorem exists_pairwise_dvd_addEquiv_pi (ι : Type) [Finite ι] (n : ι → ℕ)
    (hn : ∀ i, n i ≠ 0) : ∃ l : List ℕ, l.Pairwise (· ∣ ·) ∧ (∀ d ∈ l, d ≠ 0) ∧
      Nonempty ((∀ i, ZMod (n i)) ≃+ ZModPi l) := by
  revert n
  refine Finite.induction_empty_option (P := fun ι ↦ ∀ n : ι → ℕ, (∀ i, n i ≠ 0) →
    ∃ l : List ℕ, l.Pairwise (· ∣ ·) ∧ (∀ d ∈ l, d ≠ 0) ∧
      Nonempty ((∀ i, ZMod (n i)) ≃+ ZModPi l)) ?_ ?_ ?_ ι
  · intro α β e h n hn
    obtain ⟨l, hl, hl0, ⟨f⟩⟩ := h (n ∘ e) fun i ↦ hn (e i)
    exact ⟨l, hl, hl0, ⟨(RingEquiv.piCongrLeft (fun i ↦ ZMod (n i)) e).toAddEquiv.symm.trans f⟩⟩
  · exact fun _ _ ↦ ⟨[], .nil, by simp, ⟨AddEquiv.ofUnique⟩⟩
  · intro α _ h n hn
    obtain ⟨l, hl, hl0, ⟨f⟩⟩ := h (fun i ↦ n (some i)) fun i ↦ hn (some i)
    obtain ⟨g⟩ := nonempty_addEquiv_insertChain (n none) l
    exact ⟨insertChain (n none) l, pairwise_insertChain _ hl,
      ne_zero_of_mem_insertChain (hn none) hl0,
      ⟨RingEquiv.piOptionEquivProd.toAddEquiv.trans (((AddEquiv.refl _).prodCongr f).trans g)⟩⟩

/-- Existence of invariant factors: a finite abelian group is `∏ ZMod dᵢ` for a divisibility
chain `d₁ ∣ d₂ ∣ ⋯` of integers `> 1`. -/
private theorem exists_invariantFactors (A : Type*) [AddCommGroup A] [Finite A] :
    ∃ l : List ℕ, l.Pairwise (· ∣ ·) ∧ (∀ d ∈ l, 1 < d) ∧
      Nonempty (A ≃+ ((i : Fin l.length) → ZMod l[i])) := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
  obtain ⟨l, hl, hl0, ⟨f⟩⟩ := exists_pairwise_dvd_addEquiv_pi ι n fun i ↦ (hn i).ne_bot
  obtain ⟨g⟩ := nonempty_addEquiv_filter l
  refine ⟨l.filter (· ≠ 1), hl.filter _, fun d hd ↦ ?_,
    ⟨e.trans ((DirectSum.addEquivProd _).trans (f.trans g))⟩⟩
  rw [List.mem_filter, decide_eq_true_iff] at hd
  have := hl0 d hd.1
  omega

/-- The gcd profile at `0` is the product of the entries. -/
private theorem prod_map_gcd_zero (l : List ℕ) : (l.map (Nat.gcd 0)).prod = l.prod := by
  rw [show Nat.gcd 0 = id from funext Nat.gcd_zero_left, List.map_id]

/-- If `D :: t` is a chain listed from its largest entry down and `D' :: t'` is a list of
integers `> 1` with the same gcd profile `m ↦ ∏ gcd m dᵢ`, then `D'` divides `D`. -/
private theorem dvd_of_prod_map_gcd_eq {D D' : ℕ} {t t' : List ℕ}
    (hl : (D :: t).Pairwise (fun a b ↦ b ∣ a)) (h1' : ∀ d ∈ D' :: t', 1 < d)
    (h : ∀ m : ℕ, ((D :: t).map m.gcd).prod = ((D' :: t').map m.gcd).prod) : D' ∣ D := by
  -- At `m = D` the left side is the full product, as every entry divides `D`; on the right each
  -- factor `gcd D d'` is at most `d'`, so equality forces `gcd D D' = D'`.
  have hdvd (x : ℕ) (hx : x ∈ D :: t) : x ∣ D := by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact dvd_rfl
    · exact (List.pairwise_cons.1 hl).1 x hx
  have hD := h D
  rw [List.map_congr_left fun x hx ↦ Nat.gcd_eq_right (hdvd x hx), List.map_id',
    ← prod_map_gcd_zero, h 0] at hD
  simp only [List.map_cons, List.prod_cons, Nat.gcd_zero_left, prod_map_gcd_zero] at hD
  have hpos (d : ℕ) (hd : d ∈ t') : 0 < d := zero_lt_one.trans (h1' d (List.mem_cons_of_mem _ hd))
  have hY : (t'.map D.gcd).prod ≤ t'.prod := by
    simpa using List.prod_le_prod (l := t') (f := D.gcd) (g := id)
      fun x hx ↦ Nat.gcd_le_right _ (hpos x hx)
  have hg : D.gcd D' ≤ D' := Nat.gcd_le_right _ (zero_lt_one.trans (h1' D' List.mem_cons_self))
  have hgD : D.gcd D' = D' := by
    by_contra hne
    have : D.gcd D' * (t'.map D.gcd).prod < D' * t'.prod :=
      calc _ ≤ D.gcd D' * t'.prod := Nat.mul_le_mul_left _ hY
        _ < D' * t'.prod := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hg hne)
          (List.prod_pos hpos)
    omega
  exact hgD ▸ Nat.gcd_dvd_left D D'

/-- The gcd profile `m ↦ ∏ gcd m dᵢ` determines a chain `d₁ ∣ d₂ ∣ ⋯`, listed here from its
largest entry down, of integers `> 1`. -/
private theorem eq_of_prod_map_gcd_eq_of_pairwise_dvd_swap {l l' : List ℕ}
    (hl : l.Pairwise (fun a b ↦ b ∣ a)) (hl' : l'.Pairwise (fun a b ↦ b ∣ a))
    (h1 : ∀ d ∈ l, 1 < d) (h1' : ∀ d ∈ l', 1 < d)
    (h : ∀ m : ℕ, (l.map m.gcd).prod = (l'.map m.gcd).prod) : l = l' := by
  -- An empty list has gcd profile `1` at `m = 0`, a nonempty one does not.
  have hne {D : ℕ} {t s : List ℕ} (h1 : ∀ d ∈ D :: t, 1 < d)
      (h : ∀ m : ℕ, ((D :: t).map m.gcd).prod = (s.map m.gcd).prod) : s ≠ [] := by
    rintro rfl
    have := h 0
    rw [prod_map_gcd_zero, List.map_nil, List.prod_nil, List.prod_cons] at this
    exact (h1 D List.mem_cons_self).ne' (Nat.eq_one_of_mul_eq_one_right this)
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons D' t' => exact absurd rfl (hne h1' fun m ↦ (h m).symm)
  | cons D t ih =>
    cases l' with
    | nil => exact absurd rfl (hne h1 h)
    | cons D' t' =>
      obtain rfl : D = D' := Nat.dvd_antisymm (dvd_of_prod_map_gcd_eq hl' h1 fun m ↦ (h m).symm)
        (dvd_of_prod_map_gcd_eq hl h1' h)
      refine congrArg _ (ih (List.pairwise_cons.1 hl).2 (List.pairwise_cons.1 hl').2
        (fun d hd ↦ h1 d (List.mem_cons_of_mem _ hd)) (fun d hd ↦ h1' d (List.mem_cons_of_mem _ hd))
        fun m ↦ Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_right m
          (zero_lt_one.trans (h1 D List.mem_cons_self))) ?_)
      simpa only [List.map_cons, List.prod_cons] using h m

/-- Two divisibility chains `d₁ ∣ d₂ ∣ ⋯` of integers `> 1` with the same gcd profile
`m ↦ ∏ gcd m dᵢ` are equal. -/
private theorem eq_of_prod_map_gcd_eq {l l' : List ℕ} (hl : l.Pairwise (· ∣ ·))
    (hl' : l'.Pairwise (· ∣ ·)) (h1 : ∀ d ∈ l, 1 < d) (h1' : ∀ d ∈ l', 1 < d)
    (h : ∀ m : ℕ, (l.map m.gcd).prod = (l'.map m.gcd).prod) : l = l' := by
  refine List.reverse_injective <| eq_of_prod_map_gcd_eq_of_pairwise_dvd_swap
    (List.pairwise_reverse.2 hl) (List.pairwise_reverse.2 hl') (by simpa using h1)
    (by simpa using h1') fun m ↦ ?_
  simpa [List.map_reverse, List.prod_reverse] using h m

/-- In `∏ ZMod dᵢ` with all `dᵢ ≠ 0`, the elements killed by `m` number `∏ gcd m dᵢ`. -/
private theorem card_torsionBy_zmodPi (l : List ℕ) (hl : ∀ d ∈ l, d ≠ 0) (m : ℕ) :
    Nat.card (AddSubgroup.torsionBy (ZModPi l) (m : ℤ)) = (l.map m.gcd).prod := by
  rw [Nat.card_congr (AddSubgroup.torsionByPiEquiv _ _).toEquiv, Nat.card_pi,
    ← Fin.prod_univ_fun_getElem]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have : NeZero l[i] := ⟨hl _ (List.getElem_mem _)⟩
  exact ZMod.card_torsionBy m _

/-- **Invariant factors.** A finite abelian group is `∏ ZMod dᵢ` for exactly one divisibility
chain `d₁ ∣ d₂ ∣ ⋯` of integers `> 1`; the chain is empty for the trivial group. -/
theorem existsUnique_invariantFactors (A : Type*) [AddCommGroup A] [Finite A] :
    ∃! l : List ℕ, l.Pairwise (· ∣ ·) ∧ (∀ d ∈ l, 1 < d) ∧
      Nonempty (A ≃+ ((i : Fin l.length) → ZMod l[i])) := by
  obtain ⟨l, hl⟩ := exists_invariantFactors A
  refine ⟨l, hl, fun l' ⟨hl', h1', ⟨e'⟩⟩ ↦ ?_⟩
  obtain ⟨hl, h1, ⟨e⟩⟩ := hl
  refine eq_of_prod_map_gcd_eq hl' hl h1' h1 fun m ↦ ?_
  rw [← card_torsionBy_zmodPi l' (fun d hd ↦ (h1' d hd).ne_bot) m,
    ← card_torsionBy_zmodPi l (fun d hd ↦ (h1 d hd).ne_bot) m]
  exact Nat.card_congr (AddEquiv.torsionByCongr (e'.symm.trans e) m).toEquiv

/-- The **invariant factors** of a finite abelian group `A`: the unique divisibility chain
`d₁ ∣ d₂ ∣ ⋯` of integers `> 1` with `A ≃+ ∏ ZMod dᵢ` (`existsUnique_invariantFactors`). -/
noncomputable def invariantFactors (A : Type*) [AddCommGroup A] [Finite A] : List ℕ :=
  (existsUnique_invariantFactors A).exists.choose

variable {A B : Type*} [AddCommGroup A] [Finite A] [AddCommGroup B] [Finite B]

/-- The invariant factors are characterized as the divisibility chain of integers `> 1` whose
cyclic factors multiply to `A`. -/
theorem invariantFactors_eq_iff {l : List ℕ} :
    invariantFactors A = l ↔ l.Pairwise (· ∣ ·) ∧ (∀ d ∈ l, 1 < d) ∧
      Nonempty (A ≃+ ((i : Fin l.length) → ZMod l[i])) :=
  ⟨fun h ↦ h ▸ (existsUnique_invariantFactors A).exists.choose_spec,
    fun h ↦ (existsUnique_invariantFactors A).unique
      (existsUnique_invariantFactors A).exists.choose_spec h⟩

/-- Each invariant factor divides the later ones. -/
theorem pairwise_dvd_invariantFactors : (invariantFactors A).Pairwise (· ∣ ·) :=
  (invariantFactors_eq_iff.1 rfl).1

/-- Every invariant factor is greater than `1`. -/
theorem one_lt_of_mem_invariantFactors {d : ℕ} (hd : d ∈ invariantFactors A) : 1 < d :=
  (invariantFactors_eq_iff.1 rfl).2.1 d hd

/-- A finite abelian group is the product of the cyclic groups of its invariant factors. -/
theorem nonempty_addEquiv_invariantFactors (A : Type*) [AddCommGroup A] [Finite A] :
    Nonempty (A ≃+ ((i : Fin (invariantFactors A).length) → ZMod (invariantFactors A)[i])) :=
  (invariantFactors_eq_iff.1 rfl).2.2

/-- Isomorphic finite abelian groups have the same invariant factors. -/
theorem invariantFactors_congr (e : A ≃+ B) : invariantFactors A = invariantFactors B := by
  obtain ⟨f⟩ := nonempty_addEquiv_invariantFactors B
  exact invariantFactors_eq_iff.2 ⟨pairwise_dvd_invariantFactors,
    fun _ ↦ one_lt_of_mem_invariantFactors, ⟨e.trans f⟩⟩

/-- **The invariant factors are a complete invariant**: two finite abelian groups are isomorphic
exactly when they have the same invariant factors. -/
theorem nonempty_addEquiv_iff_invariantFactors_eq :
    Nonempty (A ≃+ B) ↔ invariantFactors A = invariantFactors B := by
  refine ⟨fun ⟨e⟩ ↦ invariantFactors_congr e, fun h ↦ ?_⟩
  obtain ⟨e⟩ := nonempty_addEquiv_invariantFactors A
  obtain ⟨-, -, ⟨f⟩⟩ := invariantFactors_eq_iff.1 h.symm
  exact ⟨e.trans f.symm⟩

/-- The number of elements of `A` killed by `m` is `∏ gcd m dᵢ` over the invariant factors. -/
theorem card_torsionBy_eq_prod_map_gcd (m : ℕ) :
    Nat.card (AddSubgroup.torsionBy A (m : ℤ)) = ((invariantFactors A).map m.gcd).prod := by
  obtain ⟨e⟩ := nonempty_addEquiv_invariantFactors A
  rw [Nat.card_congr (AddEquiv.torsionByCongr e m).toEquiv]
  exact card_torsionBy_zmodPi _ (fun _ hd ↦ (one_lt_of_mem_invariantFactors hd).ne_bot) m

/-- The invariant factors multiply to the order of the group. -/
@[simp]
theorem prod_invariantFactors : (invariantFactors A).prod = Nat.card A := by
  have htop : AddSubgroup.torsionBy A ((0 : ℕ) : ℤ) = ⊤ := by
    ext
    simp
  rw [← prod_map_gcd_zero, ← card_torsionBy_eq_prod_map_gcd, htop, AddSubgroup.card_top]

/-- A finite abelian group has no invariant factors exactly when it is trivial. -/
@[simp]
theorem invariantFactors_eq_nil_iff : invariantFactors A = [] ↔ Subsingleton A := by
  rw [← Finite.card_le_one_iff_subsingleton, ← prod_invariantFactors]
  refine ⟨fun h ↦ by simp [h], fun h ↦ List.eq_nil_iff_forall_not_mem.2 fun d hd ↦ ?_⟩
  have hpos : 0 < ((invariantFactors A).erase d).prod := List.prod_pos fun x hx ↦
    zero_lt_one.trans (one_lt_of_mem_invariantFactors (List.mem_of_mem_erase hx))
  rw [← List.prod_erase hd] at h
  nlinarith [one_lt_of_mem_invariantFactors hd]

/-- The last invariant factor is the exponent of the group. -/
theorem getLast_invariantFactors (h : invariantFactors A ≠ []) :
    (invariantFactors A).getLast h = AddMonoid.exponent A := by
  obtain ⟨e⟩ := nonempty_addEquiv_invariantFactors A
  rw [AddMonoid.exponent_eq_of_addEquiv e, AddMonoid.exponent_pi]
  simp only [ZMod.exponent]
  have hlen : (invariantFactors A).length - 1 < (invariantFactors A).length :=
    Nat.sub_one_lt (List.length_pos_iff.2 h).ne'
  rw [List.getLast_eq_getElem]
  -- Every entry divides the last one, which is itself one of the entries.
  refine Nat.dvd_antisymm (Finset.dvd_lcm (Finset.mem_univ (⟨_, hlen⟩ : Fin _)))
    (Finset.lcm_dvd fun i _ ↦ ?_)
  rcases (Nat.le_sub_one_of_lt i.isLt).lt_or_eq with hi | hi
  · exact List.pairwise_iff_getElem.1 pairwise_dvd_invariantFactors _ _ i.isLt hlen hi
  · simp [hi]

/-- A cyclic group `ZMod n` with `n > 1` has the single invariant factor `n`. -/
@[simp]
theorem invariantFactors_zmod {n : ℕ} [NeZero n] (hn : n ≠ 1) :
    invariantFactors (ZMod n) = [n] :=
  invariantFactors_eq_iff.2 ⟨List.pairwise_singleton _ _,
    by simpa [Nat.one_lt_iff_ne_zero_and_ne_one] using ⟨NeZero.ne n, hn⟩, ⟨singletonAddEquiv n⟩⟩

/-- For `a ∣ b` with `a > 1`, the group `ZMod a × ZMod b` has invariant factors `[a, b]`. -/
@[simp]
theorem invariantFactors_zmod_prod {a b : ℕ} [NeZero a] [NeZero b] (ha : a ≠ 1) (hab : a ∣ b) :
    invariantFactors (ZMod a × ZMod b) = [a, b] := by
  have hb : b ≠ 1 := fun hb ↦ ha (Nat.dvd_one.1 (hb ▸ hab))
  refine invariantFactors_eq_iff.2 ⟨by simpa using hab, ?_,
    ⟨((AddEquiv.refl _).prodCongr (singletonAddEquiv b)).trans (consAddEquiv a [b]).symm⟩⟩
  simpa [Nat.one_lt_iff_ne_zero_and_ne_one] using ⟨⟨NeZero.ne a, ha⟩, NeZero.ne b, hb⟩

end TauCeti.AddCommGroup
