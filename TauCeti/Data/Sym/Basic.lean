/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Basic lemmas for symmetric powers

This file records small API extensions for Mathlib's symmetric powers, and the map
`TauCeti.Sym.ofFn` reading an ordered `n`-tuple `f : Fin n → α` as an unordered one.

`ofFn` presents `Sym α n` as a quotient of `Fin n → α`: it is surjective, and its fibres are the
orbits of the permutation action, by `TauCeti.Sym.ofFn_eq_ofFn_iff`. Nothing here is topological;
`TauCeti/Topology/Sym/Basic.lean` uses this to give `Sym α n` the quotient topology coinduced along
`ofFn`.

## Main declarations

* `TauCeti.Sym.ofFn`: the ordered tuple `f : Fin n → α` read as a point of `Sym α n`, and
  `TauCeti.Sym.ofFn_surjective`, that every unordered tuple arises this way.
* `TauCeti.Sym.map_ofFn`, `TauCeti.Sym.map_comp_ofFn` and `TauCeti.Sym.ofFn_fin_append`: `ofFn`
  intertwines postcomposition with `Sym.map`, and concatenation of ordered tuples with
  `Sym.append`.
* `TauCeti.Sym.ofFn_eq_ofFn_iff`: two ordered tuples have the same underlying unordered tuple
  exactly when one is a reindexing of the other by a permutation.
* `TauCeti.Sym.count_coe_ofFn`: the multiplicity of a value in an unordered tuple is the number
  of entries of the ordered tuple taking that value.
* `TauCeti.Sym.sum_single_eq_sum_single_iff`: two ordered tuples have the same letter counts
  `∑ₜ single (f t) 1` exactly when they have the same underlying unordered tuple, and
  `TauCeti.Sym.exists_sum_single_eq_iff`: the letter counts of ordered `n`-tuples are exactly the
  exponent vectors of total degree `n`.
* `TauCeti.Sym.basepointDivisor` is the set of unordered tuples containing a fixed point;
  `TauCeti.Sym.range_cons` identifies it with the range of adjoining that point.
* `TauCeti.symFinTwoEquiv`: an unordered `d`-tuple over `Fin 2` is determined by how many of its
  entries are `0`, so there are `d + 1` of them.
-/

public section

namespace Sym

variable {X Y : Type*} {d e : ℕ}

/-- Mapping a function over an appended symmetric-power point is the append of the mapped
symmetric-power points. -/
@[simp]
theorem map_append (f : X → Y) (s : Sym X d) (t : Sym X e) :
    Sym.map f (s.append t) = (Sym.map f s).append (Sym.map f t) :=
  Subtype.ext <| by simp [Multiset.map_add]

end Sym

namespace TauCeti

namespace Sym

variable {α β ι : Type*} {m n : ℕ}

/-! ### Ordered tuples as unordered ones -/

/-- The ordered `n`-tuple `f : Fin n → α` read as an unordered `n`-tuple.

This is Mathlib's quotient map `Sym.ofVector` precomposed with `List.Vector.ofFn`; the `Fin n → α`
form is the one that carries a product topology, so it is the map that `Sym α n` carries the
quotient topology along in `TauCeti/Topology/Sym/Basic.lean`. -/
def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)

/-- The multiset underlying `ofFn f` is the list of values of `f`. -/
@[simp]
theorem coe_ofFn (f : Fin n → α) : (ofFn f : Multiset α) = ↑(List.ofFn f) :=
  congrArg _ (List.Vector.toList_ofFn f)

/-- The multiplicity of a value in `ofFn f` is the number of entries of `f` equal to it. -/
theorem count_coe_ofFn [DecidableEq α] (f : Fin n → α) (a : α) :
    Multiset.count a (ofFn f : Multiset α) = (Finset.univ.filter fun i => f i = a).card := by
  simp

/-- The points of `ofFn f` are exactly the values of `f`. -/
@[simp]
theorem mem_ofFn {a : α} {f : Fin n → α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  rw [← _root_.Sym.mem_coe, coe_ofFn]
  simp

/-- Every unordered `n`-tuple is the image of an ordered one: `ofFn` is the quotient map
presenting `Sym α n` as a quotient of `Fin n → α`. -/
theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  obtain rfl : l.length = n := by simpa using hs
  exact ⟨l.get, Subtype.ext (by simp)⟩

/-- Prepending a point to an ordered tuple adjoins it to the unordered one. -/
@[simp]
theorem ofFn_cons (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a ::ₛ ofFn f :=
  Subtype.ext <| by simp [Sym.coe_cons, List.ofFn_succ]

/-- Applying a function to every entry of an ordered tuple applies it to every point of the
unordered one. -/
@[simp]
theorem map_ofFn (f : α → β) (g : Fin n → α) : Sym.map f (ofFn g) = ofFn (f ∘ g) :=
  Sym.coe_injective <| by simp [Sym.coe_map]

/-- The compatibility of `Sym.map` with `ofFn`, as an equality of maps out of ordered tuples. -/
theorem map_comp_ofFn (f : α → β) :
    (Sym.map f : Sym α n → Sym β n) ∘ ofFn = ofFn ∘ Pi.map fun _ : Fin n => f :=
  funext (map_ofFn f)

/-- The range of the map on symmetric powers consists of the unordered tuples whose every point
lies in the range of the original map. -/
theorem mem_range_map (f : α → β) {w : Sym β n} :
    w ∈ Set.range (Sym.map f) ↔ ∀ b ∈ w, b ∈ Set.range f := by
  refine ⟨?_, fun hw => ?_⟩
  · rintro ⟨s, rfl⟩ b hb
    obtain ⟨a, -, rfl⟩ := Sym.mem_map.1 hb
    exact Set.mem_range_self a
  · choose g hg using fun b : {b // b ∈ w} => hw b b.2
    exact ⟨Sym.map g w.attach,
      (Sym.map_map _ _ _).trans ((Sym.map_congr fun b _ => hg b).trans w.attach_map_coe)⟩

/-- Concatenating two ordered tuples adjoins the two unordered ones. -/
@[simp]
theorem ofFn_fin_append (f : Fin m → α) (g : Fin n → α) :
    ofFn (Fin.append f g) = (ofFn f).append (ofFn g) :=
  Sym.coe_injective <| by simp [Sym.coe_append, List.ofFn_fin_append]

/-! ### The fibres of the quotient map -/

/-- Reindexing an ordered tuple by a permutation leaves the underlying unordered tuple unchanged. -/
theorem ofFn_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → α) : ofFn (f ∘ σ) = ofFn f :=
  Sym.coe_injective <| by simpa using Multiset.coe_eq_coe.2 (σ.ofFn_comp_perm f)

/-- Two ordered tuples have the same underlying unordered tuple exactly when one is a reindexing
of the other: the fibres of `ofFn` are the orbits of the permutation action. -/
theorem ofFn_eq_ofFn_iff {f g : Fin n → α} :
    ofFn f = ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · -- the two tuples take each value the same number of times, so their fibres are equinumerous
    have hcard : ∀ c : α, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← count_coe_ofFn g c, ← count_coe_ofFn f c, h]
    exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
      funext fun i => Equiv.ofFiberEquiv_map _ i⟩
  · rintro ⟨σ, rfl⟩
    exact (ofFn_comp_perm σ f).symm

/-! ### Letter counts -/

/-- The letter counts of a family: the coefficient of `a` in `∑ₜ single (f t) 1` is the
number of indices `t` with `f t = a`. -/
theorem sum_single_apply [Fintype ι] [DecidableEq α] (f : ι → α) (a : α) :
    (∑ t, Finsupp.single (f t) 1 : α →₀ ℕ) a = (Finset.univ.filter fun t => f t = a).card := by
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The letter counts of a family with values in `F` sum, over `F`, to the number of indices. -/
theorem sum_sum_single_apply [Fintype ι] {f : ι → α} {F : Finset α} (hf : ∀ t, f t ∈ F) :
    ∑ a ∈ F, (∑ t, Finsupp.single (f t) 1 : α →₀ ℕ) a = Fintype.card ι := by
  classical
  simp only [sum_single_apply]
  exact (Finset.card_eq_sum_card_fiberwise fun t _ => hf t).symm

/-- A value is taken by a family exactly when its letter count is nonzero. -/
theorem sum_single_apply_ne_zero_iff [Fintype ι] {f : ι → α} {a : α} :
    (∑ t, Finsupp.single (f t) 1 : α →₀ ℕ) a ≠ 0 ↔ ∃ t, f t = a := by
  classical
  simp [sum_single_apply]

/-- Two ordered tuples have the same letter counts exactly when they have the same underlying
unordered tuple. -/
theorem sum_single_eq_sum_single_iff {f g : Fin n → α} :
    (∑ t, Finsupp.single (f t) 1 : α →₀ ℕ) = ∑ t, Finsupp.single (g t) 1 ↔ ofFn f = ofFn g := by
  classical
  refine ⟨fun h => Sym.coe_injective (Multiset.ext.mpr fun a => ?_),
    fun h => Finsupp.ext fun a => ?_⟩
  · simpa only [count_coe_ofFn, sum_single_apply] using DFunLike.congr_fun h a
  · simpa only [count_coe_ofFn, sum_single_apply] using
      congrArg (fun s : Sym α n => Multiset.count a (s : Multiset α)) h

/-- The letter counts of ordered `n`-tuples are exactly the exponent vectors of total degree
`n`. -/
theorem exists_sum_single_eq_iff (l : α →₀ ℕ) :
    (∃ f : Fin n → α, ∑ t, Finsupp.single (f t) 1 = l) ↔ (l.sum fun _ k => k) = n := by
  classical
  refine ⟨?_, fun hl => ?_⟩
  · rintro ⟨f, rfl⟩
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) fun _ _ _ => rfl]
    simp
  · obtain ⟨f, hf⟩ := ofFn_surjective (α := α) (n := n)
      ⟨Finsupp.toMultiset l, by rw [Finsupp.card_toMultiset]; exact hl⟩
    refine ⟨f, Finsupp.ext fun a => ?_⟩
    simpa only [count_coe_ofFn, sum_single_apply, _root_.Sym.coe_mk, Finsupp.count_toMultiset]
      using congrArg (fun s : Sym α n => Multiset.count a (s : Multiset α)) hf

/-! ### Adjoining a fixed point -/

/-- The divisor of unordered tuples containing the fixed point `a`. -/
def basepointDivisor (a : α) : Set (Sym α n) := {s | a ∈ s}

@[simp]
theorem mem_basepointDivisor {a : α} {s : Sym α n} :
    s ∈ basepointDivisor a ↔ a ∈ s := Iff.rfl

/-- No unordered tuple of length zero contains a point. -/
@[simp]
theorem basepointDivisor_zero (a : α) : (basepointDivisor a : Set (Sym α 0)) = ∅ :=
  Set.eq_empty_of_forall_notMem fun s => by simp [_root_.Sym.eq_nil_of_card_zero s]

/-- The unordered `(n + 1)`-tuples obtained by adjoining the point `a` are exactly those that
contain `a`. -/
@[simp]
theorem range_cons (a : α) :
    Set.range (Sym.cons a : Sym α n → Sym α (n + 1)) = basepointDivisor a := by
  ext s
  exact ⟨fun ⟨t, ht⟩ => ht ▸ Sym.mem_cons_self a t,
    fun hs => (Sym.exists_cons_of_mem hs).imp fun _ => Eq.symm⟩

end Sym

/-! ### Unordered tuples over a two-element type -/

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`: the two counts sum to `d`, so the pair of them runs
over the antidiagonal of `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

/-- `TauCeti.symFinTwoEquiv` is the number of entries equal to `0`. -/
@[simp]
theorem coe_symFinTwoEquiv_apply (d : ℕ) (s : Sym (Fin 2) d) :
    (symFinTwoEquiv d s : ℕ) = Multiset.count 0 (s : Multiset (Fin 2)) := (rfl)

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]

end TauCeti
