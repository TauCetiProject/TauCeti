/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence
public import TauCeti.Data.Setoid.Isolation
public import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Extension spectra and level-by-level counting of back-and-forth classes

Fix a family of structures `M i`, `i : ι`, of a relational language `L`. At an ordinal depth `α`
and an arity `n`, back-and-forth equivalence is the equivalence relation `bfTupleSetoid L M α n` on
the pointed tuples `⟨i, a⟩` with `a : Fin n → M i`, comparing tuples across all members of the
family (see `TauCeti.ModelTheory.BackAndForth.Equivalence`).

The **depth-`α` extension spectrum** of a pointed tuple `⟨i, a⟩` is the set of depth-`α` classes
of its one-point extensions `⟨i, snoc a m⟩`, `m : M i`. Two pointed tuples are equivalent at depth
`α + 1` exactly when they are equivalent at depth `α` and have the same extension spectrum. So the
classes at depth `α + 1` inject into pairs of a class at depth `α` and a realized extension
spectrum, which bounds their number.

`BFSmall L M` collects three local conditions on the family: countably many classes of tuples at
depth `0`, countably many realized extension spectra at every countable depth, and isolation of
each countable limit depth by the depths below it (`Setoid.IsolatedBy`). Together they give
countably many classes of tuples at every countable depth and every arity. This is the
level-by-level analysis that bounds the number of isomorphism classes of a family of countable
structures through its back-and-forth levels.

Neither of the first and last conditions is automatic. At depth `0` a tuple is classified by its
atomic type, a set of atomic formulas, so with infinitely many relation symbols there can be
continuum many classes. At a limit depth `λ`, countably many classes at every depth below `λ` do not
bound the classes at `λ`: a class at `λ` is a coherent choice of classes below `λ`, and a countable
product of countable sets can have the size of the continuum. Isolation is the hypothesis that
closes this gap.

## Main definitions

* `TauCeti.bfExtensionSpectrum L M α n x`: the depth-`α` classes of the one-point extensions of
  `x`; `TauCeti.bfExtensionSpectra L M α n`: the realized spectra.
* `TauCeti.BFSmall L M`: the three local smallness conditions.

## Main results

* `TauCeti.bfTupleSetoid_add_one_iff`: equivalence at depth `α + 1` is equivalence at depth `α`
  together with equality of extension spectra.
* `TauCeti.mk_quotient_bfTupleSetoid_add_one_le`: the classes at depth `α + 1` number at most the
  classes at depth `α` times the realized spectra;
  `TauCeti.countable_quotient_bfTupleSetoid_add_one` and
  `TauCeti.mk_quotient_bfTupleSetoid_add_one_le_of_le` transfer countability and any infinite
  bound, such as `ℵ₁`, one level up.
* `TauCeti.BFSmall.countable_quotient`: under `BFSmall`, countably many classes at every depth
  below `ω₁` and every arity.

## References

* The successor step and the smallness conditions follow Cameron Freer's
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/ModelTheory/BFExtensionSpectrum.lean` and
  `InfinitaryLogic/ModelTheory/BFSmallCounting.lean` (Apache-2.0).
* Divergences from that source: the tuples range over an arbitrary family of structures rather
  than over coded models of a sentence, the ordinal universe of the setoids and spectra is
  arbitrary, and the successor bound is stated for any infinite cardinal.
-/

public section

universe u v w o x

namespace TauCeti

open FirstOrder Fin Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type x} {M : ι → Type w}
variable [∀ i, L.Structure (M i)]

variable {α : Ordinal.{o}} {n : ℕ}

variable (L M) in
/-- The **depth-`α` extension spectrum** of a pointed tuple `x = ⟨i, a⟩`: the depth-`α` classes of
its one-point extensions `⟨i, snoc a m⟩`, for `m : M i`. -/
def bfExtensionSpectrum (α : Ordinal.{o}) (n : ℕ) (x : Σ i, Fin n → M i) :
    Set (Quotient (bfTupleSetoid L M α (n + 1))) :=
  Set.range fun m : M x.1 => Quotient.mk _ ⟨x.1, snoc x.2 m⟩

variable (L M) in
/-- The **realized extension spectra** at depth `α` of the pointed `n`-tuples of the family. -/
def bfExtensionSpectra (α : Ordinal.{o}) (n : ℕ) :
    Set (Set (Quotient (bfTupleSetoid L M α (n + 1)))) :=
  Set.range (bfExtensionSpectrum L M α n)

@[simp]
theorem mem_bfExtensionSpectrum {x : Σ i, Fin n → M i}
    {q : Quotient (bfTupleSetoid L M α (n + 1))} :
    q ∈ bfExtensionSpectrum L M α n x ↔ ∃ m : M x.1, Quotient.mk _ ⟨x.1, snoc x.2 m⟩ = q :=
  Set.mem_range

/-- The class of a pointed `(n + 1)`-tuple lies in the extension spectrum of `x` exactly when the
tuple is equivalent to a one-point extension of `x`. -/
theorem mk_mem_bfExtensionSpectrum_iff {x : Σ i, Fin n → M i} {y : Σ i, Fin (n + 1) → M i} :
    Quotient.mk _ y ∈ bfExtensionSpectrum L M α n x ↔
      ∃ m : M x.1, BFEquiv (L := L) α (n + 1) (snoc x.2 m) y.2 := by
  simp only [mem_bfExtensionSpectrum, Quotient.eq, bfTupleSetoid_apply]

@[simp]
theorem mem_bfExtensionSpectra {s : Set (Quotient (bfTupleSetoid L M α (n + 1)))} :
    s ∈ bfExtensionSpectra L M α n ↔ ∃ x, bfExtensionSpectrum L M α n x = s :=
  Set.mem_range

/-- One extension spectrum is contained in another exactly when the forth condition of the
back-and-forth step holds: every one-point extension of `x` is matched by one of `y`. -/
theorem bfExtensionSpectrum_subset_iff {x y : Σ i, Fin n → M i} :
    bfExtensionSpectrum L M α n x ⊆ bfExtensionSpectrum L M α n y ↔
      ∀ m : M x.1, ∃ m' : M y.1, BFEquiv (L := L) α (n + 1) (snoc x.2 m) (snoc y.2 m') := by
  refine ⟨fun h m => ?_, fun h _ hq => ?_⟩
  · obtain ⟨m', hm'⟩ := mk_mem_bfExtensionSpectrum_iff.1 (h (mem_bfExtensionSpectrum.2 ⟨m, rfl⟩))
    exact ⟨m', hm'.symm⟩
  · obtain ⟨m, rfl⟩ := mem_bfExtensionSpectrum.1 hq
    obtain ⟨m', hm'⟩ := h m
    exact mk_mem_bfExtensionSpectrum_iff.2 ⟨m', hm'.symm⟩

/-- **The successor step.** Two pointed tuples are equivalent at depth `α + 1` exactly when they
are equivalent at depth `α` and have the same depth-`α` extension spectrum. -/
theorem bfTupleSetoid_add_one_iff {x y : Σ i, Fin n → M i} :
    bfTupleSetoid L M (α + 1) n x y ↔
      bfTupleSetoid L M α n x y ∧
        bfExtensionSpectrum L M α n x = bfExtensionSpectrum L M α n y := by
  rw [bfTupleSetoid_apply, BFEquiv.add_one, Set.Subset.antisymm_iff,
    bfExtensionSpectrum_subset_iff, bfExtensionSpectrum_subset_iff]
  exact and_congr bfTupleSetoid_apply.symm (and_congr Iff.rfl
    (forall_congr' fun _ => exists_congr fun _ => BFEquiv.symm_iff _ _ _))

variable (L M) in
/-- The classes at depth `α + 1` inject into pairs of a class at depth `α` and a realized
extension spectrum. -/
theorem exists_injective_quotient_bfTupleSetoid_add_one (α : Ordinal.{o}) (n : ℕ) :
    ∃ f : Quotient (bfTupleSetoid L M (α + 1) n) →
      Quotient (bfTupleSetoid L M α n) × bfExtensionSpectra L M α n, Function.Injective f := by
  refine ⟨Quotient.lift (fun x => (Quotient.mk _ x, ⟨bfExtensionSpectrum L M α n x, x, rfl⟩))
    fun x y h => ?_, fun q₁ q₂ hq => ?_⟩
  · obtain ⟨h₀, hs⟩ := bfTupleSetoid_add_one_iff.1 h
    exact Prod.ext (Quotient.sound h₀) (Subtype.ext hs)
  · induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn
    simp only [Quotient.lift_mk, Prod.mk.injEq, Quotient.eq] at hq
    exact Quotient.sound (bfTupleSetoid_add_one_iff.2 ⟨hq.1, congrArg Subtype.val hq.2⟩)

variable (L M) in
/-- The classes at depth `α + 1` number at most the classes at depth `α` times the realized
extension spectra at depth `α`. -/
theorem mk_quotient_bfTupleSetoid_add_one_le (α : Ordinal.{o}) (n : ℕ) :
    #(Quotient (bfTupleSetoid L M (α + 1) n)) ≤
      #(Quotient (bfTupleSetoid L M α n)) * #(bfExtensionSpectra L M α n) := by
  obtain ⟨f, hf⟩ := exists_injective_quotient_bfTupleSetoid_add_one L M α n
  simpa only [mk_prod, Cardinal.lift_id] using mk_le_of_injective hf

/-- **Countable transfer at a successor.** Countably many classes and countably many realized
extension spectra at depth `α` give countably many classes at depth `α + 1`. -/
theorem countable_quotient_bfTupleSetoid_add_one [Countable (Quotient (bfTupleSetoid L M α n))]
    (h : (bfExtensionSpectra L M α n).Countable) :
    Countable (Quotient (bfTupleSetoid L M (α + 1) n)) := by
  have := h.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_quotient_bfTupleSetoid_add_one L M α n
  exact hf.countable

/-- **Cardinal transfer at a successor.** If the classes and the realized extension spectra at
depth `α` number at most an infinite cardinal `κ`, such as `ℵ₁`, so do the classes at depth
`α + 1`. -/
theorem mk_quotient_bfTupleSetoid_add_one_le_of_le {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    (hq : #(Quotient (bfTupleSetoid L M α n)) ≤ κ) (hs : #(bfExtensionSpectra L M α n) ≤ κ) :
    #(Quotient (bfTupleSetoid L M (α + 1) n)) ≤ κ :=
  (mk_quotient_bfTupleSetoid_add_one_le L M α n).trans (mul_le_of_le hκ hq hs)

variable (L M) in
/-- **Level-by-level smallness** of a family of structures, with depths in `Ordinal.{0}`:
countably many classes of `n`-tuples at depth `0`, countably many realized extension spectra at
every depth below `ω₁`, and, at every limit depth below `ω₁`, isolation of the classes by the
depths below it. -/
structure BFSmall : Prop where
  /-- Countably many classes of `n`-tuples at depth `0`, for every arity `n`. -/
  zero (n : ℕ) : Countable (Quotient (bfTupleSetoid L M (0 : Ordinal.{0}) n))
  /-- Countably many realized extension spectra at every depth below `ω₁` and every arity. -/
  add_one {α : Ordinal.{0}} (hα : α < ω₁) (n : ℕ) : (bfExtensionSpectra L M α n).Countable
  /-- At a limit depth below `ω₁`, every pointed tuple is pinned, up to equivalence at the limit
  depth, by its class at some smaller depth. -/
  limit {α : Ordinal.{0}} (hα : α < ω₁) (hlim : Order.IsSuccLimit α) (n : ℕ) :
    (bfTupleSetoid L M α n).IsolatedBy fun β : Set.Iio α => bfTupleSetoid L M β.1 n

/-- **Countably many classes at every countable depth.** Under `BFSmall`, back-and-forth
equivalence at any depth below `ω₁` has countably many classes of `n`-tuples, for every arity
`n`. -/
theorem BFSmall.countable_quotient (h : BFSmall L M) {α : Ordinal.{0}} (hα : α < ω₁) (n : ℕ) :
    Countable (Quotient (bfTupleSetoid L M α n)) := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact h.zero n
  | add_one α ih =>
    have hα' : α < ω₁ := (Order.lt_add_one_iff.mpr le_rfl).trans hα
    have := ih hα' n
    exact countable_quotient_bfTupleSetoid_add_one (h.add_one hα' n)
  | limit α hlim ih =>
    have : Countable (Set.Iio α) := (countable_Iio_of_lt_omega_one hα).to_subtype
    have : ∀ β : Set.Iio α, Countable (Quotient (bfTupleSetoid L M β.1 n)) :=
      fun β => ih β.1 β.2 (β.2.trans hα) n
    exact (h.limit hα hlim n).countable_quotient

end TauCeti
