/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Basic

/-!
# Labelled dominant weights and Hodge–Tate labels

A labelled dominant weight for `GL n` assigns a weakly decreasing integer tuple to each
embedding. The label type is arbitrary in the coordinate constructions; for a number field
`F` and coefficient field `Ω` it is `F →+* Ω`. Purity pairs a label with its conjugate and
reverses the coordinate index. Pullback along restriction of embeddings preserves this
condition when restriction commutes with conjugation.

The Hodge–Tate labels here are the integers predicted by the algebraic weight, not the
Hodge–Tate weights of an already constructed Galois representation. The normalization
`HT(ε) = -1` gives `aᵢ + n - 1 - i` on zero-based indices. The shift removes repetitions even
when the original weight has equal coordinates. Extreme regularity is stronger: at some
label, equal-sized subsets of the shifted coordinates must have different sums unless they
coincide.

## References

* T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, *Potential automorphy and change of
  weight*, [arXiv:1010.2561v4](https://arxiv.org/abs/1010.2561v4), §2.1 and Theorem 2.1.1(3).
-/

public section

open scoped BigOperators

namespace TauCeti

namespace DominantWeight

variable {n : ℕ}

/-- The predicted Hodge–Tate weight at a zero-based coordinate, in the convention
`HT(ε) = -1`. This is the existing `rhoShift` translated by `n - 1`. -/
def hodgeTateWeight (a : DominantWeight n) (i : Fin n) : ℤ := a.rhoShift i + ((n : ℤ) - 1)

/-- The coordinate formula for the Hodge–Tate shift. -/
theorem hodgeTateWeight_apply (a : DominantWeight n) (i : Fin n) :
    a.hodgeTateWeight i = a.val i + ((n : ℤ) - 1 - i) := by
  rw [hodgeTateWeight, rhoShift_apply]
  ring

/-- The shifted coordinates strictly decrease, even if the dominant weight has repetitions. -/
theorem strictAnti_hodgeTateWeight (a : DominantWeight n) : StrictAnti a.hodgeTateWeight :=
  fun _ _ hij => add_lt_add_left (a.rhoShift_strictAnti hij) _

/-- Translation of a dominant weight adds the same integer to each Hodge–Tate label. -/
@[simp] theorem hodgeTateWeight_shift (a : DominantWeight n) (m : ℤ) (i : Fin n) :
    (a.shift m).hodgeTateWeight i = a.hodgeTateWeight i + m := by
  simp only [hodgeTateWeight_apply, shift_apply]
  ring

/-- The full multiset of predicted Hodge–Tate weights at one embedding. -/
def hodgeTateWeights (a : DominantWeight n) : Multiset ℤ := List.ofFn a.hodgeTateWeight

/-- The multiset records each shifted coordinate, indexed by `Fin n`. -/
theorem hodgeTateWeights_def (a : DominantWeight n) :
    a.hodgeTateWeights = (List.ofFn a.hodgeTateWeight : Multiset ℤ) := (rfl)

/-- Membership in the Hodge–Tate multiset is occurrence as a shifted coordinate. -/
@[simp] theorem mem_hodgeTateWeights {a : DominantWeight n} {x : ℤ} :
    x ∈ a.hodgeTateWeights ↔ ∃ i, a.hodgeTateWeight i = x := by
  simp [hodgeTateWeights_def]

/-- The Hodge–Tate multiset has one entry per coordinate. -/
@[simp] theorem card_hodgeTateWeights (a : DominantWeight n) : a.hodgeTateWeights.card = n := by
  simp [hodgeTateWeights_def]

/-- The predicted Hodge–Tate weights have no repetitions. -/
@[simp] theorem nodup_hodgeTateWeights (a : DominantWeight n) : a.hodgeTateWeights.Nodup := by
  rw [hodgeTateWeights_def, Multiset.coe_nodup, List.nodup_ofFn]
  exact a.strictAnti_hodgeTateWeight.injective

/-- A determinant twist translates the Hodge–Tate multiset. For a norm twist of exponent `t`,
use `m = -t`. -/
@[simp] theorem hodgeTateWeights_shift (a : DominantWeight n) (m : ℤ) :
    (a.shift m).hodgeTateWeights = a.hodgeTateWeights.map (· + m) := by
  simp only [hodgeTateWeights_def, Multiset.map_coe, List.map_ofFn]
  exact congrArg (fun f : Fin n → ℤ => (List.ofFn f : Multiset ℤ))
    (funext (hodgeTateWeight_shift a m))

/-- The determinant Hodge weight: the coordinate sum plus the triangular shift. -/
theorem sum_hodgeTateWeights (a : DominantWeight n) :
    a.hodgeTateWeights.sum = (∑ i, a.val i) + (↑(n * (n - 1) / 2) : ℤ) := by
  have h (i : Fin n) : a.hodgeTateWeight i = a.val i + (i.rev.val : ℤ) := by
    rw [hodgeTateWeight_apply, Fin.val_rev]
    have := i.isLt
    omega
  simp only [hodgeTateWeights_def, Multiset.sum_coe, List.sum_ofFn, h, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin n, (i.rev.val : ℤ)) = ∑ i : Fin n, (i.val : ℤ) :=
      Equiv.sum_comp Fin.revPerm fun i => (i.val : ℤ)
    _ = ↑(n * (n - 1) / 2 : ℕ) := by
      rw [← Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

/-- The shifted coordinates distinguish all subsets of the same cardinality by their sums. -/
def IsExtremelyRegular (a : DominantWeight n) : Prop :=
  ∀ s t : Finset (Fin n), s.card = t.card →
    (∑ i ∈ s, a.hodgeTateWeight i) = (∑ i ∈ t, a.hodgeTateWeight i) → s = t

/-- Extreme regularity at one embedding is a test on equal-cardinality subsets. -/
theorem isExtremelyRegular_def (a : DominantWeight n) :
    a.IsExtremelyRegular ↔ ∀ s t : Finset (Fin n), s.card = t.card →
      (∑ i ∈ s, a.hodgeTateWeight i) = (∑ i ∈ t, a.hodgeTateWeight i) → s = t := Iff.rfl

/-- The subset-sum test is invariant under a common translation of the coordinates. -/
@[simp] theorem isExtremelyRegular_shift_iff (a : DominantWeight n) (m : ℤ) :
    (a.shift m).IsExtremelyRegular ↔ a.IsExtremelyRegular := by
  simp only [isExtremelyRegular_def, hodgeTateWeight_shift, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul]
  constructor <;> intro h s t hcard heq <;> apply h s t hcard
  · rw [hcard, heq]
  · rw [hcard] at heq
    omega

end DominantWeight

/-- A family of dominant `GL n` weights, one per label. For algebraic automorphic weights the
labels are field embeddings, not infinite places modulo conjugation. -/
abbrev LabelledDominantWeight (ι : Type*) (n : ℕ) := ι → DominantWeight n

namespace LabelledDominantWeight

variable {ι κ η : Type*} {n : ℕ}

/-- Construct a labelled weight directly from antitone integer coordinates. -/
def ofCoordinates (a : ι → Fin n → ℤ) (ha : ∀ τ, Antitone (a τ)) : LabelledDominantWeight ι n :=
  fun τ => ⟨a τ, ha τ⟩

/-- Reading the coordinates of a weight built from antitone tuples recovers those tuples. -/
@[simp] theorem ofCoordinates_apply (a : ι → Fin n → ℤ) (ha : ∀ τ, Antitone (a τ))
    (τ : ι) (i : Fin n) : (ofCoordinates a ha τ : Fin n → ℤ) i = a τ i := (rfl)

/-- Labelled weights are determined by their integer coordinates. -/
theorem ext {a b : LabelledDominantWeight ι n} (h : ∀ τ i, (a τ).val i = (b τ).val i) : a = b :=
  funext fun τ => Subtype.ext (funext (h τ))

/-- Relabel by precomposition; for embeddings this gives base change along restriction. -/
def pullback (a : LabelledDominantWeight ι n) (f : κ → ι) : LabelledDominantWeight κ n := a ∘ f

/-- The weight at a new label is the weight at its image under the restriction map. -/
@[simp] theorem pullback_apply (a : LabelledDominantWeight ι n) (f : κ → ι) (τ : κ) :
    a.pullback f τ = a (f τ) := (rfl)

/-- Pullback along the identity does not change the labelled weight. -/
@[simp] theorem pullback_id (a : LabelledDominantWeight ι n) : a.pullback id = a := by
  funext τ
  simp

/-- Successive restrictions give pullback along their composite. -/
@[simp] theorem pullback_pullback (a : LabelledDominantWeight ι n) (f : κ → ι) (g : η → κ) :
    (a.pullback f).pullback g = a.pullback (f ∘ g) := by
  funext τ
  simp

/-- Purity of weight `w` pairs each coordinate at `τ` with the reverse coordinate at `c τ`.
The coordinate condition is defined without assuming that `c` is an involution. -/
def IsPure (a : LabelledDominantWeight ι n) (c : ι → ι) (w : ℤ) : Prop :=
  ∀ τ i, (a τ).val i + (a (c τ)).val i.rev = w

/-- Coordinate characterization of purity. -/
theorem isPure_def (a : LabelledDominantWeight ι n) (c : ι → ι) (w : ℤ) :
    a.IsPure c w ↔ ∀ τ i, (a τ).val i + (a (c τ)).val i.rev = w := Iff.rfl

/-- Purity is preserved by pullback along a map commuting with conjugation. -/
theorem IsPure.pullback {a : LabelledDominantWeight ι n} {c : ι → ι} {w : ℤ}
    (h : a.IsPure c w) {d : κ → κ} {f : κ → ι} (hf : Function.Semiconj f d c) :
    (a.pullback f).IsPure d w := by
  rw [isPure_def]
  intro τ i
  simpa only [pullback_apply, hf τ] using (isPure_def ..).mp h (f τ) i

/-- For a CM field and complex coefficients, conjugating a label on the target is equivalent
to precomposing it with the field's CM involution. -/
theorem isPure_complexEmbedding_conjugate_iff {F : Type*} [Field F] [CharZero F]
    [Algebra.IsIntegral ℚ F] [NumberField.IsCMField F]
    (a : LabelledDominantWeight (F →+* ℂ) n) (w : ℤ) :
    a.IsPure NumberField.ComplexEmbedding.conjugate w ↔
      a.IsPure (fun τ => τ.comp (NumberField.IsCMField.complexConj F).toRingEquiv.toRingHom) w := by
  have h (τ : F →+* ℂ) : NumberField.ComplexEmbedding.conjugate τ =
      τ.comp (NumberField.IsCMField.complexConj F).toRingEquiv.toRingHom :=
    RingHom.ext fun x => (NumberField.IsCMField.complexEmbedding_complexConj F τ x).symm
  simp only [isPure_def, h]

/-- At conjugate labels the Hodge–Tate entries in opposite positions add to `w + n - 1`.
Conversely these shifted equalities recover the unshifted purity condition. -/
theorem isPure_iff_hodgeTateWeight_add (a : LabelledDominantWeight ι n) (c : ι → ι) (w : ℤ) :
    a.IsPure c w ↔ ∀ τ i, (a τ).hodgeTateWeight i + (a (c τ)).hodgeTateWeight i.rev =
      w + (n : ℤ) - 1 := by
  simp only [isPure_def, DominantWeight.hodgeTateWeight_apply, Fin.val_rev]
  constructor <;> intro h τ i <;> have hcoord := h τ i <;> have hi := i.isLt <;> omega

/-- At a conjugate label the Hodge–Tate multiset is reflected about half the purity weight
`w + n - 1` of the predicted representation. -/
theorem IsPure.hodgeTateWeights_conj {a : LabelledDominantWeight ι n} {c : ι → ι} {w : ℤ}
    (h : a.IsPure c w) (τ : ι) :
    (a (c τ)).hodgeTateWeights = (a τ).hodgeTateWeights.map (fun x => w + (n : ℤ) - 1 - x) := by
  have heq (i : Fin n) : (a (c τ)).hodgeTateWeight i.rev =
      w + (n : ℤ) - 1 - (a τ).hodgeTateWeight i := by
    have := (isPure_iff_hodgeTateWeight_add a c w).mp h τ i
    omega
  simp only [DominantWeight.hodgeTateWeights_def, Multiset.map_coe, List.map_ofFn]
  rw [← Multiset.coe_eq_coe.mpr (Fin.revPerm.ofFn_comp_perm (a (c τ)).hodgeTateWeight)]
  exact congrArg (fun f : Fin n → ℤ => (List.ofFn f : Multiset ℤ)) (funext heq)

/-- A labelled weight is extremely regular if the equal-cardinality subset-sum test succeeds
at at least one label. -/
def IsExtremelyRegular (a : LabelledDominantWeight ι n) : Prop :=
  ∃ τ, (a τ).IsExtremelyRegular

/-- Extreme regularity asks for one embedding witnessing the subset-sum condition. -/
theorem isExtremelyRegular_def (a : LabelledDominantWeight ι n) :
    a.IsExtremelyRegular ↔ ∃ τ, (a τ).IsExtremelyRegular := Iff.rfl

/-- Reindexing along a surjection preserves and reflects extreme regularity; in particular,
a witnessing embedding can be lifted along such a restriction map. -/
theorem isExtremelyRegular_pullback_iff (a : LabelledDominantWeight ι n) {f : κ → ι}
    (hf : Function.Surjective f) : (a.pullback f).IsExtremelyRegular ↔ a.IsExtremelyRegular := by
  simpa only [isExtremelyRegular_def, pullback_apply] using
    (hf.exists (p := fun τ => (a τ).IsExtremelyRegular)).symm

end LabelledDominantWeight

/-! ### Normalization checks -/

open LabelledDominantWeight

-- The classical weight `k` has purity weight `k - 2` and labels `k - 1` and `0`.
example (k : ℤ) (hk : 2 ≤ k) :
    ∃ a : LabelledDominantWeight Unit 2, (a ()).val = ![k - 2, 0] ∧
      a.IsPure id (k - 2) ∧ (a ()).hodgeTateWeights = {k - 1, 0} := by
  have ha : Antitone (![k - 2, 0] : Fin 2 → ℤ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨ofCoordinates (fun _ => ![k - 2, 0]) (fun _ => ha),
    funext (ofCoordinates_apply _ _ ()), ?_, ?_⟩
  · rw [isPure_def]
    intro τ i
    fin_cases i <;> simp [Fin.rev]
  · have h (i : Fin 2) :
        (ofCoordinates (fun _ : Unit => ![k - 2, 0]) (fun _ => ha) ()).hodgeTateWeight i =
          ![k - 1, 0] i := by
      rw [DominantWeight.hodgeTateWeight_apply, ofCoordinates_apply]
      fin_cases i <;> simp
      omega
    rw [DominantWeight.hodgeTateWeights_def, funext h]
    rfl

-- The two sums at the first label of a conjugate pair can disagree.
example : ∃ a : LabelledDominantWeight Bool 2,
    (a false).val = ![1, 0] ∧ (a true).val = ![0, 0] ∧ ¬ ∃ w, a.IsPure not w := by
  let a := ofCoordinates (fun τ : Bool => if τ then ![0, 0] else ![1, 0])
    (by intro τ; cases τ <;> decide)
  refine ⟨a, funext (ofCoordinates_apply _ _ false), funext (ofCoordinates_apply _ _ true), ?_⟩
  rintro ⟨w, hw⟩
  have h₀ := (isPure_def ..).mp hw false 0
  have h₁ := (isPure_def ..).mp hw false 1
  simp [a, Fin.rev] at h₀ h₁
  omega

-- At parallel weight zero in rank four, the subsets `{0, 3}` and `{1, 2}` both sum to `3`.
example : ¬ IsExtremelyRegular (fun _ : Unit => (0 : DominantWeight 4)) := by
  rintro ⟨⟨⟩, hτ⟩
  apply (by decide : ({0, 3} : Finset (Fin 4)) ≠ {1, 2})
  apply hτ _ _ (by decide)
  simp only [DominantWeight.hodgeTateWeight_apply, DominantWeight.zero_apply]
  decide

-- The shifted coordinates `(8, 4, 2, 1)` distinguish all equal-sized subsets by their sums.
example : IsExtremelyRegular (fun _ : Unit =>
    (⟨![5, 2, 1, 1], by decide⟩ : DominantWeight 4)) := by
  refine ⟨(), ?_⟩
  simp only [DominantWeight.isExtremelyRegular_def, DominantWeight.hodgeTateWeight_apply]
  decide

end TauCeti
