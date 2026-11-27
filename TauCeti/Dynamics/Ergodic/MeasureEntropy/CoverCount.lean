/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic
public import TauCeti.InformationTheory.PartitionEntropy.RestrictLabel
import Mathlib.Topology.UniformSpace.Compact
import TauCeti.InformationTheory.PartitionEntropy.Finite

/-!
# Counting itineraries along dynamical covers

This is the counting step of Goodwyn's inequality `h_μ(T) ≤ h_top(T)` (ArithmeticDynamics §2.7).
Let `ζ : X → ι ⊕ Unit` be a label whose `Sum.inl` values are *separated by an entourage `U`*: two
points `U`-close to a common point never carry different `Sum.inl` values. This is the case for
the restriction `restrictLabel a (⋃ i, F i)` of a label `a` to closed sets `F i ⊆ a ⁻¹' {i}` when
the images `U.image (F i)` are pairwise disjoint
(`TauCeti.isInlSeparated_restrictLabel_iUnion`), and on a compact uniform space such an entourage
exists for pairwise disjoint closed sets (`TauCeti.exists_mem_uniformity_disjoint_image`).

Then the itineraries of length `n` of the points in one dynamical ball for `U` are determined by
which of their entries are `Sum.inl`, so there are at most `2 ^ n` of them, and a dynamical cover
`s` gives at most `card s * 2 ^ n` itineraries in all. By the support bound, the entropy of the
itinerary is at most `log (card s * 2 ^ n) = n log 2 + log (card s)`
(`TauCeti.countablePartitionEntropy_iteratedPartitionLabel_le_log_card_mul`).

## Main definitions

* `TauCeti.IsInlSeparated ζ U`: points `U`-close to a common point carry equal `Sum.inl` values.

## Main results

* `TauCeti.IsInlSeparated.iteratedPartitionLabel_eq`: in a dynamical ball, an itinerary is
  determined by the positions of its `Sum.inl` entries.
* `TauCeti.countablePartitionEntropy_iteratedPartitionLabel_le_log_card_mul`: for a dynamical cover
  `s` of `X`, `H(join_n ζ) ≤ log (card s * 2 ^ n)`.
* `TauCeti.isInlSeparated_restrictLabel_iUnion`, `TauCeti.exists_mem_uniformity_disjoint_image`:
  restrictions to closed sets with disjoint `U`-images are separated, and on a compact uniform space
  disjoint closed sets have such an entourage.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, §4.6.3, pp. 122–123.
-/

public section

open MeasureTheory Set Dynamics
open scoped ENNReal Uniformity

namespace TauCeti

variable {X ι : Type*}

/-- A label `ζ : X → ι ⊕ Unit` is `Sum.inl`-separated by `U` if any two points `U`-close to a
common point that both carry `Sum.inl` values carry the same one. -/
def IsInlSeparated (ζ : X → ι ⊕ Unit) (U : SetRel X X) : Prop :=
  ∀ ⦃y z z' : X⦄, (z, y) ∈ U → (z', y) ∈ U → ∀ ⦃i j : ι⦄, ζ z = .inl i → ζ z' = .inl j → i = j

/-- In a dynamical ball for an entourage separating the `Sum.inl` values of `ζ`, the itinerary of
`ζ` is determined by the positions of its `Sum.inl` entries. -/
theorem IsInlSeparated.iteratedPartitionLabel_eq {ζ : X → ι ⊕ Unit} {U : SetRel X X}
    (h : IsInlSeparated ζ U) {T : X → X} {n : ℕ} {y z z' : X}
    (hz : (z, y) ∈ dynEntourage T U n) (hz' : (z', y) ∈ dynEntourage T U n)
    (hl : ∀ k, (iteratedPartitionLabel T ζ n z k).isLeft =
      (iteratedPartitionLabel T ζ n z' k).isLeft) :
    iteratedPartitionLabel T ζ n z = iteratedPartitionLabel T ζ n z' := by
  rw [mem_dynEntourage] at hz hz'
  funext k
  have hk := hl k
  simp only [iteratedPartitionLabel_apply] at hk ⊢
  rcases hw : ζ (T^[k] z) with i | u <;> rcases hw' : ζ (T^[k] z') with j | u' <;>
    rw [hw, hw'] at hk
  · rw [h (hz k k.isLt) (hz' k k.isLt) hw hw']
  · simp at hk
  · simp at hk

/-- The itineraries of length `n` of the points of `X` take at most `card s * 2 ^ n` values for a
dynamical cover `s` by an entourage separating the `Sum.inl` values of `ζ`. -/
theorem IsInlSeparated.exists_finset_iteratedPartitionLabel {ζ : X → ι ⊕ Unit} {U : SetRel X X}
    (h : IsInlSeparated ζ U) {T : X → X} {n : ℕ} {s : Finset X} (hs : IsDynCoverOf T univ U n s) :
    ∃ S : Finset (Fin n → ι ⊕ Unit), S.card ≤ s.card * 2 ^ n ∧
      ∀ z, iteratedPartitionLabel T ζ n z ∈ S := by
  classical
  -- A point of the cover and a pattern of `Sum.inl` positions determine the itinerary.
  let G : X × (Fin n → Bool) → Fin n → ι ⊕ Unit := fun p ↦
    if hp : ∃ z, (z, p.1) ∈ dynEntourage T U n ∧
        (fun k ↦ (iteratedPartitionLabel T ζ n z k).isLeft) = p.2 then
      iteratedPartitionLabel T ζ n hp.choose
    else fun _ ↦ .inr ()
  refine ⟨(s ×ˢ (Finset.univ : Finset (Fin n → Bool))).image G, ?_, fun z ↦ ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp [Finset.card_univ, Fintype.card_bool]
  · obtain ⟨y, hy, hzy⟩ := hs (mem_univ z)
    have hp : ∃ z', (z', y) ∈ dynEntourage T U n ∧
        (fun k ↦ (iteratedPartitionLabel T ζ n z' k).isLeft) =
          fun k ↦ (iteratedPartitionLabel T ζ n z k).isLeft := ⟨z, hzy, rfl⟩
    refine Finset.mem_image.2 ⟨(y, fun k ↦ (iteratedPartitionLabel T ζ n z k).isLeft),
      Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩, ?_⟩
    simp only [G, dite_eq_left_of_eq_true (eq_true hp)]
    exact h.iteratedPartitionLabel_eq hp.choose_spec.1 hzy (congrFun hp.choose_spec.2)

/-- **Counting step of Goodwyn's inequality.** Under a probability measure (or the zero measure),
if `U` separates the `Sum.inl` values of a measurable label `ζ` and `s` is a dynamical cover of
`X` by `U` at time `n`, then `H(join_n ζ) ≤ log (card s * 2 ^ n)`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_le_log_card_mul [MeasurableSpace X]
    {μ : Measure X} [IsZeroOrProbabilityMeasure μ] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {T : X → X} (hT : Measurable T) {ζ : X → ι ⊕ Unit}
    (hζ : Measurable ζ) {U : SetRel X X} (h : IsInlSeparated ζ U) {n : ℕ} {s : Finset X}
    (hs : IsDynCoverOf T univ U n s) :
    countablePartitionEntropy μ (iteratedPartitionLabel T ζ n) ≤
      ENNReal.ofReal (Real.log (s.card * 2 ^ n)) := by
  obtain ⟨S, hS, hmem⟩ := h.exists_finset_iteratedPartitionLabel hs
  refine (countablePartitionEntropy_le_ofReal_log_card
    (measurable_iteratedPartitionLabel hT hζ n) S hmem).trans ?_
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  refine ENNReal.ofReal_le_ofReal (Real.log_le_log (by exact_mod_cast hne.card_pos) ?_)
  exact_mod_cast hS

/-- The restriction of a label `a` to the union of sets `F i ⊆ a ⁻¹' {i}` is `Sum.inl`-separated
by every entourage `U` whose images of the `F i` are pairwise disjoint. -/
theorem isInlSeparated_restrictLabel_iUnion {a : X → ι} {F : ι → Set X}
    (hF : ∀ i, F i ⊆ a ⁻¹' {i}) {U : SetRel X X}
    (hU : ∀ i j, i ≠ j → Disjoint (U.image (F i)) (U.image (F j))) :
    IsInlSeparated (restrictLabel a (⋃ i, F i)) U := by
  -- A point of the union with `Sum.inl` value `i` lies in `F i`.
  have hmem {z : X} {i : ι} (hz : restrictLabel a (⋃ i, F i) z = .inl i) : z ∈ F i := by
    by_cases hzF : z ∈ ⋃ i, F i
    · rw [restrictLabel_of_mem hzF, Sum.inl.injEq] at hz
      obtain ⟨k, hk⟩ := mem_iUnion.1 hzF
      have hak : a z = k := hF k hk
      rwa [← hz, hak]
    · simp [restrictLabel_of_notMem hzF] at hz
  intro y z z' hz hz' i j hzi hzj
  by_contra hij
  exact disjoint_left.1 (hU i j hij) (SetRel.mem_image.2 ⟨z, hmem hzi, hz⟩)
    (SetRel.mem_image.2 ⟨z', hmem hzj, hz'⟩)

/-- On a compact uniform space, finitely many pairwise disjoint closed sets `F i` have an
entourage whose images of the `F i` are pairwise disjoint. -/
theorem exists_mem_uniformity_disjoint_image [UniformSpace X] [CompactSpace X] [Finite ι]
    {F : ι → Set X} (hF : ∀ i, IsClosed (F i)) (hdisj : Pairwise (Function.onFun Disjoint F)) :
    ∃ U ∈ 𝓤 X, ∀ i j, i ≠ j → Disjoint (SetRel.image U (F i)) (SetRel.image U (F j)) := by
  have hpair (p : ι × ι) : ∃ V ∈ 𝓤 X,
      p.1 ≠ p.2 → Disjoint (SetRel.image V (F p.1)) (SetRel.image V (F p.2)) := by
    by_cases hp : p.1 = p.2
    · exact ⟨univ, Filter.univ_mem, fun h ↦ (h hp).elim⟩
    · obtain ⟨V, hV, hd⟩ :=
        (hdisj hp).exists_uniform_thickening (hF p.1).isCompact (hF p.2)
      -- The image under the symmetrization of `V` lies in the `V`-thickening.
      have himage (A : Set X) : (SetRel.symmetrize V).image A ⊆ ⋃ x ∈ A, SetRel.ball V x :=
        fun b hb ↦ by
          obtain ⟨a, ha, hab⟩ := SetRel.mem_image.1 hb
          exact mem_iUnion₂.2 ⟨a, ha, SetRel.mem_ball.2 hab.2⟩
      exact ⟨_, symmetrize_mem_uniformity hV, fun _ ↦ hd.mono (himage _) (himage _)⟩
  choose V hV hd using hpair
  refine ⟨⋂ p, V p, Filter.iInter_mem.2 hV, fun i j hij ↦ (hd (i, j) hij).mono ?_ ?_⟩ <;>
    exact SetRel.image_subset_image_left (iInter_subset V (i, j))

end TauCeti
