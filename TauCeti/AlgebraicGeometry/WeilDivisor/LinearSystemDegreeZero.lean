/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem

/-!
# Degree-zero complete linear systems

This file records the elementary degree-zero consequences of the complete-linear-system API
for formal Weil divisors.  If the weights on points are strictly positive and principal
divisors have weighted degree zero, then an effective divisor of weighted degree zero is the
zero divisor.  Hence a divisor of weighted degree zero has a nonempty complete linear system
exactly when its divisor class is zero, and in that case the complete linear system is the
singleton `{0}`.

For the unweighted specialization this says that a degree-zero divisor has a nonempty complete
linear system exactly when it is linearly equivalent to zero.  This is a standard Layer A
divisor fact used before the later Picard and Abel-Jacobi constructions: degree-zero effective
representatives are rigid.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the "Divisors on a
curve" and "Degree" items leading to the abstract `Pic⁰ X = ker deg`.  No external
mathematics is vendored; the proofs reuse Tau Ceti's existing `WeilDivisor`,
`OrderSystem.completeLinearSystem`, and weighted-degree API.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-! ### Weighted degree-zero complete linear systems -/

/-- In a positive-weight theory, every member of the complete linear system of a
weighted-degree-zero divisor is zero. -/
lemma eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero {w : X → ℤ}
    (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w) {D E : WeilDivisor X}
    (hE : E ∈ S.completeLinearSystem D) (hD : weightedDegree w D = 0) : E = 0 := by
  have hEeff : IsEffective E := S.isEffective_of_mem_completeLinearSystem hE
  have hdeg : weightedDegree w E = 0 := by
    rw [S.weightedDegree_eq_of_mem_completeLinearSystem h hE, hD]
  exact hEeff.eq_zero_of_weightedDegree_eq_zero_of_pos hw hdeg

/-- If `D` has weighted degree zero, then `|D|` is contained in `{0}`. -/
lemma completeLinearSystem_subset_singleton_zero_of_weightedDegree_zero {w : X → ℤ}
    (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w) {D : WeilDivisor X}
    (hD : weightedDegree w D = 0) : S.completeLinearSystem D ⊆ {0} := by
  intro E hE
  rw [Set.mem_singleton_iff]
  exact S.eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero hw h hE hD

/-- The zero divisor lies in `|D|` exactly when the class of `D` is zero. -/
lemma zero_mem_completeLinearSystem_iff_divisorClass_eq_zero {D : WeilDivisor X} :
    0 ∈ S.completeLinearSystem D ↔ S.divisorClass D = 0 := by
  constructor
  · intro h0
    have hclass := (S.mem_completeLinearSystem_iff_divisorClass.mp h0).2
    simpa using hclass
  · intro hclass
    exact S.mem_completeLinearSystem_iff_divisorClass.mpr ⟨isEffective_zero, by simpa using hclass⟩

/-- For a weighted-degree-zero divisor, nonemptiness of the complete linear system is
equivalent to the divisor class being zero. -/
lemma nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.divisorClass D = 0 := by
  constructor
  · rintro ⟨E, hE⟩
    have hE0 : E = 0 :=
      S.eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero hw h hE hD
    have hclass := S.divisorClass_eq_of_mem_completeLinearSystem hE
    simpa [hE0] using hclass.symm
  · intro hclass
    exact ⟨0, (S.zero_mem_completeLinearSystem_iff_divisorClass_eq_zero).mpr hclass⟩

/-- For a weighted-degree-zero divisor, the complete linear system is `{0}` exactly when its
divisor class is zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    S.completeLinearSystem D = {0} ↔ S.divisorClass D = 0 := by
  constructor
  · intro hset
    rw [← S.zero_mem_completeLinearSystem_iff_divisorClass_eq_zero]
    rw [hset]
    simp
  · intro hclass
    apply Set.Subset.antisymm
    · exact S.completeLinearSystem_subset_singleton_zero_of_weightedDegree_zero hw h hD
    · rw [Set.singleton_subset_iff]
      exact (S.zero_mem_completeLinearSystem_iff_divisorClass_eq_zero).mpr hclass

/-- A weighted-degree-zero divisor has complete linear system `{0}` exactly when it is linearly
equivalent to zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_linearlyEquivalent_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    S.completeLinearSystem D = {0} ↔ S.LinearlyEquivalent D 0 := by
  rw [S.completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_weightedDegree_zero
    hw h hD, ← S.divisorClass_eq_iff]
  simp

/-- A weighted-degree-zero divisor has a nonempty complete linear system exactly when it is
linearly equivalent to zero. -/
lemma nonempty_completeLinearSystem_iff_linearlyEquivalent_zero_of_weightedDegree_zero
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (h : S.IsWeightedDegreeZero w)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.LinearlyEquivalent D 0 := by
  rw [S.nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero hw h hD,
    ← S.divisorClass_eq_iff]
  simp

/-! ### Unweighted degree-zero complete linear systems -/

/-- In the unweighted theory, every member of the complete linear system of a degree-zero
divisor is zero. -/
lemma eq_zero_of_mem_completeLinearSystem_of_degree_zero (h : S.IsUnweightedDegreeZero)
    {D E : WeilDivisor X} (hE : E ∈ S.completeLinearSystem D) (hD : degree D = 0) : E = 0 := by
  exact S.eq_zero_of_mem_completeLinearSystem_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h hE (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- If `D` has degree zero, then `|D|` is contained in `{0}`. -/
lemma completeLinearSystem_subset_singleton_zero_of_degree_zero (h : S.IsUnweightedDegreeZero)
    {D : WeilDivisor X} (hD : degree D = 0) : S.completeLinearSystem D ⊆ {0} := by
  exact S.completeLinearSystem_subset_singleton_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- A degree-zero divisor has a nonempty complete linear system exactly when its divisor class
is zero. -/
lemma nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} (hD : degree D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.divisorClass D = 0 := by
  exact S.nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- A degree-zero divisor has complete linear system `{0}` exactly when its divisor class is
zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} (hD : degree D = 0) :
    S.completeLinearSystem D = {0} ↔ S.divisorClass D = 0 := by
  exact S.completeLinearSystem_eq_singleton_zero_iff_divisorClass_eq_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- A degree-zero divisor has complete linear system `{0}` exactly when it is linearly
equivalent to zero. -/
lemma completeLinearSystem_eq_singleton_zero_iff_linearlyEquivalent_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} (hD : degree D = 0) :
    S.completeLinearSystem D = {0} ↔ S.LinearlyEquivalent D 0 := by
  exact S.completeLinearSystem_eq_singleton_zero_iff_linearlyEquivalent_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

/-- A degree-zero divisor has a nonempty complete linear system exactly when it is linearly
equivalent to zero. -/
lemma nonempty_completeLinearSystem_iff_linearlyEquivalent_zero_of_degree_zero
    (h : S.IsUnweightedDegreeZero) {D : WeilDivisor X} (hD : degree D = 0) :
    (S.completeLinearSystem D).Nonempty ↔ S.LinearlyEquivalent D 0 := by
  exact S.nonempty_completeLinearSystem_iff_linearlyEquivalent_zero_of_weightedDegree_zero
    (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) h (by
      simpa [weightedDegree_one_eq_degree D] using hD)

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
