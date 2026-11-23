/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.Independence.Integration
public import TauCeti.Combinatorics.TreeWalk.Product
public import TauCeti.LinearAlgebra.Matrix.Trace.Pow
public import TauCeti.Probability.RandomMatrix.Wigner.Basic

/-!
# Trace words of Wigner matrices

The moment method for the semicircle law expands the expected moment `E trace Hₙᵏ` of a Wigner
matrix `Hₙ` into a sum over closed walks `w : Fin k → Fin n` of the expectations of the products
`∏ₜ Hₙ (w t) (w (t + 1))` of the entries read along the walk (`Matrix.trace_pow_eq_sum_prod`).
Each step `w t → w (t + 1)` reads the entry at the unordered position `s(w t, w (t + 1))`, its
*edge*; a loop `w t = w (t + 1)` reads a diagonal entry.

When the corner entries are independent, two products of entries reading disjoint sets of
unordered positions are independent and factor in expectation. When the corner entries are also
centred, a product of entries in which some edge is read exactly once has expectation zero: that
entry is independent of all the others and has mean zero. Consequently only the closed walks
traversing each of their edges at least twice contribute to the expected moment. This is the first
reduction of the trace-word expansion; the remaining walks are then classified by their numbers of
vertices and distinct edges.

For a leading word of length `2 * m`, the maximal `m + 1` visited vertices force a
double-traversal tree. Pairing each discovery with its reverse reduces the entry product
to independent squared absolute values. Common off-diagonal second moment `s` in the `n × n` corner
then gives `((n : ℂ)⁻¹ * s) ^ m` (in particular `n⁻ᵐ` when `s = 1`), without centering, higher
moments, or any assumptions on the diagonal entries. The path formulation includes the zero-step
case and proves integrability first.

## Main results

* `TauCeti.indepFun_prod_wignerMatrix_apply_of_disjoint` and
  `TauCeti.integral_prod_mul_prod_wignerMatrix_apply_of_disjoint`: for independent corner entries,
  entry products reading disjoint sets of unordered positions are independent and factor in
  expectation.
* `TauCeti.integral_prod_wignerMatrix_apply_eq_zero`: for independent centred corner entries, a
  product of entries reading some edge exactly once has expectation zero.
* `TauCeti.integral_trace_pow_wignerMatrix`: for `k > 0`, when the corner entries are
  independent, centred and in `Lᵏ`, the expectation of `(Hₙ ^ k).trace` is the sum, over the
  closed walks of length `k` traversing each of their edges at least twice, of the expected
  products of entries along the walk. The integrability of `(Hₙ ^ k).trace` for corner entries
  in `Lᵏ`, which needs neither independence nor centering, is
  `TauCeti.integrable_trace_pow_wignerMatrix` in
  `TauCeti.Probability.RandomMatrix.Wigner.Trace.Integrability`; that theorem covers every `k`
  and assumes a finite measure when `k = 0`.

* `TauCeti.integrable_prod_wignerMatrix_apply_path`,
  `TauCeti.integral_prod_wignerMatrix_apply_path`, and
  `TauCeti.integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq`: integrability and
  second-moment product formulas for double-traversal tree paths (including `m = 0`).
* `TauCeti.integral_prod_wignerMatrix_apply_leading`,
  `TauCeti.integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq`, and
  `TauCeti.integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one`: second-moment
  product formulas for leading cyclic Wigner words, giving `((n : ℂ)⁻¹ * s) ^ m` under
  independence and common off-diagonal second moment `s` in the `n × n` corner (and `n⁻ᵐ` when
  `s = 1`).

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

section SingleEdge

/-- The coordinate of the `n × n` corner entry array read by the `(i, j)` entry of an `n × n`
Wigner matrix. -/
private def entryIndex {n : ℕ} (i j : Fin n) :
    {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} :=
  if h : i.val < j.val then .inl ⟨⟨(i, j), h⟩, j.isLt⟩
  else if h' : j.val < i.val then .inl ⟨⟨(j, i), h'⟩, i.isLt⟩
  else .inr ⟨i, i.isLt⟩

/-- Two entries read the same coordinate of the corner array exactly when they sit at the same
unordered position. -/
private theorem entryIndex_eq_entryIndex_iff {n : ℕ} {i j i' j' : Fin n} :
    entryIndex i j = entryIndex i' j' ↔ s(i, j) = s(i', j') := by
  unfold entryIndex
  split_ifs <;> simp [Fin.ext_iff] <;> omega

/-- The `(i, j)` entry of a Wigner matrix, up to the factor `1/√n`, as a function of the
coordinate of the array it reads: the coordinate itself above the diagonal, its conjugate below
it, and its real part on it. -/
private def orientEntry {n : ℕ} (i j : Fin n) (z : ℂ) : ℂ :=
  if i.val < j.val then z else if j.val < i.val then star z else (z.re : ℂ)

private theorem measurable_orientEntry {n : ℕ} (i j : Fin n) : Measurable (orientEntry i j) := by
  unfold orientEntry
  split_ifs
  · exact measurable_id
  · exact continuous_star.measurable
  · exact Complex.measurable_ofReal.comp Complex.measurable_re

omit [MeasurableSpace Ω] in
private theorem wignerMatrix_apply_eq_orientEntry {n : ℕ} (ω : Ω) (i j : Fin n) :
    wignerMatrix ξ η n ω i j = (Real.sqrt n : ℂ)⁻¹ *
      orientEntry i j
        (Sum.elim (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val)
          (fun i : {i : ℕ // i < n} ↦ fun ω ↦ (η i.val ω : ℂ)) (entryIndex i j) ω) := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [orientEntry, entryIndex, h]
  · obtain rfl := Fin.ext h
    simp [orientEntry, entryIndex]
  · simp [orientEntry, entryIndex, h, h.not_gt]

/-- The coordinates of the `n × n` corner entry array are almost everywhere measurable. -/
private theorem aemeasurable_cornerEntry {n : ℕ}
    (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEMeasurable (η i) P)
    (r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n}) :
    AEMeasurable (Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P := by
  cases r with
  | inl ij => exact hξm ij.val ij.property
  | inr i => exact Complex.measurable_ofReal.comp_aemeasurable (hηm i.val i.property)

/-- **Edge-disjoint Wigner products are independent.** Let the entries in the `n × n` corner be
independent. Two finite products of entries of the `n × n` Wigner matrix reading disjoint sets of
unordered positions are independent. No centering or finite-moment assumption is required. -/
theorem indepFun_prod_wignerMatrix_apply_of_disjoint {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {n : ℕ} (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n)
    (hdisj : ∀ s t, s(u₁ s, v₁ s) ≠ s(u₂ t, v₂ t)) :
    IndepFun
      (fun ω ↦ ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s))
      (fun ω ↦ ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) P := by
  refine (hindep.indepFun_fun_prod_comp_of_disjoint (aemeasurable_cornerEntry hξm hηm)
    (e₁ := fun s ↦ entryIndex (u₁ s) (v₁ s)) (e₂ := fun t ↦ entryIndex (u₂ t) (v₂ t))
    (fun s t h ↦ hdisj s t (entryIndex_eq_entryIndex_iff.mp h))
    (g₁ := fun s z ↦ (Real.sqrt n : ℂ)⁻¹ * orientEntry (u₁ s) (v₁ s) z)
    (g₂ := fun t z ↦ (Real.sqrt n : ℂ)⁻¹ * orientEntry (u₂ t) (v₂ t) z)
    (fun _ ↦ measurable_const.mul (measurable_orientEntry _ _))
    (fun _ ↦ measurable_const.mul (measurable_orientEntry _ _))).congr ?_ ?_ <;>
  exact .of_forall fun ω ↦ by simp only [wignerMatrix_apply_eq_orientEntry]

/-- **Factorization of edge-disjoint Wigner products.** Let the entries in the `n × n` corner be
independent. When two finite products of entries of the `n × n` Wigner matrix read disjoint sets of
unordered positions, the integral of their product equals the product of their integrals. -/
theorem integral_prod_mul_prod_wignerMatrix_apply_of_disjoint {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] {n : ℕ}
    (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n)
    (hdisj : ∀ s t, s(u₁ s, v₁ s) ≠ s(u₂ t, v₂ t)) :
    ∫ ω, (∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s)) *
        (∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) ∂P =
      (∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P := by
  have hW := aemeasurable_wignerMatrix hξm hηm
  exact (indepFun_prod_wignerMatrix_apply_of_disjoint hξm hηm hindep u₁ v₁ u₂ v₂
    hdisj).integral_fun_mul_eq_mul_integral
    (Finset.aestronglyMeasurable_fun_prod Finset.univ fun s _ ↦
      ((Matrix.measurable_apply (i := u₁ s) (j := v₁ s)).comp_aemeasurable hW).aestronglyMeasurable)
    (Finset.aestronglyMeasurable_fun_prod Finset.univ fun t _ ↦
      ((Matrix.measurable_apply (i := u₂ t) (j := v₂ t)).comp_aemeasurable hW).aestronglyMeasurable)

/-- **Singleton edges vanish.** Let the entries in the `n × n` corner be independent and centred.
For a finite family of positions `(u s, v s)`, if the unordered position `s(u t, v t)` is read by
no other member of the family, then the product of the corresponding entries of the `n × n` Wigner
matrix has expectation zero. -/
theorem integral_prod_wignerMatrix_apply_eq_zero {ι : Type*} [Fintype ι] {n : ℕ}
    (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hη : ∀ i < n, ∫ ω, η i ω ∂P = 0) (u v : ι → Fin n)
    {t : ι} (ht : ∀ s, s(u s, v s) = s(u t, v t) → s = t) :
    ∫ ω, ∏ s, wignerMatrix ξ η n ω (u s) (v s) ∂P = 0 := by
  have h := hindep.integral_fun_prod_comp_eq_zero (aemeasurable_cornerEntry hξm hηm)
    (e := fun s ↦ entryIndex (u s) (v s))
    (g := fun s z ↦ (Real.sqrt n : ℂ)⁻¹ * orientEntry (u s) (v s) z)
    (fun _ ↦ measurable_const.mul (measurable_orientEntry _ _)) (t := t)
    (fun s hs ↦ ht s (entryIndex_eq_entryIndex_iff.mp hs)) (by
      simpa only [wignerMatrix_apply_eq_orientEntry] using
        integral_wignerMatrix_apply_eq_zero (P := P) hξ hη (u t) (v t))
  simpa only [wignerMatrix_apply_eq_orientEntry] using h

/-- **Trace-word expansion of Wigner moments.** Let the entries in the `n × n` corner be
independent, centred and in `Lᵏ`, `k ≠ 0`. Then the expected trace of `Hₙᵏ` is the sum, over the
closed walks `w : Fin k → Fin n` that traverse each of their edges `s(w t, w (t + 1))` at least
twice, of the expected product of the entries of `Hₙ` along the walk: the closed walks with an edge
traversed exactly once contribute zero. -/
theorem integral_trace_pow_wignerMatrix {k n : ℕ} (hk : k ≠ 0)
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hη : ∀ i < n, ∫ ω, η i ω ∂P = 0)
    (hξk : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) k P)
    (hηk : ∀ i < n, MemLp (η i) k P) :
    ∫ ω, (wignerMatrix ξ η n ω ^ k).trace ∂P =
      ∑ w : Fin k → Fin n with
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate k s)) = s(w t, w (finRotate k t)),
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t)) ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  simp_rw [trace_pow_eq_sum_prod _ hk]
  rw [integral_finsetSum _ fun w _ ↦ integrable_prod_wignerMatrix_apply
    (fun ij hij ↦ by simpa using hξk ij hij) (fun i hi ↦ by simpa using hηk i hi) _ _]
  refine (Finset.sum_filter_of_ne fun w _ hw t ↦ ?_).symm
  by_contra! h
  exact hw (integral_prod_wignerMatrix_apply_eq_zero
    (fun ij hij ↦ (hξk ij hij).aestronglyMeasurable.aemeasurable)
    (fun i hi ↦ (hηk i hi).aestronglyMeasurable.aemeasurable) hindep hξ hη _ _
    fun s hs ↦ by_contra fun hst ↦ h s hst hs)

end SingleEdge

end TauCeti

open MeasureTheory ProbabilityTheory Matrix Finset
open TauCeti.TreeWalk

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {m n : ℕ}

private abbrev DiscoverySteps (v : Fin (2 * m + 1) → Fin n) :=
  ↥({i : Fin (2 * m) | canonicalWalk v i.succ = i.succ} : Finset _)

private noncomputable def discoveryFactor (v : Fin (2 * m + 1) → Fin n)
    (i : DiscoverySteps v) (ω : Ω) : ℝ :=
  ‖wignerMatrix ξ η n ω (v i.val.castSucc) (v i.val.succ)‖ ^ 2

private theorem indep_discoveryFactor (v : Fin (2 * m + 1) → Fin n)
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P) :
    iIndepFun (discoveryFactor (ξ := ξ) (η := η) v) P :=
  iIndepFun_norm_wignerMatrix_apply_sq_of_ne _ _
    (fun i ↦ ne_of_canonicalWalk_succ_eq v i.val (mem_filter.mp i.property).2)
    (fun i j hij ↦ Subtype.ext (injOn_edge_setOf_canonicalWalk_succ_eq v
      (mem_filter.mp i.property).2 (mem_filter.mp j.property).2 hij)) hindep

private theorem integrable_discoveryFactor (v : Fin (2 * m + 1) → Fin n)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (i : DiscoverySteps v) :
    Integrable (discoveryFactor (ξ := ξ) (η := η) v i) P := by
  unfold discoveryFactor
  have hne := ne_of_canonicalWalk_succ_eq v i.val (mem_filter.mp i.property).2
  simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hne]
  exact (hξ _ (max_lt (v i.val.castSucc).isLt (v i.val.succ).isLt)).const_mul _

omit [MeasurableSpace Ω] in
private theorem prod_path_eq_prod_discoveryFactor (v : Fin (2 * m + 1) → Fin n)
    (hclosed : v (Fin.last (2 * m)) = v 0) (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2)
    (ω : Ω) :
    ∏ i : Fin (2 * m), wignerMatrix ξ η n ω (v i.castSucc) (v i.succ) =
      ((∏ i : DiscoverySteps v, discoveryFactor (ξ := ξ) (η := η) v i ω : ℝ) : ℂ) := by
  rw [prod_path_eq_prod_up_mul_reverse v hclosed hv he
    (fun i j ↦ wignerMatrix ξ η n ω i j)]
  unfold discoveryFactor DiscoverySteps
  rw [Complex.ofReal_prod, Finset.prod_coe_sort _
    (fun i : Fin (2 * m) ↦ ((‖wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)‖ ^ 2 : ℝ) : ℂ))]
  apply prod_congr rfl
  intro i _
  rw [← (wignerMatrix_isHermitian ξ η ω n).apply (v i.succ) (v i.castSucc)]
  rw [Complex.ofReal_pow]
  exact Complex.mul_conj' _

/-- A double-traversal tree word is integrable when the upper entries in the `n × n` corner are
independent and their squared absolute values are integrable. The diagonal entries may be
arbitrary. -/
theorem integrable_prod_wignerMatrix_apply_path
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (v : Fin (2 * m + 1) → Fin n) (hclosed : v (Fin.last (2 * m)) = v 0)
    (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    Integrable (fun ω ↦ ∏ i : Fin (2 * m),
      wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)) P := by
  have hint := (indep_discoveryFactor (η := η) v hindep).integrable_fun_prod
    (integrable_discoveryFactor v hξ)
  exact hint.ofReal.congr (.of_forall fun ω ↦
    (prod_path_eq_prod_discoveryFactor v hclosed hv he ω).symm)

/-- The expected product along a double-traversal tree path is the product of the second
absolute moments at its discovery steps whenever the upper entries in the `n × n` corner are
independent and have almost-everywhere strongly measurable squared norms. No centering, identical
distribution, or diagonal assumption is needed. -/
theorem integral_prod_wignerMatrix_apply_path
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (v : Fin (2 * m + 1) → Fin n) (hclosed : v (Fin.last (2 * m)) = v 0)
    (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    ∫ ω, ∏ i : Fin (2 * m), wignerMatrix ξ η n ω (v i.castSucc) (v i.succ) ∂P =
      ((∏ i : Fin (2 * m) with canonicalWalk v i.succ = i.succ,
        ∫ ω, ‖wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)‖ ^ 2 ∂P : ℝ) : ℂ) := by
  rw [integral_congr_ae (.of_forall (prod_path_eq_prod_discoveryFactor v hclosed hv he)),
    integral_complex_ofReal]
  rw [(indep_discoveryFactor (η := η) v hindep).integral_fun_prod_eq_prod_integral
    (fun i ↦ by
      unfold discoveryFactor
      have hne := ne_of_canonicalWalk_succ_eq v i.val (mem_filter.mp i.property).2
      simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hne]
      exact (hξ _ (max_lt (v i.val.castSucc).isLt (v i.val.succ).isLt)).const_mul _)]
  unfold discoveryFactor DiscoverySteps
  rw [Finset.prod_coe_sort _ (fun i : Fin (2 * m) ↦
    ∫ ω, ‖wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)‖ ^ 2 ∂P)]

/-- Along any closed double-traversal tree path `v : Fin (2 * m + 1) → Fin n`, the expected product
of Wigner entries equals `((n : ℂ)⁻¹ * s) ^ m` whenever the strictly upper coordinates `ξ` in the
`n × n` corner are independent, have almost-everywhere strongly measurable squared norms, and have
common second absolute moment `s`. The zero-step path (`m = 0`) contributes `1`, and neither
centering nor any assumption on the diagonal entries `η` is needed. -/
theorem integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq {s : ℝ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hξindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hξsq : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s)
    (v : Fin (2 * m + 1) → Fin n) (hclosed : v (Fin.last (2 * m)) = v 0)
    (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    ∫ ω, ∏ i : Fin (2 * m), wignerMatrix ξ η n ω (v i.castSucc) (v i.succ) ∂P =
      ((n : ℂ)⁻¹ * s) ^ m := by
  rw [integral_prod_wignerMatrix_apply_path (η := η) hξ hξindep v hclosed hv he]
  have hterm (i : Fin (2 * m)) (hi : i ∈
      ({i : Fin (2 * m) | canonicalWalk v i.succ = i.succ} : Finset _)) :
      ∫ ω, ‖wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)‖ ^ 2 ∂P = (n : ℝ)⁻¹ * s := by
    have hne := ne_of_canonicalWalk_succ_eq v i (mem_filter.mp hi).2
    simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hne, integral_const_mul]
    rw [hξsq _ (max_lt (v i.castSucc).isLt (v i.succ).isLt)]
  rw [prod_congr rfl hterm, prod_const, card_filter_canonicalWalk_succ_eq, hv,
    Nat.add_sub_cancel]
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- With independent upper entries in the `n × n` corner having unit second absolute moments, every
double-traversal tree path of length `2 * m` has expected entry product `n⁻ᵐ`. The zero-step path
contributes `1`. -/
theorem integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq_one
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hsecond : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (v : Fin (2 * m + 1) → Fin n) (hclosed : v (Fin.last (2 * m)) = v 0)
    (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    ∫ ω, ∏ i : Fin (2 * m), wignerMatrix ξ η n ω (v i.castSucc) (v i.succ) ∂P =
      (n : ℂ)⁻¹ ^ m := by
  simpa using integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq (η := η)
    (fun ij hij ↦ (integrable_of_integral_eq_one (hsecond ij hij)).aestronglyMeasurable)
    hindep hsecond v hclosed hv he

/-- A leading cyclic Wigner word is integrable when the upper entries in the `n × n` corner are
independent and their squared absolute values are integrable. The diagonal entries may be
arbitrary. -/
theorem integrable_prod_wignerMatrix_apply_leading
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (w : Fin (2 * m) → Fin n)
    (h : ∀ i, ∃ j ≠ i,
      s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    Integrable (fun ω ↦ ∏ i,
      wignerMatrix ξ η n ω (w i) (w (finRotate (2 * m) i))) P := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hv
  have := NeZero.mk hm
  have hp := integrable_prod_wignerMatrix_apply_path
    (η := η) hξ hindep (cyclicPath w) (by simp) (by simpa using hv)
    (card_edge_fiber_cyclicPath w h hv)
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using hp

/-- The expected product along a leading cyclic Wigner word is the product of the second
absolute moments at its discovery steps. Only measurability of the squared upper entries and
independence in the `n × n` corner are required; the diagonal entries may be arbitrary. -/
theorem integral_prod_wignerMatrix_apply_leading [NeZero m]
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (w : Fin (2 * m) → Fin n)
    (h : ∀ i, ∃ j ≠ i,
      s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    ∫ ω, ∏ i, wignerMatrix ξ η n ω (w i) (w (finRotate (2 * m) i)) ∂P =
      ((∏ i : Fin (2 * m) with canonicalWalk (cyclicPath w) i.succ = i.succ,
        ∫ ω, ‖wignerMatrix ξ η n ω (w i) (w (finRotate (2 * m) i))‖ ^ 2 ∂P : ℝ) : ℂ) := by
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using
    integral_prod_wignerMatrix_apply_path (η := η) hξ hindep (cyclicPath w)
      (by simp) (by simpa using hv) (card_edge_fiber_cyclicPath w h hv)

/-- Along any leading cyclic word `w : Fin (2 * m) → Fin n`, the expected product of Wigner entries
equals `((n : ℂ)⁻¹ * s) ^ m` whenever the strictly upper coordinates `ξ` in the `n × n` corner are
independent, have almost-everywhere strongly measurable squared norms, and have common second
absolute moment `s`. Neither centering nor any assumption on the diagonal entries `η` is needed,
because leading words have no self-loops. -/
theorem integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq {s : ℝ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hξindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hξsq : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s)
    (w : Fin (2 * m) → Fin n)
    (h : ∀ t, ∃ r ≠ t, s(w r, w (finRotate (2 * m) r)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) :
    ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P =
      ((n : ℂ)⁻¹ * s) ^ m := by
  have : NeZero m := ⟨by rintro rfl; simp at hv⟩
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using
    integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq (η := η) hξ hξindep hξsq
      (cyclicPath w) (by simp) (by simpa using hv) (card_edge_fiber_cyclicPath w h hv)

/-- **Leading Wigner words.** A cyclic word of length `2 * m`, with no singleton unordered
edge and `m + 1` distinct vertices, contributes exactly `n⁻ᵐ` to the expected trace.
Only independence and unit second absolute moments of the upper entries in the `n × n` corner are
required; centering, higher moments, and all conditions on the diagonal are unnecessary here. -/
theorem integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P)
    (hsecond : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (w : Fin (2 * m) → Fin n)
    (h : ∀ i, ∃ j ≠ i,
      s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    ∫ ω, ∏ i, wignerMatrix ξ η n ω (w i) (w (finRotate (2 * m) i)) ∂P =
      (n : ℂ)⁻¹ ^ m := by
  simpa using integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq (η := η)
    (fun ij hij ↦ (integrable_of_integral_eq_one (hsecond ij hij)).aestronglyMeasurable)
    hindep hsecond w h hv

end TauCeti
