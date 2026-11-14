/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.Independence.Integration
public import TauCeti.Combinatorics.TreeWalk.Product
public import TauCeti.LinearAlgebra.Matrix.Trace.Pow
public import TauCeti.Probability.RandomMatrix.Wigner

/-!
# Trace words of Wigner matrices

The moment method for the semicircle law expands the expected moment `E trace Hₙᵏ` of a Wigner
matrix `Hₙ` into a sum over closed walks `w : Fin k → Fin n` of the expectations of the products
`∏ₜ Hₙ (w t) (w (t + 1))` of the entries read along the walk (`Matrix.trace_pow_eq_sum_prod`).
Each step `w t → w (t + 1)` reads the entry at the unordered position `s(w t, w (t + 1))`, its
*edge*; a loop `w t = w (t + 1)` reads a diagonal entry.

When the entries are independent and centred, a product of entries in which some edge is read
exactly once has expectation zero: that entry is independent of all the others and has mean
zero. Consequently only the closed walks traversing each of their edges at least twice contribute
to the expected moment. This is the first reduction of the trace-word expansion; the remaining
walks are then classified by their numbers of vertices and distinct edges.

For a leading word of length `2 * m`, the maximal `m + 1` visited vertices force a
double-traversal tree. Pairing each discovery with its reverse reduces the entry product
to independent squared absolute values. Unit off-diagonal second moments then give exactly
`n⁻ᵐ`, without centering, higher moments, or any assumptions on the diagonal entries.
The path formulation includes the zero-step case and proves integrability first.

## Main results

* `TauCeti.integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral`: products of Wigner entries
  over two finite families with disjoint unordered edge sets factor in expectation.
* `TauCeti.integral_prod_wignerMatrix_apply_eq_zero_of_lt` and
  `TauCeti.integral_prod_wignerMatrix_apply_eq_zero`: for independent centred entries, a product
  of entries reading some edge exactly once has expectation zero.
* `TauCeti.integral_trace_pow_wignerMatrix`: for independent centred entries in `Lᵏ`, the
  expected trace of `Hₙᵏ` is the sum, over the closed walks of length `k` traversing each of
  their edges at least twice, of the expected products of entries along the walk.

* `TauCeti.integrable_prod_wignerMatrix_apply_path` and
  `TauCeti.integral_prod_wignerMatrix_apply_path`: integrability and a second-moment product
  formula for double-traversal tree paths.
* `TauCeti.integral_prod_wignerMatrix_apply_leading`: a second-moment product formula for
  leading cyclic Wigner words.
* `TauCeti.integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one`: every leading
  cyclic Wigner word contributes `n⁻ᵐ` under independence and unit off-diagonal second moments.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

section SingleEdge

/-- The coordinate of the top-left `n × n` corner `Fin n ⊕ FinStrictUpper n` read by the `(i, j)`
entry of a Wigner matrix. -/
private def entryIndex {n : ℕ} (i j : Fin n) : Fin n ⊕ FinStrictUpper n :=
  if h : i.val < j.val then .inr ⟨(i, j), h⟩
  else if h' : j.val < i.val then .inr ⟨(j, i), h'⟩ else .inl i

/-- Two entries read the same corner coordinate exactly when they sit at the same unordered
position. -/
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
        (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n (entryIndex i j)) ω) := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [orientEntry, entryIndex, h]
  · obtain rfl := Fin.ext h
    simp [orientEntry, entryIndex]
  · simp [orientEntry, entryIndex, h, h.not_gt]

private theorem aemeasurable_wignerCoordinate {n : ℕ}
    (hξ : ∀ ij, ij.1.2 < n → AEMeasurable (ξ ij) P)
    (hη : ∀ i, i < n → AEMeasurable (η i) P) (k : Fin n ⊕ FinStrictUpper n) :
    AEMeasurable (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)) P := by
  cases k with
  | inl i =>
    simp only [wignerCoordinateIndex_inl, Sum.elim_inr]
    exact Complex.measurable_ofReal.comp_aemeasurable (hη i.val i.2)
  | inr p =>
    simp only [wignerCoordinateIndex_inr, Sum.elim_inl]
    exact hξ ⟨(p.1.1.val, p.1.2.val), p.2⟩ p.1.2.2

/-- Products of Wigner matrix entries over two finite index families whose unordered edge sets are
disjoint are independent whenever the corner entries are independent, so the expectation of their
product factors. -/
theorem integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {n : ℕ}
    (hξm : ∀ ij, ij.1.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i, i < n → AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)) P)
    (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n)
    (hdisj : ∀ s t, s(u₁ s, v₁ s) ≠ s(u₂ t, v₂ t)) :
    ∫ ω, (∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s)) *
        (∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) ∂P =
      (∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
        (∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P) := by
  classical
  let X (k : Fin n ⊕ FinStrictUpper n) : Ω → ℂ :=
    Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)
  let e₁ : ι₁ → Fin n ⊕ FinStrictUpper n := fun s ↦ entryIndex (u₁ s) (v₁ s)
  let e₂ : ι₂ → Fin n ⊕ FinStrictUpper n := fun t ↦ entryIndex (u₂ t) (v₂ t)
  let S₁ : Finset (Fin n ⊕ FinStrictUpper n) := Finset.univ.image e₁
  let S₂ : Finset (Fin n ⊕ FinStrictUpper n) := Finset.univ.image e₂
  have hS₁₂ : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro k hk₁ hk₂
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hk₁
    obtain ⟨t, -, het⟩ := Finset.mem_image.mp hk₂
    exact hdisj s t (entryIndex_eq_entryIndex_iff.mp het.symm)
  have hX (k : Fin n ⊕ FinStrictUpper n) : AEMeasurable (X k) P :=
    aemeasurable_wignerCoordinate hξm hηm k
  let c : ℂ := (Real.sqrt n : ℂ)⁻¹
  let φ₁ : (S₁ → ℂ) → ℂ := fun g ↦ ∏ s : ι₁,
    c * orientEntry (u₁ s) (v₁ s) (g ⟨e₁ s, Finset.mem_image_of_mem e₁ (Finset.mem_univ s)⟩)
  let φ₂ : (S₂ → ℂ) → ℂ := fun g ↦ ∏ t : ι₂,
    c * orientEntry (u₂ t) (v₂ t) (g ⟨e₂ t, Finset.mem_image_of_mem e₂ (Finset.mem_univ t)⟩)
  have hφ₁ : Measurable φ₁ := Finset.measurable_prod _ fun s _ ↦
    measurable_const.mul ((measurable_orientEntry _ _).comp (measurable_pi_apply _))
  have hφ₂ : Measurable φ₂ := Finset.measurable_prod _ fun t _ ↦
    measurable_const.mul ((measurable_orientEntry _ _).comp (measurable_pi_apply _))
  have hXS₁ : AEMeasurable (fun ω (k : S₁) ↦ X k ω) P := aemeasurable_pi_iff.2 fun k ↦ hX k
  have hXS₂ : AEMeasurable (fun ω (k : S₂) ↦ X k ω) P := aemeasurable_pi_iff.2 fun k ↦ hX k
  have hind := (hindep.indepFun_finset₀ S₁ S₂ hS₁₂ hX).comp hφ₁ hφ₂
  have heq₁ (ω : Ω) : (∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s)) = φ₁ (fun k : S₁ ↦ X k ω) := by
    simp only [wignerMatrix_apply_eq_orientEntry, φ₁, X, e₁, c]
  have heq₂ (ω : Ω) : (∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) = φ₂ (fun k : S₂ ↦ X k ω) := by
    simp only [wignerMatrix_apply_eq_orientEntry, φ₂, X, e₂, c]
  simp_rw [heq₁, heq₂]
  have hmul := hind.integral_fun_mul_eq_mul_integral
    (hφ₁.comp_aemeasurable hXS₁).aestronglyMeasurable
    (hφ₂.comp_aemeasurable hXS₂).aestronglyMeasurable
  simpa only [Function.comp_apply] using hmul

/-- **Singleton edges vanish (corner hypotheses).** Let the entries of the `n × n` corner be
independent and centred. For a finite family of positions `(u s, v s)`, if the unordered position
`s(u t, v t)` is read by no other member of the family, then the product of the corresponding
entries of the Wigner matrix has expectation zero. -/
theorem integral_prod_wignerMatrix_apply_eq_zero_of_lt {ι : Type*} [Fintype ι] {n : ℕ}
    (hξm : ∀ ij, ij.1.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i, i < n → AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n k)) P)
    (hξ : ∀ ij, ij.1.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hη : ∀ i, i < n → ∫ ω, η i ω ∂P = 0) (u v : ι → Fin n)
    {t : ι} (ht : ∀ s, s(u s, v s) = s(u t, v t) → s = t) :
    ∫ ω, ∏ s, wignerMatrix ξ η n ω (u s) (v s) ∂P = 0 := by
  classical
  have hsplit (ω : Ω) : ∏ s, wignerMatrix ξ η n ω (u s) (v s) =
      (∏ s : {s : ι // s = t}, wignerMatrix ξ η n ω (u s.1) (v s.1)) *
        (∏ s : {s : ι // s ≠ t}, wignerMatrix ξ η n ω (u s.1) (v s.1)) := by
    convert (Fintype.prod_subtype_mul_prod_subtype (· = t)
      (fun s ↦ wignerMatrix ξ η n ω (u s) (v s))).symm
  simp_rw [hsplit]
  rw [integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral hξm hηm hindep
    (fun s : {s // s = t} ↦ u s.1) (fun s : {s // s = t} ↦ v s.1)
    (fun s : {s // s ≠ t} ↦ u s.1) (fun s : {s // s ≠ t} ↦ v s.1)
    fun s₁ s₂ h ↦ s₂.2 (ht s₂.1 (h.symm.trans (by rw [s₁.2])))]
  have huniq (ω : Ω) :
      (∏ s : {s : ι // s = t}, wignerMatrix ξ η n ω (u s.1) (v s.1)) =
        wignerMatrix ξ η n ω (u t) (v t) :=
    Fintype.prod_unique _
  simp_rw [huniq]
  rw [integral_wignerMatrix_apply_eq_zero_of_lt hξ hη (u t) (v t), zero_mul]

/-- **Singleton edges vanish.** Let the entries of the array be independent and centred. For a
finite family of positions `(u s, v s)`, if the unordered position `s(u t, v t)` is read by no
other member of the family, then the product of the corresponding entries of the Wigner matrix
has expectation zero. -/
theorem integral_prod_wignerMatrix_apply_eq_zero {ι : Type*} [Fintype ι]
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξ : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hη : ∀ i, ∫ ω, η i ω ∂P = 0) {n : ℕ} (u v : ι → Fin n)
    {t : ι} (ht : ∀ s, s(u s, v s) = s(u t, v t) → s = t) :
    ∫ ω, ∏ s, wignerMatrix ξ η n ω (u s) (v s) ∂P = 0 :=
  integral_prod_wignerMatrix_apply_eq_zero_of_lt (fun ij _ ↦ hξm ij) (fun i _ ↦ hηm i)
    (hindep.precomp (wignerCoordinateIndex_injective n)) (fun ij _ ↦ hξ ij) (fun i _ ↦ hη i)
    u v ht

/-- **Trace-word expansion of Wigner moments.** Let the entries of the array be independent,
centred and in `Lᵏ`, `k ≠ 0`. Then the expected trace of `Hₙᵏ` is the sum, over the closed walks
`w : Fin k → Fin n` that traverse each of their edges `s(w t, w (t + 1))` at least twice, of the
expected product of the entries of `Hₙ` along the walk: the closed walks with an edge traversed
exactly once contribute zero. -/
theorem integral_trace_pow_wignerMatrix [IsFiniteMeasure P]
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξ : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hη : ∀ i, ∫ ω, η i ω ∂P = 0) {k : ℕ} (hk : k ≠ 0)
    (hξk : ∀ ij, MemLp (ξ ij) k P) (hηk : ∀ i, MemLp (η i) k P) (n : ℕ) :
    ∫ ω, (wignerMatrix ξ η n ω ^ k).trace ∂P =
      ∑ w : Fin k → Fin n with
        ∀ t, ∃ s ≠ t, s(w s, w (finRotate k s)) = s(w t, w (finRotate k t)),
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t)) ∂P := by
  simp_rw [trace_pow_eq_sum_prod _ hk]
  rw [integral_finsetSum _ fun w _ ↦ integrable_prod_wignerMatrix_apply
    (by simpa using hξk) (by simpa using hηk) _ _]
  refine (Finset.sum_filter_of_ne fun w _ hw t ↦ ?_).symm
  by_contra! h
  exact hw (integral_prod_wignerMatrix_apply_eq_zero
    (fun ij ↦ (hξk ij).aestronglyMeasurable.aemeasurable)
    (fun i ↦ (hηk i).aestronglyMeasurable.aemeasurable) hindep hξ hη _ _
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
    (hindep : iIndepFun ξ P) :
    iIndepFun (discoveryFactor (ξ := ξ) (η := η) v) P :=
  iIndepFun_norm_wignerMatrix_apply_sq_of_ne _ _
    (fun i ↦ ne_of_canonicalWalk_succ_eq v i.val (mem_filter.mp i.property).2)
    (fun i j hij ↦ Subtype.ext (injOn_edge_setOf_canonicalWalk_succ_eq v
      (mem_filter.mp i.property).2 (mem_filter.mp j.property).2 hij)) hindep

private theorem integrable_discoveryFactor (v : Fin (2 * m + 1) → Fin n)
    (hξ : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (i : DiscoverySteps v) :
    Integrable (discoveryFactor (ξ := ξ) (η := η) v i) P := by
  unfold discoveryFactor
  have hne := ne_of_canonicalWalk_succ_eq v i.val (mem_filter.mp i.property).2
  simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hne]
  exact (hξ _).const_mul _

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

/-- A double-traversal tree word is integrable when the upper entries are independent
and their squared absolute values are integrable. The diagonal entries may be arbitrary. -/
theorem integrable_prod_wignerMatrix_apply_path
    (hξ : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hindep : iIndepFun ξ P)
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
absolute moments at its discovery steps. No centering or identical-distribution assumption
is needed. -/
theorem integral_prod_wignerMatrix_apply_path
    (hξ : ∀ ij, AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hindep : iIndepFun ξ P)
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
      exact (hξ _).const_mul _)]
  unfold discoveryFactor DiscoverySteps
  rw [Finset.prod_coe_sort _ (fun i : Fin (2 * m) ↦
    ∫ ω, ‖wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)‖ ^ 2 ∂P)]

/-- With unit off-diagonal second moments, every double-traversal tree path of length
`2 * m` has expected entry product `n⁻ᵐ`. The zero-step path contributes `1`. -/
theorem integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq_one
    (hindep : iIndepFun ξ P)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (v : Fin (2 * m + 1) → Fin n) (hclosed : v (Fin.last (2 * m)) = v 0)
    (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    ∫ ω, ∏ i : Fin (2 * m), wignerMatrix ξ η n ω (v i.castSucc) (v i.succ) ∂P =
      (n : ℂ)⁻¹ ^ m := by
  have hξ (ij : StrictUpper) : AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P :=
    (integrable_of_integral_eq_one (hsecond ij)).aestronglyMeasurable
  rw [integral_prod_wignerMatrix_apply_path hξ hindep v hclosed hv he]
  have hterm (i : Fin (2 * m)) (hi : i ∈
      ({i : Fin (2 * m) | canonicalWalk v i.succ = i.succ} : Finset _)) :
      ∫ ω, ‖wignerMatrix ξ η n ω (v i.castSucc) (v i.succ)‖ ^ 2 ∂P = (n : ℝ)⁻¹ := by
    have hne := ne_of_canonicalWalk_succ_eq v i (mem_filter.mp hi).2
    simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hne, integral_const_mul,
      hsecond, mul_one]
  rw [prod_congr rfl hterm, prod_const, card_filter_canonicalWalk_succ_eq, hv,
    Nat.add_sub_cancel]
  simp only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- A leading cyclic Wigner word is integrable when the upper entries are independent
and their squared absolute values are integrable. The diagonal entries may be arbitrary. -/
theorem integrable_prod_wignerMatrix_apply_leading
    (hξ : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hindep : iIndepFun ξ P)
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
absolute moments at its discovery steps. Only measurability of the squared upper entries
and independence are required; the diagonal entries may be arbitrary. -/
theorem integral_prod_wignerMatrix_apply_leading [NeZero m]
    (hξ : ∀ ij, AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hindep : iIndepFun ξ P)
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

/-- **Leading Wigner words.** A cyclic word of length `2 * m`, with no singleton unordered
edge and `m + 1` distinct vertices, contributes exactly `n⁻ᵐ` to the expected trace.
Only independence and unit second absolute moments of the upper entries are required;
centering, higher moments, and all conditions on the diagonal are unnecessary here. -/
theorem integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one
    (hindep : iIndepFun ξ P)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1) (w : Fin (2 * m) → Fin n)
    (h : ∀ i, ∃ j ≠ i,
      s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    ∫ ω, ∏ i, wignerMatrix ξ η n ω (w i) (w (finRotate (2 * m) i)) ∂P =
      (n : ℂ)⁻¹ ^ m := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hv
  have := NeZero.mk hm
  have hp := integral_prod_wignerMatrix_apply_path_of_integral_norm_sq_eq_one
    (η := η) hindep hsecond (cyclicPath w) (by simp) (by simpa using hv)
    (card_edge_fiber_cyclicPath w h hv)
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using hp

end TauCeti
