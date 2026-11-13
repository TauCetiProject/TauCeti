/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Integration
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

## Main results

* `TauCeti.integral_prod_wignerMatrix_apply_eq_zero`: for independent centred entries, a product
  of entries reading some edge exactly once has expectation zero.
* `TauCeti.integral_trace_pow_wignerMatrix`: for independent centred entries in `Lᵏ`, the
  expected trace of `Hₙᵏ` is the sum, over the closed walks of length `k` traversing each of
  their edges at least twice, of the expected products of entries along the walk.

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

/-- The coordinate of the entry array `StrictUpper ⊕ ℕ` read by the `(i, j)` entry of a Wigner
matrix. -/
private def entryIndex {n : ℕ} (i j : Fin n) : StrictUpper ⊕ ℕ :=
  if h : i.val < j.val then .inl ⟨(i, j), h⟩
  else if h' : j.val < i.val then .inl ⟨(j, i), h'⟩ else .inr i

/-- Two entries read the same coordinate of the array exactly when they sit at the same unordered
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
      orientEntry i j (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (entryIndex i j) ω) := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [orientEntry, entryIndex, h]
  · obtain rfl := Fin.ext h
    simp [orientEntry, entryIndex]
  · simp [orientEntry, entryIndex, h, h.not_gt]

/-- **Singleton edges vanish.** Let the entries of the array be independent and centred. For a
finite family of positions `(u s, v s)`, if the unordered position `s(u t, v t)` is read by no
other member of the family, then the product of the corresponding entries of the Wigner matrix
has expectation zero. -/
theorem integral_prod_wignerMatrix_apply_eq_zero {ι : Type*} [Fintype ι]
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξ : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hη : ∀ i, ∫ ω, η i ω ∂P = 0) {n : ℕ} (u v : ι → Fin n)
    {t : ι} (ht : ∀ s, s(u s, v s) = s(u t, v t) → s = t) :
    ∫ ω, ∏ s, wignerMatrix ξ η n ω (u s) (v s) ∂P = 0 := by
  classical
  set X : StrictUpper ⊕ ℕ → Ω → ℂ := fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k
  set e : ι → StrictUpper ⊕ ℕ := fun s ↦ entryIndex (u s) (v s)
  set c : ℂ := (Real.sqrt n : ℂ)⁻¹
  have hX (k : StrictUpper ⊕ ℕ) : AEMeasurable (X k) P := aemeasurable_sumElim_ofReal hξm hηm k
  -- The coordinate read at step `t` and the coordinates read at the other steps.
  set S : Finset (StrictUpper ⊕ ℕ) := {e t}
  set T : Finset (StrictUpper ⊕ ℕ) := (Finset.univ.erase t).image e
  have hST : Disjoint S T := by
    refine Finset.disjoint_singleton_left.2 fun hmem ↦ ?_
    obtain ⟨s, hs, hes⟩ := Finset.mem_image.1 hmem
    exact (Finset.mem_erase.1 hs).1 (ht s (entryIndex_eq_entryIndex_iff.1 hes))
  -- The entry at step `t` and the product of the other entries, as functions of these coordinates.
  set φ : (S → ℂ) → ℂ := fun g ↦ c * orientEntry (u t) (v t) (g ⟨e t, Finset.mem_singleton_self _⟩)
  set ψ : (T → ℂ) → ℂ := fun g ↦ ∏ s ∈ (Finset.univ.erase t).attach,
    c * orientEntry (u s) (v s) (g ⟨e s, Finset.mem_image_of_mem e s.2⟩)
  have hφ : Measurable φ :=
    measurable_const.mul ((measurable_orientEntry _ _).comp (measurable_pi_apply _))
  have hψ : Measurable ψ := Finset.measurable_prod _ fun s _ ↦
    measurable_const.mul ((measurable_orientEntry _ _).comp (measurable_pi_apply _))
  have hXS : AEMeasurable (fun ω (k : S) ↦ X k ω) P := aemeasurable_pi_iff.2 fun k ↦ hX k
  have hXT : AEMeasurable (fun ω (k : T) ↦ X k ω) P := aemeasurable_pi_iff.2 fun k ↦ hX k
  have hind := (hindep.indepFun_finset₀ S T hST hX).comp hφ hψ
  have hsplit (ω : Ω) : ∏ s, wignerMatrix ξ η n ω (u s) (v s) =
      φ (fun k : S ↦ X k ω) * ψ (fun k : T ↦ X k ω) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), ← Finset.prod_attach (Finset.univ.erase t)]
    simp only [wignerMatrix_apply_eq_orientEntry, φ, ψ, X, e, c]
  have hφt : ∫ ω, φ (fun k : S ↦ X k ω) ∂P = 0 := by
    rw [← integral_wignerMatrix_apply_eq_zero (P := P) hξ hη (u t) (v t)]
    simp only [wignerMatrix_apply_eq_orientEntry, φ, X, e, c]
  simp_rw [hsplit]
  have hmul := hind.integral_fun_mul_eq_mul_integral
    (hφ.comp_aemeasurable hXS).aestronglyMeasurable (hψ.comp_aemeasurable hXT).aestronglyMeasurable
  simp only [Function.comp_apply] at hmul
  rw [hmul, hφt, zero_mul]

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
