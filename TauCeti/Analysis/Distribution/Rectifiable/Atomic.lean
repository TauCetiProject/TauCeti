/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.Integral
import TauCeti.MeasureTheory.Measure.Count.Integrable
import TauCeti.Topology.Codiscrete

/-!
# Integral currents of degree zero are atomic

Let `Ω` be an open subset of a finite-dimensional real inner product space `V`. In degree zero the
normalized Hausdorff measure `μHE[0]` is counting measure, and an integer-rectifiable `0`-current
(`Distribution.IsIntegerRectifiable`) is the sum `ω ↦ ∑ θ(x) ω_x()` of point evaluations weighted
by an integer multiplicity `θ`. Local integrability of `θ` for counting measure forces the points
where `θ ≠ 0` to be finite in every compact subset of `Ω`, and an isolated atom is detected by a
test form supported near it. So the support of the current in `Ω` is exactly the set of its atoms,
which is locally finite in `Ω` (`Distribution.IsIntegerRectifiable.finite_inter_dsupport_finZero`)
but in general infinite when the support is not compact.

When the support is a compact subset of `Ω`, the current is a finite sum
`ω ↦ ∑ x ∈ s, a(x) ω_x()` of point masses with nonzero integer coefficients `a(x)`, over the finite
set `s` equal to its support
(`Distribution.IsIntegerRectifiable.exists_finset_apply_eq_sum_finZero`). Conversely, every finite
integer combination of point masses is integer-rectifiable, so the compactly supported integral
`0`-currents are exactly the finite integer combinations of point masses at points of `Ω`
(`Distribution.isCompactlySupportedIntegralCurrent_finZero_iff`). For a finite set `s ⊆ Ω`, the
augmentation at a `0`-form `c` of a finite combination of point masses at the points of `s` is the
sum of its coefficients times `c ![]` (`Distribution.augmentation_sum_mul_apply_finZero`). So the
augmentation of a compactly supported integral `0`-current at the unit `0`-form is the sum of its
integer coefficients, and its mass is the sum of their absolute values
(`Distribution.mass_sum_mul_apply_finZero`).

## Main declarations

* `Distribution.IsIntegerRectifiable.finite_inter_dsupport_finZero`: the support of an
  integer-rectifiable `0`-current is finite in every compact subset of `Ω`.
* `Distribution.IsIntegerRectifiable.exists_finset_apply_eq_sum_finZero`: an integer-rectifiable
  `0`-current whose support is a compact subset of `Ω` is a finite sum of integer point masses,
  located exactly at the points of its support.
* `Distribution.isIntegerRectifiable_finZero_of_apply_eq_sum`: finite integer combinations of
  point masses are integer-rectifiable.
* `Distribution.isCompactlySupportedIntegralCurrent_finZero_iff`: the compactly supported integral
  `0`-currents are the finite integer combinations of point masses at points of `Ω`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.24 (integral currents).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3 (integer multiplicity
  rectifiable currents).
-/

public section

noncomputable section

open Set Metric TopologicalSpace TestFunction MeasureTheory
open scoped Distributions ENNReal

namespace Distribution

open TauCeti

/-- If `Aᶜ` is codiscrete within an open set `U`, each point `x ∈ U` has a closed ball around it
inside `U` meeting `A` at most in `x`. -/
private theorem exists_closedBall_inter_subset_singleton {X : Type*} [PseudoMetricSpace X]
    {U A : Set X} (hU : IsOpen U) (hA : Aᶜ ∈ Filter.codiscreteWithin U) {x : X} (hx : x ∈ U) :
    ∃ δ > 0, closedBall x δ ⊆ U ∧ closedBall x δ ∩ A ⊆ {x} := by
  obtain ⟨ε, hε, hεA⟩ :=
    Metric.mem_nhdsWithin_iff.1 (hU.sdiff_mem_nhdsNE_of_compl_mem_codiscreteWithin hA hx)
  have hball : closedBall x (ε / 2) ⊆ ball x ε := closedBall_subset_ball (half_lt_self hε)
  refine ⟨ε / 2, half_pos hε, fun y hy ↦ ?_, fun y hy ↦
    by_contra fun hyx ↦ (hεA ⟨hball hy.1, hyx⟩).2 hy.2⟩
  by_cases hyx : y = x
  · exact hyx ▸ hx
  · exact (hεA ⟨hball hy, hyx⟩).1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {n : ℕ∞}

section Multiplicity

variable {θ : V → ℤ}

/-- An integer multiplicity locally integrable on `Ω` for the counting measure `μHE[0]` is nonzero
at only finitely many points of each compact subset of `Ω`. -/
private theorem finite_inter_setOf_ne_zero (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0])
    {K : Set V} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (K ∩ {x | θ x ≠ 0}).Finite := by
  have hint := hθ.integrableOn_compact_subset hKΩ hK
  rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_count] at hint
  exact hint.finite_inter_support_of_count

/-- The points of `Ω` where a locally integrable integer multiplicity is nonzero are isolated: each
point of `Ω` has a closed ball around it inside `Ω` containing no other such point. -/
private theorem exists_closedBall_inter_setOf_ne_zero_subset
    (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0]) {x : V} (hx : x ∈ Ω) :
    ∃ δ > 0, closedBall x δ ⊆ Ω ∧ closedBall x δ ∩ {y | θ y ≠ 0} ⊆ {x} :=
  exists_closedBall_inter_subset_singleton Ω.isOpen
    (Ω.isOpen.compl_mem_codiscreteWithin_iff_forall_finite_inter.2 fun _ hK hKΩ ↦
      finite_inter_setOf_ne_zero hθ hK hKΩ) hx

variable {τ : V → Fin 0 → V} (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0])
include hθ

/-- A test `0`-form `ω` pairs with the frame current of an integer multiplicity `θ` as the finite
sum `∑ x ∈ s, θ(x) ω_x()` over any finite set `s` containing the points of `tsupport ω` where
`θ ≠ 0`. The empty frames `τ x` are automatically measurable and orthonormal. -/
private theorem frameCurrent_finZero_apply_eq_sum (ω : 𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ))
    {s : Finset V} (hs : tsupport ω ∩ {x | θ x ≠ 0} ⊆ s) :
    frameCurrent (fun x ↦ (θ x : ℝ)) τ ω = ∑ x ∈ s, (θ x : ℝ) * ω x ![] := by
  have hτ : Measurable τ := measurable_of_subsingleton_codomain τ
  have hτo (x : V) (_ : (θ x : ℝ) ≠ 0) : Orthonormal ℝ (τ x) := .of_isEmpty _
  have hint := integrable_frameCurrent_integrand hθ hτ hτo ω
  rw [frameCurrent_apply hθ hτ hτo]
  rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_count] at hint ⊢
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (s : Set V)) fun x hx ↦ ?_,
    setIntegral_finset s hint.integrableOn]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [Subsingleton.elim (τ x) ![]]
  · by_cases hθx : θ x = 0
    · simp [hθx]
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs ⟨h, hθx⟩)]

/-- The support in `Ω` of the frame current of an integer multiplicity `θ` in degree zero is the
set of points of `Ω` where `θ ≠ 0`. -/
private theorem inter_dsupport_frameCurrent_finZero :
    (Ω : Set V) ∩ dsupport (frameCurrent (fun x ↦ (θ x : ℝ)) τ :
      𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) = (Ω : Set V) ∩ {x | θ x ≠ 0} := by
  set T : 𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ := frameCurrent (fun x ↦ (θ x : ℝ)) τ
  refine subset_antisymm ?_ ?_
  · rintro x ⟨hxΩ, hxT⟩
    refine ⟨hxΩ, fun hθx ↦ ?_⟩
    -- Near a point `x` with `θ x = 0` there is no atom, so `T` vanishes there.
    obtain ⟨δ, hδ, -, hδθ⟩ := exists_closedBall_inter_setOf_ne_zero_subset hθ hxΩ
    have hvan : IsVanishingOn T (ball x δ) := fun ω hω ↦ by
      rw [frameCurrent_finZero_apply_eq_sum hθ ω (s := ∅) fun y hy ↦ ?_, Finset.sum_empty]
      obtain rfl : y = x := hδθ ⟨ball_subset_closedBall (hω hy.1), hy.2⟩
      exact (hy.2 hθx).elim
    exact (hvan.disjoint_dsupport isOpen_ball).ne_of_mem (mem_ball_self hδ) hxT rfl
  · rintro x ⟨hxΩ, hθx⟩
    refine ⟨hxΩ, by_contra fun hxT ↦ ?_⟩
    -- A test form equal to the unit `0`-form at an isolated atom `x`, supported away from the
    -- support of `T`, would be sent both to `θ x` and to zero.
    obtain ⟨δ, hδ, hδΩ, hδθ⟩ := exists_closedBall_inter_setOf_ne_zero_subset hθ hxΩ
    obtain ⟨ω, hωU, hωx⟩ := exists_tsupport_subset_apply_eq (n := n)
      ((isOpen_ball.inter isClosed_dsupport.isOpen_compl).mem_nhds ⟨mem_ball_self hδ, hxT⟩)
      (inter_subset_left.trans (ball_subset_closedBall.trans hδΩ))
      (ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (1 : ℝ))
    have h0 : T ω = 0 := map_eq_zero_of_disjoint_dsupport T
      (subset_compl_iff_disjoint_right.1 (hωU.trans inter_subset_right))
    have h1 : T ω = θ x := by
      rw [frameCurrent_finZero_apply_eq_sum hθ ω (s := {x}) fun y hy ↦ by
        simpa using hδθ ⟨ball_subset_closedBall (hωU hy.1).1, hy.2⟩]
      simp [hωx]
    exact hθx (by exact_mod_cast h1.symm.trans h0)

end Multiplicity

section IntegerRectifiable

variable {T : 𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- **Integer-rectifiable `0`-currents have locally finite support.** The support of an
integer-rectifiable `0`-current meets each compact subset of `Ω` in a finite set. -/
theorem IsIntegerRectifiable.finite_inter_dsupport_finZero (hT : IsIntegerRectifiable T)
    {K : Set V} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (K ∩ dsupport T).Finite := by
  obtain ⟨θ, τ, -, -, -, hθ, -, -, rfl⟩ := isIntegerRectifiable_iff.1 hT
  refine (finite_inter_setOf_ne_zero hθ hK hKΩ).subset fun x ⟨hxK, hxT⟩ ↦ ⟨hxK, ?_⟩
  have hx : x ∈ (Ω : Set V) ∩ dsupport (frameCurrent (fun x ↦ (θ x : ℝ)) τ :
      𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) := ⟨hKΩ hxK, hxT⟩
  rw [inter_dsupport_frameCurrent_finZero hθ] at hx
  exact hx.2

/-- **Compactly supported integer-rectifiable `0`-currents are finite sums of integer point
masses.** If the support of an integer-rectifiable `0`-current `T` is a compact subset of `Ω`, then
`T ω = ∑ x ∈ s, a x * ω x ![]` for the finite set `s` equal to the support of `T` and integer
coefficients `a x`, nonzero on `s`. -/
theorem IsIntegerRectifiable.exists_finset_apply_eq_sum_finZero (hT : IsIntegerRectifiable T)
    (hTc : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    ∃ (s : Finset V) (a : V → ℤ), (s : Set V) = dsupport T ∧ (∀ x ∈ s, a x ≠ 0) ∧
      ∀ ω, T ω = ∑ x ∈ s, (a x : ℝ) * ω x ![] := by
  have hfin : (dsupport T).Finite := by
    simpa using hT.finite_inter_dsupport_finZero hTc hTΩ
  obtain ⟨θ, τ, -, -, -, hθ, -, -, rfl⟩ := isIntegerRectifiable_iff.1 hT
  have hsupp := inter_dsupport_frameCurrent_finZero (n := n) (τ := τ) hθ
  rw [inter_eq_right.2 hTΩ] at hsupp
  refine ⟨hfin.toFinset, θ, by simp, fun x hx ↦ ?_, fun ω ↦ ?_⟩
  · have hx' := hfin.mem_toFinset.1 hx
    rw [hsupp] at hx'
    exact hx'.2
  · refine frameCurrent_finZero_apply_eq_sum hθ ω fun x hx ↦ ?_
    rw [Finite.coe_toFinset, hsupp]
    exact ⟨ω.tsupport_subset hx.1, hx.2⟩

/-- **Finite integer combinations of point masses are integer-rectifiable.** A `0`-current with
`T ω = ∑ x ∈ s, a x * ω x ![]` for a finite set `s` and integer coefficients `a x` is
integer-rectifiable. -/
theorem isIntegerRectifiable_finZero_of_apply_eq_sum (s : Finset V) (a : V → ℤ)
    (hT : ∀ ω, T ω = ∑ x ∈ s, (a x : ℝ) * ω x ![]) : IsIntegerRectifiable T := by
  classical
  -- `T` is the frame current of the multiplicity equal to `a` on `s` and to zero elsewhere.
  set θ : V → ℤ := fun x ↦ if x ∈ s then a x else 0
  have hθs : {x | θ x ≠ 0} ⊆ s := fun x hx ↦
    by_contra fun h ↦ hx (by simp_all [θ])
  have hfin : (Function.support θ).Finite := s.finite_toSet.subset hθs
  have hθi : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0] := by
    refine Integrable.locallyIntegrable ?_ |>.locallyIntegrableOn _
    rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_count,
      integrable_count_iff]
    exact summable_of_ne_finset_zero (s := s) fun x hx ↦ by simp [θ, hx]
  refine isIntegerRectifiable_iff.2 ⟨θ, fun _ ↦ ![],
    measurable_zero.measurable_of_countable_ne (hfin.countable.mono fun _ hx ↦ Ne.symm hx),
    measurable_const, hfin.countable.countablyRectifiable, hθi, fun _ _ ↦ .of_isEmpty _,
    ae_of_all _ fun x _ _ ↦ ?_, ?_⟩
  · -- The finitely many atoms are isolated, so the cone-density condition holds at each of them.
    obtain ⟨δ, hδ, -, hδθ⟩ := exists_closedBall_inter_subset_singleton isOpen_univ
      (compl_finite_mem_codiscreteWithin hfin) (mem_univ x)
    refine densityZeroOutsideCones_of_forall_sub_mem hδ fun z hz ↦ ?_
    obtain rfl : z = x := hδθ ⟨hz.2, hz.1⟩
    simp
  · ext ω
    rw [hT, frameCurrent_finZero_apply_eq_sum hθi ω fun x hx ↦ hθs hx.2]
    exact Finset.sum_congr rfl fun x hx ↦ by simp [θ, hx]

end IntegerRectifiable

section Integral

variable {T : 𝓓(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- **Compactly supported integral `0`-currents are the finite integer combinations of point
masses.** A `0`-current on `Ω` is a compactly supported integral current exactly when
`T ω = ∑ x ∈ s, a x * ω x ![]` for a finite set `s ⊆ Ω` and integer coefficients `a x`. -/
theorem isCompactlySupportedIntegralCurrent_finZero_iff :
    IsCompactlySupportedIntegralCurrent T ↔ ∃ (s : Finset V) (a : V → ℤ), (s : Set V) ⊆ Ω ∧
      ∀ ω, T ω = ∑ x ∈ s, (a x : ℝ) * ω x ![] := by
  refine ⟨fun hT ↦ ?_, fun ⟨s, a, hs, hT⟩ ↦ ?_⟩
  · obtain ⟨s, a, hsT, -, hT'⟩ := (isLocallyIntegral_finZero_iff.1 hT.isLocallyIntegral)
      |>.exists_finset_apply_eq_sum_finZero hT.isCompact_dsupport hT.dsupport_subset
    exact ⟨s, a, hsT ▸ hT.dsupport_subset, hT'⟩
  · have hsupp : dsupport T ⊆ s := by
      rw [funext hT]
      simpa using dsupport_sum_apply_apply_subset s fun x ↦
        (((a x : ℝ) • ContinuousAlternatingMap.apply ℝ V ℝ ![] :
          (V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) : (V [⋀^Fin 0]→L[ℝ] ℝ) →+ ℝ)
    exact (isLocallyIntegral_finZero_iff.2 (isIntegerRectifiable_finZero_of_apply_eq_sum s a hT))
      |>.isCompactlySupportedIntegralCurrent
        (s.finite_toSet.isCompact.of_isClosed_subset isClosed_dsupport hsupp) (hsupp.trans hs)

end Integral

end Distribution
