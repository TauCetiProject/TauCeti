/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.Integral
import TauCeti.MeasureTheory.Measure.Hausdorff

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
set `s` equal to its support (`Distribution.IsIntegerRectifiable.exists_finset_finZero`).
Conversely, every finite integer combination of point masses is integer-rectifiable, so the
compactly supported integral `0`-currents are exactly the finite integer combinations of point
masses at points of `Ω` (`Distribution.isCompactlySupportedIntegralCurrent_finZero_iff`). The
augmentation of a finite combination of point masses is the sum of its coefficients
(`Distribution.augmentation_sum_mul_apply_finZero`), so the augmentation of a compactly supported
integral `0`-current is an integer, and its mass is the sum of the absolute values of the
coefficients (`Distribution.mass_sum_mul_apply_finZero`).

## Main declarations

* `Distribution.IsIntegerRectifiable.finite_inter_dsupport_finZero`: the support of an
  integer-rectifiable `0`-current is finite in every compact subset of `Ω`.
* `Distribution.IsIntegerRectifiable.exists_finset_finZero`: an integer-rectifiable `0`-current
  whose support is a compact subset of `Ω` is a finite sum of integer point masses, located exactly
  at the points of its support.
* `Distribution.isIntegerRectifiable_finZero_of_apply_eq_sum`: finite integer combinations of
  point masses are integer-rectifiable.
* `Distribution.isCompactlySupportedIntegralCurrent_finZero_iff`: the compactly supported integral
  `0`-currents are the finite integer combinations of point masses at points of `Ω`.
* `Distribution.dsupport_sum_mul_apply_finZero_subset`,
  `Distribution.augmentation_sum_mul_apply_finZero`: a finite combination of point masses is
  supported on its atoms, and its augmentation is the sum of the coefficients.

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

section Augmentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}

/-- The support of a finite combination `ω ↦ ∑ x ∈ s, a x * ω x ![]` of point masses lies in the
finite set `s`. -/
theorem dsupport_sum_mul_apply_finZero_subset (s : Finset E) (a : E → ℝ) :
    dsupport (fun ω : 𝓓^{n}(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) ↦ ∑ x ∈ s, a x * ω x ![]) ⊆ s := by
  simpa using dsupport_sum_apply_apply_subset s
    fun x ↦ ((a x • ContinuousAlternatingMap.apply ℝ E ℝ ![] :
      (E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) : (E [⋀^Fin 0]→L[ℝ] ℝ) →+ ℝ)

/-- **The augmentation of a finite combination of point masses** is the sum of the coefficients:
for a finite set `s ⊆ Ω`, the `0`-current `ω ↦ ∑ x ∈ s, a x * ω x ![]` evaluated on the constant
`0`-form `c` near its support is `(∑ x ∈ s, a x) * c ![]`. -/
theorem augmentation_sum_mul_apply_finZero [FiniteDimensional ℝ E] {s : Finset E}
    (hs : (s : Set E) ⊆ Ω) (a : E → ℝ) (c : E [⋀^Fin 0]→L[ℝ] ℝ) :
    augmentation (fun ω : 𝓓^{n}(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) ↦ ∑ x ∈ s, a x * ω x ![]) c =
      (∑ x ∈ s, a x) * c ![] := by
  simpa [Finset.sum_mul] using augmentation_sum_apply_apply hs
    (fun x ↦ ((a x • ContinuousAlternatingMap.apply ℝ E ℝ ![] :
      (E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) : (E [⋀^Fin 0]→L[ℝ] ℝ) →+ ℝ)) c

end Augmentation

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
  rw [← Measure.count_apply_lt_top]
  calc Measure.count (K ∩ {x | θ x ≠ 0})
      ≤ (Measure.count.restrict K) {x | 1 ≤ ‖(θ x : ℝ)‖ₑ} := by
        have hsub : K ∩ {x | θ x ≠ 0} ⊆ {x | 1 ≤ ‖(θ x : ℝ)‖ₑ} ∩ K := fun x hx ↦ by
          refine ⟨?_, hx.1⟩
          rw [mem_ofPred_eq, Real.eNorm_eq_ofReal_abs, ENNReal.one_le_ofReal, ← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hx.2
        exact (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
    _ ≤ ∫⁻ x in K, ‖(θ x : ℝ)‖ₑ ∂Measure.count := by
        simpa using mul_meas_ge_le_lintegral₀ hint.aestronglyMeasurable.eNorm 1
    _ < ∞ := hint.2

/-- Each point of `Ω` has an open neighbourhood in `Ω` containing no other point where the integer
multiplicity is nonzero. -/
private theorem exists_isOpen_inter_setOf_ne_zero_subset
    (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0]) {x : V} (hx : x ∈ Ω) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ U ∩ {y | θ y ≠ 0} ⊆ {x} := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hK : closedBall x (r / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hrΩ
  have hfin := finite_inter_setOf_ne_zero hθ (isCompact_closedBall x (r / 2)) hK
  refine ⟨ball x (r / 2) \ ((closedBall x (r / 2) ∩ {y | θ y ≠ 0}) \ {x}),
    isOpen_ball.sdiff (hfin.sdiff).isClosed, ⟨mem_ball_self (half_pos hr), fun h ↦ h.2 rfl⟩,
    sdiff_subset.trans (ball_subset_closedBall.trans hK), fun y hy ↦ ?_⟩
  by_contra hyx
  exact hy.1.2 ⟨⟨ball_subset_closedBall hy.1.1, hy.2⟩, hyx⟩

variable {τ : V → Fin 0 → V} (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0])
  (hτ : Measurable τ) (hτo : ∀ x, (θ x : ℝ) ≠ 0 → Orthonormal ℝ (τ x))
include hθ hτ hτo

/-- A test `0`-form `ω` pairs with the frame current of an integer multiplicity `θ` as the finite
sum `∑ x ∈ s, θ(x) ω_x()` over any finite set `s` containing the points of `tsupport ω` where
`θ ≠ 0`. -/
private theorem frameCurrent_finZero_apply_eq_sum (ω : 𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ))
    {s : Finset V} (hs : tsupport ω ∩ {x | θ x ≠ 0} ⊆ s) :
    frameCurrent (fun x ↦ (θ x : ℝ)) τ ω = ∑ x ∈ s, (θ x : ℝ) * ω x ![] := by
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
    obtain ⟨U, hU, hxU, -, hUθ⟩ := exists_isOpen_inter_setOf_ne_zero_subset hθ hxΩ
    have hvan : IsVanishingOn T U := fun ω hω ↦ by
      rw [frameCurrent_finZero_apply_eq_sum hθ hτ hτo ω (s := ∅) fun y hy ↦ ?_,
        Finset.sum_empty]
      obtain rfl : y = x := hUθ ⟨hω hy.1, hy.2⟩
      exact (hy.2 hθx).elim
    exact (hvan.disjoint_dsupport hU).ne_of_mem hxU hxT rfl
  · rintro x ⟨hxΩ, hθx⟩
    refine ⟨hxΩ, by_contra fun hxT ↦ ?_⟩
    -- A test form equal to the unit `0`-form at an isolated atom `x`, supported away from the
    -- support of `T`, would be sent both to `θ x` and to zero.
    obtain ⟨U, hU, hxU, hUΩ, hUθ⟩ := exists_isOpen_inter_setOf_ne_zero_subset hθ hxΩ
    obtain ⟨ω, hωU, hωx⟩ := exists_tsupport_subset_apply_eq (n := n)
      ((hU.inter isClosed_dsupport.isOpen_compl).mem_nhds ⟨hxU, hxT⟩)
      (inter_subset_left.trans hUΩ) (ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (1 : ℝ))
    have h0 : T ω = 0 := map_eq_zero_of_disjoint_dsupport T
      (subset_compl_iff_disjoint_right.1 (hωU.trans inter_subset_right))
    have h1 : T ω = θ x := by
      rw [frameCurrent_finZero_apply_eq_sum hθ hτ hτo ω (s := {x}) fun y hy ↦ by
        simpa using hUθ ⟨(hωU hy.1).1, hy.2⟩]
      simp [hωx]
    exact hθx (by exact_mod_cast h1.symm.trans h0)

end Multiplicity

section IntegerRectifiable

variable {T : 𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- **Integer-rectifiable `0`-currents have locally finite support.** The support of an
integer-rectifiable `0`-current meets each compact subset of `Ω` in a finite set. -/
theorem IsIntegerRectifiable.finite_inter_dsupport_finZero (hT : IsIntegerRectifiable T)
    {K : Set V} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (K ∩ dsupport T).Finite := by
  obtain ⟨θ, τ, -, hτ, -, hθ, hτo, -, rfl⟩ := isIntegerRectifiable_iff.1 hT
  have hτo' (x : V) (hx : (θ x : ℝ) ≠ 0) : Orthonormal ℝ (τ x) := hτo x (by exact_mod_cast hx)
  refine (finite_inter_setOf_ne_zero hθ hK hKΩ).subset fun x ⟨hxK, hxT⟩ ↦ ⟨hxK, ?_⟩
  have hx : x ∈ (Ω : Set V) ∩ dsupport (frameCurrent (fun x ↦ (θ x : ℝ)) τ :
      𝓓^{n}(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) := ⟨hKΩ hxK, hxT⟩
  rw [inter_dsupport_frameCurrent_finZero hθ hτ hτo'] at hx
  exact hx.2

/-- **Compactly supported integer-rectifiable `0`-currents are finite sums of integer point
masses.** If the support of an integer-rectifiable `0`-current `T` is a compact subset of `Ω`, then
`T ω = ∑ x ∈ s, a x * ω x ![]` for the finite set `s` equal to the support of `T` and integer
coefficients `a x`, nonzero on `s`. -/
theorem IsIntegerRectifiable.exists_finset_finZero (hT : IsIntegerRectifiable T)
    (hTc : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    ∃ (s : Finset V) (a : V → ℤ), (s : Set V) = dsupport T ∧ (∀ x ∈ s, a x ≠ 0) ∧
      ∀ ω, T ω = ∑ x ∈ s, (a x : ℝ) * ω x ![] := by
  have hfin : (dsupport T).Finite := by
    simpa [inter_eq_right.2 subset_rfl] using hT.finite_inter_dsupport_finZero hTc hTΩ
  obtain ⟨θ, τ, -, hτ, -, hθ, hτo, -, rfl⟩ := isIntegerRectifiable_iff.1 hT
  have hτo' (x : V) (hx : (θ x : ℝ) ≠ 0) : Orthonormal ℝ (τ x) := hτo x (by exact_mod_cast hx)
  have hsupp := inter_dsupport_frameCurrent_finZero (n := n) hθ hτ hτo'
  rw [inter_eq_right.2 hTΩ] at hsupp
  refine ⟨hfin.toFinset, θ, by simp, fun x hx ↦ ?_, fun ω ↦ ?_⟩
  · have hx' := hfin.mem_toFinset.1 hx
    rw [hsupp] at hx'
    exact hx'.2
  · refine frameCurrent_finZero_apply_eq_sum hθ hτ hτo' ω fun x hx ↦ ?_
    rw [Finite.coe_toFinset, hsupp]
    exact ⟨ω.tsupport_subset hx.1, hx.2⟩

/-- **Finite integer combinations of point masses are integer-rectifiable.** A `0`-current with
`T ω = ∑ x ∈ s, a x * ω x ![]` for a finite set `s` and integer coefficients `a x` is the frame
current of the integer multiplicity equal to `a` on `s` and to zero elsewhere. -/
theorem isIntegerRectifiable_finZero_of_apply_eq_sum (s : Finset V) (a : V → ℤ)
    (hT : ∀ ω, T ω = ∑ x ∈ s, (a x : ℝ) * ω x ![]) : IsIntegerRectifiable T := by
  classical
  set θ : V → ℤ := fun x ↦ if x ∈ s then a x else 0
  have hθs : {x | θ x ≠ 0} ⊆ s := fun x hx ↦
    by_contra fun h ↦ hx (by simp_all [θ])
  have hfin : (Function.support θ).Finite := s.finite_toSet.subset hθs
  have hθm : Measurable θ := measurable_to_countable' fun m ↦ by
    by_cases hm : m = 0
    · have h : θ ⁻¹' {m} = (Function.support θ)ᶜ := by ext; simp [hm]
      exact h ▸ hfin.measurableSet.compl
    · exact (hfin.subset (t := θ ⁻¹' {m}) fun x hx ↦ by simp_all).measurableSet
  have hθi : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[0] := by
    refine Integrable.locallyIntegrable ?_ |>.locallyIntegrableOn _
    rw [Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_eq_count,
      integrable_count_iff]
    exact summable_of_ne_finset_zero (s := s) fun x hx ↦ by simp [θ, hx]
  refine isIntegerRectifiable_iff.2 ⟨θ, fun _ ↦ ![], hθm, measurable_const, ?_, hθi,
    fun _ _ ↦ .of_isEmpty _, ae_of_all _ fun x _ _ ↦ ?_, ?_⟩
  · exact (CountablyRectifiable.iUnion fun x : s ↦ CountablyRectifiable.singleton (x : V)).mono
      fun x hx ↦ mem_iUnion.2 ⟨⟨x, hθs hx⟩, rfl⟩
  · -- The finitely many atoms are isolated, so the cone-density condition holds at each of them.
    have hF : IsOpen ({y | θ y ≠ 0} \ {x})ᶜ :=
      (hfin.subset (t := {y | θ y ≠ 0} \ {x}) fun y hy ↦ hy.1).isClosed.isOpen_compl
    obtain ⟨r, hr, hrF⟩ := Metric.isOpen_iff.1 hF x (by simp)
    refine densityZeroOutsideCones_of_inter_closedBall_subset (half_pos hr) (fun y hy ↦ ?_) _
    by_contra hyx
    exact hrF (closedBall_subset_ball (half_lt_self hr) hy.2) ⟨hy.1, hyx⟩
  · ext ω
    rw [hT, frameCurrent_finZero_apply_eq_sum hθi measurable_const (fun _ _ ↦ .of_isEmpty _) ω
      fun x hx ↦ hθs hx.2]
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
      |>.exists_finset_finZero hT.isCompact_dsupport hT.dsupport_subset
    exact ⟨s, a, hsT ▸ hT.dsupport_subset, hT'⟩
  · have hsupp : dsupport T ⊆ s := by
      rw [funext hT]
      exact dsupport_sum_mul_apply_finZero_subset s _
    exact (isLocallyIntegral_finZero_iff.2 (isIntegerRectifiable_finZero_of_apply_eq_sum s a hT))
      |>.isCompactlySupportedIntegralCurrent
        (s.finite_toSet.isCompact.of_isClosed_subset isClosed_dsupport hsupp) (hsupp.trans hs)

end Integral

end Distribution
