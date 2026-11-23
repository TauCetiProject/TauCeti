/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Unitization
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Schmidt
public import TauCeti.Analysis.Normed.Lp.Diagonal.Positive
public import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
public import TauCeti.Analysis.VonNeumannAlgebra.Kaplansky
public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Examples and negative controls for Kaplansky's density theorem

We verify two opposite regimes of Kaplansky's density theorem and exhibit the sharpness of its
strong-operator topology in the positive-contraction clause:

* For the scalar star subalgebra `⊥` (`ℂ • 1`), the double commutant is `⊥` itself, so the unit
  balls of `⊥` and `⊥''` coincide and the strong-operator unit ball of `⊥` is already closed.
* For the unital star subalgebra `finiteRankPlusScalars H` of finite-rank perturbations of scalars
  on a complete complex Hilbert space `H`, the commutant consists of the scalars and the double
  commutant is all of `H →L[ℂ] H`. By Kaplansky's density theorem, the strong-operator closure of
  its unit ball is the entire unit ball of `H →L[ℂ] H`, and the strong-operator closure of its
  positive contractions is all of `Set.Icc 0 1`.
* On `ℓ^2(ℕ, ℂ)`, the diagonal orthogonal projection `evenProjection` onto the even coordinates is
  a positive contraction in `(finiteRankPlusScalars ℓ^2(ℕ, ℂ))'' = Set.univ`, approximated in the
  strong operator topology by its finite-rank coordinate truncations `evenProjectionTrunc n`. Yet
  for every scalar `c : ℂ` and compact operator `K`, testing on the even and odd coordinate basis
  vectors yields `max ‖1 - c‖ ‖c‖ ≤ ‖evenProjection - (algebraMap ℂ _ c + K)‖`, hence
  `1 / 2 ≤ ‖evenProjection - a‖` for every `a ∈ finiteRankPlusScalars ℓ^2(ℕ, ℂ)`. Thus
  `evenProjection` lies at operator-norm distance at least `1 / 2` from `finiteRankPlusScalars`,
  demonstrating that strong-operator density in Kaplansky's theorem cannot be upgraded to norm
  density.
-/

public section

noncomputable section

open Filter Metric Set
open scoped ComplexOrder ENNReal InnerProductSpace lp Topology

namespace TauCeti.KaplanskyExample

/-! ### Positive trivial check: the scalar star subalgebra `⊥` -/

section Bot

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The double commutant of the scalar star subalgebra `⊥` equals `⊥`. -/
theorem centralizer_centralizer_coe_bot :
    ((⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)).centralizer.centralizer =
      ((⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
  rw [← VonNeumannAlgebra.toStarSubalgebra_bot]
  exact (⊥ : VonNeumannAlgebra H).centralizer_centralizer

/-- For `⊥ = ℂ • 1`, the strong-operator closure of the unit ball is the unit ball of `⊥` itself. -/
theorem closure_unitBall_bot_eq_image :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x : H →L[ℂ] H | x ∈ (⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x : H →L[ℂ] H | x ∈ (⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) ∧ ‖x‖ ≤ 1} := by
  simpa only [centralizer_centralizer_coe_bot H, SetLike.mem_coe] using
    (⊥ : StarSubalgebra ℂ (H →L[ℂ] H)).closure_unitBall_eq_unitBall_double_centralizer

end Bot

/-! ### Finite-rank perturbations of scalars on a Hilbert space -/

section FiniteRankPlusScalars

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H) in
/-- The nonunital star subalgebra of finite-rank bounded operators on `H`. -/
def finiteRankOperators : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {F | (F : H →ₗ[ℂ] H).HasFiniteRange}
  add_mem' hF₁ hF₂ := hF₁.add hF₂
  zero_mem' := LinearMap.HasFiniteRange.zero
  mul_mem' hF₁ _ := hF₁.comp_right _
  smul_mem' c _ hF := hF.smul c
  star_mem' hF := hF.star

/-- A bounded operator belongs to `finiteRankOperators H` if and only if its underlying linear map
has finite range. -/
@[simp]
theorem mem_finiteRankOperators {T : H →L[ℂ] H} :
    T ∈ finiteRankOperators H ↔ (T : H →ₗ[ℂ] H).HasFiniteRange :=
  Iff.rfl

variable (H) in
/-- The unital star subalgebra of bounded operators of the form `algebraMap ℂ _ c + F` with `F` of
finite rank. -/
def finiteRankPlusScalars : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (NonUnitalStarSubalgebra.unitization (finiteRankOperators H)).range

@[simp]
theorem mem_finiteRankPlusScalars {T : H →L[ℂ] H} :
    T ∈ finiteRankPlusScalars H ↔ ∃ (c : ℂ) (F : H →L[ℂ] H),
      (F : H →ₗ[ℂ] H).HasFiniteRange ∧ T = algebraMap ℂ (H →L[ℂ] H) c + F := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.fst, x.snd, x.snd.property, NonUnitalStarSubalgebra.unitization_apply _ x⟩
  · rintro ⟨c, F, hF, rfl⟩
    refine ⟨Unitization.inl c + Unitization.inr (⟨F, hF⟩ : finiteRankOperators H), ?_⟩
    simp [NonUnitalStarSubalgebra.unitization_apply]

/-- Every finite-rank operator belongs to `finiteRankPlusScalars H`. -/
theorem mem_finiteRankPlusScalars_of_hasFiniteRange {F : H →L[ℂ] H}
    (hF : (F : H →ₗ[ℂ] H).HasFiniteRange) : F ∈ finiteRankPlusScalars H :=
  mem_finiteRankPlusScalars.2 ⟨0, F, hF, by simp⟩

/-- The commutant of `finiteRankPlusScalars H` consists strictly of scalar multiples of `1`. -/
theorem centralizer_coe_finiteRankPlusScalars :
    (finiteRankPlusScalars H : Set (H →L[ℂ] H)).centralizer =
      Set.range (algebraMap ℂ (H →L[ℂ] H)) := by
  refine subset_antisymm (fun R hR ↦ ?_) ?_
  · by_cases hH : ∃ u : H, u ≠ 0
    · obtain ⟨u, hu⟩ := hH
      have hu_norm : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
      let e : H := (‖u‖⁻¹ : ℝ) • u
      have hn : ‖e‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hu_norm]
      refine ⟨⟪e, R e⟫_ℂ, ContinuousLinearMap.ext fun x ↦ ?_⟩
      let Eex : H →L[ℂ] H := InnerProductSpace.rankOne ℂ x e
      have hEex_fin : (Eex : H →ₗ[ℂ] H).HasFiniteRange := by
        simp only [Eex, InnerProductSpace.rankOne_def']
        exact LinearMap.HasFiniteRange.of_finite_dom.comp_right _
      have hcomm := DFunLike.congr_fun
        (hR Eex (mem_finiteRankPlusScalars_of_hasFiniteRange hEex_fin)) e
      simpa [Eex, mul_apply_eq_comp, hn, Algebra.algebraMap_eq_smul_one] using hcomm
    · push Not at hH
      exact ⟨0, ContinuousLinearMap.ext fun x ↦ by simp [hH x]⟩
  · rintro _ ⟨c, rfl⟩ S _
    exact (Algebra.commutes c S).symm

/-- The double commutant of `finiteRankPlusScalars H` is the entire algebra `H →L[ℂ] H`. -/
theorem centralizer_centralizer_coe_finiteRankPlusScalars :
    (finiteRankPlusScalars H : Set (H →L[ℂ] H)).centralizer.centralizer = Set.univ := by
  rw [centralizer_coe_finiteRankPlusScalars, ← VonNeumannAlgebra.coe_bot,
    ← VonNeumannAlgebra.coe_commutant, VonNeumannAlgebra.commutant_bot, VonNeumannAlgebra.coe_top]

/-- By Kaplansky's density theorem, the strong-operator closure of the unit ball of
`finiteRankPlusScalars H` is the entire unit ball of `H →L[ℂ] H`. -/
theorem closure_unitBall_finiteRankPlusScalars :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x : H →L[ℂ] H | x ∈ finiteRankPlusScalars H ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x : H →L[ℂ] H | ‖x‖ ≤ 1} := by
  simpa [centralizer_centralizer_coe_finiteRankPlusScalars] using
    (finiteRankPlusScalars H).closure_unitBall_eq_unitBall_double_centralizer

/-- By the positive-part Kaplansky density theorem, the strong-operator closure of the positive
contractions of `finiteRankPlusScalars H` is the entire order interval `Set.Icc 0 1`. -/
theorem closure_inter_Icc_zero_one_finiteRankPlusScalars :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((finiteRankPlusScalars H : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        Icc (0 : H →L[ℂ] H) 1 := by
  simpa [centralizer_centralizer_coe_finiteRankPlusScalars] using
    (finiteRankPlusScalars H).closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one

end FiniteRankPlusScalars

/-! ### Negative control on `ℓ^2(ℕ, ℂ)`: strong density vs. operator-norm distance `≥ 1 / 2` -/

/-- Bounded sequence on `ℕ` equal to `1` on even indices and `0` on odd indices. -/
def evenSeq : ℓ^∞(ℕ, ℂ) :=
  ⟨fun n ↦ if Even n then 1 else 0,
    memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; dsimp; split_ifs <;> simp⟩⟩

@[simp]
theorem evenSeq_apply (n : ℕ) : evenSeq n = if Even n then 1 else 0 := (rfl)

/-- Diagonal orthogonal projection on `ℓ^2(ℕ, ℂ)` onto the closed span of the even basis vectors. -/
def evenProjection : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) :=
  lp.diagonalCLM evenSeq

/-- `evenProjection` is the diagonal operator with symbol `evenSeq`. -/
theorem evenProjection_def : evenProjection = lp.diagonalCLM evenSeq :=
  (rfl)

/-- On coordinates, `evenProjection` retains even entries and zeroes odd entries. -/
@[simp]
theorem evenProjection_apply (x : ℓ^2(ℕ, ℂ)) (n : ℕ) :
    evenProjection x n = if Even n then x n else 0 := by
  simp [evenProjection_def]

/-- `evenProjection` is an orthogonal projection (`IsStarProjection`). -/
theorem isStarProjection_evenProjection : IsStarProjection evenProjection where
  isIdempotentElem := by
    ext x n
    simp only [mul_apply_eq_comp, evenProjection_apply]
    split_ifs <;> simp
  isSelfAdjoint := by
    rw [evenProjection_def, lp.isSelfAdjoint_diagonalCLM_iff]
    intro n
    simp only [evenSeq_apply]
    split_ifs <;> simp

/-- Finite-rank coordinate truncations of `evenProjection` along `Finset.range n`. -/
def evenProjectionTrunc (n : ℕ) : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) :=
  lp.diagonalTruncation evenSeq (Finset.range n)

/-- `evenProjectionTrunc n` is the `Finset.range n` diagonal truncation of `evenSeq`. -/
theorem evenProjectionTrunc_def (n : ℕ) :
    evenProjectionTrunc n = lp.diagonalTruncation evenSeq (Finset.range n) :=
  (rfl)

/-- On coordinates, `evenProjectionTrunc n` retains even entries strictly below `n`. -/
@[simp]
theorem evenProjectionTrunc_apply (n : ℕ) (x : ℓ^2(ℕ, ℂ)) (k : ℕ) :
    evenProjectionTrunc n x k = if k < n ∧ Even k then x k else 0 := by
  simp only [evenProjectionTrunc_def, lp.diagonalTruncation_apply, Finset.mem_range, evenSeq_apply]
  split_ifs <;> simp_all

/-- `evenProjection` is a positive contraction (`0 ≤ evenProjection` and `evenProjection ≤ 1`). -/
theorem evenProjection_mem_Icc :
    evenProjection ∈ Icc (0 : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) 1 :=
  isStarProjection_evenProjection.mem_Icc

/-- Each finite-rank truncation `evenProjectionTrunc n` is a positive contraction in
`finiteRankPlusScalars ℓ^2(ℕ, ℂ)`. -/
theorem evenProjectionTrunc_mem_inter_Icc (n : ℕ) :
    evenProjectionTrunc n ∈
      (finiteRankPlusScalars ℓ^2(ℕ, ℂ) : Set (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ))) ∩ Icc 0 1 := by
  have hd0 : ∀ k, 0 ≤ evenSeq k := fun k ↦ by simp only [evenSeq_apply]; split_ifs <;> simp
  have hfin : Module.Finite ℂ (LinearMap.range (evenProjectionTrunc n).toLinearMap) :=
    Module.rank_lt_aleph0_iff.mp
      ((lp.rank_diagonalTruncation_range_le (p := 2) evenSeq n).trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨mem_finiteRankPlusScalars_of_hasFiniteRange (Module.Finite.iff_fg.mp hfin),
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((lp.isPositive_diagonalTruncation_iff evenSeq (Finset.range n)).2 fun k _ ↦ hd0 k),
    (lp.diagonalTruncation_le_diagonalCLM hd0 (Finset.range n)).trans evenProjection_mem_Icc.2⟩

/-- The finite-rank positive contractions `evenProjectionTrunc n` converge to `evenProjection` in
the strong operator topology. -/
theorem tendsto_toPointwiseConvergenceCLM_evenProjectionTrunc :
    Tendsto (fun n ↦ ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ) (evenProjectionTrunc n))
      atTop (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ) evenProjection)) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  intro x
  exact (lp.tendsto_diagonalTruncation_apply (p := 2) ENNReal.ofNat_ne_top evenSeq x).comp
    tendsto_finset_range

/-- `evenProjection` belongs to the strong-operator closure of the positive contractions in
`finiteRankPlusScalars ℓ^2(ℕ, ℂ)`. -/
theorem toPointwiseConvergenceCLM_evenProjection_mem_closure_inter_Icc :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ)
        evenProjection ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        ℓ^2(ℕ, ℂ) ℓ^2(ℕ, ℂ) ''
        ((finiteRankPlusScalars ℓ^2(ℕ, ℂ) : Set (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ))) ∩ Icc 0 1)) := by
  rw [closure_inter_Icc_zero_one_finiteRankPlusScalars]
  exact ⟨evenProjection, evenProjection_mem_Icc, rfl⟩

/-- Every compact perturbation of a scalar `c • 1 + K` on `ℓ^2(ℕ, ℂ)` has operator-norm distance at
least `max ‖1 - c‖ ‖c‖` from `evenProjection`. -/
theorem max_norm_le_norm_evenProjection_sub_algebraMap_add_compact (c : ℂ)
    {K : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)} (hK : IsCompactOperator K) :
    max ‖1 - c‖ ‖c‖ ≤
      ‖evenProjection - (algebraMap ℂ (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) c + K)‖ := by
  let e : ℕ → ℓ^2(ℕ, ℂ) := fun n ↦ lp.single 2 n 1
  have he : Orthonormal ℂ e := orthonormal_iff_ite.mpr fun i j ↦ by
    simp [e, lp.inner_single_left, Pi.single_apply]
  have hKe : Tendsto (fun n : ℕ ↦ ‖K (e n)‖) atTop (𝓝 0) := by
    simpa [Nat.cofinite_eq_atTop] using he.tendsto_norm_apply_cofinite hK
  set D := evenProjection - (algebraMap ℂ (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) c + K)
  have hsub (f : ℕ → ℕ) (hf : StrictMono f) (α : ℂ)
      (hα : ∀ k, evenProjection (e (f k)) = α • e (f k)) : ‖α - c‖ ≤ ‖D‖ := by
    have hlim : Tendsto (fun k ↦ ‖α - c‖ - ‖K (e (f k))‖) atTop (𝓝 ‖α - c‖) := by
      simpa using tendsto_const_nhds.sub (hKe.comp hf.tendsto_atTop)
    refine le_of_tendsto hlim (Eventually.of_forall fun k ↦ ?_)
    have hDe : D (e (f k)) = (α - c) • e (f k) - K (e (f k)) := by
      simp [D, Algebra.algebraMap_eq_smul_one, sub_add_eq_sub_sub, hα, sub_smul]
    calc ‖α - c‖ - ‖K (e (f k))‖
        = ‖(α - c) • e (f k)‖ - ‖K (e (f k))‖ := by rw [norm_smul, he.1 (f k), mul_one]
      _ ≤ ‖(α - c) • e (f k) - K (e (f k))‖ := norm_sub_norm_le _ _
      _ = ‖D (e (f k))‖ := by rw [hDe]
      _ ≤ ‖D‖ := by simpa [he.1 (f k)] using D.le_opNorm (e (f k))
  refine max_le
    (hsub (2 * ·) (fun _ _ h ↦ Nat.mul_lt_mul_of_pos_left h two_pos) 1 fun k ↦ by
      simp [evenProjection_def, e, lp.diagonalCLM_single]) ?_
  simpa using hsub (fun k ↦ 2 * k + 1)
    (fun _ _ h ↦ Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left h two_pos) 1) 0 fun k ↦ by
      simp [evenProjection_def, e, lp.diagonalCLM_single]

/-- Every element of `finiteRankPlusScalars ℓ^2(ℕ, ℂ)` lies at operator-norm distance at least
`1 / 2` from `evenProjection`. -/
theorem half_le_norm_evenProjection_sub {a : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)}
    (ha : a ∈ finiteRankPlusScalars ℓ^2(ℕ, ℂ)) :
    (1 / 2 : ℝ) ≤ ‖evenProjection - a‖ := by
  obtain ⟨c, F, hF, rfl⟩ := mem_finiteRankPlusScalars.1 ha
  have hmax := max_norm_le_norm_evenProjection_sub_algebraMap_add_compact c hF.isCompactOperator
  have h1 : (1 : ℝ) ≤ ‖1 - c‖ + ‖c‖ := by simpa using norm_add_le (1 - c) c
  linarith [le_max_left ‖1 - c‖ ‖c‖, le_max_right ‖1 - c‖ ‖c‖]

/-- `evenProjection` does not lie in the operator-norm closure of
`finiteRankPlusScalars ℓ^2(ℕ, ℂ)`, so the strong-operator closure in Kaplansky's density theorem
cannot be strengthened to operator-norm closure. -/
theorem evenProjection_notMem_closure_finiteRankPlusScalars :
    evenProjection ∉
      closure (finiteRankPlusScalars ℓ^2(ℕ, ℂ) : Set (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ))) := fun hcl ↦ by
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.1 hcl (1 / 2) (by positivity)
  rw [dist_eq_norm] at hdist
  exact hdist.not_ge (half_le_norm_evenProjection_sub ha)

end TauCeti.KaplanskyExample
