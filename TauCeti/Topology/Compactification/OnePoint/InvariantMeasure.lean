/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.GroupTheory.Amenable.Basic

import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.Sequences
import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.GroupTheory.Amenable.Subgroup
import TauCeti.Topology.Compactification.OnePoint.Amenable
import TauCeti.Topology.Compactification.OnePoint.Nhds
import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Invariant probability measures on the projective line and Furstenberg's lemma

For a proper normed field `𝕜`, the special linear group `SL(2, 𝕜)` acts on the
projective line `OnePoint 𝕜` by Möbius transformations. A sequence of matrices in `GL(2, 𝕜)`
converging entrywise to a nonzero singular matrix `M` contracts the complement of the projective
kernel of `M` to the projective image of `M`. Consequently, any Borel probability measure on
`OnePoint 𝕜` preserved by such a sequence and giving mass zero to the projective kernel must be the
Dirac mass at the projective image.

Rescaling an unbounded sequence in `SL(2, 𝕜)` by its largest entry produces a sequence in the
compact unit polydisc whose determinant tends to zero, so a subsequence converges to a nonzero
singular matrix. This yields Furstenberg's lemma: the set of elements of `SL(2, 𝕜)` preserving a
Borel probability measure without point masses on `OnePoint 𝕜` has uniformly bounded matrix
entries.

Combined with the amenability of projective-line point stabilizers
(`MonoidHom.amenable_comap_onePoint_stabilizer`), any group admitting a proper homomorphism into
`SL(2, 𝕜)` (meaning bounded matrix sets have finite preimages) — in particular the image of any
homomorphism into `SL(2, ℤ)` acting on `OnePoint ℝ` or `OnePoint ℂ` — preserving a Borel
probability measure on `OnePoint 𝕜` is amenable for every group topology: a measure with no point
masses forces the group to be finite, while a point mass has a finite orbit and therefore a
finite-index amenable stabilizer.

## Main definitions

* `OnePoint.ofVec`: homogeneous-coordinate projection `(Fin 2 → K) → OnePoint K`, agreeing with
  `OnePoint.equivProjectivization` away from zero.

## Main results

* `OnePoint.exists_tendsto_smul_of_det_eq_zero`: entrywise convergence in `GL(2, 𝕜)` to a nonzero
  singular matrix contracts the complement of one point of `OnePoint 𝕜` to a single point.
* `OnePoint.exists_norm_le_of_measure_singleton_eq_zero`: Furstenberg's lemma for `SL(2, 𝕜)`
  acting on `OnePoint 𝕜`.
* `MonoidHom.amenable_of_map_smul_onePoint_eq_of_finite_preimage`,
  `MonoidHom.amenable_range_of_map_smul_onePoint_eq`, and
  `MonoidHom.amenable_of_map_smul_onePoint_eq`: amenability for every group topology from an
  invariant Borel probability measure on `OnePoint 𝕜`.

## References

* H. Furstenberg, *A Poisson formula for semi-simple Lie groups*, Ann. of Math. (2) 77 (1963),
  335–386.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), §1.4.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

open Filter Matrix MeasureTheory MulAction Set Topology
open scoped MatrixGroups OnePoint

namespace OnePoint

/-! ### Homogeneous coordinates on the projective line -/

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Homogeneous-coordinate projection from `K²` to the projective line `OnePoint K`, sending
`v` to `v 0 / v 1` when `v 1 ≠ 0` and to `∞` when `v 1 = 0`. Away from `0` this agrees with
`OnePoint.equivProjectivization`. -/
def ofVec (v : Fin 2 → K) : OnePoint K :=
  if v 1 = 0 then ∞ else (v 0 / v 1 : K)

/-- Away from zero, `ofVec` agrees with `OnePoint.equivProjectivization`. -/
theorem ofVec_eq_equivProjectivization_symm_mk {v : Fin 2 → K} (hv : v ≠ 0) :
    ofVec v = (equivProjectivization K).symm (.mk K v hv) := by
  rw [equivProjectivization_symm_apply_mk, ofVec, div_eq_inv_mul]

/-- The zero vector maps to infinity. -/
@[simp]
theorem ofVec_zero : ofVec (0 : Fin 2 → K) = ∞ := by
  simp [ofVec]

/-- Scaling by a nonzero scalar preserves `ofVec`. -/
theorem ofVec_smul {c : K} (hc : c ≠ 0) (v : Fin 2 → K) : ofVec (c • v) = ofVec v := by
  simp only [ofVec, Pi.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]
  split_ifs with h
  · rfl
  · rw [mul_div_mul_left _ _ hc]

/-- Matrix multiplication intertwines `ofVec` with the Möbius action of `GL(2, K)` on nonzero
vectors. -/
theorem ofVec_mulVec (g : GL (Fin 2) K) {v : Fin 2 → K} (hv : v ≠ 0) :
    ofVec ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = g • ofVec v := by
  have hgv : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v ≠ 0 := by
    intro h
    apply hv
    have hmul : (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) = 0 := by
      rw [h, mulVec_zero]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at hmul
    exact hmul
  rw [ofVec_eq_equivProjectivization_symm_mk hgv, ofVec_eq_equivProjectivization_symm_mk hv]
  apply (equivProjectivization K).injective
  rw [equivProjectivization_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- Every point of the projective line is represented by a nonzero vector. -/
theorem exists_ofVec_eq (x : OnePoint K) : ∃ v : Fin 2 → K, v ≠ 0 ∧ ofVec v = x := by
  induction x using OnePoint.rec with
  | infty => exact ⟨![1, 0], by simp, by simp [ofVec]⟩
  | coe t => exact ⟨![t, 1], by simp, by simp [ofVec]⟩

/-- Two nonzero vectors represent the same point of `OnePoint K` iff they are proportional. -/
theorem ofVec_eq_ofVec_iff {u v : Fin 2 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ofVec u = ofVec v ↔ u 0 * v 1 = u 1 * v 0 := by
  by_cases hu1 : u 1 = 0 <;> by_cases hv1 : v 1 = 0
  · simp [ofVec, hu1, hv1]
  · have hu0 : u 0 ≠ 0 := fun h0 => hu (funext fun i => by fin_cases i <;> assumption)
    simp [ofVec, hu1, hv1, hu0]
  · have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i <;> assumption)
    simp [ofVec, hu1, hv1, hv0]
  · simp only [ofVec, hu1, hv1, ↓reduceIte, OnePoint.coe_eq_coe, div_eq_div_iff hu1 hv1]
    constructor <;> intro h <;> linear_combination h

/-- `ofVec v` equals `∞` if and only if the second coordinate vanishes. -/
@[simp]
theorem ofVec_eq_infty_iff (v : Fin 2 → K) : ofVec v = ∞ ↔ v 1 = 0 := by
  simp [ofVec]

/-- The homogeneous-coordinate projection is measurable for Borel structures on `K` and
`OnePoint K`. -/
@[fun_prop]
theorem measurable_ofVec [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    [MeasurableDiv₂ K] [MeasurableSingletonClass K]
    [MeasurableSpace (OnePoint K)] [BorelSpace (OnePoint K)] :
    Measurable (ofVec : (Fin 2 → K) → OnePoint K) := by
  refine Measurable.ite ?_ measurable_const ?_
  · exact (measurable_pi_apply 1) (measurableSet_singleton 0)
  · exact OnePoint.continuous_coe.measurable.comp
      ((measurable_pi_apply 0).div (measurable_pi_apply 1))

end Field

/-! ### Continuity and contraction on the projective line -/

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] [DecidableEq 𝕜]

/-- Away from zero, the homogeneous-coordinate projection is continuous. -/
theorem continuousAt_ofVec {v : Fin 2 → 𝕜} (hv : v ≠ 0) : ContinuousAt ofVec v := by
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i <;> assumption)
    simp only [ContinuousAt, ofVec, hv1, ↓reduceIte]
    rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
    rintro K ⟨-, hK⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : 𝕜)
    have _ : 0 ≤ max R 0 := le_max_right R 0
    have hpos : 0 < ‖v 0‖ / (2 * (max R 0 + 1)) := by positivity
    have h0 : ∀ᶠ w : Fin 2 → 𝕜 in 𝓝 v, ‖v 0‖ / 2 < ‖w 0‖ :=
      ((continuous_apply 0).norm.tendsto v).eventually
        (lt_mem_nhds (half_lt_self (norm_pos_iff.2 hv0)))
    have h1 : ∀ᶠ w : Fin 2 → 𝕜 in 𝓝 v, ‖w 1‖ < ‖v 0‖ / (2 * (max R 0 + 1)) := by
      have ht : Tendsto (fun w : Fin 2 → 𝕜 => ‖w 1‖) (𝓝 v) (𝓝 0) := by
        simpa [hv1] using (continuous_apply 1).norm.tendsto v
      exact ht.eventually (gt_mem_nhds hpos)
    filter_upwards [h0, h1] with w hw0 hw1
    rw [← OnePoint.compl_image_coe]
    simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, ofVec]
    split_ifs with hw1z
    · intro x _; exact OnePoint.coe_ne_infty x
    · intro x hx hxeq
      have hxw : x = w 0 / w 1 := OnePoint.coe_injective hxeq
      have hxnorm : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
      have hnorm_gt : max R 0 + 1 < ‖w 0 / w 1‖ := by
        rw [norm_div, lt_div_iff₀ (norm_pos_iff.2 hw1z)]
        have hmul : (max R 0 + 1) * ‖w 1‖ < (max R 0 + 1) * (‖v 0‖ / (2 * (max R 0 + 1))) :=
          mul_lt_mul_of_pos_left hw1 (by positivity)
        have hsimp : (max R 0 + 1) * (‖v 0‖ / (2 * (max R 0 + 1))) = ‖v 0‖ / 2 := by
          field_simp
        linarith
      linarith [hxw ▸ hxnorm, le_max_left R 0]
  · have hev : ∀ᶠ w : Fin 2 → 𝕜 in 𝓝 v, ofVec w = ((w 0 / w 1 : 𝕜) : OnePoint 𝕜) := by
      filter_upwards [((continuous_apply 1).tendsto v).eventually_ne hv1] with w hw
      simp [ofVec, hw]
    exact ContinuousAt.congr
      (OnePoint.continuous_coe.continuousAt.comp
        ((continuous_apply 0).continuousAt.div (continuous_apply 1).continuousAt hv1))
      (hev.mono fun _ => Eq.symm)

/-- Every nonzero singular `2 × 2` matrix over a field factors as an outer product `u ⊗ w`. -/
private theorem exists_outer_product_of_det_eq_zero {K : Type*} [Field K]
    {M : Matrix (Fin 2) (Fin 2) K} (hM : M ≠ 0) (hdet : M.det = 0) :
    ∃ u w : Fin 2 → K, u ≠ 0 ∧ w ≠ 0 ∧ ∀ v : Fin 2 → K, M *ᵥ v = (w ⬝ᵥ v) • u := by
  have hex : ∃ i₀ j₀ : Fin 2, M i₀ j₀ ≠ 0 := by
    by_contra! h
    exact hM (Matrix.ext fun i j => h i j)
  obtain ⟨i₀, j₀, h0⟩ := hex
  refine ⟨fun i => M i j₀, fun j => M i₀ j / M i₀ j₀,
    fun hu => h0 (congrFun hu i₀),
    fun hw => (one_ne_zero (α := K)) (by simpa [h0] using congrFun hw j₀),
    fun v => funext fun i => ?_⟩
  have hmul (j : Fin 2) : M i j = M i j₀ * (M i₀ j / M i₀ j₀) := by
    rw [Matrix.det_fin_two] at hdet
    fin_cases i₀ <;> fin_cases j₀ <;> fin_cases i <;> fin_cases j <;>
      dsimp only [Fin.zero_eta, Fin.mk_one] at h0 ⊢ <;>
      field_simp [h0]
    · linear_combination hdet
    · linear_combination -hdet
    · linear_combination -hdet
    · linear_combination hdet
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  rw [hmul 0, hmul 1]
  ring

/-- **Projective contraction.** If `M` is a nonzero singular `2 × 2` matrix, there exist points
`a, b ∈ OnePoint 𝕜` such that every net in `GL(2, 𝕜)` converging entrywise to `M` carries every
point `x ≠ a` to `b`. -/
theorem exists_tendsto_smul_of_det_eq_zero {M : Matrix (Fin 2) (Fin 2) 𝕜} (hM : M ≠ 0)
    (hdet : M.det = 0) :
    ∃ a b : OnePoint 𝕜, ∀ {ι : Type*} {l : Filter ι} {A : ι → GL (Fin 2) 𝕜},
      Tendsto (fun i => (A i : Matrix (Fin 2) (Fin 2) 𝕜)) l (𝓝 M) →
      ∀ x : OnePoint 𝕜, x ≠ a → Tendsto (fun i => A i • x) l (𝓝 b) := by
  obtain ⟨u, w, hu, hw, hMu⟩ := exists_outer_product_of_det_eq_zero hM hdet
  let k : Fin 2 → 𝕜 := ![w 1, -w 0]
  have hk : k ≠ 0 := fun h => hw (funext fun j => by
    fin_cases j
    · simpa [k] using congrFun h 1
    · simpa [k] using congrFun h 0)
  refine ⟨ofVec k, ofVec u, fun {ι l A} hA x hx => ?_⟩
  obtain ⟨v, hv, rfl⟩ := exists_ofVec_eq x
  have hwv : w ⬝ᵥ v ≠ 0 := by
    intro hdot
    apply hx
    rw [ofVec_eq_ofVec_iff hv hk]
    simp only [dotProduct, Fin.sum_univ_two] at hdot
    simp only [k, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination -hdot
  have hMv : M *ᵥ v ≠ 0 := by
    rw [hMu]
    exact smul_ne_zero hwv hu
  have hval : ofVec (M *ᵥ v) = ofVec u := by
    rw [hMu, ofVec_smul hwv]
  have htvec : Tendsto (fun i => (A i : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ v) l (𝓝 (M *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto M).comp hA
  have htproj := (continuousAt_ofVec hMv).tendsto.comp htvec
  rw [hval] at htproj
  refine htproj.congr fun i => ?_
  exact ofVec_mulVec (A i) hv

/-- Given a sequence in `SL(2, 𝕜)` with unbounded entries, construct rescaled matrices in `GL(2, 𝕜)`
in the unit polydisc acting identically on `OnePoint 𝕜`, each having an entry of norm `1` and
determinant tending to `0`. -/
private theorem exists_rescaled_of_unbounded {g : ℕ → SL(2, 𝕜)}
    (hunb : ∀ C : ℝ, ∃ n i j, C < ‖(g n : Matrix (Fin 2) (Fin 2) 𝕜) i j‖) :
    ∃ (B : ℕ → GL (Fin 2) 𝕜) (k : ℕ → ℕ),
      (∀ n i j, ‖(B n : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ ≤ 1) ∧
      (∀ n, ∃ i j, ‖(B n : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ = 1) ∧
      (∀ n (x : OnePoint 𝕜), B n • x = (g (k n) : GL (Fin 2) 𝕜) • x) ∧
      Tendsto (fun n => ((B n : Matrix (Fin 2) (Fin 2) 𝕜)).det) atTop (𝓝 0) := by
  have hsub (n : ℕ) : ∃ m : ℕ, ∃ p : Fin 2 × Fin 2,
      (n + 1 : ℝ) < ‖(g m : Matrix (Fin 2) (Fin 2) 𝕜) p.1 p.2‖ := by
    obtain ⟨m, i, j, hm⟩ := hunb (n + 1)
    exact ⟨m, (i, j), hm⟩
  choose k pk hpk using hsub
  have hmax (n : ℕ) : ∃ q : Fin 2 × Fin 2, ∀ p : Fin 2 × Fin 2,
      ‖(g (k n) : Matrix (Fin 2) (Fin 2) 𝕜) p.1 p.2‖ ≤
        ‖(g (k n) : Matrix (Fin 2) (Fin 2) 𝕜) q.1 q.2‖ := by
    obtain ⟨q, -, hq⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
      (fun p => ‖(g (k n) : Matrix (Fin 2) (Fin 2) 𝕜) p.1 p.2‖) Finset.univ_nonempty
    exact ⟨q, fun p => hq p (Finset.mem_univ p)⟩
  choose q hq using hmax
  let c (n : ℕ) : 𝕜 := (g (k n) : Matrix (Fin 2) (Fin 2) 𝕜) (q n).1 (q n).2
  have hc_gt (n : ℕ) : (n + 1 : ℝ) < ‖c n‖ := (hpk n).trans_le (hq n (pk n))
  have hc_ne (n : ℕ) : c n ≠ 0 := norm_pos_iff.1 ((by positivity : (0 : ℝ) < n + 1).trans (hc_gt n))
  let B (n : ℕ) : GL (Fin 2) 𝕜 :=
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c n)⁻¹ (inv_ne_zero (hc_ne n))) *
      (g (k n) : GL (Fin 2) 𝕜)
  have hB_entry (n : ℕ) (i j : Fin 2) :
      (B n : Matrix (Fin 2) (Fin 2) 𝕜) i j =
        (c n)⁻¹ * (g (k n) : Matrix (Fin 2) (Fin 2) 𝕜) i j := by
    simp [B, Matrix.scalar_apply]
  refine ⟨B, k, fun n i j => ?_, fun n => ?_, fun n x => ?_, ?_⟩
  · rw [hB_entry, norm_mul, norm_inv]
    exact (inv_mul_le_one₀ (norm_pos_iff.2 (hc_ne n))).2 (hq n (i, j))
  · exact ⟨(q n).1, (q n).2, by rw [hB_entry, inv_mul_cancel₀ (hc_ne n), norm_one]⟩
  · rw [mul_smul, TauCeti.scalar_smul_onePoint_eq_self]
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmat : (B n : Matrix (Fin 2) (Fin 2) 𝕜) =
        (c n)⁻¹ • (g (k n) : Matrix (Fin 2) (Fin 2) 𝕜) := by ext i j; exact hB_entry n i j
    rw [hmat, Matrix.det_smul, Fintype.card_fin, (g (k n)).det_coe, mul_one, norm_pow, norm_inv]
    have h1 : (n + 1 : ℝ) ≤ ‖c n‖ ^ 2 := by
      have hlt := (hc_gt n).le
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa [one_div, inv_pow] using inv_anti₀ (by positivity) h1

/-! ### Invariant Borel probability measures and Furstenberg's lemma -/

section ProperField

variable [ProperSpace 𝕜]

/-- Extracting a convergent subsequence from `exists_rescaled_of_unbounded` yields a nonzero
singular cluster point in `M₂(𝕜)`. -/
private theorem exists_tendsto_of_unbounded {g : ℕ → SL(2, 𝕜)}
    (hunb : ∀ C : ℝ, ∃ n i j, C < ‖(g n : Matrix (Fin 2) (Fin 2) 𝕜) i j‖) :
    ∃ (A : ℕ → GL (Fin 2) 𝕜) (φ : ℕ → ℕ) (M : Matrix (Fin 2) (Fin 2) 𝕜),
      M ≠ 0 ∧ M.det = 0 ∧
      (∀ n (x : OnePoint 𝕜), A n • x = (g (φ n) : GL (Fin 2) 𝕜) • x) ∧
      Tendsto (fun n => (A n : Matrix (Fin 2) (Fin 2) 𝕜)) atTop (𝓝 M) := by
  obtain ⟨B, k, hBle, hBone, hBsmul, hBdet⟩ := exists_rescaled_of_unbounded hunb
  have hcomp : IsCompact (Set.univ.pi (fun _ : Fin 2 =>
      Set.univ.pi (fun _ : Fin 2 => Metric.closedBall (0 : 𝕜) 1))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : 𝕜) 1
  obtain ⟨(M : Matrix (Fin 2) (Fin 2) 𝕜), -, σ, hσ, hMlim⟩ := hcomp.isSeqCompact fun n i _ j _ => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hBle n i j
  have hent (i j : Fin 2) : Continuous fun A : Matrix (Fin 2) (Fin 2) 𝕜 => A i j :=
    (continuous_apply j).comp (continuous_apply i)
  have hMne : M ≠ 0 := by
    intro hM0
    let s : Matrix (Fin 2) (Fin 2) 𝕜 → ℝ := fun A =>
      ‖A 0 0‖ + ‖A 0 1‖ + ‖A 1 0‖ + ‖A 1 1‖
    have hs : Continuous s :=
      ((((hent 0 0).norm.add (hent 0 1).norm).add (hent 1 0).norm).add (hent 1 1).norm)
    have hnorm : Tendsto (fun n => s (B (σ n) : Matrix (Fin 2) (Fin 2) 𝕜)) atTop (𝓝 0) := by
      have h := (hs.tendsto M).comp hMlim
      rwa [show s M = 0 by simp [s, hM0]] at h
    have hge (n : ℕ) : (1 : ℝ) ≤ s (B (σ n) : Matrix (Fin 2) (Fin 2) 𝕜) := by
      obtain ⟨i₀, j₀, h1⟩ := hBone (σ n)
      dsimp only [s]
      fin_cases i₀ <;> fin_cases j₀ <;>
        dsimp only [Fin.zero_eta, Fin.mk_one] at h1 <;>
        linarith [h1, norm_nonneg ((B (σ n) : Matrix (Fin 2) (Fin 2) 𝕜) 0 0),
          norm_nonneg ((B (σ n) : Matrix (Fin 2) (Fin 2) 𝕜) 0 1),
          norm_nonneg ((B (σ n) : Matrix (Fin 2) (Fin 2) 𝕜) 1 0),
          norm_nonneg ((B (σ n) : Matrix (Fin 2) (Fin 2) 𝕜) 1 1)]
    linarith [ge_of_tendsto' hnorm hge]
  have hMdet : M.det = 0 := by
    have hcdet : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) 𝕜 → 𝕜) :=
      (((hent 0 0).mul (hent 1 1)).sub ((hent 0 1).mul (hent 1 0))).congr
        fun A => (Matrix.det_fin_two A).symm
    exact tendsto_nhds_unique ((hcdet.tendsto M).comp hMlim) (hBdet.comp hσ.tendsto_atTop)
  exact ⟨fun n => B (σ n), fun n => k (σ n), M, hMne, hMdet, fun n x => hBsmul (σ n) x, hMlim⟩

end ProperField

end NormedField

section Measure

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]
  [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]

/-- Under a sequence preserving `ν` and contracting `{a}ᶜ` to `b`, every open neighbourhood of `b`
has measure `1` whenever `ν {a} = 0`. -/
private theorem measure_isOpen_eq_one_of_tendsto_smul {ν : Measure (OnePoint 𝕜)}
    [IsProbabilityMeasure ν] {A : ℕ → GL (Fin 2) 𝕜} {a b : OnePoint 𝕜}
    (hinv : ∀ n, Measure.map (A n • ·) ν = ν)
    (hlim : ∀ x : OnePoint 𝕜, x ≠ a → Tendsto (fun n => A n • x) atTop (𝓝 b))
    (ha : ν {a} = 0) {U : Set (OnePoint 𝕜)} (hU : IsOpen U) (hbU : b ∈ U) : ν U = 1 := by
  have hae : ∀ᵐ x ∂ν, Tendsto (fun n => U.indicator (1 : OnePoint 𝕜 → ℝ) (A n • x))
      atTop (𝓝 1) := by
    have hne : ∀ᵐ x ∂ν, x ≠ a := by simpa [ae_iff] using ha
    filter_upwards [hne] with x hx
    exact tendsto_const_nhds.congr' <| ((hlim x hx).eventually (hU.mem_nhds hbU)).mono
      fun n hn => by simp [Set.indicator_of_mem hn]
  have hint (n : ℕ) :
      ∫ x, U.indicator (1 : OnePoint 𝕜 → ℝ) (A n • x) ∂ν = ν.real U := by
    have hm : Measurable (fun x : OnePoint 𝕜 => A n • x) := (continuous_const_smul (A n)).measurable
    have hf : AEStronglyMeasurable (U.indicator (1 : OnePoint 𝕜 → ℝ))
        (Measure.map (A n • ·) ν) :=
      (measurable_const.indicator hU.measurableSet).aestronglyMeasurable
    rw [← MeasureTheory.integral_map hm.aemeasurable hf, hinv n,
      MeasureTheory.integral_indicator_one hU.measurableSet]
  have htend := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun n x => U.indicator (1 : OnePoint 𝕜 → ℝ) (A n • x)) (fun _ => (1 : ℝ))
    (fun n => ((measurable_const.indicator hU.measurableSet).comp
      (continuous_const_smul (A n)).measurable).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => .of_forall fun x => by
      by_cases hx : A n • x ∈ U
      · rw [Set.indicator_of_mem hx, Pi.one_apply, norm_one]
      · rw [Set.indicator_of_notMem hx, norm_zero]; exact zero_le_one)
    hae
  have hreal : ν.real U = 1 := by
    simp_rw [hint] at htend
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at htend
    have htend' : Tendsto (fun _ : ℕ => ν.real U) atTop (𝓝 1) := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using htend
    exact tendsto_nhds_unique tendsto_const_nhds htend'
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν U), ← measureReal_def, hreal, ENNReal.ofReal_one]

/-- If a Borel probability measure `ν` on `OnePoint 𝕜` is preserved by a sequence `A : ℕ → GL(2, 𝕜)`
contracting `{a}ᶜ` to `b`, and `ν {a} = 0`, then `ν` is the Dirac mass at `b`. -/
private theorem measure_eq_dirac_of_tendsto_smul {ν : Measure (OnePoint 𝕜)} [IsProbabilityMeasure ν]
    {A : ℕ → GL (Fin 2) 𝕜} {a b : OnePoint 𝕜}
    (hinv : ∀ n, Measure.map (A n • ·) ν = ν)
    (hlim : ∀ x : OnePoint 𝕜, x ≠ a → Tendsto (fun n => A n • x) atTop (𝓝 b))
    (ha : ν {a} = 0) : ν = Measure.dirac b := by
  obtain ⟨U, hUb⟩ := Filter.exists_antitone_basis (𝓝 b)
  have hcompl_eq : ({b}ᶜ : Set (OnePoint 𝕜)) = ⋃ m : ℕ, (interior (U m))ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion]
    refine ⟨fun hx => ?_, fun ⟨m, hm⟩ hxb => hm (hxb ▸ mem_interior_iff_mem_nhds.2 (hUb.mem m))⟩
    obtain ⟨V, W, hVopen, _, hbV, hxW, hVW⟩ := t2_separation (Ne.symm hx)
    obtain ⟨m, -, hm⟩ := hUb.toHasBasis.mem_iff.1 (hVopen.mem_nhds hbV)
    exact ⟨m, fun h => hVW.le_bot ⟨hm (interior_subset h), hxW⟩⟩
  have hcompl_zero : ν {b}ᶜ = 0 := by
    rw [hcompl_eq]
    refine measure_iUnion_null fun m => ?_
    have hfull : ν (interior (U m)) = 1 :=
      measure_isOpen_eq_one_of_tendsto_smul hinv hlim ha isOpen_interior
        (mem_interior_iff_mem_nhds.2 (hUb.mem m))
    have hadd := measure_add_measure_compl (μ := ν) (s := interior (U m))
      isOpen_interior.measurableSet
    rw [hfull, measure_univ] at hadd
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (by simpa using hadd)
  ext E hE
  rw [Measure.dirac_apply' b hE]
  by_cases hbE : b ∈ E
  · have hEc : ν Eᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hbE)) hcompl_zero
    have hadd := measure_add_measure_compl (μ := ν) hE
    rw [hEc, add_zero, measure_univ] at hadd
    simpa [hbE] using hadd
  · have hsub : E ⊆ {b}ᶜ := fun x hx hxb => hbE (hxb ▸ hx)
    simpa [hbE] using measure_mono_null hsub hcompl_zero

end Measure

/-- **Furstenberg's lemma** for `SL(2, 𝕜)` acting on the projective line `OnePoint 𝕜`: any set of
matrices in `SL(2, 𝕜)` preserving a Borel probability measure on `OnePoint 𝕜` without point masses
has uniformly bounded matrix entries. -/
theorem exists_norm_le_of_measure_singleton_eq_zero
    {𝕜 : Type*} [NormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]
    [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]
    {ν : Measure (OnePoint 𝕜)} [IsProbabilityMeasure ν] (hno : ∀ x : OnePoint 𝕜, ν {x} = 0)
    {S : Set SL(2, 𝕜)}
    (hinv : ∀ g ∈ S, Measure.map ((g : GL (Fin 2) 𝕜) • ·) ν = ν) :
    ∃ C : ℝ, ∀ g ∈ S, ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ ≤ C := by
  by_cases hnt : ∃ x : 𝕜, 1 < ‖x‖
  · let : NontriviallyNormedField 𝕜 := ⟨hnt⟩
    by_contra! hunb
    have hex (n : ℕ) : ∃ g ∈ S, ∃ i j : Fin 2,
        (n : ℝ) < ‖(g : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ := hunb n
    choose g hg ig jg hng using hex
    have hunb_seq (C : ℝ) : ∃ n i j, C < ‖(g n : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ := by
      obtain ⟨n, hn⟩ := exists_nat_gt C
      exact ⟨n, ig n, jg n, hn.trans (hng n)⟩
    obtain ⟨A, φ, M, hMne, hMdet, hAsmul, hAlim⟩ := exists_tendsto_of_unbounded hunb_seq
    obtain ⟨a, b, hcontr⟩ := exists_tendsto_smul_of_det_eq_zero hMne hMdet
    have hAinv (n : ℕ) : Measure.map (A n • ·) ν = ν := by
      have hfun : (fun x : OnePoint 𝕜 => A n • x) =
          fun x => (g (φ n) : GL (Fin 2) 𝕜) • x := funext (hAsmul n)
      rw [hfun]
      exact hinv (g (φ n)) (hg (φ n))
    have hdirac : ν = Measure.dirac b :=
      measure_eq_dirac_of_tendsto_smul hAinv (hcontr hAlim) (hno a)
    have hzero : ν {b} = 0 := hno b
    rw [hdirac, Measure.dirac_apply' b (measurableSet_singleton b)] at hzero
    simp at hzero
  · push Not at hnt
    exact ⟨1, fun g _ i j => hnt _⟩

end OnePoint

/-! ### Amenability from an invariant Borel probability measure on the projective line -/

namespace MonoidHom

/-- If a group acts by measurable bijections preserving a finite measure, every atom has a finite
orbit. -/
private theorem finite_orbit_of_measure_singleton_ne_zero {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {ν : Measure X} [IsFiniteMeasure ν]
    (hmeas : ∀ g : G, Measurable (fun z : X => g • z))
    (hinv : ∀ g : G, Measure.map (fun z : X => g • z) ν = ν)
    {x : X} (hx : ν {x} ≠ 0) : (Set.range fun g : G => g • x).Finite := by
  have hconst : ∀ y ∈ Set.range (fun g : G => g • x), ν.real {y} = ν.real {x} := by
    rintro _ ⟨g, rfl⟩
    have hpre : (fun z : X => g • z) ⁻¹' {g • x} = {x} := by
      ext z; simp
    have hmeas_eq : ν {g • x} = ν {x} := by
      conv_lhs => rw [← hinv g]
      rw [Measure.map_apply (hmeas g) (measurableSet_singleton _), hpre]
    simp [measureReal_def, hmeas_eq]
  have hpos : 0 < ν.real {x} := ENNReal.toReal_pos hx (measure_ne_top ν {x})
  by_contra hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (ν.real Set.univ / ν.real {x})
  obtain ⟨F, hFO, hFcard⟩ := (Set.not_finite.1 hinf).exists_subset_card_eq N
  have hsum : ∑ y ∈ F, ν.real {y} = ν.real (F : Set X) := by
    have hdisj : Set.PairwiseDisjoint (F : Set X) (fun y => ({y} : Set X)) := by
      intro a _ b _ hab
      exact Set.disjoint_singleton.2 hab
    have h := measureReal_biUnion_finset (μ := ν) hdisj (fun y _ => measurableSet_singleton y)
    have hU : (⋃ y ∈ F, ({y} : Set X)) = (F : Set X) := by ext z; simp
    rw [hU] at h
    exact h.symm
  have hle : (N : ℝ) * ν.real {x} ≤ ν.real Set.univ := by
    calc (N : ℝ) * ν.real {x} = ∑ _ ∈ F, ν.real {x} := by simp [hFcard]
      _ = ∑ y ∈ F, ν.real {y} := Finset.sum_congr rfl fun y hy => (hconst y (hFO hy)).symm
      _ = ν.real (F : Set X) := hsum
      _ ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hlt : ν.real Set.univ < (N : ℝ) * ν.real {x} := (div_lt_iff₀ hpos).1 hN
  linarith

/-- If a group embeds into `GL(2, K)` and fixes a point of `OnePoint K` up to a finite orbit,
then the group is amenable for every group topology. -/
private theorem amenable_of_finite_orbit_onePoint {K G : Type*} [Field K] [DecidableEq K]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ψ : G →* GL (Fin 2) K) (hψ : Function.Injective ψ)
    {x : OnePoint K} (hfin : (Set.range fun g : G => ψ g • x).Finite) :
    TauCeti.Amenable G := by
  apply TauCeti.Amenable.of_discrete
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let O := Set.range fun g : G => ψ g • x
  have : Finite O := hfin.to_subtype
  let : TopologicalSpace (Equiv.Perm O) := ⊥
  let : DiscreteTopology (Equiv.Perm O) := ⟨rfl⟩
  let α : G →* Equiv.Perm O :=
    { toFun g :=
        { toFun y := ⟨ψ g • y.1, by
            rcases y.2 with ⟨h, hh⟩
            exact ⟨g * h, by simp [map_mul, mul_smul, ← hh]⟩⟩
          invFun y := ⟨ψ g⁻¹ • y.1, by
            rcases y.2 with ⟨h, hh⟩
            exact ⟨g⁻¹ * h, by simp [map_mul, mul_smul, ← hh]⟩⟩
          left_inv y := Subtype.ext (by simp [← mul_smul])
          right_inv y := Subtype.ext (by simp [← mul_smul]) }
      map_one' := by ext y; simp
      map_mul' g h := by ext y; simp [mul_smul] }
  have hker : α.ker ≤ (stabilizer (GL (Fin 2) K) x).comap ψ := by
    intro g hg
    have hx : x ∈ O := ⟨1, by simp⟩
    have hfix := congrArg Subtype.val (Equiv.Perm.ext_iff.1 (MonoidHom.mem_ker.1 hg) ⟨x, hx⟩)
    simpa [α, MulAction.mem_stabilizer_iff] using hfix
  have hstab : TauCeti.Amenable ((stabilizer (GL (Fin 2) K) x).comap ψ) :=
    ψ.amenable_comap_onePoint_stabilizer hψ x
  have : TauCeti.Amenable α.ker :=
    TauCeti.Amenable.of_injective (Subgroup.inclusion hker) (Subgroup.inclusion_injective hker)
  have : TauCeti.Amenable (Equiv.Perm O) := TauCeti.Amenable.of_finite
  exact TauCeti.Amenable.of_ker_le_range α.ker.subtype α (by simp)

/-- A group with a proper homomorphism into `SL(2, 𝕜)` (over a proper normed field `𝕜`, meaning
bounded matrix sets have finite preimages) whose Möbius action on `OnePoint 𝕜` preserves a Borel
probability measure is amenable for every group topology. -/
theorem amenable_of_map_smul_onePoint_eq_of_finite_preimage
    {𝕜 G : Type*} [NormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]
    [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* SL(2, 𝕜))
    (hfin : ∀ C : ℝ, {g : G | ∀ i j, ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ ≤ C}.Finite)
    {ν : Measure (OnePoint 𝕜)} [IsProbabilityMeasure ν]
    (hinv : ∀ g : G, Measure.map ((φ g : GL (Fin 2) 𝕜) • ·) ν = ν) :
    TauCeti.Amenable G := by
  by_cases hnt : ∃ x : 𝕜, 1 < ‖x‖
  · let : NontriviallyNormedField 𝕜 := ⟨hnt⟩
    by_cases hatom : ∃ x : OnePoint 𝕜, ν {x} ≠ 0
    · obtain ⟨x, hx⟩ := hatom
      apply TauCeti.Amenable.of_discrete
      let : TopologicalSpace G := ⊥
      let : DiscreteTopology G := ⟨rfl⟩
      let : TopologicalSpace φ.range := ⊥
      let : DiscreteTopology φ.range := ⟨rfl⟩
      have hker_fin : (φ.ker : Set G).Finite := (hfin 1).subset fun g hg i j => by
        have h1 : (φ g : Matrix (Fin 2) (Fin 2) 𝕜) = 1 := congrArg Subtype.val hg
        rw [h1]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have : Finite φ.ker := hker_fin.to_subtype
      have : TauCeti.Amenable φ.ker := TauCeti.Amenable.of_finite
      let ψ : φ.range →* GL (Fin 2) 𝕜 := Matrix.SpecialLinearGroup.toGL.comp φ.range.subtype
      have hψ : Function.Injective ψ := fun a b hab =>
        Subtype.ext (Subtype.ext (by simpa [ψ] using congrArg Units.val hab))
      have hinv_range : ∀ k : φ.range, Measure.map (ψ k • ·) ν = ν := by
        rintro ⟨_, g, rfl⟩
        exact hinv g
      let : MulAction φ.range (OnePoint 𝕜) := MulAction.compHom (OnePoint 𝕜) ψ
      have hfinO : (Set.range fun k : φ.range => ψ k • x).Finite :=
        finite_orbit_of_measure_singleton_ne_zero (G := φ.range) (X := OnePoint 𝕜) (ν := ν)
          (fun k => (continuous_const_smul (ψ k)).measurable) hinv_range hx
      have : TauCeti.Amenable φ.range := amenable_of_finite_orbit_onePoint ψ hψ hfinO
      exact TauCeti.Amenable.of_ker_le_range φ.ker.subtype φ.rangeRestrict fun g hg => by
        simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hg
    · push Not at hatom
      obtain ⟨C, hC⟩ := OnePoint.exists_norm_le_of_measure_singleton_eq_zero (ν := ν) hatom
        (S := Set.range φ) (by rintro _ ⟨g, rfl⟩; exact hinv g)
      have huniv : (Set.univ : Set G).Finite :=
        (hfin C).subset fun g _ i j => hC (φ g) ⟨g, rfl⟩ i j
      have : Finite G := Set.finite_univ_iff.1 huniv
      exact TauCeti.Amenable.of_finite
  · push Not at hnt
    have huniv : (Set.univ : Set G).Finite := (hfin 1).subset fun _ _ _ _ => hnt _
    have : Finite G := Set.finite_univ_iff.1 huniv
    exact TauCeti.Amenable.of_finite

/-- For any homomorphism `φ : G →* SL(2, ℤ)` whose Möbius action on `OnePoint 𝕜` (`𝕜 = ℝ` or `ℂ`)
preserves a Borel probability measure, the image `φ.range` is amenable for every group topology. -/
theorem amenable_range_of_map_smul_onePoint_eq
    {𝕜 G : Type*} [RCLike 𝕜] [DecidableEq 𝕜]
    [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]
    [Group G] (φ : G →* SL(2, ℤ))
    [TopologicalSpace φ.range] [IsTopologicalGroup φ.range]
    {ν : Measure (OnePoint 𝕜)} [IsProbabilityMeasure ν]
    (hinv : ∀ g : G, Measure.map (Matrix.SpecialLinearGroup.mapGL 𝕜 (φ g) • ·) ν = ν) :
    TauCeti.Amenable φ.range := by
  let ψ : φ.range →* SL(2, 𝕜) :=
    (Matrix.SpecialLinearGroup.map (Int.castRingHom 𝕜)).comp φ.range.subtype
  have hfin (C : ℝ) :
      {k : φ.range | ∀ i j, ‖(ψ k : Matrix (Fin 2) (Fin 2) 𝕜) i j‖ ≤ C}.Finite := by
    let B : Set (Matrix (Fin 2) (Fin 2) ℤ) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (⌈-C⌉ : ℤ) ⌊C⌋
    have hB : B.Finite :=
      Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
    refine (hB.preimage fun a _ b _ hab =>
      Subtype.ext (Subtype.ext hab)).subset fun k hk i _ j _ => ?_
    have hij : |((k.1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)| ≤ C := by
      have h : ‖(((k.1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : 𝕜)‖ ≤ C := hk i j
      rwa [← RCLike.ofReal_intCast, RCLike.norm_ofReal] at h
    rw [abs_le] at hij
    exact ⟨Int.ceil_le.2 hij.1, Int.le_floor.2 hij.2⟩
  refine amenable_of_map_smul_onePoint_eq_of_finite_preimage (ν := ν) ψ hfin ?_
  rintro ⟨_, g, rfl⟩
  exact hinv g

/-- A group embedding into `SL(2, ℤ)` whose Möbius action on `OnePoint 𝕜` (`𝕜 = ℝ` or `ℂ`)
preserves a Borel probability measure is amenable for every group topology. -/
theorem amenable_of_map_smul_onePoint_eq
    {𝕜 G : Type*} [RCLike 𝕜] [DecidableEq 𝕜]
    [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* SL(2, ℤ)) (hφ : Function.Injective φ)
    {ν : Measure (OnePoint 𝕜)} [IsProbabilityMeasure ν]
    (hinv : ∀ g : G, Measure.map (Matrix.SpecialLinearGroup.mapGL 𝕜 (φ g) • ·) ν = ν) :
    TauCeti.Amenable G := by
  apply TauCeti.Amenable.of_discrete
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let : TopologicalSpace φ.range := ⊥
  let : DiscreteTopology φ.range := ⟨rfl⟩
  have : TauCeti.Amenable φ.range := amenable_range_of_map_smul_onePoint_eq φ hinv
  exact TauCeti.Amenable.of_injective φ.rangeRestrict
    fun a b hab => hφ (congrArg Subtype.val hab)

end MonoidHom
