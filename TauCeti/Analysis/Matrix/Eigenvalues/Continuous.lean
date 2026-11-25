/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Spectrum

/-!
# Continuity of ordered Hermitian eigenvalues

The decreasing eigenvalue list of a Hermitian matrix is `1`-Lipschitz from the Euclidean
operator norm to the sup norm on the list. In particular it is continuous, including at
repeated eigenvalues, and measurable for the entrywise Borel structure on matrices.
These results allow eigenvalues of a measurable random Hermitian matrix to be treated as
random variables, without choosing measurable eigenvectors.

We use the subtype of Hermitian matrices, with its inherited topology and measurable
structure. For a family of Hermitian matrices, continuity of the entries at a point gives
continuity of the ordered eigenvalues there (`Matrix.continuousAt_eigenvalues₀`), and
differentiability of the entries at a point makes the ordered eigenvalues move by `O(‖x - x₀‖)`
(`Matrix.isBigO_eigenvalues₀_sub`). Along any filter, if `‖A i - B i‖ → 0` in the Euclidean
operator norm for Hermitian `A i` and `B i`, then selected ordered eigenvalues of `A i` converge
to the limit of the corresponding eigenvalues of `B i`
(`Filter.Tendsto.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero`); the sizes may vary. Continuity
uses the usual entrywise topology: Mathlib's Euclidean operator norm induces this same topology.
Empty index types are allowed. On all index types (with value `0` on empty carriers), the extreme
spectral values `sSup (spectrum ℝ A)` and `sInf (spectrum ℝ A)` are continuous and measurable on
the Hermitian subtype (`TauCeti.continuous_sSup_spectrum_real`,
`TauCeti.continuous_sInf_spectrum_real`, `TauCeti.measurable_sSup_spectrum_real`,
`TauCeti.measurable_sInf_spectrum_real`) and a.e. measurable when composed with an a.e. Hermitian
matrix-valued random variable (`TauCeti.aemeasurable_sSup_spectrum_real`,
`TauCeti.aemeasurable_sInf_spectrum_real`).

## References

* R. Bhatia, *Matrix Analysis*, Springer (1997), Chapter III, for Weyl's perturbation bound
  and continuity of ordered eigenvalues.
-/

public section

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator

/-- The decreasing eigenvalue list is `1`-Lipschitz for the Euclidean operator norm on
Hermitian matrices and the sup norm on the eigenvalue list. -/
theorem lipschitzWith_eigenvalues₀ :
    LipschitzWith 1 (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) := by
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    A.property.abs_eigenvalues₀_sub_le_norm B.property i

/-- Ordered Hermitian eigenvalues depend continuously on the matrix, even at repeated
eigenvalues. -/
@[fun_prop]
theorem continuous_eigenvalues₀ :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) :=
  lipschitzWith_eigenvalues₀.continuous

/-- Mathlib's matrix-indexed eigenvalue list is continuous on Hermitian matrices. -/
@[fun_prop]
theorem continuous_eigenvalues :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues) := by
  apply continuous_pi
  intro i
  -- The matrix-indexed list is the sorted list reindexed by a fixed finite equivalence.
  simpa only [IsHermitian.eigenvalues, Function.comp_def] using
    (continuous_apply _).comp (continuous_eigenvalues₀ (n := n) (𝕜 := 𝕜))

/-- The ordered eigenvalues of a family of Hermitian matrices are continuous at every point at
which its entries are, including at repeated eigenvalues. -/
theorem continuousAt_eigenvalues₀ {X : Type*} [TopologicalSpace X] {M : X → Matrix n n 𝕜}
    (hM : ∀ x, (M x).IsHermitian) {x₀ : X} (h : ∀ a b, ContinuousAt (fun x ↦ M x a b) x₀)
    (i : Fin (Fintype.card n)) : ContinuousAt (fun x ↦ (hM x).eigenvalues₀ i) x₀ :=
  ((continuous_apply i).comp continuous_eigenvalues₀).continuousAt.comp
    (f := fun x ↦ (⟨M x, hM x⟩ : {A : Matrix n n 𝕜 // A.IsHermitian}))
    (tendsto_subtype_rng.2 (continuousAt_pi.2 fun a ↦ continuousAt_pi.2 fun b ↦ h a b))

open Asymptotics Filter Finset Topology in
/-- The sorted eigenvalues of a family of Hermitian matrices whose entries are differentiable at
`x₀` move by `O(‖x - x₀‖)`. -/
theorem isBigO_eigenvalues₀_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : E → Matrix n n 𝕜} {x₀ : E} (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) :
    (fun x ↦ (hM x).eigenvalues₀ - (hM x₀).eigenvalues₀) =O[𝓝 x₀] fun x ↦ x - x₀ := by
  set ε : E → ℝ := fun x ↦ ∑ a, ∑ b, ‖M x a b - M x₀ a b‖
  have hεO : ε =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ :=
    IsBigO.fun_sum fun a _ ↦ IsBigO.fun_sum fun b _ ↦
      (hMd a b).hasFDerivAt.isBigO_sub.norm_left.norm_right
  refine IsBigO.of_norm_right (IsBigO.trans ?_ hεO)
  refine IsBigO.of_bound (Fintype.card n) (Eventually.of_forall fun x ↦ ?_)
  have hε : 0 ≤ ε x := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [Real.norm_of_nonneg hε]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  -- Each entry of `M x - M x₀` is bounded by the sum `ε x` of all of them.
  refine (hM x).abs_eigenvalues₀_sub_le_of_entry_le (hM x₀) (fun a b ↦ ?_) i
  exact (single_le_sum (f := fun b ↦ ‖M x a b - M x₀ a b‖) (fun _ _ ↦ norm_nonneg _)
    (mem_univ b)).trans (single_le_sum (f := fun a ↦ ∑ b, ‖M x a b - M x₀ a b‖)
      (fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _) (mem_univ a))

open Filter in
open scoped Topology in
/-- If the selected ordered eigenvalues of `B` converge and `‖A - B‖` tends to zero in
operator norm, the corresponding eigenvalues of `A` converge to the same limit.
The index type may vary. -/
theorem _root_.Filter.Tendsto.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
    {ι : Type*} {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {A B : (i : ι) → Matrix (m i) (m i) 𝕜} {hB : ∀ i, (B i).IsHermitian}
    {j : (i : ι) → Fin (Fintype.card (m i))} {l : Filter ι} {c : ℝ}
    (h : Tendsto (fun i ↦ (hB i).eigenvalues₀ (j i)) l (𝓝 c))
    (hA : ∀ i, (A i).IsHermitian) (hd : Tendsto (fun i ↦ ‖A i - B i‖) l (𝓝 0)) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ (j i)) l (𝓝 c) := by
  apply h.congr_dist
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ ?_) hd
  rw [dist_comm, Real.dist_eq]
  exact (hA i).abs_eigenvalues₀_sub_le_norm (hB i) (j i)

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The ordered eigenvalue list of a Hermitian matrix is measurable for the entrywise
Borel structure. -/
@[fun_prop]
theorem measurable_eigenvalues₀ :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) :=
  continuous_eigenvalues₀.measurable

/-- Mathlib's matrix-indexed eigenvalue list is measurable on Hermitian matrices. -/
@[fun_prop]
theorem measurable_eigenvalues :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues) :=
  continuous_eigenvalues.measurable

end Matrix

namespace TauCeti

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The supremum of the real spectrum depends continuously on a Hermitian matrix, including on
empty index types (where the spectrum is empty and `sSup` is `0`). -/
@[fun_prop]
theorem continuous_sSup_spectrum_real :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
      sSup (spectrum ℝ (A : Matrix n n 𝕜))) := by
  by_cases hn : Nonempty n
  · let : Nonempty n := hn
    have hfun : (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
          sSup (spectrum ℝ (A : Matrix n n 𝕜))) =
        fun A ↦ A.property.eigenvalues₀ ⟨0, Fintype.card_pos⟩ :=
      funext fun A ↦ A.property.sSup_spectrum_real_eq_eigenvalues₀_zero
    rw [hfun]
    exact (continuous_apply _).comp Matrix.continuous_eigenvalues₀
  · have : IsEmpty n := not_nonempty_iff.1 hn
    have hfun : (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
          sSup (spectrum ℝ (A : Matrix n n 𝕜))) = fun _ ↦ 0 :=
      funext fun A ↦ by rw [Subsingleton.elim (A : Matrix n n 𝕜) 0, sSup_spectrum_real_zero]
    rw [hfun]
    exact continuous_const

/-- The infimum of the real spectrum depends continuously on a Hermitian matrix, including on
empty index types (where the spectrum is empty and `sInf` is `0`). -/
@[fun_prop]
theorem continuous_sInf_spectrum_real :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
      sInf (spectrum ℝ (A : Matrix n n 𝕜))) := by
  by_cases hn : Nonempty n
  · let : Nonempty n := hn
    have hfun : (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
          sInf (spectrum ℝ (A : Matrix n n 𝕜))) =
        fun A ↦ A.property.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos one_pos⟩ :=
      funext fun A ↦ A.property.sInf_spectrum_real_eq_eigenvalues₀_last
    rw [hfun]
    exact (continuous_apply _).comp Matrix.continuous_eigenvalues₀
  · have : IsEmpty n := not_nonempty_iff.1 hn
    have hfun : (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
          sInf (spectrum ℝ (A : Matrix n n 𝕜))) = fun _ ↦ 0 :=
      funext fun A ↦ by rw [Subsingleton.elim (A : Matrix n n 𝕜) 0, sInf_spectrum_real_zero]
    rw [hfun]
    exact continuous_const

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The supremum of the real spectrum is Borel measurable on the Hermitian subtype. -/
@[fun_prop]
theorem measurable_sSup_spectrum_real :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
      sSup (spectrum ℝ (A : Matrix n n 𝕜))) :=
  continuous_sSup_spectrum_real.measurable

/-- The infimum of the real spectrum is Borel measurable on the Hermitian subtype. -/
@[fun_prop]
theorem measurable_sInf_spectrum_real :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} ↦
      sInf (spectrum ℝ (A : Matrix n n 𝕜))) :=
  continuous_sInf_spectrum_real.measurable

/-- Composing `sSup (spectrum ℝ ·)` with an a.e. measurable, a.e. Hermitian matrix-valued map
yields an a.e. measurable real-valued map. -/
theorem aemeasurable_sSup_spectrum_real {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian) :
    AEMeasurable (fun ω ↦ sSup (spectrum ℝ (X ω))) P := by
  classical
  have hclosed : IsClosed {A : Matrix n n 𝕜 | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hg : Measurable ({A : Matrix n n 𝕜 | A.IsHermitian}.piecewise
      (fun A ↦ sSup (spectrum ℝ A)) 0) :=
    (continuousOn_iff_continuous_domRestrict.2 continuous_sSup_spectrum_real).measurable_piecewise
      continuousOn_const hclosed.measurableSet
  refine (hg.comp_aemeasurable hmeas).congr (hherm.mono fun ω hω ↦ ?_)
  simp [hω]

/-- Composing `sInf (spectrum ℝ ·)` with an a.e. measurable, a.e. Hermitian matrix-valued map
yields an a.e. measurable real-valued map. -/
theorem aemeasurable_sInf_spectrum_real {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian) :
    AEMeasurable (fun ω ↦ sInf (spectrum ℝ (X ω))) P := by
  classical
  have hclosed : IsClosed {A : Matrix n n 𝕜 | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hg : Measurable ({A : Matrix n n 𝕜 | A.IsHermitian}.piecewise
      (fun A ↦ sInf (spectrum ℝ A)) 0) :=
    (continuousOn_iff_continuous_domRestrict.2 continuous_sInf_spectrum_real).measurable_piecewise
      continuousOn_const hclosed.measurableSet
  refine (hg.comp_aemeasurable hmeas).congr (hherm.mono fun ω hω ↦ ?_)
  simp [hω]

end TauCeti
