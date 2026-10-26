/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Algebra.Module.ZLattice.Dual
public import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# The covolume of a lattice in an inner product space

In a finite-dimensional real inner product space, equipped with the volume measure of its inner
product, the square of the covolume of a `ℤ`-lattice is the determinant of the Gram matrix of any
of its `ℤ`-bases. This is the metric form of `ZLattice.covolume_eq_det`, which computes the
covolume in the coordinate space `ι → ℝ` as the absolute determinant of a basis.

The Gram determinant is computed from inner products alone, so this identity expresses the
covolume, a measure-theoretic invariant of the lattice, through the metric data of any of its
bases. In particular the covolume does not depend on a choice of coordinates, and two lattices
with the same Gram matrix in some bases have the same covolume.

The covolume of the dual lattice `L^∨ = ZLattice.dual L` is the inverse of the covolume of `L`
(`ZLattice.covolume_dual`): in an `ℤ`-basis of `L` and the dual basis of `L^∨`, the Gram matrices
are inverse to each other.

Independently of any inner product, pulling a full lattice back along a continuous linear
automorphism `A` of a finite-dimensional real normed space divides its covolume by `|det A|`, for
every Haar measure (`ZLattice.covolume_comap_continuousLinearEquiv`). Since Mathlib writes the
image `A L` as the pullback `ZLattice.comap ℝ L A⁻¹`, this says `covolume (A L) = |det A| *
covolume L`. Likewise, the image of a set `s` under the coordinates of any `ℤ`-basis of `L` has
Lebesgue measure `μ s / covolume L μ` for every Haar measure `μ`
(`ZLattice.volume_image_eq_measure_div_covolume`): the coordinates carry `μ` to `covolume L μ` times
Lebesgue measure. This reduces volume estimates for `L` to estimates for `ℤⁿ ⊆ ℝⁿ`.

Mathlib's asymptotic lattice-point count `ZLattice.covolume.tendsto_card_le_div''`, applied to the
dilates of the unit ball, shows that a full lattice in a real normed space of dimension `n` has
`O(R^n)` points in the ball of radius `R` (`ZLattice.ncard_closedBall_inter_isBigO`).

## Main results

* `ZLattice.covolume_sq_eq_det_gram`: `covolume L ^ 2` is the determinant of the Gram matrix of
  any `ℤ`-basis of `L`.
* `ZLattice.covolume_dual`: `covolume L^∨ = (covolume L)⁻¹`.
* `ZLattice.covolume_comap_continuousLinearEquiv`: the covolume of the pullback of `L` along a
  continuous linear automorphism `A` is `|det A|⁻¹ * covolume L`.
* `ZLattice.volume_image_eq_measure_div_covolume`: the image of `s` under the coordinates of a
  `ℤ`-basis of `L` has Lebesgue measure `μ s / covolume L μ`.
* `ZLattice.ncard_closedBall_inter_isBigO`: a full lattice has `O(R^n)` points in the ball of
  radius `R`.
-/

public section

open Asymptotics Filter Metric Module MeasureTheory Submodule
open LinearMap (BilinForm)

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Pulling a full lattice back along a continuous linear automorphism `A` divides its covolume
by `|det A|`, for any Haar measure. Read through images, `covolume (A L) = |det A| * covolume L`.
Mathlib's `ZLattice.covolume_comap` is the measure-preserving case. -/
theorem _root_.ZLattice.covolume_comap_continuousLinearEquiv (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (A : E ≃L[ℝ] E) (μ : Measure E := by volume_tac)
    [μ.IsAddHaarMeasure] :
    ZLattice.covolume (ZLattice.comap ℝ L A.toLinearMap) μ =
      |A.toLinearMap.det|⁻¹ * ZLattice.covolume L μ := by
  let b := Free.chooseBasis ℤ L
  -- The fundamental domain of the pulled-back basis is the image of that of `b` under `A⁻¹`.
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ μ
      (ZLattice.isAddFundamentalDomain b μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ μ
      (ZLattice.isAddFundamentalDomain (b.ofZLatticeComap ℝ L A.toLinearEquiv) μ),
    Basis.ofZLatticeBasis_comap, ← ZSpan.map_fundamentalDomain, measureReal_def, measureReal_def]
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, Measure.addHaar_image_continuousLinearEquiv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv]

/-- The coordinates of a `ℤ`-basis `b` of a full lattice `L` carry any Haar measure `μ` to
`covolume L μ` times Lebesgue measure on `ι → ℝ`: the image of any set `s` has volume
`μ s / covolume L μ`. This is Mathlib's `ZLattice.volume_image_eq_volume_div_covolume'` for an
arbitrary Haar measure on a normed space and an arbitrary set. -/
theorem _root_.ZLattice.volume_image_eq_measure_div_covolume (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by
  set φ := (b.ofZLatticeBasis ℝ).equivFun
  have hφ : MeasurableEmbedding φ :=
    φ.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have : (μ.map φ).IsAddHaarMeasure := φ.toContinuousLinearEquiv.isAddHaarMeasure_map μ
  -- The image of `μ` is a multiple `c • volume`, and `c` is the measure of the fundamental domain.
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, μ.map φ = c • volume :=
    ⟨_, by rw [← addHaarMeasure_eq_volume_pi ι]; exact Measure.addHaarMeasure_unique _ _⟩
  have hμ : ∀ t, μ t = c * volume (φ '' t) := fun t ↦ by
    rw [← smul_eq_mul, ← Measure.smul_apply, ← hc, hφ.map_apply,
      Set.preimage_image_eq t φ.injective]
  have hF : φ '' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) =
      Set.pi Set.univ fun _ ↦ Set.Ico (0 : ℝ) 1 := by
    ext x
    have hx : ∀ i, (b.ofZLatticeBasis ℝ).repr (φ.symm x) i = x i := fun i ↦
      congrFun (φ.apply_symm_apply x) i
    simp [LinearEquiv.image_eq_preimage_symm, ZSpan.mem_fundamentalDomain, hx]
  have hcov : ENNReal.ofReal (ZLattice.covolume L μ) = c := by
    have hfin := (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top (μ := μ)
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ),
      measureReal_def, ENNReal.ofReal_toReal hfin.ne]
    simp [hμ, hF, Real.volume_pi_Ico]
  rw [hμ s, ← hcov, mul_comm, ENNReal.mul_div_cancel_right
    (ENNReal.ofReal_pos.2 (ZLattice.covolume_pos L μ)).ne' ENNReal.ofReal_ne_top]

end NormedSpace

section Growth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A full lattice in a real normed space of dimension `n` has `O(R^n)` points in the closed ball
of radius `R` about the origin, as `R → ∞`. -/
theorem _root_.ZLattice.ncard_closedBall_inter_isBigO (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    (fun R : ℝ ↦ ((closedBall (0 : E) R ∩ L).ncard : ℝ)) =O[atTop]
      fun R ↦ R ^ finrank ℝ E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun R ↦ ?_)
    simp only [finrank_zero_of_subsingleton, pow_zero, norm_one, mul_one, Real.norm_natCast]
    exact_mod_cast Set.ncard_le_one_of_subsingleton _
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  -- The sublevel sets of `x ↦ ‖x‖ ^ n` are the closed balls.
  have hball : ∀ R, 0 ≤ R → {x : E | ‖x‖ ^ n ≤ R ^ n} = closedBall 0 R := by
    intro R hR
    ext x
    simp [pow_le_pow_iff_left₀ (norm_nonneg x) hR hn]
  have h1 : {x : E | x ∈ Set.univ ∧ ‖x‖ ^ n ≤ 1} = closedBall 0 1 := by
    simpa using hball 1 zero_le_one
  -- Mathlib's asymptotic count of lattice points in the dilates of the unit ball, in the
  -- coordinates of a `ℤ`-basis `b` of `L`.
  let b := Free.chooseBasis ℤ L
  have : Nonempty (Free.ChooseBasisIndex ℤ L) := by
    have : Nontrivial L := nontrivial_of_finrank_pos <| (ZLattice.rank ℝ L).symm ▸ finrank_pos
    infer_instance
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = n := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  -- The image of the unit ball in the coordinates of `b` is convex, so its frontier is null.
  have hnull :
      volume (frontier ((b.ofZLatticeBasis ℝ L).equivFun '' closedBall (0 : E) 1)) = 0 :=
    ((convex_closedBall (0 : E) 1).linear_image
      (b.ofZLatticeBasis ℝ L).equivFun.toLinearMap).addHaar_frontier volume
  have key := ZLattice.covolume.tendsto_card_le_div'' b (X := Set.univ) (F := fun x ↦ ‖x‖ ^ n)
    (fun _ _ _ _ ↦ Set.mem_univ _)
    (fun x r hr ↦ by rw [hcard, norm_smul, Real.norm_of_nonneg hr, mul_pow])
    (h1 ▸ isBounded_closedBall) (h1 ▸ measurableSet_closedBall) (h1 ▸ hnull)
  have hO : (fun c : ℝ ↦ (Nat.card ({x : E | x ∈ Set.univ ∧ ‖x‖ ^ n ≤ c} ∩ L : Set E) : ℝ))
      =O[atTop] fun c ↦ c :=
    isBigO_of_div_tendsto_nhds ((eventually_gt_atTop 0).mono fun c hc h0 ↦ absurd h0 hc.ne') _ key
  refine (hO.comp_tendsto (tendsto_pow_atTop hn)).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_ge_atTop 0] with R hR
  simp only [Function.comp_apply, Nat.card_coe_set_eq, Set.mem_univ, true_and, hball R hR]

end Growth

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The square of the covolume of a lattice in a finite-dimensional real inner product space is
the determinant of the Gram matrix of any `ℤ`-basis of the lattice. -/
theorem _root_.ZLattice.covolume_sq_eq_det_gram (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ fun i ↦ (b i : E)).det := by
  have hcard : finrank ℝ E = Fintype.card ι := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hcard.symm).symm
  -- The fundamental parallelepiped of an orthonormal basis has volume `1`.
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
      OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one]
  -- The Gram matrix is `Mᵀ M`, where `M` is the matrix of the lattice basis in orthonormal
  -- coordinates.
  have hM : o.toBasis.toMatrix ((↑) ∘ b) = Matrix.of fun i j ↦ o.repr (b j : E) i := by
    ext i j
    simp [Basis.toMatrix_apply]
  have hgram : (Matrix.gram ℝ fun i ↦ (b i : E)).det = o.toBasis.det ((↑) ∘ b) ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose,
      star_trivial, Basis.det_apply, hM, sq]
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, hvol, hgram, mul_one, sq_abs]

/-- The covolume of the dual of a full lattice is the inverse of the covolume of the lattice. -/
@[simp]
theorem _root_.ZLattice.covolume_dual (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (ZLattice.dual L) = (ZLattice.covolume L)⁻¹ := by
  classical
  let b := Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ L
  let D := BilinForm.dualBasis (innerₗ E) nondegenerate_inner B
  -- The dual lattice is the `ℤ`-span of the dual basis `D`, so `D` is a `ℤ`-basis of it.
  have hdual : span ℤ (Set.range D) = ZLattice.dual L := by
    conv_rhs => rw [← b.ofZLatticeBasis_span ℝ L]
    rw [ZLattice.dual_span_basis]
  let bD : Basis _ ℤ (ZLattice.dual L) :=
    (Basis.span (D.linearIndependent.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hdual)
  have hB : (fun i ↦ (b i : E)) = ⇑B := funext fun i ↦ (b.ofZLatticeBasis_apply ℝ L i).symm
  have hD : (fun i ↦ (bD i : E)) = ⇑D := funext fun i ↦ by simp [bD, Basis.span_apply]
  have hgram (v : Basis (Free.ChooseBasisIndex ℤ L) ℝ E) :
      Matrix.gram ℝ ⇑v = BilinForm.toMatrix v (innerₗ E) := by
    ext i j
    simp [BilinForm.toMatrix_apply, Matrix.gram_apply]
  -- The squared covolumes are the Gram determinants of `D` and `B`, which are inverse.
  have hsq : (ZLattice.covolume (ZLattice.dual L) * ZLattice.covolume L) ^ 2 = 1 := by
    rw [mul_pow, ZLattice.covolume_sq_eq_det_gram _ bD, ZLattice.covolume_sq_eq_det_gram L b, hB,
      hD, hgram, hgram]
    exact BilinForm.det_toMatrix_dualBasis_mul_det_toMatrix _ _ B
  have hpos := mul_pos (ZLattice.covolume_pos (ZLattice.dual L) volume)
    (ZLattice.covolume_pos L volume)
  exact eq_inv_of_mul_eq_one_left ((pow_eq_one_iff_of_nonneg hpos.le two_ne_zero).mp hsq)

end InnerProductSpace

end TauCeti
