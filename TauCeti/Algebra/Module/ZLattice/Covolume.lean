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
public import TauCeti.MeasureTheory.Group.FundamentalDomain
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

The covolume is antitone in the lattice: a full sublattice has covolume at least that of the
ambient lattice, for every Haar measure (`ZLattice.covolume_le_covolume_of_le`). Applied to the
`ℤ`-span of a real basis `b` made of lattice vectors, this bounds the covolume of a full lattice by
the volume of the parallelepiped of `b`; in an inner product space that volume is `|det_o b|` for
any orthonormal basis `o` (`ZLattice.covolume_le_abs_det`). This is the covolume bound in the lower
half of Minkowski's second theorem, where `b` attains the successive minima but need not be a
`ℤ`-basis.

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
* `ZLattice.covolume_le_covolume_of_le`: a full sublattice `L₁ ≤ L₂` has
  `covolume L₂ μ ≤ covolume L₁ μ`.
* `ZLattice.covolume_le_abs_det_mul_measureReal`: a real basis `b` of lattice vectors has
  `covolume L μ ≤ |det_{b₀} b| * μ.real (fundamentalDomain b₀)` for any Haar measure `μ` and any
  real basis `b₀`.
* `ZLattice.covolume_le_abs_det`: a real basis `b` of lattice vectors has `covolume L ≤ |det_o b|`
  for any orthonormal basis `o`.
* `ZLattice.ncard_closedBall_inter_isBigO`: a full lattice has `O(R^n)` points in the ball of
  radius `R`.

## References

* J.-H. Evertse, *Geometry of Numbers*, §2.3, lower-bound proof of Theorem 2.9,
  printed p.27: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>. This is the source of
  `ZLattice.covolume_le_covolume_of_le` and `ZLattice.covolume_le_abs_det`.
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
  -- The coordinates carry `μ` to Lebesgue measure scaled by the covolume, which is the measure of
  -- the fundamental domain.
  have hfin := (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top (μ := μ)
  rw [(b.ofZLatticeBasis ℝ).addHaar_eq_measure_fundamentalDomain_mul_volume_image μ s,
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ),
    measureReal_def, ENNReal.ofReal_toReal hfin.ne, mul_comm,
    ENNReal.mul_div_cancel_right (ZSpan.measure_fundamentalDomain_ne_zero _) hfin.ne]

/-- **The covolume is antitone in the lattice.** If a full lattice `L₁` is contained in a discrete
`ℤ`-submodule `L₂`, then `covolume L₂ μ ≤ covolume L₁ μ` for any Haar measure `μ`. The submodule
`L₂` is then full as well. -/
theorem _root_.ZLattice.covolume_le_covolume_of_le {L₁ L₂ : Submodule ℤ E} [DiscreteTopology L₁]
    [IsZLattice ℝ L₁] [DiscreteTopology L₂] (h : L₁ ≤ L₂) (μ : Measure E := by volume_tac)
    [μ.IsAddHaarMeasure] :
    ZLattice.covolume L₂ μ ≤ ZLattice.covolume L₁ μ := by
  have : IsZLattice ℝ L₂ :=
    ⟨eq_top_iff.2 (IsZLattice.span_top (K := ℝ) (L := L₁) ▸ span_mono h)⟩
  -- A fundamental parallelepiped of `L₂` is disjoint from its translates by the nonzero vectors
  -- of `L₁`, so it is no larger than a fundamental domain of `L₁`.
  let b₂ := (Free.chooseBasis ℤ L₂).ofZLatticeBasis ℝ L₂
  have h₁ := ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L₁) μ
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L₁ μ h₁,
    ZLattice.covolume_eq_measure_fundamentalDomain L₂ μ
      (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L₂) μ), measureReal_def,
    measureReal_def]
  refine ENNReal.toReal_mono (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne ?_
  have : MeasurableVAdd L₁ E := (inferInstance : MeasurableVAdd L₁.toAddSubgroup E)
  have : VAddInvariantMeasure L₁ E μ :=
    (inferInstance : VAddInvariantMeasure L₁.toAddSubgroup E μ)
  refine h₁.measure_le_of_disjoint_vadd (ZSpan.fundamentalDomain_measurableSet b₂).nullMeasurableSet
    fun g hg ↦ Set.disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ hgx
  -- Both `0` and `g`, viewed in the `ℤ`-span of `b₂`, translate `x` into the parallelepiped.
  have hg₂ : (g : E) ∈ span ℤ (Set.range b₂) := by
    rw [Basis.ofZLatticeBasis_span]
    exact h g.2
  have hx₀ : (0 : span ℤ (Set.range b₂)) +ᵥ x ∈ ZSpan.fundamentalDomain b₂ := by
    rwa [zero_vadd]
  have hg₀ := (ZSpan.exist_unique_vadd_mem_fundamentalDomain b₂ x).unique
    (y₁ := ⟨g, hg₂⟩) hgx hx₀
  exact hg (Subtype.ext (congrArg Subtype.val hg₀ :))

/-- If a real basis `b` of `E` consists of vectors of a discrete `ℤ`-submodule `L`, then the
covolume of `L` is at most `|det_{b₀} b|` times the measure of the fundamental parallelepiped of
any real basis `b₀`, for any Haar measure. The right side is the covolume of the full sublattice
spanned by `b`, as in `ZLattice.covolume_eq_det_mul_measureReal`. -/
theorem _root_.ZLattice.covolume_le_abs_det_mul_measureReal (L : Submodule ℤ E)
    [DiscreteTopology L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (hb : ∀ i, b i ∈ L) (b₀ : Basis ι ℝ E) (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    ZLattice.covolume L μ ≤ |b₀.det b| * μ.real (ZSpan.fundamentalDomain b₀) := by
  calc ZLattice.covolume L μ ≤ ZLattice.covolume (span ℤ (Set.range b)) μ :=
        ZLattice.covolume_le_covolume_of_le (span_le.2 (Set.range_subset_iff.2 hb)) μ
    _ = |b₀.det b| * μ.real (ZSpan.fundamentalDomain b₀) := by
      rw [ZLattice.covolume_eq_measure_fundamentalDomain _ μ (ZSpan.isAddFundamentalDomain b μ),
        ZSpan.measureReal_fundamentalDomain b μ b₀]

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

/-- The fundamental parallelepiped of an orthonormal basis has volume `1`. -/
@[simp]
theorem _root_.OrthonormalBasis.volume_fundamentalDomain {ι : Type*} [Fintype ι]
    (o : OrthonormalBasis ι ℝ E) : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]

/-- The fundamental parallelepiped of an orthonormal basis has real volume `1`. -/
@[simp]
theorem _root_.OrthonormalBasis.volume_real_fundamentalDomain {ι : Type*} [Fintype ι]
    (o : OrthonormalBasis ι ℝ E) : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  simp [measureReal_def]

/-- The squared Euclidean volume of a basis parallelepiped is its Gram determinant. -/
theorem _root_.Module.Basis.volume_real_fundamentalDomain_sq_eq_det_gram {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    volume.real (ZSpan.fundamentalDomain b) ^ 2 = (Matrix.gram ℝ b).det := by
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex
      (Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm).symm
  have hM : o.toBasis.toMatrix b = Matrix.of fun i j ↦ o.repr (b j) i := by
    ext i j
    simp [Basis.toMatrix_apply]
  have hgram : (Matrix.gram ℝ b).det = o.toBasis.det b ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose,
      star_trivial, Basis.det_apply, hM, sq]
  rw [ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    o.volume_real_fundamentalDomain, mul_one, sq_abs, hgram]

/-- The square of the covolume of a lattice in a finite-dimensional real inner product space is
the determinant of the Gram matrix of any `ℤ`-basis of the lattice. -/
theorem _root_.ZLattice.covolume_sq_eq_det_gram (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ fun i ↦ (b i : E)).det := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume
    (ZLattice.isAddFundamentalDomain b volume),
    (b.ofZLatticeBasis ℝ L).volume_real_fundamentalDomain_sq_eq_det_gram]
  congr 1
  ext i j
  simp only [Matrix.gram_apply, Basis.ofZLatticeBasis_apply]

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

/-- **The covolume is at most the volume of any lattice parallelepiped.** If a real basis `b` of
`E` consists of vectors of a discrete `ℤ`-submodule `L`, then `covolume L ≤ |det_o b|` for any
orthonormal basis `o`, the covolume being taken for the volume of the inner product. -/
theorem _root_.ZLattice.covolume_le_abs_det (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (hb : ∀ i, b i ∈ L)
    (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume L ≤ |o.toBasis.det b| := by
  simpa using ZLattice.covolume_le_abs_det_mul_measureReal L b hb o.toBasis volume

end InnerProductSpace

end TauCeti
