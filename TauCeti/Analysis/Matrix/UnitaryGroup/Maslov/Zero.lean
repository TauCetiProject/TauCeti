/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cayley
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# The zero axiom for the Maslov index of paths

The Maslov index `Matrix.UnitaryGroup.maslovIndex` of a path `γ` of unitary frames is Souriau's
formula `angleChange (det ∘ W ∘ γ) / (2π) - (s(W V) - s(W U))`, where `W U = U Uᵀ` is the Souriau
map and `s` the spectral angle sum `Matrix.spectralAngleSum`, the sum of `arg (-λ) / (2π)` over the
eigenvalues `λ ≠ 1` of `W`. The **zero axiom** of Robbin and Salamon says that the index of a path
along which the intersection `γ t ℝⁿ ∩ ℝⁿ` of the Lagrangians with `ℝⁿ` keeps the same dimension
vanishes (`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_finrank_realImage_inf_realSubspace`).

That dimension is the multiplicity of the eigenvalue `1` of the Souriau map
(`Matrix.UnitaryGroup.count_roots_charpoly_souriau`). Indeed, since `U U⋆ = 1`,
`U Uᵀ - 1 = U (Uᵀ - U⋆) = 2 i U (Im U)ᵀ`, so `U Uᵀ - 1` has the rank of the imaginary part
`Im U`; a real vector `U x`, for real `x`, is real exactly when `(Im U) x = 0`; and for a unitary
matrix the multiplicity of an eigenvalue is the dimension of its eigenspace
(`Matrix.count_roots_charpoly_add_rank_sub_one`). So it suffices to prove the zero axiom for paths
along which the multiplicity of the eigenvalue `1` of the Souriau maps is constant
(`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_count_roots_charpoly_souriau`). This has two
ingredients, both about a unitary matrix `W` with the eigenvalue `1` of multiplicity `k`.

* `exp (2πi s(W)) = (-1)^(n - k) det W` (`Matrix.exp_two_pi_mul_I_mul_spectralAngleSum`): each
  eigenvalue `λ ≠ 1` contributes `exp (i arg (-λ)) = -λ`.
* `s` is continuous along a continuous family of unitary matrices on which the multiplicity of the
  eigenvalue `1` is locally constant (`Matrix.continuousAt_spectralAngleSum`). Near a given unitary
  matrix `W₀`, choose a point `c` of the circle such that `c W₀` does not have the eigenvalue `-1`.
  Then `c W` is the Cayley transform of the Hermitian matrix `invCayley (c W)`, which depends
  continuously on `W`. So the eigenvalues of `W` are `c⁻¹ e^{2 i arctan λⱼ}` for the eigenvalues
  `λⱼ` of a continuous family of Hermitian matrices, and these depend continuously on `W`
  (`Matrix.continuous_eigenvalues`). An eigenvalue `≠ 1` of `W₀` stays `≠ 1` nearby, where
  `arg (-λ)` is continuous, and since the multiplicity of `1` is constant the eigenvalues equal to
  `1` stay equal to `1`.

Along the path, with `θ` a continuous angle of `det (W (γ t))`, the function `θ - 2π s(W ∘ γ)`
is therefore continuous, and its exponential is the constant `(-1)^(n - k)`. So it is constant,
which is the vanishing of the Maslov index.

## Main results

* `Matrix.exp_two_pi_mul_I_mul_spectralAngleSum`: the exponential of the spectral angle sum of a
  unitary matrix.
* `Matrix.count_roots_charpoly_add_rank_sub_one`: algebraic and geometric multiplicities of the
  eigenvalue `1` of a unitary matrix agree.
* `Matrix.continuousAt_spectralAngleSum`: continuity of the spectral angle sum where the
  multiplicity of the eigenvalue `1` is locally constant.
* `Matrix.UnitaryGroup.count_roots_charpoly_souriau`: the multiplicity of the eigenvalue `1` of
  `U Uᵀ` is the dimension of `U ℝⁿ ∩ ℝⁿ`.
* `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_finrank_realImage_inf_realSubspace`: the zero axiom,
  with `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_count_roots_charpoly_souriau` its form in terms
  of the Souriau maps.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the zero axiom).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117--148.
-/

public section

open Complex Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Cayley charts of unitary matrices -/

/-- Every square complex matrix `W` has a point `c` of the circle such that `1 + c W` is
invertible: only finitely many `c` make `-c⁻¹` an eigenvalue of `W`. -/
private theorem exists_isUnit_det_one_add_smul (W : Matrix n n ℂ) :
    ∃ c : Circle, IsUnit (1 + (c : ℂ) • W).det := by
  classical
  -- Pick `c = e^{it}` with `t ∈ (0, 1)` such that `-c⁻¹ = -e^{-it}` is not a root of the
  -- characteristic polynomial.
  set e : ℝ → ℂ := fun t => -exp (↑(-t) * I)
  have he : Set.InjOn e (Set.Ioo 0 1) := by
    intro s hs t ht hst
    have h := congrArg (fun z => arg (-z)) hst
    simp only [e, neg_neg] at h
    have hmod {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
        toIocMod Real.two_pi_pos (-Real.pi) (-u) = -u :=
      (toIocMod_eq_self _).2 ⟨by linarith [hu.2, Real.two_le_pi], by linarith [hu.1, Real.pi_pos]⟩
    rwa [arg_exp_mul_I, arg_exp_mul_I, hmod hs, hmod ht, neg_inj] at h
  obtain ⟨_, ⟨t, -, rfl⟩, htF⟩ :=
    ((Set.Ioo_infinite (zero_lt_one' ℝ)).image he).exists_notMem_finset W.charpoly.roots.toFinset
  refine ⟨Circle.exp t, ?_⟩
  set c : ℂ := (Circle.exp t : ℂ)
  have hc : c ≠ 0 := Circle.coe_ne_zero _
  have hz : e t = -c⁻¹ := by simp [e, c, Circle.coe_exp, ← exp_neg]
  have hunit : IsUnit (algebraMap ℂ (Matrix n n ℂ) (e t) - W) := by
    have hspec : e t ∉ spectrum ℂ W := by
      rwa [mem_spectrum_iff_isRoot_charpoly, ← Polynomial.mem_roots (charpoly_monic W).ne_zero,
        ← Multiset.mem_toFinset]
    simpa [spectrum.mem_iff] using hspec
  have heq : 1 + c • W = (-c) • (algebraMap ℂ (Matrix n n ℂ) (e t) - W) := by
    rw [hz, smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul]
    field_simp
    simp [sub_eq_add_neg]
  rw [heq, det_smul]
  exact ((neg_ne_zero.2 hc).isUnit.pow _).mul ((isUnit_iff_isUnit_det _).1 hunit)

/-- A unitary matrix `W` with `1 + c W` invertible, for `c` on the circle, is `c⁻¹` times the
Cayley transform of the Hermitian matrix `invCayley (c W)`. -/
private theorem isHermitian_invCayley_and_eq {W : Matrix n n ℂ} (hW : W ∈ unitaryGroup n ℂ)
    {c : Circle} (h : IsUnit (1 + (c : ℂ) • W).det) :
    (invCayley ((c : ℂ) • W)).IsHermitian ∧ W = (c : ℂ)⁻¹ • cayley (invCayley ((c : ℂ) • W)) := by
  refine ⟨isHermitian_invCayley (Unitary.smul_mem_of_mem (Circle.coe_mem_unitary c) hW) h, ?_⟩
  rw [cayley_invCayley h, smul_smul, inv_mul_cancel₀ (Circle.coe_ne_zero c), one_smul]

section Chart

variable {A : Matrix n n ℂ}

/-- The eigenvalues `c e^{2 i arctan λⱼ}` of `c • cayley A`, for the eigenvalues `λⱼ` of the
Hermitian matrix `A`. -/
private noncomputable def chartEig (hA : A.IsHermitian) (c : ℂ) (j : n) : ℂ :=
  c * exp (↑(2 * Real.arctan (hA.eigenvalues j)) * I)

private theorem smul_cayley_eq (hA : A.IsHermitian) (c : ℂ) :
    c • cayley A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (chartEig hA c) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [hA.cayley_eq_mul_diagonal_mul_star, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  rfl

private theorem charpoly_smul_cayley (hA : A.IsHermitian) (c : ℂ) :
    (c • cayley A).charpoly = (diagonal (chartEig hA c)).charpoly := by
  have hU := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hU' := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Unitary.coe_star] at hU
  have h := charpoly_units_conj (⟨_, _, hU, hU'⟩ : (Matrix n n ℂ)ˣ) (diagonal (chartEig hA c))
  rw [Units.val_mk, inv_eq_left_inv hU'] at h
  rw [smul_cayley_eq hA c, h]

/-- The roots of the characteristic polynomial of `c • cayley A` are the `chartEig hA c j`. -/
private theorem roots_charpoly_smul_cayley (hA : A.IsHermitian) (c : ℂ) :
    (c • cayley A).charpoly.roots = Finset.univ.val.map (chartEig hA c) := by
  rw [charpoly_smul_cayley hA, charpoly_diagonal, Finset.prod_eq_multiset_prod,
    ← Function.comp_def (fun a : ℂ => Polynomial.X - Polynomial.C a) (chartEig hA c),
    ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]

private theorem spectralAngleSum_smul_cayley (hA : A.IsHermitian) (c : ℂ) :
    spectralAngleSum (c • cayley A) = ∑ j, if chartEig hA c j = 1 then 0 else
      arg (-chartEig hA c j) / (2 * Real.pi) := by
  have hU := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hU' := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Unitary.coe_star] at hU
  rw [smul_cayley_eq hA c, spectralAngleSum_conj hU hU', spectralAngleSum_diagonal]

private theorem count_roots_charpoly_smul_cayley (hA : A.IsHermitian) (c : ℂ) (z : ℂ) :
    (c • cayley A).charpoly.roots.count z =
      (Finset.univ.filter fun j => chartEig hA c j = z).card := by
  classical
  rw [roots_charpoly_smul_cayley hA, Multiset.count_map, Finset.card_def, Finset.filter_val]
  simp [eq_comm]

private theorem det_smul_cayley (hA : A.IsHermitian) (c : ℂ) :
    (c • cayley A).det = ∏ j, chartEig hA c j := by
  rw [det_eq_prod_roots_charpoly, roots_charpoly_smul_cayley hA]
  rfl

private theorem rank_smul_cayley_sub_one (hA : A.IsHermitian) (c : ℂ) :
    (c • cayley A - 1).rank = (Finset.univ.filter fun j => chartEig hA c j ≠ 1).card := by
  classical
  set P : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hU : P * star P = 1 := by simp [P]
  have heq : c • cayley A - 1 = P * diagonal (fun j => chartEig hA c j - 1) * star P := by
    rw [smul_cayley_eq hA c, ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hU]
  rw [heq, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_left_inverse hU),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse hU), rank_diagonal,
    Fintype.card_subtype]
  simp [sub_ne_zero]

private theorem norm_chartEig (hA : A.IsHermitian) (c : Circle) (j : n) :
    ‖chartEig hA (c : ℂ) j‖ = 1 := by
  rw [chartEig, norm_mul, norm_exp_ofReal_mul_I, Circle.norm_coe, mul_one]

end Chart

/-! ### The spectral angle sum of a unitary matrix -/

/-- **The exponential of the spectral angle sum.** For a unitary matrix `W` with the eigenvalue
`1` of multiplicity `k`, `exp (2πi s(W)) = (-1)^(n - k) det W`: each eigenvalue `λ ≠ 1`, of norm
`1`, contributes `exp (i arg (-λ)) = -λ`. -/
theorem exp_two_pi_mul_I_mul_spectralAngleSum {W : Matrix n n ℂ} (hW : W ∈ unitaryGroup n ℂ) :
    exp (2 * Real.pi * I * spectralAngleSum W) =
      (-1) ^ (Fintype.card n - W.charpoly.roots.count 1) * W.det := by
  classical
  obtain ⟨c, hdet⟩ := exists_isUnit_det_one_add_smul W
  obtain ⟨hA, hWA⟩ := isHermitian_invCayley_and_eq hW hdet
  set d := chartEig hA (c : ℂ)⁻¹
  have hd (j : n) : ‖d j‖ = 1 := by simpa using norm_chartEig hA c⁻¹ j
  have hterm (j : n) : exp (2 * Real.pi * I *
      ((if d j = 1 then 0 else arg (-d j) / (2 * Real.pi) : ℝ) : ℂ)) =
      (if d j = 1 then 1 else -1) * d j := by
    split_ifs with h
    · simp [h]
    · have := norm_mul_exp_arg_mul_I (-d j)
      rw [norm_neg, hd, ofReal_one, one_mul] at this
      have harg : 2 * (Real.pi : ℂ) * I * (((-d j).arg / (2 * Real.pi) : ℝ) : ℂ) =
          (-d j).arg * I := by
        push_cast
        field_simp
      rw [harg, this, neg_one_mul]
  rw [hWA, spectralAngleSum_smul_cayley hA, count_roots_charpoly_smul_cayley hA,
    det_smul_cayley hA, ofReal_sum, Finset.mul_sum, exp_sum,
    Finset.prod_congr rfl fun j _ => hterm j, Finset.prod_mul_distrib, Finset.prod_ite,
    Finset.prod_const_one, one_mul, Finset.prod_const, ← Finset.card_compl, Finset.compl_filter]

/-- **Algebraic and geometric multiplicities agree for unitary matrices.** The multiplicity of the
eigenvalue `1` of a unitary matrix `W`, as a root of its characteristic polynomial, is the
dimension `n - rank (W - 1)` of its eigenspace. -/
theorem count_roots_charpoly_add_rank_sub_one {W : Matrix n n ℂ} (hW : W ∈ unitaryGroup n ℂ) :
    W.charpoly.roots.count 1 + (W - 1).rank = Fintype.card n := by
  classical
  obtain ⟨c, hdet⟩ := exists_isUnit_det_one_add_smul W
  obtain ⟨hA, hWA⟩ := isHermitian_invCayley_and_eq hW hdet
  rw [hWA, count_roots_charpoly_smul_cayley hA, rank_smul_cayley_sub_one hA]
  exact Finset.card_filter_add_card_filter_not _

/-- The function `z ↦ arg (-z) / (2π)`, set to `0` at `z = 1`, is continuous at every point of the
unit circle other than `1`. -/
private theorem continuousAt_angleOffset {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ContinuousAt (fun w : ℂ => if w = 1 then 0 else arg (-w) / (2 * Real.pi)) z := by
  have hslit : -z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_contra! h
    have him : z.im = 0 := by simpa using h.2
    have hre : 0 ≤ z.re := by simpa using h.1
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    rw [hz', norm_real, Real.norm_of_nonneg hre] at hz
    exact hz1 (by rw [hz', hz, ofReal_one])
  refine ContinuousAt.congr (f := fun w : ℂ => arg (-w) / (2 * Real.pi))
    (((continuousAt_arg hslit).comp continuousAt_neg).div_const _) ?_
  filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
  simp [hw]

/-- **Continuity of the spectral angle sum.** Along a family `W` of unitary matrices continuous at
`x₀`, on which the multiplicity of the eigenvalue `1` is constant near `x₀`, the spectral angle sum
is continuous at `x₀`. No eigenvalue crosses `1`: those `≠ 1` stay away from `1`, and those equal
to `1` stay there. -/
theorem continuousAt_spectralAngleSum {X : Type*} [TopologicalSpace X] {W : X → Matrix n n ℂ}
    {x₀ : X} (hW : ContinuousAt W x₀) (hWu : ∀ᶠ x in 𝓝 x₀, W x ∈ unitaryGroup n ℂ)
    (hcount : ∀ᶠ x in 𝓝 x₀,
      (W x).charpoly.roots.count 1 = (W x₀).charpoly.roots.count 1) :
    ContinuousAt (fun x => spectralAngleSum (W x)) x₀ := by
  classical
  obtain ⟨c, hc₀⟩ := exists_isUnit_det_one_add_smul (W x₀)
  set A : X → Matrix n n ℂ := fun x => invCayley ((c : ℂ) • W x)
  -- Near `x₀`, `1 + c W x` stays invertible, and `A` is continuous at `x₀`.
  have h1 : ContinuousAt (fun x => 1 + (c : ℂ) • W x) x₀ :=
    continuousAt_const.add (hW.const_smul (c : ℂ))
  have hdet : ∀ᶠ x in 𝓝 x₀, IsUnit (1 + (c : ℂ) • W x).det := by
    have hdetc : ContinuousAt (fun x => (1 + (c : ℂ) • W x).det) x₀ :=
      ContinuousAt.comp (g := fun M : Matrix n n ℂ => M.det)
        (Continuous.matrix_det continuous_id).continuousAt h1
    filter_upwards [hdetc.eventually_ne hc₀.ne_zero] with x hx
    exact isUnit_iff_ne_zero.2 hx
  have hAc : ContinuousAt A x₀ := by
    have hinv : ContinuousAt (fun x => (1 + (c : ℂ) • W x)⁻¹) x₀ :=
      ContinuousAt.comp (g := Inv.inv)
        (continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hc₀.unit)) h1
    have h2 : ContinuousAt (fun x => 1 - (c : ℂ) • W x) x₀ :=
      continuousAt_const.sub (hW.const_smul (c : ℂ))
    have hA : A = fun x => I • ((1 - (c : ℂ) • W x) * (1 + (c : ℂ) • W x)⁻¹) :=
      funext fun x => invCayley_def _
    rw [hA]
    exact (h2.mul hinv).const_smul I
  have hAh : ∀ᶠ x in 𝓝 x₀, (A x).IsHermitian ∧ W x = (c : ℂ)⁻¹ • cayley (A x) := by
    filter_upwards [hWu, hdet] with x hx hx'
    exact isHermitian_invCayley_and_eq hx hx'
  have hx₀ := hAh.self_of_nhds
  -- The matrices `A x`, as points of the space of Hermitian matrices.
  let B : X → {A : Matrix n n ℂ // A.IsHermitian} := fun x =>
    if h : (A x).IsHermitian then ⟨A x, h⟩ else ⟨A x₀, hx₀.1⟩
  have hBx {x : X} (h : (A x).IsHermitian) : B x = ⟨A x, h⟩ := by simp [B, h]
  have hB : Tendsto B (𝓝 x₀) (𝓝 (B x₀)) := by
    rw [hBx hx₀.1, tendsto_subtype_rng]
    refine hAc.tendsto.congr' ?_
    filter_upwards [hAh] with x hx
    rw [hBx hx.1]
  -- The eigenvalues `d x j = c⁻¹ e^{2 i arctan λⱼ(A x)}` of `W x` depend continuously on `x`.
  set d : X → n → ℂ := fun x => chartEig (B x).2 (c : ℂ)⁻¹
  have hd (j : n) : Tendsto (fun x => d x j) (𝓝 x₀) (𝓝 (d x₀ j)) := by
    have hcont : Continuous fun M : {A : Matrix n n ℂ // A.IsHermitian} =>
        chartEig M.2 (c : ℂ)⁻¹ j :=
      continuous_const.mul (continuous_exp.comp ((continuous_ofReal.comp
        (continuous_const.mul (Real.continuous_arctan.comp
          ((continuous_apply j).comp continuous_eigenvalues)))).mul continuous_const))
    exact (hcont.tendsto _).comp hB
  have hdnorm (x : X) (j : n) : ‖d x j‖ = 1 := by simpa using norm_chartEig (B x).2 c⁻¹ j
  -- Near `x₀`, the spectral angle sum and the multiplicity of `1` are read off `d x`.
  set F : ℂ → ℝ := fun w => if w = 1 then 0 else arg (-w) / (2 * Real.pi)
  have hsum : ∀ᶠ x in 𝓝 x₀, spectralAngleSum (W x) = ∑ j, F (d x j) := by
    filter_upwards [hAh] with x hx
    rw [hx.2, spectralAngleSum_smul_cayley hx.1]
    simp only [d, hBx hx.1, F]
  have hcard : ∀ᶠ x in 𝓝 x₀, (W x).charpoly.roots.count 1 =
      (Finset.univ.filter fun j => d x j = 1).card := by
    filter_upwards [hAh] with x hx
    rw [hx.2, count_roots_charpoly_smul_cayley hx.1]
    simp only [d, hBx hx.1]
  -- The indices `j` with `d x j = 1` are eventually those with `d x₀ j = 1`: none can join, by
  -- continuity, and none can leave, since their number is constant.
  set J := Finset.univ.filter fun j => d x₀ j = 1
  have hJ : ∀ᶠ x in 𝓝 x₀, ∀ j, d x j = 1 ↔ j ∈ J := by
    have hout : ∀ᶠ x in 𝓝 x₀, ∀ j ∉ J, d x j ≠ 1 := by
      rw [eventually_all]
      intro j
      by_cases hj : j ∈ J
      · exact Eventually.of_forall fun _ h => (h hj).elim
      · have hj' : d x₀ j ≠ 1 := by simpa [J] using hj
        filter_upwards [(hd j).eventually (isOpen_ne.mem_nhds hj')] with x hx _
        exact hx
    filter_upwards [hout, hcount, hcard] with x hx hx' hx''
    have hsub : (Finset.univ.filter fun j => d x j = 1) ⊆ J := fun j hj => by
      by_contra h
      exact hx j h (by simpa using hj)
    have heq : (Finset.univ.filter fun j => d x j = 1) = J :=
      Finset.eq_of_subset_of_card_le hsub (by rw [← hx'', hx', hcard.self_of_nhds])
    intro j
    rw [← heq]
    simp
  refine Tendsto.congr' (EventuallyEq.symm hsum) ?_
  dsimp only
  rw [hsum.self_of_nhds]
  refine tendsto_finsetSum _ fun j _ => ?_
  by_cases hj : j ∈ J
  · -- At an eigenvalue `1` of `W x₀`, the term is eventually `F 1 = 0`.
    have hj' : d x₀ j = 1 := by simpa [J] using hj
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hJ] with x hx
    rw [(hx j).2 hj, hj']
  · exact (continuousAt_angleOffset (hdnorm x₀ j) (by simpa [J] using hj)).tendsto.comp (hd j)

/-! ### The zero axiom -/

namespace UnitaryGroup

open scoped unitInterval

/-- The rank of `U Uᵀ - 1` is the rank of the imaginary part of `U`: since `U U⋆ = 1`,
`U Uᵀ - 1 = U (Uᵀ - U⋆)`, and `Uᵀ - U⋆ = 2 i (Im U)ᵀ`. -/
theorem rank_souriau_sub_one (U : unitaryGroup n ℂ) :
    ((souriau U : Matrix n n ℂ) - 1).rank = ((U : Matrix n n ℂ).map Complex.im).rank := by
  have hU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := (mem_unitaryGroup_iff).1 U.2
  have h1 : (souriau U : Matrix n n ℂ) - 1 =
      (U : Matrix n n ℂ) * ((U : Matrix n n ℂ)ᵀ - star (U : Matrix n n ℂ)) := by
    rw [coe_souriau, Matrix.mul_sub, hU]
  have h2 : (U : Matrix n n ℂ)ᵀ - star (U : Matrix n n ℂ) =
      ((2 * Complex.I) • ((U : Matrix n n ℂ).map Complex.im).map ((↑) : ℝ → ℂ))ᵀ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.star_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul, RCLike.star_def]
    rw [Complex.sub_conj]
    push_cast
    ring
  rw [h1, rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse hU), h2,
    rank_transpose, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (by simp)),
    show ((U : Matrix n n ℂ).map Complex.im).map ((↑) : ℝ → ℂ) =
      ((U : Matrix n n ℂ).map Complex.im).map Complex.ofRealHom from rfl, rank_map]

/-- **The eigenvalue `1` of the Souriau map.** The multiplicity of the eigenvalue `1` of
`U Uᵀ` is the dimension of the intersection `U ℝⁿ ∩ ℝⁿ` of the Lagrangian framed by `U` with
`ℝⁿ`. -/
theorem count_roots_charpoly_souriau (U : unitaryGroup n ℂ) :
    (souriau U : Matrix n n ℂ).charpoly.roots.count 1 =
      Module.finrank ℝ ↥((U : Matrix n n ℂ).realImage ⊓ TauCeti.realSubspace n) := by
  have h1 := count_roots_charpoly_add_rank_sub_one (souriau U).2
  have h2 := finrank_realImage_inf_realSubspace_add_rank
    (isUnit_det_of_right_inverse ((mem_unitaryGroup_iff).1 U.2)).ne_zero
  rw [rank_souriau_sub_one] at h1
  omega

/-- **The zero axiom of Robbin and Salamon.** If along a path `γ` of unitary frames the
eigenvalue `1` of the Souriau maps `γ t γ tᵀ` keeps the same multiplicity, then the Maslov index of
`γ` vanishes. -/
theorem maslovIndex_eq_zero_of_count_roots_charpoly_souriau {U V : unitaryGroup n ℂ}
    (γ : Path U V) (h : ∀ t, (souriau (γ t) : Matrix n n ℂ).charpoly.roots.count 1 =
      (souriau U : Matrix n n ℂ).charpoly.roots.count 1) :
    maslovIndex γ = 0 := by
  set W : I → Matrix n n ℂ := fun t => souriau (γ t) with hW
  have hWc : Continuous W := continuous_subtype_val.comp (continuous_souriau.comp γ.continuous)
  have hs : Continuous fun t => spectralAngleSum (W t) :=
    continuous_iff_continuousAt.2 fun t => continuousAt_spectralAngleSum hWc.continuousAt
      (Eventually.of_forall fun s => (souriau (γ s)).2)
      (Eventually.of_forall fun s => (h s).trans (h t).symm)
  obtain ⟨θ, hθ⟩ := Circle.exists_lift (detSouriauPath γ)
  set g : I → ℝ := fun t => θ t - 2 * Real.pi * spectralAngleSum (W t) with hg
  -- `exp (i g)` is the constant sign `(-1)^(n - k)`, `k` the multiplicity of the eigenvalue `1`.
  set m := Fintype.card n - (souriau U : Matrix n n ℂ).charpoly.roots.count 1
  have hexp (t : I) : (Circle.exp (g t) : ℂ) = ((-1) ^ m)⁻¹ := by
    have hdet : (W t).det ≠ 0 := by
      rw [hW, ← coe_detCircle]
      exact Circle.coe_ne_zero _
    have h1 : exp (↑(θ t) * Complex.I) = (W t).det := by
      rw [← Circle.coe_exp, hθ t, detSouriauPath_apply, coe_detCircle]
    have h2 : exp (2 * Real.pi * Complex.I * spectralAngleSum (W t)) = (-1) ^ m * (W t).det := by
      have := exp_two_pi_mul_I_mul_spectralAngleSum (souriau (γ t)).2
      rwa [h t] at this
    rw [Circle.coe_exp, hg]
    dsimp only
    rw [ofReal_sub, sub_mul, exp_sub, h1, ofReal_mul, ofReal_mul, ofReal_ofNat, show
      (2 : ℂ) * ↑Real.pi * ↑(spectralAngleSum (W t)) * Complex.I =
        2 * ↑Real.pi * Complex.I * ↑(spectralAngleSum (W t)) by ring, h2]
    field_simp
  -- A continuous lift of a constant is constant.
  have hgc : Continuous g := θ.continuous.sub (continuous_const.mul hs)
  obtain ⟨c, hc⟩ := Circle.exists_forall_eq_add_of_exp_eq hgc continuous_const
    (fun t => Circle.ext ((hexp t).trans (hexp 0).symm))
  have hc0 : c = 0 := by simpa using hc 0
  have h10 := hc 1
  rw [hc0, add_zero, hg] at h10
  dsimp only at h10
  rw [maslovIndex_def, Circle.angleChange_eq_sub _ θ.continuous hθ]
  have hW0 : W 0 = souriau U := by simp [hW]
  have hW1 : W 1 = souriau V := by simp [hW]
  rw [← hW0, ← hW1]
  field_simp
  linarith

/-- **The zero axiom of Robbin and Salamon.** If along a path `γ` of unitary frames the
intersection `γ t ℝⁿ ∩ ℝⁿ` of the Lagrangians with `ℝⁿ` keeps the same dimension, then the Maslov
index of `γ` relative to `ℝⁿ` vanishes. -/
theorem maslovIndex_eq_zero_of_finrank_realImage_inf_realSubspace {U V : unitaryGroup n ℂ}
    (γ : Path U V)
    (h : ∀ t, Module.finrank ℝ ↥((γ t : Matrix n n ℂ).realImage ⊓ TauCeti.realSubspace n) =
      Module.finrank ℝ ↥((U : Matrix n n ℂ).realImage ⊓ TauCeti.realSubspace n)) :
    maslovIndex γ = 0 :=
  maslovIndex_eq_zero_of_count_roots_charpoly_souriau γ fun t => by
    rw [count_roots_charpoly_souriau, count_roots_charpoly_souriau, h t]

end UnitaryGroup

end Matrix
