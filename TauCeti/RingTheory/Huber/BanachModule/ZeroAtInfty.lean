/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# Completed base change of the model space `C₀(I, R)`

Let `R` be a normed commutative ring with a multiplicative pseudo-uniformiser, `I` a discrete
index type and `S` a complete ultrametric normed commutative `R`-algebra whose structure map is
bounded, `‖algebraMap R S r‖ ≤ C * ‖r‖`. The coefficients of `R` and `S` need not share a ground
field. Extending the coefficients of `C₀(I, R)` along `R → S` by the completed tensor product
gives the model space over `S`:

`Θ : C₀(I, R) ⊗̂_R S ≃L[R] C₀(I, S)`,  `Θ (x ⊗ s) i = x i • s`

(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv`). Its inverse sends `y` to the
unconditionally convergent sum `∑' i, eᵢ ⊗ y i`, where `eᵢ = single i 1` is the `i`-th
coordinate vector of `C₀(I, R)`. The equivalence intertwines multiplication by `s ∈ S` on the
second tensor factor with the action of `s` on `C₀(I, S)`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map_smul`).

Under this identification the completed tensor extension `u ⊗̂ 1` of an operator `u` between
model spaces is its coefficientwise extension `u.mapCoeffs`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map`), so statements about matrices
of operators over `S` apply to completed base changes.

On a finite tensor presentation `∑ⱼ xⱼ ⊗ sⱼ`, the image has norm at most
`max_j C ‖xⱼ‖ ‖sⱼ‖` (`TauCeti.Huber.BanachModule.CompletedTensor.norm_zeroAtInftyEquiv_sum_le`).
Conversely a finitely supported `y` is the image of the finite presentation `∑ᵢ eᵢ ⊗ y i`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_symm_single`), whose terms satisfy
`‖eᵢ‖ * ‖y i‖ ≤ ‖y‖` since `‖eᵢ‖ = ‖1‖ = 1`.

The forward map is the universal property of the completed tensor product applied to the
continuous bilinear map `(x, s) ↦ (x i • s)ᵢ`. Convergence and continuity of the inverse use the
pseudo-uniformiser `ϖ`: rewriting `eᵢ ⊗ s = (ϖⁿ eᵢ) ⊗ (ϖ⁻ⁿ s)` makes the first factor small
uniformly in `i`, so the elementary tensors `eᵢ ⊗ s` tend to zero as `s → 0`, uniformly in `i`.

## Main definitions

* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv`: the continuous linear
  equivalence `C₀(I, R) ⊗̂_R S ≃L[R] C₀(I, S)`.

## Main results

* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_tmul_apply`: the defining
  equation `Θ (x ⊗ s) i = x i • s`.
* `TauCeti.Huber.BanachModule.CompletedTensor.hasSum_zeroAtInftyEquiv_symm`: the inverse is the
  sum of the elementary tensors `eᵢ ⊗ y i`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_symm_single`: the inverse sends
  the coordinate vector `single i s` to `eᵢ ⊗ s`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map_smul`: compatibility with
  the action of `S`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map`: the tensor extension of an
  operator is its coefficientwise extension.
* `TauCeti.Huber.BanachModule.CompletedTensor.norm_zeroAtInftyEquiv_sum_le`: the norm bound on
  finite tensor presentations.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §1.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.2, proof of Lemma 2.2.9.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty NNReal

namespace TauCeti.Huber.BanachModule.CompletedTensor

variable (I : Type*) [TopologicalSpace I] [DiscreteTopology I]
  {R : Type*} [NormedCommRing R]
  {S : Type*} [NormedCommRing S] [Algebra R S]

section Forward

omit [DiscreteTopology I]

/-- The coefficientwise structure map `C₀(I, R) → C₀(I, S)`. -/
private noncomputable def coeffMap (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    C₀(I, R) →L[R] C₀(I, S) :=
  have := continuousSMul_of_algebraMap R S <|
    hφ.elim fun C hC ↦ AddMonoidHomClass.continuous_of_bound _ C hC
  compLeft (algebraMapCLM R S) (by
    obtain ⟨C, hC⟩ := hφ
    exact ⟨C, fun r ↦ by simpa [coe_algebraMapCLM] using hC r⟩)

private theorem coeffMap_apply (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (x : C₀(I, R)) (i : I) : coeffMap I hφ x i = algebraMap R S (x i) :=
  compLeft_apply _ _ x i

/-- The bilinear map `(x, s) ↦ (x i • s)ᵢ` inducing the completed base change. -/
private noncomputable def coeffBilin (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    C₀(I, R) →ₗ[R] S →ₗ[R] C₀(I, S) :=
  LinearMap.mk₂ R (fun x s ↦ s • coeffMap I hφ x)
    (fun x x' s ↦ by rw [map_add]; exact smul_add s (coeffMap I hφ x) (coeffMap I hφ x'))
    (fun r x s ↦ by rw [map_smul]; exact smul_comm s r (coeffMap I hφ x))
    (fun x s s' ↦ add_smul s s' (coeffMap I hφ x))
    (fun r x s ↦ smul_assoc r s (coeffMap I hφ x))

private theorem coeffBilin_apply (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (x : C₀(I, R)) (s : S) (i : I) : coeffBilin I hφ x s i = x i • s := by
  simp [coeffBilin, coeffMap_apply, Algebra.smul_def, mul_comm]

private theorem continuous_coeffBilin (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    Continuous fun p : C₀(I, R) × S ↦ coeffBilin I hφ p.1 p.2 :=
  continuous_snd.smul ((coeffMap I hφ).continuous.comp continuous_fst)

variable [IsUltrametricDist S] [CompleteSpace S]

/-- The forward map `C₀(I, R) ⊗̂_R S → C₀(I, S)` of the completed base change. -/
private noncomputable def toZeroAtInfty (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    CompletedTensor R C₀(I, R) S →L[R] C₀(I, S) :=
  have := continuousSMul_of_algebraMap R S <|
    hφ.elim fun C hC ↦ AddMonoidHomClass.continuous_of_bound _ C hC
  have : ContinuousSMul R C₀(I, S) := IsScalarTower.continuousSMul S
  lift (coeffBilin I hφ) (continuous_coeffBilin I hφ)

private theorem toZeroAtInfty_tmul_apply
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) (x : C₀(I, R)) (s : S) (i : I) :
    toZeroAtInfty I hφ (tmul R _ S x s) i = x i • s := by
  simp [toZeroAtInfty, coeffBilin_apply]

end Forward

private theorem toZeroAtInfty_tmul_single_one [DecidableEq I] [IsUltrametricDist S]
    [CompleteSpace S] (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) (i : I) (s : S) :
    toZeroAtInfty I hφ (tmul R _ S (single i 1) s) = single i s := by
  ext j
  by_cases h : j = i <;> simp [toZeroAtInfty_tmul_apply, h]

section Inverse

variable [DecidableEq I] [TauCeti.NormedRing.IsTate R]

/-- **Uniform smallness of coordinate tensors.** The elementary tensors `eᵢ ⊗ s` tend to zero in
`C₀(I, R) ⊗̂_R S` as `s → 0`, uniformly in the coordinate `i`. -/
private theorem tendsto_tmul_single_one :
    Tendsto (fun p : I × S ↦ tmul R C₀(I, R) S (single p.1 1) p.2) (⊤ ×ˢ 𝓝 0) (𝓝 0) := by
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  intro U hU
  -- `tmul` is continuous at `(0, 0)`, so it maps a product of neighbourhoods into `U`
  have hcont := (continuous_tmul R C₀(I, R) S).tendsto ((0 : C₀(I, R)), (0 : S))
  simp only [map_zero] at hcont
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp (hcont hU)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  -- some power `u` of the pseudo-uniformiser makes every `u • eᵢ` lie in `V`
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one ϖ.norm_lt_one).eventually
    (Metric.ball_mem_nhds 0 hε)).exists
  let u : Rˣ := ϖ.unit ^ n
  have hW' : (fun s : S ↦ ((u⁻¹ : Rˣ) : R) • s) ⁻¹' W ∈ 𝓝 0 :=
    (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using hW)
  refine mem_map.mpr (mem_of_superset (prod_mem_prod univ_mem hW') ?_)
  rintro ⟨i, s⟩ ⟨-, hs⟩
  have hsingle : single i (u : R) ∈ V := hεV <| by simpa [u, norm_single] using hn
  -- `eᵢ ⊗ s = (u • eᵢ) ⊗ (u⁻¹ • s)`
  have key : tmul R C₀(I, R) S (single i (u : R)) (((u⁻¹ : Rˣ) : R) • s) =
      tmul R C₀(I, R) S (single i 1) s := by
    rw [← smul_single_one i (u : R), LinearMap.map_smul₂, ← map_smul, smul_smul, Units.mul_inv,
      one_smul]
  rw [Set.mem_preimage, ← key]
  exact hVW (Set.mk_mem_prod hsingle hs)

/-- The coordinate tensors `eᵢ ⊗ y i` of a null family `y` are summable. -/
private theorem summable_tmul_single_one (y : C₀(I, S)) :
    Summable fun i ↦ tmul R C₀(I, R) S (single i 1) (y i) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    ((tendsto_tmul_single_one I).comp (tendsto_top.prodMk y.tendsto_cofinite))

/-- The inverse map `C₀(I, S) → C₀(I, R) ⊗̂_R S`, `y ↦ ∑' i, eᵢ ⊗ y i`, as a linear map. -/
private noncomputable def ofZeroAtInftyₗ : C₀(I, S) →ₗ[R] CompletedTensor R C₀(I, R) S where
  toFun y := ∑' i, tmul R C₀(I, R) S (single i 1) (y i)
  map_add' y z := by
    simp only [_root_.add_apply, map_add]
    exact (summable_tmul_single_one I y).tsum_add (summable_tmul_single_one I z)
  map_smul' r y := by
    simp only [_root_.smul_apply, map_smul, RingHom.id_apply]
    exact (summable_tmul_single_one I y).tsum_const_smul r

private theorem continuous_ofZeroAtInftyₗ :
    Continuous (ofZeroAtInftyₗ I (R := R) (S := S)) := by
  refine continuous_of_continuousAt_zero (ofZeroAtInftyₗ I (R := R) (S := S)) ?_
  rw [ContinuousAt, map_zero]
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  -- a ball of coefficients `s` whose coordinate tensors `eᵢ ⊗ s` all lie in `V`
  obtain ⟨t, ht, htV⟩ := mem_comap.mp <| (top_prod (α := I) ▸ tendsto_tmul_single_one I (R := R))
    (V.isOpen.mem_nhds V.zero_mem)
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp ht
  refine mem_map.mpr (mem_of_superset (Metric.ball_mem_nhds (0 : C₀(I, S)) hδ) fun y hy ↦ hVU ?_)
  have hterm (i : I) : tmul R C₀(I, R) S (single i 1) (y i) ∈ V :=
    @htV (i, y i) <| hδt <| mem_ball_zero_iff.mpr <|
      (norm_coe_le_norm y i).trans_lt (mem_ball_zero_iff.mp hy)
  exact V.isClosed.mem_of_tendsto (summable_tmul_single_one I y).hasSum
    (Eventually.of_forall fun F ↦ V.sum_mem fun i _ ↦ hterm i)

/-- The inverse map `C₀(I, S) → C₀(I, R) ⊗̂_R S`. -/
private noncomputable def ofZeroAtInfty : C₀(I, S) →L[R] CompletedTensor R C₀(I, R) S :=
  ⟨ofZeroAtInftyₗ I, continuous_ofZeroAtInftyₗ I⟩

private theorem ofZeroAtInfty_apply (y : C₀(I, S)) :
    ofZeroAtInfty I y = ∑' i, tmul R C₀(I, R) S (single i 1) (y i) :=
  (rfl)

variable [IsUltrametricDist S] [CompleteSpace S]

private theorem ofZeroAtInfty_toZeroAtInfty
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) (z : CompletedTensor R C₀(I, R) S) :
    ofZeroAtInfty I (toZeroAtInfty I hφ z) = z := by
  suffices (ofZeroAtInfty I).comp (toZeroAtInfty I hφ) = .id R _ from
    DFunLike.congr_fun this z
  refine ext fun x s ↦ ?_
  -- `∑' i, eᵢ ⊗ (x i • s) = ∑' i, (x i • eᵢ) ⊗ s = x ⊗ s`
  have hx := (hasSum_single x).map ((tmul R C₀(I, R) S).flip s)
    ((continuous_tmul R C₀(I, R) S).comp (continuous_id.prodMk continuous_const))
  have hcoord (i : I) : tmul R C₀(I, R) S (single i 1) (toZeroAtInfty I hφ (tmul R _ S x s) i) =
      (tmul R C₀(I, R) S).flip s (single i (x i)) := by
    rw [toZeroAtInfty_tmul_apply, map_smul, ← LinearMap.map_smul₂, smul_single_one,
      LinearMap.flip_apply]
  simpa [ofZeroAtInfty_apply, hcoord] using hx.tsum_eq

private theorem toZeroAtInfty_ofZeroAtInfty
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) (y : C₀(I, S)) :
    toZeroAtInfty I hφ (ofZeroAtInfty I y) = y := by
  have h := (summable_tmul_single_one I y).hasSum.mapL (toZeroAtInfty I hφ)
  simp only [toZeroAtInfty_tmul_single_one] at h
  exact h.unique (hasSum_single y)

end Inverse

variable [TauCeti.NormedRing.IsTate R] [IsUltrametricDist S] [CompleteSpace S]

/-- **Completed base change of the model space `C₀(I, R)`.** For a complete ultrametric
`R`-algebra `S` with bounded structure map, extending the coefficients of `C₀(I, R)` to `S` by the
completed tensor product gives `C₀(I, S)`: the elementary tensor `x ⊗ s` goes to `(x i • s)ᵢ`
(`zeroAtInftyEquiv_tmul_apply`), and the inverse sends `y` to `∑' i, eᵢ ⊗ y i`, where `eᵢ` is the
`i`-th coordinate vector of `C₀(I, R)` (`hasSum_zeroAtInftyEquiv_symm`). -/
noncomputable def zeroAtInftyEquiv (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    CompletedTensor R C₀(I, R) S ≃L[R] C₀(I, S) :=
  letI := Classical.decEq I
  .equivOfInverse (toZeroAtInfty I hφ) (ofZeroAtInfty I) (ofZeroAtInfty_toZeroAtInfty I hφ)
    (toZeroAtInfty_ofZeroAtInfty I hφ)

variable (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)

/-- **The defining equation of the completed base change**: `x ⊗ s ↦ (x i • s)ᵢ`. -/
@[simp]
theorem zeroAtInftyEquiv_tmul_apply (x : C₀(I, R)) (s : S) (i : I) :
    zeroAtInftyEquiv I hφ (tmul R C₀(I, R) S x s) i = x i • s :=
  toZeroAtInfty_tmul_apply I hφ x s i

/-- **Compatibility with the action of `S`.** Multiplication by `s ∈ S` on the second factor of
`C₀(I, R) ⊗̂_R S` corresponds to the action of `s` on `C₀(I, S)`. -/
theorem zeroAtInftyEquiv_map_smul (s : S) (z : CompletedTensor R C₀(I, R) S) :
    zeroAtInftyEquiv I hφ (map (.id R C₀(I, R)) (s • .id R S) z) =
      s • zeroAtInftyEquiv I hφ z := by
  suffices (zeroAtInftyEquiv I hφ : _ →L[R] C₀(I, S)).comp
      (map (.id R C₀(I, R)) (s • .id R S)) = s • (zeroAtInftyEquiv I hφ : _ →L[R] C₀(I, S)) from
    DFunLike.congr_fun this z
  refine ext fun x t ↦ ?_
  ext i
  simp

/-- **Coefficientwise extension of operators.** Under the completed base change, the completed
tensor extension `u ⊗̂ 1` of an operator `u : C₀(J, R) →L[R] C₀(I, R)` is its coefficientwise
extension `u.mapCoeffs`, the operator over `S` with matrix `u.matrixCoeff.map (algebraMap R S)`. -/
theorem zeroAtInftyEquiv_map {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
    (u : C₀(J, R) →L[R] C₀(I, R)) (z : CompletedTensor R C₀(J, R) S) :
    zeroAtInftyEquiv I hφ (map u (.id R S) z) =
      u.mapCoeffs (algebraMap R S) hφ (zeroAtInftyEquiv J hφ z) := by
  suffices (zeroAtInftyEquiv I hφ : _ →L[R] C₀(I, S)).comp (map u (.id R S)) =
      ((u.mapCoeffs (algebraMap R S) hφ).restrictScalars R).comp
        (zeroAtInftyEquiv J hφ : _ →L[R] C₀(J, S)) from DFunLike.congr_fun this z
  have := continuousSMul_of_algebraMap R S <|
    hφ.elim fun C hC ↦ AddMonoidHomClass.continuous_of_bound _ C hC
  refine ext fun x s ↦ ?_
  ext i
  -- both sides are the sum over `j` of `(u.matrixCoeff i j * x j) • s`
  have hu := (u.hasSum_matrixCoeff_mul x i).map (LinearMap.toSpanSingleton R S s)
    (continuous_id.smul continuous_const)
  have hv := (u.mapCoeffs (algebraMap R S) hφ).hasSum_matrixCoeff_mul
    (zeroAtInftyEquiv J hφ (tmul R C₀(J, R) S x s)) i
  have hterm (j : J) : algebraMap R S (u.matrixCoeff i j) * (x j • s) =
      (u.matrixCoeff i j * x j) • s := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  simp only [ContinuousLinearMap.matrixCoeff_mapCoeffs, Matrix.map_apply,
    zeroAtInftyEquiv_tmul_apply, hterm] at hv
  simpa using hu.unique hv

/-- **Norm bound on finite tensor presentations.** If `‖algebraMap R S r‖ ≤ C * ‖r‖`, the image of
`∑ⱼ xⱼ ⊗ sⱼ` has norm at most any bound `b ≥ 0` for the products `C * ‖xⱼ‖ * ‖sⱼ‖`. -/
theorem norm_zeroAtInftyEquiv_sum_le {C : ℝ≥0} (hC : ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    {ι : Type*} (F : Finset ι) (x : ι → C₀(I, R)) (s : ι → S) {b : ℝ} (hb : 0 ≤ b)
    (hxs : ∀ j ∈ F, C * ‖x j‖ * ‖s j‖ ≤ b) :
    ‖zeroAtInftyEquiv I ⟨C, hC⟩ (∑ j ∈ F, tmul R C₀(I, R) S (x j) (s j))‖ ≤ b := by
  refine (norm_le hb).2 fun i ↦ ?_
  simp only [map_sum, coe_sum, Finset.sum_apply, zeroAtInftyEquiv_tmul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun j hj ↦ ?_
  calc ‖x j i • s j‖ ≤ ‖algebraMap R S (x j i)‖ * ‖s j‖ := by
        rw [Algebra.smul_def]; exact norm_mul_le _ _
    _ ≤ C * ‖x j‖ * ‖s j‖ := by
        gcongr
        exact (hC _).trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm _ _) C.coe_nonneg)
    _ ≤ b := hxs j hj

variable [DecidableEq I]

/-- **The inverse of the completed base change** sends `y` to the unconditionally convergent sum
of the elementary tensors `eᵢ ⊗ y i`. -/
theorem hasSum_zeroAtInftyEquiv_symm (y : C₀(I, S)) :
    HasSum (fun i ↦ tmul R C₀(I, R) S (single i 1) (y i)) ((zeroAtInftyEquiv I hφ).symm y) := by
  rw [(zeroAtInftyEquiv I hφ).symm_apply_eq.mpr (toZeroAtInfty_ofZeroAtInfty I hφ y).symm]
  exact (summable_tmul_single_one I y).hasSum

/-- The inverse of the completed base change as an unconditional sum. -/
theorem zeroAtInftyEquiv_symm_apply (y : C₀(I, S)) :
    (zeroAtInftyEquiv I hφ).symm y = ∑' i, tmul R C₀(I, R) S (single i 1) (y i) :=
  (hasSum_zeroAtInftyEquiv_symm I hφ y).tsum_eq.symm

/-- The inverse of the completed base change sends the coordinate vector `single i s` of
`C₀(I, S)` to the elementary tensor `eᵢ ⊗ s`. -/
@[simp]
theorem zeroAtInftyEquiv_symm_single (i : I) (s : S) :
    (zeroAtInftyEquiv I hφ).symm (single i s) = tmul R C₀(I, R) S (single i 1) s :=
  (zeroAtInftyEquiv I hφ).symm_apply_eq.mpr (toZeroAtInfty_tmul_single_one I hφ i s).symm

end TauCeti.Huber.BanachModule.CompletedTensor
