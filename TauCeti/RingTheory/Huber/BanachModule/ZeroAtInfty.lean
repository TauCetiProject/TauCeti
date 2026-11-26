/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.RingTheory.Huber.BanachModule.BaseChange
public import TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Completed base change of the model space `C₀(I, R)`

Let `R` be a seminormed commutative ring admitting a sequence of units tending to zero, `I` a
discrete index type and `E` a complete ultrametric normed `R`-module whose scalar action is
bounded, `‖r • m‖ ≤ C * ‖r‖ * ‖m‖`. No common ground field is assumed. Extending the coefficients
of `C₀(I, R)` to `E` by the completed tensor product gives `C₀(I, E)`:

`Θ : C₀(I, R) ⊗̂_R E ≃L[R] C₀(I, E)`,  `Θ (x ⊗ m) i = x i • m`

(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv`). Its inverse sends `y` to the
unconditionally convergent sum `∑' i, eᵢ ⊗ y i`, where `eᵢ = single i 1` is the `i`-th
coordinate vector of `C₀(I, R)`.

For a complete ultrametric normed commutative `R`-algebra `S` this is the completed base change
of the model space along `R → S`. The equivalence intertwines multiplication by `s ∈ S` on the
second tensor factor with the action of `s` on `C₀(I, S)`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map_smul`). When `R` is a normed
commutative Tate ring, the completed tensor extension `u ⊗̂ 1` of an operator `u` between model
spaces is its coefficientwise extension `u.mapCoeffs`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map`), so statements about matrices
of operators over `S` apply to completed base changes.

On a finite tensor presentation `∑ⱼ xⱼ ⊗ mⱼ`, the image has norm at most
`max_j C ‖xⱼ‖ ‖mⱼ‖` (`TauCeti.Huber.BanachModule.CompletedTensor.norm_zeroAtInftyEquiv_sum_le`).
Conversely a finitely supported `y` is the image of the finite presentation `∑ᵢ eᵢ ⊗ y i`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_symm_single`), whose terms satisfy
`‖eᵢ‖ * ‖y i‖ ≤ ‖1‖ * ‖y‖`.

The forward map is the universal property of the completed tensor product applied to the
continuous bilinear map `(x, m) ↦ (x i • m)ᵢ`. Convergence and continuity of the inverse use a
unit `v` of small norm: rewriting `eᵢ ⊗ m = (v eᵢ) ⊗ (v⁻¹ m)` makes the first factor small
uniformly in `i`, so the elementary tensors `eᵢ ⊗ m` tend to zero as `m → 0`, uniformly in `i`.

Composing with `comm` gives the `S`-linear scalar extension `S ⊗̂_R C₀(I, R) ≃L[S] C₀(I, S)`
(`zeroAtInftyBaseChange`). Independently of units in `R`, the completion of `S ⊗[R] C₀(I, R)` for
`TauCeti.Huber.BanachModule.productSeminorm R S C₀(I, R)` is `S`-linearly isomorphic to `C₀(I, S)`
(`c0CompletedBaseChangeEquiv`, `c0_completedBaseChange`, `c0CompletedBaseChangeIsometry`), agreeing
with `S ⊗̂_R C₀(I, R)` when `R` has a zero sequence of units
(`completedTensorEquivProductSeminormCompletion`).

## Main definitions

* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv`: the continuous linear
  equivalence `C₀(I, R) ⊗̂_R E ≃L[R] C₀(I, E)`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyBaseChange`, `c0CompletedBaseChangeEquiv`,
  `c0CompletedBaseChangeIsometry`, `completedTensorEquivProductSeminormCompletion`: `S`-linear
  completed scalar extension of `C₀(I, R)` and its product-seminorm comparison.

## Main results

* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_tmul_apply`: the defining
  equation `Θ (x ⊗ m) i = x i • m`.
* `TauCeti.Huber.BanachModule.CompletedTensor.hasSum_zeroAtInftyEquiv_symm`: the inverse is the
  sum of the elementary tensors `eᵢ ⊗ y i`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_symm_single`: the inverse sends
  the coordinate vector `single i m` to `eᵢ ⊗ m`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map_smul`: compatibility with
  the action of `S`.
* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map`: the tensor extension of an
  operator is its coefficientwise extension.
* `TauCeti.Huber.BanachModule.CompletedTensor.norm_zeroAtInftyEquiv_sum_le`: the norm bound on
  finite tensor presentations.
* `TauCeti.Huber.BanachModule.CompletedTensor.c0_completedBaseChange`: product-seminorm base change
  with forward bound `L` and inverse bound `1`.

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

section ModelSpace

variable (I : Type*) [TopologicalSpace I]
  {R : Type*} [SeminormedCommRing R]
  {E : Type*} [NormedAddCommGroup E] [Module R E] [ContinuousConstSMul R E]

section Forward

variable (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖)

/-- The pointwise action `x ↦ (x i • m)ᵢ` of `C₀(I, R)` on a fixed vector `m`. -/
private noncomputable def coeffMap (m : E) : C₀(I, R) →L[R] C₀(I, E) :=
  have := continuousSMul_of_norm_smul_le hE
  compLeft (ContinuousLinearMap.toSpanSingleton R m) (by
    obtain ⟨C, hC⟩ := hE
    exact ⟨C * ‖m‖, fun r ↦ by simpa [mul_right_comm] using hC r m⟩)

private theorem coeffMap_apply (m : E) (x : C₀(I, R)) (i : I) :
    coeffMap I hE m x i = x i • m :=
  compLeft_apply _ _ x i

/-- The bilinear map `(x, m) ↦ (x i • m)ᵢ` inducing the completed base change. -/
private noncomputable def coeffBilin : C₀(I, R) →ₗ[R] E →ₗ[R] C₀(I, E) :=
  LinearMap.mk₂ R (fun x m ↦ coeffMap I hE m x)
    (fun x x' m ↦ map_add _ x x')
    (fun r x m ↦ map_smul _ r x)
    (fun x m m' ↦ by ext i; simp [coeffMap_apply, smul_add])
    (fun r x m ↦ by ext i; simp [coeffMap_apply, smul_comm r])

private theorem coeffBilin_apply (x : C₀(I, R)) (m : E) (i : I) :
    coeffBilin I hE x m i = x i • m :=
  coeffMap_apply I hE m x i

private theorem continuous_coeffBilin :
    Continuous fun p : C₀(I, R) × E ↦ coeffBilin I hE p.1 p.2 := by
  obtain ⟨C, hC⟩ := hE
  refine LinearMap.continuous₂_of_bound _ C fun x m ↦ (norm_le (by positivity)).2 fun i ↦ ?_
  rw [coeffBilin_apply]
  exact (hC _ _).trans (by gcongr; exact norm_coe_le_norm x i)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- The forward map `C₀(I, R) ⊗̂_R E → C₀(I, E)` of the completed base change. -/
private noncomputable def toZeroAtInfty : CompletedTensor R C₀(I, R) E →L[R] C₀(I, E) :=
  have := continuousSMul_of_norm_smul_le (M := C₀(I, E)) <| hE.imp fun C hC r y ↦
    (norm_le (by positivity)).2 fun i ↦ (hC r (y i)).trans (by gcongr; exact norm_coe_le_norm y i)
  lift (coeffBilin I hE) (continuous_coeffBilin I hE)

private theorem toZeroAtInfty_tmul_apply (x : C₀(I, R)) (m : E) (i : I) :
    toZeroAtInfty I hE (tmul R _ E x m) i = x i • m := by
  simp [toZeroAtInfty, coeffBilin_apply]

end Forward

section Inverse

variable [DiscreteTopology I] [DecidableEq I]

private theorem toZeroAtInfty_tmul_single_one [IsUltrametricDist E] [CompleteSpace E]
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) (i : I) (m : E) :
    toZeroAtInfty I hE (tmul R _ E (single i 1) m) = single i m := by
  ext j
  by_cases h : j = i <;> simp [toZeroAtInfty_tmul_apply, h]

variable [TauCeti.HasZeroSequenceOfUnits R]

/-- **Uniform smallness of coordinate tensors.** The elementary tensors `eᵢ ⊗ m` tend to zero in
`C₀(I, R) ⊗̂_R E` as `m → 0`, uniformly in the coordinate `i`. -/
private theorem tendsto_tmul_single_one :
    Tendsto (fun p : I × E ↦ tmul R C₀(I, R) E (single p.1 1) p.2) (⊤ ×ˢ 𝓝 0) (𝓝 0) := by
  obtain ⟨u, hu⟩ := ‹TauCeti.HasZeroSequenceOfUnits R›.exists_tendsto
  intro U hU
  -- `tmul` is continuous at `(0, 0)`, so it maps a product of neighbourhoods into `U`
  have hcont := (continuous_tmul R C₀(I, R) E).tendsto ((0 : C₀(I, R)), (0 : E))
  simp only [map_zero] at hcont
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp (hcont hU)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  -- some unit `v` of the zero sequence makes every `v • eᵢ` lie in `V`
  obtain ⟨n, hn⟩ := (hu.eventually (Metric.ball_mem_nhds 0 hε)).exists
  let v : Rˣ := u n
  have hW' : (fun m : E ↦ ((v⁻¹ : Rˣ) : R) • m) ⁻¹' W ∈ 𝓝 0 :=
    (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using hW)
  refine mem_map.mpr (mem_of_superset (prod_mem_prod univ_mem hW') ?_)
  rintro ⟨i, m⟩ ⟨-, hm⟩
  have hsingle : single i (v : R) ∈ V := hεV <| by simpa [v, norm_single] using hn
  -- `eᵢ ⊗ m = (v • eᵢ) ⊗ (v⁻¹ • m)`
  have key : tmul R C₀(I, R) E (single i (v : R)) (((v⁻¹ : Rˣ) : R) • m) =
      tmul R C₀(I, R) E (single i 1) m := by
    rw [← smul_single_one i (v : R), LinearMap.map_smul₂, ← map_smul, smul_smul, Units.mul_inv,
      one_smul]
  rw [Set.mem_preimage, ← key]
  exact hVW (Set.mk_mem_prod hsingle hm)

/-- The coordinate tensors `eᵢ ⊗ y i` of a null family `y` are summable. -/
private theorem summable_tmul_single_one (y : C₀(I, E)) :
    Summable fun i ↦ tmul R C₀(I, R) E (single i 1) (y i) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    ((tendsto_tmul_single_one I).comp (tendsto_top.prodMk y.tendsto_cofinite))

/-- The inverse map `C₀(I, E) → C₀(I, R) ⊗̂_R E`, `y ↦ ∑' i, eᵢ ⊗ y i`, as a linear map. -/
private noncomputable def ofZeroAtInftyₗ : C₀(I, E) →ₗ[R] CompletedTensor R C₀(I, R) E where
  toFun y := ∑' i, tmul R C₀(I, R) E (single i 1) (y i)
  map_add' y z := by
    simp only [_root_.add_apply, map_add]
    exact (summable_tmul_single_one I y).tsum_add (summable_tmul_single_one I z)
  map_smul' r y := by
    simp only [_root_.smul_apply, map_smul, RingHom.id_apply]
    exact (summable_tmul_single_one I y).tsum_const_smul r

private theorem continuous_ofZeroAtInftyₗ :
    Continuous (ofZeroAtInftyₗ I (R := R) (E := E)) := by
  refine continuous_of_continuousAt_zero (ofZeroAtInftyₗ I (R := R) (E := E)) ?_
  rw [ContinuousAt, map_zero]
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  -- a ball of coefficients `m` whose coordinate tensors `eᵢ ⊗ m` all lie in `V`
  obtain ⟨t, ht, htV⟩ := mem_comap.mp <| (top_prod (α := I) ▸ tendsto_tmul_single_one I (R := R))
    (V.isOpen.mem_nhds V.zero_mem)
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp ht
  refine mem_map.mpr (mem_of_superset (Metric.ball_mem_nhds (0 : C₀(I, E)) hδ) fun y hy ↦ hVU ?_)
  have hterm (i : I) : tmul R C₀(I, R) E (single i 1) (y i) ∈ V :=
    @htV (i, y i) <| hδt <| mem_ball_zero_iff.mpr <|
      (norm_coe_le_norm y i).trans_lt (mem_ball_zero_iff.mp hy)
  exact V.isClosed.mem_of_tendsto (summable_tmul_single_one I y).hasSum
    (Eventually.of_forall fun F ↦ V.sum_mem fun i _ ↦ hterm i)

/-- The inverse map `C₀(I, E) → C₀(I, R) ⊗̂_R E`. -/
private noncomputable def ofZeroAtInfty : C₀(I, E) →L[R] CompletedTensor R C₀(I, R) E :=
  ⟨ofZeroAtInftyₗ I, continuous_ofZeroAtInftyₗ I⟩

private theorem ofZeroAtInfty_apply (y : C₀(I, E)) :
    ofZeroAtInfty I y = ∑' i, tmul R C₀(I, R) E (single i 1) (y i) :=
  rfl

variable [IsUltrametricDist E] [CompleteSpace E]

private theorem ofZeroAtInfty_toZeroAtInfty
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖)
    (z : CompletedTensor R C₀(I, R) E) : ofZeroAtInfty I (toZeroAtInfty I hE z) = z := by
  suffices (ofZeroAtInfty I).comp (toZeroAtInfty I hE) = .id R _ from
    DFunLike.congr_fun this z
  refine ext fun x m ↦ ?_
  -- `∑' i, eᵢ ⊗ (x i • m) = ∑' i, (x i • eᵢ) ⊗ m = x ⊗ m`
  have hx := (hasSum_single x).map ((tmul R C₀(I, R) E).flip m)
    ((continuous_tmul R C₀(I, R) E).comp (continuous_id.prodMk continuous_const))
  have hcoord (i : I) : tmul R C₀(I, R) E (single i 1) (toZeroAtInfty I hE (tmul R _ E x m) i) =
      (tmul R C₀(I, R) E).flip m (single i (x i)) := by
    rw [toZeroAtInfty_tmul_apply, map_smul, ← LinearMap.map_smul₂, smul_single_one,
      LinearMap.flip_apply]
  simpa [ofZeroAtInfty_apply, hcoord] using hx.tsum_eq

private theorem toZeroAtInfty_ofZeroAtInfty
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) (y : C₀(I, E)) :
    toZeroAtInfty I hE (ofZeroAtInfty I y) = y := by
  have h := (summable_tmul_single_one I y).hasSum.mapL (toZeroAtInfty I hE)
  simp only [toZeroAtInfty_tmul_single_one] at h
  exact h.unique (hasSum_single y)

end Inverse

section Equiv

variable [DiscreteTopology I] [TauCeti.HasZeroSequenceOfUnits R]
  [IsUltrametricDist E] [CompleteSpace E]

/-- **Completed base change of the model space `C₀(I, R)`.** For a complete ultrametric normed
`R`-module `E` with bounded scalar action, extending the coefficients of `C₀(I, R)` to `E` by the
completed tensor product gives `C₀(I, E)`: the elementary tensor `x ⊗ m` goes to `(x i • m)ᵢ`
(`zeroAtInftyEquiv_tmul_apply`), and the inverse sends `y` to `∑' i, eᵢ ⊗ y i`, where `eᵢ` is the
`i`-th coordinate vector of `C₀(I, R)` (`hasSum_zeroAtInftyEquiv_symm`). -/
noncomputable def zeroAtInftyEquiv
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) :
    CompletedTensor R C₀(I, R) E ≃L[R] C₀(I, E) :=
  letI := Classical.decEq I
  .ofContinuousLinearMap (toZeroAtInfty I hE) (ofZeroAtInfty I)
    (ContinuousLinearMap.ext (toZeroAtInfty_ofZeroAtInfty I hE))
    (ContinuousLinearMap.ext (ofZeroAtInfty_toZeroAtInfty I hE))

variable (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖)

/-- **The defining equation of the completed base change**: `x ⊗ m ↦ (x i • m)ᵢ`. -/
@[simp]
theorem zeroAtInftyEquiv_tmul_apply (x : C₀(I, R)) (m : E) (i : I) :
    zeroAtInftyEquiv I hE (tmul R C₀(I, R) E x m) i = x i • m :=
  toZeroAtInfty_tmul_apply I hE x m i

/-- **Norm bound on finite tensor presentations.** If `‖r • m‖ ≤ C * ‖r‖ * ‖m‖`, the image of
`∑ⱼ xⱼ ⊗ mⱼ` has norm at most any bound `b ≥ 0` for the products `C * ‖xⱼ‖ * ‖mⱼ‖`. -/
theorem norm_zeroAtInftyEquiv_sum_le {C : ℝ≥0}
    (hC : ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) {ι : Type*} (F : Finset ι)
    (x : ι → C₀(I, R)) (m : ι → E) {b : ℝ} (hb : 0 ≤ b)
    (hxm : ∀ j ∈ F, C * ‖x j‖ * ‖m j‖ ≤ b) :
    ‖zeroAtInftyEquiv I ⟨C, hC⟩ (∑ j ∈ F, tmul R C₀(I, R) E (x j) (m j))‖ ≤ b := by
  refine (norm_le hb).2 fun i ↦ ?_
  simp only [map_sum, FunLike.coe_sum, Finset.sum_apply, zeroAtInftyEquiv_tmul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun j hj ↦ ?_
  calc ‖x j i • m j‖ ≤ C * ‖x j i‖ * ‖m j‖ := hC _ _
    _ ≤ C * ‖x j‖ * ‖m j‖ := by gcongr; exact norm_coe_le_norm _ _
    _ ≤ b := hxm j hj

section Coordinates

variable [DecidableEq I]

/-- **The inverse of the completed base change** sends `y` to the unconditionally convergent sum
of the elementary tensors `eᵢ ⊗ y i`. -/
theorem hasSum_zeroAtInftyEquiv_symm (y : C₀(I, E)) :
    HasSum (fun i ↦ tmul R C₀(I, R) E (single i 1) (y i)) ((zeroAtInftyEquiv I hE).symm y) := by
  rw [(zeroAtInftyEquiv I hE).symm_apply_eq.mpr (toZeroAtInfty_ofZeroAtInfty I hE y).symm]
  exact (summable_tmul_single_one I y).hasSum

/-- The inverse of the completed base change as an unconditional sum. -/
theorem zeroAtInftyEquiv_symm_apply (y : C₀(I, E)) :
    (zeroAtInftyEquiv I hE).symm y = ∑' i, tmul R C₀(I, R) E (single i 1) (y i) :=
  (hasSum_zeroAtInftyEquiv_symm I hE y).tsum_eq.symm

/-- The inverse of the completed base change sends the coordinate vector `single i m` of
`C₀(I, E)` to the elementary tensor `eᵢ ⊗ m`. -/
@[simp]
theorem zeroAtInftyEquiv_symm_single (i : I) (m : E) :
    (zeroAtInftyEquiv I hE).symm (single i m) = tmul R C₀(I, R) E (single i 1) m :=
  (zeroAtInftyEquiv I hE).symm_apply_eq.mpr (toZeroAtInfty_tmul_single_one I hE i m).symm

end Coordinates

end Equiv

end ModelSpace

section ScalarExtension

variable (I : Type*) [TopologicalSpace I]
  {R : Type*} [SeminormedCommRing R]
  {S : Type*} [NormedCommRing S] [Algebra R S]

private theorem comm_smul_eq_map_smul (s : S) (z : CompletedTensor R S C₀(I, R)) :
    comm R S C₀(I, R) (s • z) =
      map (.id R C₀(I, R)) (s • ContinuousLinearMap.id R S) (comm R S C₀(I, R) z) := by
  let f := (map (.id R C₀(I, R)) (s • ContinuousLinearMap.id R S)).comp
    (comm R S C₀(I, R)).toContinuousLinearMap
  refine (denseRange_toCompletion R S C₀(I, R)).induction_on z
    (isClosed_eq ((comm R S C₀(I, R)).continuous.comp (continuous_const_smul s)) f.continuous)
    fun u ↦ TensorProduct.inductionOn u (fun _ _ ↦ by simp) fun _ _ hu hv ↦ by
      simp only [smul_add, map_add, hu, hv]

variable [DiscreteTopology I] [TauCeti.HasZeroSequenceOfUnits R]
  [IsUltrametricDist S] [CompleteSpace S]

section BaseChange

variable (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

/-- **Compatibility with the action of `S`.** For an `R`-algebra `S`, multiplication by `s ∈ S` on
the second factor of `C₀(I, R) ⊗̂_R S` corresponds to the action of `s` on `C₀(I, S)`. -/
theorem zeroAtInftyEquiv_map_smul (s : S) (z : CompletedTensor R C₀(I, R) S) :
    zeroAtInftyEquiv I hS (map (.id R C₀(I, R)) (s • .id R S) z) =
      s • zeroAtInftyEquiv I hS z := by
  suffices (zeroAtInftyEquiv I hS : _ →L[R] C₀(I, S)).comp
      (map (.id R C₀(I, R)) (s • .id R S)) = s • (zeroAtInftyEquiv I hS : _ →L[R] C₀(I, S)) from
    DFunLike.congr_fun this z
  refine ext fun x t ↦ ?_
  ext i
  simp

private noncomputable def zeroAtInftyBaseChangeCLM :
    CompletedTensor R S C₀(I, R) →L[S] C₀(I, S) where
  toFun z := zeroAtInftyEquiv I hS (comm R S C₀(I, R) z)
  map_add' _ _ := by simp
  map_smul' s z := by rw [comm_smul_eq_map_smul, zeroAtInftyEquiv_map_smul, RingHom.id_apply]
  cont := (zeroAtInftyEquiv I hS).continuous.comp (comm R S C₀(I, R)).continuous

private noncomputable def zeroAtInftyBaseChangeInvCLM :
    C₀(I, S) →L[S] CompletedTensor R S C₀(I, R) where
  toFun y := comm R C₀(I, R) S ((zeroAtInftyEquiv I hS).symm y)
  map_add' _ _ := by simp
  map_smul' s y := ((zeroAtInftyEquiv I hS).injective.comp (comm R S C₀(I, R)).injective) <| by
    simp only [Function.comp_apply, RingHom.id_apply]
    rw [comm_smul_eq_map_smul, zeroAtInftyEquiv_map_smul]; simp
  cont := (comm R C₀(I, R) S).continuous.comp (zeroAtInftyEquiv I hS).symm.continuous

/-- **`S`-linear completed scalar extension of `C₀(I, R)`.** For a complete ultrametric normed
commutative `R`-algebra `S` with bounded `R`-action `hS`, `S ⊗̂_R C₀(I, R) ≃L[S] C₀(I, S)` sends
`s ⊗ x` to `(s * algebraMap R S (x i))ᵢ` (`zeroAtInftyBaseChange_tmul_apply`), with inverse
`y ↦ ∑' i, y i ⊗ eᵢ` (`hasSum_zeroAtInftyBaseChange_symm`). -/
noncomputable def zeroAtInftyBaseChange : CompletedTensor R S C₀(I, R) ≃L[S] C₀(I, S) :=
  .ofContinuousLinearMap (zeroAtInftyBaseChangeCLM I hS) (zeroAtInftyBaseChangeInvCLM I hS)
    (ContinuousLinearMap.ext fun _ ↦ by
      simp [zeroAtInftyBaseChangeCLM, zeroAtInftyBaseChangeInvCLM])
    (ContinuousLinearMap.ext fun _ ↦ by
      simp [zeroAtInftyBaseChangeCLM, zeroAtInftyBaseChangeInvCLM])

/-- `zeroAtInftyBaseChange` is `comm` followed by `zeroAtInftyEquiv`. -/
theorem zeroAtInftyBaseChange_apply (z : CompletedTensor R S C₀(I, R)) :
    zeroAtInftyBaseChange I hS z = zeroAtInftyEquiv I hS (comm R S C₀(I, R) z) := (rfl)

/-- `zeroAtInftyBaseChange.symm` is `zeroAtInftyEquiv.symm` followed by `comm`. -/
theorem zeroAtInftyBaseChange_symm_eq (y : C₀(I, S)) :
    (zeroAtInftyBaseChange I hS).symm y = comm R C₀(I, R) S ((zeroAtInftyEquiv I hS).symm y) :=
  (rfl)

/-- **The defining equation of `zeroAtInftyBaseChange`**: `s ⊗ x ↦ (s * algebraMap R S (x i))ᵢ`. -/
@[simp]
theorem zeroAtInftyBaseChange_tmul_apply (s : S) (x : C₀(I, R)) (i : I) :
    zeroAtInftyBaseChange I hS (tmul R S C₀(I, R) s x) i = s * algebraMap R S (x i) := by
  rw [zeroAtInftyBaseChange_apply, comm_tmul, zeroAtInftyEquiv_tmul_apply, Algebra.smul_def,
    mul_comm]

end BaseChange

/-- Joint continuity of the `S`-action on `S ⊗̂_R C₀(I, R)`. -/
theorem continuousSMul_completedTensor_zeroAtInfty
    (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    ContinuousSMul S (CompletedTensor R S C₀(I, R)) :=
  let e := zeroAtInftyBaseChange I hS
  ⟨(e.symm.continuous.comp <|
    continuous_smul.comp (continuous_id.prodMap e.continuous)).congr fun _ ↦ by simp [e]⟩

section Coordinates

variable (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) [DecidableEq I]

/-- **The inverse of `zeroAtInftyBaseChange`** sends `y` to `∑' i, y i ⊗ eᵢ`. -/
theorem hasSum_zeroAtInftyBaseChange_symm (y : C₀(I, S)) :
    HasSum (fun i ↦ tmul R S C₀(I, R) (y i) (single i 1))
      ((zeroAtInftyBaseChange I hS).symm y) := by
  simpa [zeroAtInftyBaseChange, zeroAtInftyBaseChangeInvCLM] using
    (hasSum_zeroAtInftyEquiv_symm I hS y).mapL (comm R C₀(I, R) S).toContinuousLinearMap

/-- The inverse of `zeroAtInftyBaseChange` as an unconditional sum. -/
theorem zeroAtInftyBaseChange_symm_apply (y : C₀(I, S)) :
    (zeroAtInftyBaseChange I hS).symm y = ∑' i, tmul R S C₀(I, R) (y i) (single i 1) :=
  (hasSum_zeroAtInftyBaseChange_symm I hS y).tsum_eq.symm

/-- `zeroAtInftyBaseChange.symm` sends `single i s` to `s ⊗ eᵢ`. -/
@[simp]
theorem zeroAtInftyBaseChange_symm_single (i : I) (s : S) :
    (zeroAtInftyBaseChange I hS).symm (single i s) = tmul R S C₀(I, R) s (single i 1) := by
  rw [zeroAtInftyBaseChange_symm_eq, zeroAtInftyEquiv_symm_single, comm_tmul]

end Coordinates

end ScalarExtension

section NormedRing

variable (I : Type*) [TopologicalSpace I] [DiscreteTopology I]
  {R : Type*} [NormedCommRing R]

section Self

variable [TauCeti.HasZeroSequenceOfUnits R]

/-- **Identity base change of `C₀(I, R)`.** When `S = R`, `zeroAtInftyBaseChange` coincides with the
unit isomorphism `lid R C₀(I, R)`. -/
theorem zeroAtInftyBaseChange_self [IsUltrametricDist R] [CompleteSpace R]
    (z : CompletedTensor R R C₀(I, R)) :
    zeroAtInftyBaseChange I ⟨1, fun r s ↦ by simpa using norm_mul_le r s⟩ z =
      lid R C₀(I, R) z :=
  (denseRange_toCompletion R R C₀(I, R)).induction_on z
    (isClosed_eq (zeroAtInftyBaseChange I _).continuous (lid R C₀(I, R)).continuous) fun u ↦
    TensorProduct.inductionOn u (fun _ _ ↦ by ext i; simp) fun _ _ hu hv ↦ by
      simp only [map_add, hu, hv]

end Self

section MapCoeffs

variable [TauCeti.NormedRing.IsTate R]
  {S : Type*} [NormedCommRing S] [Algebra R S] [IsUltrametricDist S] [CompleteSpace S]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)
  {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]

/-- **Coefficientwise extension of operators.** For a Tate ring `R` and an `R`-algebra `S` with
bounded action `hS`, the completed tensor extension `u ⊗̂ 1` of an operator
`u : C₀(J, R) →L[R] C₀(I, R)` is its coefficientwise extension `u.mapCoeffs`, the operator over `S`
with matrix `u.matrixCoeff.map (algebraMap R S)`. The structure-map bound that `mapCoeffs` requires
follows from `hS` (`TauCeti.exists_norm_algebraMap_le_of_norm_smul_le`). -/
theorem zeroAtInftyEquiv_map
    (u : C₀(J, R) →L[R] C₀(I, R)) (z : CompletedTensor R C₀(J, R) S) :
    zeroAtInftyEquiv I hS (map u (.id R S) z) =
      u.mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS)
        (zeroAtInftyEquiv J hS z) := by
  have hφ := exists_norm_algebraMap_le_of_norm_smul_le hS
  suffices (zeroAtInftyEquiv I hS : _ →L[R] C₀(I, S)).comp (map u (.id R S)) =
      ((u.mapCoeffs (algebraMap R S) hφ).restrictScalars R).comp
        (zeroAtInftyEquiv J hS : _ →L[R] C₀(J, S)) from DFunLike.congr_fun this z
  have := continuousSMul_of_norm_smul_le hS
  refine ext fun x s ↦ ?_
  ext i
  -- both sides are the sum over `j` of `(u.matrixCoeff i j * x j) • s`
  have hu := (u.hasSum_matrixCoeff_mul x i).map (LinearMap.toSpanSingleton R S s)
    (continuous_id.smul continuous_const)
  have hv := (u.mapCoeffs (algebraMap R S) hφ).hasSum_matrixCoeff_mul
    (zeroAtInftyEquiv J hS (tmul R C₀(J, R) S x s)) i
  have hterm (j : J) : algebraMap R S (u.matrixCoeff i j) * (x j • s) =
      (u.matrixCoeff i j * x j) • s := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  simp only [ContinuousLinearMap.matrixCoeff_mapCoeffs, Matrix.map_apply,
    zeroAtInftyEquiv_tmul_apply, hterm] at hv
  simpa using hu.unique hv

/-- **Intertwining of `baseChange` with `mapCoeffs`.** For a Tate ring `R` and bounded `R`-algebra
`S`, `zeroAtInftyBaseChange` identifies `baseChange S u` with `u.mapCoeffs (algebraMap R S) _`. -/
theorem zeroAtInftyBaseChange_baseChange
    (u : C₀(J, R) →L[R] C₀(I, R)) (z : CompletedTensor R S C₀(J, R)) :
    zeroAtInftyBaseChange I hS (baseChange S u z) =
      u.mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS)
        (zeroAtInftyBaseChange J hS z) := by
  rw [zeroAtInftyBaseChange_apply, baseChange_apply, comm_map_apply, zeroAtInftyEquiv_map I hS u,
    ← zeroAtInftyBaseChange_apply]

/-- Operator-level intertwining `(zeroAtInftyBaseChange I hS) ∘ (baseChange S u) ∘
(zeroAtInftyBaseChange J hS)⁻¹ = u.mapCoeffs`. -/
theorem zeroAtInftyBaseChange_comp_baseChange_comp_symm
    (u : C₀(J, R) →L[R] C₀(I, R)) :
    (zeroAtInftyBaseChange I hS).toContinuousLinearMap.comp
      ((baseChange S u).comp (zeroAtInftyBaseChange J hS).symm.toContinuousLinearMap) =
        u.mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS) := by
  ext y i
  simp [ContinuousLinearMap.comp_apply, zeroAtInftyBaseChange_baseChange]

end MapCoeffs

end NormedRing

section ProductSeminorm

open scoped TensorProduct
open UniformSpace

variable (I : Type*) [TopologicalSpace I]
  {R : Type*} [SeminormedCommRing R]
  {S : Type*} [NormedCommRing S] [Algebra R S]

private noncomputable def c0AlgForward
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    S ⊗[R] C₀(I, R) →ₗ[S] C₀(I, S) :=
  { toFun := TensorProduct.lift (coeffBilin I (exists_norm_smul_le_of_norm_algebraMap_le hφ)).flip
    map_add' := map_add _
    map_smul' := fun t z ↦ TensorProduct.inductionOn z
      (fun s x ↦ by
        ext i
        simp only [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.lift.tmul,
          LinearMap.flip_apply, coeffBilin_apply, Algebra.smul_def, RingHom.id_apply,
          _root_.smul_apply]
        ring)
      fun _ _ hu hv ↦ by simp only [smul_add, map_add, RingHom.id_apply] at hu hv ⊢; rw [hu, hv] }

private theorem c0AlgForward_tmul_apply
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (s : S) (x : C₀(I, R)) (i : I) :
    c0AlgForward I hφ (s ⊗ₜ[R] x) i = s * algebraMap R S (x i) := by
  simp [c0AlgForward, coeffBilin_apply, Algebra.smul_def, mul_comm]

private theorem norm_c0AlgForward_le [IsUltrametricDist S] {L : ℝ}
    (hφ : ∀ r : R, ‖algebraMap R S r‖ ≤ L * ‖r‖) (z : S ⊗[R] C₀(I, R)) :
    ‖c0AlgForward I (exists_nnreal_norm_le_of_norm_le hφ) z‖ ≤
      L * BanachModule.productSeminorm R S C₀(I, R) z := by
  rcases le_or_gt 0 L with hL | hL
  · exact BanachModule.norm_lift_le_mul_productSeminorm
      (coeffBilin I (exists_norm_smul_le_of_norm_algebraMap_le
        (exists_nnreal_norm_le_of_norm_le hφ))).flip hL
      (fun s x ↦ (norm_le (by positivity)).2 fun i ↦ by
        rw [LinearMap.flip_apply, coeffBilin_apply, Algebra.smul_def, mul_comm]
        calc ‖s * algebraMap R S (x i)‖ ≤ ‖s‖ * ‖algebraMap R S (x i)‖ := norm_mul_le _ _
          _ ≤ ‖s‖ * (L * ‖x i‖) := mul_le_mul_of_nonneg_left (hφ _) (norm_nonneg _)
          _ ≤ ‖s‖ * (L * ‖x‖) := by gcongr; exact norm_coe_le_norm x i
          _ = L * ‖s‖ * ‖x‖ := by ring) z
  · have h1norm : ‖(1 : S)‖ ≤ L * ‖(1 : R)‖ := by simpa using hφ 1
    have h1 : (1 : S) = 0 := norm_eq_zero.mp <| le_antisymm
      (h1norm.trans (mul_nonpos_of_nonpos_of_nonneg hL.le (norm_nonneg _))) (norm_nonneg _)
    have : Subsingleton S := subsingleton_of_zero_eq_one h1.symm
    have hz : z = 0 := Subsingleton.elim z 0
    simp [hz]

/-- The seminormed additive group structure induced by `productSeminorm R S C₀(I, R)`,
registered locally on `S ⊗[R] C₀(I, R)`. -/
noncomputable local instance : SeminormedAddCommGroup (S ⊗[R] C₀(I, R)) :=
  (BanachModule.productSeminorm R S C₀(I, R)).toSeminormedAddCommGroup

local instance : IsBoundedSMul S (S ⊗[R] C₀(I, R)) :=
  IsBoundedSMul.of_norm_smul_le
    (BanachModule.productSeminorm_smul_le (A := R) (S := S) (V := S) (W := C₀(I, R)))

local instance : UniformContinuousConstSMul S (S ⊗[R] C₀(I, R)) :=
  uniformContinuousConstSMul_of_continuousConstSMul S (S ⊗[R] C₀(I, R))

section ProductHelpers

private theorem coe_finset_sum {ι : Type*} (F : Finset ι) (f : ι → S ⊗[R] C₀(I, R)) :
    (∑ i ∈ F, (f i : Completion (S ⊗[R] C₀(I, R)))) = ↑(∑ i ∈ F, f i) :=
  (map_sum Completion.toCompl f F).symm

private theorem summable_c0CoordTensor [DiscreteTopology I] [DecidableEq I] (y : C₀(I, S)) :
    Summable (fun i ↦ ((y i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) :
      Completion (S ⊗[R] C₀(I, R)))) := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have htend : Tendsto (fun i : I ↦ ‖y i‖ * ‖(1 : R)‖) cofinite (𝓝 0) := by
    simpa using ((continuous_norm.tendsto (0 : S)).comp y.tendsto_cofinite).mul_const ‖(1 : R)‖
  have hfin : {i : I | ε / 2 ≤ ‖y i‖ * ‖(1 : R)‖}.Finite :=
    (Filter.eventually_cofinite.mp (htend.eventually (gt_mem_nhds (half_pos hε)))).subset
      fun _ hi ↦ not_lt_of_ge hi
  refine ⟨hfin.toFinset, fun F hF ↦ ?_⟩
  rw [coe_finset_sum I, Completion.norm_coe]
  refine (BanachModule.productSeminorm_sum_tmul_le_of_le F (fun i ↦ y i) (fun i ↦ single i 1)
    (half_pos hε).le fun i hi ↦ ?_).trans_lt (half_lt_self hε)
  have hlt : ‖y i‖ * ‖(1 : R)‖ < ε / 2 :=
    lt_of_not_ge fun hge ↦ Finset.disjoint_left.mp hF hi (hfin.mem_toFinset.mpr hge)
  simpa [norm_single] using hlt.le

private theorem norm_tsum_c0CoordTensor_le [DiscreteTopology I] [DecidableEq I] (y : C₀(I, S)) :
    ‖∑' i : I, ((y i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) : Completion (S ⊗[R] C₀(I, R)))‖ ≤
      ‖(1 : R)‖ * ‖y‖ := by
  refine le_of_tendsto (continuous_norm.tendsto _ |>.comp (summable_c0CoordTensor I y).hasSum)
    (Eventually.of_forall fun F ↦ ?_)
  dsimp only [Function.comp_apply]
  rw [coe_finset_sum I, Completion.norm_coe]
  refine BanachModule.productSeminorm_sum_tmul_le_of_le F (fun i ↦ y i) (fun i ↦ single i 1)
    (by positivity) fun i _ ↦ ?_
  rw [norm_single, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_coe_le_norm y i) (norm_nonneg _)

private noncomputable def c0CompletedInverseCLM [DiscreteTopology I] [DecidableEq I] :
    C₀(I, S) →L[S] Completion (S ⊗[R] C₀(I, R)) :=
  let invₗ : C₀(I, S) →ₗ[S] Completion (S ⊗[R] C₀(I, R)) :=
    { toFun := fun y ↦ ∑' i : I, ((y i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) :
        Completion (S ⊗[R] C₀(I, R)))
      map_add' := fun y w ↦ by
        simp only [_root_.add_apply, TensorProduct.add_tmul, Completion.coe_add]
        exact (summable_c0CoordTensor I y).tsum_add (summable_c0CoordTensor I w)
      map_smul' := fun s y ↦ by
        simp only [_root_.smul_apply, RingHom.id_apply, ← TensorProduct.smul_tmul',
          Completion.coe_smul]
        exact (summable_c0CoordTensor I y).tsum_const_smul s }
  ⟨invₗ, AddMonoidHomClass.continuous_of_bound invₗ ‖(1 : R)‖ (norm_tsum_c0CoordTensor_le I)⟩

private theorem c0CompletedInverseCLM_apply [DiscreteTopology I] [DecidableEq I] (y : C₀(I, S)) :
    c0CompletedInverseCLM I (R := R) y =
      ∑' i : I, ((y i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) : Completion (S ⊗[R] C₀(I, R))) :=
  rfl

private theorem hasSum_c0Coord_tmul [DiscreteTopology I] [DecidableEq I]
    (s : S) (x : C₀(I, R)) :
    HasSum (fun i : I ↦ ((s ⊗ₜ[R] single i (x i) : S ⊗[R] C₀(I, R)) :
      Completion (S ⊗[R] C₀(I, R)))) ((s ⊗ₜ[R] x : S ⊗[R] C₀(I, R)) :
      Completion (S ⊗[R] C₀(I, R))) := by
  rw [HasSum, ← tendsto_sub_nhds_zero_iff, tendsto_iff_norm_sub_tendsto_zero]
  have hx := tendsto_iff_norm_sub_tendsto_zero.mp (hasSum_single x)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun F ↦ ?_) (by simpa using hx.const_mul ‖s‖)
  rw [sub_zero, coe_finset_sum I, ← Completion.coe_sub, ← TensorProduct.tmul_sum,
    ← TensorProduct.tmul_sub, Completion.norm_coe]
  exact BanachModule.productSeminorm_tmul_le s _

variable [IsUltrametricDist S] [CompleteSpace S]

private noncomputable def c0CompletedForwardCLM
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) :
    Completion (S ⊗[R] C₀(I, R)) →L[S] C₀(I, S) :=
  ContinuousLinearMap.fromCompletion
    ⟨c0AlgForward I hφ, by
      obtain ⟨C, hC⟩ := hφ
      exact AddMonoidHomClass.continuous_of_bound (c0AlgForward I ⟨C, hC⟩) C
        (norm_c0AlgForward_le I hC)⟩

private theorem c0CompletedForwardCLM_coe
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) (u : S ⊗[R] C₀(I, R)) :
    c0CompletedForwardCLM I hφ (u : Completion (S ⊗[R] C₀(I, R))) = c0AlgForward I hφ u := by
  simp [c0CompletedForwardCLM]

private theorem c0CompletedForward_inverse [DiscreteTopology I] [DecidableEq I]
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖) (y : C₀(I, S)) :
    c0CompletedForwardCLM I hφ (c0CompletedInverseCLM I y) = y := by
  have hy := (summable_c0CoordTensor I (R := R) y).hasSum.mapL (c0CompletedForwardCLM I hφ)
  have hsingle (i : I) :
      c0CompletedForwardCLM I hφ ((y i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) :
        Completion (S ⊗[R] C₀(I, R))) = single i (y i) := by
    ext j
    by_cases hij : j = i <;> simp [c0CompletedForwardCLM_coe, c0AlgForward_tmul_apply, hij]
  simp only [hsingle] at hy
  rw [c0CompletedInverseCLM_apply]
  exact hy.unique (hasSum_single y)

private theorem c0CompletedInverse_forward [DiscreteTopology I] [DecidableEq I]
    (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (z : Completion (S ⊗[R] C₀(I, R))) :
    c0CompletedInverseCLM I (c0CompletedForwardCLM I hφ z) = z := by
  suffices ((c0CompletedInverseCLM I).comp (c0CompletedForwardCLM I hφ)) z =
      ContinuousLinearMap.id S _ z from this
  refine Completion.induction_on z
    (isClosed_eq ((c0CompletedInverseCLM I).comp (c0CompletedForwardCLM I hφ)).continuous
      continuous_id) fun u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul s x =>
    have hterm (i : I) :
        (((c0CompletedForwardCLM I hφ ↑(s ⊗ₜ[R] x)) i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) :
          Completion (S ⊗[R] C₀(I, R))) =
          ((s ⊗ₜ[R] single i (x i) : S ⊗[R] C₀(I, R)) : Completion (S ⊗[R] C₀(I, R))) := by
      rw [c0CompletedForwardCLM_coe, c0AlgForward_tmul_apply]
      congr 1
      rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, smul_single_one]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      c0CompletedInverseCLM_apply, hterm]
    exact (hasSum_c0Coord_tmul I s x).tsum_eq
  | add u v hu hv => rw [Completion.coe_add, map_add, map_add, hu, hv]

end ProductHelpers

section ProductEquiv

variable [DiscreteTopology I] [IsUltrametricDist S] [CompleteSpace S]
  (hφ : ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖)

/-- **Completed base change of `C₀(I, R)` for the product seminorm.** The separated completion of
`S ⊗[R] C₀(I, R)` for `TauCeti.Huber.BanachModule.productSeminorm R S C₀(I, R)` is `S`-linearly
isomorphic to `C₀(I, S)` via `s ⊗ₜ x ↦ (s * algebraMap R S (x i))ᵢ` (no units in `R` needed). -/
noncomputable def c0CompletedBaseChangeEquiv : Completion (S ⊗[R] C₀(I, R)) ≃L[S] C₀(I, S) :=
  letI := Classical.decEq I
  .ofContinuousLinearMap (c0CompletedForwardCLM I hφ) (c0CompletedInverseCLM I)
    (ContinuousLinearMap.ext (c0CompletedForward_inverse I hφ))
    (ContinuousLinearMap.ext (c0CompletedInverse_forward I hφ))

private theorem c0CompletedBaseChangeEquiv_apply (z : Completion (S ⊗[R] C₀(I, R))) :
    c0CompletedBaseChangeEquiv I hφ z = c0CompletedForwardCLM I hφ z :=
  rfl

/-- `c0CompletedBaseChangeEquiv` sends `s ⊗ₜ x` to `(s * algebraMap R S (x i))ᵢ`. -/
@[simp]
theorem c0CompletedBaseChangeEquiv_coe_tmul_apply (s : S) (x : C₀(I, R)) (i : I) :
    c0CompletedBaseChangeEquiv I hφ ((s ⊗ₜ[R] x : S ⊗[R] C₀(I, R)) :
      Completion (S ⊗[R] C₀(I, R))) i = s * algebraMap R S (x i) := by
  rw [c0CompletedBaseChangeEquiv_apply, c0CompletedForwardCLM_coe, c0AlgForward_tmul_apply]

/-- **Coordinate series of the inverse** `(c0CompletedBaseChangeEquiv I hφ)⁻¹`: the coordinate
elementary tensors `y i ⊗ₜ eᵢ` sum unconditionally to `(c0CompletedBaseChangeEquiv I hφ).symm y`. -/
theorem hasSum_c0CompletedBaseChangeEquiv_symm [DecidableEq I] (y : C₀(I, S)) :
    HasSum (fun i : I ↦ ((y i ⊗ₜ[R] single i 1 : S ⊗[R] C₀(I, R)) :
      Completion (S ⊗[R] C₀(I, R)))) ((c0CompletedBaseChangeEquiv I hφ).symm y) := by
  have hinv : (c0CompletedBaseChangeEquiv I hφ).symm y = c0CompletedInverseCLM I y := by
    rw [ContinuousLinearEquiv.symm_apply_eq, c0CompletedBaseChangeEquiv_apply,
      c0CompletedForward_inverse]
  rw [hinv, c0CompletedInverseCLM_apply]
  exact (summable_c0CoordTensor I (R := R) y).hasSum

/-- Forward norm bound `‖e z‖ ≤ L * ‖z‖` on the product-seminorm completion. -/
theorem norm_c0CompletedBaseChangeEquiv_le {L : ℝ}
    (hφ' : ∀ r : R, ‖algebraMap R S r‖ ≤ L * ‖r‖) (z : Completion (S ⊗[R] C₀(I, R))) :
    ‖c0CompletedBaseChangeEquiv I (exists_nnreal_norm_le_of_norm_le hφ') z‖ ≤ L * ‖z‖ := by
  refine Completion.induction_on z
    (isClosed_le (continuous_norm.comp
      (c0CompletedBaseChangeEquiv I (exists_nnreal_norm_le_of_norm_le hφ')).continuous)
      (continuous_const.mul continuous_norm)) fun u ↦ ?_
  rw [c0CompletedBaseChangeEquiv_apply, c0CompletedForwardCLM_coe, Completion.norm_coe]
  exact norm_c0AlgForward_le I hφ' u

/-- Inverse norm bound `‖e.symm y‖ ≤ ‖(1 : R)‖ * ‖y‖` on the product-seminorm completion. -/
theorem norm_c0CompletedBaseChangeEquiv_symm_le_mul (y : C₀(I, S)) :
    ‖(c0CompletedBaseChangeEquiv I hφ).symm y‖ ≤ ‖(1 : R)‖ * ‖y‖ := by
  let _ := Classical.decEq I
  rw [← (hasSum_c0CompletedBaseChangeEquiv_symm I hφ y).tsum_eq]
  exact norm_tsum_c0CoordTensor_le I (R := R) y

/-- **Product-seminorm completion realises ring-scalar `C₀` extension (`c0_completedBaseChange`).**
When `[NormOneClass R]` and `‖algebraMap R S r‖ ≤ L * ‖r‖`, the completion of `S ⊗[R] C₀(I, R)`
for `TauCeti.Huber.BanachModule.productSeminorm R S C₀(I, R)` is `S`-linearly isomorphic to
`C₀(I, S)` with `‖e z‖ ≤ L * ‖z‖` and `‖e.symm y‖ ≤ ‖y‖`. -/
theorem c0_completedBaseChange [NormOneClass R] {L : ℝ}
    (hφ' : ∀ r : R, ‖algebraMap R S r‖ ≤ L * ‖r‖) :
    ∃ e : Completion (S ⊗[R] C₀(I, R)) ≃L[S] C₀(I, S),
      (∀ (s : S) (x : C₀(I, R)) (i : I),
        e ((s ⊗ₜ[R] x : S ⊗[R] C₀(I, R)) : Completion (S ⊗[R] C₀(I, R))) i =
          s * algebraMap R S (x i)) ∧
      (∀ z, ‖e z‖ ≤ L * ‖z‖) ∧ (∀ y, ‖e.symm y‖ ≤ ‖y‖) := by
  have hφ₀ := exists_nnreal_norm_le_of_norm_le hφ'
  exact ⟨c0CompletedBaseChangeEquiv I hφ₀, c0CompletedBaseChangeEquiv_coe_tmul_apply I hφ₀,
    norm_c0CompletedBaseChangeEquiv_le I hφ', fun y ↦ by
      simpa using norm_c0CompletedBaseChangeEquiv_symm_le_mul I hφ₀ y⟩

/-- **Comparison between `CompletedTensor R S C₀(I, R)` and the product-seminorm completion.**
When `R` has a sequence of units tending to zero, `CompletedTensor R S C₀(I, R)` is `S`-linearly
isomorphic to `Completion (S ⊗[R] C₀(I, R))`, compatibly with `toCompletion`. -/
noncomputable def completedTensorEquivProductSeminormCompletion [TauCeti.HasZeroSequenceOfUnits R] :
    CompletedTensor R S C₀(I, R) ≃L[S] Completion (S ⊗[R] C₀(I, R)) :=
  (zeroAtInftyBaseChange I (exists_norm_smul_le_of_norm_algebraMap_le hφ)).trans
    (c0CompletedBaseChangeEquiv I hφ).symm

/-- `completedTensorEquivProductSeminormCompletion` sends `toCompletion R S C₀(I, R) z` to the
canonical image of `z` in `UniformSpace.Completion (S ⊗[R] C₀(I, R))`. -/
@[simp]
theorem completedTensorEquivProductSeminormCompletion_toCompletion
    [TauCeti.HasZeroSequenceOfUnits R] (z : S ⊗[R] C₀(I, R)) :
    completedTensorEquivProductSeminormCompletion I hφ (toCompletion R S C₀(I, R) z) =
      (z : Completion (S ⊗[R] C₀(I, R))) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    rw [toCompletion_tmul, completedTensorEquivProductSeminormCompletion,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_eq]
    ext i
    simp
  | add u v hu hv => rw [map_add, map_add, Completion.coe_add, hu, hv]

end ProductEquiv

section ProductIsometry

variable [DiscreteTopology I] [IsUltrametricDist S] [CompleteSpace S] [NormOneClass R]
  (hφ : ∀ r : R, ‖algebraMap R S r‖ ≤ ‖r‖)

/-- **Contractive `C₀` completed base change is an isometry.** When `‖algebraMap R S r‖ ≤ ‖r‖` and
`[NormOneClass R]`, `c0CompletedBaseChangeEquiv` upgrades to an isometric equivalence. -/
noncomputable def c0CompletedBaseChangeIsometry : Completion (S ⊗[R] C₀(I, R)) ≃ₗᵢ[S] C₀(I, S) :=
  have hφ1 : ∀ r : R, ‖algebraMap R S r‖ ≤ (1 : ℝ) * ‖r‖ := fun r ↦ by simpa using hφ r
  let e := c0CompletedBaseChangeEquiv I (exists_nnreal_norm_le_of_norm_le hφ1)
  { e.toLinearEquiv with
    norm_map' := fun z ↦ le_antisymm
      (by simpa [e] using norm_c0CompletedBaseChangeEquiv_le I hφ1 z)
      (by
        simpa [e] using
          norm_c0CompletedBaseChangeEquiv_symm_le_mul I
            (exists_nnreal_norm_le_of_norm_le hφ1) (e z)) }

/-- `c0CompletedBaseChangeIsometry` sends `s ⊗ₜ x` to `(s * algebraMap R S (x i))ᵢ`. -/
@[simp]
theorem c0CompletedBaseChangeIsometry_coe_tmul_apply (s : S) (x : C₀(I, R)) (i : I) :
    c0CompletedBaseChangeIsometry I hφ ((s ⊗ₜ[R] x : S ⊗[R] C₀(I, R)) :
      Completion (S ⊗[R] C₀(I, R))) i = s * algebraMap R S (x i) := by
  simp [c0CompletedBaseChangeIsometry]

/-- `c0CompletedBaseChangeIsometry` agrees as a continuous linear equivalence with
`c0CompletedBaseChangeEquiv`. -/
theorem c0CompletedBaseChangeIsometry_toContinuousLinearEquiv :
    (c0CompletedBaseChangeIsometry I hφ).toContinuousLinearEquiv =
      c0CompletedBaseChangeEquiv I ⟨1, fun r ↦ by simpa using hφ r⟩ := by
  refine DFunLike.ext _ _ fun z ↦ Completion.induction_on z
    (isClosed_eq (c0CompletedBaseChangeIsometry I hφ).toContinuousLinearEquiv.continuous
      (c0CompletedBaseChangeEquiv I ⟨1, fun r ↦ by simpa using hφ r⟩).continuous) fun u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul s x => ext i; simp [LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  | add u v hu hv => rw [Completion.coe_add, map_add, map_add, hu, hv]

end ProductIsometry

end ProductSeminorm

end TauCeti.Huber.BanachModule.CompletedTensor
