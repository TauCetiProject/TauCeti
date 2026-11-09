/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange

/-!
# Completed base change of the model space `C₀(I, R)`

Let `R` be a normed commutative ring admitting a sequence of units tending to zero, `I` a discrete
index type and `E` a complete ultrametric normed `R`-module whose scalar action is bounded,
`‖r • m‖ ≤ C * ‖r‖ * ‖m‖`. No common ground field is assumed. Extending the coefficients of
`C₀(I, R)` to `E` by the completed tensor product gives `C₀(I, E)`:

`Θ : C₀(I, R) ⊗̂_R E ≃L[R] C₀(I, E)`,  `Θ (x ⊗ m) i = x i • m`

(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv`). Its inverse sends `y` to the
unconditionally convergent sum `∑' i, eᵢ ⊗ y i`, where `eᵢ = single i 1` is the `i`-th
coordinate vector of `C₀(I, R)`.

For a complete ultrametric normed commutative `R`-algebra `S` this is the completed base change
of the model space along `R → S`. The equivalence intertwines multiplication by `s ∈ S` on the
second tensor factor with the action of `s` on `C₀(I, S)`
(`TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv_map_smul`). When `R` has a
multiplicative pseudo-uniformiser, the completed tensor extension `u ⊗̂ 1` of an operator `u`
between model spaces is its coefficientwise extension `u.mapCoeffs`
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

## Main definitions

* `TauCeti.Huber.BanachModule.CompletedTensor.zeroAtInftyEquiv`: the continuous linear
  equivalence `C₀(I, R) ⊗̂_R E ≃L[R] C₀(I, E)`.

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
  {E : Type*} [NormedAddCommGroup E] [Module R E] [ContinuousConstSMul R E]

section Forward

omit [DiscreteTopology I]

/-- The pointwise action `x ↦ (x i • m)ᵢ` of `C₀(I, R)` on a fixed vector `m`. -/
private noncomputable def coeffMap
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) (m : E) :
    C₀(I, R) →L[R] C₀(I, E) :=
  have := continuousSMul_of_norm_smul_le hE
  compLeft (ContinuousLinearMap.toSpanSingleton R m) (by
    obtain ⟨C, hC⟩ := hE
    exact ⟨C * ‖m‖, fun r ↦ by simpa [mul_right_comm] using hC r m⟩)

private theorem coeffMap_apply (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖)
    (m : E) (x : C₀(I, R)) (i : I) : coeffMap I hE m x i = x i • m :=
  compLeft_apply _ _ x i

/-- The bilinear map `(x, m) ↦ (x i • m)ᵢ` inducing the completed base change. -/
private noncomputable def coeffBilin
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) :
    C₀(I, R) →ₗ[R] E →ₗ[R] C₀(I, E) :=
  LinearMap.mk₂ R (fun x m ↦ coeffMap I hE m x)
    (fun x x' m ↦ map_add _ x x')
    (fun r x m ↦ map_smul _ r x)
    (fun x m m' ↦ by ext i; simp [coeffMap_apply, smul_add])
    (fun r x m ↦ by ext i; simp [coeffMap_apply, smul_comm r])

private theorem coeffBilin_apply (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖)
    (x : C₀(I, R)) (m : E) (i : I) : coeffBilin I hE x m i = x i • m :=
  coeffMap_apply I hE m x i

private theorem continuous_coeffBilin
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) :
    Continuous fun p : C₀(I, R) × E ↦ coeffBilin I hE p.1 p.2 := by
  obtain ⟨C, hC⟩ := hE
  refine LinearMap.continuous₂_of_bound _ C fun x m ↦ (norm_le (by positivity)).2 fun i ↦ ?_
  rw [coeffBilin_apply]
  exact (hC _ _).trans (by gcongr; exact norm_coe_le_norm x i)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- The forward map `C₀(I, R) ⊗̂_R E → C₀(I, E)` of the completed base change. -/
private noncomputable def toZeroAtInfty
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) :
    CompletedTensor R C₀(I, R) E →L[R] C₀(I, E) :=
  have := continuousSMul_of_norm_smul_le (M := C₀(I, E)) <| hE.imp fun C hC r y ↦
    (norm_le (by positivity)).2 fun i ↦ (hC r (y i)).trans (by gcongr; exact norm_coe_le_norm y i)
  lift (coeffBilin I hE) (continuous_coeffBilin I hE)

private theorem toZeroAtInfty_tmul_apply
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) (x : C₀(I, R)) (m : E)
    (i : I) : toZeroAtInfty I hE (tmul R _ E x m) i = x i • m := by
  simp [toZeroAtInfty, coeffBilin_apply]

end Forward

private theorem toZeroAtInfty_tmul_single_one [DecidableEq I] [IsUltrametricDist E]
    [CompleteSpace E] (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) (i : I)
    (m : E) : toZeroAtInfty I hE (tmul R _ E (single i 1) m) = single i m := by
  ext j
  by_cases h : j = i <;> simp [toZeroAtInfty_tmul_apply, h]

section Inverse

variable [DecidableEq I] [TauCeti.HasZeroSequenceOfUnits R]

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
  (rfl)

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

variable [TauCeti.HasZeroSequenceOfUnits R] [IsUltrametricDist E] [CompleteSpace E]

/-- **Completed base change of the model space `C₀(I, R)`.** For a complete ultrametric normed
`R`-module `E` with bounded scalar action, extending the coefficients of `C₀(I, R)` to `E` by the
completed tensor product gives `C₀(I, E)`: the elementary tensor `x ⊗ m` goes to `(x i • m)ᵢ`
(`zeroAtInftyEquiv_tmul_apply`), and the inverse sends `y` to `∑' i, eᵢ ⊗ y i`, where `eᵢ` is the
`i`-th coordinate vector of `C₀(I, R)` (`hasSum_zeroAtInftyEquiv_symm`). -/
noncomputable def zeroAtInftyEquiv
    (hE : ∃ C : ℝ≥0, ∀ (r : R) (m : E), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) :
    CompletedTensor R C₀(I, R) E ≃L[R] C₀(I, E) :=
  letI := Classical.decEq I
  .equivOfInverse (toZeroAtInfty I hE) (ofZeroAtInfty I) (ofZeroAtInfty_toZeroAtInfty I hE)
    (toZeroAtInfty_ofZeroAtInfty I hE)

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
  simp only [map_sum, coe_sum, Finset.sum_apply, zeroAtInftyEquiv_tmul_apply]
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

section Algebra

variable {S : Type*} [NormedCommRing S] [Algebra R S] [IsUltrametricDist S] [CompleteSpace S]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

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

/-- **Coefficientwise extension of operators.** For an `R`-algebra `S` with bounded action `hS`,
the completed tensor extension `u ⊗̂ 1` of an operator `u : C₀(J, R) →L[R] C₀(I, R)` is its
coefficientwise extension `u.mapCoeffs`, the operator over `S` with matrix
`u.matrixCoeff.map (algebraMap R S)`. The structure-map bound that `mapCoeffs` requires follows
from `hS` (`TauCeti.exists_norm_algebraMap_le_of_norm_smul_le`). -/
theorem zeroAtInftyEquiv_map [TauCeti.NormedRing.IsTate R]
    {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
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

end Algebra

end TauCeti.Huber.BanachModule.CompletedTensor
