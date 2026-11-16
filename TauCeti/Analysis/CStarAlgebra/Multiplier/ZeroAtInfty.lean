/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import TauCeti.Analysis.Normed.Algebra.DoubleCentralizer
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Multiplier algebra of `C₀(X, A)`

Every bounded continuous function `f : X →ᵇ A` multiplies continuous functions vanishing at
infinity `C₀(X, A)` on both sides, yielding a unital algebra homomorphism
`BoundedContinuousFunction.toDoubleCentralizerAlgHom : (X →ᵇ A) →ₐ[𝕜] 𝓜(𝕜, C₀(X, A))` (and a
`⋆`-algebra homomorphism `BoundedContinuousFunction.toDoubleCentralizerStarAlgHom` when `A` has a
compatible involution) that extends the canonical inclusion `C₀(X, A) → 𝓜(𝕜, C₀(X, A))`.

When `X` is a weakly locally compact `R₁` space (in particular, any locally compact Hausdorff or
compact Hausdorff space) and `A` is a unital normed `𝕜`-algebra that is also a real normed space
(covering `ℝ`, `ℂ`, and every unital complex Banach or C⋆-algebra), Urysohn cutoffs yield an
inverse `DoubleCentralizer.toBCF : 𝓜(𝕜, C₀(X, A)) → (X →ᵇ A)`. Evaluating the centrality relation
`m.snd e * g = e * m.fst g` against a compactly supported bump `e` equal to `1` on a compact
neighborhood of `x` identifies `m.fst g` as pointwise left multiplication by `m.toBCF` and
`m.snd g` as pointwise right multiplication by `m.toBCF`, establishing
`DoubleCentralizer.toBCFAlgEquiv : 𝓜(𝕜, C₀(X, A)) ≃ₐ[𝕜] (X →ᵇ A)` and
`DoubleCentralizer.toBCFStarAlgEquiv : 𝓜(𝕜, C₀(X, A)) ≃⋆ₐ[𝕜] (X →ᵇ A)`. When `‖(1 : A)‖ = 1`
(`NormOneClass A`, automatic for `ℝ`, `ℂ`, and nontrivial unital C⋆-algebras), this equivalence is
isometric (`DoubleCentralizer.toBCFLinearIsometryEquiv`).

## Main definitions

* `BoundedContinuousFunction.toDoubleCentralizer`: the multiplier of `C₀(X, A)` given by
  pointwise left and right multiplication by `f : X →ᵇ A`, bundled as
  `toDoubleCentralizerAlgHom` and `toDoubleCentralizerStarAlgHom`.
* `DoubleCentralizer.toBCF`: the bounded continuous function representing a multiplier
  `m : 𝓜(𝕜, C₀(X, A))`, bundled as `toBCFAlgEquiv`, `toBCFStarAlgEquiv`, and
  `toBCFLinearIsometryEquiv`.

## Main results

* `DoubleCentralizer.fst_apply_eq_toBCF_mul`, `DoubleCentralizer.snd_apply_eq_mul_toBCF`:
  pointwise action of a multiplier of `C₀(X, A)` via `m.toBCF`.
* `DoubleCentralizer.norm_toBCF`, `BoundedContinuousFunction.norm_toDoubleCentralizer`:
  the identification `𝓜(𝕜, C₀(X, A)) ≃ (X →ᵇ A)` is isometric when `[NormOneClass A]`.
* `DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact_nhds_zero`: a multiplier lies in the
  canonical image of `C₀(X, A)` if and only if its bounded continuous function vanishes at
  infinity.

## References

* Bruce Blackadar, *Operator Algebras*, Section II.7.3 (Example II.7.3.12).
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Example 2.47.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction MultiplierAlgebra ZeroAtInfty

namespace BoundedContinuousFunction

section ToDoubleCentralizer

variable {𝕜 X A : Type*} [TopologicalSpace X]

section NonUnital

variable [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

private theorem tendsto_mul_zeroAtInfty (f : X →ᵇ A) (g : C₀(X, A)) :
    Tendsto (fun x => f x * g x) (cocompact X) (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _))) ?_
  simpa only [mul_zero] using
    (tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty g)).const_mul ‖f‖

private theorem tendsto_zeroAtInfty_mul (f : X →ᵇ A) (g : C₀(X, A)) :
    Tendsto (fun x => g x * f x) (cocompact X) (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))) ?_
  simpa only [zero_mul] using
    (tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty g)).mul_const ‖f‖

private def mulLeftZeroAtInfty (f : X →ᵇ A) (g : C₀(X, A)) : C₀(X, A) where
  toFun x := f x * g x
  continuous_toFun := f.continuous.mul g.continuous
  zero_at_infty' := tendsto_mul_zeroAtInfty f g

private def mulRightZeroAtInfty (f : X →ᵇ A) (g : C₀(X, A)) : C₀(X, A) where
  toFun x := g x * f x
  continuous_toFun := g.continuous.mul f.continuous
  zero_at_infty' := tendsto_zeroAtInfty_mul f g

private theorem norm_mulLeftZeroAtInfty_le (f : X →ᵇ A) (g : C₀(X, A)) :
    ‖mulLeftZeroAtInfty f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg f) (norm_nonneg g))]
  intro x
  exact (norm_mul_le _ _).trans <|
    mul_le_mul (f.norm_coe_le_norm x) (g.toBCF.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

private theorem norm_mulRightZeroAtInfty_le (f : X →ᵇ A) (g : C₀(X, A)) :
    ‖mulRightZeroAtInfty f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg f) (norm_nonneg g))]
  intro x
  rw [mul_comm ‖f‖ ‖g‖]
  exact (norm_mul_le _ _).trans <|
    mul_le_mul (g.toBCF.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

private def mulLeftCLM (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 A]
    [SMulCommClass 𝕜 A A] (f : X →ᵇ A) :
    C₀(X, A) →L[𝕜] C₀(X, A) :=
  LinearMap.mkContinuous
    { toFun := mulLeftZeroAtInfty f
      map_add' _ _ := ZeroAtInftyContinuousMap.ext fun _ => mul_add _ _ _
      map_smul' _ _ := ZeroAtInftyContinuousMap.ext fun _ => mul_smul_comm _ _ _ }
    ‖f‖ (norm_mulLeftZeroAtInfty_le f)

private def mulRightCLM (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] (f : X →ᵇ A) :
    C₀(X, A) →L[𝕜] C₀(X, A) :=
  LinearMap.mkContinuous
    { toFun := mulRightZeroAtInfty f
      map_add' _ _ := ZeroAtInftyContinuousMap.ext fun _ => add_mul _ _ _
      map_smul' _ _ := ZeroAtInftyContinuousMap.ext fun _ => smul_mul_assoc _ _ _ }
    ‖f‖ (norm_mulRightZeroAtInfty_le f)

variable (𝕜) in
/-- View a bounded continuous function `f : X →ᵇ A` as a multiplier of `C₀(X, A)` acting by
pointwise left and right multiplication. -/
def toDoubleCentralizer (f : X →ᵇ A) : 𝓜(𝕜, C₀(X, A)) where
  fst := mulLeftCLM 𝕜 f
  snd := mulRightCLM 𝕜 f
  central _ _ := ZeroAtInftyContinuousMap.ext fun _ => mul_assoc _ _ _

/-- The left centralizer of `f.toDoubleCentralizer 𝕜` acts by pointwise left multiplication. -/
@[simp]
theorem toDoubleCentralizer_fst_apply (f : X →ᵇ A) (g : C₀(X, A)) (x : X) :
    (f.toDoubleCentralizer 𝕜).fst g x = f x * g x :=
  (rfl)

/-- The right centralizer of `f.toDoubleCentralizer 𝕜` acts by pointwise right multiplication. -/
@[simp]
theorem toDoubleCentralizer_snd_apply (f : X →ᵇ A) (g : C₀(X, A)) (x : X) :
    (f.toDoubleCentralizer 𝕜).snd g x = g x * f x :=
  (rfl)

/-- `toDoubleCentralizer` is contractive. -/
theorem norm_toDoubleCentralizer_le (f : X →ᵇ A) : ‖f.toDoubleCentralizer 𝕜‖ ≤ ‖f‖ := by
  rw [DoubleCentralizer.norm_def, DoubleCentralizer.toProdHom_apply, Prod.norm_def, max_le_iff]
  exact ⟨ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_mulLeftZeroAtInfty_le f),
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_mulRightZeroAtInfty_le f)⟩

/-- `toDoubleCentralizer` sends `0` to `0`. -/
@[simp]
theorem toDoubleCentralizer_zero : (0 : X →ᵇ A).toDoubleCentralizer 𝕜 = 0 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp)

/-- `toDoubleCentralizer` preserves addition. -/
@[simp]
theorem toDoubleCentralizer_add (f₁ f₂ : X →ᵇ A) :
    (f₁ + f₂).toDoubleCentralizer 𝕜 =
      f₁.toDoubleCentralizer 𝕜 + f₂.toDoubleCentralizer 𝕜 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => add_mul _ _ _)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => mul_add _ _ _)

/-- `toDoubleCentralizer` preserves negation. -/
@[simp]
theorem toDoubleCentralizer_neg (f : X →ᵇ A) :
    (-f).toDoubleCentralizer 𝕜 = -f.toDoubleCentralizer 𝕜 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => neg_mul _ _)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => mul_neg _ _)

/-- `toDoubleCentralizer` preserves subtraction. -/
@[simp]
theorem toDoubleCentralizer_sub (f₁ f₂ : X →ᵇ A) :
    (f₁ - f₂).toDoubleCentralizer 𝕜 =
      f₁.toDoubleCentralizer 𝕜 - f₂.toDoubleCentralizer 𝕜 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => sub_mul _ _ _)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => mul_sub _ _ _)

/-- `toDoubleCentralizer` preserves multiplication. -/
@[simp]
theorem toDoubleCentralizer_mul (f₁ f₂ : X →ᵇ A) :
    (f₁ * f₂).toDoubleCentralizer 𝕜 =
      f₁.toDoubleCentralizer 𝕜 * f₂.toDoubleCentralizer 𝕜 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => mul_assoc _ _ _)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => (mul_assoc _ _ _).symm)

/-- `toDoubleCentralizer` preserves scalar multiplication. -/
@[simp]
theorem toDoubleCentralizer_smul (c : 𝕜) (f : X →ᵇ A) :
    (c • f).toDoubleCentralizer 𝕜 = c • f.toDoubleCentralizer 𝕜 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => smul_mul_assoc _ _ _)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => mul_smul_comm _ _ _)

/-- `toDoubleCentralizer` preserves the star operation. -/
@[simp]
theorem toDoubleCentralizer_star [StarRing 𝕜] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A]
    (f : X →ᵇ A) :
    (star f).toDoubleCentralizer 𝕜 = star (f.toDoubleCentralizer 𝕜) :=
  DoubleCentralizer.ext_fst_snd
    (fun g => ZeroAtInftyContinuousMap.ext fun x => by
      simp [DoubleCentralizer.star_fst, star_mul])
    (fun g => ZeroAtInftyContinuousMap.ext fun x => by
      simp [DoubleCentralizer.star_snd, star_mul])

/-- On functions vanishing at infinity, `toDoubleCentralizer` agrees with the canonical inclusion
`DoubleCentralizer.coe`. -/
@[simp]
theorem toDoubleCentralizer_zeroAtInfty (g : C₀(X, A)) :
    g.toBCF.toDoubleCentralizer 𝕜 = (g : 𝓜(𝕜, C₀(X, A))) :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => rfl)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => rfl)

end NonUnital

section Unital

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- `toDoubleCentralizer` sends `1` to `1`. -/
@[simp]
theorem toDoubleCentralizer_one : (1 : X →ᵇ A).toDoubleCentralizer 𝕜 = 1 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => one_mul _)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => mul_one _)

/-- `toDoubleCentralizer` commutes with `algebraMap`. -/
@[simp]
theorem toDoubleCentralizer_algebraMap (c : 𝕜) :
    (algebraMap 𝕜 (X →ᵇ A) c).toDoubleCentralizer 𝕜 = algebraMap 𝕜 𝓜(𝕜, C₀(X, A)) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, toDoubleCentralizer_smul,
    toDoubleCentralizer_one]

variable (𝕜 X A) in
/-- `BoundedContinuousFunction.toDoubleCentralizer` bundled as a unital algebra homomorphism. -/
def toDoubleCentralizerAlgHom : (X →ᵇ A) →ₐ[𝕜] 𝓜(𝕜, C₀(X, A)) where
  toFun := toDoubleCentralizer 𝕜
  map_one' := toDoubleCentralizer_one
  map_mul' := toDoubleCentralizer_mul
  map_zero' := toDoubleCentralizer_zero
  map_add' := toDoubleCentralizer_add
  commutes' := toDoubleCentralizer_algebraMap

/-- Evaluating `toDoubleCentralizerAlgHom` yields `toDoubleCentralizer`. -/
@[simp]
theorem coe_toDoubleCentralizerAlgHom :
    ⇑(toDoubleCentralizerAlgHom 𝕜 X A) = toDoubleCentralizer 𝕜 :=
  (rfl)

variable [StarRing 𝕜] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A]

variable (𝕜 X A) in
/-- `BoundedContinuousFunction.toDoubleCentralizer` bundled as a unital `⋆`-algebra
homomorphism. -/
def toDoubleCentralizerStarAlgHom : (X →ᵇ A) →⋆ₐ[𝕜] 𝓜(𝕜, C₀(X, A)) where
  __ := toDoubleCentralizerAlgHom 𝕜 X A
  map_star' := toDoubleCentralizer_star

/-- Evaluating `toDoubleCentralizerStarAlgHom` yields `toDoubleCentralizer`. -/
@[simp]
theorem coe_toDoubleCentralizerStarAlgHom :
    ⇑(toDoubleCentralizerStarAlgHom 𝕜 X A) = toDoubleCentralizer 𝕜 :=
  (rfl)

/-- Composing `toDoubleCentralizerStarAlgHom` with
`ZeroAtInftyContinuousMap.toBCFNonUnitalStarAlgHom` recovers `DoubleCentralizer.coeHom`. -/
@[simp]
theorem toDoubleCentralizerStarAlgHom_comp_toBCFNonUnitalStarAlgHom :
    (toDoubleCentralizerStarAlgHom 𝕜 X A).toNonUnitalStarAlgHom.comp
      (ZeroAtInftyContinuousMap.toBCFNonUnitalStarAlgHom 𝕜 X A) =
        DoubleCentralizer.coeHom (𝕜 := 𝕜) := by
  ext g : 1
  simp

end Unital

end ToDoubleCentralizer

end BoundedContinuousFunction

namespace DoubleCentralizer

section ToBCF

variable {𝕜 X A : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X]
  [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [NormedSpace ℝ A]

omit [WeaklyLocallyCompactSpace X] [R1Space X] [NormedSpace ℝ A] in
private theorem snd_apply_eq_of_eq_one (m : 𝓜(𝕜, C₀(X, A))) {e₁ e₂ : C₀(X, A)} {x : X}
    (h₁ : e₁ x = 1) (h₂ : e₂ x = 1) : m.snd e₁ x = m.snd e₂ x := by
  have h12 : m.snd e₁ x = m.fst e₂ x := by
    simpa [h₁, h₂] using congr($(m.central e₁ e₂) x)
  have h22 : m.snd e₂ x = m.fst e₂ x := by
    simpa [h₂] using congr($(m.central e₂ e₂) x)
  exact h12.trans h22.symm

private def toBCFFun (m : 𝓜(𝕜, C₀(X, A))) (x : X) : A :=
  m.snd (ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)).choose x

private theorem toBCFFun_eq_snd (m : 𝓜(𝕜, C₀(X, A))) {e : C₀(X, A)} {x : X} (he : e x = 1) :
    toBCFFun m x = m.snd e x :=
  snd_apply_eq_of_eq_one m
    (ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)).choose_spec.1 he

private theorem toBCFFun_eq_fst (m : 𝓜(𝕜, C₀(X, A))) {e : C₀(X, A)} {x : X} (he : e x = 1) :
    toBCFFun m x = m.fst e x := by
  rw [toBCFFun_eq_snd m he]
  simpa [he] using congr($(m.central e e) x)

private theorem continuous_toBCFFun (m : 𝓜(𝕜, C₀(X, A))) : Continuous (toBCFFun m) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨e, heK, -, -⟩ := ZeroAtInftyContinuousMap.exists_eqOn_const_of_isCompact hK (1 : A)
  refine (m.snd e).continuous.continuousAt.congr ?_
  filter_upwards [hKx] with y hy
  exact (toBCFFun_eq_snd m (heK hy)).symm

private theorem norm_toBCFFun_le (m : 𝓜(𝕜, C₀(X, A))) (x : X) :
    ‖toBCFFun m x‖ ≤ ‖m.snd‖ * ‖(1 : A)‖ := by
  set e := (ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)).choose
  have hnorm : ‖e‖ ≤ ‖(1 : A)‖ :=
    (ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)).choose_spec.2
  calc ‖toBCFFun m x‖ = ‖m.snd e x‖ := rfl
    _ ≤ ‖m.snd e‖ := (m.snd e).toBCF.norm_coe_le_norm x
    _ ≤ ‖m.snd‖ * ‖e‖ := m.snd.le_opNorm e
    _ ≤ ‖m.snd‖ * ‖(1 : A)‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

/-- The bounded continuous function `X →ᵇ A` representing a multiplier `m : 𝓜(𝕜, C₀(X, A))`. -/
def toBCF (m : 𝓜(𝕜, C₀(X, A))) : X →ᵇ A :=
  BoundedContinuousFunction.ofNormedAddCommGroup (toBCFFun m) (continuous_toBCFFun m)
    (‖m.snd‖ * ‖(1 : A)‖) (norm_toBCFFun_le m)

/-- The value of `m.toBCF` at `x` equals `m.snd e x` for any `e : C₀(X, A)` with `e x = 1`. -/
theorem toBCF_apply_eq_snd (m : 𝓜(𝕜, C₀(X, A))) {e : C₀(X, A)} {x : X} (he : e x = 1) :
    m.toBCF x = m.snd e x :=
  toBCFFun_eq_snd m he

/-- The value of `m.toBCF` at `x` equals `m.fst e x` for any `e : C₀(X, A)` with `e x = 1`. -/
theorem toBCF_apply_eq_fst (m : 𝓜(𝕜, C₀(X, A))) {e : C₀(X, A)} {x : X} (he : e x = 1) :
    m.toBCF x = m.fst e x :=
  toBCFFun_eq_fst m he

/-- The left centralizer of `m : 𝓜(𝕜, C₀(X, A))` acts as pointwise left multiplication by
`m.toBCF`. -/
theorem fst_apply_eq_toBCF_mul (m : 𝓜(𝕜, C₀(X, A))) (g : C₀(X, A)) (x : X) :
    m.fst g x = m.toBCF x * g x := by
  obtain ⟨e, he, -⟩ := ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)
  rw [toBCF_apply_eq_snd m he]
  simpa [he] using congr($(m.central e g) x).symm

/-- The right centralizer of `m : 𝓜(𝕜, C₀(X, A))` acts as pointwise right multiplication by
`m.toBCF`. -/
theorem snd_apply_eq_mul_toBCF (m : 𝓜(𝕜, C₀(X, A))) (g : C₀(X, A)) (x : X) :
    m.snd g x = g x * m.toBCF x := by
  obtain ⟨e, he, -⟩ := ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)
  rw [toBCF_apply_eq_fst m he]
  simpa [he] using congr($(m.central g e) x)

/-- Recovering the bounded continuous function from `f.toDoubleCentralizer 𝕜` returns `f`. -/
@[simp]
theorem toBCF_toDoubleCentralizer (f : X →ᵇ A) : (f.toDoubleCentralizer 𝕜).toBCF = f := by
  ext x
  obtain ⟨e, he, -⟩ := ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : A)
  simp [toBCF_apply_eq_snd _ he, he]

/-- Reconstructing a multiplier from `m.toBCF` recovers `m`. -/
@[simp]
theorem toDoubleCentralizer_toBCF (m : 𝓜(𝕜, C₀(X, A))) : m.toBCF.toDoubleCentralizer 𝕜 = m :=
  ext_fst_snd
    (fun g => ZeroAtInftyContinuousMap.ext fun x => (fst_apply_eq_toBCF_mul m g x).symm)
    (fun g => ZeroAtInftyContinuousMap.ext fun x => (snd_apply_eq_mul_toBCF m g x).symm)

/-- `DoubleCentralizer.toBCF` is injective on `𝓜(𝕜, C₀(X, A))`. -/
theorem toBCF_injective : Function.Injective (toBCF (X := X) (𝕜 := 𝕜) (A := A)) :=
  Function.LeftInverse.injective toDoubleCentralizer_toBCF

/-- `BoundedContinuousFunction.toDoubleCentralizer` is injective on `X →ᵇ A`. -/
theorem _root_.BoundedContinuousFunction.toDoubleCentralizer_injective :
    Function.Injective (BoundedContinuousFunction.toDoubleCentralizer 𝕜 (X := X) (A := A)) :=
  Function.LeftInverse.injective toBCF_toDoubleCentralizer

/-- On the canonical image of `C₀(X, A)`, `DoubleCentralizer.toBCF` agrees with
`ZeroAtInftyContinuousMap.toBCF`. -/
@[simp]
theorem toBCF_coe (g : C₀(X, A)) : (g : 𝓜(𝕜, C₀(X, A))).toBCF = g.toBCF := by
  rw [← BoundedContinuousFunction.toDoubleCentralizer_zeroAtInfty (𝕜 := 𝕜) g,
    toBCF_toDoubleCentralizer]

/-- `DoubleCentralizer.toBCF` sends `0` to `0`. -/
@[simp]
theorem toBCF_zero : (0 : 𝓜(𝕜, C₀(X, A))).toBCF = 0 := by
  rw [← BoundedContinuousFunction.toDoubleCentralizer_zero (X := X) (𝕜 := 𝕜) (A := A),
    toBCF_toDoubleCentralizer]

/-- `DoubleCentralizer.toBCF` sends `1` to `1`. -/
@[simp]
theorem toBCF_one : (1 : 𝓜(𝕜, C₀(X, A))).toBCF = 1 := by
  rw [← BoundedContinuousFunction.toDoubleCentralizer_one (X := X) (𝕜 := 𝕜) (A := A),
    toBCF_toDoubleCentralizer]

/-- `DoubleCentralizer.toBCF` preserves addition. -/
@[simp]
theorem toBCF_add (m n : 𝓜(𝕜, C₀(X, A))) : (m + n).toBCF = m.toBCF + n.toBCF := by
  rw [← toBCF_toDoubleCentralizer (𝕜 := 𝕜) (m.toBCF + n.toBCF),
    BoundedContinuousFunction.toDoubleCentralizer_add, toDoubleCentralizer_toBCF,
    toDoubleCentralizer_toBCF]

/-- `DoubleCentralizer.toBCF` preserves negation. -/
@[simp]
theorem toBCF_neg (m : 𝓜(𝕜, C₀(X, A))) : (-m).toBCF = -m.toBCF := by
  rw [← toBCF_toDoubleCentralizer (𝕜 := 𝕜) (-m.toBCF),
    BoundedContinuousFunction.toDoubleCentralizer_neg, toDoubleCentralizer_toBCF]

/-- `DoubleCentralizer.toBCF` preserves subtraction. -/
@[simp]
theorem toBCF_sub (m n : 𝓜(𝕜, C₀(X, A))) : (m - n).toBCF = m.toBCF - n.toBCF := by
  rw [← toBCF_toDoubleCentralizer (𝕜 := 𝕜) (m.toBCF - n.toBCF),
    BoundedContinuousFunction.toDoubleCentralizer_sub, toDoubleCentralizer_toBCF,
    toDoubleCentralizer_toBCF]

/-- `DoubleCentralizer.toBCF` preserves multiplication. -/
@[simp]
theorem toBCF_mul (m n : 𝓜(𝕜, C₀(X, A))) : (m * n).toBCF = m.toBCF * n.toBCF := by
  rw [← toBCF_toDoubleCentralizer (𝕜 := 𝕜) (m.toBCF * n.toBCF),
    BoundedContinuousFunction.toDoubleCentralizer_mul, toDoubleCentralizer_toBCF,
    toDoubleCentralizer_toBCF]

/-- `DoubleCentralizer.toBCF` preserves scalar multiplication. -/
@[simp]
theorem toBCF_smul (c : 𝕜) (m : 𝓜(𝕜, C₀(X, A))) : (c • m).toBCF = c • m.toBCF := by
  rw [← toBCF_toDoubleCentralizer (𝕜 := 𝕜) (c • m.toBCF),
    BoundedContinuousFunction.toDoubleCentralizer_smul, toDoubleCentralizer_toBCF]

/-- `DoubleCentralizer.toBCF` commutes with `algebraMap`. -/
@[simp]
theorem toBCF_algebraMap (c : 𝕜) :
    (algebraMap 𝕜 𝓜(𝕜, C₀(X, A)) c).toBCF = algebraMap 𝕜 (X →ᵇ A) c := by
  rw [← BoundedContinuousFunction.toDoubleCentralizer_algebraMap, toBCF_toDoubleCentralizer]

/-- `DoubleCentralizer.toBCF` preserves the star operation. -/
@[simp]
theorem toBCF_star [StarRing 𝕜] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A]
    (m : 𝓜(𝕜, C₀(X, A))) : (star m).toBCF = star m.toBCF := by
  rw [← toBCF_toDoubleCentralizer (𝕜 := 𝕜) (star m.toBCF),
    BoundedContinuousFunction.toDoubleCentralizer_star, toDoubleCentralizer_toBCF]

/-- The norm of `m.toBCF` is bounded by `‖m‖ * ‖(1 : A)‖`. -/
theorem norm_toBCF_le (m : 𝓜(𝕜, C₀(X, A))) : ‖m.toBCF‖ ≤ ‖m‖ * ‖(1 : A)‖ :=
  (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_toBCFFun_le m)).trans <|
      mul_le_mul_of_nonneg_right (norm_snd_le m) (norm_nonneg _)

/-- The norm of `f : X →ᵇ A` is bounded by `‖f.toDoubleCentralizer 𝕜‖ * ‖(1 : A)‖`. -/
theorem _root_.BoundedContinuousFunction.norm_le_norm_toDoubleCentralizer_mul_norm_one
    (f : X →ᵇ A) : ‖f‖ ≤ ‖f.toDoubleCentralizer 𝕜‖ * ‖(1 : A)‖ := by
  simpa using norm_toBCF_le (f.toDoubleCentralizer 𝕜)

/-- When `‖(1 : A)‖ = 1`, `DoubleCentralizer.toBCF` preserves the norm. -/
@[simp]
theorem norm_toBCF [NormOneClass A] (m : 𝓜(𝕜, C₀(X, A))) : ‖m.toBCF‖ = ‖m‖ := by
  refine le_antisymm ?_ ?_
  · simpa using norm_toBCF_le m
  · simpa using BoundedContinuousFunction.norm_toDoubleCentralizer_le (𝕜 := 𝕜) m.toBCF

/-- When `‖(1 : A)‖ = 1`, `BoundedContinuousFunction.toDoubleCentralizer` preserves the norm. -/
@[simp]
theorem _root_.BoundedContinuousFunction.norm_toDoubleCentralizer [NormOneClass A] (f : X →ᵇ A) :
    ‖f.toDoubleCentralizer 𝕜‖ = ‖f‖ := by
  rw [← norm_toBCF, toBCF_toDoubleCentralizer]

/-- When `‖(1 : A)‖ = 1`, `DoubleCentralizer.toBCF` is an isometry. -/
theorem isometry_toBCF [NormOneClass A] :
    Isometry (toBCF (X := X) (𝕜 := 𝕜) (A := A)) :=
  AddMonoidHomClass.isometry_of_norm
    ({ toFun := toBCF, map_zero' := toBCF_zero, map_add' := toBCF_add } :
      𝓜(𝕜, C₀(X, A)) →+ (X →ᵇ A)) norm_toBCF

/-- When `‖(1 : A)‖ = 1`, `BoundedContinuousFunction.toDoubleCentralizer` is an isometry. -/
theorem _root_.BoundedContinuousFunction.isometry_toDoubleCentralizer [NormOneClass A] :
    Isometry (BoundedContinuousFunction.toDoubleCentralizer 𝕜 (X := X) (A := A)) :=
  AddMonoidHomClass.isometry_of_norm
    (BoundedContinuousFunction.toDoubleCentralizerAlgHom 𝕜 X A)
    BoundedContinuousFunction.norm_toDoubleCentralizer

/-- A multiplier `m : 𝓜(𝕜, C₀(X, A))` lies in the canonical image of `C₀(X, A)` if and only if
`m.toBCF` vanishes at infinity. -/
theorem mem_range_coe_iff_tendsto_cocompact_nhds_zero (m : 𝓜(𝕜, C₀(X, A))) :
    m ∈ Set.range (DoubleCentralizer.coe 𝕜 : C₀(X, A) → 𝓜(𝕜, C₀(X, A))) ↔
      Tendsto m.toBCF (cocompact X) (𝓝 0) := by
  refine ⟨?_, fun hm => ?_⟩
  · rintro ⟨g, rfl⟩
    rw [toBCF_coe]
    exact zero_at_infty g
  · refine ⟨{ toFun := m.toBCF, continuous_toFun := m.toBCF.continuous, zero_at_infty' := hm }, ?_⟩
    apply toBCF_injective
    ext x
    simp

variable (𝕜 X A) in
/-- The canonical algebra equivalence `𝓜(𝕜, C₀(X, A)) ≃ₐ[𝕜] (X →ᵇ A)` for a weakly locally
compact `R₁` space `X`. -/
def toBCFAlgEquiv : 𝓜(𝕜, C₀(X, A)) ≃ₐ[𝕜] (X →ᵇ A) where
  toFun := toBCF
  invFun := BoundedContinuousFunction.toDoubleCentralizer 𝕜
  left_inv := toDoubleCentralizer_toBCF
  right_inv := toBCF_toDoubleCentralizer
  map_mul' := toBCF_mul
  map_add' := toBCF_add
  commutes' := toBCF_algebraMap

/-- Evaluating `toBCFAlgEquiv` yields `DoubleCentralizer.toBCF`. -/
@[simp]
theorem coe_toBCFAlgEquiv : ⇑(toBCFAlgEquiv 𝕜 X A) = toBCF :=
  (rfl)

/-- Evaluating `(toBCFAlgEquiv).symm` yields `BoundedContinuousFunction.toDoubleCentralizer`. -/
@[simp]
theorem coe_toBCFAlgEquiv_symm :
    ⇑(toBCFAlgEquiv 𝕜 X A).symm = BoundedContinuousFunction.toDoubleCentralizer 𝕜 :=
  (rfl)

variable (𝕜 X A) in
/-- The canonical `⋆`-algebra equivalence `𝓜(𝕜, C₀(X, A)) ≃⋆ₐ[𝕜] (X →ᵇ A)` for a weakly locally
compact `R₁` space `X`. -/
def toBCFStarAlgEquiv [StarRing 𝕜] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A] :
    𝓜(𝕜, C₀(X, A)) ≃⋆ₐ[𝕜] (X →ᵇ A) where
  __ := (toBCFAlgEquiv 𝕜 X A).toRingEquiv
  map_smul' := toBCF_smul
  map_star' := toBCF_star

/-- Evaluating `toBCFStarAlgEquiv` yields `DoubleCentralizer.toBCF`. -/
@[simp]
theorem coe_toBCFStarAlgEquiv [StarRing 𝕜] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A] :
    ⇑(toBCFStarAlgEquiv 𝕜 X A) = toBCF :=
  (rfl)

/-- Evaluating `(toBCFStarAlgEquiv).symm` yields `BoundedContinuousFunction.toDoubleCentralizer`. -/
@[simp]
theorem coe_toBCFStarAlgEquiv_symm [StarRing 𝕜] [StarRing A] [NormedStarGroup A]
    [StarModule 𝕜 A] :
    ⇑(toBCFStarAlgEquiv 𝕜 X A).symm = BoundedContinuousFunction.toDoubleCentralizer 𝕜 :=
  (rfl)

/-- The inverse of `toBCFStarAlgEquiv`, coerced to a `⋆`-algebra homomorphism, is
`BoundedContinuousFunction.toDoubleCentralizerStarAlgHom`. -/
@[simp]
theorem toBCFStarAlgEquiv_symm_toStarAlgHom [StarRing 𝕜] [StarRing A] [NormedStarGroup A]
    [StarModule 𝕜 A] :
    (toBCFStarAlgEquiv 𝕜 X A).symm.toStarAlgHom =
      BoundedContinuousFunction.toDoubleCentralizerStarAlgHom 𝕜 X A :=
  (rfl)

variable (𝕜 X A) in
/-- The canonical linear isometry equivalence `𝓜(𝕜, C₀(X, A)) ≃ₗᵢ[𝕜] (X →ᵇ A)` when
`‖(1 : A)‖ = 1`. -/
def toBCFLinearIsometryEquiv [NormOneClass A] : 𝓜(𝕜, C₀(X, A)) ≃ₗᵢ[𝕜] (X →ᵇ A) where
  __ := (toBCFAlgEquiv 𝕜 X A).toLinearEquiv
  norm_map' := norm_toBCF

/-- Evaluating `toBCFLinearIsometryEquiv` yields `DoubleCentralizer.toBCF`. -/
@[simp]
theorem coe_toBCFLinearIsometryEquiv [NormOneClass A] :
    ⇑(toBCFLinearIsometryEquiv 𝕜 X A) = toBCF :=
  (rfl)

/-- Evaluating `(toBCFLinearIsometryEquiv).symm` yields
`BoundedContinuousFunction.toDoubleCentralizer`. -/
@[simp]
theorem coe_toBCFLinearIsometryEquiv_symm [NormOneClass A] :
    ⇑(toBCFLinearIsometryEquiv 𝕜 X A).symm = BoundedContinuousFunction.toDoubleCentralizer 𝕜 :=
  (rfl)

end ToBCF

end DoubleCentralizer
