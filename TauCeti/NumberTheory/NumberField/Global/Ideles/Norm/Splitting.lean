/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup

/-!
# The norm quotient of the idele class group

The idele class norm `‖·‖ : C_K → ℝ>0` of a number field `K` has a continuous homomorphic
section. Fix an infinite place `w` of `K`, with multiplicity `m_w ∈ {1, 2}`. The idele whose
`w`-coordinate is the positive real number `t ^ (1 / m_w)` and whose other coordinates are `1` has
idele norm `t`, because the normalized absolute value at `w` is `|·| ^ m_w`.

A continuous map with a continuous right inverse is a quotient map, and a quotient homomorphism of
topological groups is open. So the idele norm and the idele class norm are open quotient maps,
and the topological first isomorphism theorem identifies the **norm quotient**
`C_K / C_K¹` with `ℝ>0` as a topological group. In particular the full idele class group is not
compact, in contrast to the norm-one idele class group `C_K¹`. The section also splits the
idele class group as a topological group: `C_K ≃ C_K¹ × ℝ>0`.

## Main definitions

* `TauCeti.GlobalNumberFields.completionNormSection`: the positive real number `t ^ (1 / m_w)`
  as a unit of the completion `K_w`.
* `TauCeti.GlobalNumberFields.ideleNormSection` and
  `TauCeti.GlobalNumberFields.ideleClassNormSection`: the resulting continuous sections of the
  idele norm and of the idele class norm.
* `NumberField.IdeleClassGroup.quotientNormOneEquiv`: the isomorphism of
  topological groups `C_K / C_K¹ ≃ₜ* ℝ>0` induced by the idele class norm.
* `NumberField.IdeleClassGroup.normOneProdEquiv`: the splitting
  `C_K ≃ₜ* C_K¹ × ℝ>0` determined by an infinite place.

## Main results

* `TauCeti.GlobalNumberFields.ideleNorm_ideleNormSection` and
  `TauCeti.GlobalNumberFields.ideleClassNorm_ideleClassNormSection`: the sections are right
  inverse to the norms.
* `TauCeti.GlobalNumberFields.isOpenQuotientMap_ideleNorm` and
  `TauCeti.GlobalNumberFields.isOpenQuotientMap_ideleClassNorm`: the norms are open quotient maps.
* `NumberField.IdeleClassGroup.quotientNormOneEquiv_mk`: the norm quotient
  isomorphism is induced by the idele class norm.
* `NumberField.IdeleClassGroup.not_compactSpace`: the idele class group is not
  compact.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K]

/-! ### The section at one infinite place -/

/-- The positive real number `t ^ (1 / m_w)` as a unit of the completion at the infinite place
`w`, where `m_w` is the multiplicity of `w`. Its normalized absolute value is `t`
(`completionNormalizedAbsValue_completionNormSection`). -/
def completionNormSection (w : InfinitePlace K) : ℝ≥0ˣ →ₜ* w.Completionˣ where
  toMonoidHom := Units.map <|
    ((Completion.ofReal w).toMonoidHom.comp NNReal.toRealHom.toMonoidHom).comp
      (NNReal.rpowMonoidHom (w.mult : ℝ)⁻¹)
  continuous_toFun := Continuous.units_map _ <|
    (Completion.continuous_ofReal w).comp <| NNReal.continuous_coe.comp <|
      NNReal.continuous_rpow_const (by positivity)

/-- The underlying element of `completionNormSection w t` is the real number `t ^ (1 / m_w)`. -/
@[simp]
theorem coe_completionNormSection (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    (completionNormSection w t : w.Completion) =
      Completion.ofReal w ((t : ℝ≥0) ^ (w.mult : ℝ)⁻¹ : ℝ≥0) :=
  (rfl)

/-- The normalized absolute value of `completionNormSection w t` is `t`. -/
theorem completionNormalizedAbsValue_completionNormSection (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    completionNormalizedAbsValue w (completionNormSection w t) = (t : ℝ≥0) := by
  rw [coe_completionNormSection, completionNormalizedAbsValue_ofReal, NNReal.abs_eq,
    ← NNReal.coe_pow, NNReal.rpow_inv_natCast_pow _ w.mult_ne_zero]

variable [NumberField K]

variable (K) in
/-- The continuous section of the idele norm at the infinite place `w`: the idele whose
`w`-coordinate is the positive real number `t ^ (1 / m_w)` and whose other coordinates are `1`. -/
def ideleNormSection (w : InfinitePlace K) : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 K) K where
  toMonoidHom := (IdeleGroup.ofCompletion (𝓞 K) K w).comp (completionNormSection w)
  continuous_toFun :=
    (IdeleGroup.continuous_ofCompletion (𝓞 K) K w).comp (completionNormSection w).continuous

/-- The section of the idele norm at `w` is concentrated at `w`, with coordinate
`completionNormSection w t`. -/
theorem ideleNormSection_apply (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    ideleNormSection K w t = IdeleGroup.ofCompletion (𝓞 K) K w (completionNormSection w t) :=
  (rfl)

/-- **The section is right inverse to the idele norm.** -/
@[simp]
theorem ideleNorm_ideleNormSection (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    ideleNorm (ideleNormSection K w t) = t :=
  Units.ext <| NNReal.eq <| by
    rw [ideleNormSection_apply, coe_ideleNorm_ofCompletion,
      completionNormalizedAbsValue_completionNormSection]

variable (K) in
/-- The continuous section of the idele class norm at the infinite place `w`: the class of
`ideleNormSection K w t`. -/
def ideleClassNormSection (w : InfinitePlace K) : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K where
  toMonoidHom := (QuotientGroup.mk' _).comp (ideleNormSection K w).toMonoidHom
  continuous_toFun := continuous_quot_mk.comp (ideleNormSection K w).continuous

/-- The section of the idele class norm at `w` is the class of the section of the idele norm. -/
theorem ideleClassNormSection_apply (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    ideleClassNormSection K w t = (ideleNormSection K w t : IdeleClassGroup (𝓞 K) K) :=
  (rfl)

/-- **The section is right inverse to the idele class norm.** -/
@[simp]
theorem ideleClassNorm_ideleClassNormSection (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    ideleClassNorm (ideleClassNormSection K w t) = t := by
  rw [ideleClassNormSection_apply, ideleClassNorm_mk, ideleNorm_ideleNormSection]

/-! ### The norms are open quotient maps -/

/-- The idele norm is an open quotient map onto `ℝ>0`: it has a continuous section. -/
theorem isOpenQuotientMap_ideleNorm : IsOpenQuotientMap (ideleNorm (K := K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact MonoidHom.isOpenQuotientMap_of_isQuotientMap <|
    .of_inverse (ideleNormSection K w).continuous continuous_ideleNorm
      (ideleNorm_ideleNormSection w)

/-- The idele class norm is an open quotient map onto `ℝ>0`: it has a continuous section. -/
theorem isOpenQuotientMap_ideleClassNorm : IsOpenQuotientMap (ideleClassNorm (K := K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact MonoidHom.isOpenQuotientMap_of_isQuotientMap <|
    .of_inverse (ideleClassNormSection K w).continuous continuous_ideleClassNorm
      (ideleClassNorm_ideleClassNormSection w)

end TauCeti.GlobalNumberFields

namespace NumberField.IdeleClassGroup

open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### The norm quotient -/

variable (K) in
/-- **The norm quotient of the idele class group is `ℝ>0`**: the idele class norm induces an
isomorphism of topological groups `C_K / C_K¹ ≃ₜ* ℝ>0`. -/
def quotientNormOneEquiv : IdeleClassGroup (𝓞 K) K ⧸ normOne K ≃ₜ* ℝ≥0ˣ :=
  -- `normOne K` is the kernel of the idele class norm, but not by unfolding outside its module.
  ((ContinuousMulEquiv.refl _).quotientCongr (normOne K) (ideleClassNorm (K := K)).ker <|
    Subgroup.ext fun _ ↦ by simp).trans <|
  ContinuousMulEquiv.quotientKerEquivOfSurjective (ideleClassNorm (K := K))
    ((isOpenQuotientMap_ideleClassNorm (K := K)).isOpenMap.isStrictMap
      (continuous_ideleClassNorm (K := K)))
    ideleClassNorm_surjective

/-- The norm quotient isomorphism sends the class of an idele class to its idele class norm. -/
@[simp]
theorem quotientNormOneEquiv_mk (c : IdeleClassGroup (𝓞 K) K) :
    quotientNormOneEquiv K (c : IdeleClassGroup (𝓞 K) K ⧸ normOne K) = ideleClassNorm c := by
  rw [quotientNormOneEquiv, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.quotientCongr_mk,
    ContinuousMulEquiv.quotientKerEquivOfSurjective_apply_mk, ContinuousMulEquiv.refl_apply]

/-- **The idele class group of a number field is not compact**: it surjects continuously onto
the noncompact group `ℝ>0`. This is in contrast to the norm-one subgroup `C_K¹`, which is
compact. -/
theorem not_compactSpace : ¬ CompactSpace (IdeleClassGroup (𝓞 K) K) := fun _ ↦ by
  obtain ⟨M, hM⟩ := (isCompact_range <| Units.continuous_val.comp
    (continuous_ideleClassNorm (K := K))).bddAbove
  obtain ⟨c, hc⟩ := ideleClassNorm_surjective (K := K)
    (Units.mk0 (M + 1) (by positivity))
  have h := hM ⟨c, rfl⟩
  simp only [Function.comp_apply, hc, Units.val_mk0] at h
  exact (lt_add_one M).not_ge h

/-! ### The splitting `C_K ≃ C_K¹ × ℝ>0` -/

/-- The norm-one part `c · s(‖c‖)⁻¹` of an idele class `c`, for the section `s` at `w`. -/
private theorem mul_inv_ideleClassNormSection_mem_normOne (w : InfinitePlace K)
    (c : IdeleClassGroup (𝓞 K) K) :
    c * (ideleClassNormSection K w (ideleClassNorm c))⁻¹ ∈ normOne K := by
  rw [mem_normOne_iff, map_mul, map_inv, ideleClassNorm_ideleClassNormSection, mul_inv_cancel]

/-- **The idele class group splits as `C_K¹ × ℝ>0`.** The infinite place `w` determines the
isomorphism of topological groups sending an idele class `c` to its norm-one part
`c · s(‖c‖)⁻¹` and its norm `‖c‖`, where `s = ideleClassNormSection K w`. -/
def normOneProdEquiv (w : InfinitePlace K) :
    IdeleClassGroup (𝓞 K) K ≃ₜ* normOne K × ℝ≥0ˣ where
  toFun c := (⟨_, mul_inv_ideleClassNormSection_mem_normOne w c⟩, ideleClassNorm c)
  invFun p := p.1 * ideleClassNormSection K w p.2
  left_inv c := by simp
  right_inv p := by
    have hp := mem_normOne_iff.mp p.1.2
    ext
    · simp [hp]
    · simp [hp]
  map_mul' c d := by
    ext
    · simp only [Prod.fst_mul, Subgroup.coe_mul, map_mul]
      -- Term mode: `rw` does not match the commutative-group lemmas against the quotient group
      -- multiplication of `IdeleClassGroup` up to instances.
      exact (congrArg (c * d * ·) (mul_inv _ _)).trans (mul_mul_mul_comm c d _ _)
    · simp
  continuous_toFun :=
    ((continuous_id.mul ((ideleClassNormSection K w).continuous.comp
      continuous_ideleClassNorm).inv).subtype_mk _).prodMk continuous_ideleClassNorm
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((ideleClassNormSection K w).continuous.comp continuous_snd)

/-- The norm-one component of the splitting at `w` is `c · s(‖c‖)⁻¹`. -/
@[simp]
theorem coe_normOneProdEquiv_fst (w : InfinitePlace K) (c : IdeleClassGroup (𝓞 K) K) :
    ((normOneProdEquiv w c).1 : IdeleClassGroup (𝓞 K) K) =
      c * (ideleClassNormSection K w (ideleClassNorm c))⁻¹ :=
  (rfl)

/-- The `ℝ>0` component of the splitting is the idele class norm. -/
@[simp]
theorem normOneProdEquiv_snd (w : InfinitePlace K) (c : IdeleClassGroup (𝓞 K) K) :
    (normOneProdEquiv w c).2 = ideleClassNorm c :=
  (rfl)

/-- The inverse of the splitting multiplies a norm-one idele class by the section at `w`. -/
@[simp]
theorem normOneProdEquiv_symm_apply (w : InfinitePlace K) (p : normOne K × ℝ≥0ˣ) :
    (normOneProdEquiv w).symm p = p.1 * ideleClassNormSection K w p.2 :=
  (rfl)

end NumberField.IdeleClassGroup
