/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic
public import TauCeti.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Basic

import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rademacher type and cotype

A seminormed group `E` has *(Rademacher) type `p` with constant `C`* if every finite family
`y` in `E` satisfies `R₂(y) ≤ C ‖y‖ₚ`, and *cotype `q` with constant `C`* if
`‖y‖_q ≤ C R₂(y)`, where `R₂(y) = (𝔼_ε ‖∑ i, εᵢ yᵢ‖²)^(1/2)` is the Rademacher second moment.
The `ℓᵖ` norms of the family are written as norms of `WithLp.toLp p y`: for `0 < p < ∞` this is
`(∑ i, ‖yᵢ‖ ^ p) ^ (1 / p)`, for `p = ∞` it is the maximum of the norms, and for `p = 0` it is
the number of members of nonzero norm. Type and cotype measure how far
the average of the signed sums of a family may stray from that of an orthogonal family: since
distinct signs are orthogonal on average, inner product spaces have type `2` and cotype `2` with
constant `1`. The
interesting range is `1 ≤ p ≤ 2` and `2 ≤ q ≤ ∞`: every seminormed group has type `1` and every
real normed space has cotype `∞`, with constant `1`, while no nonzero real normed space has type
`p > 2` or cotype `q < 2`, whatever the constant.

Both notions pass to the domain of an additive map `f : E → F` with `‖x‖ ≤ K ‖f x‖` and
`‖f x‖ ≤ M ‖x‖`, the constant being multiplied by `K M`. In particular they pass with the same
constant along linear isometries, hence to subspaces, and along a bounded linear equivalence
`U` with the constant multiplied by `‖U‖ ‖U⁻¹‖`.

## Main declarations

* `TauCeti.HasType`, `TauCeti.HasCotype`: Rademacher type `p` and cotype `q` with constant `C`.
* `TauCeti.HasType.rademacherSecondMoment_le`, `TauCeti.HasCotype.norm_toLp_le`: the defining
  inequalities for families indexed by any finite type.
* `TauCeti.HasType.of_map`, `TauCeti.HasCotype.of_map`: transport along bounded additive maps
  with a lower bound; `of_linearIsometry` and `of_continuousLinearEquiv` specialise them.
* `TauCeti.hasType_one`, `TauCeti.hasCotype_top`: the trivial type and cotype.
* `TauCeti.hasType_two_of_innerProductSpace`, `TauCeti.hasCotype_two_of_innerProductSpace`:
  inner product spaces have type and cotype `2` with constant `1`.
* `TauCeti.HasType.le_two`, `TauCeti.HasCotype.two_le`: a nonzero real normed space has no type
  `p > 2` and no cotype `q < 2`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012), §9.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §6.2.
-/

public section

noncomputable section

open Filter Finset
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

variable (E) in
/-- `E` has *Rademacher type `p` with constant `C`* if every finite family `y` in `E` satisfies
`R₂(y) ≤ C ‖y‖ₚ`, where `‖y‖ₚ = ‖WithLp.toLp p y‖` is the `ℓᵖ` norm of the family:
`(∑ i, ‖yᵢ‖ ^ p) ^ (1 / p)` for `0 < p < ∞`, the largest `‖yᵢ‖` for `p = ∞`, and the number of
`yᵢ` of nonzero norm for `p = 0`. -/
def HasType (p : ℝ≥0∞) (C : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (y : Fin n → E), rademacherSecondMoment y ≤ C * ‖WithLp.toLp p y‖

variable (E) in
/-- `E` has *Rademacher cotype `q` with constant `C`* if every finite family `y` in `E` satisfies
`‖y‖_q ≤ C R₂(y)`, where `‖y‖_q = ‖WithLp.toLp q y‖` is the `ℓ^q` norm of the family:
`(∑ i, ‖yᵢ‖ ^ q) ^ (1 / q)` for `0 < q < ∞`, the largest `‖yᵢ‖` for `q = ∞`, and the number of
`yᵢ` of nonzero norm for `q = 0`. -/
def HasCotype (q : ℝ≥0∞) (C : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (y : Fin n → E), ‖WithLp.toLp q y‖ ≤ C * rademacherSecondMoment y

variable {p q : ℝ≥0∞} {C C' : ℝ≥0}

/-- The defining inequality of type `p` with constant `C`, for families indexed by `Fin n`. -/
theorem hasType_iff :
    HasType E p C ↔ ∀ (n : ℕ) (y : Fin n → E), rademacherSecondMoment y ≤ C * ‖WithLp.toLp p y‖ :=
  Iff.rfl

/-- The defining inequality of cotype `q` with constant `C`, for families indexed by `Fin n`. -/
theorem hasCotype_iff :
    HasCotype E q C ↔
      ∀ (n : ℕ) (y : Fin n → E), ‖WithLp.toLp q y‖ ≤ C * rademacherSecondMoment y :=
  Iff.rfl

/-- A type constant may be enlarged. -/
theorem HasType.mono_const (h : HasType E p C) (hC : C ≤ C') : HasType E p C' := fun n y ↦
  (h n y).trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hC) (PiLp.norm_nonneg' _))

/-- A cotype constant may be enlarged. -/
theorem HasCotype.mono_const (h : HasCotype E q C) (hC : C ≤ C') : HasCotype E q C' :=
  fun n y ↦ (h n y).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hC) (rademacherSecondMoment_nonneg _))

section Fintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The type inequality holds for families indexed by any finite type. -/
theorem HasType.rademacherSecondMoment_le (h : HasType E p C) (y : ι → E) :
    rademacherSecondMoment y ≤ C * ‖WithLp.toLp p y‖ := by
  let e := Fintype.equivFin ι
  have hy := h _ (y ∘ e.symm)
  rwa [rademacherSecondMoment_comp_equiv, PiLp.norm_toLp_comp_equiv] at hy

/-- The cotype inequality holds for families indexed by any finite type. -/
theorem HasCotype.norm_toLp_le (h : HasCotype E q C) (y : ι → E) :
    ‖WithLp.toLp q y‖ ≤ C * rademacherSecondMoment y := by
  let e := Fintype.equivFin ι
  have hy := h _ (y ∘ e.symm)
  rwa [rademacherSecondMoment_comp_equiv, PiLp.norm_toLp_comp_equiv] at hy

end Fintype

/-! ### Transport -/

section Transport

variable {𝓕 : Type*} [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] {K M : ℝ≥0}

/-- Type passes to the domain of an additive map `f` with `‖x‖ ≤ K ‖f x‖` and
`‖f x‖ ≤ M ‖x‖`, the constant being multiplied by `K M`. -/
theorem HasType.of_map [Fact (1 ≤ p)] (h : HasType F p C) (f : 𝓕) (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : HasType E p (K * C * M) := fun n y ↦ calc
  rademacherSecondMoment y ≤ K * rademacherSecondMoment (fun i ↦ f (y i)) :=
    rademacherSecondMoment_le_mul_map f K.2 hK y
  _ ≤ K * (C * (M * ‖WithLp.toLp p y‖)) := by
    gcongr
    exact (h n _).trans (by gcongr; exact PiLp.norm_toLp_comp_le M.2 hM y)
  _ = (K * C * M : ℝ≥0) * ‖WithLp.toLp p y‖ := by push_cast; ring

/-- Cotype passes to the domain of an additive map `f` with `‖x‖ ≤ K ‖f x‖` and
`‖f x‖ ≤ M ‖x‖`, the constant being multiplied by `K M`. -/
theorem HasCotype.of_map [Fact (1 ≤ q)] (h : HasCotype F q C) (f : 𝓕)
    (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : HasCotype E q (K * C * M) :=
  fun n y ↦ calc
  ‖WithLp.toLp q y‖ ≤ K * ‖WithLp.toLp q (fun i ↦ f (y i))‖ := by
    calc ‖WithLp.toLp q y‖ ≤ ‖(K : ℝ) • WithLp.toLp q (fun i ↦ ‖f (y i)‖)‖ :=
          PiLp.norm_mono fun i ↦ by simpa [abs_of_nonneg K.2] using hK (y i)
      _ = K * ‖WithLp.toLp q (fun i ↦ f (y i))‖ := by
          rw [norm_smul, Real.norm_eq_abs, NNReal.abs_eq,
            PiLp.norm_norm (WithLp.toLp q fun i ↦ f (y i))]
  _ ≤ K * (C * (M * rademacherSecondMoment y)) := by
    gcongr
    exact (h n _).trans (by gcongr; exact rademacherSecondMoment_map_le f M.2 hM y)
  _ = (K * C * M : ℝ≥0) * rademacherSecondMoment y := by push_cast; ring

/-- Type passes along linear isometries with the same constant; in particular it passes to
subspaces, through `Submodule.subtypeₗᵢ`. -/
theorem HasType.of_linearIsometry {R : Type*} [Semiring R] [Module R E] [Module R F]
    (h : HasType F p C) (f : E →ₗᵢ[R] F) : HasType E p C := fun n y ↦ by
  have hR := rademacherSecondMoment_le_mul_map f zero_le_one (fun x ↦ by simp) y
  have hy : ‖WithLp.toLp p fun i ↦ f (y i)‖ = ‖WithLp.toLp p y‖ :=
    le_antisymm (PiLp.norm_mono fun i ↦ by simp) (PiLp.norm_mono fun i ↦ by simp)
  rw [one_mul] at hR
  rw [← hy]
  exact hR.trans (h n _)

/-- Cotype passes along linear isometries with the same constant; in particular it passes to
subspaces, through `Submodule.subtypeₗᵢ`. -/
theorem HasCotype.of_linearIsometry {R : Type*} [Semiring R] [Module R E] [Module R F]
    (h : HasCotype F q C) (f : E →ₗᵢ[R] F) : HasCotype E q C := fun n y ↦ by
  have hR := rademacherSecondMoment_map_le f zero_le_one (fun x ↦ by simp) y
  have hy : ‖WithLp.toLp q fun i ↦ f (y i)‖ = ‖WithLp.toLp q y‖ :=
    le_antisymm (PiLp.norm_mono fun i ↦ by simp) (PiLp.norm_mono fun i ↦ by simp)
  rw [one_mul] at hR
  rw [← hy]
  exact (h n _).trans (by gcongr)

section ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Type passes along a bounded linear equivalence `U`, the constant being multiplied by
`‖U⁻¹‖ ‖U‖`. -/
theorem HasType.of_continuousLinearEquiv [Fact (1 ≤ p)] (h : HasType F p C) (U : E ≃L[𝕜] F) :
    HasType E p (‖(U.symm : F →L[𝕜] E)‖₊ * C * ‖(U : E →L[𝕜] F)‖₊) :=
  h.of_map U (fun x ↦ by simpa using (U.symm : F →L[𝕜] E).le_opNorm (U x))
    fun x ↦ (U : E →L[𝕜] F).le_opNorm x

/-- Cotype passes along a bounded linear equivalence `U`, the constant being multiplied by
`‖U⁻¹‖ ‖U‖`. -/
theorem HasCotype.of_continuousLinearEquiv [Fact (1 ≤ q)] (h : HasCotype F q C)
    (U : E ≃L[𝕜] F) : HasCotype E q (‖(U.symm : F →L[𝕜] E)‖₊ * C * ‖(U : E →L[𝕜] F)‖₊) :=
  h.of_map U (fun x ↦ by simpa using (U.symm : F →L[𝕜] E).le_opNorm (U x))
    fun x ↦ (U : E →L[𝕜] F).le_opNorm x

end ContinuousLinearEquiv

end Transport

/-! ### Examples -/

variable (E) in
/-- Every seminormed group has type `1` with constant `1`. -/
theorem hasType_one : HasType E 1 1 := fun n y ↦ by
  simpa [PiLp.norm_eq_of_L1] using rademacherSecondMoment_le_sum_norm y

variable (E) in
/-- Every real normed space has cotype `∞` with constant `1`. -/
theorem hasCotype_top [NormedSpace ℝ E] : HasCotype E ∞ 1 := fun n y ↦ by
  rw [PiLp.norm_eq_ciSup, NNReal.coe_one, one_mul]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp
  exact ciSup_le fun i ↦ norm_le_rademacherSecondMoment y i

section InnerProductSpace

variable (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

include 𝕜 in
/-- An inner product space has type `2` with constant `1`. -/
theorem hasType_two_of_innerProductSpace : HasType H 2 1 := fun n y ↦ by
  rw [rademacherSecondMoment_eq_norm_toLp_two 𝕜, NNReal.coe_one, one_mul]

include 𝕜 in
/-- An inner product space has cotype `2` with constant `1`. -/
theorem hasCotype_two_of_innerProductSpace : HasCotype H 2 1 := fun n y ↦ by
  rw [rademacherSecondMoment_eq_norm_toLp_two 𝕜, NNReal.coe_one, one_mul]

end InnerProductSpace

/-! ### Bounds on the exponents -/

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A nonzero real normed space has no Rademacher type `p > 2`: the family of `n` copies of a
nonzero vector has `R₂ = √n ‖y‖` but `ℓᵖ` norm `n ^ (1 / p) ‖y‖`. -/
theorem HasType.le_two {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Nontrivial G]
    (h : HasType G p C) : p ≤ 2 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : G)
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have key : (1 / 2 : ℝ) ≤ (p⁻¹).toReal := le_of_forall_rpow_le_mul_rpow (C := C) fun n ↦ by
    have := h (n + 1) (Function.const _ y)
    rw [PiLp.norm_toLp_const', ← Function.const_def, rademacherSecondMoment_const,
      ← mul_assoc] at this
    simpa [Real.sqrt_eq_rpow] using le_of_mul_le_mul_right this hy'
  have hp : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (zero_lt_one.trans_le Fact.out).ne'
  rw [← ENNReal.inv_le_inv, ← ENNReal.ofReal_toReal hp]
  calc (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (p⁻¹).toReal := ENNReal.ofReal_le_ofReal key

/-- A nonzero real normed space has no Rademacher cotype `q < 2`: the family of `n` copies of a
nonzero vector has `ℓ^q` norm `n ^ (1 / q) ‖y‖` but `R₂ = √n ‖y‖`. -/
theorem HasCotype.two_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Nontrivial G]
    (h : HasCotype G q C) : 2 ≤ q := by
  obtain ⟨y, hy⟩ := exists_ne (0 : G)
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have key : (q⁻¹).toReal ≤ 1 / 2 := le_of_forall_rpow_le_mul_rpow (C := C) fun n ↦ by
    have := h (n + 1) (Function.const _ y)
    rw [PiLp.norm_toLp_const', ← Function.const_def, rademacherSecondMoment_const,
      ← mul_assoc] at this
    simpa [Real.sqrt_eq_rpow] using le_of_mul_le_mul_right this hy'
  have hq : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (zero_lt_one.trans_le Fact.out).ne'
  rw [← ENNReal.inv_le_inv, ← ENNReal.ofReal_toReal hq]
  calc ENNReal.ofReal (q⁻¹).toReal ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal key
    _ = (2 : ℝ≥0∞)⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

end TauCeti
