/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.ModularForm
import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The depletion of a modular form

For `d ≥ 1`, the **`d`-depletion** of a modular form `f` for `Γ₁(N)` is `f - V_d U_d f`, where
`U_d` is the upper-triangular Hecke operator `∑_{b < d} f ∣ [1, b; 0, d]`, which extracts the
coefficients `a_{d m}`, and `V_d` is the level-raising operator `τ ↦ d τ`, which substitutes
`q ↦ q ^ d`. On `q`-expansions it deletes the terms whose index is divisible by `d`:

`aₙ(f - V_d U_d f) = 0` if `d ∣ n`, and `aₙ(f)` otherwise.

`U_d` acts at a level divisible by `d`, and `V_d` multiplies the level by `d`. Here `f` is read at
the level `L / d`, which `N` and `d` divide, then raised by `V_d` to `L`; so the depletion is a
modular form for `Γ₁(L)` whenever `N * d ∣ L` and `d * d ∣ L`. For instance the `2`-depletion of
`Δ` has level `Γ₁(4)`. Depletions at different levels are compared as functions on `ℍ`.

## Main definitions

* `ModularForm.depletion`, `CuspForm.depletion`: the `d`-depletion `f - V_d U_d f`, from level
  `Γ₁(N)` to level `Γ₁(L)` for `N * d ∣ L` and `d * d ∣ L`.
* `ModularForm.depletionₗ`, `CuspForm.depletionₗ`: the depletion as a `ℂ`-linear map.

## Main results

* `ModularForm.depletion_apply`: `(f - V_d U_d f)(τ) = f(τ) - (U_d f)(d τ)`.
* `CuspForm.coe_depletion`, `ModularForm.depletion_coe_cuspForm`: depletion commutes with the
  inclusion of cusp forms into modular forms.
* `ModularForm.qExpansion_depletion_coeff`, `CuspForm.qExpansion_depletion_coeff`: the depletion
  deletes the coefficients at the multiples of `d`.
* `ModularForm.coe_depletion_depletion`, `CuspForm.coe_depletion_depletion`: depletion is
  idempotent.

## References

* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978), 221–243, §3.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N L d : ℕ} {k : ℤ}

/-- The intermediate level `L / d` of the depletion is positive. -/
private lemma neZero_div [NeZero L] [NeZero d] (hdL : d * d ∣ L) : NeZero (L / d) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) ((dvd_mul_right d d).trans hdL))
    (NeZero.pos d)).ne'⟩

/-! ### The depletion of a modular form -/

/-- **The `d`-depletion of a modular form**, `f - V_d U_d f`. For `f` a modular form for `Γ₁(N)`,
`N * d ∣ L` and `d * d ∣ L`, it reads `f` at the level `L / d`, which `d` divides, applies the
upper-triangular Hecke operator `U_d` there, raises the result by `V_d` to level `L`, and subtracts
it from `f` read at level `L`. Its `q`-expansion is that of `f` with the terms of index divisible by
`d` deleted (`qExpansion_depletion_coeff`). -/
def _root_.ModularForm.depletion [NeZero L] (d : ℕ) [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k :=
  haveI := neZero_div (L := L) hdL
  _root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd ((dvd_mul_right N d).trans hNL)) f -
    ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd
      (dvd_of_eq (Nat.mul_div_cancel' ((dvd_mul_right d d).trans hdL))))
      (heckeSlashUpperTriModularFormEnd k (Nat.dvd_div_of_mul_dvd hdL)
        (_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd
          (Nat.dvd_div_of_mul_dvd (mul_comm N d ▸ hNL))) f))

/-- The defining formula of the depletion: `(f - V_d U_d f)(τ) = f(τ) - (U_d f)(d τ)`, where
`U_d f = ∑_{b < d} f ∣ [1, b; 0, d]` is `heckeSlashUpperTri k d f`. -/
@[simp]
lemma _root_.ModularForm.depletion_apply [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    ModularForm.depletion d hNL hdL f τ = f τ - heckeSlashUpperTri k d f (scaleGL d • τ) := by
  simp [ModularForm.depletion]

/-- The `d`-depletion, as a `ℂ`-linear map `M_k(Γ₁(N)) → M_k(Γ₁(L))`. -/
def _root_.ModularForm.depletionₗ [NeZero L] (d : ℕ) [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) :
    _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k where
  toFun := ModularForm.depletion d hNL hdL
  map_add' f g := by
    ext τ
    simp
    ring
  map_smul' c f := by
    ext τ
    simp
    ring

@[simp]
lemma _root_.ModularForm.depletionₗ_apply [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.depletionₗ d hNL hdL f = ModularForm.depletion d hNL hdL f := (rfl)

/-- **The `q`-expansion of the depletion.** `aₙ(f - V_d U_d f)` is `0` when `d ∣ n` and `aₙ(f)`
otherwise. -/
@[simp]
theorem _root_.ModularForm.qExpansion_depletion_coeff [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.depletion d hNL hdL f)).coeff n =
      if d ∣ n then 0 else (qExpansion 1 f).coeff n := by
  have := neZero_div (L := L) hdL
  rw [ModularForm.depletion, FunLike.coe_sub,
    _root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map L),
    map_sub, ModularForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _),
    _root_.ModularForm.coe_restrict]
  split_ifs with hdn
  · rw [coe_heckeSlashUpperTriModularFormEnd,
      qExpansion_coeff_heckeSlashUpperTri' k d (one_mem_strictPeriods_Gamma1_map _) (NeZero.pos d),
      _root_.ModularForm.coe_restrict, Nat.mul_div_cancel' hdn, sub_self]
  · rw [sub_zero]

/-- **Depletion is idempotent**: depleting twice at `d` deletes the same coefficients as depleting
once. The two depletions are compared as functions, at their own levels. -/
theorem _root_.ModularForm.coe_depletion_depletion [NeZero L] {L' : ℕ} [NeZero L'] [NeZero d]
    (hNL : N * d ∣ L) (hdL : d * d ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.depletion d hLL' hdL' (ModularForm.depletion d hNL hdL f)) =
      ⇑(ModularForm.depletion d hNL hdL f) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L')
    (one_mem_strictPeriods_Gamma1_map L) (PowerSeries.ext fun n ↦ ?_)
  simp only [ModularForm.qExpansion_depletion_coeff]
  split_ifs <;> rfl

/-! ### The depletion of a cusp form -/

/-- **The `d`-depletion of a cusp form**, `f - V_d U_d f`, from level `Γ₁(N)` to level `Γ₁(L)`
for `N * d ∣ L` and `d * d ∣ L`. Its underlying function is that of the depletion of `f` as a
modular form (`coe_depletion`). -/
def _root_.CuspForm.depletion [NeZero L] (d : ℕ) [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.CuspForm ((Gamma1 L).map (mapGL ℝ)) k :=
  haveI := neZero_div (L := L) hdL
  _root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd ((dvd_mul_right N d).trans hNL)) f -
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd
      (dvd_of_eq (Nat.mul_div_cancel' ((dvd_mul_right d d).trans hdL))))
      (heckeSlashUpperTriCuspFormEnd k (Nat.dvd_div_of_mul_dvd hdL)
        (_root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd
          (Nat.dvd_div_of_mul_dvd (mul_comm N d ▸ hNL))) f))

/-- The depletion of a cusp form has the same underlying function as the depletion of `f` regarded
as a modular form. -/
@[simp]
lemma _root_.CuspForm.coe_depletion [NeZero L] [NeZero d] (hNL : N * d ∣ L) (hdL : d * d ∣ L)
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.depletion d hNL hdL f) =
      ⇑(ModularForm.depletion d hNL hdL (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  ext τ
  simp [CuspForm.depletion]

/-- The depletion of a cusp form, regarded as a modular form, is the depletion of the underlying
modular form. -/
theorem _root_.ModularForm.depletion_coe_cuspForm [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.depletion d hNL hdL (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (CuspForm.depletion d hNL hdL f : _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k) := by
  ext τ
  simp

/-- **The `q`-expansion of the depletion of a cusp form.** `aₙ(f - V_d U_d f)` is `0` when `d ∣ n`
and `aₙ(f)` otherwise. -/
theorem _root_.CuspForm.qExpansion_depletion_coeff [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.depletion d hNL hdL f)).coeff n =
      if d ∣ n then 0 else (qExpansion 1 f).coeff n := by
  rw [CuspForm.coe_depletion]
  exact ModularForm.qExpansion_depletion_coeff hNL hdL _ n

/-- The `d`-depletion, as a `ℂ`-linear map `S_k(Γ₁(N)) → S_k(Γ₁(L))`. -/
def _root_.CuspForm.depletionₗ [NeZero L] (d : ℕ) [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) :
    _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      _root_.CuspForm ((Gamma1 L).map (mapGL ℝ)) k where
  toFun := CuspForm.depletion d hNL hdL
  map_add' f g := by
    ext τ
    simp
    ring
  map_smul' c f := by
    ext τ
    simp
    ring

@[simp]
lemma _root_.CuspForm.depletionₗ_apply [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.depletionₗ d hNL hdL f = CuspForm.depletion d hNL hdL f := (rfl)

/-- **Depletion of cusp forms is idempotent.** -/
theorem _root_.CuspForm.coe_depletion_depletion [NeZero L] {L' : ℕ} [NeZero L'] [NeZero d]
    (hNL : N * d ∣ L) (hdL : d * d ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.depletion d hLL' hdL' (CuspForm.depletion d hNL hdL f)) =
      ⇑(CuspForm.depletion d hNL hdL f) := by
  rw [CuspForm.coe_depletion, CuspForm.coe_depletion]
  refine (congrArg _ (_root_.ModularForm.ext fun τ ↦ ?_)).trans
    (ModularForm.coe_depletion_depletion hNL hdL hLL' hdL' _)
  simp

end TauCeti
