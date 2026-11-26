/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Basic
public import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination

/-!
# Twisted translations of theta functions

Let `D = (B, χ)` be an Appell–Humbert datum for a subgroup `L` of a complex normed space `V`, with
Riemann form `E` (`TauCeti.AppellHumbertData`). The **twisted translation** by `a ∈ V`
(`TauCeti.AppellHumbertData.translate`) is the complex linear map on functions `V → ℂ`

`(T_a f) (z) = exp (-(B (a, z) + B (a, a) / 2)) f (z + a)`.

It is the analytic form of the pull-back along the translation `t_a` of the torus `V ⧸ L`: it maps
the theta functions of `D` to those of the datum whose semicharacter is twisted by the unitary
character `exp (2πi E (a, ·))` of `L` (`TauCeti.AppellHumbertData.translate_mem_thetaSpace`). This
is the statement `t_a^* L (H, α) ≅ L (H, α · exp (2πi E (a, ·)))` at the level of theta functions;
line bundles on the torus are not formalized here. The twisted data are the sums
`D + ofAddChar ψ` with the topologically trivial data `TauCeti.AppellHumbertData.ofAddChar ψ`,
`B = 0` and semicharacter a character `ψ` of `L`. The theta functions of `ofAddChar ψ` are the
entire maps with `f (z + l) = ψ (l) f (z)`
(`TauCeti.AppellHumbertData.mem_thetaSpace_ofAddChar_iff`), the holomorphic sections of the flat
unitary line bundle of `ψ` studied in `TauCeti.Analysis.Complex.QuasiPeriodic.Basic`. The twist is
trivial exactly when `a` lies in the dual of `L` for `E`
(`TauCeti.AppellHumbertData.riemannChar_eq_one_iff`), and then `T_a` preserves the theta functions
of `D` (`TauCeti.AppellHumbertData.translate_mem_thetaSpace_of_mem_dualSubmodule`). On a theta
function, translation by `l ∈ L` is multiplication by `χ (l)`
(`TauCeti.AppellHumbertData.translate_eq_smul_of_mem_thetaSpace`).

The twisted translations satisfy the Heisenberg relations: `T_u T_v = exp (-πi E (u, v)) T_(u + v)`
(`TauCeti.AppellHumbertData.translate_translate`), so two of them commute up to the phase
`exp (2πi E (v, u))` (`TauCeti.AppellHumbertData.translate_translate_eq_smul_swap`). They are
compatible with products and powers of theta functions.

## Main declarations

* `TauCeti.AppellHumbertData.translate`: the twisted translation `T_a`.
* `TauCeti.AppellHumbertData.ofAddChar`: the datum `(0, ψ)` of a unitary character `ψ` of `L`.
* `TauCeti.AppellHumbertData.riemannChar`: the character `exp (2πi E (a, ·))` of `L`.
* `TauCeti.AppellHumbertData.translate_translate`,
  `TauCeti.AppellHumbertData.translate_translate_eq_smul_swap`: the Heisenberg relations.
* `TauCeti.AppellHumbertData.translate_mem_thetaSpace`: translation twists the semicharacter by
  `exp (2πi E (a, ·))`.

## Provenance

`TauCeti.AppellHumbertData.translate` and its lemmas are adapted from
`New.RealComplexForm.thetaShift`, `New.thetaShift_apply_apply`, `New.differentiable_thetaShift`,
`New.thetaShift_zero`, `New.thetaShift_mul`, `New.thetaShift_pow`, `New.thetaShift_of_mem`,
`New.IsAppellHumbert.thetaShift_thetaShift`, `New.IsAppellHumbert.thetaShift_comm`,
`New.IsAppellHumbert.thetaShift_add_eq_smul_of_mem`, `New.IsAppellHumbert.thetaShift_mem`,
`New.IsAppellHumbert.thetaShift_mem_of_mem_dualLattice` and `New.IsAppellHumbert.mul_riemannPhase`
(file `src/Lib/Shimura/ComplexTheta/AppellHumbertData.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The phases are restated for the Riemann form `E = Im H`,
the negative of the source's. The description of the
twist through the data `TauCeti.AppellHumbertData.ofAddChar` of characters and the
characterization `TauCeti.AppellHumbertData.riemannChar_eq_one_iff` are new here.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Chapter 2 (the translates `t_v^* L (H, α)`).
* D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research, 1970, Chapter I, §2
  (line bundles on a complex torus) and Chapter IV, §23 (the theta group).
-/

public section

open Complex
open scoped Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  (D D' : AppellHumbertData L)

/-! ### Data of unitary characters -/

/-- The topologically trivial Appell–Humbert datum `(0, ψ)` of a unitary character `ψ` of `L`; its
factor of automorphy is `ψ (l)` (`TauCeti.AppellHumbertData.factor_ofAddChar`). -/
noncomputable def ofAddChar (ψ : AddChar L Circle) : AppellHumbertData L where
  form := 0
  re_form_comm _ _ := rfl
  semichar := ψ
  semichar_add_eq_mul l m := by simp [AddChar.map_add_eq_mul]

/-- The form of the datum of a character is `0`. -/
@[simp]
theorem form_ofAddChar (ψ : AddChar L Circle) : (ofAddChar ψ).form = 0 := (rfl)

/-- The semicharacter of the datum of a character `ψ` is `ψ`. -/
@[simp]
theorem semichar_ofAddChar (ψ : AddChar L Circle) : (ofAddChar ψ).semichar = ψ := (rfl)

/-- The factor of automorphy of the datum of a character `ψ` is `ψ (l)`. -/
@[simp]
theorem factor_ofAddChar (ψ : AddChar L Circle) (l : L) (z : V) :
    (ofAddChar ψ).factor l z = ψ l := by
  simp [factor_def]

/-- The theta functions of the datum of a character `ψ` are the entire maps with
`f (z + l) = ψ (l) f (z)`. -/
theorem mem_thetaSpace_ofAddChar_iff (ψ : AddChar L Circle) {f : V → ℂ} :
    f ∈ (ofAddChar ψ).thetaSpace ↔
      Differentiable ℂ f ∧ ∀ (l : L) (z : V), f (z + l) = ψ l * f z := by
  simp [mem_thetaSpace_iff]

/-- The Riemann form of the datum of a character is `0`. -/
@[simp]
theorem riemannForm_ofAddChar (ψ : AddChar L Circle) : (ofAddChar ψ).riemannForm = 0 := by
  ext u v
  simp [riemannForm_apply]

/-- The datum of the trivial character is the zero datum. -/
@[simp]
theorem ofAddChar_one : ofAddChar (1 : AddChar L Circle) = 0 :=
  AppellHumbertData.ext rfl rfl

/-- The unitary character `l ↦ exp (2πi E (a, l))` of `L`, for `a ∈ V` and the Riemann form `E` of
`D`. -/
noncomputable def riemannChar (a : V) : AddChar L Circle :=
  Real.fourierChar.compAddMonoidHom
    ((D.riemannForm a).toAddMonoidHom.comp L.subtype.toAddMonoidHom)

/-- The defining formula of `TauCeti.AppellHumbertData.riemannChar`. -/
@[simp]
theorem riemannChar_apply (a : V) (l : L) :
    D.riemannChar a l = Circle.exp (2 * π * D.riemannForm a l) := (rfl)

/-- The character `exp (2πi E (a, ·))` is trivial exactly when `a` lies in the dual of `L` for the
Riemann form `E`. -/
theorem riemannChar_eq_one_iff {a : V} :
    D.riemannChar a = 1 ↔ a ∈ D.riemannForm.dualSubmodule L := by
  simp only [AddChar.ext_iff, riemannChar_apply, _root_.one_apply,
    LinearMap.BilinForm.mem_dualSubmodule,     Submodule.mem_one, Circle.exp_eq_one, Subtype.forall]
  refine forall₂_congr fun l _ ↦ ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩
  · simp only [algebraMap_int_eq, eq_intCast]
    exact mul_left_cancel₀ Real.two_pi_pos.ne' (by linarith)
  · simp only [algebraMap_int_eq, eq_intCast] at hn
    rw [← hn]
    ring

/-! ### Twisted translations -/

/-- The **twisted translation** by `a ∈ V`, the complex linear map on functions `V → ℂ` given by
`(T_a f) (z) = exp (-(B (a, z) + B (a, a) / 2)) f (z + a)`. -/
noncomputable def translate (a : V) : (V → ℂ) →ₗ[ℂ] V → ℂ where
  toFun f z := exp (-(D.form a z + D.form a a / 2)) * f (z + a)
  map_add' f g := by
    ext z
    simp [mul_add]
  map_smul' c f := by
    ext z
    simp [mul_left_comm]

/-- The defining formula of the twisted translation. -/
@[simp]
theorem translate_apply (a : V) (f : V → ℂ) (z : V) :
    D.translate a f z = exp (-(D.form a z + D.form a a / 2)) * f (z + a) := (rfl)

/-- The twisted translation by `0` is the identity. -/
@[simp]
theorem translate_zero (f : V → ℂ) : D.translate 0 f = f := by
  ext z
  simp [translate_apply]

/-- **Composition of twisted translations**: `T_u T_v = exp (-πi E (u, v)) T_(u + v)`. -/
theorem translate_translate (u v : V) (f : V → ℂ) :
    D.translate u (D.translate v f) =
      exp (-(π * I * D.riemannForm u v)) • D.translate (u + v) f := by
  ext z
  have h_exp : -(D.form u z + D.form u u / 2) + -(D.form v (z + u) + D.form v v / 2) =
      -(π * I * D.riemannForm u v) + -(D.form (u + v) z + D.form (u + v) (u + v) / 2) := by
    simp only [map_add, _root_.add_apply]
    linear_combination (-1 / 2 : ℂ) * D.form_sub_form u v
  simp only [translate_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← exp_add, h_exp, exp_add, add_assoc]
  ring

/-- **The Heisenberg commutation relation**: two twisted translations commute up to the phase
`exp (2πi E (v, u))`. -/
theorem translate_translate_eq_smul_swap (u v : V) (f : V → ℂ) :
    D.translate u (D.translate v f) =
      (Circle.exp (2 * π * D.riemannForm v u) : ℂ) • D.translate v (D.translate u f) := by
  rw [D.translate_translate, D.translate_translate v u, add_comm v u, smul_smul, Circle.coe_exp,
    ← exp_add, D.riemannForm_swap v u]
  congr 2
  push_cast
  ring

/-- Twisted translation is compatible with products: the translate of `f g` for the sum of two data
is the product of the translates. -/
theorem translate_mul (u : V) (f g : V → ℂ) :
    (D + D').translate u (f * g) = D.translate u f * D'.translate u g := by
  ext z
  simp only [translate_apply, form_add, _root_.add_apply, Pi.mul_apply, add_div]
  rw [show -(D.form u z + D'.form u z + (D.form u u / 2 + D'.form u u / 2)) =
    -(D.form u z + D.form u u / 2) + -(D'.form u z + D'.form u u / 2) by ring, exp_add]
  ring

/-- Twisted translation is compatible with powers: the translate of `f ^ n` for `n • D` is the
`n`-th power of the translate. -/
theorem translate_pow (u : V) (f : V → ℂ) (n : ℕ) :
    (n • D).translate u (f ^ n) = D.translate u f ^ n := by
  ext z
  simp only [translate_apply, form_nsmul, _root_.smul_apply, nsmul_eq_mul, Pi.pow_apply, mul_pow,
    ← exp_natCast_mul]
  congr 2
  ring

variable {D} {f : V → ℂ}

/-- On a theta function, the twisted translation by `l ∈ L` is multiplication by `χ (l)`. -/
theorem translate_eq_smul_of_mem_thetaSpace (hf : f ∈ D.thetaSpace) (l : L) :
    D.translate l f = (D.semichar l : ℂ) • f := by
  ext z
  rw [translate_apply, apply_add_of_mem_thetaSpace hf, factor_def, Pi.smul_apply, smul_eq_mul,
    exp_neg]
  field_simp

/-- On a theta function, changing `u` by `l ∈ L` changes the twisted translation by `u` by the
scalar `exp (πi E (u, l)) χ (l)`. -/
theorem translate_add_eq_smul_of_mem_thetaSpace (hf : f ∈ D.thetaSpace) (u : V) (l : L) :
    D.translate (u + l) f = (exp (π * I * D.riemannForm u l) * D.semichar l) • D.translate u f := by
  have h := D.translate_translate u l f
  rw [translate_eq_smul_of_mem_thetaSpace hf, map_smul] at h
  rw [mul_smul, h, smul_smul, ← exp_add, add_neg_cancel, exp_zero, one_smul]

/-- **Translation twists the semicharacter**: the twisted translate by `a ∈ V` of a theta function
of `D` is a theta function of the datum `D + ofAddChar (D.riemannChar a)`, whose semicharacter is
`χ · exp (2πi E (a, ·))`. -/
theorem translate_mem_thetaSpace (hf : f ∈ D.thetaSpace) (a : V) :
    D.translate a f ∈ (D + ofAddChar (D.riemannChar a)).thetaSpace := by
  refine (mem_thetaSpace_iff _).mpr ⟨?_, fun l z ↦ ?_⟩
  · have hdiff := differentiable_of_mem_thetaSpace hf
    have : Differentiable ℂ fun z ↦ exp (-(D.form a z + D.form a a / 2)) := by fun_prop
    exact this.mul (hdiff.comp (differentiable_id.add_const a))
  -- The exponents differ by `B (l, a) - B (a, l) = 2πi E (a, l)`.
  have h_exp : -(D.form a (z + l) + D.form a a / 2) + (D.form l (z + a) + D.form l l / 2) =
      (2 * π * D.riemannForm a l : ℝ) * I + (D.form l z + D.form l l / 2) +
        -(D.form a z + D.form a a / 2) := by
    simp only [map_add]
    push_cast
    linear_combination D.form_sub_form a l
  rw [factor_add, factor_ofAddChar, riemannChar_apply, translate_apply, translate_apply,
    add_right_comm z (l : V) a, apply_add_of_mem_thetaSpace hf l (z + a), factor_def, factor_def,
    Circle.coe_exp]
  calc _ = D.semichar l * exp (-(D.form a (z + l) + D.form a a / 2) +
        (D.form l (z + a) + D.form l l / 2)) * f (z + a) := by
        rw [exp_add (-(D.form a (z + l) + D.form a a / 2))]
        ring
    _ = _ := by
        rw [h_exp, exp_add, exp_add]
        ring

/-- For `a` in the dual of `L` for the Riemann form, the twisted translation by `a` preserves the
theta functions of `D`. -/
theorem translate_mem_thetaSpace_of_mem_dualSubmodule {a : V}
    (ha : a ∈ D.riemannForm.dualSubmodule L) (hf : f ∈ D.thetaSpace) :
    D.translate a f ∈ D.thetaSpace := by
  simpa [(D.riemannChar_eq_one_iff).mpr ha] using translate_mem_thetaSpace hf a

end TauCeti.AppellHumbertData
