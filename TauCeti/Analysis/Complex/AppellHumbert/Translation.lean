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
(`TauCeti.AppellHumbertData.twistedTranslate`) is the complex linear map on functions `V → ℂ`

`(T_a f) (z) = exp (-(B (a, z) + B (a, a) / 2)) f (z + a)`.

When `V` is finite-dimensional and `L` is a full lattice, it is the analytic form of the pull-back
along the translation `t_a` of the torus `V ⧸ L`. The geometric interpretations below assume
these classical hypotheses; the analytic definitions and results do not require them. It maps
the theta functions of `D` to those of the datum whose semicharacter is twisted by the unitary
character `exp (2πi E (a, ·))` of `L`
(`TauCeti.AppellHumbertData.twistedTranslate_mem_thetaSpace`). This
is the statement `t_a^* L (H, α) ≅ L (H, α · exp (2πi E (a, ·)))` at the level of theta functions;
line bundles on the torus are not formalized here. The twisted data are the sums
`D + ofAddChar ψ` with the topologically trivial data `TauCeti.AppellHumbertData.ofAddChar ψ`,
`B = 0` and semicharacter a character `ψ` of `L`. The theta functions of `ofAddChar ψ` are the
entire maps with `f (z + l) = ψ (l) f (z)`
(`TauCeti.AppellHumbertData.mem_thetaSpace_ofAddChar_iff`), the holomorphic sections of the flat
unitary line bundle of `ψ` studied in `TauCeti.Analysis.Complex.QuasiPeriodic.Basic`. The twist is
trivial exactly when `a` lies in the dual of `L` for `E`
(`TauCeti.AppellHumbertData.riemannChar_eq_one_iff`), and then `T_a` preserves the theta functions
of `D` (`TauCeti.AppellHumbertData.twistedTranslate_mem_thetaSpace_of_mem_dualSubmodule`).
On a theta function, translation by `l ∈ L` is multiplication by `χ (l)`
(`TauCeti.AppellHumbertData.twistedTranslate_eq_smul_of_mem_thetaSpace`).

The twisted translations satisfy the Heisenberg relations: `T_u T_v = exp (-πi E (u, v)) T_(u + v)`
(`TauCeti.AppellHumbertData.twistedTranslate_twistedTranslate`), so two of them commute up to the
phase `exp (2πi E (v, u))`
(`TauCeti.AppellHumbertData.twistedTranslate_twistedTranslate_eq_smul_swap`). They are
compatible with products and powers of theta functions. For `a` in the dual `L^⊥` of `L`, the
restriction `U_a` of `T_a` to the theta functions of `D`
(`TauCeti.AppellHumbertData.twistedTranslateEnd`) satisfies the same relations as endomorphisms.

**Normalised translations.** For a complex linear endomorphism `b` of `V`, the normalised
translation `N_x = χ_b (x)⁻¹ T_x` (`TauCeti.AppellHumbertData.normalizedTranslate`) divides `T_x` by
the canonical multiplier `χ_b (x) = exp (πi E (x, b x))`. If
`E (b u, w) + E (u, b w) = E (u, w)`, they satisfy the Heisenberg law
`N_x N_y = exp (2πi E (y, b x)) N_(x + y)`
(`TauCeti.AppellHumbertData.normalizedTranslate_normalizedTranslate`), and the theta functions of
the datum `(B, χ_b)` of `TauCeti.AppellHumbertData.ofCanonicalSemichar` are the entire functions
fixed by every `N_l`, `l ∈ L` (`TauCeti.AppellHumbertData.mem_thetaSpace_ofCanonicalSemichar_iff`).
The Riemann form here is `E = Im H`. With the opposite convention
`E_B (u, v) = Im (B (u, v) - B (v, u)) / 2π = -E (u, v)`, used for instance for the canonical
factors of Birkenhake–Lange, Section 3.1, the multiplier `exp (πi E_B (b x, x))` is
`exp (πi E (x, b x))`, and the phase `exp (2πi E_B (b x, y))` is `exp (2πi E (y, b x))`.

## Main declarations

* `TauCeti.AppellHumbertData.twistedTranslate`: the twisted translation `T_a`.
* `TauCeti.AppellHumbertData.ofAddChar`: the datum `(0, ψ)` of a unitary character `ψ` of `L`.
* `TauCeti.AppellHumbertData.riemannChar`: the character `exp (2πi E (a, ·))` of `L`.
* `TauCeti.AppellHumbertData.twistedTranslate_twistedTranslate`,
  `TauCeti.AppellHumbertData.twistedTranslate_twistedTranslate_eq_smul_swap`:
  the Heisenberg relations.
* `TauCeti.AppellHumbertData.twistedTranslate_mem_thetaSpace`: translation twists the semicharacter
  by `exp (2πi E (a, ·))`.
* `TauCeti.AppellHumbertData.twistedTranslateEnd`: the twisted translation by `a ∈ L^⊥` as an
  endomorphism of the theta functions.
* `TauCeti.AppellHumbertData.normalizedTranslate`: the normalised translation `N_x`, and its
  Heisenberg law `TauCeti.AppellHumbertData.normalizedTranslate_normalizedTranslate`.

## Provenance

`TauCeti.AppellHumbertData.twistedTranslate` and its lemmas are adapted from
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
`TauCeti.AppellHumbertData.normalizedTranslate`,
`TauCeti.AppellHumbertData.normalizedTranslate_normalizedTranslate` and
`TauCeti.AppellHumbertData.mem_thetaSpace_ofCanonicalSemichar_iff` are adapted from
`New.ThetaTori.normalizedShift`, `New.IsAppellHumbert.normalizedShift_normalizedShift` and
`New.ThetaTori.mem_thetaSpace_iff_normalizedShift`, and
`TauCeti.AppellHumbertData.twistedTranslateEnd` from the endomorphisms of
`New.IsAppellHumbert.linearIndependent_thetaShiftEnd_out` (file
`src/Lib/Shimura/ComplexTheta/DimensionFormula.lean`), at the same commit.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Chapter 2 (the translates `t_v^* L (H, α)`) and Section 3.1 (canonical factors).
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
  semichar_add_eq_circleExp_mul_mul l m := by simp [AddChar.map_add_eq_mul]

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

/-- Multiplying unitary characters adds their Appell–Humbert data. -/
@[simp]
theorem ofAddChar_mul (ψ φ : AddChar L Circle) :
    ofAddChar (ψ * φ) = ofAddChar ψ + ofAddChar φ := by
  apply AppellHumbertData.ext
  · simp only [form_add, form_ofAddChar]
    ext u v
    simp only [_root_.add_apply, _root_.zero_apply]
    exact (add_zero (0 : ℂ)).symm
  · ext l
    rfl

/-- The unitary character `l ↦ exp (2πi E (a, l))` of `L`, for `a ∈ V` and the Riemann form `E` of
`D`. -/
noncomputable def riemannChar (a : V) : AddChar L Circle :=
  Real.fourierChar.compAddMonoidHom
    ((D.riemannForm a).toAddMonoidHom.comp L.subtype.toAddMonoidHom)

/-- The defining formula of `TauCeti.AppellHumbertData.riemannChar`. -/
@[simp]
theorem riemannChar_apply (a : V) (l : L) :
    D.riemannChar a l = Circle.exp (2 * π * D.riemannForm a l) := (rfl)

/-- The Riemann character of the zero vector is trivial. -/
@[simp]
theorem riemannChar_zero : D.riemannChar 0 = 1 := by
  ext l
  simp

/-- Adding translation vectors multiplies their Riemann characters. -/
@[simp]
theorem riemannChar_add (a b : V) : D.riemannChar (a + b) = D.riemannChar a * D.riemannChar b := by
  ext l
  simp [mul_add, Circle.exp_add]

/-- Negating a translation vector inverts its Riemann character. -/
@[simp]
theorem riemannChar_neg (a : V) : D.riemannChar (-a) = (D.riemannChar a)⁻¹ := by
  ext l
  simp [mul_neg, Circle.exp_neg]

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
noncomputable def twistedTranslate (a : V) : (V → ℂ) →ₗ[ℂ] V → ℂ where
  toFun f z := exp (-(D.form a z + D.form a a / 2)) * f (z + a)
  map_add' f g := by
    ext z
    simp [mul_add]
  map_smul' c f := by
    ext z
    simp [mul_left_comm]

/-- The defining formula of the twisted translation. -/
@[simp]
theorem twistedTranslate_apply (a : V) (f : V → ℂ) (z : V) :
    D.twistedTranslate a f z = exp (-(D.form a z + D.form a a / 2)) * f (z + a) := (rfl)

/-- The twisted translation by `0` is the identity. -/
@[simp]
theorem twistedTranslate_zero (f : V → ℂ) : D.twistedTranslate 0 f = f := by
  ext z
  simp [twistedTranslate_apply]

/-- **Composition of twisted translations**: `T_u T_v = exp (-πi E (u, v)) T_(u + v)`. -/
theorem twistedTranslate_twistedTranslate (u v : V) (f : V → ℂ) :
    D.twistedTranslate u (D.twistedTranslate v f) =
      exp (-(π * I * D.riemannForm u v)) • D.twistedTranslate (u + v) f := by
  ext z
  have h_exp : -(D.form u z + D.form u u / 2) + -(D.form v (z + u) + D.form v v / 2) =
      -(π * I * D.riemannForm u v) + -(D.form (u + v) z + D.form (u + v) (u + v) / 2) := by
    simp only [map_add, _root_.add_apply]
    linear_combination (-1 / 2 : ℂ) * D.form_sub_form u v
  simp only [twistedTranslate_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← exp_add, h_exp, exp_add, add_assoc]
  ring

/-- **The Heisenberg commutation relation**: two twisted translations commute up to the phase
`exp (2πi E (v, u))`. -/
theorem twistedTranslate_twistedTranslate_eq_smul_swap (u v : V) (f : V → ℂ) :
    D.twistedTranslate u (D.twistedTranslate v f) =
      (Circle.exp (2 * π * D.riemannForm v u) : ℂ) •
        D.twistedTranslate v (D.twistedTranslate u f) := by
  rw [D.twistedTranslate_twistedTranslate, D.twistedTranslate_twistedTranslate v u, add_comm v u,
    smul_smul, Circle.coe_exp, ← exp_add, D.riemannForm_swap v u]
  congr 2
  push_cast
  ring

/-- Twisted translation is compatible with products: the translate of `f g` for the sum of two data
is the product of the translates. -/
theorem twistedTranslate_mul (u : V) (f g : V → ℂ) :
    (D + D').twistedTranslate u (f * g) = D.twistedTranslate u f * D'.twistedTranslate u g := by
  ext z
  simp only [twistedTranslate_apply, form_add, _root_.add_apply, Pi.mul_apply, add_div]
  have h_exp : -(D.form u z + D'.form u z + (D.form u u / 2 + D'.form u u / 2)) =
      -(D.form u z + D.form u u / 2) + -(D'.form u z + D'.form u u / 2) := by ring
  rw [h_exp, exp_add]
  ring

/-- Twisted translation is compatible with powers: the translate of `f ^ n` for `n • D` is the
`n`-th power of the translate. -/
theorem twistedTranslate_pow (u : V) (f : V → ℂ) (n : ℕ) :
    (n • D).twistedTranslate u (f ^ n) = D.twistedTranslate u f ^ n := by
  ext z
  simp only [twistedTranslate_apply, form_nsmul, _root_.smul_apply, nsmul_eq_mul, Pi.pow_apply,
    mul_pow, ← exp_natCast_mul]
  congr 2
  ring

variable {D} {f : V → ℂ}

/-- On a theta function, the twisted translation by `l ∈ L` is multiplication by `χ (l)`. -/
theorem twistedTranslate_eq_smul_of_mem_thetaSpace (hf : f ∈ D.thetaSpace) (l : L) :
    D.twistedTranslate l f = (D.semichar l : ℂ) • f := by
  ext z
  rw [twistedTranslate_apply, apply_add_of_mem_thetaSpace hf, factor_def, Pi.smul_apply,
    smul_eq_mul, exp_neg]
  field_simp

/-- On a theta function, changing `u` by `l ∈ L` changes the twisted translation by `u` by the
scalar `exp (πi E (u, l)) χ (l)`. -/
theorem twistedTranslate_add_eq_smul_of_mem_thetaSpace (hf : f ∈ D.thetaSpace) (u : V) (l : L) :
    D.twistedTranslate (u + l) f =
      (exp (π * I * D.riemannForm u l) * D.semichar l) • D.twistedTranslate u f := by
  have h := D.twistedTranslate_twistedTranslate u l f
  rw [twistedTranslate_eq_smul_of_mem_thetaSpace hf, map_smul] at h
  rw [mul_smul, h, smul_smul, ← exp_add, add_neg_cancel, exp_zero, one_smul]

/-- **Translation twists the semicharacter**: the twisted translate by `a ∈ V` of a theta function
of `D` is a theta function of the datum `D + ofAddChar (D.riemannChar a)`, whose semicharacter is
`χ · exp (2πi E (a, ·))`. -/
theorem twistedTranslate_mem_thetaSpace (hf : f ∈ D.thetaSpace) (a : V) :
    D.twistedTranslate a f ∈ (D + ofAddChar (D.riemannChar a)).thetaSpace := by
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
  rw [factor_add, factor_ofAddChar, riemannChar_apply, twistedTranslate_apply,
    twistedTranslate_apply, add_right_comm z (l : V) a,
    apply_add_of_mem_thetaSpace hf l (z + a), factor_def, factor_def, Circle.coe_exp]
  calc _ = D.semichar l * exp (-(D.form a (z + l) + D.form a a / 2) +
        (D.form l (z + a) + D.form l l / 2)) * f (z + a) := by
        rw [exp_add (-(D.form a (z + l) + D.form a a / 2))]
        ring
    _ = _ := by
        rw [h_exp, exp_add, exp_add]
        ring

/-- For `a` in the dual of `L` for the Riemann form, the twisted translation by `a` preserves the
theta functions of `D`. -/
theorem twistedTranslate_mem_thetaSpace_of_mem_dualSubmodule {a : V}
    (ha : a ∈ D.riemannForm.dualSubmodule L) (hf : f ∈ D.thetaSpace) :
    D.twistedTranslate a f ∈ D.thetaSpace := by
  simpa [(D.riemannChar_eq_one_iff).mpr ha] using twistedTranslate_mem_thetaSpace hf a

variable (D) in
/-- The **twisted translation** `U_a` by `a` in the dual `L^⊥` of `L` for the Riemann form, as an
endomorphism of the space of theta functions. -/
noncomputable def twistedTranslateEnd (a : D.riemannForm.dualSubmodule L) :
    Module.End ℂ D.thetaSpace :=
  (D.twistedTranslate a).restrict fun _ hf ↦
    twistedTranslate_mem_thetaSpace_of_mem_dualSubmodule a.property hf

/-- On a theta function, `TauCeti.AppellHumbertData.twistedTranslateEnd` is the twisted
translation. -/
@[simp]
theorem coe_twistedTranslateEnd_apply (a : D.riemannForm.dualSubmodule L) (f : D.thetaSpace) :
    (D.twistedTranslateEnd a f : V → ℂ) = D.twistedTranslate a f := (rfl)

variable (D) in
/-- The twisted translation by `0` of theta functions is the identity. -/
@[simp]
theorem twistedTranslateEnd_zero : D.twistedTranslateEnd 0 = 1 :=
  LinearMap.ext fun f ↦ Subtype.ext (by
    rw [coe_twistedTranslateEnd_apply, ZeroMemClass.coe_zero, twistedTranslate_zero,
      one_apply_eq_self])

/-- **Composition of twisted translations of theta functions**:
`U_a U_b = exp (-πi E (a, b)) U_(a + b)`. -/
theorem twistedTranslateEnd_mul (a b : D.riemannForm.dualSubmodule L) :
    D.twistedTranslateEnd a * D.twistedTranslateEnd b =
      exp (-(π * I * D.riemannForm a b)) • D.twistedTranslateEnd (a + b) :=
  LinearMap.ext fun f ↦ Subtype.ext (by
    rw [mul_apply_eq_comp, coe_twistedTranslateEnd_apply, coe_twistedTranslateEnd_apply,
      LinearMap.smul_apply, Submodule.coe_smul, coe_twistedTranslateEnd_apply,
      Submodule.coe_add, D.twistedTranslate_twistedTranslate])

/-! ### Normalised translations -/

variable (D) in
/-- The **normalised translation** `N_x = χ_b (x)⁻¹ T_x` by `x ∈ V`: the twisted translation
divided by the canonical multiplier `χ_b (x) = exp (πi E (x, b x))` of a complex linear map `b`. -/
noncomputable def normalizedTranslate (b : V →L[ℂ] V) (x : V) : (V → ℂ) →ₗ[ℂ] V → ℂ :=
  (Circle.exp (π * D.riemannForm x (b x)) : ℂ)⁻¹ • D.twistedTranslate x

/-- The defining formula of the normalised translation. -/
@[simp]
theorem normalizedTranslate_apply (b : V →L[ℂ] V) (x : V) (f : V → ℂ) :
    D.normalizedTranslate b x f = (Circle.exp (π * D.riemannForm x (b x)) : ℂ)⁻¹ •
      D.twistedTranslate x f := (rfl)

/-- **The Heisenberg law of the normalised translations**: if
`E (b u, w) + E (u, b w) = E (u, w)`, then `N_x N_y = exp (2πi E (y, b x)) N_(x + y)`. -/
theorem normalizedTranslate_normalizedTranslate {b : V →L[ℂ] V}
    (hadj : ∀ u w, D.riemannForm (b u) w + D.riemannForm u (b w) = D.riemannForm u w)
    (x y : V) (f : V → ℂ) :
    D.normalizedTranslate b x (D.normalizedTranslate b y f) =
      (Circle.exp (2 * π * D.riemannForm y (b x)) : ℂ) • D.normalizedTranslate b (x + y) f := by
  -- The multipliers at `x`, `y` and `x + y` contribute `exp (πi (E (x, b y) + E (y, b x)))`.
  have h_exp : D.riemannForm (x + y) (b (x + y)) = D.riemannForm x (b x) +
      D.riemannForm y (b y) + 2 * D.riemannForm x (b y) - D.riemannForm x y := by
    have h1 := hadj x y
    simp only [map_add, LinearMap.add_apply]
    rw [D.riemannForm_swap (b x) y]
    linarith
  have h_phase : D.riemannForm y (b x) = D.riemannForm x (b y) - D.riemannForm x y := by
    have h1 := hadj x y
    rw [D.riemannForm_swap (b x) y]
    linarith
  simp only [normalizedTranslate_apply, map_smul, smul_smul,
    D.twistedTranslate_twistedTranslate x y f]
  congr 1
  rw [h_exp, h_phase]
  simp only [Circle.coe_exp, ← exp_neg, ← exp_add]
  congr 1
  push_cast
  ring

section CanonicalSemichar

variable (B : V →L[ℝ] V →L[ℂ] ℂ) (hB : ∀ u v, (B u v).re = (B v u).re) (b : V →L[ℂ] V)
  (hadj : ∀ u w, (B w (b u) - B (b u) w).im / (2 * π) + (B (b w) u - B u (b w)).im / (2 * π) =
    (B w u - B u w).im / (2 * π))
  (hint : ∀ l m : L, ∃ k : ℤ, (B m (b l) - B (b l) m).im / (2 * π) = k)

/-- The theta functions of `(B, χ_b)` are the entire functions fixed by the normalised
translations `N_l`, `l ∈ L`. -/
theorem mem_thetaSpace_ofCanonicalSemichar_iff {f : V → ℂ} :
    f ∈ (ofCanonicalSemichar B hB b hadj hint).thetaSpace ↔ Differentiable ℂ f ∧
      ∀ l : L, (ofCanonicalSemichar B hB b hadj hint).normalizedTranslate b l f = f := by
  set D' := ofCanonicalSemichar B hB b hadj hint
  have hsc (l : L) : (D'.semichar l : ℂ) = Circle.exp (π * D'.riemannForm l (b l)) := by
    rw [semichar_ofCanonicalSemichar_eq_circleExp]
  rw [mem_thetaSpace_iff]
  refine and_congr_right fun _ ↦ ⟨fun h l ↦ funext fun z ↦ ?_, fun h l z ↦ ?_⟩
  · rw [normalizedTranslate_apply, Pi.smul_apply, twistedTranslate_apply, h l z, factor_def,
      smul_eq_mul, exp_neg, ← hsc]
    have he := exp_ne_zero (D'.form l z + D'.form l l / 2)
    have hc := Circle.coe_ne_zero (D'.semichar l)
    generalize exp (D'.form l z + D'.form l l / 2) = e at he ⊢
    field_simp
  · have h' := congrFun (h l) z
    rw [normalizedTranslate_apply, Pi.smul_apply, twistedTranslate_apply, smul_eq_mul, exp_neg,
      ← hsc] at h'
    rw [factor_def]
    have he := exp_ne_zero (D'.form l z + D'.form l l / 2)
    have hc := Circle.coe_ne_zero (D'.semichar l)
    generalize exp (D'.form l z + D'.form l l / 2) = e at he h' ⊢
    field_simp at h'
    linear_combination h'

end CanonicalSemichar

end TauCeti.AppellHumbertData
