/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Analysis.Calculus.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.LinearCombination

/-!
# Appell–Humbert data and their factors of automorphy

Let `V` be a complex normed space and `L ⊆ V` an additive subgroup (for a complex torus `V ⧸ L`,
the period lattice). An Appell–Humbert datum `D` for `L` (`TauCeti.AppellHumbertData`) consists of

* a continuous form `B (u, z)` on `V`, real linear in `u` and complex linear in `z`, whose real part
  is symmetric, and
* a map `χ : L → U(1)` that is a semicharacter for the Riemann form
  `E (u, v) = Im (B (v, u) - B (u, v)) / (2π)` of `B`:
  `χ (l + m) = exp (π i E (l, m)) χ (l) χ (m)`.

Its factor of automorphy is `e_l (z) = χ (l) exp (B (l, z) + B (l, l) / 2)`, and its theta functions
(`TauCeti.AppellHumbertData.thetaSpace`) are the entire functions `f` with
`f (z + l) = e_l (z) f (z)` for `l ∈ L`. When `V` is finite-dimensional and `L` is a full lattice,
these identify with the holomorphic sections of the line bundle on the complex torus `V ⧸ L`
that `e` defines. The geometric interpretations below assume these classical hypotheses;
the analytic definitions and results do not require them.

The semicharacter law forces `E` to be integral on `L`
(`TauCeti.AppellHumbertData.exists_riemannForm_eq_intCast`), so it reads
`χ (l + m) = (-1) ^ E (l, m) χ (l) χ (m)`, and it makes `e` a cocycle:
`e_(l + m) (z) = e_l (z + m) e_m (z)` (`TauCeti.AppellHumbertData.factor_cocycle`).

**Hermitian data.** For a Hermitian form `H` on `V`, complex linear in the first variable, with
`E = Im H` integral on `L`, and a semicharacter `α : L → U(1)` with
`α (l + m) = (-1) ^ E (l, m) α (l) α (m)`, the form `B (u, z) = π H (z, u)` gives an Appell–Humbert
datum (`TauCeti.AppellHumbertData.ofHermitian`) whose Riemann form is `Im H` and whose factor of
automorphy is the classical `α (l) exp (π H (z, l) + π H (l, l) / 2)`
(`TauCeti.AppellHumbertData.factor_ofHermitian`). Every datum differs from a Hermitian one by a
complex bilinear symmetric part of `B`, which changes the factor by the coboundary of a quadratic
exponential (this decomposition is not formalized here). Correspondingly, multiplication by
`exp ((B' (z, z) - B (z, z)) / 2)` identifies the theta functions of two data with the same
Riemann form and semicharacter (`TauCeti.AppellHumbertData.exp_mul_mem_thetaSpace`). This is why
`B` is not required to be Hermitian: the classical factors used to write theta functions as
Fourier series are of this more general shape.

The data form an additive group (`B` adds, `χ` multiplies), which corresponds to the tensor product
of line bundles; on theta functions, products and powers land in the theta functions of the sum
and of the multiple (`TauCeti.AppellHumbertData.mul_mem_thetaSpace_add`,
`TauCeti.AppellHumbertData.pow_mem_thetaSpace_nsmul`).

The convention for `H`, complex linear in the first variable with `E = Im H`, is that of
`TauCeti.AlmostComplexStructure.RiemannForm.hermitian`, which builds `H` from an integral
Riemann form on the realification of a lattice. Here `V` is a complex normed space and `L` a
subgroup of it, the carrier on which theta functions are holomorphic functions. For `V = ℂ`, the
lattice `ℤ + τℤ` with `Im τ ≠ 0` and an integer `k`, the level-`k` factor `TauCeti.thetaFactor` of
`TauCeti.Analysis.Complex.ThetaLine.Basic` has this shape, with
`B (l, z) = -2πik (Im l / Im τ) z`; this comparison is not formalized here.

## Main declarations

* `TauCeti.AppellHumbertData`: Appell–Humbert data for a subgroup `L`.
* `TauCeti.AppellHumbertData.riemannForm`: the Riemann form `E`.
* `TauCeti.AppellHumbertData.factor`: the factor of automorphy `e_l (z)`.
* `TauCeti.AppellHumbertData.factor_cocycle`: the cocycle law.
* `TauCeti.AppellHumbertData.le_dualSubmodule`: `E` is integral on `L`.
* `TauCeti.AppellHumbertData.thetaSpace`: the theta functions of a datum.
* `TauCeti.AppellHumbertData.ofHermitian`: the datum of a Hermitian form and a semicharacter.

## Provenance

`TauCeti.AppellHumbertData`, `TauCeti.AppellHumbertData.riemannForm` (with `riemannForm_apply`,
`riemannForm_self`, `riemannForm_swap`, `form_sub_form`), `TauCeti.AppellHumbertData.thetaSpace`
(with `mem_thetaSpace_iff`, `differentiable_of_mem_thetaSpace`, `apply_add_of_mem_thetaSpace`),
`TauCeti.AppellHumbertData.le_dualSubmodule`, `TauCeti.AppellHumbertData.exp_mul_mem_thetaSpace`,
the sum, negative and multiples of data,
`TauCeti.AppellHumbertData.mul_mem_thetaSpace_add` and
`TauCeti.AppellHumbertData.pow_mem_thetaSpace_nsmul` are adapted from `New.IsAppellHumbert`,
`New.RealComplexForm.riemannForm`, `New.riemannForm_def`, `New.riemannForm_self`,
`New.riemannForm_swap`, `New.IsAppellHumbert.sub_eq_riemannForm`,
`New.RealComplexForm.thetaSpace`, `New.mem_thetaSpace_iff`, `New.differentiable_of_mem_thetaSpace`,
`New.apply_add_of_mem_thetaSpace`, `New.IsAppellHumbert.le_dualLattice`,
`New.IsAppellHumbert.exp_mul_mem_thetaSpace`,
`New.IsAppellHumbert.add`, `New.IsAppellHumbert.neg`, `New.IsAppellHumbert.nsmul`,
`New.thetaSpace.mul` and `New.thetaSpace.pow` (file
`src/Lib/Shimura/ComplexTheta/AppellHumbertData.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The Riemann form here is the negative of the source's,
so that `E = Im H`, and the semicharacter is a map
`L → U(1)` rather than a function on `V` of modulus one on `L`. The bundled datum and its group
structure, the cocycle law `TauCeti.AppellHumbertData.factor_cocycle`, the integrality
statement in `(-1) ^ E` form and the Hermitian constructor
`TauCeti.AppellHumbertData.ofHermitian` are new here.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Chapter 2 (factors of automorphy, the Appell–Humbert theorem) and Chapter 3 (canonical and
  classical factors).
* D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research, 1970, Chapter I, §2
  (line bundles on a complex torus, the Appell–Humbert theorem).
-/

public section

open Complex
open scoped Real ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

variable (L) in
/-- **Appell–Humbert data** for a subgroup `L` of a complex normed space `V`: a continuous form
`B (u, z)` (`form`), real linear in `u` and complex linear in `z`, with symmetric real part, and a
semicharacter `χ : L → U(1)` (`semichar`) for the Riemann form
`E (u, v) = Im (B (v, u) - B (u, v)) / (2π)` of `B`, that is
`χ (l + m) = exp (π i E (l, m)) χ (l) χ (m)`. The factor of automorphy of the datum is
`χ (l) exp (B (l, z) + B (l, l) / 2)` (`TauCeti.AppellHumbertData.factor`). -/
@[ext]
structure AppellHumbertData where
  /-- The form `B (u, z)`, real linear in `u` and complex linear in `z`. -/
  form : V →L[ℝ] V →L[ℂ] ℂ
  /-- The real part of `B` is symmetric. -/
  re_form_comm (u v : V) : (form u v).re = (form v u).re
  /-- The semicharacter `χ : L → U(1)`. -/
  semichar : L → Circle
  /-- The semicharacter law `χ (l + m) = exp (π i E (l, m)) χ (l) χ (m)`, where
  `π E (l, m) = Im (B (m, l) - B (l, m)) / 2`. -/
  semichar_add_eq_circleExp_mul_mul (l m : L) :
    semichar (l + m) = Circle.exp ((form m l - form l m).im / 2) * semichar l * semichar m

namespace AppellHumbertData

variable (D D' : AppellHumbertData L)

/-! ### The Riemann form -/

/-- The **Riemann form** `E (u, v) = Im (B (v, u) - B (u, v)) / (2π)` of an Appell–Humbert datum,
an alternating real bilinear form on `V`. For a Hermitian datum `B (u, z) = π H (z, u)` it is
`Im H` (`TauCeti.AppellHumbertData.riemannForm_ofHermitian_apply`). -/
noncomputable def riemannForm : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun u v ↦ (D.form v u - D.form u v).im / (2 * π))
    (fun u u' v ↦ by
      simp only [map_add, _root_.add_apply, Complex.sub_im, Complex.add_im]
      ring)
    (fun c u v ↦ by
      simp only [map_smul, _root_.smul_apply, ContinuousLinearMap.map_smul_of_tower]
      simp only [Complex.real_smul, ← mul_sub, Complex.im_ofReal_mul]
      ring)
    (fun u v v' ↦ by
      simp only [map_add, _root_.add_apply, Complex.sub_im, Complex.add_im]
      ring)
    (fun c u v ↦ by
      simp only [map_smul, _root_.smul_apply, ContinuousLinearMap.map_smul_of_tower]
      simp only [Complex.real_smul, ← mul_sub, Complex.im_ofReal_mul]
      ring)

/-- The defining formula `E (u, v) = Im (B (v, u) - B (u, v)) / (2π)` of the Riemann form. -/
theorem riemannForm_apply (u v : V) :
    D.riemannForm u v = (D.form v u - D.form u v).im / (2 * π) := (rfl)

/-- The Riemann form is alternating. -/
@[simp]
theorem riemannForm_self (u : V) : D.riemannForm u u = 0 := by
  simp [riemannForm_apply]

/-- The Riemann form is antisymmetric. -/
theorem riemannForm_swap (u v : V) : D.riemannForm v u = -D.riemannForm u v := by
  simp only [riemannForm_apply, ← neg_div, ← Complex.neg_im, neg_sub]

/-- As the real part of `B` is symmetric, `B (v, u) - B (u, v) = 2πi E (u, v)`. -/
theorem form_sub_form (u v : V) :
    D.form v u - D.form u v = 2 * π * I * D.riemannForm u v := by
  apply Complex.ext
  · simp [D.re_form_comm u v]
  · have h : 2 * π * I * (D.riemannForm u v : ℂ) = ((2 * π * D.riemannForm u v : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h, Complex.mul_I_im, Complex.ofReal_re, riemannForm_apply]
    field_simp

/-- The semicharacter law `χ (l + m) = exp (π i E (l, m)) χ (l) χ (m)`. -/
theorem semichar_add_eq_circleExp_mul (l m : L) :
    D.semichar (l + m) = Circle.exp (π * D.riemannForm l m) * D.semichar l * D.semichar m := by
  rw [D.semichar_add_eq_circleExp_mul_mul, riemannForm_apply]
  congr 3
  field_simp

/-- The semicharacter is `1` at the zero period. -/
@[simp]
theorem semichar_apply_zero : D.semichar 0 = 1 := by
  simpa using D.semichar_add_eq_circleExp_mul_mul 0 0

/-- **The Riemann form is integral on `L`**: for `l, m ∈ L`, `E (l, m)` is an integer. Comparing
`χ (l + m)` with `χ (m + l)` gives `exp (2πi E (l, m)) = 1`. -/
theorem exists_riemannForm_eq_intCast (l m : L) : ∃ n : ℤ, D.riemannForm l m = n := by
  have h := D.semichar_add_eq_circleExp_mul l m
  rw [add_comm, D.semichar_add_eq_circleExp_mul m l, D.riemannForm_swap,
    mul_right_comm _ (D.semichar m)] at h
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp (mul_right_cancel (mul_right_cancel h))
  exact ⟨-k, mul_left_cancel₀ Real.pi_ne_zero (by push_cast; linear_combination (-1 / 2 : ℝ) * hk)⟩

/-- **`L` lies in its dual for the Riemann form**: `E` is integral on `L`. -/
theorem le_dualSubmodule : L ≤ D.riemannForm.dualSubmodule L := fun l hl m hm ↦ by
  obtain ⟨n, hn⟩ := D.exists_riemannForm_eq_intCast ⟨l, hl⟩ ⟨m, hm⟩
  exact Submodule.mem_one.mpr ⟨n, by simpa using hn.symm⟩

/-- `exp (2πi E (l, m)) = 1` for `l, m ∈ L`. -/
theorem circleExp_two_pi_mul_riemannForm_eq_one (l m : L) :
    Circle.exp (2 * π * D.riemannForm l m) = 1 := by
  obtain ⟨n, hn⟩ := D.exists_riemannForm_eq_intCast l m
  rw [hn]
  exact Circle.exp_two_pi_mul_int n

/-- The semicharacter law in the form `χ (l + m) = (-1) ^ E (l, m) χ (l) χ (m)`, with the integer
`n = E (l, m)`. -/
theorem semichar_add_eq_neg_one_zpow_mul (l m : L) {n : ℤ} (hn : D.riemannForm l m = n) :
    (D.semichar (l + m) : ℂ) = (-1) ^ n * D.semichar l * D.semichar m := by
  rw [D.semichar_add_eq_circleExp_mul, hn]
  simp only [Circle.coe_mul, mul_comm π (n : ℝ), Circle.exp_intCast_mul, Circle.coe_zpow,
    Circle.coe_exp, exp_pi_mul_I]

/-! ### The factor of automorphy -/

/-- The **factor of automorphy** `e_l (z) = χ (l) exp (B (l, z) + B (l, l) / 2)` of an
Appell–Humbert datum, for `l ∈ L` and `z ∈ V`. -/
noncomputable def factor (l : L) (z : V) : ℂ :=
  D.semichar l * exp (D.form l z + D.form l l / 2)

/-- The defining formula of the factor of automorphy. -/
theorem factor_def (l : L) (z : V) :
    D.factor l z = D.semichar l * exp (D.form l z + D.form l l / 2) := (rfl)

/-- The factor of automorphy is `1` at the zero period. -/
@[simp]
theorem factor_zero_period (z : V) : D.factor 0 z = 1 := by
  simp [factor_def]

/-- The factor of automorphy does not vanish. -/
theorem factor_ne_zero (l : L) (z : V) : D.factor l z ≠ 0 :=
  mul_ne_zero (Circle.coe_ne_zero _) (exp_ne_zero _)

/-- **The cocycle law** `e_(l + m) (z) = e_l (z + m) e_m (z)` of the factor of automorphy, which
makes `(z, w) ↦ (z + l, e_l (z) w)` an action of `L` on `V × ℂ`. -/
theorem factor_cocycle (l m : L) (z : V) :
    D.factor (l + m) z = D.factor l (z + m) * D.factor m z := by
  -- The exponents differ by `2πi E (l, m)`, by `form_sub_form`; this is `1` by integrality.
  have h_exp : ((π * D.riemannForm l m : ℝ) : ℂ) * I +
      (D.form (l + m : L) z + D.form (l + m : L) (l + m : L) / 2) =
        (D.form l (z + m) + D.form l l / 2) + (D.form m z + D.form m m / 2) +
          2 * π * I * D.riemannForm l m := by
    simp only [Submodule.coe_add, map_add, _root_.add_apply]
    push_cast
    linear_combination (1 / 2 : ℂ) * D.form_sub_form l m
  have h_one : exp (2 * π * I * D.riemannForm l m) = 1 := by
    have := congrArg ((↑) : Circle → ℂ) (D.circleExp_two_pi_mul_riemannForm_eq_one l m)
    rw [Circle.coe_exp, Circle.coe_one] at this
    rw [← this]
    congr 1
    push_cast
    ring
  rw [factor_def, factor_def, factor_def, D.semichar_add_eq_circleExp_mul, Circle.coe_mul,
    Circle.coe_mul, Circle.coe_exp]
  calc _ = D.semichar l * D.semichar m * exp (((π * D.riemannForm l m : ℝ) : ℂ) * I +
        (D.form (l + m : L) z + D.form (l + m : L) (l + m : L) / 2)) := by
        rw [exp_add (((π * D.riemannForm l m : ℝ) : ℂ) * I)]
        ring
    _ = _ := by
        rw [h_exp, exp_add, exp_add, h_one]
        ring

/-! ### The group of Appell–Humbert data -/

/-- The datum with `B = 0` and `χ = 1`, whose factor of automorphy is `1`. -/
noncomputable instance : Zero (AppellHumbertData L) where
  zero :=
    { form := 0
      re_form_comm _ _ := rfl
      semichar := 1
      semichar_add_eq_circleExp_mul_mul _ _ := by simp }

/-- The sum of two data: the forms add and the semicharacters multiply. -/
noncomputable instance : Add (AppellHumbertData L) where
  add D D' :=
    { form := D.form + D'.form
      re_form_comm u v := by simp [D.re_form_comm u v, D'.re_form_comm u v]
      semichar := D.semichar * D'.semichar
      semichar_add_eq_circleExp_mul_mul l m := by
        simp only [Pi.mul_apply, D.semichar_add_eq_circleExp_mul_mul,
          D'.semichar_add_eq_circleExp_mul_mul, _root_.add_apply, add_sub_add_comm, Complex.add_im,
          add_div, Circle.exp_add]
        simp only [mul_comm, mul_assoc, mul_left_comm] }

/-- The negative of a datum: `(-B, χ⁻¹)`. -/
noncomputable instance : Neg (AppellHumbertData L) where
  neg D :=
    { form := -D.form
      re_form_comm u v := by simp [D.re_form_comm u v]
      semichar := D.semichar⁻¹
      semichar_add_eq_circleExp_mul_mul l m := by
        have h : ((-D.form) m l - (-D.form) l m).im / 2 =
            -((D.form m l - D.form l m).im / 2) := by
          simp only [_root_.neg_apply, neg_sub_neg, ← neg_sub (D.form m l), Complex.neg_im,
            neg_div]
        rw [h, Circle.exp_neg, Pi.inv_apply, Pi.inv_apply, Pi.inv_apply,
          D.semichar_add_eq_circleExp_mul_mul, mul_inv, mul_inv] }

/-- The difference of two data: `(B - B', χ / χ')`. -/
noncomputable instance : Sub (AppellHumbertData L) where
  sub D D' := D + -D'

/-- The `n`-th multiple of a datum: `(n • B, χ ^ n)`. -/
noncomputable instance : SMul ℕ (AppellHumbertData L) where
  smul n D :=
    { form := n • D.form
      re_form_comm u v := by simp [D.re_form_comm u v]
      semichar := D.semichar ^ n
      semichar_add_eq_circleExp_mul_mul l m := by
        simp only [Pi.pow_apply, D.semichar_add_eq_circleExp_mul_mul, _root_.smul_apply, ← smul_sub,
          Complex.smul_im, smul_div_assoc, Circle.exp_nsmul, mul_pow] }

/-- The `n`-th multiple of a datum, for an integer `n`: `(n • B, χ ^ n)`. -/
noncomputable instance : SMul ℤ (AppellHumbertData L) where
  smul n D :=
    { form := n • D.form
      re_form_comm u v := by simp [D.re_form_comm u v]
      semichar := D.semichar ^ n
      semichar_add_eq_circleExp_mul_mul l m := by
        simp only [Pi.pow_apply, D.semichar_add_eq_circleExp_mul_mul, _root_.smul_apply, ← smul_sub,
          Complex.smul_im, smul_div_assoc, Circle.exp_zsmul, mul_zpow] }

/-- The form of the zero datum is `0`. -/
@[simp] theorem form_zero : (0 : AppellHumbertData L).form = 0 := rfl

/-- The semicharacter of the zero datum is `1`. -/
@[simp] theorem semichar_zero : (0 : AppellHumbertData L).semichar = 1 := rfl

/-- The form of a sum is the sum of the forms. -/
@[simp] theorem form_add : (D + D').form = D.form + D'.form := rfl

/-- The semicharacter of a sum is the product of the semicharacters. -/
@[simp] theorem semichar_add : (D + D').semichar = D.semichar * D'.semichar := rfl

/-- The form of `-D` is `-B`. -/
@[simp] theorem form_neg : (-D).form = -D.form := rfl

/-- The semicharacter of `-D` is `χ⁻¹`. -/
@[simp] theorem semichar_neg : (-D).semichar = D.semichar⁻¹ := rfl

/-- The form of a difference is the difference of the forms. -/
@[simp] theorem form_sub : (D - D').form = D.form - D'.form := by
  rw [sub_eq_add_neg D.form]
  rfl

/-- The semicharacter of a difference is the quotient of the semicharacters. -/
@[simp] theorem semichar_sub : (D - D').semichar = D.semichar / D'.semichar := by
  rw [div_eq_mul_inv D.semichar]
  rfl

/-- The form of `n • D` is `n • B`. -/
@[simp] theorem form_nsmul (n : ℕ) : (n • D).form = n • D.form := rfl

/-- The semicharacter of `n • D` is `χ ^ n`. -/
@[simp] theorem semichar_nsmul (n : ℕ) : (n • D).semichar = D.semichar ^ n := rfl

/-- The form of `n • D` is `n • B`, for an integer `n`. -/
@[simp] theorem form_zsmul (n : ℤ) : (n • D).form = n • D.form := rfl

/-- The semicharacter of `n • D` is `χ ^ n`, for an integer `n`. -/
@[simp] theorem semichar_zsmul (n : ℤ) : (n • D).semichar = D.semichar ^ n := rfl

/-- Appell–Humbert data for `L` form an additive commutative group, the group of factors of
automorphy of Appell–Humbert type, in which the sum corresponds to the tensor product of line
bundles. -/
noncomputable instance : AddCommGroup (AppellHumbertData L) :=
  Function.Injective.addCommGroup
    (fun D : AppellHumbertData L ↦ (D.form, Additive.ofMul D.semichar))
    (fun _ _ h ↦ AppellHumbertData.ext (congrArg Prod.fst h)
      (Additive.ofMul.injective (congrArg Prod.snd h)))
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun D D' ↦ Prod.ext (form_sub D D') (congrArg Additive.ofMul (semichar_sub D D')))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Evaluation of the factor of automorphy is a homomorphism from addition of data to
multiplication of nonzero complex numbers. -/
noncomputable def factorHom (l : L) (z : V) : AppellHumbertData L →+ Additive ℂˣ where
  toFun D := Additive.ofMul (Units.mk0 (D.factor l z) (D.factor_ne_zero l z))
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    simp [factor_def]
  map_add' D D' := by
    apply Additive.toMul.injective
    apply Units.ext
    -- Reduce the unit and additive wrappers before rewriting the complex-valued formula.
    change (D + D').factor l z = D.factor l z * D'.factor l z
    simp only [factor_def, form_add, semichar_add, Pi.mul_apply, Circle.coe_mul,
      _root_.add_apply, add_div]
    rw [add_add_add_comm, exp_add]
    ring

/-- The value of the factor homomorphism is the factor of automorphy. -/
@[simp]
theorem factorHom_apply (l : L) (z : V) (D : AppellHumbertData L) :
    ((factorHom l z D).toMul : ℂ) = D.factor l z := (rfl)

/-- The factor of automorphy of the zero datum is `1`. -/
@[simp]
theorem factor_zero (l : L) (z : V) : (0 : AppellHumbertData L).factor l z = 1 := by
  simpa only [toMul_zero, Units.val_one, factorHom_apply] using
    congrArg (fun u : Additive ℂˣ ↦ (u.toMul : ℂ)) (map_zero (factorHom l z))

/-- The factor of automorphy of a sum is the product of the factors. -/
@[simp]
theorem factor_add (l : L) (z : V) : (D + D').factor l z = D.factor l z * D'.factor l z := by
  simpa only [toMul_add, Units.val_mul, factorHom_apply] using
    congrArg (fun u : Additive ℂˣ ↦ (u.toMul : ℂ)) (map_add (factorHom l z) D D')

/-- The factor of automorphy of a negative datum is the inverse factor. -/
@[simp]
theorem factor_neg (l : L) (z : V) : (-D).factor l z = (D.factor l z)⁻¹ := by
  simpa only [toMul_neg, Units.val_inv_eq_inv_val, factorHom_apply] using
    congrArg (fun u : Additive ℂˣ ↦ (u.toMul : ℂ)) (map_neg (factorHom l z) D)

/-- The factor of automorphy of a difference is the quotient of the factors. -/
@[simp]
theorem factor_sub (l : L) (z : V) : (D - D').factor l z = D.factor l z / D'.factor l z := by
  simpa only [toMul_sub, Units.val_div_eq_div_val, factorHom_apply] using
    congrArg (fun u : Additive ℂˣ ↦ (u.toMul : ℂ)) (map_sub (factorHom l z) D D')

/-- Natural multiples of a datum give natural powers of its factor of automorphy. -/
@[simp]
theorem factor_nsmul (n : ℕ) (l : L) (z : V) : (n • D).factor l z = D.factor l z ^ n := by
  simpa only [toMul_nsmul, Units.val_pow_eq_pow_val, factorHom_apply] using
    congrArg (fun u : Additive ℂˣ ↦ (u.toMul : ℂ)) (map_nsmul (factorHom l z) n D)

/-- Integer multiples of a datum give integer powers of its factor of automorphy. -/
@[simp]
theorem factor_zsmul (n : ℤ) (l : L) (z : V) : (n • D).factor l z = D.factor l z ^ n := by
  simpa only [toMul_zsmul, Units.val_zpow_eq_zpow_val, factorHom_apply] using
    congrArg (fun u : Additive ℂˣ ↦ (u.toMul : ℂ)) (map_zsmul (factorHom l z) n D)

/-- The Riemann form as an additive homomorphism in the datum. -/
noncomputable def riemannFormHom : AppellHumbertData L →+ LinearMap.BilinForm ℝ V where
  toFun := riemannForm
  map_zero' := by
    ext u v
    simp [riemannForm_apply]
  map_add' D D' := by
    ext u v
    simp only [riemannForm_apply, form_add, _root_.add_apply, LinearMap.add_apply]
    rw [add_sub_add_comm, Complex.add_im, add_div]

/-- Evaluation of the Riemann form homomorphism. -/
@[simp]
theorem riemannFormHom_apply (D : AppellHumbertData L) : riemannFormHom D = D.riemannForm := (rfl)

/-- The Riemann form of the zero datum is `0`. -/
@[simp]
theorem riemannForm_zero : (0 : AppellHumbertData L).riemannForm = 0 :=
  map_zero riemannFormHom

/-- The Riemann form is additive in the datum. -/
@[simp]
theorem riemannForm_add : (D + D').riemannForm = D.riemannForm + D'.riemannForm :=
  map_add riemannFormHom D D'

/-- The Riemann form of a negative datum is the negative Riemann form. -/
@[simp]
theorem riemannForm_neg : (-D).riemannForm = -D.riemannForm :=
  map_neg riemannFormHom D

/-- The Riemann form of a difference is the difference of the Riemann forms. -/
@[simp]
theorem riemannForm_sub : (D - D').riemannForm = D.riemannForm - D'.riemannForm :=
  map_sub riemannFormHom D D'

/-- The Riemann form of a natural multiple is the same multiple of the Riemann form. -/
@[simp]
theorem riemannForm_nsmul (n : ℕ) : (n • D).riemannForm = n • D.riemannForm :=
  map_nsmul riemannFormHom n D

/-- The Riemann form of an integer multiple is the same multiple of the Riemann form. -/
@[simp]
theorem riemannForm_zsmul (n : ℤ) : (n • D).riemannForm = n • D.riemannForm :=
  map_zsmul riemannFormHom n D

/-! ### Theta functions -/

/-- The space of **theta functions** of an Appell–Humbert datum: the entire functions `f : V → ℂ`
with `f (z + l) = e_l (z) f (z)` for `l ∈ L`, where `e` is the factor of automorphy. -/
noncomputable def thetaSpace : Submodule ℂ (V → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ (l : L) (z : V), f (z + l) = D.factor l z * f z}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun l z ↦ by simp [hf.2 l z, hg.2 l z, mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, by simp⟩
  smul_mem' c _ hf := ⟨hf.1.const_smul c, fun l z ↦ by simp [hf.2 l z, mul_left_comm]⟩

/-- Membership in the theta functions, written out. -/
theorem mem_thetaSpace_iff {f : V → ℂ} :
    f ∈ D.thetaSpace ↔ Differentiable ℂ f ∧ ∀ (l : L) (z : V), f (z + l) = D.factor l z * f z :=
  Iff.rfl

variable {D} in
/-- A theta function is entire. -/
theorem differentiable_of_mem_thetaSpace {f : V → ℂ} (hf : f ∈ D.thetaSpace) :
    Differentiable ℂ f :=
  hf.1

variable {D} in
/-- The automorphy law `f (z + l) = e_l (z) f (z)` of a theta function. -/
theorem apply_add_of_mem_thetaSpace {f : V → ℂ} (hf : f ∈ D.thetaSpace) (l : L) (z : V) :
    f (z + l) = D.factor l z * f z :=
  hf.2 l z

variable {D D'} in
/-- **The product of theta functions** of two data is a theta function of their sum. -/
theorem mul_mem_thetaSpace_add {f g : V → ℂ} (hf : f ∈ D.thetaSpace) (hg : g ∈ D'.thetaSpace) :
    f * g ∈ (D + D').thetaSpace :=
  ⟨(differentiable_of_mem_thetaSpace hf).mul (differentiable_of_mem_thetaSpace hg), fun l z ↦ by
    simp only [Pi.mul_apply, hf.2 l z, hg.2 l z, factor_add]
    ring⟩

variable {D} in
/-- **The `n`-th power of a theta function** of `D` is a theta function of `n • D`. -/
theorem pow_mem_thetaSpace_nsmul {f : V → ℂ} (hf : f ∈ D.thetaSpace) (n : ℕ) :
    f ^ n ∈ (n • D).thetaSpace :=
  ⟨Differentiable.pow (differentiable_of_mem_thetaSpace hf) n, fun l z ↦ by
    simp only [Pi.pow_apply, hf.2 l z, factor_nsmul, mul_pow]⟩

variable {D D'} in
/-- **Change of the symmetric part.** If two Appell–Humbert data have the same Riemann form and the
same semicharacter, then `B' - B` is complex bilinear and symmetric, and multiplication by
`exp ((B' (z, z) - B (z, z)) / 2)` sends theta functions of the first datum to theta functions of
the second. -/
theorem exp_mul_mem_thetaSpace (h_riem : D.riemannForm = D'.riemannForm)
    (h_semichar : D.semichar = D'.semichar) {f : V → ℂ} (hf : f ∈ D.thetaSpace) :
    (fun z ↦ exp ((D'.form z z - D.form z z) / 2) * f z) ∈ D'.thetaSpace := by
  -- `B' - B` is symmetric, as both forms have the Riemann form `E`.
  have h_symm (u v : V) : (D'.form - D.form) u v = (D'.form - D.form) v u := by
    have h := D'.form_sub_form u v
    rw [← h_riem] at h
    simp only [_root_.sub_apply]
    linear_combination D.form_sub_form u v - h
  have h_diff : Differentiable ℂ fun z ↦ (D'.form z z - D.form z z) / 2 := by
    simpa only [_root_.sub_apply, div_eq_mul_inv] using
      (ContinuousLinearMap.differentiable_apply_self_of_symm _ h_symm).mul_const (2⁻¹ : ℂ)
  refine ⟨h_diff.cexp.mul (differentiable_of_mem_thetaSpace hf), fun l z ↦ ?_⟩
  have h_exp : (D'.form (z + l) (z + l) - D.form (z + l) (z + l)) / 2 +
      (D.form l z + D.form l l / 2) =
      (D'.form l z + D'.form l l / 2) + (D'.form z z - D.form z z) / 2 := by
    have := h_symm z l
    simp only [map_add, _root_.add_apply, _root_.sub_apply] at this ⊢
    linear_combination this / 2
  simp only [hf.2 l z, factor_def, h_semichar]
  rw [← mul_assoc, mul_left_comm, ← exp_add, h_exp, exp_add]
  ring

/-! ### Hermitian data -/

/-- The Appell–Humbert datum `(B, α)` of a **Hermitian form** `H` on `V`, complex linear in the
first variable and conjugate linear in the second, whose imaginary part `E = Im H` is integral on
`L`, and of a semicharacter `α : L → U(1)` with `α (l + m) = (-1) ^ E (l, m) α (l) α (m)`. The form
is `B (u, z) = π H (z, u)`, so the factor of automorphy is `α (l) exp (π H (z, l) + π H (l, l) / 2)`
(`TauCeti.AppellHumbertData.factor_ofHermitian`) and the Riemann form is `Im H`
(`TauCeti.AppellHumbertData.riemannForm_ofHermitian_apply`). -/
noncomputable def ofHermitian (H : V →L[ℂ] V →L⋆[ℂ] ℂ) (hH : ∀ u v, conj (H u v) = H v u)
    (h_int : ∀ l m : L, ∃ n : ℤ, (H l m).im = n) (α : L → Circle)
    (hα : ∀ (l m : L) (n : ℤ), (H l m).im = n → (α (l + m) : ℂ) = (-1) ^ n * α l * α m) :
    AppellHumbertData L where
  form := (π : ℂ) • AddMonoidHom.toRealLinearMap (H.flip : V →+ V →L[ℂ] ℂ) H.flip.continuous
  re_form_comm u v := by
    simp [← hH u v]
  semichar := α
  semichar_add_eq_circleExp_mul_mul l m := by
    obtain ⟨n, hn⟩ := h_int l m
    have h_im : ((π : ℂ) * H l m - π * H m l).im / 2 = n * π := by
      rw [← hH l m, ← hn]
      simp only [Complex.sub_im, Complex.im_ofReal_mul, Complex.conj_im]
      ring
    ext1
    simp only [_root_.smul_apply, AddMonoidHom.coe_toRealLinearMap, AddMonoidHom.coe_ofClass,
      ContinuousLinearMap.flip_apply, smul_eq_mul, h_im, Circle.coe_mul,
      hα l m n hn]
    simp only [Circle.exp_intCast_mul, Circle.coe_zpow, Circle.coe_exp, exp_pi_mul_I]

variable (H : V →L[ℂ] V →L⋆[ℂ] ℂ) (hH : ∀ u v, conj (H u v) = H v u)
  (h_int : ∀ l m : L, ∃ n : ℤ, (H l m).im = n) (α : L → Circle)
  (hα : ∀ (l m : L) (n : ℤ), (H l m).im = n → (α (l + m) : ℂ) = (-1) ^ n * α l * α m)

/-- The form of the datum of a Hermitian form `H` is `B (u, z) = π H (z, u)`. -/
@[simp]
theorem form_ofHermitian_apply (u z : V) :
    (ofHermitian H hH h_int α hα).form u z = π * H z u := (rfl)

/-- The semicharacter of the datum of a Hermitian form is the given `α`. -/
@[simp]
theorem semichar_ofHermitian : (ofHermitian H hH h_int α hα).semichar = α := (rfl)

/-- The Riemann form of the datum of a Hermitian form `H` is `Im H`. -/
@[simp]
theorem riemannForm_ofHermitian_apply (u v : V) :
    (ofHermitian H hH h_int α hα).riemannForm u v = (H u v).im := by
  rw [riemannForm_apply, form_ofHermitian_apply, form_ofHermitian_apply, ← hH u v]
  simp only [Complex.sub_im, Complex.im_ofReal_mul, Complex.conj_im]
  field_simp
  ring

/-- **The factor of automorphy of a Hermitian datum** is the classical
`α (l) exp (π H (z, l) + π H (l, l) / 2)`. -/
@[simp]
theorem factor_ofHermitian (l : L) (z : V) :
    (ofHermitian H hH h_int α hα).factor l z = α l * exp (π * H z l + π * H l l / 2) := by
  rw [factor_def, form_ofHermitian_apply, form_ofHermitian_apply, semichar_ofHermitian]

end AppellHumbertData

end TauCeti
