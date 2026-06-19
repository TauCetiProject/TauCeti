/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Almost complex structures as complex module structures

A pointwise almost complex structure `J` on a real module `V` (a real-linear endomorphism with
`J ∘ J = -1`, from `TauCeti.AlmostComplexStructure`) is the same data as a complex vector space
structure on `V` extending the real one: scalar multiplication by `a + b·i` is `a • v + b • J v`,
and conversely multiplication by `i` recovers `J`. This file makes that classical correspondence
(McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1) precise.

The forward direction `AlmostComplexStructure.complexModule` turns `J` into a `Module ℂ V`; it is
deliberately a `def`, not an instance, because the complex structure depends on the chosen `J` and
is not canonical. The backward direction `AlmostComplexStructure.ofComplexModule` reads an almost
complex structure off any complex module structure compatible with the real scalars. The round-trip
lemmas say that `ofComplexModule` applied to `complexModule J` returns `J`, and that the module
structure induced from `ofComplexModule` recovers the original complex scalar action.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexModule`: the `Module ℂ V` with
  `(a + b·i) • v = a • v + b • J v`.
* `TauCeti.AlmostComplexStructure.complexModule_smul_def`: the defining scalar action.
* `TauCeti.AlmostComplexStructure.complexModule_I_smul`: `i • v = J v` in the induced module.
* `TauCeti.AlmostComplexStructure.complexModule_ofReal_smul`: the induced action restricts to the
  original real action.
* `TauCeti.AlmostComplexStructure.complexModule_isScalarTower`: `ℝ`, `ℂ`, `V` form a scalar tower.
* `TauCeti.AlmostComplexStructure.ofComplexModule`: the almost complex structure `v ↦ i • v` on a
  complex module.
* `TauCeti.AlmostComplexStructure.ofComplexModule_complexModule`: the round trip recovers `J`.
* `TauCeti.AlmostComplexStructure.complexModule_ofComplexModule_smul`: the opposite round trip
  recovers the original complex scalar action.
-/

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*}

section ToComplex

variable [AddCommGroup V] [Module ℝ V]

/-- The complex vector space structure on a real module `V` induced by an almost complex
structure `J`: the scalar `a + b·i` acts as `a • v + b • J v`.

This is a `def` rather than an instance because the complex structure is not canonical: it depends
on the chosen `J`. Restricted to the real scalars it is the original `Module ℝ V`
(`complexModule_isScalarTower`, `complexModule_ofReal_smul`). -/
@[implicit_reducible]
def complexModule (J : AlmostComplexStructure V) : Module ℂ V where
  __ := Module.compHom V (Complex.liftAux J.toLinearMap (by
    ext v
    simp [Module.End.mul_apply, J.apply_apply])).toRingHom

/-- The defining formula for the complex action induced by an almost complex structure. -/
lemma complexModule_smul_def (J : AlmostComplexStructure V) (z : ℂ) (v : V) :
    letI := J.complexModule
    z • v = z.re • v + z.im • J v :=
  by
  letI := J.complexModule
  rw [show z • v = (Complex.liftAux J.toLinearMap (by
    ext v
    simp [Module.End.mul_apply, J.apply_apply]) z) v from rfl]
  rw [Complex.liftAux_apply]
  rfl

/-- In the induced complex structure, multiplication by `i` is `J`. -/
@[simp]
lemma complexModule_I_smul (J : AlmostComplexStructure V) (v : V) :
    letI := J.complexModule
    (Complex.I) • v = J v := by
  letI := J.complexModule
  rw [complexModule_smul_def, Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_add]

/-- The induced complex action restricts along `ℝ → ℂ` to the original real action. -/
@[simp]
lemma complexModule_ofReal_smul (J : AlmostComplexStructure V) (r : ℝ) (v : V) :
    letI := J.complexModule
    (r : ℂ) • v = r • v := by
  letI := J.complexModule
  rw [complexModule_smul_def, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- `ℝ`, `ℂ`, and `V` form a scalar tower for the induced complex structure: the real scalars act
the same whether through `ℝ` or through `ℂ`. -/
lemma complexModule_isScalarTower (J : AlmostComplexStructure V) :
    letI := J.complexModule
    IsScalarTower ℝ ℂ V := by
  letI := J.complexModule
  refine ⟨fun a b v => ?_⟩
  rw [complexModule_smul_def, complexModule_smul_def, Complex.smul_re, Complex.smul_im]
  simp only [smul_eq_mul]
  module

end ToComplex

section OfComplex

variable [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

/-- The almost complex structure `v ↦ i • v` on a complex module whose real scalars are compatible
with the ambient real structure. This is the inverse construction to `complexModule`. -/
def ofComplexModule (V : Type*) [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    AlmostComplexStructure V where
  toLinearMap := (LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ
  square_neg := by
    ext v
    simp [smul_smul, Complex.I_mul_I]

@[simp]
lemma ofComplexModule_apply (v : V) : ofComplexModule V v = Complex.I • v :=
  rfl

end OfComplex

/-- Reading the almost complex structure back off the induced complex module recovers `J`. -/
lemma ofComplexModule_complexModule {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : AlmostComplexStructure V) :
    letI := J.complexModule
    letI := J.complexModule_isScalarTower
    ofComplexModule V = J := by
  letI := J.complexModule
  letI := J.complexModule_isScalarTower
  refine AlmostComplexStructure.ext fun v => ?_
  rw [ofComplexModule_apply, complexModule_I_smul]

/-- The complex module induced by `ofComplexModule` has the original complex scalar action. -/
lemma complexModule_ofComplexModule_smul {V : Type*}
    [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (z : ℂ) (v : V) :
    let smul₀ : ℂ → V → V := (· • ·)
    letI := (ofComplexModule V).complexModule
    z • v = smul₀ z v := by
  let smul₀ : ℂ → V → V := (· • ·)
  have coe_smul' (r : ℝ) (w : V) : (r : ℂ) • w = r • w := by
    have h := smul_assoc r (1 : ℂ) w
    simp only [one_smul, Algebra.smul_def, mul_one] at h
    exact h
  have hdecomp : z.re • v + z.im • smul₀ Complex.I v = smul₀ z v := by
    dsimp only [smul₀]
    rw [← Complex.re_add_im z]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, Complex.I_im,
      add_zero, zero_add, mul_one]
    conv_rhs => rw [add_smul, mul_smul, coe_smul', coe_smul']
  letI := (ofComplexModule V).complexModule
  rw [complexModule_smul_def]
  dsimp only [ofComplexModule]
  simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  exact hdecomp

end AlmostComplexStructure

end TauCeti
