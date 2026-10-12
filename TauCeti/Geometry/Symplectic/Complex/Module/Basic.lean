/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.Module

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
structure induced from `ofComplexModule` recovers the original complex module structure.

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
* `TauCeti.AlmostComplexStructure.complexModule_ofComplexModule`: the opposite round trip
  recovers the original complex module structure.
-/

public section

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*}

section ToComplex

variable [AddCommGroup V] [Module ℝ V]

/-- The complex vector space structure on a real module `V` induced by an almost complex
structure `J`: the scalar `a + b·i` acts as `a • v + b • J v`.

This is a `def` rather than an instance because the complex structure is not canonical: it depends
on the chosen `J`. It uses `Complex.liftAux` to extend the real scalars through the endomorphism
algebra. Restricted to the real scalars it is the original `Module ℝ V`
(`complexModule_isScalarTower`, `complexModule_ofReal_smul`). -/
@[implicit_reducible]
def complexModule (J : AlmostComplexStructure V) : Module ℂ V :=
  Module.compHom V (Complex.liftAux J.toLinearMap (by
    simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id] using J.square_neg)).toRingHom

/-- The defining formula for the complex action induced by an almost complex structure. -/
@[simp]
lemma complexModule_smul_def (J : AlmostComplexStructure V) (z : ℂ) (v : V) :
    letI := J.complexModule
    z • v = z.re • v + z.im • J v := by
  let := J.complexModule
  rw [MulAction.compHom_smul_def, Module.End.smul_def]
  exact congrArg (fun f : Module.End ℝ V => f v) (Complex.liftAux_apply J.toLinearMap _ z)

/-- In the induced complex structure, multiplication by `i` is `J`. -/
lemma complexModule_I_smul (J : AlmostComplexStructure V) (v : V) :
    letI := J.complexModule
    Complex.I • v = J v := by
  let := J.complexModule
  simp

/-- The induced complex action restricts along `ℝ → ℂ` to the original real action. -/
lemma complexModule_ofReal_smul (J : AlmostComplexStructure V) (r : ℝ) (v : V) :
    letI := J.complexModule
    (r : ℂ) • v = r • v := by
  let := J.complexModule
  simp

/-- `ℝ`, `ℂ`, and `V` form a scalar tower for the induced complex structure: the real scalars act
the same whether through `ℝ` or through `ℂ`. -/
lemma complexModule_isScalarTower (J : AlmostComplexStructure V) :
    letI := J.complexModule
    IsScalarTower ℝ ℂ V := by
  let := J.complexModule
  exact IsScalarTower.of_algebraMap_smul fun r v => by
    simpa only [Complex.coe_algebraMap] using J.complexModule_ofReal_smul r v

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

/-- The almost complex structure read from a complex module acts by multiplication by `i`. -/
@[simp]
lemma ofComplexModule_apply (v : V) : ofComplexModule V v = Complex.I • v :=
  (rfl)

end OfComplex

/-- Reading the almost complex structure back off the induced complex module recovers `J`. -/
@[simp]
lemma ofComplexModule_complexModule {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : AlmostComplexStructure V) :
    letI := J.complexModule
    letI := J.complexModule_isScalarTower
    ofComplexModule V = J := by
  let := J.complexModule
  let := J.complexModule_isScalarTower
  refine AlmostComplexStructure.ext fun v => ?_
  rw [ofComplexModule_apply, complexModule_I_smul]

/-- The complex module induced by `ofComplexModule` is the original module structure. -/
@[simp]
lemma complexModule_ofComplexModule {V : Type*}
    [AddCommGroup V] [Module ℝ V] [m : Module ℂ V] [IsScalarTower ℝ ℂ V] :
    (ofComplexModule V).complexModule = m := by
  apply Module.ext
  funext z v
  exact ((ofComplexModule V).complexModule_smul_def z v).trans (by
    rw [ofComplexModule_apply, Complex.re_smul_add_im_smul]
    rfl)

end AlmostComplexStructure

end TauCeti
