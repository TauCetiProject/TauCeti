/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Flat scalar extension of fixed Lie subalgebras

The tensor extension of the fixed subalgebra maps into the fixed subalgebra of the
extended endomorphism. Mathlib's flat tensor equalizer theorem makes this comparison
an equivalence over a flat coefficient algebra. Both the comparison and its inverse
are natural under intertwining maps.

Flatness is essential: negation on the zero-bracket Lie algebra `ℤ` has no nonzero
fixed element, whereas after extension to `ZMod 2` every element is fixed.
-/

public section

open TensorProduct

variable {R L M : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  (S : Type*) [CommRing S] [Algebra R S]

namespace LieHom

variable (f : L →ₗ⁅R⁆ L)

private def fixedSubalgebraTensorEquiv :
    S ⊗[R] f.fixedSubalgebra ≃ₗ[S] S ⊗[R] LinearMap.eqLocus f.toLinearMap LinearMap.id :=
  LinearEquiv.baseChange R S _ _
    (LinearEquiv.ofEq _ _ (fixedSubalgebra_toSubmodule_eq_eqLocus f))

/-- The equalizer of the extended endomorphism and the identity is the fixed subalgebra of the
extended endomorphism. -/
private theorem eqLocus_baseChange :
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S S f.toLinearMap)
      (AlgebraTensorModule.lTensor S S (LinearMap.id : L →ₗ[R] L)) =
        (f.baseChange S).fixedSubalgebra.toSubmodule := by
  rw [fixedSubalgebra_toSubmodule_eq_eqLocus, coe_baseChange,
    AlgebraTensorModule.lTensor_eq_baseChange S f.toLinearMap, AlgebraTensorModule.lTensor_id]

/-- Extended fixed elements are fixed by the extended endomorphism. -/
private theorem baseChange_incl_mem_fixedSubalgebra (x : S ⊗[R] f.fixedSubalgebra) :
    f.fixedSubalgebra.incl.baseChange S x ∈ (f.baseChange S).fixedSubalgebra := by
  rw [mem_fixedSubalgebra, ← comp_apply, ← baseChange_comp, comp_incl_fixedSubalgebra]

/-- The canonical map from extended fixed elements to fixed extended elements: the extended
inclusion, with its codomain restricted. -/
def fixedBaseChange :
    S ⊗[R] f.fixedSubalgebra →ₗ⁅S⁆ (f.baseChange S).fixedSubalgebra where
  __ := (f.fixedSubalgebra.incl.baseChange S).toLinearMap.codRestrict
    (f.baseChange S).fixedSubalgebra.toSubmodule fun x =>
      (LieSubalgebra.mem_toSubmodule _).mpr (baseChange_incl_mem_fixedSubalgebra S f x)
  map_lie' {x y} := Subtype.ext ((f.fixedSubalgebra.incl.baseChange S).map_lie x y)

@[simp]
theorem coe_fixedBaseChange (x : S ⊗[R] f.fixedSubalgebra) :
    (fixedBaseChange S f x : S ⊗[R] L) = f.fixedSubalgebra.incl.baseChange S x := by
  rfl

theorem fixedBaseChange_tmul (s : S) (x : f.fixedSubalgebra) :
    (fixedBaseChange S f (s ⊗ₜ[R] x) : S ⊗[R] L) = s ⊗ₜ[R] (x : L) := by
  simp [coe_fixedBaseChange]

/-- Mathlib's flat equalizer equivalence, transported to the fixed subalgebras. -/
private noncomputable def fixedBaseChangeLinearEquiv [Module.Flat R S] :
    S ⊗[R] f.fixedSubalgebra ≃ₗ[S] (f.baseChange S).fixedSubalgebra.toSubmodule :=
  (fixedSubalgebraTensorEquiv S f).trans
    ((LinearMap.tensorEqLocusEquiv S S f.toLinearMap LinearMap.id).trans
      (LinearEquiv.ofEq _ _ (eqLocus_baseChange S f)))

/-- The flat equalizer equivalence agrees with the canonical comparison. -/
private theorem coe_fixedBaseChangeLinearEquiv [Module.Flat R S]
    (x : S ⊗[R] f.fixedSubalgebra) :
    (fixedBaseChangeLinearEquiv S f x : S ⊗[R] L) = fixedBaseChange S f x := by
  induction x with
  | tmul s x =>
    simp only [fixedBaseChangeLinearEquiv, fixedSubalgebraTensorEquiv, LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul, LinearMap.tensorEqLocusEquiv_apply, LinearEquiv.coe_ofEq_apply,
      LinearMap.tensorEqLocus_tmul, coe_fixedBaseChange, baseChange_tmul, LieSubalgebra.coe_incl]
    -- `LinearEquiv.coe_ofEq_apply` applies only up to unfolding the `SetLike` instances: `x` is
    -- read in the Lie subalgebra on the right and in its underlying submodule on the left.
    exact congrArg (s ⊗ₜ[R] ·) (LinearEquiv.coe_ofEq_apply _ x)
  | add x y hx hy => simp [hx, hy]

private theorem fixedBaseChange_bijective [Module.Flat R S] :
    Function.Bijective (fixedBaseChange S f) :=
  ⟨fun x y hxy => (fixedBaseChangeLinearEquiv S f).injective (Subtype.ext (by
      rw [coe_fixedBaseChangeLinearEquiv, coe_fixedBaseChangeLinearEquiv, hxy])),
    fun y => ⟨(fixedBaseChangeLinearEquiv S f).symm
      ⟨y, (LieSubalgebra.mem_toSubmodule _).mpr y.property⟩, Subtype.ext (by
        rw [← coe_fixedBaseChangeLinearEquiv, LinearEquiv.apply_symm_apply])⟩⟩

/-- Fixed Lie subalgebras commute with flat scalar extension. -/
noncomputable def fixedBaseChangeEquiv [Module.Flat R S] :
    S ⊗[R] f.fixedSubalgebra ≃ₗ⁅S⁆ (f.baseChange S).fixedSubalgebra :=
  LieEquiv.ofBijective (fixedBaseChange S f) (by exact fixedBaseChange_bijective S f)

@[simp]
theorem fixedBaseChangeEquiv_apply [Module.Flat R S] (x : S ⊗[R] f.fixedSubalgebra) :
    fixedBaseChangeEquiv S f x = fixedBaseChange S f x := by
  rfl

/-- The inverse comparison undoes the comparison map. -/
@[simp]
theorem fixedBaseChangeEquiv_symm_fixedBaseChange [Module.Flat R S]
    (x : S ⊗[R] f.fixedSubalgebra) :
    (fixedBaseChangeEquiv S f).symm (fixedBaseChange S f x) = x := by
  rw [← fixedBaseChangeEquiv_apply, LieEquiv.symm_apply_apply]

/-- The comparison map undoes the inverse comparison. -/
@[simp]
theorem fixedBaseChange_fixedBaseChangeEquiv_symm [Module.Flat R S]
    (y : (f.baseChange S).fixedSubalgebra) :
    fixedBaseChange S f ((fixedBaseChangeEquiv S f).symm y) = y := by
  rw [← fixedBaseChangeEquiv_apply, LieEquiv.apply_symm_apply]

/-- The inverse comparison still maps to the given element under the extended inclusion. -/
@[simp]
theorem baseChange_incl_fixedBaseChangeEquiv_symm [Module.Flat R S]
    (x : (f.baseChange S).fixedSubalgebra) :
    f.fixedSubalgebra.incl.baseChange S ((fixedBaseChangeEquiv S f).symm x) = x := by
  rw [← coe_fixedBaseChange, ← fixedBaseChangeEquiv_apply, LieEquiv.apply_symm_apply]

variable {f} {g : M →ₗ⁅R⁆ M} (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f)

/-- The fixed-subalgebra comparison is natural under intertwining maps. -/
theorem fixedBaseChange_natural :
    (fixedBaseChange S g).comp ((restrictFixed u h).baseChange S) =
      (restrictFixed (u.baseChange S) (baseChange_intertwines S u h)).comp
        (fixedBaseChange S f) := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  induction x with
  | tmul s x => simp [LieHom.comp_apply]
  | add x y hx hy => simp_all

/-- The inverses of the flat comparison equivalences form the reverse naturality square. -/
theorem fixedBaseChangeEquiv_symm_natural [Module.Flat R S]
    (x : (f.baseChange S).fixedSubalgebra) :
    (restrictFixed u h).baseChange S ((fixedBaseChangeEquiv S f).symm x) =
      (fixedBaseChangeEquiv S g).symm
        (restrictFixed (u.baseChange S) (baseChange_intertwines S u h) x) := by
  apply (LieEquiv.eq_symm_apply _).2
  simpa only [LieHom.comp_apply, ← fixedBaseChangeEquiv_apply, LieEquiv.apply_symm_apply]
    using congr_fun (fixedBaseChange_natural S u h) ((fixedBaseChangeEquiv S f).symm x)

end LieHom
