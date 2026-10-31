/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.FixedSubalgebra.Basic

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
    (LinearEquiv.ofEq _ _ (fixedSubalgebra_eq_eqLocus f))

private theorem eqLocus_baseChange :
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S S f.toLinearMap)
      (AlgebraTensorModule.lTensor S S (LinearMap.id : L →ₗ[R] L)) =
        (f.baseChange S).fixedSubalgebra.toSubmodule := by
  rw [fixedSubalgebra_eq_eqLocus, coe_baseChange]
  exact congrArg (LinearMap.eqLocus (LinearMap.baseChange S f.toLinearMap))
    (LinearMap.baseChange_id (R := R) (A := S) (M := L))

private def fixedBaseChangeLinearMap :
    S ⊗[R] f.fixedSubalgebra →ₗ[S] (f.baseChange S).fixedSubalgebra :=
  (LinearEquiv.ofEq _ _ (eqLocus_baseChange S f)).toLinearMap.comp
    ((LinearMap.tensorEqLocus S S f.toLinearMap LinearMap.id).comp
      (fixedSubalgebraTensorEquiv S f).toLinearMap)

private theorem coe_fixedBaseChangeLinearMap (x : S ⊗[R] f.fixedSubalgebra) :
    (fixedBaseChangeLinearMap S f x : S ⊗[R] L) =
      f.fixedSubalgebra.incl.baseChange S x := by
  induction x with
  | tmul s x =>
      simp [fixedBaseChangeLinearMap, fixedSubalgebraTensorEquiv]
      rfl
  | add x y hx hy => simp [hx, hy]

/-- The canonical map from extended fixed elements to fixed extended elements. -/
def fixedBaseChange :
    S ⊗[R] f.fixedSubalgebra →ₗ⁅S⁆ (f.baseChange S).fixedSubalgebra where
  __ := fixedBaseChangeLinearMap S f
  map_lie' {x y} := Subtype.ext (calc
    (fixedBaseChangeLinearMap S f ⁅x, y⁆ : S ⊗[R] L) =
        f.fixedSubalgebra.incl.baseChange S ⁅x, y⁆ := coe_fixedBaseChangeLinearMap S f _
    _ = ⁅f.fixedSubalgebra.incl.baseChange S x, f.fixedSubalgebra.incl.baseChange S y⁆ :=
      (f.fixedSubalgebra.incl.baseChange S).map_lie x y
    _ = ⁅(fixedBaseChangeLinearMap S f x : S ⊗[R] L),
        (fixedBaseChangeLinearMap S f y : S ⊗[R] L)⁆ := by
      rw [coe_fixedBaseChangeLinearMap, coe_fixedBaseChangeLinearMap])

@[simp]
theorem coe_fixedBaseChange (x : S ⊗[R] f.fixedSubalgebra) :
    (fixedBaseChange S f x : S ⊗[R] L) = f.fixedSubalgebra.incl.baseChange S x :=
  coe_fixedBaseChangeLinearMap S f x

theorem fixedBaseChange_tmul (s : S) (x : f.fixedSubalgebra) :
    (fixedBaseChange S f (s ⊗ₜ[R] x) : S ⊗[R] L) = s ⊗ₜ[R] (x : L) := by
  simp [coe_fixedBaseChange]

private theorem fixedBaseChange_bijective [Module.Flat R S] :
    Function.Bijective (fixedBaseChange S f) := by
  let e := (fixedSubalgebraTensorEquiv S f).trans
    ((LinearMap.tensorEqLocusEquiv S S f.toLinearMap LinearMap.id).trans
      (LinearEquiv.ofEq _ _ (eqLocus_baseChange S f)))
  have he (x : S ⊗[R] f.fixedSubalgebra) : e x = fixedBaseChange S f x := by
    simp only [e, LinearEquiv.trans_apply, LinearMap.tensorEqLocusEquiv_apply]
    rfl
  exact (funext he) ▸ e.bijective

/-- Fixed Lie subalgebras commute with flat scalar extension. -/
noncomputable def fixedBaseChangeEquiv [Module.Flat R S] :
    S ⊗[R] f.fixedSubalgebra ≃ₗ⁅S⁆ (f.baseChange S).fixedSubalgebra :=
  LieEquiv.ofBijective (fixedBaseChange S f) (by exact fixedBaseChange_bijective S f)

@[simp]
theorem fixedBaseChangeEquiv_apply [Module.Flat R S] (x : S ⊗[R] f.fixedSubalgebra) :
    fixedBaseChangeEquiv S f x = fixedBaseChange S f x := by
  rfl

/-- The inverse comparison still maps to the given element under the extended inclusion. -/
@[simp]
theorem incl_fixedBaseChangeEquiv_symm [Module.Flat R S]
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
