/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Extension of scalars and exterior powers

Exterior powers commute with extension of scalars along an arbitrary map of commutative rings.
This file packages `TauCeti.exteriorPower.equivBaseChange` as a natural isomorphism of module
functors. Its forward map sends a scalar tensored with a wedge to the scalar multiple of the
wedge of the base-changed vectors. This is the module calculation for pullback of exterior
powers of quasicoherent sheaves on affine schemes.

## References

* The Stacks Project, Lemma 10.13.6 (Tag 0C6F).
-/

public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace TauCeti

universe u

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Exterior powers commute with extension of scalars, without a flatness or finiteness
assumption. -/
def extendScalarsExteriorPowerIso (n : ℕ) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj (M.exteriorPower n) ≅
      ((ModuleCat.extendScalars f).obj M).exteriorPower n := by
  let _ := f.toAlgebra
  exact (exteriorPower.equivBaseChange S n (M := M)).symm.toModuleIso

/-- The forward comparison on a pure tensor with a decomposable wedge. -/
@[simp]
theorem extendScalarsExteriorPowerIso_hom_tmul_mk (n : ℕ) (M : ModuleCat.{u} R)
    (s : S) (m : Fin n → M) :
    (extendScalarsExteriorPowerIso f n M).hom (s ⊗ₜ[R,f] ModuleCat.exteriorPower.mk m) =
      s • ModuleCat.exteriorPower.mk
        (M := (ModuleCat.extendScalars f).obj M) (fun i ↦ (1 : S) ⊗ₜ[R,f] m i) := by
  let _ := f.toAlgebra
  -- Identify the category's pure tensors with the tensors for `f.toAlgebra` before
  -- applying the underlying linear-equivalence formula.
  change (exteriorPower.equivBaseChange S n (M := M)).symm
    (s ⊗ₜ[R] _root_.exteriorPower.ιMulti R n m) = _
  exact exteriorPower.equivBaseChange_symm_tmul_ιMulti S s m

/-- The inverse comparison on a wedge of pure tensors. -/
@[simp]
theorem extendScalarsExteriorPowerIso_inv_mk_tmul (n : ℕ) (M : ModuleCat.{u} R)
    (s : Fin n → S) (m : Fin n → M) :
    (extendScalarsExteriorPowerIso f n M).inv
        (ModuleCat.exteriorPower.mk
          (M := (ModuleCat.extendScalars f).obj M) (fun i ↦ s i ⊗ₜ[R,f] m i)) =
      (∏ i, s i) ⊗ₜ[R,f] ModuleCat.exteriorPower.mk m := by
  let _ := f.toAlgebra
  -- Unwrap the categorical isomorphism to use the underlying wedge formula.
  change exteriorPower.equivBaseChange S n (M := M)
    (_root_.exteriorPower.ιMulti S n (fun i ↦ s i ⊗ₜ[R] m i)) = _
  exact exteriorPower.equivBaseChange_ιMulti_tmul S s m

/-- The scalar-extension comparison is natural in the module. -/
@[reassoc]
theorem extendScalarsExteriorPowerIso_hom_naturality (n : ℕ)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars f).map (ModuleCat.exteriorPower.map g n) ≫
        (extendScalarsExteriorPowerIso f n N).hom =
      (extendScalarsExteriorPowerIso f n M).hom ≫
        ModuleCat.exteriorPower.map ((ModuleCat.extendScalars f).map g) n := by
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
  apply ModuleCat.exteriorPower.hom_ext
  ext m
  simp only [ModuleCat.AlternatingMap.postcomp_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  -- The adjunction produces applications of `ConcreteCategory.hom`; use morphism
  -- applications here so that the tensor and wedge computation lemmas match directly.
  change (extendScalarsExteriorPowerIso f n N).hom
      ((ModuleCat.extendScalars f).map (ModuleCat.exteriorPower.map g n)
        ((1 : S) ⊗ₜ[R,f] ModuleCat.exteriorPower.mk m)) =
    ModuleCat.exteriorPower.map ((ModuleCat.extendScalars f).map g) n
      ((extendScalarsExteriorPowerIso f n M).hom
        ((1 : S) ⊗ₜ[R,f] ModuleCat.exteriorPower.mk m))
  simp only [ModuleCat.ExtendScalars.map_tmul, ModuleCat.exteriorPower.map_mk,
    extendScalarsExteriorPowerIso_hom_tmul_mk, one_smul]
  erw [extendScalarsExteriorPowerIso_hom_tmul_mk, ModuleCat.exteriorPower.map_mk]
  simp only [one_smul]
  congr 1

/-- The natural scalar-extension comparison for the `n`-th exterior power. -/
def extendScalarsExteriorPowerNatIso (n : ℕ) :
    ModuleCat.exteriorPower.functor R n ⋙ ModuleCat.extendScalars f ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.exteriorPower.functor S n :=
  NatIso.ofComponents (extendScalarsExteriorPowerIso f n)
    (fun g ↦ extendScalarsExteriorPowerIso_hom_naturality f n g)

/-- The forward components of the natural scalar-extension comparison. -/
@[simp]
theorem extendScalarsExteriorPowerNatIso_hom_app (n : ℕ) (M : ModuleCat.{u} R) :
    (extendScalarsExteriorPowerNatIso f n).hom.app M =
      (extendScalarsExteriorPowerIso f n M).hom :=
  (rfl)

/-- The inverse components of the natural scalar-extension comparison. -/
@[simp]
theorem extendScalarsExteriorPowerNatIso_inv_app (n : ℕ) (M : ModuleCat.{u} R) :
    (extendScalarsExteriorPowerNatIso f n).inv.app M =
      (extendScalarsExteriorPowerIso f n M).inv :=
  (rfl)

end

end TauCeti
