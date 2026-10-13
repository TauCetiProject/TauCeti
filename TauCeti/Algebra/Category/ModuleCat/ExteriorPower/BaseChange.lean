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

universe u₁ u₂ v

noncomputable section

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

/-- Exterior powers commute with extension of scalars, without a flatness or finiteness
assumption. -/
def extendScalarsExteriorPowerIso (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (ModuleCat.extendScalars f).obj (M.exteriorPower n) ≅
      ((ModuleCat.extendScalars f).obj M).exteriorPower n := by
  let _ := f.toAlgebra
  exact (exteriorPower.equivBaseChange S n (M := M)).symm.toModuleIso

/-- The forward comparison on a pure tensor with a decomposable wedge. -/
@[simp]
theorem extendScalarsExteriorPowerIso_hom_tmul_mk (n : ℕ) (M : ModuleCat.{max u₁ v} R)
    (s : S) (m : Fin n → M) :
    (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n M).hom (s ⊗ₜ[R,f] ModuleCat.exteriorPower.mk m) =
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
theorem extendScalarsExteriorPowerIso_inv_mk_tmul (n : ℕ) (M : ModuleCat.{max u₁ v} R)
    (s : Fin n → S) (m : Fin n → M) :
    (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n M).inv
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
    {M N : ModuleCat.{max u₁ v} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars f).map (ModuleCat.exteriorPower.map g n) ≫
        (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n N).hom =
      (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n M).hom ≫
        ModuleCat.exteriorPower.map ((ModuleCat.extendScalars f).map g) n := by
  let _ := f.toAlgebra
  apply (Iso.comp_inv_eq (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n N).symm).2
  rw [Category.assoc]
  apply (Iso.eq_inv_comp (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n M).symm).2
  apply ModuleCat.exteriorPower.hom_ext
  ext m
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.comp_apply,
    ModuleCat.exteriorPower.map_mk]
  -- Compute the exterior-power maps on wedges before applying linear naturality.
  -- `erw` identifies the categorical tensor object with the underlying tensor product.
  have h := (exteriorPower.equivBaseChange_map S n g.hom
    (_root_.exteriorPower.ιMulti S n m)).symm
  erw [_root_.exteriorPower.map_apply_ιMulti] at h
  exact h

/-- The natural scalar-extension comparison for the `n`-th exterior power. -/
def extendScalarsExteriorPowerNatIso (n : ℕ) :
    ModuleCat.exteriorPower.functor.{max u₁ v} R n ⋙
        ModuleCat.extendScalars.{u₁, u₂, max u₁ v} f ≅
      ModuleCat.extendScalars.{u₁, u₂, max u₁ v} f ⋙
        ModuleCat.exteriorPower.functor.{max u₁ u₂ v} S n :=
  NatIso.ofComponents (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n)
    (fun g ↦ extendScalarsExteriorPowerIso_hom_naturality.{u₁, u₂, v} f n g)

/-- The forward components of the natural scalar-extension comparison. -/
@[simp]
theorem extendScalarsExteriorPowerNatIso_hom_app (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (extendScalarsExteriorPowerNatIso.{u₁, u₂, v} f n).hom.app M =
      (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n M).hom :=
  (rfl)

/-- The inverse components of the natural scalar-extension comparison. -/
@[simp]
theorem extendScalarsExteriorPowerNatIso_inv_app (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (extendScalarsExteriorPowerNatIso.{u₁, u₂, v} f n).inv.app M =
      (extendScalarsExteriorPowerIso.{u₁, u₂, v} f n M).inv :=
  (rfl)

end

end TauCeti
