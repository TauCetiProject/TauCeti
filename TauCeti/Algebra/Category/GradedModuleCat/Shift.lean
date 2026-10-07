/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic

/-!
# Integer powers of the grading shift

The integer powers of the grading-shift autoequivalence agree, up to natural isomorphism, with
the explicit internal shifts `M{d}`. This comparison lets graded Hom computations made using
the pieces `(M{d})ₚ = M_{p-d}` enter graded Ext and Euler characteristics, which use powers of
an autoequivalence. No finiteness or projectivity assumptions are required.

## References

* Năstăsescu--Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

/-- The internal shift by zero is naturally isomorphic to the identity functor. -/
def shiftFunctorZeroIso : shiftFunctor (𝒜 := 𝒜) 0 ≅ 𝟭 (GradedModuleCat.{v} 𝒜) :=
  NatIso.ofComponents (fun M ↦ isoMk (LinearEquiv.refl A M) fun p x ↦ by simp; rfl)
    fun _ ↦ by ext; rfl

@[simp]
theorem hom_shiftFunctorZeroIso_hom_app (M : GradedModuleCat.{v} 𝒜) :
    ((shiftFunctorZeroIso 𝒜).hom.app M).hom = LinearMap.id :=
  (rfl)

@[simp]
theorem hom_shiftFunctorZeroIso_inv_app (M : GradedModuleCat.{v} 𝒜) :
    ((shiftFunctorZeroIso 𝒜).inv.app M).hom = LinearMap.id :=
  (rfl)

/-- Successive internal shifts add their amounts; the comparison preserves the underlying
linear maps. -/
def shiftFunctorAddIso (a b : ℤ) :
    shiftFunctor (𝒜 := 𝒜) a ⋙ shiftFunctor b ≅ shiftFunctor (a + b) :=
  NatIso.ofComponents (fun M ↦ isoMk (LinearEquiv.refl A M) fun p x ↦ by
    simp [add_comm]; rfl) fun _ ↦ by ext; rfl

@[simp]
theorem hom_shiftFunctorAddIso_hom_app (a b : ℤ) (M : GradedModuleCat.{v} 𝒜) :
    ((shiftFunctorAddIso 𝒜 a b).hom.app M).hom = LinearMap.id :=
  (rfl)

@[simp]
theorem hom_shiftFunctorAddIso_inv_app (a b : ℤ) (M : GradedModuleCat.{v} 𝒜) :
    ((shiftFunctorAddIso 𝒜 a b).inv.app M).hom = LinearMap.id :=
  (rfl)

private def shiftPowNatIso : ∀ n : ℕ,
    ((shift 𝒜).powNat n).functor ≅ shiftFunctor (𝒜 := 𝒜) n
  | 0 => (shiftFunctorZeroIso 𝒜).symm
  | 1 => Iso.refl _
  | n + 2 =>
    Functor.isoWhiskerLeft _ (shiftPowNatIso (n + 1)) ≪≫
      shiftFunctorAddIso 𝒜 1 ((n + 1 : ℕ) : ℤ) ≪≫
        eqToIso (congrArg (shiftFunctor (𝒜 := 𝒜))
          (by omega : 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ)))

private def shiftInversePowNatIso : ∀ n : ℕ,
    ((shift 𝒜).symm.powNat n).functor ≅ shiftFunctor (𝒜 := 𝒜) (-(n : ℤ))
  | 0 => (shiftFunctorZeroIso 𝒜).symm
  | 1 => Iso.refl _
  | n + 2 =>
    Functor.isoWhiskerLeft _ (shiftInversePowNatIso (n + 1)) ≪≫
      shiftFunctorAddIso 𝒜 (-1) (-((n + 1 : ℕ) : ℤ)) ≪≫
        eqToIso (congrArg (shiftFunctor (𝒜 := 𝒜))
          (by omega : -1 + -((n + 1 : ℕ) : ℤ) = -((n + 2 : ℕ) : ℤ)))

/-- The `d`-th integer power of the grading-shift autoequivalence is the explicit internal
shift by `d`. Its components compare the same graded module with two presentations of its
shifted grading. -/
def shiftPowIso : ∀ d : ℤ, ((shift 𝒜) ^ d).functor ≅ shiftFunctor (𝒜 := 𝒜) d
  | Int.ofNat n => shiftPowNatIso 𝒜 n
  | Int.negSucc n => shiftInversePowNatIso 𝒜 (n + 1)

/-- Morphisms into the categorical `d`-th power of the grading shift are linearly equivalent to
morphisms into the explicit internal shift by `d`. -/
def homShiftPowEquiv (P M : GradedModuleCat.{v} 𝒜) (d : ℤ) :
    (P ⟶ ((shift 𝒜) ^ d).functor.obj M) ≃ₗ[k] (P ⟶ M.shiftObj d) :=
  Linear.homCongr k (Iso.refl P) ((shiftPowIso 𝒜 d).app M)

@[simp]
theorem homShiftPowEquiv_apply (P M : GradedModuleCat.{v} 𝒜) (d : ℤ)
    (f : P ⟶ ((shift 𝒜) ^ d).functor.obj M) :
    homShiftPowEquiv 𝒜 P M d f = f ≫ (shiftPowIso 𝒜 d).hom.app M := by
  rw [homShiftPowEquiv]
  exact (Linear.homCongr_apply k _ _ f).trans (by simp)

@[simp]
theorem homShiftPowEquiv_symm_apply (P M : GradedModuleCat.{v} 𝒜) (d : ℤ)
    (f : P ⟶ M.shiftObj d) :
    (homShiftPowEquiv 𝒜 P M d).symm f = f ≫ (shiftPowIso 𝒜 d).inv.app M := by
  rw [homShiftPowEquiv]
  exact (Linear.homCongr_symm_apply k _ _ f).trans (by simp)

end TauCeti.GradedModuleCat
