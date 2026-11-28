/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.OreExtension.Basic

/-!
# Modules over a skew polynomial ring from semilinear endomorphisms

Let `σ` be an endomorphism of a ring `R` and let `R[X; σ]` be the skew polynomial ring, the Ore
extension `TauCeti.OreExtension σ 0` with `X * a = σ a * X`. A left `R[X; σ]`-module is the same
thing as an `R`-module `N` with a `σ`-semilinear endomorphism `F`, through which `X` acts. This
file builds the `R[X; σ]`-module structure from `F`, on the type synonym
`TauCeti.OreExtension.SkewModule F`.

## Main definitions

* `TauCeti.OreExtension.semilinearEndHom σ F`: the action of `R[X; σ]` on `N` in which `X` acts
  by `F`, as a ring homomorphism to the additive endomorphisms of `N`.
* `TauCeti.OreExtension.SkewModule F`: an `R`-module `N`, as an `R[X; σ]`-module in which `X`
  acts by a `σ`-semilinear map `F`.
-/

public section

noncomputable section

namespace TauCeti.OreExtension

universe u v

variable {k : Type u} {R : Type v} [CommSemiring k] [Ring R] [Algebra k R] (σ : R →ₐ[k] R)
  {N : Type*} [AddCommGroup N] [Module R N] (F : N →ₛₗ[(σ : R →+* R)] N)

/-- The action of the skew polynomial ring `R[X; σ]` on an `R`-module `N` in which `X` acts by the
`σ`-semilinear map `F`, as a ring homomorphism to the additive endomorphisms of `N`. -/
def semilinearEndHom : OreExtension σ 0 →+* Module.End ℤ N :=
  lift (Module.toModuleEnd ℤ N) F.toAddMonoidHom.toIntLinearMap fun a ↦ LinearMap.ext fun n ↦ by
    simp [SigmaDerivation.coe_zero]

/-- The constants act through the `R`-module structure. -/
@[simp]
theorem semilinearEndHom_C (a : R) (n : N) : semilinearEndHom σ F (C a) n = a • n := by
  simp [semilinearEndHom]

/-- The variable acts by `F`. -/
@[simp]
theorem semilinearEndHom_X (n : N) : semilinearEndHom σ F X n = F n := by
  simp [semilinearEndHom]

variable {σ}

/-- A type synonym for an `R`-module `N` with a `σ`-semilinear endomorphism `F`, regarded as a left
module over the skew polynomial ring `R[X; σ]` in which `X` acts by `F` and the constants act
through `R`. -/
@[expose]
def SkewModule (_F : N →ₛₗ[(σ : R →+* R)] N) : Type _ :=
  N

namespace SkewModule

instance : AddCommGroup (SkewModule F) :=
  inferInstanceAs (AddCommGroup N)

instance : Module (OreExtension σ 0) (SkewModule F) :=
  Module.compHom N (semilinearEndHom σ F)

/-- The identification of `N` with the skew module `SkewModule F`. -/
def of : N ≃+ SkewModule F :=
  AddEquiv.refl N

/-- `R[X; σ]` acts on `SkewModule F` through `semilinearEndHom σ F`. -/
theorem smul_of (p : OreExtension σ 0) (n : N) : p • of F n = of F (semilinearEndHom σ F p n) :=
  (rfl)

/-- The constants act on `SkewModule F` through the `R`-module structure of `N`. -/
@[simp]
theorem C_smul_of (a : R) (n : N) : (C a : OreExtension σ 0) • of F n = of F (a • n) :=
  congrArg (of F) (semilinearEndHom_C σ F a n)

/-- The variable acts on `SkewModule F` by `F`. -/
@[simp]
theorem X_smul_of (n : N) : (X : OreExtension σ 0) • of F n = of F (F n) :=
  congrArg (of F) (semilinearEndHom_X σ F n)

/-- `X - 1` acts on `SkewModule F` by `F - 1`. -/
@[simp]
theorem X_sub_one_smul_of (n : N) : (X - 1 : OreExtension σ 0) • of F n = of F (F n - n) := by
  rw [sub_smul, one_smul, X_smul_of, map_sub]

end SkewModule

end TauCeti.OreExtension
