/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.RightAction
public import Mathlib.Algebra.Algebra.Basic
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import TauCeti.Algebra.Module.Dual.ProjectiveInjective

/-!
# Nakayama modules

The Nakayama construction sends a left `A`-module `P` to
`ν(P) = Hom_k(Hom_A(P, A), k)`. Both dualizations reverse arrows, so `ν` is covariant.
The left action is `(a • φ)(ψ) = φ(ψ · a)`, where the inner dual is a right `A`-module.
Finite projective modules go to injective modules when `k` is a field.

These modules are the injective terms obtained by dualizing a projective presentation when
computing the Auslander–Reiten translate. The type synonym keeps the domain action separate
from Mathlib's codomain action on linear maps. `NakayamaModule.equivDual` identifies the
underlying scalar module with the double dual, and `LinearMap.nakayamaMap` computes its maps.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.

The action uses `TauCeti.dualRightAction`; injectivity uses the opposite dual of a finite
projective module and `LinearEquiv.moduleInjective_of_dual_projective`.
-/

public section

namespace TauCeti

universe u v w z t

variable (k : Type u) (A : Type v) (P : Type w)
  [CommSemiring k] [Semiring A] [Algebra k A] [AddCommMonoid P] [Module A P]

/-- The Nakayama module `ν(P) = D Hom_A(P, A)`, with the left action dual to the right
action on `Hom_A(P, A)`. -/
-- The module compiler needs the synonym exposed to compile its inherited operations.
-- A `def`, rather than an `abbrev`, keeps instance search from identifying the two actions.
@[expose] def NakayamaModule := Module.Dual k (Module.Dual A P)

namespace NakayamaModule

section Semiring

instance : AddCommMonoid (NakayamaModule k A P) :=
  inferInstanceAs (AddCommMonoid (Module.Dual k (Module.Dual A P)))

instance : Module k (NakayamaModule k A P) :=
  inferInstanceAs (Module k (Module.Dual k (Module.Dual A P)))

instance : Module A (NakayamaModule k A P) :=
  Module.compHom (Module.Dual k (Module.Dual A P)) (dualRightAction k (Module.Dual A P))

/-- The underlying scalar module of `ν(P)` is the scalar dual of its algebra-valued dual. -/
def equivDual : NakayamaModule k A P ≃ₗ[k] Module.Dual k (Module.Dual A P) :=
  LinearEquiv.refl k _

/-- Nakayama functionals are determined by evaluation on algebra-valued functionals. -/
@[ext]
theorem ext {φ χ : NakayamaModule k A P}
    (h : ∀ ψ, equivDual k A P φ ψ = equivDual k A P χ ψ) : φ = χ :=
  (equivDual k A P).injective (LinearMap.ext h)

/-- The left action is dual to right multiplication on the values of an inner functional. -/
@[simp]
theorem smul_apply (a : A) (φ : NakayamaModule k A P) (ψ : Module.Dual A P) :
    equivDual k A P (a • φ) ψ = equivDual k A P φ (MulOpposite.op a • ψ) :=
  dualRightAction_apply_apply k (Module.Dual A P) a (equivDual k A P φ) ψ

instance : IsScalarTower k A (NakayamaModule k A P) :=
  IsScalarTower.of_algebraMap_smul fun c φ ↦ by
    ext ψ
    simp [smul_apply, ← MulOpposite.algebraMap_apply]

end Semiring

section Ring

variable (k : Type u) (A : Type v) (P : Type w)
  [CommRing k] [Semiring A] [Algebra k A] [AddCommMonoid P] [Module A P]

instance : AddCommGroup (NakayamaModule k A P) :=
  inferInstanceAs (AddCommGroup (Module.Dual k (Module.Dual A P)))

end Ring

section Field

variable (k : Type u) (A : Type v) (P : Type w)
  [Field k] [Ring A] [Algebra k A] [AddCommMonoid P] [Module A P]

/-- The Nakayama module of a finite projective module is injective over an algebra over
a field. The algebra need not be finite-dimensional. -/
instance [Module.Finite A P] [Module.Projective A P] :
    Module.Injective A (NakayamaModule k A P) :=
  (equivDual k A P).moduleInjective_of_dual_projective fun a φ ψ ↦ smul_apply k A P a φ ψ

end Field

end NakayamaModule

end TauCeti

namespace LinearMap

open TauCeti

universe u v w z t

variable {k : Type u} {A : Type v} [CommSemiring k] [Semiring A] [Algebra k A]
  {P : Type w} {Q : Type z} {N : Type t}
  [AddCommMonoid P] [Module A P] [AddCommMonoid Q] [Module A Q]
  [AddCommMonoid N] [Module A N]

/-- The covariant Nakayama map, obtained by applying the algebra dual and then the scalar dual. -/
def nakayamaMap (f : P →ₗ[A] Q) : NakayamaModule k A P →ₗ[A] NakayamaModule k A Q where
  toFun φ := (NakayamaModule.equivDual k A Q).symm
    (((f.lcomp Aᵐᵒᵖ A).restrictScalars k).dualMap (NakayamaModule.equivDual k A P φ))
  map_add' := fun _ _ ↦ by ext; simp
  map_smul' := fun _ _ ↦ by ext; simp [NakayamaModule.smul_apply]

/-- A Nakayama map evaluates by precomposing the inner functional with the original map. -/
@[simp]
theorem nakayamaMap_apply (f : P →ₗ[A] Q) (φ : NakayamaModule k A P) (ψ : Module.Dual A Q) :
    NakayamaModule.equivDual k A Q (f.nakayamaMap φ) ψ =
      NakayamaModule.equivDual k A P φ (ψ.comp f) := (rfl)

/-- The Nakayama construction preserves identity maps. -/
@[simp]
theorem nakayamaMap_id : (LinearMap.id : P →ₗ[A] P).nakayamaMap (k := k) = LinearMap.id := by
  ext φ ψ
  simp

/-- The Nakayama construction preserves composition in its original order. -/
@[simp]
theorem nakayamaMap_comp (g : Q →ₗ[A] N) (f : P →ₗ[A] Q) :
    (g.comp f).nakayamaMap (k := k) = g.nakayamaMap.comp f.nakayamaMap := by
  ext φ ψ
  simp [LinearMap.comp_assoc]

/-- The Nakayama construction sends the zero map to zero. -/
@[simp]
theorem nakayamaMap_zero : (0 : P →ₗ[A] Q).nakayamaMap (k := k) = 0 := by
  ext φ ψ
  simp

/-- The Nakayama construction preserves addition of maps. -/
@[simp]
theorem nakayamaMap_add (f g : P →ₗ[A] Q) :
    (f + g).nakayamaMap (k := k) = f.nakayamaMap + g.nakayamaMap := by
  ext φ ψ
  simp [LinearMap.comp_add]

end LinearMap
