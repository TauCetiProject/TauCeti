/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic
import TauCeti.Algebra.BigOperators.Ring.List
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.Basic

/-!
# Derivations of an exterior algebra induced by endomorphisms

A linear endomorphism `f` of a module `M` over a commutative ring `R` extends uniquely to a
derivation of the exterior algebra `⋀ M`, sending each generator `ι m` to `ι (f m)`. On a
decomposable wedge it differentiates one factor at a time,

`f (m₁ ∧ ⋯ ∧ mₖ) = ∑ᵢ m₁ ∧ ⋯ ∧ f mᵢ ∧ ⋯ ∧ mₖ`,

so it preserves each exterior power `⋀ᵏ M`, where it is the infinitesimal action
`exteriorPower.lieMap k f`. The assignment `f ↦` (its derivation) is a homomorphism of Lie algebras
from `Module.End R M`, with the commutator bracket, to the derivation Lie algebra of `⋀ M`; this is
the exterior counterpart of `SymmetricAlgebra.derivationOfEnd`.

Specialising `f` to the endomorphisms `⁅x, -⁆` of a Lie module gives the action of a Lie algebra
on the exterior algebra of the module by derivations, available as the scoped Lie module
structure `ExteriorAlgebra.LieAction.instLieRingModule`. For the adjoint representation of a Lie
algebra `𝔤` this is the action on `⋀ 𝔤` whose invariants `(⋀ 𝔤)^𝔤` enter Kostant's description of
the Clifford algebra of `𝔤`.

## Main definitions and results

* `ExteriorAlgebra.derivationOfEnd`: the Lie algebra homomorphism from `Module.End R M` to the
  derivations of `ExteriorAlgebra R M`.
* `ExteriorAlgebra.derivationOfEnd_ι`: the induced derivation sends `ι m` to `ι (f m)`.
* `ExteriorAlgebra.eq_derivationOfEnd`: it is the only derivation doing so.
* `ExteriorAlgebra.derivationOfEnd_ιMulti`: the derivation rule on a decomposable wedge.
* `ExteriorAlgebra.derivationOfEnd_mem_exteriorPower`: the induced derivation preserves each
  exterior power `⋀ᵏ M`.
* `ExteriorAlgebra.LieAction.instLieRingModule`, `ExteriorAlgebra.LieAction.lie_def`: for a Lie
  module `M` over `L`, the scoped action of `L` on `⋀ M` by the derivations
  `derivationOfEnd R M (LieModule.toEnd R L M x)`.

## References

* N. Bourbaki, *Algebra*, Chapter III, §10.
-/

public section

namespace ExteriorAlgebra

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The derivation of `⋀ M` extending `f`: the untwisted `ExteriorAlgebra.liftTwistedDerivation`
with zero degree-zero part, bundled with its Leibniz rule. -/
private noncomputable def derivationOfEndFun (f : Module.End R M) :
    derivationLieAlgebra R (ExteriorAlgebra R M) :=
  ⟨liftTwistedDerivation (AlgHom.id R (ExteriorAlgebra R M)) 0 (by simp) (ι R ∘ₗ f) (by simp)
      (fun m ↦ by simp [ι_add_mul_swap]),
    mem_derivationLieAlgebra.2 fun x y ↦ by
      rw [liftTwistedDerivation_mul, AlgHom.id_apply]⟩

variable {R}

/-- A derivation of `⋀ M` sending each `ι m` to `ι (f m)` is `derivationOfEndFun R f`. -/
private theorem eq_derivationOfEndFun {f : Module.End R M}
    {D : derivationLieAlgebra R (ExteriorAlgebra R M)}
    (hD : ∀ m, (D : Module.End R (ExteriorAlgebra R M)) (ι R m) = ι R (f m)) :
    D = derivationOfEndFun R f :=
  Subtype.ext <| liftTwistedDerivation_unique _ _ _ _ _ _
    (fun s ↦ by simp) hD (derivationLieAlgebra.leibniz D)

variable (R M)

/-- The derivation of `ExteriorAlgebra R M` induced by a linear endomorphism `f` of `M`: the
unique derivation sending each generator `ι m` to `ι (f m)`. The assignment is a homomorphism of
Lie algebras from `Module.End R M`, with the commutator bracket, to the derivation Lie algebra. -/
noncomputable def derivationOfEnd :
    Module.End R M →ₗ⁅R⁆ derivationLieAlgebra R (ExteriorAlgebra R M) where
  toFun := derivationOfEndFun R
  map_add' f g := (eq_derivationOfEndFun fun m ↦ by simp [derivationOfEndFun]).symm
  map_smul' r f := (eq_derivationOfEndFun fun m ↦ by simp [derivationOfEndFun]).symm
  map_lie' {f g} :=
    (eq_derivationOfEndFun fun m ↦ by simp [Ring.lie_def, derivationOfEndFun]).symm

variable {R M}

/-- The derivation induced by `f` sends the generator `ι m` to `ι (f m)`. -/
@[simp]
theorem derivationOfEnd_ι (f : Module.End R M) (m : M) :
    (derivationOfEnd R M f : Module.End R (ExteriorAlgebra R M)) (ι R m) = ι R (f m) := by
  simp [derivationOfEnd, derivationOfEndFun]

/-- **Uniqueness**: a derivation of `⋀ M` sending each generator `ι m` to `ι (f m)` is the
derivation induced by `f`. -/
theorem eq_derivationOfEnd {f : Module.End R M} {D : derivationLieAlgebra R (ExteriorAlgebra R M)}
    (hD : ∀ m, (D : Module.End R (ExteriorAlgebra R M)) (ι R m) = ι R (f m)) :
    D = derivationOfEnd R M f :=
  eq_derivationOfEndFun hD

/-- **The derivation rule on a decomposable wedge**: the derivation induced by `f` differentiates
one factor at a time. -/
@[simp]
theorem derivationOfEnd_ιMulti (f : Module.End R M) {n : ℕ} (v : Fin n → M) :
    (derivationOfEnd R M f : Module.End R (ExteriorAlgebra R M)) (ιMulti R n v) =
      ∑ i, ιMulti R n (Function.update v i (f (v i))) := by
  simp only [ιMulti_apply]
  rw [map_prod_ofFn_of_leibniz _ (derivationLieAlgebra.leibniz (derivationOfEnd R M f))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [derivationOfEnd_ι, ← Function.comp_def (ι R) v, ← Function.comp_update]
  rfl

/-- **The derivation induced by `f` preserves degrees**: it maps each exterior power `⋀ᵏ M` into
itself. -/
theorem derivationOfEnd_mem_exteriorPower (f : Module.End R M) {k : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) :
    (derivationOfEnd R M f : Module.End R (ExteriorAlgebra R M)) x ∈ ⋀[R]^k M :=
  liftTwistedDerivation_mem_exteriorPower _ _ _ _ _ _ (r := 0)
    (fun m ↦ by simp) (fun s ↦ by simp) (fun m ↦ by simp) hx

namespace LieAction

variable (R M) (L : Type*) [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]

/-- **The exterior algebra of a Lie module.** `L` acts on `⋀ M` through the derivations
`ExteriorAlgebra.derivationOfEnd R M (LieModule.toEnd R L M x)` extending its action on `M`.
Scoped, like Kostant's spinor module `TauCeti.SpinPolarizationData.kostantSpinLieRingModule`: an
exterior algebra can carry other `L`-module structures. -/
noncomputable scoped instance instLieRingModule : LieRingModule L (ExteriorAlgebra R M) :=
  LieRingModule.compLieHom _ ((derivationLieAlgebra R (ExteriorAlgebra R M)).incl.comp
    ((derivationOfEnd R M).comp (LieModule.toEnd R L M)))

/-- The exterior algebra of a Lie module is a Lie module over the base ring. -/
noncomputable scoped instance instLieModule : LieModule R L (ExteriorAlgebra R M) :=
  LieModule.compLieHom _ _

variable {R L M}

/-- **The defining equation of the exterior algebra of a Lie module**: `x` acts by the derivation
extending its action on `M`. -/
@[simp, grind =]
theorem lie_def (x : L) (y : ExteriorAlgebra R M) :
    ⁅x, y⁆ =
      (derivationOfEnd R M (LieModule.toEnd R L M x) : Module.End R (ExteriorAlgebra R M)) y :=
  rfl

end LieAction

end ExteriorAlgebra
