/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.Lie.ExteriorPower
import TauCeti.Algebra.BigOperators.Ring.List
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.Basic

/-!
# Derivations of an exterior algebra induced by endomorphisms

A linear endomorphism `f` of a module `M` over a commutative ring `R` extends uniquely to a
derivation of the exterior algebra `⋀ M`, sending each generator `ι m` to `ι (f m)`. On a
decomposable wedge it differentiates one factor at a time,

`f (m₁ ∧ ⋯ ∧ mₖ) = ∑ᵢ m₁ ∧ ⋯ ∧ f mᵢ ∧ ⋯ ∧ mₖ`,

so on each exterior power `⋀ᵏ M` it is the infinitesimal action `exteriorPower.lieMap k f`. The
assignment `f ↦` (its derivation) is a homomorphism of Lie algebras from `Module.End R M`, with the
commutator bracket, to the derivation Lie algebra of `⋀ M`; this is the exterior counterpart of
`SymmetricAlgebra.derivationOfEnd`.

Specialising `f` to the endomorphisms `⁅x, -⁆` of a Lie module gives the action of a Lie algebra
on the exterior algebra of the module by derivations. For the adjoint representation of a Lie
algebra `𝔤` this is the action on `⋀ 𝔤` whose invariants `(⋀ 𝔤)^𝔤` enter Kostant's description of
the Clifford algebra of `𝔤`.

## Main definitions and results

* `ExteriorAlgebra.derivationOfEnd`: the Lie algebra homomorphism from `Module.End R M` to the
  derivations of `ExteriorAlgebra R M`.
* `ExteriorAlgebra.derivationOfEnd_ι`: the induced derivation sends `ι m` to `ι (f m)`.
* `ExteriorAlgebra.eq_derivationOfEnd`: it is the only derivation doing so.
* `ExteriorAlgebra.derivationOfEnd_ιMulti`: the derivation rule on a decomposable wedge.
* `ExteriorAlgebra.derivationOfEnd_coe`: on `⋀ᵏ M` the induced derivation is
  `exteriorPower.lieMap k f`.

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
theorem derivationOfEnd_ιMulti (f : Module.End R M) {n : ℕ} (v : Fin n → M) :
    (derivationOfEnd R M f : Module.End R (ExteriorAlgebra R M)) (ιMulti R n v) =
      ∑ i, ιMulti R n (Function.update v i (f (v i))) := by
  simp only [ιMulti_apply]
  rw [map_prod_ofFn_of_leibniz _ (derivationLieAlgebra.leibniz (derivationOfEnd R M f))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [derivationOfEnd_ι, ← Function.comp_def (ι R) v, ← Function.comp_update]
  rfl

/-- **On an exterior power, the derivation induced by `f` is the infinitesimal action**
`exteriorPower.lieMap k f`. In particular it preserves each exterior power `⋀ᵏ M`. -/
theorem derivationOfEnd_coe (f : Module.End R M) {k : ℕ} (x : ⋀[R]^k M) :
    (derivationOfEnd R M f : Module.End R (ExteriorAlgebra R M)) x =
      exteriorPower.lieMap k f x := by
  have h : (derivationOfEnd R M f : Module.End R (ExteriorAlgebra R M)) ∘ₗ (⋀[R]^k M).subtype =
      (⋀[R]^k M).subtype ∘ₗ (exteriorPower.lieMap k f : Module.End R (⋀[R]^k M)) :=
    exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp [derivationOfEnd_ιMulti, exteriorPower.lieMap_apply_ιMulti]
  exact LinearMap.congr_fun h x

end ExteriorAlgebra
