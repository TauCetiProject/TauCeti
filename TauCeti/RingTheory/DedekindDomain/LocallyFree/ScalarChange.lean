/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.CentralBaseChange
public import TauCeti.RingTheory.DedekindDomain.LocallyFree.Basic

/-!
# Extension of locally free lattices

Extension of scalars along a morphism `Λ →ₐ[A] Γ` of algebras over a Dedekind domain preserves
local freeness and its rank, provided the destination algebra `Γ` is finite over `A`; the source
algebra need not be. At each height-one prime, balanced extension commutes with central
completion, and extending a completed free basis gives a free basis of the same rank over the
completed destination algebra (`TauCeti.LocallyFree.nonempty_linearEquiv_extendScalars`, which
needs no finiteness of `Γ` and holds after any central base change).

The induced map of locally free class groups is `TauCeti.LocallyFree.classGroupMap`, in
`TauCeti.RingTheory.DedekindDomain.LocallyFree.ClassGroup`.

## References

* A. Fröhlich, *Arithmetic and Galois module structure for tame extensions*, Appendix VI,
  Proposition 2, and Appendix VII, Proposition 1.
-/

public section

open scoped TensorProduct

attribute [local instance low] TauCeti.CentralBaseChange.module
  TauCeti.BalancedExtension.moduleBase

namespace TauCeti.LocallyFree

variable {A : Type*} [CommRing A] {Λ Γ : Type*} [Ring Λ] [Ring Γ] [Algebra A Λ] [Algebra A Γ]
  {M : Type*} [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M] {n : ℕ}

/-- Extension along a morphism `f : Λ →ₐ[A] Γ` of `A`-algebras preserves freeness of rank `n`
after central base change to a commutative `A`-algebra `S`: if `S ⊗[A] M ≃ S ⊗[A] Λⁿ`, then
`S ⊗[A] (Γ ⊗_Λ M) ≃ S ⊗[A] Γⁿ`. No finiteness of `Γ` over `A` is needed. For `S` a completion
`𝒪_v` this is the local condition of `IsLocallyFreeOfRank.extendScalars`. -/
theorem nonempty_linearEquiv_extendScalars {S : Type*} [CommRing S] [Algebra A S]
    (f : Λ →ₐ[A] Γ) [Module A (BalancedExtension (RingHomClass.toRingHom f) M)]
    [IsScalarTower A Γ (BalancedExtension (RingHomClass.toRingHom f) M)]
    (h : Nonempty (S ⊗[A] M ≃ₗ[S ⊗[A] Λ] S ⊗[A] (Fin n → Λ))) :
    Nonempty (S ⊗[A] BalancedExtension (RingHomClass.toRingHom f) M ≃ₗ[S ⊗[A] Γ]
      S ⊗[A] (Fin n → Γ)) := by
  let g := RingHomClass.toRingHom (Algebra.TensorProduct.map (AlgHom.id A S) f)
  exact ⟨(BalancedExtension.baseChangeEquiv A S Λ M f).symm.trans <|
    (BalancedExtension.congr g h.some).trans <|
      (BalancedExtension.congr g (CentralBaseChange.piRight A S Λ (Fin n))).trans <|
        (BalancedExtension.piScalarRight g (Fin n)).trans
          (CentralBaseChange.piRight A S Γ (Fin n)).symm⟩

variable [IsDedekindDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- Extension along a morphism of algebras over the central Dedekind base, whose destination
algebra is finite over the base, preserves locally free lattices and their rank. The extended
module must carry an `A`-action compatible with its destination-algebra action. When no such
action is already available, activate `TauCeti.BalancedExtension.moduleBase` locally. -/
theorem IsLocallyFreeOfRank.extendScalars [Module.Finite A Γ]
    (h : IsLocallyFreeOfRank A K Λ M n) (f : Λ →ₐ[A] Γ)
    [Module A (BalancedExtension (RingHomClass.toRingHom f) M)]
    [IsScalarTower A Γ (BalancedExtension (RingHomClass.toRingHom f) M)] :
    IsLocallyFreeOfRank A K Γ (BalancedExtension (RingHomClass.toRingHom f) M) n where
  finite := by
    have := h.finite
    have := Module.Finite.of_restrictScalars_finite A Λ M
    exact Module.Finite.trans Γ (BalancedExtension (RingHomClass.toRingHom f) M)
  nonempty_linearEquiv v := nonempty_linearEquiv_extendScalars f (h.nonempty_linearEquiv v)

end TauCeti.LocallyFree
