/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Isomorphism
public import TauCeti.RingTheory.IntegralClosure.ExtendAlgHom

/-!
# Every character of the centre is a Verma central character

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system.
Every algebra character `χ : Z(U(L)) →ₐ[K] K` is the central character `χ_λ` of a Verma module
(`TauCeti.exists_eq_vermaCentralCharacter`), and `λ` is unique up to the dot action of the Weyl
group (`TauCeti.vermaCentralCharacter_eq_iff`). Through the linear Harish-Chandra isomorphism
`Z(U(L)) ≃ S(H)^W`, `χ` is a character of the Weyl invariants; `S(H)` is a finite module over
`S(H)^W` (Noether), hence integral over it (`TauCeti.isIntegral_linearInvariants`), so `χ` extends
to a character of the polynomial algebra `S(H)` (`TauCeti.exists_algHom_comp_toAlgHom_eq`), which
is evaluation at a weight `μ`; then `χ = χ_{μ - ρ}`.

## Main results

* `TauCeti.exists_eq_vermaCentralCharacter`: every character of `Z(U(L))` is a Verma central
  character.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
* J. Dixmier, *Enveloping Algebras*, §7.4.
-/

public section

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

local notation "U" => _root_.UniversalEnvelopingAlgebra K

variable [IsAlgClosed K] (b : (IsKilling.rootSystem H).Base)

/-- **Every character of the centre is a central character.** For `L` with non-degenerate Killing
form over an algebraically closed field of characteristic zero, every algebra character of
`Z(U(L))` is the central character `χ_λ` of the Verma module of some weight `λ`. -/
theorem exists_eq_vermaCentralCharacter (χ : Subalgebra.center K (U L) →ₐ[K] K) :
    ∃ lam : Module.Dual K H, χ = vermaCentralCharacter b lam := by
  -- `χ` is a character of `S(H)^W`, which extends to a character of `S(H)`.
  obtain ⟨g, hg⟩ := exists_algHom_comp_toAlgHom_eq (S := _root_.SymmetricAlgebra K H)
    (χ.comp (harishChandraLinearIso b).symm.toAlgHom)
    fun p hp ↦ by simp_all
  -- A character of `S(H)` is evaluation at the weight `μ = g ∘ ι`.
  let μ : Module.Dual K H := g.toLinearMap.comp (_root_.SymmetricAlgebra.ι K H)
  have hgμ : g = _root_.SymmetricAlgebra.lift μ :=
    _root_.SymmetricAlgebra.algHom_ext (LinearMap.ext fun h ↦ by simp [μ])
  refine ⟨μ - weylVector (IsKilling.rootSystem H) b, AlgHom.ext fun z ↦ ?_⟩
  rw [← lift_hcProjectionLinear, ← hgμ, ← coe_harishChandraLinearIso_apply]
  have := DFunLike.congr_fun hg (harishChandraLinearIso b z)
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] at this
  exact this.symm

end TauCeti
