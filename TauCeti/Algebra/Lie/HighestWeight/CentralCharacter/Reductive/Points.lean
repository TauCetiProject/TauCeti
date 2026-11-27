/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Points
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Reductive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter.Basic

/-!
# Every character of the centre of a reductive enveloping algebra is a central character

Let `L` be a finite-dimensional reductive Lie algebra over an algebraically closed field `K` of
characteristic zero, with centre `z(L)`, `H` a Cartan subalgebra of `[L, L]` and `b` a base of its
root system. Every character of `Z(U(L))` is `TauCeti.reductiveCentralCharacter b ζ λ` for a
central weight `ζ ∈ z(L)^*` and `λ ∈ H^*` (`TauCeti.exists_eq_reductiveCentralCharacter`), and
`(ζ, λ)` is unique up to the dot action on `λ` (`TauCeti.reductiveCentralCharacter_eq_iff`). The
proof splits a character along `Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`: on `Sym(z(L))` it is
evaluation at `ζ`, and on `Z(U([L, L]))` it is a Verma central character
(`TauCeti.exists_eq_vermaCentralCharacter`).

So the infinitesimal character of a module is a pair of a central weight and a dot orbit of
weights: a module with an infinitesimal character has one of the form `χ_{(ζ, λ)}`
(`TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.exists_reductiveCentralCharacter`),
and for a nonzero module the parameters `(ζ', μ)` of its infinitesimal character are exactly
`ζ' = ζ` and `μ` in the dot orbit of `λ`
(`TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.reductiveCentralCharacter_iff`).

## Main results

* `TauCeti.exists_eq_reductiveCentralCharacter`: every character of `Z(U(L))` is a reductive
  central character `χ_{(ζ, λ)}`.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.reductiveCentralCharacter_iff`:
  the infinitesimal character of a nonzero module determines its central weight and the dot orbit
  of its weight.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
* J. Dixmier, *Enveloping Algebras*, §7.4.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter V, §5, for the
  Harish-Chandra isomorphism of a reductive Lie algebra.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra TauCeti.UniversalEnvelopingAlgebra

universe u v w

section Reductive

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L]
  {H : LieSubalgebra K (derivedSeries K L 1)} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H (derivedSeries K L 1)]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K
local notation "SZ" => _root_.SymmetricAlgebra K (center K L)

/-- **Every character of the centre of a reductive Lie algebra is a central character.** Every
algebra character of `Z(U(L))` is `χ_{(ζ, λ)}` for a central weight `ζ ∈ z(L)^*` and a weight
`λ ∈ H^*`. -/
theorem exists_eq_reductiveCentralCharacter (χ : Subalgebra.center K (U L) →ₐ[K] K) :
    ∃ (ζ : Module.Dual K (center K L)) (lam : Module.Dual K H),
      χ = reductiveCentralCharacter b ζ lam := by
  -- Read `χ` on `Sym(z(L)) ⊗ Z(U([L, L]))` and split it into its two factors.
  let φ := χ.comp (reductiveCenterEquiv K L).symm.toAlgHom
  let ζ : Module.Dual K (center K L) :=
    (φ.comp Algebra.TensorProduct.includeLeft).toLinearMap.comp
      (_root_.SymmetricAlgebra.ι K (center K L))
  obtain ⟨lam, hlam⟩ := exists_eq_vermaCentralCharacter b
    (φ.comp (Algebra.TensorProduct.includeRight :
      Subalgebra.center K (U (derivedSeries K L 1)) →ₐ[K] SZ ⊗[K] _))
  have hζ : φ.comp Algebra.TensorProduct.includeLeft = _root_.SymmetricAlgebra.lift ζ :=
    _root_.SymmetricAlgebra.algHom_ext (LinearMap.ext fun h ↦ by simp [ζ])
  refine ⟨ζ, lam, AlgHom.ext fun z ↦ ?_⟩
  obtain ⟨t, rfl⟩ := (reductiveCenterEquiv K L).symm.surjective z
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a c =>
    calc χ ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c))
        = φ (a ⊗ₜ[K] 1) * φ (1 ⊗ₜ[K] c) := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, AlgHom.comp_apply,
            AlgEquiv.coe_toAlgHom]
      _ = _root_.SymmetricAlgebra.lift ζ a * vermaCentralCharacter b lam c := by
          rw [← hζ, ← hlam]
          simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply]
      _ = _ := (reductiveCentralCharacter_reductiveCenterEquiv_symm_tmul ζ lam a c).symm

namespace UniversalEnvelopingAlgebra.HasInfinitesimalCharacter

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- **The infinitesimal character as a central weight and a weight.** A module with an
infinitesimal character has an infinitesimal character of the form `χ_{(ζ, λ)}`. -/
theorem exists_reductiveCentralCharacter {χ : Subalgebra.center K (U L) →ₐ[K] K}
    (h : HasInfinitesimalCharacter K L M χ) :
    ∃ (ζ : Module.Dual K (center K L)) (lam : Module.Dual K H),
      HasInfinitesimalCharacter K L M (reductiveCentralCharacter b ζ lam) := by
  obtain ⟨ζ, lam, rfl⟩ := exists_eq_reductiveCentralCharacter b χ
  exact ⟨ζ, lam, h⟩

variable {b} in
/-- **The infinitesimal character is a central weight and a dot orbit.** If a nonzero module has
infinitesimal character `χ_{(ζ, λ)}`, then it has infinitesimal character `χ_{(ζ', μ)}` exactly
when `ζ' = ζ` and `μ` lies in the dot orbit of `λ`. -/
theorem reductiveCentralCharacter_iff [Nontrivial M] {ζ ζ' : Module.Dual K (center K L)}
    {lam mu : Module.Dual K H}
    (h : HasInfinitesimalCharacter K L M (reductiveCentralCharacter b ζ lam)) :
    HasInfinitesimalCharacter K L M (reductiveCentralCharacter b ζ' mu) ↔
      ζ = ζ' ∧ ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu := by
  rw [← reductiveCentralCharacter_eq_iff]
  exact ⟨h.eq, fun he ↦ he ▸ h⟩

end UniversalEnvelopingAlgebra.HasInfinitesimalCharacter

end Reductive

end TauCeti
