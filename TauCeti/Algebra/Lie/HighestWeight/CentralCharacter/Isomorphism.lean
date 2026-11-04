/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Injective
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.OrbitSeparation
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Surjective

/-!
# The Harish-Chandra isomorphism

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system,
with Weyl vector `ρ`. The Harish-Chandra projection `TauCeti.hcProjection b : Z(U(L)) →ₐ[K] S(H)`
records the central characters, `χ_λ(z) = (hcProjection b z)(λ)`, and lands in the
dot-invariants `S(H)^{W·}`; its linear normalization `TauCeti.hcProjectionLinear b`, the
translate by `-ρ`, lands in the Weyl invariants `S(H)^W`. Both are injective
(`TauCeti.hcProjection_injective`) and onto (`TauCeti.range_hcProjection` and
`TauCeti.range_hcProjectionLinear`). This file packages them as isomorphisms

`Z(U(L)) ≃ₐ[K] S(H)^{W·}` and `Z(U(L)) ≃ₐ[K] S(H)^W`

(`TauCeti.harishChandraIso` and `TauCeti.harishChandraLinearIso`), and derives the
central-character orbit theorem: `χ_λ = χ_μ` exactly when `μ` lies in the dot orbit `W · λ`
(`TauCeti.vermaCentralCharacter_eq_iff`). Given equal central characters, every dot-invariant
`p` is `hcProjection b z` for a central `z`, so `p` takes the same value at `λ` and `μ`; since the
dot-invariants separate dot orbits (`TauCeti.forall_mem_dotInvariants_lift_eq_iff`), `μ ∈ W · λ`.

## Main definitions

* `TauCeti.harishChandraLinearIso b`: the linear Harish-Chandra isomorphism
  `Z(U(L)) ≃ₐ[K] S(H)^W`.
* `TauCeti.harishChandraIso b`: the Harish-Chandra isomorphism `Z(U(L)) ≃ₐ[K] S(H)^{W·}`.

## Main results

* `TauCeti.harishChandraLinearIso_symm_mem_pbwFiltration` and
  `TauCeti.harishChandraIso_symm_mem_pbwFiltration`: the inverse isomorphisms send an invariant of
  degree at most `n` to a central element of PBW degree at most `n`.
* `TauCeti.vermaCentralCharacter_eq_iff`: **two weights have the same central character exactly
  when they lie in one dot orbit.**

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
* J. Dixmier, *Enveloping Algebras*, §7.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §8.
-/

public section

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra

universe v

variable {K : Type} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L]
  [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-- A Weyl invariant is the linear Harish-Chandra projection of a central element. -/
private theorem exists_hcProjectionLinear_eq {q : _root_.SymmetricAlgebra K H}
    (hq : q ∈ linearInvariants H) :
    ∃ z : Subalgebra.center K (U L), hcProjectionLinear b z = q :=
  (AlgHom.mem_range _).1 <| (range_hcProjectionLinear b).ge hq

/-- A dot-invariant is the Harish-Chandra projection of a central element. -/
private theorem exists_hcProjection_eq {p : _root_.SymmetricAlgebra K H}
    (hp : p ∈ dotInvariants b) :
    ∃ z : Subalgebra.center K (U L), hcProjection b z = p :=
  (AlgHom.mem_range _).1 <| (range_hcProjection b).ge hp

/-! ### The isomorphisms -/

/-- **The linear Harish-Chandra isomorphism** `Z(U(L)) ≃ₐ[K] S(H)^W`: the linear Harish-Chandra
projection `TauCeti.hcProjectionLinear b`, with its values in the Weyl invariants. -/
noncomputable def harishChandraLinearIso : Subalgebra.center K (U L) ≃ₐ[K] linearInvariants H :=
  AlgEquiv.ofBijective
    ((hcProjectionLinear b).codRestrict (linearInvariants H)
      (hcProjectionLinear_mem_linearInvariants b))
    ⟨fun _ _ h ↦ hcProjectionLinear_injective b (congrArg Subtype.val h),
      fun q ↦ (exists_hcProjectionLinear_eq b q.2).imp fun _ hz ↦ Subtype.ext hz⟩

/-- The linear Harish-Chandra isomorphism is the linear Harish-Chandra projection. -/
@[simp]
theorem coe_harishChandraLinearIso_apply (z : Subalgebra.center K (U L)) :
    (harishChandraLinearIso b z : _root_.SymmetricAlgebra K H) = hcProjectionLinear b z :=
  (rfl)

/-- The inverse of the linear Harish-Chandra isomorphism sends a Weyl invariant to the central
element projecting to it. -/
@[simp]
theorem hcProjectionLinear_harishChandraLinearIso_symm_apply (q : linearInvariants H) :
    hcProjectionLinear b ((harishChandraLinearIso b).symm q) = q := by
  rw [← coe_harishChandraLinearIso_apply, AlgEquiv.apply_symm_apply]

/-- **The Harish-Chandra isomorphism** `Z(U(L)) ≃ₐ[K] S(H)^{W·}`: the Harish-Chandra projection
`TauCeti.hcProjection b`, with its values in the dot-invariants. -/
noncomputable def harishChandraIso : Subalgebra.center K (U L) ≃ₐ[K] dotInvariants b :=
  AlgEquiv.ofBijective
    ((hcProjection b).codRestrict (dotInvariants b) hcProjection_mem_dotInvariants)
    ⟨fun _ _ h ↦ hcProjection_injective b (congrArg Subtype.val h),
      fun p ↦ (exists_hcProjection_eq b p.2).imp fun _ hz ↦ Subtype.ext hz⟩

/-- The Harish-Chandra isomorphism is the Harish-Chandra projection. -/
@[simp]
theorem coe_harishChandraIso_apply (z : Subalgebra.center K (U L)) :
    (harishChandraIso b z : _root_.SymmetricAlgebra K H) = hcProjection b z :=
  (rfl)

/-- The inverse of the Harish-Chandra isomorphism sends a dot-invariant to the central element
projecting to it. -/
@[simp]
theorem hcProjection_harishChandraIso_symm_apply (p : dotInvariants b) :
    hcProjection b ((harishChandraIso b).symm p) = p := by
  rw [← coe_harishChandraIso_apply, AlgEquiv.apply_symm_apply]

/-- The two Harish-Chandra isomorphisms differ by the translation by `-ρ` from the dot-invariants
to the Weyl invariants: the linear one is the Harish-Chandra isomorphism followed by
`TauCeti.dotInvariantsEquivLinearInvariants b`. -/
theorem harishChandraIso_trans_dotInvariantsEquivLinearInvariants :
    (harishChandraIso b).trans (dotInvariantsEquivLinearInvariants b) =
      harishChandraLinearIso b :=
  AlgEquiv.ext fun z ↦ Subtype.ext <| by simp [hcProjectionLinear_apply]

/-! ### Inverse filtration -/

/-- **The inverse linear Harish-Chandra isomorphism preserves degrees**: a Weyl invariant has
degree at most `n` exactly when the corresponding central element has PBW degree at most `n`. -/
@[simp]
theorem harishChandraLinearIso_symm_mem_pbwFiltration {n : ℕ} (q : linearInvariants H) :
    (((harishChandraLinearIso b).symm q : Subalgebra.center K (U L)) : U L) ∈
        UniversalEnvelopingAlgebra.pbwFiltration K L n ↔
      (q : _root_.SymmetricAlgebra K H) ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n := by
  rw [← hcProjectionLinear_mem_wordFiltration_iff b,
    hcProjectionLinear_harishChandraLinearIso_symm_apply]

/-- **The inverse Harish-Chandra isomorphism preserves degrees**: a dot-invariant has degree at
most `n` exactly when the corresponding central element has PBW degree at most `n`. -/
@[simp]
theorem harishChandraIso_symm_mem_pbwFiltration {n : ℕ} (p : dotInvariants b) :
    (((harishChandraIso b).symm p : Subalgebra.center K (U L)) : U L) ∈
        UniversalEnvelopingAlgebra.pbwFiltration K L n ↔
      (p : _root_.SymmetricAlgebra K H) ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n := by
  rw [← hcProjection_mem_wordFiltration_iff b, hcProjection_harishChandraIso_symm_apply]

/-! ### Central characters and dot orbits -/

/-- **Harish-Chandra's theorem on central characters**: two weights `lam` and `mu` have the same
central character, `χ_lam = χ_mu`, exactly when `mu` lies in the dot orbit of `lam`, that is
`mu = w · lam = w (lam + ρ) - ρ` for an element `w` of the Weyl group. -/
theorem vermaCentralCharacter_eq_iff {lam mu : Module.Dual K H} :
    vermaCentralCharacter b lam = vermaCentralCharacter b mu ↔
      ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu := by
  refine ⟨fun h ↦ forall_mem_dotInvariants_lift_eq_iff.1 fun p hp ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_hcProjection_eq b hp
    rw [lift_hcProjection, lift_hcProjection, h]
  · rintro ⟨w, rfl⟩
    rw [vermaCentralCharacter_dotAction]

end TauCeti
