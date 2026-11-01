/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Injective
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.OrbitSeparation
import TauCeti.LinearAlgebra.SymmetricAlgebra.DegreeFiltration

/-!
# The Harish-Chandra isomorphism

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system,
with Weyl vector `ρ`. The Harish-Chandra projection `TauCeti.hcProjection b : Z(U(L)) →ₐ[K] S(H)`
records the central characters, `χ_λ(z) = (hcProjection b z)(λ)`, and lands in the
dot-invariants `S(H)^{W·}`; its linear normalization `TauCeti.hcProjectionLinear b`, the
translate by `-ρ`, lands in the Weyl invariants `S(H)^W`. Both are injective
(`TauCeti.hcProjection_injective`). This file proves that they are onto, so that

`Z(U(L)) ≃ₐ[K] S(H)^{W·}` and `Z(U(L)) ≃ₐ[K] S(H)^W`

(`TauCeti.harishChandraIso` and `TauCeti.harishChandraLinearIso`), and derives the
central-character orbit theorem: `χ_λ = χ_μ` exactly when `μ` lies in the dot orbit `W · λ`
(`TauCeti.vermaCentralCharacter_eq_iff`).

## The proof of surjectivity

It is an induction on the degree of a Weyl invariant `q`, carried out on the linear side, where
the Weyl group acts linearly and the invariants are graded
(`TauCeti.isHomogeneous_linearInvariants`).
If `q` has degree at most `n`, its homogeneous component `q_n` of degree `n` is a Weyl invariant, so
by Chevalley's restriction theorem it is the restriction to `H` of a homogeneous invariant
`p ∈ S^n(L)^L`
(`LieSubalgebra.linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants`). The
symmetrization `s` of `p` is central, and its linear Harish-Chandra projection agrees with the
restriction of `p` up to degree below `n`: for the projection itself this is the leading-term
computation `TauCeti.hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious`, and the
translation by `-ρ` changes nothing in top degree
(`SymmetricAlgebra.translation_sub_self_mem_wordFiltrationPrevious`). Since `q` agrees with `q_n`
up to degree below `n` (`TauCeti.SymmetricAlgebra.sub_decompose_mem_wordFiltrationPrevious`), the
Weyl invariant `q - hcProjectionLinear b s` has degree below `n`, and induction finishes.

The algebraic closure of `K` enters only through Chevalley's restriction theorem, whose
surjectivity uses the finite-dimensional irreducible modules `L(λ)`.

## Main definitions

* `TauCeti.harishChandraLinearIso b`: the linear Harish-Chandra isomorphism
  `Z(U(L)) ≃ₐ[K] S(H)^W`.
* `TauCeti.harishChandraIso b`: the Harish-Chandra isomorphism `Z(U(L)) ≃ₐ[K] S(H)^{W·}`.

## Main results

* `TauCeti.range_hcProjectionLinear`: the image of the linear Harish-Chandra projection is
  `S(H)^W`.
* `TauCeti.range_hcProjection`: the image of the Harish-Chandra projection is `S(H)^{W·}`.
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

/-! ### Surjectivity -/

/-- **One step of the degree induction**: a Weyl invariant `q` of degree at most `n` agrees with
the linear Harish-Chandra projection of some central element up to degree below `n`. -/
private theorem exists_sub_hcProjectionLinear_mem_wordFiltrationPrevious {n : ℕ}
    {q : _root_.SymmetricAlgebra K H} (hq : q ∈ linearInvariants H)
    (hqn : q ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n) :
    ∃ s : Subalgebra.center K (U L),
      q - hcProjectionLinear b s ∈ wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) n := by
  have hn : IsUnit (n.factorial : K) := (Nat.cast_ne_zero.mpr n.factorial_ne_zero).isUnit
  -- the top component `qₙ` of `q` is the restriction of a homogeneous invariant `p` of degree `n`
  obtain ⟨p, ⟨hp, hpn⟩, hpq⟩ :=
    LieSubalgebra.linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants H n
      ⟨isHomogeneous_linearInvariants H n hq, SetLike.coe_mem _⟩
  -- the symmetrization `s` of `p` is central of PBW degree at most `n`
  let s : Subalgebra.center K (U L) :=
    ⟨UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization K L n hn ⟨p, hpn⟩,
      UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center K L n hn hp⟩
  refine ⟨s, ?_⟩
  have hs : (s : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n :=
    UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_pbwFiltration K L n hn ⟨p, hpn⟩
  -- `q - qₙ`, `HC s - res p` and `HC_lin s - HC s` all have degree below `n`
  have htop := sub_decompose_mem_wordFiltrationPrevious hqn
  have hlead := hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious b hn ⟨p, hpn⟩
    (z := s) rfl
  have htrans := _root_.SymmetricAlgebra.translation_sub_self_mem_wordFiltrationPrevious
    (-weylVector (IsKilling.rootSystem H) b) (hcProjection_mem_wordFiltration b hs)
  rw [AlgHom.toLinearMap_apply] at hpq
  rw [← hpq] at htop
  rw [hcProjectionLinear_apply]
  convert sub_mem (sub_mem htop hlead) htrans using 1
  abel

/-- **The linear Harish-Chandra projection is onto the Weyl invariants**: every Weyl invariant
`q ∈ S(H)^W` is `hcProjectionLinear b z` for a central element `z`. -/
theorem exists_hcProjectionLinear_eq {q : _root_.SymmetricAlgebra K H}
    (hq : q ∈ linearInvariants H) :
    ∃ z : Subalgebra.center K (U L), hcProjectionLinear b z = q := by
  obtain ⟨n, hqn⟩ := exists_mem_wordFiltration q
  induction n using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    obtain ⟨s, hs⟩ := exists_sub_hcProjectionLinear_mem_wordFiltrationPrevious b hq hqn
    cases n with
    | zero =>
      rw [wordFiltrationPrevious_zero, Submodule.mem_bot, sub_eq_zero] at hs
      exact ⟨s, hs.symm⟩
    | succ m =>
      rw [wordFiltrationPrevious_succ] at hs
      obtain ⟨z, hz⟩ := ih m (Nat.lt_succ_self m)
        (sub_mem hq (hcProjectionLinear_mem_linearInvariants b s)) hs
      exact ⟨z + s, by rw [map_add, hz, sub_add_cancel]⟩

/-- **The image of the linear Harish-Chandra projection is the Weyl invariants** `S(H)^W`. -/
theorem range_hcProjectionLinear : (hcProjectionLinear b).range = linearInvariants H :=
  le_antisymm (fun _ ⟨z, hz⟩ ↦ hz ▸ hcProjectionLinear_mem_linearInvariants b z)
    fun _ hq ↦ exists_hcProjectionLinear_eq b hq

/-- **The Harish-Chandra projection is onto the dot-invariants**: every dot-invariant
`p ∈ S(H)^{W·}` is `hcProjection b z` for a central element `z`. -/
theorem exists_hcProjection_eq {p : _root_.SymmetricAlgebra K H} (hp : p ∈ dotInvariants b) :
    ∃ z : Subalgebra.center K (U L), hcProjection b z = p := by
  obtain ⟨z, hz⟩ := exists_hcProjectionLinear_eq b
    ((translation_neg_weylVector_mem_linearInvariants_iff b).2 hp)
  exact ⟨z, (_root_.SymmetricAlgebra.translation _).injective <| by
    rw [← hcProjectionLinear_apply, hz]⟩

/-- **The image of the Harish-Chandra projection is the dot-invariants** `S(H)^{W·}`. -/
theorem range_hcProjection : (hcProjection b).range = dotInvariants b :=
  le_antisymm (fun _ ⟨z, hz⟩ ↦ hz ▸ hcProjection_mem_dotInvariants z)
    fun _ hp ↦ exists_hcProjection_eq b hp

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
