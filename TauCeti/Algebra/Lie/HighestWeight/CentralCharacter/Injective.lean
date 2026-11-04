/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.LeadingTerm
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Linear
-- Non-public: the inputs of the degree induction, and the determination of an element of `S(H)`
-- by its values over the infinite field `K`, used only inside the proofs.
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Algebra.Lie.Killing.ChevalleyRestriction
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Center
import TauCeti.LinearAlgebra.SymmetricAlgebra.DegreeFiltration
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation

/-!
# The Harish-Chandra projection is injective

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, `H` a splitting Cartan subalgebra and `b` a base of its root system. This file
proves that the Harish-Chandra projection `TauCeti.hcProjection b : Z(U(L)) →ₐ[K] S(H)` is injective
(`TauCeti.hcProjection_injective`), and so is its linear normalization
`TauCeti.hcProjectionLinear b` (`TauCeti.hcProjectionLinear_injective`).

More precisely, the projection matches the PBW filtration of the centre with the degree filtration
of `S(H)` exactly: a central element `z` has PBW degree at most `n` if and only if its projection
has degree at most `n` (`TauCeti.hcProjection_mem_wordFiltration_iff`). One direction is
`TauCeti.hcProjection_mem_wordFiltration`. For the other, it suffices to show that the degree of a
central element `z` drops below `m` once its projection does. Let `p ∈ S^m(L)` be the PBW symbol of
`z`; it is a Lie invariant
(`TauCeti.UniversalEnvelopingAlgebra.mem_lieInvariants_of_pbwHomogeneousComponentMap_eq_mk`), so its
symmetrization `s` is central and agrees with `z` up to degree below `m`. The projection of `s` is
the Chevalley restriction of `p` up to degree below `m`
(`TauCeti.hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious`), so the restriction of
`p`, which is homogeneous of degree `m`, has degree below `m` and therefore vanishes. Chevalley's
restriction theorem is injective on the invariants
(`LieSubalgebra.lieCartanRestriction_injOn_lieInvariants`), so `p = 0` and `z` has degree below `m`.

Injectivity is one half of the Harish-Chandra isomorphism `Z(U(L)) ≃ S(H)^{W·}`, the other being
that the projection is onto the dot-invariants (`TauCeti.range_hcProjection`, over an
algebraically closed field). Since the projection records the central characters
`χ_λ`, a central element is determined by its central characters
(`TauCeti.eq_of_forall_vermaCentralCharacter_eq`).

## Main results

* `TauCeti.hcProjection_mem_wordFiltrationPrevious_iff` and
  `TauCeti.hcProjection_mem_wordFiltration_iff`: the Harish-Chandra projection matches the PBW
  filtration of the centre with the degree filtration of `S(H)`.
* `TauCeti.hcProjection_injective`: the Harish-Chandra projection is injective.
* `TauCeti.eq_of_forall_vermaCentralCharacter_eq`: a central element is determined by its central
  characters.
* `TauCeti.hcProjectionLinear_mem_wordFiltration_iff` and `TauCeti.hcProjectionLinear_injective`:
  the same for the linear Harish-Chandra projection.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
* J. Dixmier, *Enveloping Algebras*, §7.4.
-/

public section

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra

universe v

variable {K : Type} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-- **The degree of a central element drops with that of its Harish-Chandra projection**: a central
element of PBW degree at most `m` whose projection has degree below `m` has PBW degree below `m`. -/
private theorem mem_pbwFiltrationPrevious_of_hcProjection_mem {m : ℕ}
    {z : Subalgebra.center K (U L)}
    (hzm : (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L m)
    (hz : hcProjection b z ∈ wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) m) :
    (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltrationPrevious K L m := by
  have hm : IsUnit (m.factorial : K) := (Nat.cast_ne_zero.mpr m.factorial_ne_zero).isUnit
  rw [UniversalEnvelopingAlgebra.pbwFiltration_def] at hzm
  -- the PBW symbol `p` of `z` is a homogeneous Lie invariant
  obtain ⟨p, hp⟩ := UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap_surjective K L m
    (Submodule.Quotient.mk ⟨z, hzm⟩)
  have hinv :=
    UniversalEnvelopingAlgebra.mem_lieInvariants_of_pbwHomogeneousComponentMap_eq_mk hm z.2 hzm hp
  -- its symmetrization `s` is central and agrees with `z` up to degree below `m`
  let s : Subalgebra.center K (U L) :=
    ⟨UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization K L m hm p,
      UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center K L m hm hinv⟩
  have hsz : ((s - z : Subalgebra.center K (U L)) : U L) ∈
      UniversalEnvelopingAlgebra.pbwFiltrationPrevious K L m := by
    have h := (UniversalEnvelopingAlgebra.mk_pbwHomogeneousSymmetrization K L m hm p).trans hp
    rwa [Submodule.Quotient.eq, wordFiltration.mem_previousRestricted_iff,
      ← UniversalEnvelopingAlgebra.pbwFiltrationPrevious_def] at h
  -- so the Chevalley restriction of `p`, homogeneous of degree `m`, has degree below `m`
  have hres : lieCartanRestriction H (p : _root_.SymmetricAlgebra K L) ∈
      wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) m := by
    have hlead := hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious b hm p
      (z := s) rfl
    have hdiff := hcProjection_mem_wordFiltrationPrevious b hsz
    rw [map_sub] at hdiff
    convert sub_mem (add_mem hdiff hz) hlead using 1
    abel
  have hres0 := Submodule.disjoint_def.mp (disjoint_homogeneousSubmodule_wordFiltrationPrevious m)
    _ (lieCartanRestriction_mem_homogeneousSubmodule H p.2) hres
  -- Chevalley's restriction theorem is injective on the invariants, so `p = 0`
  have hp0 : p = 0 := Subtype.ext <|
    LieSubalgebra.lieCartanRestriction_injOn_lieInvariants H hinv (zero_mem _)
      (hres0.trans (map_zero _).symm)
  have hs0 : (s : U L) = 0 := by
    simp only [s, hp0, map_zero]
  simpa [hs0] using hsz

/-- **The Harish-Chandra projection detects the PBW degree**: a central element has PBW degree at
most `n` exactly when its Harish-Chandra projection has degree at most `n` in `S(H)`. -/
@[simp]
theorem hcProjection_mem_wordFiltration_iff {n : ℕ} {z : Subalgebra.center K (U L)} :
    hcProjection b z ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n ↔
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n := by
  refine ⟨fun hz ↦ ?_, hcProjection_mem_wordFiltration b⟩
  -- descend from some PBW degree `m` of `z`, one degree at a time, down to `n`
  obtain ⟨m, hm⟩ := UniversalEnvelopingAlgebra.exists_mem_pbwFiltration K L (z : U L)
  induction m with
  | zero => exact UniversalEnvelopingAlgebra.pbwFiltration_mono K L (Nat.zero_le n) hm
  | succ m ih =>
      rcases le_or_gt (m + 1) n with hmn | hnm
      · exact UniversalEnvelopingAlgebra.pbwFiltration_mono K L hmn hm
      · refine ih ?_
        rw [← UniversalEnvelopingAlgebra.pbwFiltrationPrevious_succ]
        refine mem_pbwFiltrationPrevious_of_hcProjection_mem b hm ?_
        rw [wordFiltrationPrevious_succ]
        exact wordFiltration_mono _ (Nat.le_of_lt_succ hnm) hz

/-- **The Harish-Chandra projection detects the strict PBW degree**: a central element has PBW
degree below `n` exactly when its Harish-Chandra projection has degree below `n` in `S(H)`. -/
@[simp]
theorem hcProjection_mem_wordFiltrationPrevious_iff {n : ℕ} {z : Subalgebra.center K (U L)} :
    hcProjection b z ∈ wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) n ↔
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltrationPrevious K L n := by
  cases n with
  | zero =>
      refine ⟨fun hz ↦ mem_pbwFiltrationPrevious_of_hcProjection_mem b ?_ hz,
        hcProjection_mem_wordFiltrationPrevious b⟩
      rw [wordFiltrationPrevious_zero, Submodule.mem_bot] at hz
      rw [← hcProjection_mem_wordFiltration_iff b, hz]
      exact zero_mem _
  | succ n =>
      rw [wordFiltrationPrevious_succ, UniversalEnvelopingAlgebra.pbwFiltrationPrevious_succ,
        hcProjection_mem_wordFiltration_iff]

/-- **The Harish-Chandra projection is injective**: a central element of `U(L)` is determined by
its Harish-Chandra projection. -/
theorem hcProjection_injective : Function.Injective (hcProjection b) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  have h := (hcProjection_mem_wordFiltrationPrevious_iff b (n := 0) (z := z)).mp
    (by rw [hz]; exact zero_mem _)
  rw [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_zero, Submodule.mem_bot] at h
  exact Subtype.ext h

/-- **A central element is determined by its central characters**: if `χ_lam(z) = χ_lam(w)` for
every weight `lam`, then `z = w`. -/
theorem eq_of_forall_vermaCentralCharacter_eq {z w : Subalgebra.center K (U L)}
    (h : ∀ lam : Module.Dual K H, vermaCentralCharacter b lam z = vermaCentralCharacter b lam w) :
    z = w :=
  hcProjection_injective b <| eq_of_forall_lift_apply_eq fun lam ↦ by
    rw [lift_hcProjection, lift_hcProjection, h]

/-- **The linear Harish-Chandra projection detects the PBW degree**: a central element has PBW
degree at most `n` exactly when its linear Harish-Chandra projection has degree at most `n`. -/
@[simp]
theorem hcProjectionLinear_mem_wordFiltration_iff {n : ℕ} {z : Subalgebra.center K (U L)} :
    hcProjectionLinear b z ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n ↔
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n := by
  rw [hcProjectionLinear_apply, _root_.SymmetricAlgebra.translation_mem_wordFiltration_iff,
    hcProjection_mem_wordFiltration_iff]

/-- **The linear Harish-Chandra projection is injective.** -/
theorem hcProjectionLinear_injective : Function.Injective (hcProjectionLinear b) := by
  intro z w h
  rw [hcProjectionLinear_apply, hcProjectionLinear_apply] at h
  exact hcProjection_injective b ((_root_.SymmetricAlgebra.translation _).injective h)

end TauCeti
