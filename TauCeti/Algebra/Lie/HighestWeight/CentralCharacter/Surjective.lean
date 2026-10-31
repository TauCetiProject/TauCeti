/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.LeadingTerm
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Linear

/-!
# Surjectivity of the Harish-Chandra projection

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a splitting Cartan subalgebra and `b` a base of its
root system, with Weyl vector `ρ`. The Harish-Chandra projection
`TauCeti.hcProjection b : Z(U(L)) →ₐ[K] S(H)` takes values in the dot-invariants `S(H)^{W·}`, and
its linear normalization `TauCeti.hcProjectionLinear b`, the projection followed by translation by
`-ρ`, takes values in the Weyl invariants `S(H)^W`. This file proves that both are onto:

`(hcProjectionLinear b).range = S(H)^W`   and   `(hcProjection b).range = S(H)^{W·}`.

The proof is the degree induction of Harish-Chandra's theorem, with a degree bound on the
preimage: a Weyl invariant `q` of degree at most `n` is the image of a central element of PBW
degree at most `n` (`TauCeti.exists_mem_pbwFiltration_hcProjectionLinear_eq`). Its homogeneous
component `q_n` of degree `n` is again a Weyl invariant, so by Chevalley's restriction theorem
it is the restriction to `H` of a homogeneous invariant `p ∈ S(L)^L` of degree `n`. The PBW
symmetrization `z` of `p` is central, and the leading term of the Harish-Chandra projection is the
Chevalley restriction (`TauCeti.hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious`),
while translation by `-ρ` only changes lower-degree terms. So `hcProjectionLinear b z - q_n`, and
with it `q - hcProjectionLinear b z`, is a Weyl invariant of degree strictly less than `n`, to
which the induction hypothesis applies.

Injectivity, and hence the Harish-Chandra isomorphism `Z(U(L)) ≃ S(H)^W`, needs in addition that
the PBW symbol of a central element is a Lie invariant; it is not proved here.

## Main results

* `TauCeti.exists_mem_pbwFiltration_hcProjectionLinear_eq`: a Weyl invariant of degree at most `n`
  is the linear Harish-Chandra projection of a central element of PBW degree at most `n`.
* `TauCeti.range_hcProjectionLinear`: the linear Harish-Chandra projection is onto the Weyl
  invariants.
* `TauCeti.exists_mem_pbwFiltration_hcProjection_eq` and `TauCeti.range_hcProjection`: the same
  for the Harish-Chandra projection and the dot-invariants.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
-/

public section

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra

universe v

variable {K : Type} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L]
  [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-- **The leading term of a homogeneous Weyl invariant is attained.** A Weyl invariant `q`
homogeneous of degree `n` agrees, up to degree strictly less than `n`, with the linear
Harish-Chandra projection of a central element of PBW degree at most `n`: the symmetrization of a
homogeneous invariant of `S(L)` restricting to `q`. This is the inductive step of
`TauCeti.exists_mem_pbwFiltration_hcProjectionLinear_eq`. -/
private theorem exists_mem_pbwFiltration_hcProjectionLinear_sub_mem_wordFiltrationPrevious {n : ℕ}
    {q : _root_.SymmetricAlgebra K H} (hq : q ∈ linearInvariants H)
    (hqn : q ∈ homogeneousSubmodule K H n) :
    ∃ z : Subalgebra.center K (U L),
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n ∧
        hcProjectionLinear b z - q ∈
          wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) n := by
  have hn : IsUnit (n.factorial : K) := (Nat.cast_ne_zero.2 n.factorial_ne_zero).isUnit
  -- Chevalley: `q` is the restriction of a homogeneous invariant `p` of degree `n`
  obtain ⟨p, ⟨hp, hpn⟩, rfl⟩ :=
    LieSubalgebra.linearInvariants_inf_homogeneousSubmodule_le_map_lieInvariants H n ⟨hq, hqn⟩
  have hz := UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_pbwFiltration K L n hn
    ⟨p, hpn⟩
  let z : Subalgebra.center K (U L) :=
    ⟨_, UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center K L n hn
      (p := ⟨p, hpn⟩) hp⟩
  refine ⟨z, hz, ?_⟩
  -- translation by `-ρ` changes `hcProjection b z` only in degree `< n`, and the leading term of
  -- `hcProjection b z` is the restriction of `p`
  have htrans := _root_.SymmetricAlgebra.translation_sub_self_mem_wordFiltrationPrevious
    (-weylVector (IsKilling.rootSystem H) b) (hcProjection_mem_wordFiltration b (z := z) hz)
  have hlead := hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious b hn ⟨p, hpn⟩
    (z := z) rfl
  rw [hcProjectionLinear_apply]
  simpa only [sub_add_sub_cancel, AlgHom.toLinearMap_apply] using add_mem htrans hlead

/-- The induction behind `TauCeti.exists_mem_pbwFiltration_hcProjectionLinear_eq`, stated with the
preceding filtration steps so that degree zero is the base case. -/
private theorem exists_mem_pbwFiltrationPrevious_hcProjectionLinear_eq (n : ℕ)
    {q : _root_.SymmetricAlgebra K H} (hq : q ∈ linearInvariants H)
    (hqn : q ∈ wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) n) :
    ∃ z : Subalgebra.center K (U L),
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltrationPrevious K L n ∧
        hcProjectionLinear b z = q := by
  induction n generalizing q with
  | zero =>
    rw [wordFiltrationPrevious_zero, Submodule.mem_bot] at hqn
    exact ⟨0, by simp, by rw [map_zero, hqn]⟩
  | succ n ih =>
    rw [wordFiltrationPrevious_succ] at hqn
    -- the top homogeneous component of `q` is a Weyl invariant of degree `n`
    set qn := (DirectSum.decompose (homogeneousSubmodule K H) q n : _root_.SymmetricAlgebra K H)
    obtain ⟨z₁, hz₁, hz₁q⟩ :=
      exists_mem_pbwFiltration_hcProjectionLinear_sub_mem_wordFiltrationPrevious b
        (isHomogeneous_linearInvariants n hq) (SetLike.coe_mem _ : qn ∈ _)
    -- what remains is a Weyl invariant of degree `< n`
    have hrest : q - hcProjectionLinear b z₁ ∈
        wordFiltrationPrevious (_root_.SymmetricAlgebra.ι K H) n := by
      simpa only [sub_sub_sub_cancel_right] using
        sub_mem (sub_decompose_mem_wordFiltrationPrevious hqn) hz₁q
    obtain ⟨z₂, hz₂, hz₂q⟩ := ih (sub_mem hq (hcProjectionLinear_mem_linearInvariants b z₁)) hrest
    refine ⟨z₁ + z₂, ?_, ?_⟩
    · rw [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_def] at hz₂
      rw [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_succ]
      rw [UniversalEnvelopingAlgebra.pbwFiltration_def] at hz₁ ⊢
      exact add_mem hz₁ (wordFiltrationPrevious_le _ n hz₂)
    · rw [map_add, hz₂q, add_sub_cancel]

/-- **Harish-Chandra surjectivity with a degree bound.** A Weyl invariant `q ∈ S(H)^W` of degree
at most `n` is the linear Harish-Chandra projection of a central element of `U(L)` of PBW degree
at most `n`. -/
theorem exists_mem_pbwFiltration_hcProjectionLinear_eq {n : ℕ} {q : _root_.SymmetricAlgebra K H}
    (hq : q ∈ linearInvariants H) (hqn : q ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n) :
    ∃ z : Subalgebra.center K (U L),
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n ∧ hcProjectionLinear b z = q := by
  rw [← wordFiltrationPrevious_succ] at hqn
  simpa only [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_succ] using
    exists_mem_pbwFiltrationPrevious_hcProjectionLinear_eq b (n + 1) hq hqn

/-- **The linear Harish-Chandra projection is onto the Weyl invariants**: its range is
`S(H)^W`. -/
theorem range_hcProjectionLinear : (hcProjectionLinear b).range = linearInvariants H := by
  refine le_antisymm (fun _ ⟨z, hz⟩ ↦ hz ▸ hcProjectionLinear_mem_linearInvariants b z)
    fun q hq ↦ ?_
  -- every element of `S(H)` has finite degree
  obtain ⟨n, hn⟩ := exists_mem_wordFiltration_of_iSup_eq_top (_root_.SymmetricAlgebra.ι K H)
    (by rw [iSup_wordFiltration_eq_adjoin, TauCeti.SymmetricAlgebra.adjoin_range_ι]; rfl) q
  obtain ⟨z, -, hz⟩ := exists_mem_pbwFiltration_hcProjectionLinear_eq b hq hn
  exact (AlgHom.mem_range _).2 ⟨z, hz⟩

/-- **Harish-Chandra surjectivity with a degree bound, dot form.** A dot-invariant
`q ∈ S(H)^{W·}` of degree at most `n` is the Harish-Chandra projection of a central element of
`U(L)` of PBW degree at most `n`. -/
theorem exists_mem_pbwFiltration_hcProjection_eq {n : ℕ} {q : _root_.SymmetricAlgebra K H}
    (hq : q ∈ dotInvariants b) (hqn : q ∈ wordFiltration (_root_.SymmetricAlgebra.ι K H) n) :
    ∃ z : Subalgebra.center K (U L),
      (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n ∧ hcProjection b z = q := by
  obtain ⟨z, hz, hzq⟩ := exists_mem_pbwFiltration_hcProjectionLinear_eq b
    ((translation_neg_weylVector_mem_linearInvariants_iff b).2 hq)
    ((_root_.SymmetricAlgebra.translation_mem_wordFiltration_iff _).2 hqn)
  refine ⟨z, hz,
    (_root_.SymmetricAlgebra.translation (-weylVector (IsKilling.rootSystem H) b)).injective ?_⟩
  rwa [← hcProjectionLinear_apply]

/-- **The Harish-Chandra projection is onto the dot-invariants**: its range is `S(H)^{W·}`. -/
theorem range_hcProjection : (hcProjection b).range = dotInvariants b := by
  refine le_antisymm (fun _ ⟨z, hz⟩ ↦ hz ▸ hcProjection_mem_dotInvariants z) fun q hq ↦ ?_
  obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 <| (range_hcProjectionLinear b).ge
    ((translation_neg_weylVector_mem_linearInvariants_iff b).2 hq)
  refine (AlgHom.mem_range _).2
    ⟨z, (_root_.SymmetricAlgebra.translation (-weylVector (IsKilling.rootSystem H) b)).injective ?_⟩
  rwa [← hcProjectionLinear_apply]

end TauCeti
