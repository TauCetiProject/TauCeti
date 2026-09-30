/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.Adjoin
import TauCeti.RepresentationTheory.Spin.OddStructure
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Representation
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation

/-!
# Irreducibility of the spin and half-spin modules over the orthogonal Lie algebra

A polarization identifies the split orthogonal matrix Lie algebra — `LieAlgebra.Orthogonal.typeB`
for an odd polarization, `LieAlgebra.Orthogonal.typeD` for an even one — with the quadratic
elements of the Clifford algebra, and through the Fock action these act on the spinor module
`S = ⋀·W`: this is the spin representation `TauCeti.SpinPolarizationData.typeBSpinLieRep` in type
`B`, and its two parity summands `TauCeti.SpinPolarizationData.typeDSpinPlusLieRep` and
`TauCeti.SpinPolarizationData.typeDSpinMinusLieRep` in type `D`.

This file proves that the operators of these Lie algebra representations generate the full
endomorphism algebra of the module, and deduces that every invariant subspace is `⊥` or everything:
the spin module and `S⁺` are irreducible, and so is `S⁻` whenever it is nonzero. The quadratic
elements generate the even Clifford subalgebra as an algebra
(`CliffordAlgebra.adjoin_coe_preimage_quadraticLieSubalgebra`), and the even subalgebra acts onto
the full endomorphism algebra of `S` in odd dimension (`TauCeti.evenSpinAction_surjective`) and of
each of `S⁺` and `S⁻` in even dimension (`TauCeti.spinPlusAction_surjective`,
`TauCeti.spinMinusAction_surjective`). The invariant-subspace dichotomy is then
`TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top`.

Irreducibility of the Spin *group* representations on the same modules is
`TauCeti/RepresentationTheory/Spin/Irreducible.lean`; the statements here are the Lie algebra
counterparts, and are what identifies the spin modules as irreducible highest weight modules once
their highest weight vectors are known. Nothing here needs the base field to be algebraically or
separably closed: only `2` has to be invertible.

As there, the invariant-subspace statements are in lattice form. `S⁻` is zero when `W = ⊥`, which
the dichotomy allows; combine it with `TauCeti.nontrivial_spinMinus`, whose hypothesis `P.W ≠ ⊥`
rules this out, for simplicity. `S` and `S⁺` always contain the scalars, so need no such hypothesis.

## Main results

* `TauCeti.SpinPolarizationData.adjoin_range_typeBSpinLieRep`: the type-`B` spin operators
  generate `Module.End K S`.
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_map_typeBSpinLieRep_le`: **the type-`B` spin
  module is irreducible.**
* `TauCeti.SpinPolarizationData.adjoin_range_typeDSpinPlusLieRep` and
  `TauCeti.SpinPolarizationData.adjoin_range_typeDSpinMinusLieRep`: the type-`D` half-spin
  operators generate `Module.End K S⁺` and `Module.End K S⁻`.
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_map_typeDSpinPlusLieRep_le`: **the even
  type-`D` half-spin module is irreducible.**
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_map_typeDSpinMinusLieRep_le`: the invariant-
  subspace dichotomy for the odd type-`D` half-spin module `S⁻`, which is therefore irreducible
  when `P.W ≠ ⊥` (`TauCeti.nontrivial_spinMinus`).

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §§20.1–20.2: the spin
  and half-spin representations of `𝔰𝔬(2n + 1)` and `𝔰𝔬(2n)`, and their irreducibility.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra Module

namespace TauCeti.SpinPolarizationData

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W) [Invertible (2 : K)]

/-- A Lie algebra acting through an isomorphism onto the quadratic Clifford elements, followed by
a surjective representation of the even subalgebra, generates the full endomorphism algebra. -/
private theorem adjoin_range_eq_top {L M : Type*} [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] (e : L ≃ₗ⁅K⁆ quadraticLieSubalgebra Q)
    (F : even Q →ₐ[K] Module.End K M) (hF : Function.Surjective F) (f : L → Module.End K M)
    (hf : ∀ x, f x = F ⟨e x, quadraticLieSubalgebra_le_even Q (e x).2⟩) :
    Algebra.adjoin K (Set.range f) = ⊤ := by
  have hrange : Set.range f =
      F '' (((↑) : even Q → CliffordAlgebra Q) ⁻¹' quadraticLieSubalgebra Q) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (e x).2, (hf x).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      have hx' : ((e x : quadraticLieSubalgebra Q) : CliffordAlgebra Q) = y :=
        congrArg Subtype.val hx
      exact ⟨x, (hf x).trans (congrArg F (Subtype.ext hx'))⟩
  rw [hrange, ← AlgHom.map_adjoin, adjoin_coe_preimage_quadraticLieSubalgebra, Algebra.map_top,
    (AlgHom.range_eq_top F).2 hF]

/-! ### Type `B` -/

section TypeB

variable (z : P.line) (hz : Q (z : V) = 1)

/-- **The type-`B` spin operators generate every endomorphism of the spinor module.** In odd
dimension the even Clifford subalgebra acts onto `Module.End K S`, and the quadratic elements
generate it. -/
theorem adjoin_range_typeBSpinLieRep :
    Algebra.adjoin K (Set.range (P.typeBSpinLieRep b z hz)) = ⊤ := by
  have := Module.Finite.of_basis (P.typeBBasis b z hz)
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  have hodd : Odd (finrank K V) := by
    rw [finrank_eq_card_basis (P.typeBBasis b z hz), Fintype.card_sum, Fintype.card_sum,
      Fintype.card_unit]
    exact ⟨Fintype.card ι, by ring⟩
  exact adjoin_range_eq_top (P.typeBQuadraticEquiv b z hz) (evenSpinAction Q P)
    (evenSpinAction_surjective P hodd) _ fun x => by
      rw [typeBSpinLieRep_apply, evenSpinAction_apply]

/-- **The type-`B` spin module is irreducible**: a subspace of `S = ⋀·W` invariant under every
element of the split odd orthogonal Lie algebra is `⊥` or all of `S`. -/
theorem eq_bot_or_eq_top_of_map_typeBSpinLieRep_le (N : Submodule K (ExteriorAlgebra K P.W))
    (hN : ∀ x, N.map (P.typeBSpinLieRep b z hz x) ≤ N) : N = ⊥ ∨ N = ⊤ :=
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top (P.adjoin_range_typeBSpinLieRep b z hz) <| by
    rintro _ ⟨x, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN x)

end TypeB

/-! ### Type `D` -/

section TypeD

/-- **The type-`D` half-spin operators generate every endomorphism of `S⁺`.** -/
theorem adjoin_range_typeDSpinPlusLieRep (hline : P.line = ⊥) :
    Algebra.adjoin K (Set.range (P.typeDSpinPlusLieRep b hline)) = ⊤ := by
  have := Module.Finite.of_basis (P.typeDBasis b hline)
  exact adjoin_range_eq_top (P.typeDQuadraticEquiv b hline) (spinPlusAction Q P hline)
    (spinPlusAction_surjective P hline) _ fun x => LinearMap.ext fun s => Subtype.ext <| by
      rw [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply, coe_spinPlusAction_apply]

/-- **The type-`D` half-spin operators generate every endomorphism of `S⁻`.** -/
theorem adjoin_range_typeDSpinMinusLieRep (hline : P.line = ⊥) :
    Algebra.adjoin K (Set.range (P.typeDSpinMinusLieRep b hline)) = ⊤ := by
  have := Module.Finite.of_basis (P.typeDBasis b hline)
  exact adjoin_range_eq_top (P.typeDQuadraticEquiv b hline) (spinMinusAction Q P hline)
    (spinMinusAction_surjective P hline) _ fun x => LinearMap.ext fun s => Subtype.ext <| by
      rw [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply, coe_spinMinusAction_apply]

/-- **The even type-`D` half-spin module is irreducible**: a subspace of `S⁺` invariant under
every element of the split even orthogonal Lie algebra is `⊥` or all of `S⁺`. -/
theorem eq_bot_or_eq_top_of_map_typeDSpinPlusLieRep_le (hline : P.line = ⊥)
    (N : Submodule K (spinPlus Q P)) (hN : ∀ x, N.map (P.typeDSpinPlusLieRep b hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top (P.adjoin_range_typeDSpinPlusLieRep b hline) <| by
    rintro _ ⟨x, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN x)

/-- **The invariant-subspace dichotomy for the odd type-`D` half-spin module**: a subspace of `S⁻`
invariant under every element of the split even orthogonal Lie algebra is `⊥` or all of `S⁻`. This
remains true when `S⁻` is zero; combine it with `TauCeti.nontrivial_spinMinus` to obtain
irreducibility when `P.W ≠ ⊥`. -/
theorem eq_bot_or_eq_top_of_map_typeDSpinMinusLieRep_le (hline : P.line = ⊥)
    (N : Submodule K (spinMinus Q P)) (hN : ∀ x, N.map (P.typeDSpinMinusLieRep b hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top (P.adjoin_range_typeDSpinMinusLieRep b hline) <| by
    rintro _ ⟨x, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN x)

end TypeD

end TauCeti.SpinPolarizationData
