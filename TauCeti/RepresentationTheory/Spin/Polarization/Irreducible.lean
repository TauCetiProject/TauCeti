/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.Adjoin
import TauCeti.Algebra.Lie.Basic
import TauCeti.RepresentationTheory.Spin.OddStructure
public import TauCeti.RepresentationTheory.Spin.Polarization.SkewAdjoint

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
(`CliffordAlgebra.adjoin_coe_preimage_quadraticLieSubalgebra_eq_top`), and the even subalgebra acts
onto the full endomorphism algebra of `S` in odd dimension (`TauCeti.evenSpinAction_surjective`)
and of each of `S⁺` and `S⁻` in even dimension (`TauCeti.spinPlusAction_surjective`,
`TauCeti.spinMinusAction_surjective`). The invariant-subspace dichotomy is then
`TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top`.

The same argument applies without coordinates to the spin representation
`TauCeti.SpinPolarizationData.soSpinLieRep` of the orthogonal Lie algebra
`skewAdjointLieSubalgebra (polarBilin Q)` of a finite-dimensional polarized space, through the
quadratic realization `CliffordAlgebra.soEquivQuadratic`: the spin module is irreducible in odd
dimension, and the half-spin modules `TauCeti.SpinPolarizationData.soSpinPlusLieRep` and
`TauCeti.SpinPolarizationData.soSpinMinusLieRep` are irreducible in even dimension, the second when
it is nonzero. Unlike the type-`B` coordinate model, the odd-dimensional statement takes no
unit-length remainder vector as an argument. This removes a choice, not a hypothesis: the remainder
coordinate squares to `Q` and is onto
(`TauCeti.SpinPolarizationData.lineCoordinate_surjective_of_ne_bot`), so such a vector always
exists.

Irreducibility of the Spin *group* representations on the same modules is
`TauCeti/RepresentationTheory/Spin/Irreducible.lean`; the statements here are the Lie algebra
counterparts, and are what identifies the spin modules as irreducible highest weight modules once
their highest weight vectors are known. Nothing here needs the base field to be algebraically or
separably closed: only `2` has to be invertible.

The invariant-subspace statements are first proved in lattice form. They are then packaged as
`LieModule.IsIrreducible` propositions for the type-`B` spin action and the type-`D` half-spin
actions, so highest-weight uniqueness can consume them directly. `S⁻` is zero when `W = ⊥`, which
the lattice dichotomy allows; its packaged theorem therefore assumes `P.W ≠ ⊥`, exactly as
`TauCeti.nontrivial_spinMinus` does. `S` and `S⁺` always contain the scalars, so need no such
hypothesis.

## Main results

* `TauCeti.SpinPolarizationData.adjoin_range_typeBSpinLieRep_eq_top`: the type-`B` spin operators
  generate `Module.End K S`.
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_map_typeBSpinLieRep_le`: **the type-`B` spin
  module is irreducible.**
* `TauCeti.SpinPolarizationData.isIrreducible_typeBSpinLieRep`: the type-`B` dichotomy packaged as
  an irreducible Lie module for the spin action.
* `TauCeti.SpinPolarizationData.adjoin_range_typeDSpinPlusLieRep_eq_top` and
  `TauCeti.SpinPolarizationData.adjoin_range_typeDSpinMinusLieRep_eq_top`: the type-`D` half-spin
  operators generate `Module.End K S⁺` and `Module.End K S⁻`.
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_map_typeDSpinPlusLieRep_le`: **the even
  type-`D` half-spin module is irreducible.**
* `TauCeti.SpinPolarizationData.eq_bot_or_eq_top_of_map_typeDSpinMinusLieRep_le`: the invariant-
  subspace dichotomy for the odd type-`D` half-spin module `S⁻`, which is therefore irreducible
  when `P.W ≠ ⊥` (`TauCeti.nontrivial_spinMinus`).
* `TauCeti.SpinPolarizationData.isIrreducible_typeDSpinPlusLieRep` and
  `TauCeti.SpinPolarizationData.isIrreducible_typeDSpinMinusLieRep`: the two dichotomies packaged
  as irreducible Lie modules for their respective half-spin actions.
* `TauCeti.SpinPolarizationData.isIrreducible_soSpinLieRep`,
  `TauCeti.SpinPolarizationData.isIrreducible_soSpinPlusLieRep` and
  `TauCeti.SpinPolarizationData.isIrreducible_soSpinMinusLieRep`: the coordinate-free statements for
  `𝔰𝔬(Q)`.

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
    (hf : ∀ x, f x = F ⟨e x, quadraticLieSubalgebra_le_even Q (e x).property⟩) :
    Algebra.adjoin K (Set.range f) = ⊤ := by
  have hrange : Set.range f =
      F '' (((↑) : even Q → CliffordAlgebra Q) ⁻¹' quadraticLieSubalgebra Q) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (e x).property, (hf x).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      have hx' : ((e x : quadraticLieSubalgebra Q) : CliffordAlgebra Q) = y :=
        congrArg Subtype.val hx
      exact ⟨x, (hf x).trans (congrArg F (Subtype.ext hx'))⟩
  rw [hrange, ← AlgHom.map_adjoin, adjoin_coe_preimage_quadraticLieSubalgebra_eq_top,
    Algebra.map_top, (AlgHom.range_eq_top F).2 hF]

/-! ### Type `B` -/

section TypeB

variable (z : P.line) (hz : Q (z : V) = 1)

/-- **The type-`B` spin operators generate every endomorphism of the spinor module.** In odd
dimension the even Clifford subalgebra acts onto `Module.End K S`, and the quadratic elements
generate it. -/
@[simp]
theorem adjoin_range_typeBSpinLieRep_eq_top :
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
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top (P.adjoin_range_typeBSpinLieRep_eq_top b z hz) <| by
    rintro _ ⟨x, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN x)

/-- **The type-`B` spin Lie module is irreducible.** The action is pulled back along
`P.typeBSpinLieRep b z hz`; the spinor module is always nonzero because it contains the scalar
vector. -/
theorem isIrreducible_typeBSpinLieRep :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeB ι K)
      (ExteriorAlgebra K P.W) :=
  LieModule.isIrreducible_compLieHom_of_eq_bot_or_eq_top (P.typeBSpinLieRep b z hz)
    (P.eq_bot_or_eq_top_of_map_typeBSpinLieRep_le b z hz)

end TypeB

/-! ### Type `D` -/

section TypeD

/-- **The type-`D` half-spin operators generate every endomorphism of `S⁺`.** -/
@[simp]
theorem adjoin_range_typeDSpinPlusLieRep_eq_top (hline : P.line = ⊥) :
    Algebra.adjoin K (Set.range (P.typeDSpinPlusLieRep b hline)) = ⊤ := by
  have := Module.Finite.of_basis (P.typeDBasis b hline)
  exact adjoin_range_eq_top (P.typeDQuadraticEquiv b hline) (spinPlusAction Q P hline)
    (spinPlusAction_surjective P hline) _ fun x => LinearMap.ext fun s => Subtype.ext <| by
      rw [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply, coe_spinPlusAction_apply]

/-- **The type-`D` half-spin operators generate every endomorphism of `S⁻`.** -/
@[simp]
theorem adjoin_range_typeDSpinMinusLieRep_eq_top (hline : P.line = ⊥) :
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
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top
    (P.adjoin_range_typeDSpinPlusLieRep_eq_top b hline) <| by
    rintro _ ⟨x, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN x)

/-- **The invariant-subspace dichotomy for the odd type-`D` half-spin module**: a subspace of `S⁻`
invariant under every element of the split even orthogonal Lie algebra is `⊥` or all of `S⁻`. This
remains true when `S⁻` is zero; combine it with `TauCeti.nontrivial_spinMinus` to obtain
irreducibility when `P.W ≠ ⊥`. -/
theorem eq_bot_or_eq_top_of_map_typeDSpinMinusLieRep_le (hline : P.line = ⊥)
    (N : Submodule K (spinMinus Q P)) (hN : ∀ x, N.map (P.typeDSpinMinusLieRep b hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top
    (P.adjoin_range_typeDSpinMinusLieRep_eq_top b hline) <| by
    rintro _ ⟨x, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN x)

/-- **The even type-`D` half-spin Lie module is irreducible.** The action is pulled back along
`P.typeDSpinPlusLieRep b hline`; the even half-spin space is always nonzero because it contains
the scalar vector. -/
theorem isIrreducible_typeDSpinPlusLieRep (hline : P.line = ⊥) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) := by
  let _ : Nontrivial (spinPlus Q P) := nontrivial_spinPlus P
  exact LieModule.isIrreducible_compLieHom_of_eq_bot_or_eq_top
    (P.typeDSpinPlusLieRep b hline) (P.eq_bot_or_eq_top_of_map_typeDSpinPlusLieRep_le b hline)

/-- **The odd type-`D` half-spin Lie module is irreducible when it is nonzero.** The action is
pulled back along `P.typeDSpinMinusLieRep b hline`; the hypothesis `P.W ≠ ⊥` is necessary
because the odd half-spin space vanishes when the isotropic summand does. -/
theorem isIrreducible_typeDSpinMinusLieRep (hline : P.line = ⊥) (hW : P.W ≠ ⊥) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) := by
  let _ : Nontrivial (spinMinus Q P) := nontrivial_spinMinus P hW
  exact LieModule.isIrreducible_compLieHom_of_eq_bot_or_eq_top
    (P.typeDSpinMinusLieRep b hline) (P.eq_bot_or_eq_top_of_map_typeDSpinMinusLieRep_le b hline)

end TypeD

/-! ### The orthogonal Lie algebra `𝔰𝔬(Q)` -/

section SkewAdjoint

variable [FiniteDimensional K V]

/-- **The spin operators of `𝔰𝔬(Q)` generate every endomorphism of the spinor module in odd
dimension.** -/
@[simp]
theorem adjoin_range_soSpinLieRep_eq_top (hodd : Odd (finrank K V)) :
    Algebra.adjoin K (Set.range P.soSpinLieRep) = ⊤ := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  have hQ := P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)
  exact adjoin_range_eq_top (soEquivQuadratic Q hQ) (evenSpinAction Q P)
    (evenSpinAction_surjective P hodd) _ fun f => by
      rw [P.soSpinLieRep_apply hQ, evenSpinAction_apply]

/-- **The spin module of `𝔰𝔬(Q)` is irreducible in odd dimension**: a subspace of `S = ⋀·W`
invariant under every skew-adjoint endomorphism is `⊥` or all of `S`. -/
theorem eq_bot_or_eq_top_of_map_soSpinLieRep_le (hodd : Odd (finrank K V))
    (N : Submodule K (ExteriorAlgebra K P.W)) (hN : ∀ f, N.map (P.soSpinLieRep f) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top (P.adjoin_range_soSpinLieRep_eq_top hodd) <| by
    rintro _ ⟨f, rfl⟩
    exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN f)

/-- **The spin Lie module of `𝔰𝔬(Q)` is irreducible in odd dimension.** The action is pulled back
along `P.soSpinLieRep`. In positive even dimension the two half-spin summands are proper
invariant subspaces, so the hypothesis cannot be dropped there; in dimension zero the spinor module
is the one-dimensional `⋀·0`, which is irreducible. -/
theorem isIrreducible_soSpinLieRep (hodd : Odd (finrank K V)) :
    letI : LieRingModule (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ P.soSpinLieRep
    letI : LieModule K (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ P.soSpinLieRep
    LieModule.IsIrreducible K (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
      (ExteriorAlgebra K P.W) :=
  LieModule.isIrreducible_compLieHom_of_eq_bot_or_eq_top P.soSpinLieRep
    (P.eq_bot_or_eq_top_of_map_soSpinLieRep_le hodd)

/-- **The even half-spin operators of `𝔰𝔬(Q)` generate every endomorphism of `S⁺`.** -/
@[simp]
theorem adjoin_range_soSpinPlusLieRep_eq_top (hline : P.line = ⊥) :
    Algebra.adjoin K (Set.range (P.soSpinPlusLieRep hline)) = ⊤ := by
  have hQ := P.nondegenerate_of_line_eq_bot hline
  exact adjoin_range_eq_top (soEquivQuadratic Q hQ) (spinPlusAction Q P hline)
    (spinPlusAction_surjective P hline) _ fun f => LinearMap.ext fun s => Subtype.ext <| by
      rw [coe_soSpinPlusLieRep_apply, P.soSpinLieRep_apply hQ, coe_spinPlusAction_apply]

/-- **The odd half-spin operators of `𝔰𝔬(Q)` generate every endomorphism of `S⁻`.** -/
@[simp]
theorem adjoin_range_soSpinMinusLieRep_eq_top (hline : P.line = ⊥) :
    Algebra.adjoin K (Set.range (P.soSpinMinusLieRep hline)) = ⊤ := by
  have hQ := P.nondegenerate_of_line_eq_bot hline
  exact adjoin_range_eq_top (soEquivQuadratic Q hQ) (spinMinusAction Q P hline)
    (spinMinusAction_surjective P hline) _ fun f => LinearMap.ext fun s => Subtype.ext <| by
      rw [coe_soSpinMinusLieRep_apply, P.soSpinLieRep_apply hQ, coe_spinMinusAction_apply]

/-- **The even half-spin Lie module of `𝔰𝔬(Q)` is irreducible.** It is always nonzero, since it
contains the scalar spinors. -/
theorem isIrreducible_soSpinPlusLieRep (hline : P.line = ⊥) :
    letI : LieRingModule (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.soSpinPlusLieRep hline)
    letI : LieModule K (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.soSpinPlusLieRep hline)
    LieModule.IsIrreducible K (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
      (spinPlus Q P) := by
  let _ : Nontrivial (spinPlus Q P) := nontrivial_spinPlus P
  exact LieModule.isIrreducible_compLieHom_of_eq_bot_or_eq_top (P.soSpinPlusLieRep hline)
    fun N hN => TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top
      (P.adjoin_range_soSpinPlusLieRep_eq_top hline) <| by
        rintro _ ⟨f, rfl⟩
        exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN f)

/-- **The odd half-spin Lie module of `𝔰𝔬(Q)` is irreducible when it is nonzero.** The hypothesis
`P.W ≠ ⊥` is necessary because the odd half-spin space vanishes when the isotropic summand
does. -/
theorem isIrreducible_soSpinMinusLieRep (hline : P.line = ⊥) (hW : P.W ≠ ⊥) :
    letI : LieRingModule (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.soSpinMinusLieRep hline)
    letI : LieModule K (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.soSpinMinusLieRep hline)
    LieModule.IsIrreducible K (skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
      (spinMinus Q P) := by
  let _ : Nontrivial (spinMinus Q P) := nontrivial_spinMinus P hW
  exact LieModule.isIrreducible_compLieHom_of_eq_bot_or_eq_top (P.soSpinMinusLieRep hline)
    fun N hN => TauCeti.eq_bot_or_eq_top_of_adjoin_eq_top
      (P.adjoin_range_soSpinMinusLieRep_eq_top hline) <| by
        rintro _ ⟨f, rfl⟩
        exact (Module.End.mem_invtSubmodule_iff_map_le _).2 (hN f)

end SkewAdjoint

end TauCeti.SpinPolarizationData
