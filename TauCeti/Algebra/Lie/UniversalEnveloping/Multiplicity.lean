/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.Algebra.Lie.UniversalEnveloping.Isotypic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module
public import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# The multiplicity of an irreducible Lie module, through the enveloping algebra

`LieModule.isotypicMultiplicity` of `TauCeti/Algebra/Lie/Multiplicity.lean` is defined and computed
without the universal enveloping algebra, in the same way as the Lie isotypy interface of
`TauCeti/Algebra/Lie/Isotypic.lean`. This file connects it to the ring-level multiplicity theory of
`TauCeti/RingTheory/Semisimple/Multiplicity.lean` across the enveloping-algebra dictionary, so that
the two are one theory rather than two parallel ones: the general invariant is the finrank of the
space of `U(L)`-linear maps `S → M`, and over an algebraically closed field, for a finite
decomposition of `M` into simple `U(L)`-modules and a finite-dimensional simple `S`, it is the
number of factors isomorphic to `S`.

The translation is `TauCeti.UniversalEnvelopingAlgebra.lieModuleHomEquiv`: a morphism of Lie
modules is exactly a `U(L)`-linear map, `R`-linearly in the morphism, so the two morphism spaces
have the same finrank.

## Main results

* `LieModule.isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul`: the invariant is the
  finrank of the space of `U(L)`-linear maps.
* `LieModule.isotypicMultiplicity_eq_natCard_of_linearEquiv_pi`: for a finite decomposition of `M`
  into simple `U(L)`-modules, the multiplicity is the ring-level count of
  `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`.
* `LieModule.nonempty_lieModuleEquiv_isotypicComponent`: **an isotypic component is a finite
  power of its irreducible type, with exponent its multiplicity**;
  `LieModule.nonempty_lieModuleEquiv_of_isotypicComponent_eq_top` and
  `LieModule.nonempty_lieModuleEquiv_of_isIsotypicOfType` give the corresponding decomposition
  of the whole module.
* `LieModule.finrank_isotypicComponent`: **the dimension of an isotypic component is the
  multiplicity times the dimension of its type**;
  `LieModule.finrank_of_isotypicComponent_eq_top`: for a module its own isotypic component, that
  dimension count is the dimension of the module; and
  `LieModule.finrank_of_isIsotypicOfType`: the same for a completely reducible module which is
  itself isotypic.

## The structure of an isotypic component

The structural equivalence and its numerical consequence are statements of Lie module theory
alone — no enveloping algebra occurs in them — but their proofs run through the dictionary, which
is why they live here rather than in `TauCeti/Algebra/Lie/Multiplicity.lean`: the isotypic
component is carried to Mathlib's `isotypicComponent` over `U(L)` by
`LieModule.lieSubmoduleOrderIso_isotypicComponent`, where
`TauCeti.nonempty_linearEquiv_isotypicComponent` identifies it with the appropriate power of its
type and `TauCeti.finrank_isotypicComponent` computes its dimension. Finite-dimensionality of `M` is
the one hypothesis those statements need: an irreducible `S` that is not finite-dimensional has
multiplicity `0` and trivial component in a finite-dimensional `M`, so the dictionary is only
used when `S` is finite-dimensional. Complete reducibility of `M` is not needed either, an
isotypic component being a sum of copies of `S` in any case. It is needed only to deduce that an
isotypic module is exhausted by this component.
-/

public section

open UniversalEnvelopingAlgebra
open scoped DirectSum

universe u v w w₁

namespace LieModule

open TauCeti.UniversalEnvelopingAlgebra

section Bridge

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module (_root_.UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) M]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- **The invariant is the finrank of an enveloping-algebra morphism space.** For compatible
`U(L)`-actions, `LieModule.isotypicMultiplicity R L M S` is the finrank of the space of
`U(L)`-linear maps `S → M`. -/
theorem isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type w₁) [AddCommGroup S] [Module R S] [LieRingModule L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) :
    isotypicMultiplicity R L M S = Module.finrank R (S →ₗ[U] M) :=
  (isotypicMultiplicity_def R L M S).trans (lieModuleHomEquiv hS hM).finrank_eq

end Bridge

section Count

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [Module (_root_.UniversalEnvelopingAlgebra K L) M]
variable [IsScalarTower K (_root_.UniversalEnvelopingAlgebra K L) M]

local notation "U" => _root_.UniversalEnvelopingAlgebra K L

/-- **The multiplicity is the ring-level multiplicity.** If a compatible `U(L)`-module `M` is a
finite product of simple `U(L)`-modules, the multiplicity of a simple, finite-dimensional `S`
counts the factors isomorphic to `S`. This is
`TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi` read through the enveloping-algebra
dictionary, so the Lie-level count of
`LieModule.isotypicMultiplicity_eq_ncard_of_isInternal` and the ring-level one compute the same
number. -/
theorem isotypicMultiplicity_eq_natCard_of_linearEquiv_pi
    (hM : ∀ (x : L) (m : M), ι K x • m = ⁅x, m⁆)
    (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [Module U S] [IsScalarTower K U S] [IsSimpleModule U S] [FiniteDimensional K S]
    (hS : ∀ (x : L) (s : S), ι K x • s = ⁅x, s⁆)
    {κ : Type*} [Finite κ] {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    [∀ i, Module U (N i)] [∀ i, IsScalarTower K U (N i)] [∀ i, IsSimpleModule U (N i)]
    (e : M ≃ₗ[U] ∀ i, N i) :
    isotypicMultiplicity K L M S = Nat.card {i // Nonempty (S ≃ₗ[U] N i)} := by
  rw [isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul hM S hS,
    TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi e]

end Count

/-! ### The structure of an isotypic component -/

section IsotypicComponent

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [FiniteDimensional K M]

open Module (finrank)

local notation "U" => _root_.UniversalEnvelopingAlgebra K L

omit [IsAlgClosed K] [LieAlgebra K L] [LieModule K L M] in
/-- **A finite-dimensional module has no component of an infinite-dimensional irreducible type.**
A morphism out of an irreducible `S` into a finite-dimensional module is zero unless `S` is itself
finite-dimensional, since its kernel is `⊥` or `⊤`. -/
theorem subsingleton_lieModuleHom_of_not_finite (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] [IsIrreducible K L S] (hS : ¬ Module.Finite K S) :
    Subsingleton (S →ₗ⁅K,L⁆ M) := by
  have h0 : ∀ f : S →ₗ⁅K,L⁆ M, f = 0 := fun f ↦ by
    rcases eq_bot_or_eq_top f.ker with h | h
    · exact absurd (Module.Finite.of_injective f.toLinearMap
        ((LieModuleHom.ker_eq_bot f).mp h)) hS
    · exact LieModuleHom.ext fun x ↦ by
        have : x ∈ f.ker := h ▸ LieSubmodule.mem_top x
        simpa using this
  exact ⟨fun f g ↦ (h0 f).trans (h0 g).symm⟩

omit [IsAlgClosed K] in
/-- The multiplicity in a finite-dimensional module of an infinite-dimensional irreducible type
is `0`. -/
theorem isotypicMultiplicity_eq_zero_of_not_finite (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] [IsIrreducible K L S] (hS : ¬ Module.Finite K S) :
    isotypicMultiplicity K L M S = 0 :=
  have := subsingleton_lieModuleHom_of_not_finite (K := K) (L := L) (M := M) S hS
  (isotypicMultiplicity_def K L M S).trans Module.finrank_zero_of_subsingleton

omit [IsAlgClosed K] [LieAlgebra K L] [LieModule K L M] in
/-- A finite-dimensional module has trivial isotypic component for an infinite-dimensional type. -/
theorem isotypicComponent_eq_bot_of_not_finite (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] (hS : ¬ Module.Finite K S) :
    isotypicComponent K L M S = ⊥ := by
  rw [isotypicComponent_def, sSup_eq_bot]
  rintro P ⟨e⟩
  exact absurd (Module.Finite.equiv e.toLinearEquiv) hS

/-- **An isotypic component is the power of its irreducible type counted by its multiplicity.**
For a finite-dimensional Lie module `M` over an algebraically closed field and an
irreducible `S`, its `S`-isotypic component is Lie-equivalent to
the direct sum of `isotypicMultiplicity K L M S` copies of `S`.

The equivalence is obtained from the corresponding ring-level result for `U(L)`: the submodule
dictionary identifies the two isotypic components, the homomorphism dictionary identifies their
multiplicities, and the equivalence dictionary transports the resulting `U(L)`-linear
equivalence back to Lie modules. Complete reducibility of `M` is not required. -/
theorem nonempty_lieModuleEquiv_isotypicComponent
    (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [LieModule K L S] [IsIrreducible K L S] :
    Nonempty (isotypicComponent K L M S ≃ₗ⁅K,L⁆
      (⨁ (_ : Fin (isotypicMultiplicity K L M S)), S)) := by
  by_cases hfin : Module.Finite K S
  swap
  · rw [isotypicComponent_eq_bot_of_not_finite (K := K) (L := L) (M := M) S hfin,
      isotypicMultiplicity_eq_zero_of_not_finite (K := K) (L := L) (M := M) S hfin]
    exact ⟨{ (0 : _ →ₗ⁅K,L⁆ _) with
      invFun := 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }⟩
  let := asModule K L M
  let := isScalarTower_asModule K L M
  let := asModule K L S
  let := isScalarTower_asModule K L S
  have hM := asModule_ι_smul K L M
  have hS := asModule_ι_smul K L S
  let : IsSimpleModule U S := (isIrreducible_iff_isSimpleModule hS).mp inferInstance
  let := asModule K L (isotypicComponent K L M S)
  let := isScalarTower_asModule K L (isotypicComponent K L M S)
  obtain ⟨e⟩ := TauCeti.nonempty_linearEquiv_isotypicComponent
    (k := K) (A := U) (M := M) (S := S)
  rw [← lieSubmoduleOrderIso_isotypicComponent hM S hS,
    ← isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul hM S hS] at e
  have hsum : ∀ (x : L) (s : ⨁ (_ : Fin (isotypicMultiplicity K L M S)), S),
      ι K x • s = ⁅x, s⁆ := by
    intro x s
    ext i
    simp only [DirectSum.lie_module_bracket_apply]
    exact hS x (s i)
  exact ⟨(lieModuleEquivEquivLinearEquiv
    (asModule_ι_smul K L (isotypicComponent K L M S))
    hsum).symm
      ((lieSubmoduleLinearEquiv hM (isotypicComponent K L M S)).trans e |>.trans
        (DFinsupp.linearEquivFunOnFintype (R := U)).symm)⟩

/-- **A module exhausted by an isotypic component is the corresponding power of its type.**
If the `S`-isotypic component is all of `M`, then `M` is Lie-equivalent to the direct sum of
`isotypicMultiplicity K L M S` copies of `S`. No complete reducibility hypothesis is needed. -/
theorem nonempty_lieModuleEquiv_of_isotypicComponent_eq_top
    (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [LieModule K L S] [IsIrreducible K L S]
    (h : isotypicComponent K L M S = ⊤) :
    Nonempty (M ≃ₗ⁅K,L⁆ (⨁ (_ : Fin (isotypicMultiplicity K L M S)), S)) := by
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_isotypicComponent (K := K) (L := L) (M := M) S
  rw [h] at e
  exact ⟨(LieModuleEquiv.ofTop K L M).symm.trans e⟩

/-- **A completely reducible isotypic module is the power of its irreducible type counted by its
multiplicity.** If every irreducible Lie submodule of `M` is equivalent to `S`, then `M` is
Lie-equivalent to the direct sum of `isotypicMultiplicity K L M S` copies of `S`. -/
theorem nonempty_lieModuleEquiv_of_isIsotypicOfType
    (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [LieModule K L S] [IsIrreducible K L S]
    [ComplementedLattice (LieSubmodule K L M)] (h : IsIsotypicOfType K L M S) :
    Nonempty (M ≃ₗ⁅K,L⁆ (⨁ (_ : Fin (isotypicMultiplicity K L M S)), S)) :=
  nonempty_lieModuleEquiv_of_isotypicComponent_eq_top (K := K) (L := L) S
    ((isotypicComponent_eq_top_iff S).mpr h)

/-- **The dimension of an isotypic component is the multiplicity times the dimension of its
type.** For a finite-dimensional Lie module `M` over an algebraically closed field and an
irreducible `S`, the `S`-isotypic component of `M`
(`LieModule.isotypicComponent`) has dimension `m · dim S`, where `m` is the multiplicity
`LieModule.isotypicMultiplicity`.

This is the counted form of the statement that the isotypic component is `S^{⊕ m}`; nothing is
assumed about `M` beyond finite-dimensionality, since the isotypic component is a sum of copies
of `S` whether or not `M` itself is completely reducible. -/
theorem finrank_isotypicComponent (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [LieModule K L S] [IsIrreducible K L S] :
    finrank K (isotypicComponent K L M S) = isotypicMultiplicity K L M S * finrank K S := by
  by_cases hfin : Module.Finite K S
  swap
  · rw [isotypicComponent_eq_bot_of_not_finite (K := K) (L := L) (M := M) S hfin,
      isotypicMultiplicity_eq_zero_of_not_finite (K := K) (L := L) (M := M) S hfin]
    rw [zero_mul]
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_isotypicComponent (K := K) (L := L) (M := M) S
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_directSum]
  simp

/-- **A module exhausted by an isotypic component has dimension the multiplicity times the
dimension of its type.** This is the numerical content of `M ≅ S^{⊕ m}`, and it needs nothing of
`M` beyond finite-dimensionality: the whole hypothesis is that the `S`-isotypic component is all
of `M`. -/
theorem finrank_of_isotypicComponent_eq_top (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] [LieModule K L S] [IsIrreducible K L S]
    (h : isotypicComponent K L M S = ⊤) :
    finrank K M = isotypicMultiplicity K L M S * finrank K S := by
  rw [← finrank_isotypicComponent (M := M) S, h]
  exact (LieModuleEquiv.ofTop K L M).toLinearEquiv.finrank_eq.symm

/-- **An isotypic module has dimension the multiplicity times the dimension of its type.** This is
the form a decomposition argument consumes: having checked that every irreducible Lie submodule of
a completely reducible `M` is equivalent to `S`, the dimension of `M` is `m · dim S` with `m` the
multiplicity. Complete reducibility enters only to turn the isotypy hypothesis into the
component-exhausts-`M` hypothesis of `LieModule.finrank_of_isotypicComponent_eq_top`. -/
theorem finrank_of_isIsotypicOfType (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] [LieModule K L S] [IsIrreducible K L S]
    [ComplementedLattice (LieSubmodule K L M)] (h : IsIsotypicOfType K L M S) :
    finrank K M = isotypicMultiplicity K L M S * finrank K S :=
  finrank_of_isotypicComponent_eq_top S ((isotypicComponent_eq_top_iff S).mpr h)

end IsotypicComponent

end LieModule
