/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.RepresentationTheory.Induction.Permutation
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup

/-!
# Young permutation modules

For a partition `μ` of `n`, the Young permutation module `M^μ` over a commutative ring `R` is
  the permutation
representation of `Equiv.Perm (Fin n)` on the left cosets of the Young subgroup associated to
`μ`. These cosets are the `μ`-tabloids.

This file records the tabloid basis and its action, computes the stabilizer of a tabloid as the
group preserving its rows (`TauCeti.stabilizer_quotientGroup_mk_youngSubgroup`), identifies `M^μ`
with the representation induced from the trivial representation of the Young subgroup, and
computes its dimension and character. In particular, the dimension is the multinomial coefficient
`n! / ∏ i, μᵢ!`, while the character at a permutation is the number of fixed tabloids.

## Main definitions

* `TauCeti.permutationModule` is the Young permutation module `M^μ`.
* `TauCeti.permutationModuleBasis` is its basis indexed by `μ`-tabloids.
* `TauCeti.permutationModuleIsoIndTrivial` identifies `M^μ` with an induced trivial
  representation.
* `TauCeti.permutationModuleFDRep` is the finitely generated bundled form of `M^μ`.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups*, for Young permutation
  modules and tabloids.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1, “The permutation module”.
-/

public section

open CategoryTheory

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R]

/-! ## The tabloid model -/

/-- The Young permutation module `M^μ` over `R`.

Its standard basis is indexed by the left cosets of `youngSubgroup μ`; these cosets are the
`μ`-tabloids, and the symmetric group acts on them by left multiplication. -/
noncomputable abbrev permutationModule {n : ℕ} (μ : n.Partition) :
    Rep R (Equiv.Perm (Fin n)) :=
  Rep.ofMulAction R (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)

/-- The standard basis of `M^μ`, indexed by the `μ`-tabloids. -/
noncomputable abbrev permutationModuleBasis {n : ℕ} (μ : n.Partition) :
    Module.Basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) R
      (permutationModule (R := R) μ).V :=
  MonoidAlgebra.basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) R

/-- **The stabilizer of a tabloid.** A permutation fixes the coset `gH` of the Young subgroup of
`μ` exactly when it preserves every fiber of the block map transported by `g`, that is, when it
permutes the labels within the rows of the tabloid. -/
theorem stabilizer_quotientGroup_mk_youngSubgroup {n : ℕ} (μ : n.Partition)
    (g : Equiv.Perm (Fin n)) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) =
      fiberSubgroup fun x => youngBlock μ (g⁻¹ x) := by
  rw [stabilizer_quotientGroup_mk, youngSubgroup_eq_fiberSubgroup]
  exact fiberSubgroup_map_conj g fun _ _ => by simp

/-! ## Induction, dimension, and character -/

/-- The Young permutation module is induction of the trivial representation of the Young
subgroup. -/
noncomputable def permutationModuleIsoIndTrivial {n : ℕ} (μ : n.Partition) :
    permutationModule (R := R) μ ≅
      Rep.ind (youngSubgroup μ).subtype
        (Rep.trivial R (youngSubgroup μ) R) :=
  (indTrivialIso R (youngSubgroup μ)).symm

/-- The dimension of `M^μ` is the index of its Young subgroup. -/
theorem finrank_permutationModule_eq_index [Nontrivial R] {n : ℕ} (μ : n.Partition) :
    Module.finrank R (permutationModule (R := R) μ).V = (youngSubgroup μ).index := by
  let : Fintype (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (permutationModuleBasis (R := R) μ)]
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]

/-- The dimension of `M^μ` is the multinomial coefficient
`n! / ∏ i, μᵢ!`. -/
@[simp]
theorem finrank_permutationModule [Nontrivial R] {n : ℕ} (μ : n.Partition) :
    Module.finrank R (permutationModule (R := R) μ).V =
      n.factorial / (μ.parts.map Nat.factorial).prod := by
  rw [finrank_permutationModule_eq_index, youngSubgroup_index]

/-- The Young permutation module bundled as a finitely generated representation. -/
noncomputable abbrev permutationModuleFDRep {n : ℕ} (μ : n.Partition) :
    FDRep R (Equiv.Perm (Fin n)) :=
  FDRep.of (permutationModule (R := R) μ).ρ

/-- The bundled Young permutation module has the same multinomial dimension. -/
@[simp]
theorem finrank_permutationModuleFDRep [Nontrivial R] {n : ℕ} (μ : n.Partition) :
    Module.finrank R (permutationModuleFDRep (R := R) μ) =
      n.factorial / (μ.parts.map Nat.factorial).prod :=
  finrank_permutationModule μ

end CommRing

variable {R : Type*} [Field R]

/-- The character of `M^μ` at `σ` is the number of `μ`-tabloids fixed by `σ`. -/
theorem char_permutationModule {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModule (R := R) μ).ρ.character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : R) := by
  let : Finite (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := inferInstance
  exact char_ofMulAction R _ σ

/-- The character of the bundled Young permutation module counts fixed tabloids. -/
@[simp]
theorem char_permutationModuleFDRep {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModuleFDRep (R := R) μ).character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : R) :=
  char_permutationModule μ σ

end TauCeti
