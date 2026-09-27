/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Module (Matrix n n R) (n → R)` through `Matrix.mulVec` is the action restricted below.
public import Mathlib.LinearAlgebra.Matrix.Action
-- `GL` occurs in every statement below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `SubMulAction` carries the action on the nonzero vectors.
public import Mathlib.GroupTheory.GroupAction.SubMulAction
-- `TauCeti.natCard_GL_fin_two` computes the order of `GL (Fin 2) F`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- `Nat.card_perm` counts the permutations of a finite type.
public import Mathlib.Data.Finite.Perm
-- `TauCeti.card_conjClasses_GL2` counts the conjugacy classes of `GL₂(F)`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses

/-!
# The general linear group permuting the nonzero vectors, and `GL₂(𝔽₂) ≅ S₃`

An invertible matrix carries a nonzero vector to a nonzero vector, so `GL n R` acts on the
nonzero vectors of `n → R`; that action is **faithful** as soon as `R` is nontrivial, because the
standard basis vector `eⱼ` is nonzero and `g • eⱼ` is the `j`-th column of `g`. The underlying
`GL n R`-set is `Matrix.GeneralLinearGroup.nonzeroVectors`, a `SubMulAction` of the
`Matrix.mulVec` action of `Mathlib.LinearAlgebra.Matrix.Action`, and the permutation
representation is Mathlib's `MulAction.toPermHom`.

Over a field with `2` elements this is an isomorphism and not merely an embedding, by a count:
`𝔽₂²` has `3` nonzero vectors, so the target `Equiv.Perm` has `3! = 6` elements, and
`TauCeti.natCard_GL_fin_two` gives `|GL₂(𝔽₂)| = (2 - 1)² · 2 · 3 = 6` as well. Hence
`TauCeti.gl2MulEquivPermFinThree`, the degenerate `q = 2` instance
`GL₂(𝔽₂) ≅ S₃` of the `GL₂(𝔽_q)` layer. The same field has a trivial unit group, which is the
reason that instance is degenerate: with `𝔽₂ˣ` a single point there is no pair of distinct
eigenvalues, so the split-semisimple conjugacy classes and the irreducible principal series
are both empty, and the `3 = q² - 1` conjugacy classes are the central, unipotent and elliptic
ones alone.

The character degrees `1, 1, 2` of that table are a statement about complex representations and
are not proved here; what is proved here is the group isomorphism they are read off, together
with the order and the class count.

## Main definitions

* `Matrix.GeneralLinearGroup.nonzeroVectors`: the nonzero vectors of `n → R` as a `GL n R`-set.
* `TauCeti.gl2MulEquivPermNonzeroVectors`, `TauCeti.gl2MulEquivPermFinThree`: over a field with
  two elements, `GL (Fin 2) F` is the symmetric group on the three nonzero vectors, and so on
  `Fin 3`.

## Main results

* `Matrix.GeneralLinearGroup.faithfulSMulNonzeroVectors`: the action on the nonzero vectors is
  faithful over a nontrivial ring.
* `Matrix.GeneralLinearGroup.natCard_nonzeroVectors`: there are `|R| ^ |n| - 1` nonzero vectors.
* `TauCeti.natCard_GL_fin_two_of_card_eq_two`,
  `TauCeti.natCard_conjClasses_GL_fin_two_of_card_eq_two`: over a field with two elements
  `GL (Fin 2) F` has order `6` and three conjugacy classes.
* `TauCeti.subsingleton_units_of_card_eq_two`: a field with two elements has a trivial unit
  group.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.
* [Character-theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9 and its staged worked examples, whose degenerate instance `GL₂(𝔽₂) ≅ S₃` is what this
  file supplies.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **The nonzero vectors of `n → R` as a `GL n R`-set.** An invertible matrix has an inverse, so
it cannot send a nonzero vector to zero; the action is the `Matrix.mulVec` action of
`Mathlib.LinearAlgebra.Matrix.Action` read through the unit group. -/
def nonzeroVectors (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] :
    SubMulAction (GL n R) (n → R) where
  carrier := {v | v ≠ 0}
  smul_mem' g _ hv := (smul_ne_zero_iff_ne g).2 hv

@[simp]
theorem mem_nonzeroVectors {v : n → R} : v ∈ nonzeroVectors n R ↔ v ≠ 0 := Iff.rfl

/-- **The action on the nonzero vectors is faithful.** The standard basis vector `eⱼ` is nonzero
because `R` is nontrivial, and `g • eⱼ` is the `j`-th column of `g`, so an element acting
trivially on every nonzero vector has the columns of the identity matrix. -/
instance faithfulSMulNonzeroVectors [Nontrivial R] :
    FaithfulSMul (GL n R) (nonzeroVectors n R) where
  eq_of_smul_eq_smul {g h} H := by
    refine Units.ext (Matrix.ext fun i j ↦ ?_)
    have hj : (Pi.single j (1 : R)) ∈ nonzeroVectors n R := by
      refine mem_nonzeroVectors.2 fun hc ↦ one_ne_zero (α := R) ?_
      simpa using congrFun hc j
    have hcol := congrArg Subtype.val (H ⟨Pi.single j 1, hj⟩)
    simp only [SubMulAction.val_smul, Units.smul_def, Matrix.smul_eq_mulVec,
      Matrix.mulVec_single_one] at hcol
    exact congrFun hcol i

/-- **The number of nonzero vectors** is `|R| ^ |n| - 1`. -/
theorem natCard_nonzeroVectors [Finite R] :
    Nat.card (nonzeroVectors n R) = Nat.card R ^ Nat.card n - 1 := by
  classical
  have e : ↥(nonzeroVectors n R) ≃ {v : n → R // v ≠ 0} :=
    Equiv.subtypeEquivRight fun _ ↦ mem_nonzeroVectors
  have key := Nat.card_congr (Equiv.optionSubtypeNe (0 : n → R))
  rw [Finite.card_option, Nat.card_fun] at key
  rw [Nat.card_congr e]
  omega

end Matrix.GeneralLinearGroup

namespace TauCeti

open Matrix.GeneralLinearGroup

variable {F : Type*} [Field F] [Fintype F]

/-- **A field with two elements has a trivial unit group.** This is why the `q = 2` instance of
the `GL₂(𝔽_q)` character table is degenerate: there is no pair of distinct eigenvalues, so no
split-semisimple conjugacy class and no irreducible principal series. -/
theorem subsingleton_units_of_card_eq_two (hF : Fintype.card F = 2) : Subsingleton Fˣ := by
  have h : Nat.card Fˣ = 1 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
  exact (Nat.card_eq_one_iff_unique.1 h).1

/-- **`GL₂` over a field with two elements has order `6`.** This is `(q - 1)² · q(q + 1)` at
`q = 2`. -/
theorem natCard_GL_fin_two_of_card_eq_two (hF : Fintype.card F = 2) :
    Nat.card (GL (Fin 2) F) = 6 := by
  rw [natCard_GL_fin_two F, hF]
  norm_num

/-- **`GL₂` over a field with two elements has three conjugacy classes**, namely `q² - 1 = 3`:
the central class `{1}`, the unipotent class of the transvections, and the elliptic class of the
elements of order `3`.  This is the `q = 2` case of the count that matches the number of
irreducible complex characters. -/
theorem natCard_conjClasses_GL_fin_two_of_card_eq_two (hF : Fintype.card F = 2) :
    Nat.card (ConjClasses (GL (Fin 2) F)) = 3 := by
  rw [card_conjClasses_GL2 F, Nat.card_eq_fintype_card, hF]
  norm_num

/-- **A plane over a field with two elements has three nonzero vectors.** -/
theorem natCard_nonzeroVectors_fin_two_of_card_eq_two (hF : Fintype.card F = 2) :
    Nat.card (nonzeroVectors (Fin 2) F) = 3 := by
  rw [natCard_nonzeroVectors, Nat.card_eq_fintype_card, hF, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- **`GL₂` over a field with two elements permutes the three nonzero vectors bijectively.**
Injectivity is faithfulness of the action; surjectivity is the coincidence `6 = 3!` of the two
orders. -/
theorem bijective_toPermHom_nonzeroVectors_of_card_eq_two (hF : Fintype.card F = 2) :
    Function.Bijective
      (MulAction.toPermHom (GL (Fin 2) F) (nonzeroVectors (Fin 2) F)) := by
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨MulAction.toPerm_injective, ?_⟩
  rw [natCard_GL_fin_two_of_card_eq_two hF, Nat.card_perm,
    natCard_nonzeroVectors_fin_two_of_card_eq_two hF]
  decide

/-- **`GL₂(𝔽₂)` is the symmetric group on the three nonzero vectors of `𝔽₂²`.** -/
noncomputable def gl2MulEquivPermNonzeroVectors (hF : Fintype.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (nonzeroVectors (Fin 2) F) :=
  MulEquiv.ofBijective _ (bijective_toPermHom_nonzeroVectors_of_card_eq_two hF)

@[simp]
theorem val_gl2MulEquivPermNonzeroVectors_apply (hF : Fintype.card F = 2) (g : GL (Fin 2) F)
    (v : nonzeroVectors (Fin 2) F) :
    ((gl2MulEquivPermNonzeroVectors hF g v : nonzeroVectors (Fin 2) F) : Fin 2 → F)
      = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (v : Fin 2 → F) := (rfl)

/-- **`GL₂(𝔽₂) ≅ S₃`.** The degenerate `q = 2` instance of the `GL₂(𝔽_q)` layer: over a field
with two elements the general linear group in size two is the symmetric group on three letters,
obtained from `TauCeti.gl2MulEquivPermNonzeroVectors` by numbering the three nonzero vectors. -/
noncomputable def gl2MulEquivPermFinThree (hF : Fintype.card F = 2) :
    GL (Fin 2) F ≃* Equiv.Perm (Fin 3) :=
  (gl2MulEquivPermNonzeroVectors hF).trans
    (Equiv.permCongrHom
      (Finite.equivFinOfCardEq (natCard_nonzeroVectors_fin_two_of_card_eq_two hF)))

end TauCeti
