/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.GaloisModule
public import TauCeti.Algebra.AlgebraicGroup.Torus.Cocharacter.Functoriality
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The field of definition of a cocharacter

Let `T` be a group of multiplicative type over a field `k`, for instance a torus, let `K` be the
chosen algebraic closure of `k`, and let `μ : 𝔾ₘ → T` be a geometric cocharacter, defined over
`K`. The absolute Galois group acts on the cocharacter lattice `X_*(T)`, and the **field of
definition** of `μ` is the subfield of `K` fixed by the stabilizer of `μ`:

```text
E(T, μ) = K ^ {σ | σ • μ = μ}.
```

For a special pair `(T, h)` of a Shimura datum, with `μ = μ_h`, this is the reflex field
`E(T, h)`, the field along which the reflex norm `Res_{E/k} 𝔾ₘ → T` restricts scalars.

The stabilizer of `μ` is open, because the character group of `T` is finitely generated
(`stabilizer_cocharacterLattice_isOpen`). Over a perfect field `k`, where `K / k` is Galois, the
infinite Galois correspondence then shows that the field of definition is a finite extension of
`k`, that its fixers are exactly the stabilizer of `μ`, and that it is the smallest intermediate
field `F` such that every automorphism fixing `F` fixes `μ`: the cocharacter is defined over `F`
exactly when `F` contains `E(T, μ)`. Its degree is the size of the Galois orbit of `μ`. Over an
imperfect field the fixed field contains the perfect closure of `k`, which is infinite over `k`,
so these statements need perfectness.

The field of definition is compatible with the structure of the lattice and of the category of
groups of multiplicative type:

* it moves with `μ` under the Galois action, `E(T, σ • μ) = σ (E(T, μ))`;
* a homomorphism `T → S` (contravariantly, a map of coordinate algebras) can only shrink it, so for
  `μ = f ∘ μ₀` the field `E(S, μ)` is contained in `E(T, μ₀)`;
* `E(T, -μ) = E(T, μ)` and `E(T, n • μ) = E(T, μ)` for `n ≠ 0`;
* over a perfect field, `E(T, μ + ν) ⊆ E(T, μ) E(T, ν)`, and `E(T, μ)` is `k` exactly when the
  Galois group fixes `μ`.

## Main declarations

* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterFieldOfDefinition`: the field of definition
  `E(T, μ)` of a geometric cocharacter.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.fixingSubgroup_cocharacterFieldOfDefinition`: its
  fixers are the stabilizer of the cocharacter.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterFieldOfDefinition_le_iff`: the cocharacter
  is fixed by the automorphisms fixing `F` exactly when `F` contains its field of definition.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.instFiniteDimensionalCocharacterFieldOfDefinition` and
  `TauCeti.MultiplicativeTypeCommHopfAlgCat.finrank_cocharacterFieldOfDefinition`: it is a finite
  extension whose degree is the size of the Galois orbit.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterFieldOfDefinition_cocharacterMap_le`: maps
  of groups of multiplicative type shrink fields of definition, and isomorphisms preserve them
  (`TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterFieldOfDefinition_cocharacterMap_of_isIso`).

## References

* J. S. Milne, *Introduction to Shimura varieties*, §12, *The reflex field*, and Remark 12.3(c),
  pp. 111–112.
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), 5.4.
* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

namespace TauCeti

universe u

namespace MultiplicativeTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The **stabilizer** of a geometric cocharacter `μ`: the absolute Galois automorphisms fixing
`μ`, as a subgroup of the automorphism group of the algebraic closure, the form on which the Galois
correspondence operates. -/
noncomputable def cocharacterStabilizer (T : MultiplicativeTypeCommHopfAlgCat k)
    (μ : cocharacterLattice T) : Subgroup Gal(AlgebraicClosure k/k) :=
  MulAction.stabilizer (Field.absoluteGaloisGroup k) μ

/-- The **field of definition** `E(T, μ)` of a geometric cocharacter `μ` of a group `T` of
multiplicative type over `k`: the subfield of the algebraic closure fixed by every absolute Galois
automorphism that fixes `μ`. For the cocharacter `μ_h` of a special pair `(T, h)` of a Shimura
datum it is the reflex field `E(T, h)`. -/
noncomputable def cocharacterFieldOfDefinition (T : MultiplicativeTypeCommHopfAlgCat k)
    (μ : cocharacterLattice T) : IntermediateField k (AlgebraicClosure k) :=
  IntermediateField.fixedField (cocharacterStabilizer T μ)

variable {T : MultiplicativeTypeCommHopfAlgCat k} {μ ν : cocharacterLattice T}

/-- An automorphism of the algebraic closure stabilizes `μ` exactly when, read as an absolute
Galois automorphism, it fixes `μ`. -/
@[simp]
theorem mem_cocharacterStabilizer_iff {σ : Gal(AlgebraicClosure k/k)} :
    σ ∈ cocharacterStabilizer T μ ↔
      cocharacterGaloisRepresentation T (Field.absoluteGaloisGroup.toAlgEquiv.symm σ) μ = μ :=
  Iff.rfl

/-- The stabilizer of a cocharacter is open for the Krull topology. -/
theorem isOpen_cocharacterStabilizer (μ : cocharacterLattice T) :
    IsOpen (cocharacterStabilizer T μ : Set Gal(AlgebraicClosure k/k)) :=
  -- Mathlib's `Field.absoluteGaloisGroup` is a named copy of `Gal(AlgebraicClosure k/k)` whose
  -- derived topology is the Krull topology, with no bridge lemma; the two statements agree.
  stabilizer_cocharacterLattice_isOpen T μ

/-- The stabilizer of a Galois translate is the conjugate stabilizer. -/
theorem cocharacterStabilizer_cocharacterGaloisRepresentation
    (σ : Field.absoluteGaloisGroup k) (μ : cocharacterLattice T) :
    cocharacterStabilizer T (cocharacterGaloisRepresentation T σ μ) =
      (cocharacterStabilizer T μ).map (MulAut.conj (Field.absoluteGaloisGroup.toAlgEquiv σ)) :=
  -- `Field.absoluteGaloisGroup.toAlgEquiv` is the identity of the named copy of the Galois group,
  -- and the action on cocharacters is the representation, so Mathlib's statement for the
  -- absolute Galois group is this one.
  MulAction.stabilizer_smul_eq_stabilizer_map_conj σ μ

/-- Negating a cocharacter does not change its stabilizer. -/
@[simp]
theorem cocharacterStabilizer_neg (μ : cocharacterLattice T) :
    cocharacterStabilizer T (-μ) = cocharacterStabilizer T μ := by
  ext σ
  simp only [mem_cocharacterStabilizer_iff, map_neg, neg_inj]

/-- A nonzero integral multiple of a cocharacter has the same stabilizer, because the cocharacter
lattice is torsion-free. -/
theorem cocharacterStabilizer_zsmul {n : ℤ} (hn : n ≠ 0) (μ : cocharacterLattice T) :
    cocharacterStabilizer T (n • μ) = cocharacterStabilizer T μ := by
  ext σ
  simp only [mem_cocharacterStabilizer_iff, map_zsmul, smul_right_inj hn]

/-- The stabilizer of a sum of cocharacters contains the common stabilizer of the summands. -/
theorem cocharacterStabilizer_inf_le_add (μ ν : cocharacterLattice T) :
    cocharacterStabilizer T μ ⊓ cocharacterStabilizer T ν ≤ cocharacterStabilizer T (μ + ν) := by
  intro σ hσ
  rw [Subgroup.mem_inf, mem_cocharacterStabilizer_iff, mem_cocharacterStabilizer_iff] at hσ
  rw [mem_cocharacterStabilizer_iff, map_add, hσ.1, hσ.2]

/-- Galois equivariance of `cocharacterMap`: every automorphism fixing `μ` fixes its image under
a map of groups of multiplicative type. -/
theorem cocharacterStabilizer_le_cocharacterMap {S : MultiplicativeTypeCommHopfAlgCat k}
    (f : S ⟶ T) (μ : cocharacterLattice T) :
    cocharacterStabilizer T μ ≤ cocharacterStabilizer S (cocharacterMap f μ) := by
  intro σ hσ
  rw [mem_cocharacterStabilizer_iff] at hσ ⊢
  rw [← cocharacterMap_smul, hσ]

theorem cocharacterFieldOfDefinition_def :
    cocharacterFieldOfDefinition T μ = IntermediateField.fixedField (cocharacterStabilizer T μ) :=
  (rfl)

/-- An element of the algebraic closure lies in the field of definition of `μ` exactly when it is
fixed by every automorphism fixing `μ`. -/
@[simp]
theorem mem_cocharacterFieldOfDefinition_iff {a : AlgebraicClosure k} :
    a ∈ cocharacterFieldOfDefinition T μ ↔
      ∀ σ : Gal(AlgebraicClosure k/k),
        cocharacterGaloisRepresentation T (Field.absoluteGaloisGroup.toAlgEquiv.symm σ) μ = μ →
          σ a = a := by
  simp [cocharacterFieldOfDefinition_def]

/-- The field of definition moves with the cocharacter: `E(T, σ • μ) = σ (E(T, μ))`. -/
@[simp]
theorem cocharacterFieldOfDefinition_cocharacterGaloisRepresentation
    (σ : Field.absoluteGaloisGroup k) (μ : cocharacterLattice T) :
    cocharacterFieldOfDefinition T (cocharacterGaloisRepresentation T σ μ) =
      (cocharacterFieldOfDefinition T μ).map
        (Field.absoluteGaloisGroup.toAlgEquiv σ).toAlgHom := by
  rw [cocharacterFieldOfDefinition_def, cocharacterStabilizer_cocharacterGaloisRepresentation,
    Subgroup.fixedField_map_conj, cocharacterFieldOfDefinition_def]

/-- **Maps of groups of multiplicative type shrink fields of definition.** A morphism `f` of
coordinate Hopf algebras, that is a homomorphism of groups `T → S`, composed with the geometric
cocharacter `μ` of `T` gives a cocharacter of `S` whose field of definition is contained in that
of `μ`. -/
theorem cocharacterFieldOfDefinition_cocharacterMap_le {S : MultiplicativeTypeCommHopfAlgCat k}
    (f : S ⟶ T) (μ : cocharacterLattice T) :
    cocharacterFieldOfDefinition S (cocharacterMap f μ) ≤ cocharacterFieldOfDefinition T μ :=
  IntermediateField.fixedField_le (cocharacterStabilizer_le_cocharacterMap f μ)

/-- An isomorphism of groups of multiplicative type preserves fields of definition. -/
theorem cocharacterFieldOfDefinition_cocharacterMap_of_isIso
    {S : MultiplicativeTypeCommHopfAlgCat k} (f : S ⟶ T) [CategoryTheory.IsIso f]
    (μ : cocharacterLattice T) :
    cocharacterFieldOfDefinition S (cocharacterMap f μ) = cocharacterFieldOfDefinition T μ := by
  refine le_antisymm (cocharacterFieldOfDefinition_cocharacterMap_le f μ) ?_
  have hμ : cocharacterMap (CategoryTheory.inv f) (cocharacterMap f μ) = μ := by
    rw [← LinearMap.comp_apply, ← cocharacterMap_comp, CategoryTheory.IsIso.inv_hom_id,
      cocharacterMap_id, LinearMap.id_apply]
  conv_lhs => rw [← hμ]
  exact cocharacterFieldOfDefinition_cocharacterMap_le _ _

/-- Negating a cocharacter does not change its field of definition. -/
@[simp]
theorem cocharacterFieldOfDefinition_neg (μ : cocharacterLattice T) :
    cocharacterFieldOfDefinition T (-μ) = cocharacterFieldOfDefinition T μ := by
  rw [cocharacterFieldOfDefinition_def, cocharacterStabilizer_neg,
    cocharacterFieldOfDefinition_def]

/-- A nonzero integral multiple of a cocharacter has the same field of definition. -/
theorem cocharacterFieldOfDefinition_zsmul {n : ℤ} (hn : n ≠ 0) (μ : cocharacterLattice T) :
    cocharacterFieldOfDefinition T (n • μ) = cocharacterFieldOfDefinition T μ := by
  rw [cocharacterFieldOfDefinition_def, cocharacterStabilizer_zsmul hn,
    cocharacterFieldOfDefinition_def]

/-! ### The Galois correspondence over a perfect field -/

section Perfect

variable [PerfectField k]

/-- **The automorphisms fixing the field of definition of `μ` are exactly those fixing `μ`.** The
stabilizer of `μ` is open, hence closed, and over a perfect field the infinite Galois
correspondence recovers it from its fixed field. -/
@[simp]
theorem fixingSubgroup_cocharacterFieldOfDefinition (μ : cocharacterLattice T) :
    (cocharacterFieldOfDefinition T μ).fixingSubgroup = cocharacterStabilizer T μ :=
  IntermediateField.fixingSubgroup_fixedField_of_isOpen (isOpen_cocharacterStabilizer μ)

/-- **A cocharacter is defined over `F` exactly when `F` contains its field of definition**: every
automorphism of the algebraic closure fixing `F` pointwise fixes `μ` if and only if
`E(T, μ) ≤ F`. In particular `μ` is fixed by the automorphisms fixing `E(T, μ)`. -/
theorem cocharacterFieldOfDefinition_le_iff {F : IntermediateField k (AlgebraicClosure k)} :
    cocharacterFieldOfDefinition T μ ≤ F ↔ F.fixingSubgroup ≤ cocharacterStabilizer T μ :=
  IntermediateField.fixedField_le_iff_fixingSubgroup_le_of_isClosed
    (Subgroup.isClosed_of_isOpen _ (isOpen_cocharacterStabilizer μ))

/-- The field of definition of a geometric cocharacter is a finite extension of the base. -/
instance instFiniteDimensionalCocharacterFieldOfDefinition (μ : cocharacterLattice T) :
    FiniteDimensional k (cocharacterFieldOfDefinition T μ) :=
  IntermediateField.finiteDimensional_fixedField_of_isOpen (isOpen_cocharacterStabilizer μ)

/-- **The degree of the field of definition is the size of the Galois orbit** of the
cocharacter. -/
theorem finrank_cocharacterFieldOfDefinition (μ : cocharacterLattice T) :
    Module.finrank k (cocharacterFieldOfDefinition T μ) =
      Nat.card (MulAction.orbit (Field.absoluteGaloisGroup k) μ) := by
  rw [cocharacterFieldOfDefinition_def,
    IntermediateField.finrank_fixedField_of_isOpen (isOpen_cocharacterStabilizer μ)]
  -- `cocharacterStabilizer T μ` is by definition the stabilizer of `μ` in
  -- `Field.absoluteGaloisGroup k`, Mathlib's named copy of `Gal(AlgebraicClosure k/k)` with no
  -- bridge lemma, so Mathlib's index formula for that stabilizer is this goal.
  exact (MulAction.index_stabilizer (Field.absoluteGaloisGroup k) μ).trans
    (Nat.card_coe_set_eq _).symm

/-- The field of definition is the base field exactly when the cocharacter is Galois-invariant,
that is, defined over `k`. -/
theorem cocharacterFieldOfDefinition_eq_bot_iff :
    cocharacterFieldOfDefinition T μ = ⊥ ↔
      ∀ σ : Field.absoluteGaloisGroup k, cocharacterGaloisRepresentation T σ μ = μ := by
  rw [← le_bot_iff, cocharacterFieldOfDefinition_le_iff, IntermediateField.fixingSubgroup_bot,
    top_le_iff, Subgroup.eq_top_iff']
  simp only [mem_cocharacterStabilizer_iff]
  exact ((Field.absoluteGaloisGroup.toAlgEquiv (k := k)).symm.surjective.forall
    (p := fun σ ↦ cocharacterGaloisRepresentation T σ μ = μ)).symm

/-- The field of definition of a sum of cocharacters lies in the compositum of their fields of
definition. -/
theorem cocharacterFieldOfDefinition_add_le (μ ν : cocharacterLattice T) :
    cocharacterFieldOfDefinition T (μ + ν) ≤
      cocharacterFieldOfDefinition T μ ⊔ cocharacterFieldOfDefinition T ν := by
  rw [cocharacterFieldOfDefinition_le_iff, IntermediateField.fixingSubgroup_sup,
    fixingSubgroup_cocharacterFieldOfDefinition, fixingSubgroup_cocharacterFieldOfDefinition]
  exact cocharacterStabilizer_inf_le_add μ ν

end Perfect

end MultiplicativeTypeCommHopfAlgCat

end TauCeti
