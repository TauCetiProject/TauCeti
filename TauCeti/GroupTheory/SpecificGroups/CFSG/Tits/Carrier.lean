/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Closure

/-!
# The ambient group of the Tits construction

The Tits group `²F₄(2)'` is built inside the group of algebraic-closure-valued points of the
short-root type-`F₄` carrier over `𝔽₂`. This is the closed subgroup scheme of `GL₂₆` generated
over `𝔽₂` by the reductions of the numbered simple root subgroups and the weight torus of the
Kostant toral closure of the twenty-six-dimensional module `V(ϖ₄)`. This file attaches that
carrier to the validated Tits index and supplies its numbered simple root subgroups and prime-field
Frobenius.

The carrier is taken over `𝔽₂` because the exceptional isogeny used by the Tits construction
exists in characteristic two. Carrying that isogeny from matrices to the carrier requires the
defining Hopf ideal to be the largest one killed by the generator coordinate maps over `𝔽₂`;
the base change of the integral toral closure is only known to contain this carrier, since new
equations can appear under a non-flat base change.

The Frobenius below squares matrix entries. It is not the Steinberg endomorphism of the Tits
construction: the latter is the characteristic-two exceptional isogeny itself, whose square is
this Frobenius. The fixed-point candidate is formed only after that exceptional isogeny has been
attached to the carrier.

The carrier uses the Bourbaki numbering of the `F₄` diagram carried by the index. The character
by which its split torus rescales the parameter of the `i`-th raising subgroup is the `i`-th simple
root of `TauCeti.DynkinType.simplyConnectedRootDatum`, so no reindexing adapter is needed.

This explicit carrier is not identified here with the pinned simply connected group scheme of
type `F₄`. Constructions on it transfer to the pinned group only along such an identification,
once one is proved. Nothing here asserts that the carrier is reductive, that its weight torus is
maximal, or that any group is finite, perfect, or simple.

## Main definitions

* `TauCeti.TitsLieIndex.AmbientGroup`: the algebraic-closure-valued points of the short-root
  type-`F₄` carrier.
* `TauCeti.TitsLieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a numbered node.
* `TauCeti.TitsLieIndex.frobenius`: the prime-field Frobenius of the ambient group.

## Main results

* `TauCeti.TitsLieIndex.rootGeneratorWeight_eq_root_simpleIndex` identifies the carrier's
  numbered root characters with the simple roots of the pinned `F₄` root datum.
* `TauCeti.TitsLieIndex.frobenius_simpleRootSubgroup` states
  `Frob₂ (x_i(u)) = x_i(u²)`.
* `TauCeti.TitsLieIndex.mem_fixedSubgroup_frobenius_iff` characterizes the Frobenius-fixed points
  by their matrix entries.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§14.1--14.2.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

-- The declaration order and Frobenius API follow the type-`F₄` Ree-family attachment in
-- https://github.com/TauCetiProject/TauCeti/pull/7666 and the existing type-`E₆` attachment.

public section

namespace TauCeti.TitsLieIndex

noncomputable section

variable (d : TitsLieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group of the Tits construction**: the algebraic-closure-valued points of the
short-root type-`F₄` carrier over `𝔽₂`, as a subgroup of `GL₂₆`.

This ambient group is generally infinite. No finiteness, reductivity, pinning, or maximality
statement is attached to it, and it is not identified here with the points of the pinned simply
connected group scheme of type `F₄`. -/
abbrev AmbientGroup : Type := F4ShortRoot.PrimeField.points d.1.Closure

/-- The Tits fixed-point construction takes place in a group. The carrier inherits this structure
as a subgroup of a general linear group. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `F₄` diagram. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure

-- This is not a simp lemma: the Frobenius action below is the intended normal form.
/-- The simple-root subgroup is the carrier's raising subgroup at the corresponding numbered
node. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      F4ShortRoot.PrimeField.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure :=
  (rfl)

/-- **The carrier's numbered root characters are the simple roots of the `F₄` root datum.**
Thus `simpleRootSubgroup i` uses the Bourbaki node represented by `i`, rather than a separately
chosen numbering of the explicit carrier. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i : Fin d.1.rank) :
    DynkinType.F4.rootGeneratorWeight DynkinType.valid_F4 (.inl (finCongr d.rank_eq_four i)) =
      (DynkinType.F4.simplyConnectedRootDatum DynkinType.valid_F4).root
        (DynkinType.F4.simpleIndex DynkinType.valid_F4 (finCongr d.rank_eq_four i)) := by
  simpa only [DynkinType.rank_F4] using
    DynkinType.F4.rootGeneratorWeight_inl_eq_root_simpleIndex DynkinType.valid_F4
      (finCongr d.rank_eq_four i)

/-! ## The prime-field Frobenius -/

/-- **The prime-field Frobenius of the Tits ambient group**, which squares every matrix entry.

This is not the Steinberg endomorphism. The Tits Steinberg endomorphism is the exceptional
isogeny whose square is this map. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.frobenius 1 d.1.Closure

-- This is not a simp lemma: the entrywise and root-subgroup equations are the normal forms.
/-- The Tits Frobenius is the carrier's Frobenius at exponent one. -/
theorem frobenius_def :
    d.frobenius = F4ShortRoot.PrimeField.frobenius 1 d.1.Closure :=
  (rfl)

/-- The Frobenius squares every matrix entry of the ambient group. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 26) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c ^ 2 := by
  rw [frobenius_def, F4ShortRoot.PrimeField.coe_frobenius_apply, pow_one]

/-- **The Frobenius fixes the numbered simple-root subgroup and squares its parameter**:
`Frob₂ (x_i(u)) = x_i(u²)`. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2)) := by
  rw [frobenius_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, pow_one]

-- This is not a simp lemma because `simp` already rewrites fixed-subgroup membership to an
-- equality by `MonoidHom.mem_eqLocus`.
/-- **A carrier point is fixed by the prime-field Frobenius exactly when all matrix entries lie
in the index's field of definition**, the copy of `𝔽₂` inside its algebraic closure. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure) :
        Matrix (Fin 26) (Fin 26) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, F4ShortRoot.PrimeField.frobenius_eq_self_iff]
  simp only [FiniteField.mem_frobeniusFixedSubalgebra, Nat.card_zmod,
    ValidLieTypeIndex.mem_fixedField, d.fieldOrder_eq_two, pow_one]

end

end TauCeti.TitsLieIndex
