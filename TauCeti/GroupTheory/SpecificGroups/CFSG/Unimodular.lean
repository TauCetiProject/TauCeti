/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.GeckCarrier
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Torus

/-!
# The Lie-type indices whose Dynkin diagram is unimodular

`TauCeti.ValidLieTypeIndex.GeckGroup` gives every valid index a concrete matrix group with numbered
root subgroups and a Frobenius. That carrier is built from the adjoint representation, so the
characters occurring in it generate the root lattice and not, in general, the whole character
lattice of the pinned torus: it is expected to be the adjoint form of a Chevalley--Demazure group,
whereas the CFSG recipe has to be run in the simply connected form. The lattice condition that
separates the two forms -- that the weights span the whole character lattice -- holds by
`TauCeti.DynkinType.span_range_geckWeight_eq_top_iff` exactly in the types `E₈`, `F₄` and `G₂`.

This file proves that span, and the closed immersion of the weight torus it buys, for
`TauCeti.UnimodularLieIndex`, the valid indices whose underlying diagram is one of those three.
Six of the seventeen Lie-type constructors qualify, and they are of two kinds:

```text
E₈(q),  F₄(q),  G₂(q),        ²G₂(3^(2m+1)),  ²F₄(2^(2m+1)),  ²F₄(2)'.
```

The three on the left are untwisted, and their Steinberg map is the `q`-power Frobenius
`TauCeti.ValidLieTypeIndex.geckFrobenius`; they are collected as
`TauCeti.UnimodularExceptionalIndex` and carried through the rest of the recipe here. The three on
the right take an odd power of a half-Frobenius instead, so their Steinberg map is not built in
this file.

The predicate `TauCeti.LieTypeIndex.HasUnimodularDiagram` is about the diagram alone, so it says
nothing about which Steinberg map an index takes. That is what makes it the right hypothesis here:
`²F₄(2^(2m+1))` and `²F₄(2)'` have the same character lattice as `F₄(q)`, and `²G₂(3^(2m+1))` the
same as `G₂(q)`, whatever endomorphism is later taken of their common carrier. The Suzuki family
`²B₂(2^(2m+1))` does *not* appear: its underlying diagram is `B₂`, whose Cartan matrix has
determinant two, so the Geck carrier is not its simply connected form.

Identifying the carrier itself with the pinned simply connected Chevalley--Demazure group, and
proving it reductive, is the Layer 9 work of `TauCetiRoadmap/ReductiveGroups/README.md` that this
roadmap consumes rather than performs; no declaration below asserts either, nor that a constructed
group is finite, perfect, or simple.

## Main definitions

* `TauCeti.UnimodularExceptionalIndex`: the unimodular indices whose Steinberg map is not a
  half-Frobenius power, that is `E₈(q)`, `F₄(q)` and `G₂(q)`, with
  `TauCeti.UnimodularExceptionalIndex.steinberg` their Steinberg map.

## Main results

* `TauCeti.UnimodularLieIndex.span_range_geckWeight_eq_top`: the Geck weights of an index with
  unimodular diagram span the whole character lattice, the lattice condition the simply connected
  form requires.
* `TauCeti.UnimodularLieIndex.isClosedImmersion_geckWeightTorus`: consequently the pinned split
  torus is a closed subgroup scheme of the Geck carrier.
* `TauCeti.UnimodularExceptionalIndex.steinberg_geckRootSubgroup` and
  `TauCeti.UnimodularExceptionalIndex.steinberg_geckWeightTorus`: the Steinberg map raises the
  parameter of every numbered root subgroup, and every coordinate of a weight-torus point, to the
  `q`-th power, which is how the Steinberg map of an untwisted index acts on both halves of the
  pinned data of this carrier.
* `TauCeti.UnimodularExceptionalIndex.mem_fixedSubgroup_steinberg_iff`: the fixed points of that
  map are the points of the carrier whose matrix entries lie in the field of definition `𝔽_q`
  recorded by `TauCeti.ValidLieTypeIndex.fixedField`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Memoirs Amer. Math. Soc. **80**
  (1968), §11, for the Steinberg endomorphism conventions.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, for the matrix realization of the carrier.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates VII--IX, for the unimodularity
  of the `E₈`, `F₄` and `G₂` Cartan matrices.

## Carrier-level description

For the three untwisted branches treated here, `steinberg` is the `q`-power Frobenius on the Geck
carrier. Thus `mem_fixedSubgroup_steinberg_iff` identifies its fixed points with the carrier points
whose matrix entries lie in `𝔽_q`. The other unimodular branches use half-Frobenius maps instead
and are therefore not included in `UnimodularExceptionalIndex`.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace UnimodularLieIndex

variable (d : UnimodularLieIndex)

/-- **The Geck weights of an index with unimodular diagram span the whole character lattice.** This
is the lattice condition that separates the simply connected form of a Chevalley--Demazure group
from the adjoint one, and it fails on every other diagram, which is why this subtype is the domain
of the results here. It is a statement about characters only: that the carrier is reductive, and
that it is the pinned simply connected group of `TauCeti.DynkinType.simplyConnectedRootDatum`, are
Layer 9 statements that this file consumes when they arrive rather than proving. -/
theorem span_range_geckWeight_eq_top :
    Submodule.span ℤ (Set.range (d.dynkinType.geckWeight d.dynkinType_valid)) = ⊤ :=
  (DynkinType.span_range_geckWeight_eq_top_iff _ d.dynkinType_valid).mpr
    d.dynkinType_eq_E8_or_eq_F4_or_eq_G2

/-- **The pinned split torus is a closed subgroup scheme of the Geck carrier.** This is the
torus half of the pinning, and it is exactly what the full character span of
`TauCeti.UnimodularLieIndex.span_range_geckWeight_eq_top` buys. -/
theorem isClosedImmersion_geckWeightTorus :
    IsClosedImmersion (d.dynkinType.geckWeightTorus d.dynkinType_valid).hom.hom.left :=
  DynkinType.isClosedImmersion_geckWeightTorus_of_span_eq_top _ d.dynkinType_valid
    d.span_range_geckWeight_eq_top

end UnimodularLieIndex

/-! ## The untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)` -/

/-- An index with unimodular diagram whose Steinberg map is not an odd power of a half-Frobenius.
By `TauCeti.LieTypeIndex.exists_eq_of_hasUnimodularDiagram_of_not_usesHalfFrobenius` these are
exactly the three untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)`; the condition removes the Ree
families `²G₂(3^(2m+1))` and `²F₄(2^(2m+1))` and the Tits index, which share their diagrams. -/
abbrev UnimodularExceptionalIndex : Type :=
  {d : UnimodularLieIndex // ¬d.1.1.UsesHalfFrobenius}

namespace UnimodularExceptionalIndex

noncomputable section

variable (d : UnimodularExceptionalIndex)

/-- The index `E₈(q)`. -/
abbrev e8 (q : PrimePower) : UnimodularExceptionalIndex :=
  ⟨UnimodularLieIndex.e8 q, by simp⟩

/-- The index `F₄(q)`. -/
abbrev f4 (q : PrimePower) : UnimodularExceptionalIndex :=
  ⟨UnimodularLieIndex.f4 q, by simp⟩

/-- The index `G₂(q)`, for `q` at least three. -/
abbrev g2 (q : PrimePower) (hq : 3 ≤ q.card) : UnimodularExceptionalIndex :=
  ⟨UnimodularLieIndex.g2 q hq, by simp⟩

/-- **The Steinberg endomorphism of an untwisted unimodular exceptional index**: the `q`-power
Frobenius of the Geck point group, where `q` is the field order recorded by the index. The three
families this covers are untwisted, so no diagram automorphism and no half-Frobenius enters. -/
def steinberg : ValidLieTypeIndex.GeckGroup d.1.1 →* ValidLieTypeIndex.GeckGroup d.1.1 :=
  d.1.1.geckFrobenius

/-- The Steinberg map of an untwisted unimodular exceptional index is the Frobenius of its Geck
point group. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_geckRootSubgroup` and `coe_steinberg_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.ValidLieTypeIndex.geckFrobenius` would keep them from firing. -/
theorem steinberg_eq_geckFrobenius : d.steinberg = d.1.1.geckFrobenius := by
  rw [steinberg]

/-- The Steinberg map acts on the Geck point group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : ValidLieTypeIndex.GeckGroup d.1.1)
    (r c : Fin (d.1.1.dynkinType.geckDim d.1.1.dynkinType_valid)) :
    ((d.steinberg g : Matrix.GeneralLinearGroup
          (Fin (d.1.1.dynkinType.geckDim d.1.1.dynkinType_valid)) d.1.1.Closure) :
        Matrix _ _ d.1.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (d.1.1.dynkinType.geckDim d.1.1.dynkinType_valid)) d.1.1.Closure) :
        Matrix _ _ d.1.1.Closure) r c ^ d.1.1.fieldOrder := by
  rw [steinberg_eq_geckFrobenius]
  exact d.1.1.coe_geckFrobenius_apply g r c

/-- **The Steinberg map raises the parameter of every numbered root subgroup to the `q`-th
power.** On a simple root subgroup this is the equation `Frob_q (x_α(t)) = x_α(t ^ q)` that
milestone L1 asks of the untwisted families, proved here on the Geck carrier. -/
@[simp]
theorem steinberg_geckRootSubgroup (i : Fin d.1.1.dynkinType.rank ⊕ Fin d.1.1.dynkinType.rank)
    (u : Multiplicative d.1.1.Closure) :
    d.steinberg (d.1.1.geckRootSubgroup i u) =
      d.1.1.geckRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.1.fieldOrder)) := by
  rw [steinberg_eq_geckFrobenius]
  exact d.1.1.geckFrobenius_geckRootSubgroup i u

/-- **The Steinberg map raises every coordinate of a weight-torus point to the `q`-th power.** It
is the untwisted case of the equation a Steinberg endomorphism satisfies on the second half of the
pinned data, the first half being `TauCeti.UnimodularExceptionalIndex.steinberg_geckRootSubgroup`
on the root subgroups. -/
@[simp]
theorem steinberg_geckWeightTorus (s : Fin d.1.1.dynkinType.rank → d.1.1.Closureˣ) :
    d.steinberg (d.1.1.geckWeightTorus s) = d.1.1.geckWeightTorus (s ^ d.1.1.fieldOrder) := by
  rw [steinberg_eq_geckFrobenius]
  exact d.1.1.geckFrobenius_geckWeightTorus s

/-- **A point of the Geck point group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the fixed-point subgroup associated to this map is therefore the group of
points of the Geck carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`simp` rewrites its left-hand side through `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects
the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : ValidLieTypeIndex.GeckGroup d.1.1) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (d.1.1.dynkinType.geckDim d.1.1.dynkinType_valid)) d.1.1.Closure) :
        Matrix (Fin (d.1.1.dynkinType.geckDim d.1.1.dynkinType_valid))
          (Fin (d.1.1.dynkinType.geckDim d.1.1.dynkinType_valid)) d.1.1.Closure) r c ∈
        d.1.1.fixedField := by
  rw [steinberg_eq_geckFrobenius]
  exact d.1.1.mem_fixedSubgroup_geckFrobenius_iff g

end

end UnimodularExceptionalIndex

end TauCeti
