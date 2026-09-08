/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Frobenius
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GraphAutomorphism

/-!
# The graph-twisted Frobenius of the doubled type-E6 minuscule carrier

`TauCeti.E6DoubledMinuscule.groupScheme` is the explicit full-weight type-`E₆` Chevalley carrier
built on `V(ϖ₁) ⊕ V(ϖ₆)` inside `GL₅₄` over `ℤ`, and its point group over a commutative ring `A`
of exponential characteristic `p` carries two pinned endomorphisms: the `p ^ k`-power Frobenius
`TauCeti.E6DoubledMinuscule.frobenius`, which raises every matrix entry to its `p ^ k`-th power,
and the graph automorphism `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints`, which is
conjugation by a signed monomial matrix realizing the order-two symmetry of the `E₆` diagram. This
file composes them into

```text
twistedFrobenius = γ₂ ∘ Frob_q,      q = p ^ k,
```

and proves the relations that make the composite behave like the Frobenius it twists: the two
factors commute, `γ₂` is an involution, and consequently

```text
twistedFrobenius ∘ twistedFrobenius = Frob_(q ^ 2).
```

The commutation is not a computation about the carrier. The graph automorphism is conjugation by
`TauCeti.E6DoubledMinuscule.graphAutomorphismMatrix`, whose entries are `0` and `±1` and which is
therefore natural in the coefficient ring, while the Frobenius is the entrywise action of a ring
endomorphism of that same coefficient ring.

The doubled carrier is the one on which this composite exists at all. The `E₆` diagram involution
exchanges the minuscule representation `V(ϖ₁)` with its contragredient `V(ϖ₆)` rather than
preserving either, so it does not act on the `27`-dimensional carrier
`TauCeti.E6Minuscule.groupScheme` that the untwisted family is built on; the twenty-seven-element
weight table is not stable under it, by
`TauCeti.DynkinType.e6MinusculeWeight_comp_graphPermE6_notMem_range`.

The square relation has an arithmetic reading. Every point fixed by the twisted map is fixed by
`Frob_(q ^ 2)`, so its matrix entries lie in the subring of `A` fixed by the `q ^ 2`-power
Frobenius. That subring is a field of `q ^ 2` elements only under hypotheses none of the statements
below assume: `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`. Under those hypotheses
it is the usual statement that the graph-twisted family of type `E₆` at parameter `q` has a matrix
realization over `𝔽_{q ^ 2}` while its Frobenius parameter is `q`. At `k = 0` the exponent `q ^ 2`
is `1` and the fixed subring is all of `A`. Only the containment is proved; no reverse containment
is claimed, and nothing here asserts that either fixed group is finite, is perfect, or is simple.

## Main definitions

* `TauCeti.E6DoubledMinuscule.twistedFrobenius`: the composite `γ₂ ∘ Frob_q` on the doubled
  type-`E₆` point group.

## Main results

* `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints_frobenius` and
  `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints_comp_frobenius`: the graph automorphism
  commutes with Frobenius.
* `TauCeti.E6DoubledMinuscule.twistedFrobenius_rootSubgroupPoints` and
  `TauCeti.E6DoubledMinuscule.twistedFrobenius_weightTorusPoints`: the equations on the pinned
  numbered root subgroups and split torus, which relabel by the `E₆` diagram involution and raise
  the parameter to its `p ^ k`-th power.
* `TauCeti.E6DoubledMinuscule.twistedFrobenius_twistedFrobenius` and
  `TauCeti.E6DoubledMinuscule.twistedFrobenius_comp_self`: the square of the twisted map is the
  `p ^ (2 * k)`-power Frobenius, pointwise and as an identity of endomorphisms.
* `TauCeti.E6DoubledMinuscule.mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self`: the matrix
  entries of a point it fixes lie in the `p ^ (2 * k)`-power Frobenius-fixed subring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.2 and 13, for the graph automorphism of `E₆` and
  the twisted family it defines.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the Steinberg endomorphisms of the graph-twisted families.
* R. Steinberg, *Lectures on Chevalley Groups*, §11.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*, for the
  small-field convention that indexes the graph-twisted family by `q` rather than by `q ^ 2`.
* The organization of this file follows the type-`A` counterpart
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius`, whose statements are the
  same ones on the standard carrier.
-/

public section

namespace TauCeti.E6DoubledMinuscule

universe v

noncomputable section

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-! ## The graph automorphism commutes with Frobenius -/

/-- **The graph automorphism of the doubled type-`E₆` carrier commutes with the Frobenius
endomorphism of its points.** Both act on matrices: the former by conjugation by the signed
monomial matrix `TauCeti.E6DoubledMinuscule.graphAutomorphismMatrix`, whose entries are integers
and so are carried along by any ring map, the latter entrywise through a ring endomorphism of the
coefficients. -/
theorem graphAutomorphismPoints_frobenius (g : points A) :
    graphAutomorphismPoints A (frobenius p k A g) =
      frobenius p k A (graphAutomorphismPoints A g) := by
  apply Subtype.ext
  simp only [coe_graphAutomorphismPoints, coe_frobenius, map_mul, map_inv,
    map_graphAutomorphismMatrix]

/-- The graph automorphism commutes with Frobenius, as an identity of endomorphisms. -/
theorem graphAutomorphismPoints_comp_frobenius :
    (graphAutomorphismPoints A).toMonoidHom.comp (frobenius p k A) =
      (frobenius p k A).comp (graphAutomorphismPoints A).toMonoidHom :=
  MonoidHom.ext (graphAutomorphismPoints_frobenius p k A)

/-! ## The twisted Frobenius -/

/-- **The graph-twisted `p ^ k`-power Frobenius of the doubled type-`E₆` minuscule carrier**, the
composite `γ₂ ∘ Frob_q` of the carrier's graph automorphism with its Frobenius endomorphism.

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Steinberg map of the
graph-twisted family `²E₆(p ^ k)`. None of those hypotheses are assumed here, and nothing here
asserts that the fixed group is finite, perfect or simple. -/
def twistedFrobenius : points A →* points A :=
  (graphAutomorphismPoints A).toMonoidHom.comp (frobenius p k A)

/-- The twisted Frobenius applies the Frobenius first and then the graph automorphism. -/
theorem twistedFrobenius_apply (g : points A) :
    twistedFrobenius p k A g = graphAutomorphismPoints A (frobenius p k A g) := (rfl)

/-- On matrices, the twisted Frobenius conjugates the entrywise `p ^ k`-power Frobenius by the
signed monomial graph-automorphism matrix. -/
theorem coe_twistedFrobenius (g : points A) :
    (twistedFrobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) =
      graphAutomorphismMatrix A *
          _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g *
        (graphAutomorphismMatrix A)⁻¹ := by
  rw [twistedFrobenius_apply, coe_graphAutomorphismPoints, coe_frobenius]

/-! ## The pinned equations -/

/-- **The twisted Frobenius relabels a numbered root subgroup by the `E₆` diagram involution and
raises its parameter to the `p ^ k`-th power.** This is the pinned equation
`γ₂ ∘ Frob_q (x_α(t)) = x_{γ₂ α}(t ^ q)` on the numbered positive and negative simple-root
subgroups. -/
@[simp]
theorem twistedFrobenius_rootSubgroupPoints (i : Fin 6 ⊕ Fin 6) (u : Multiplicative A) :
    twistedFrobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints (graphRootPerm i) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [twistedFrobenius_apply, frobenius_rootSubgroupPoints,
    graphAutomorphismPoints_rootSubgroupPoints]

/-- **The twisted Frobenius relabels the coordinates of the pinned split weight torus by the `E₆`
diagram involution and raises each of them to the `p ^ k`-th power.** -/
@[simp]
theorem twistedFrobenius_weightTorusPoints (s : Fin 6 → Aˣ) :
    twistedFrobenius p k A (weightTorusPoints A s) =
      weightTorusPoints A (fun i => s (graphPermE6 i) ^ p ^ k) := by
  rw [twistedFrobenius_apply, frobenius_weightTorusPoints,
    graphAutomorphismPoints_weightTorusPoints]
  rfl

/-! ## The square relation -/

/-- **Applying the twisted Frobenius twice raises every matrix entry to its `p ^ (2 * k)`-th
power.** The graph factor is an involution and commutes with the Frobenius factor, so the two
copies of it cancel and the two Frobenius exponents add. -/
@[simp]
theorem twistedFrobenius_twistedFrobenius (g : points A) :
    twistedFrobenius p k A (twistedFrobenius p k A g) = frobenius p (2 * k) A g := by
  rw [twistedFrobenius_apply, twistedFrobenius_apply, ← graphAutomorphismPoints_frobenius,
    graphAutomorphismPoints_graphAutomorphismPoints, two_mul, frobenius_add, MonoidHom.comp_apply]

/-- The square of the twisted Frobenius is the `p ^ (2 * k)`-power Frobenius, as an identity of
endomorphisms. -/
theorem twistedFrobenius_comp_self :
    (twistedFrobenius p k A).comp (twistedFrobenius p k A) = frobenius p (2 * k) A :=
  MonoidHom.ext (twistedFrobenius_twistedFrobenius p k A)

/-- A point fixed by the twisted Frobenius is fixed by the `p ^ (2 * k)`-power Frobenius. No
reverse containment is claimed: the twisted fixed group is in general a proper subgroup of the
untwisted one over the quadratic extension. -/
theorem fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius :
    fixedSubgroup (twistedFrobenius p k A) ≤ fixedSubgroup (frobenius p (2 * k) A) := by
  have hsq : (show Monoid.End _ from twistedFrobenius p k A) ^ 2 = frobenius p (2 * k) A :=
    (pow_two (show Monoid.End _ from twistedFrobenius p k A)).trans
      (twistedFrobenius_comp_self p k A)
  rw [← hsq]
  exact TauCeti.fixedSubgroup_le_fixedSubgroup_pow _ 2

/-- **Every matrix entry of a point fixed by the twisted Frobenius lies in the subring fixed by the
`p ^ (2 * k)`-power Frobenius.** For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`
that subring is the field of `p ^ (2 * k)` elements, so this is the statement that the graph-twisted
type-`E₆` family at Frobenius parameter `q = p ^ k` is realized by `54 × 54` matrices over
`𝔽_{q ^ 2}`. Without those hypotheses the subring need not be a finite field; at `k = 0` it is all
of `A`. -/
theorem mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self {g : points A}
    (hg : twistedFrobenius p k A g = g) (i j : Fin 54) :
    ((g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) :
        _root_.Matrix (Fin 54) (Fin 54) A) i j ∈ frobeniusFixedSubring A p (2 * k) := by
  refine (frobenius_eq_self_iff p (2 * k) A g).mp ?_ i j
  exact fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius p k A
    (mem_fixedSubgroup.mpr hg)

end

end TauCeti.E6DoubledMinuscule
