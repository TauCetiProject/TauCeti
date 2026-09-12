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

`TauCeti.E6DoubledMinuscule.groupScheme` is the doubled minuscule Kostant toral-closure carrier
built on `V(ϖ₁) ⊕ V(ϖ₆)` inside `GL₅₄` over `ℤ`, and its point group over a commutative ring `A`
of exponential characteristic `p` carries two pinned endomorphisms: the `p ^ k`-power Frobenius
`TauCeti.E6DoubledMinuscule.frobenius`, which raises every matrix entry to its `p ^ k`-th power,
and the graph automorphism `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints`, which is
conjugation by a signed monomial matrix realizing the order-two symmetry of the `E₆` diagram. This
file composes them into

```text
twistedFrobenius = γ₂ ∘ Frob_q,      q = p ^ k,
```

Using the naturality of the graph automorphism and its involutivity, the file proves

```text
twistedFrobenius ∘ twistedFrobenius = Frob_(q ^ 2).
```

The required commutation is not a computation about the carrier, and nothing here reproves it. The
graph automorphism is conjugation by `TauCeti.E6DoubledMinuscule.graphAutomorphismMatrix`, whose
entries are `0` and `±1`, so it is natural in the coefficient ring by
`TauCeti.E6DoubledMinuscule.pointsMap_comp_graphAutomorphismPoints`, while the Frobenius is the
map on points induced by a ring endomorphism of that same coefficient ring, by
`TauCeti.E6DoubledMinuscule.frobenius_eq_pointsMap`; the commutation is the Frobenius instance of
that naturality.

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
this is the field-of-definition containment asked of a graph-twisted Steinberg map of type `E₆`.
At `k = 0` the exponent `q ^ 2` is `1` and the fixed subring is all of `A`. Only the containment is
proved; no reverse containment is claimed, and nothing here identifies this carrier with a pinned
simply connected Chevalley--Demazure group of type `E₆`, nor asserts that either fixed group is
finite, is perfect, or is simple.

## Main definitions

* `TauCeti.E6DoubledMinuscule.twistedFrobenius`: the composite `γ₂ ∘ Frob_q` on the doubled
  type-`E₆` point group.

## Main results

* `TauCeti.E6DoubledMinuscule.twistedFrobenius_rootSubgroupPoints` and
  `TauCeti.E6DoubledMinuscule.twistedFrobenius_weightTorusPoints`: the equations on the pinned
  numbered root subgroups and split torus, which relabel by the `E₆` diagram involution and raise
  the parameter to its `p ^ k`-th power.
* `TauCeti.E6DoubledMinuscule.twistedFrobenius_twistedFrobenius` and
  `TauCeti.E6DoubledMinuscule.twistedFrobenius_comp_self`: the square of the twisted map is the
  `p ^ (2 * k)`-power Frobenius, pointwise and as an identity of endomorphisms.
* `TauCeti.E6DoubledMinuscule.mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self` and
  `TauCeti.E6DoubledMinuscule.map_subtype_fixedSubgroup_twistedFrobenius_le`: the points it fixes
  lie among the points over the `p ^ (2 * k)`-power Frobenius-fixed subring, entrywise and as
  subgroups.

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

/-! ## The twisted Frobenius -/

/-- **The graph-twisted `p ^ k`-power Frobenius of the doubled type-`E₆` minuscule carrier**, the
composite `γ₂ ∘ Frob_q` of the carrier's graph automorphism with its Frobenius endomorphism.

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this has the formula asked of the
Steinberg map of the graph-twisted family `²E₆(p ^ k)`. No identification of this carrier with a
pinned simply connected Chevalley--Demazure group of type `E₆` is asserted here. -/
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
  simp only [Pi.pow_apply]

/-! ## The square relation -/

/-- **Applying the twisted Frobenius twice raises every matrix entry to its `p ^ (2 * k)`-th
power.** The graph factor is an involution and commutes with the Frobenius factor, the latter
because the graph automorphism is natural in the value ring, so the two copies of it cancel and the
two Frobenius exponents add. -/
@[simp]
theorem twistedFrobenius_twistedFrobenius (g : points A) :
    twistedFrobenius p k A (twistedFrobenius p k A g) = frobenius p (2 * k) A g := by
  have hcomm : frobenius p k A (graphAutomorphismPoints A (frobenius p k A g)) =
      graphAutomorphismPoints A (frobenius p k A (frobenius p k A g)) := by
    rw [frobenius_eq_pointsMap]
    exact DFunLike.congr_fun (pointsMap_comp_graphAutomorphismPoints (iterateFrobenius A p k)) _
  rw [twistedFrobenius_apply, twistedFrobenius_apply, hcomm,
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
  -- `Monoid.End` is definitionally a bundled `MonoidHom`; naming the twisted map at that type
  -- picks the composition monoid structure, in which its square is its composite with itself.
  let τ : Monoid.End (points A) := twistedFrobenius p k A
  have hsq : τ ^ 2 = frobenius p (2 * k) A :=
    (pow_two τ).trans (twistedFrobenius_comp_self p k A)
  rw [← hsq]
  exact TauCeti.fixedSubgroup_le_fixedSubgroup_pow τ 2

/-- **Every matrix entry of a point fixed by the twisted Frobenius lies in the subring fixed by the
`p ^ (2 * k)`-power Frobenius.** For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`
that subring is the field of `p ^ (2 * k)` elements, so this is the statement that the graph-twisted
type-`E₆` formula at Frobenius parameter `q = p ^ k` has entries in `𝔽_{q ^ 2}`. Without those
hypotheses the subring need not be a finite field; at `k = 0` it is all of `A`. -/
theorem mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self {g : points A}
    (hg : twistedFrobenius p k A g = g) (i j : Fin 54) :
    ((g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) :
        _root_.Matrix (Fin 54) (Fin 54) A) i j ∈ frobeniusFixedSubring A p (2 * k) := by
  refine (frobenius_eq_self_iff p (2 * k) A g).mp ?_ i j
  exact fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius p k A
    (mem_fixedSubgroup.mpr hg)

/-- **The points fixed by the twisted Frobenius lie among the points of the same carrier over the
`p ^ (2 * k)`-power Frobenius-fixed subring.** The corresponding statement for the Frobenius itself,
`TauCeti.E6DoubledMinuscule.map_subtype_fixedSubgroup_frobenius_eq`, is an equality; here only the
containment holds. -/
theorem map_subtype_fixedSubgroup_twistedFrobenius_le :
    (fixedSubgroup (twistedFrobenius p k A)).map (points A).subtype ≤
      (points ↥(frobeniusFixedSubring A p (2 * k))).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p (2 * k)).subtype) := by
  rw [← map_subtype_fixedSubgroup_frobenius_eq p (2 * k) A]
  exact Subgroup.map_mono (fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius p k A)

end

end TauCeti.E6DoubledMinuscule
