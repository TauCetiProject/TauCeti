/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortLong
public import Mathlib.Algebra.Group.Commutator

/-!
# The ordered long–short G₂ element commutator

For a short root `α` and a long root `β`, the commutator with the long-root element first has
four factors, in increasing total degree in `α` and `β`:
`α + β`, `2α + β`, `3α + β`, `3α + 2β`.
Its coefficients are `-c`, `-d`, `-a`, `b`, in the notation of the native collection formula
`TauCeti.DynkinType.chevalleyRootSubgroup_mul_of_g2_short_long`. In particular the highest-root
coefficient is `b`, rather than the `2b` appearing when the short-root element comes first.
This distinction matters for collecting arbitrary root products in a fixed order.

The result holds on every Kostant-stable lattice over every commutative value ring. Divisions
in the coefficients take place in `ℤ` before reduction to that ring, so characteristics two
and three are included. The four displayed root equations specify the full G₂ string; no
additional bracket or nilpotence assumptions on nonsimple root vectors are imposed.

The proof consumes the native collection formula above at the negative long-root parameter;
it does not require a separate operator calculation or the opposite commutator formula.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

variable {ht : G2.Valid} {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ z ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ w ∈ M, ρ z w ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator i))))

/-- The long–short G₂ element commutator, with factors in increasing total degree in `α`, `β`.
Here `α` is the short root, `β` is the long root, and the long-root element occurs first in the
commutator. The integer highest-root coefficient is the collection coefficient `b`, not `2b`.
All coefficients are computed before passage to the commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_g2_long_short
    {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let x := fun i w => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
    ⁅x β v, x α u⁆ =
      x γ ((-c : A) * (u * v)) * x δ ((-d : A) * (u ^ 2 * v)) *
        x ε ((-a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) := by
  have h := chevalleyRootSubgroup_mul_of_g2_short_long ht ρ M hM hnil hγ hδ hε hζ A u (-v)
  dsimp only at h ⊢
  simp only [mul_neg, neg_sq] at h
  have hc := congrArg (fun g =>
    chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) * g *
      (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))⁻¹) h
  simpa only [commutatorElement_def, ofAdd_neg, map_inv, mul_assoc,
    mul_inv_cancel, mul_one, mul_inv_cancel_left, neg_mul] using hc

end TauCeti.DynkinType
