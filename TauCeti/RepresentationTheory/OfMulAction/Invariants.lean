/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import Mathlib.RepresentationTheory.Invariants

/-!
# Orbit-sum bases of permutation invariants

Let a group `G` act on a finite type `X` and let `k` be a commutative ring. A vector of the
permutation representation `k[X]` is fixed by `G` exactly when its coefficients are constant on
`G`-orbits, so the orbit sums `∑ x ∈ O, x`, one for each orbit `O`, form a basis of the invariant
subspace, with coordinates the coefficients at orbit representatives. No division is involved,
so this works over every commutative ring.

For a subgroup `H`, an element `g` normalizing `H` permutes the `H`-orbits and sends the orbit
sum of an `H`-orbit to the orbit sum of its translate. For a normal subgroup `I`, the quotient
`G ⧸ I` therefore acts compatibly on the `I`-orbits
(`MulAction.orbitRel.Quotient.instMulActionQuotientGroup`) and on the `I`-invariants of `k[X]`
(`Representation.quotientToInvariants`), and the orbit-sum basis identifies the two: the
`I`-invariants of `k[X]` are, as a representation of `G ⧸ I`, the permutation representation on
the set of `I`-orbits. This is the comparison used to read off the action of a decomposition
group on the inertia invariants of a permutation module.

## Main declarations

* `TauCeti.ofMulActionOrbitSumBasis`: the orbit-sum basis of the invariants of `k[X]`, indexed
  by the orbits.
* `TauCeti.ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer`: an element normalizing `H`
  sends the orbit sum of an `H`-orbit to the orbit sum of its translate.
* `TauCeti.ofMulActionQuotientToInvariantsEquiv`: for a normal subgroup `I`, the `I`-invariants
  of `k[X]`, as a representation of `G ⧸ I`, are equivalent to the permutation representation
  of `G ⧸ I` on the `I`-orbits.
-/

public noncomputable section

open MonoidAlgebra MulAction Module

variable {k : Type*} [CommRing k] {G : Type*} [Group G] {X : Type*} [MulAction G X]

namespace TauCeti

section Basis

variable (k G X) [Finite X]

variable {k G X} in
/-- A vector of `k[X]` whose coefficients are constant on `G`-orbits is fixed by `G`. -/
private theorem ofMulAction_ofCoeff_comp_mk (f : orbitRel.Quotient G X → k) (g : G) :
    Representation.ofMulAction k G X g
        (ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ f (Quotient.mk'' x))) =
      ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ f (Quotient.mk'' x)) := by
  ext x
  simp only [Representation.coeff_ofMulAction, Finsupp.coe_equivFunOnFinite_symm]
  exact congrArg f orbitRel.Quotient.quotient_smul_eq

/-- The coordinates of an invariant vector of `k[X]`: its coefficients at the chosen orbit
representatives. Its inverse spreads a function on orbits out over the points of each orbit. -/
private def orbitSumCoordinates :
    (Representation.ofMulAction k G X).invariants ≃ₗ[k] (orbitRel.Quotient G X → k) where
  toFun w O := w.val.coeff O.out
  invFun z := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ z (Quotient.mk'' x)),
    ofMulAction_ofCoeff_comp_mk z⟩
  left_inv w := Subtype.ext <| eq_of_coeff_out_eq_of_forall_ofMulAction_eq
    (ofMulAction_ofCoeff_comp_mk fun O ↦ w.val.coeff O.out) w.property fun O ↦ by simp
  right_inv z := funext fun O ↦ by simp
  map_add' _ _ := funext fun _ ↦ by simp
  map_smul' _ _ := funext fun _ ↦ by simp

@[simp]
private theorem orbitSumCoordinates_apply (w : (Representation.ofMulAction k G X).invariants)
    (O : orbitRel.Quotient G X) : orbitSumCoordinates k G X w O = w.val.coeff O.out :=
  rfl

/-- **The orbit-sum basis.** For a group `G` acting on a finite type `X` and a commutative ring
`k`, the orbit sums form a basis of the `G`-invariants of the permutation representation `k[X]`,
indexed by the orbits. The acting group need not be finite. -/
def ofMulActionOrbitSumBasis :
    Basis (orbitRel.Quotient G X) k (Representation.ofMulAction k G X).invariants :=
  .ofEquivFun (orbitSumCoordinates k G X)

variable {k G X}

/-- The coordinate of an invariant vector at an orbit is its coefficient at any point of that
orbit. -/
@[simp]
theorem ofMulActionOrbitSumBasis_repr_mk (w : (Representation.ofMulAction k G X).invariants)
    (x : X) : (ofMulActionOrbitSumBasis k G X).repr w (Quotient.mk'' x) = w.val.coeff x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_out_eq (G := G) (ω := Quotient.mk'' x) rfl
  have h := coeff_smul_of_forall_ofMulAction_eq w.property g
    (Quotient.mk'' x : orbitRel.Quotient G X).out
  rw [hg] at h
  rw [ofMulActionOrbitSumBasis, Basis.ofEquivFun_repr_apply, orbitSumCoordinates_apply, h]

/-- The orbit sum of an orbit `O` has coefficient `1` at the points of `O` and `0` elsewhere. -/
@[simp]
theorem coeff_ofMulActionOrbitSumBasis [DecidableEq (orbitRel.Quotient G X)]
    (O : orbitRel.Quotient G X) (x : X) :
    (ofMulActionOrbitSumBasis k G X O).val.coeff x = if Quotient.mk'' x = O then 1 else 0 := by
  rw [← ofMulActionOrbitSumBasis_repr_mk, Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- The orbit sum of an orbit `O` is the sum of the basis vectors of `k[X]` at the points of
`O`. -/
theorem coe_ofMulActionOrbitSumBasis [Fintype X] [DecidableEq (orbitRel.Quotient G X)]
    (O : orbitRel.Quotient G X) :
    (ofMulActionOrbitSumBasis k G X O : k[X]) =
      ∑ x ∈ Finset.univ.filter (fun x ↦ Quotient.mk'' x = O), single x 1 := by
  classical
  ext x
  simp [coeff_ofMulActionOrbitSumBasis, coeff_sum, coeff_single, Finsupp.single_apply]

end Basis

section Normalizer

variable [Finite X]

/-- **Normalizing elements permute orbit sums.** An element `g` normalizing a subgroup `H` sends
the orbit sum of an `H`-orbit `O` to the orbit sum of its translate `g • O`. -/
@[simp]
theorem ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer {H : Subgroup G}
    (g : Subgroup.normalizer (H : Set G)) (O : orbitRel.Quotient H X) :
    Representation.ofMulAction k G X g (ofMulActionOrbitSumBasis k H X O) =
      ofMulActionOrbitSumBasis k H X (MulAction.normalizerOrbitRelQuotientMap H g O) := by
  classical
  ext x
  rw [Representation.coeff_ofMulAction, coeff_ofMulActionOrbitSumBasis,
    coeff_ofMulActionOrbitSumBasis]
  refine if_congr ?_ rfl rfl
  -- `g⁻¹ • x` lies in `O` exactly when `x` lies in `g • O`, by the permutation of `H`-orbits
  -- induced by `g`.
  induction O using Quotient.inductionOn' with | h y =>
  rw [MulAction.normalizerOrbitRelQuotientMap_apply,
    ← MulAction.normalizerOrbitRelQuotientEquiv_symm_apply, Equiv.symm_apply_eq,
    MulAction.normalizerOrbitRelQuotientEquiv_apply]

end Normalizer

section Normal

variable (k G X) [Finite X] (I : Subgroup G) [I.Normal]

/-- The orbit-sum basis of the `I`-invariants of `k[X]`, viewed inside the invariants of the
restriction of the permutation representation of `G` to `I`. -/
private def quotientOrbitSumBasis :
    Basis (orbitRel.Quotient I X) k
      (Representation.invariants ((Representation.ofMulAction k G X).comp I.subtype)) :=
  (ofMulActionOrbitSumBasis k I X).map
    (LinearEquiv.ofEq _ _ (by rw [Representation.ofMulAction_comp_subtype]))

omit [I.Normal] in
@[simp]
private theorem coe_quotientOrbitSumBasis (O : orbitRel.Quotient I X) :
    (quotientOrbitSumBasis k G X I O : k[X]) = ofMulActionOrbitSumBasis k I X O := by
  simp [quotientOrbitSumBasis]

/-- The linear equivalence underlying `TauCeti.ofMulActionQuotientToInvariantsEquiv`: it sends the
basis vector of an `I`-orbit to its orbit sum. -/
private def quotientToInvariantsLinearEquiv :
    k[orbitRel.Quotient I X] ≃ₗ[k]
      Representation.invariants ((Representation.ofMulAction k G X).comp I.subtype) :=
  (coeffLinearEquiv k).trans (quotientOrbitSumBasis k G X I).repr.symm

omit [I.Normal] in
variable {k G X I} in
@[simp]
private theorem coe_quotientToInvariantsLinearEquiv_single (O : orbitRel.Quotient I X) (r : k) :
    (quotientToInvariantsLinearEquiv k G X I (single O r) : k[X]) =
      r • (ofMulActionOrbitSumBasis k I X O : k[X]) := by
  simp [quotientToInvariantsLinearEquiv]

/-- **The `I`-invariants of a permutation representation.** For a normal subgroup `I` of `G`
and a finite `G`-set `X`, the representation of `G ⧸ I` on the `I`-invariants of `k[X]` is
equivalent to the permutation representation of `G ⧸ I` on the set of `I`-orbits. The
equivalence sends the basis vector of an `I`-orbit to its orbit sum. -/
def ofMulActionQuotientToInvariantsEquiv :
    (Representation.ofMulAction k (G ⧸ I) (orbitRel.Quotient I X)).Equiv
      ((Representation.ofMulAction k G X).quotientToInvariants I) :=
  .mk (quotientToInvariantsLinearEquiv k G X I) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H g =>
    -- As `I` is normal, `g` normalizes `I`, and it permutes the `I`-orbits as its class in
    -- `G ⧸ I` does.
    have hg : g ∈ Subgroup.normalizer (I : Set G) := by simp [Subgroup.normalizer_eq_top]
    refine (MonoidAlgebra.basis _ k).ext fun O ↦ Subtype.ext ?_
    induction O using Quotient.inductionOn' with | h x =>
    have h := ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer (k := k) ⟨g, hg⟩
      (Quotient.mk'' x)
    rw [MulAction.normalizerOrbitRelQuotientMap_apply] at h
    -- Both sides are evaluated by `coe_quotientToInvariantsLinearEquiv_single`; what remains is
    -- the normalizer lemma `h`.
    simpa using h.symm

variable {k G X I}

/-- The equivalence `TauCeti.ofMulActionQuotientToInvariantsEquiv` sends `r` times the basis
vector of an `I`-orbit `O` to `r` times the orbit sum of `O`. -/
@[simp]
theorem coe_ofMulActionQuotientToInvariantsEquiv_single (O : orbitRel.Quotient I X) (r : k) :
    (ofMulActionQuotientToInvariantsEquiv k G X I (single O r) : k[X]) =
      r • (ofMulActionOrbitSumBasis k I X O : k[X]) := by
  simp [ofMulActionQuotientToInvariantsEquiv]

/-- The inverse of `TauCeti.ofMulActionQuotientToInvariantsEquiv` reads off the coefficient of an
`I`-invariant vector at any point of an `I`-orbit. -/
@[simp]
theorem coeff_ofMulActionQuotientToInvariantsEquiv_symm_apply
    (w : Representation.invariants ((Representation.ofMulAction k G X).comp I.subtype)) (x : X) :
    ((ofMulActionQuotientToInvariantsEquiv k G X I).symm w).coeff (Quotient.mk'' x) =
      w.val.coeff x := by
  simp [ofMulActionQuotientToInvariantsEquiv, quotientToInvariantsLinearEquiv,
    quotientOrbitSumBasis]

end Normal

end TauCeti
