/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.RepresentationTheory.OfMulAction
import TauCeti.RepresentationTheory.Coinvariants
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Invariants

/-!
# Orbit-sum bases of permutation invariants

Let a group `G` act on a finite set `X`, and let `k` be a commutative ring. A vector of the
permutation module `k[X]` is fixed by `G` exactly when its coefficients are constant on the
`G`-orbits, so the invariant submodule is free with basis the **orbit sums**
`∑_{x ∈ O} x`, one for each orbit `O`. No hypothesis on `k` or on the order of `G` is needed,
in contrast with the normalized orbit averages of `TauCeti.ofMulActionOrbitBasis`.

For a subgroup `I` of `G`, an element `d` normalizing `I` permutes the `I`-orbits, and the
permutation module action of `d` sends the sum over an `I`-orbit to the sum over its image. When
`I` is normal, the quotient group `G ⧸ I` acts on the `I`-orbits and on the `I`-invariants of
`k[X]` (Mathlib's `Representation.quotientToInvariants`), and the orbit-sum basis identifies these
two representations of `G ⧸ I`: the `I`-invariants of a permutation module are the permutation
module on the `I`-orbits. Combined with the passage of equivalences to restrictions and to
quotient representations on invariants, equivalent permutation representations of `G` therefore
give equivalent permutation representations of `D ⧸ I` on the `I`-orbits, for every subgroup `D`
of `G` and every normal subgroup `I` of `D`.

This is the representation-theoretic input to the comparison of splitting of primes in
arithmetically equivalent number fields: there `G` is a Galois group acting on the cosets of two
almost-conjugate subgroups, `D` a decomposition group and `I` its inertia subgroup, and the
`D ⧸ I`-orbits on the `I`-orbits record the primes above a given one with their residue degrees.

## Main definitions

* `TauCeti.ofMulActionOrbitSumBasis`: the basis of orbit sums of the invariants of `k[X]`.
* `TauCeti.ofMulActionOrbitRelQuotientEquiv`: for a normal subgroup `I`, the permutation
  representation of `G ⧸ I` on the `I`-orbits is equivalent to the representation of `G ⧸ I` on
  the `I`-invariants of `k[X]`, sending an orbit to its orbit sum
  (`TauCeti.coe_ofMulActionOrbitRelQuotientEquiv_single`).

## Main statements

* `TauCeti.ofMulActionOrbitSumBasis_coeff`: an orbit sum has coefficient `1` on its orbit and `0`
  elsewhere.
* `TauCeti.ofMulActionOrbitSumBasis_repr_mk`: the coordinate of an invariant vector at an orbit is
  its coefficient at any point of the orbit.
* `TauCeti.ofMulActionOrbitSumBasis_eq_sum`: an orbit-sum basis vector is the sum of the standard
  basis vectors of its orbit.
* `TauCeti.ofMulAction_ofMulActionOrbitSumBasis`: an element normalizing `I` sends the sum over an
  `I`-orbit to the sum over its image orbit.
* `TauCeti.nonempty_equiv_ofMulAction_orbitRelQuotient`: equivalent permutation representations
  of `G` give equivalent permutation representations of `D ⧸ I` on the `I`-orbits.

## References

* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public noncomputable section

open MonoidAlgebra MulAction Module Representation

namespace TauCeti

section Basis

variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X] [Finite X]

/-- The coordinates of an invariant vector of `k[X]`: its coefficient at the chosen representative
of each orbit. -/
private def orbitSumCoordinates :
    (ofMulAction k G X).invariants ≃ₗ[k] (orbitRel.Quotient G X → k) where
  toFun w O := w.val.coeff O.out
  invFun z := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ z (Quotient.mk _ x)), fun g ↦ by
    ext x
    simp [coeff_ofMulAction, orbitRel.Quotient.quotient_smul_eq]⟩
  left_inv w := Subtype.ext <|
    eq_of_coeff_out_eq_of_forall_ofMulAction_eq
      (fun g ↦ by ext x; simp [coeff_ofMulAction, orbitRel.Quotient.quotient_smul_eq])
      w.property fun O ↦ by simp
  right_inv z := funext fun O ↦ by simp
  map_add' _ _ := funext fun _ ↦ by simp
  map_smul' _ _ := funext fun _ ↦ by simp

private theorem orbitSumCoordinates_apply (w : (ofMulAction k G X).invariants)
    (O : orbitRel.Quotient G X) : orbitSumCoordinates k G X w O = w.val.coeff O.out :=
  rfl

/-- **The orbit-sum basis of the invariants of a permutation module.** For a group `G` acting on a
finite set `X`, the `G`-invariants of `k[X]` are free over any commutative ring `k`, with basis the
sums `∑_{x ∈ O} x` over the orbits `O`. -/
def ofMulActionOrbitSumBasis :
    Basis (orbitRel.Quotient G X) k (ofMulAction k G X).invariants :=
  .ofEquivFun (orbitSumCoordinates k G X)

variable {k G X}

/-- The orbit-sum coordinate of an invariant vector at the orbit of `x` is its coefficient at
`x`. -/
@[simp]
theorem ofMulActionOrbitSumBasis_repr_mk (w : (ofMulAction k G X).invariants) (x : X) :
    (ofMulActionOrbitSumBasis k G X).repr w (Quotient.mk _ x) = w.val.coeff x := by
  obtain ⟨g, hg⟩ : ∃ g : G, g • x = (Quotient.mk (orbitRel G X) x).out :=
    Quotient.mk_out (s := orbitRel G X) x
  rw [ofMulActionOrbitSumBasis, Basis.ofEquivFun_repr_apply, orbitSumCoordinates_apply, ← hg,
    coeff_smul_of_forall_ofMulAction_eq w.property]

/-- An orbit-sum basis vector has coefficient `1` on its orbit and `0` elsewhere. -/
@[simp]
theorem ofMulActionOrbitSumBasis_coeff [DecidableEq (orbitRel.Quotient G X)]
    (O : orbitRel.Quotient G X) (x : X) :
    (ofMulActionOrbitSumBasis k G X O).val.coeff x = if Quotient.mk _ x = O then 1 else 0 := by
  rw [← ofMulActionOrbitSumBasis_repr_mk, Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- An orbit-sum basis vector is the sum of the standard basis vectors of its orbit. -/
theorem ofMulActionOrbitSumBasis_eq_sum [Fintype X] [DecidableEq (orbitRel.Quotient G X)]
    (O : orbitRel.Quotient G X) :
    (ofMulActionOrbitSumBasis k G X O).val =
      ∑ x ∈ Finset.univ.filter (fun x ↦ Quotient.mk (orbitRel G X) x = O), single x 1 := by
  classical
  ext x
  rw [ofMulActionOrbitSumBasis_coeff, coeff_sum, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

end Basis

section Normalizer

variable {k G X : Type*} [CommRing k] [Group G] [MulAction G X] [Finite X]

/-- The permutation module action of `g` sends an `H`-orbit sum to the `H`-orbit sum of `O'` as
soon as `g` carries the orbit `O` onto `O'`. -/
private theorem ofMulAction_orbitSum_of_forall_iff (H : Subgroup G) (g : G)
    {O O' : orbitRel.Quotient H X}
    (h : ∀ x : X, Quotient.mk (orbitRel H X) (g⁻¹ • x) = O ↔ Quotient.mk (orbitRel H X) x = O') :
    ofMulAction k G X g (ofMulActionOrbitSumBasis k H X O).val =
      (ofMulActionOrbitSumBasis k H X O').val := by
  classical
  ext x
  simp [coeff_ofMulAction, h]

/-- **Orbit sums under the normalizer.** An element `g` normalizing a subgroup `H` sends the sum
over an `H`-orbit to the sum over its image orbit. -/
theorem ofMulAction_ofMulActionOrbitSumBasis (H : Subgroup G)
    (g : Subgroup.normalizer (H : Set G)) (O : orbitRel.Quotient H X) :
    ofMulAction k G X g (ofMulActionOrbitSumBasis k H X O).val =
      (ofMulActionOrbitSumBasis k H X (MulAction.normalizerOrbitRelQuotientMap H g O)).val := by
  refine ofMulAction_orbitSum_of_forall_iff H g fun x ↦ ?_
  have hx : (MulAction.normalizerOrbitRelQuotientEquiv H g).symm (Quotient.mk _ x) =
      Quotient.mk (orbitRel H X) ((g : G)⁻¹ • x) :=
    MulAction.normalizerOrbitRelQuotientEquiv_symm_apply H g x
  induction O using Quotient.inductionOn' with | h y => ?_
  rw [← hx, Equiv.symm_apply_eq, MulAction.normalizerOrbitRelQuotientEquiv_apply,
    MulAction.normalizerOrbitRelQuotientMap_apply]

end Normalizer

section Normal

variable (k : Type*) {G X : Type*} [CommRing k] [Group G] [MulAction G X] [Finite X]
  (H : Subgroup G)

/-- The orbit-sum basis, read in the `H`-invariants of the permutation module of `G`, which is
the form Mathlib's `Representation.quotientToInvariants` uses. -/
private def quotientOrbitSumBasis :
    Basis (orbitRel.Quotient H X) k (invariants ((ofMulAction k G X).comp H.subtype)) :=
  (ofMulActionOrbitSumBasis k H X).map
    (LinearEquiv.ofEq _ _ (by rw [ofMulAction_comp_subtype]))

/-- The linear equivalence sending an `H`-orbit to its orbit sum. -/
private def orbitSumLinearEquiv :
    k[orbitRel.Quotient H X] ≃ₗ[k] invariants ((ofMulAction k G X).comp H.subtype) :=
  (MonoidAlgebra.basis _ k).equiv (quotientOrbitSumBasis k H) (Equiv.refl _)

private theorem coe_orbitSumLinearEquiv_single (O : orbitRel.Quotient H X) (r : k) :
    (orbitSumLinearEquiv k H (single O r) : k[X]) =
      r • (ofMulActionOrbitSumBasis k H X O : k[X]) := by
  have h : (single O r : k[orbitRel.Quotient H X]) = r • MonoidAlgebra.basis _ k O := by simp
  rw [h, map_smul, orbitSumLinearEquiv, Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_smul,
    quotientOrbitSumBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]

variable [H.Normal]

/-- **The invariants of a permutation module under a normal subgroup.** For a normal subgroup `H`
of `G`, the permutation representation of `G ⧸ H` on the `H`-orbits in `X` is equivalent to the
representation of `G ⧸ H` on the `H`-invariants of `k[X]`, by sending an orbit to its orbit sum. -/
def ofMulActionOrbitRelQuotientEquiv :
    (ofMulAction k (G ⧸ H) (orbitRel.Quotient H X)).Equiv
      ((ofMulAction k G X).quotientToInvariants H) :=
  .mk (orbitSumLinearEquiv k H) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H g => ?_
    have hg : g ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer_eq_top_iff.mpr ‹_›).symm ▸ Subgroup.mem_top g
    refine (MonoidAlgebra.basis _ k).ext fun O ↦ ?_
    induction O using Quotient.inductionOn' with | h x => ?_
    apply Subtype.ext
    have h := ofMulAction_ofMulActionOrbitSumBasis (k := k) H ⟨g, hg⟩ (Quotient.mk'' x)
    rw [MulAction.normalizerOrbitRelQuotientMap_apply] at h
    simp only at h
    simp [coe_orbitSumLinearEquiv_single, h]

/-- The equivalence `TauCeti.ofMulActionOrbitRelQuotientEquiv` sends `r` times an orbit to `r`
times its orbit sum. -/
@[simp]
theorem coe_ofMulActionOrbitRelQuotientEquiv_single (O : orbitRel.Quotient H X) (r : k) :
    (ofMulActionOrbitRelQuotientEquiv k H (single O r) : k[X]) =
      r • (ofMulActionOrbitSumBasis k H X O : k[X]) :=
  coe_orbitSumLinearEquiv_single k H O r

end Normal

section Restriction

variable (k : Type*) {G X Y : Type*} [CommRing k] [Group G] [MulAction G X] [MulAction G Y]
  [Finite X] [Finite Y]

/-- **Equivalent permutation representations have equivalent orbit representations.** If the
permutation representations of `G` on `X` and on `Y` are equivalent, then for every subgroup `D`
of `G` and every normal subgroup `I` of `D`, the permutation representations of `D ⧸ I` on the
`I`-orbits in `X` and in `Y` are equivalent. -/
theorem nonempty_equiv_ofMulAction_orbitRelQuotient
    (e : (ofMulAction k G X).Equiv (ofMulAction k G Y)) (D : Subgroup G) (I : Subgroup D)
    [I.Normal] :
    Nonempty ((ofMulAction k (D ⧸ I) (orbitRel.Quotient I X)).Equiv
      (ofMulAction k (D ⧸ I) (orbitRel.Quotient I Y))) := by
  have e' := e.res D.subtype
  rw [ofMulAction_comp_subtype, ofMulAction_comp_subtype] at e'
  exact ⟨(ofMulActionOrbitRelQuotientEquiv k I).trans
    ((e'.quotientToInvariants I).trans (ofMulActionOrbitRelQuotientEquiv k I).symm)⟩

end Restriction

end TauCeti
