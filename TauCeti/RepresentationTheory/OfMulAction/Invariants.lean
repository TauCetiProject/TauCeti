/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction.OrbitBasis
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Orbit-sum bases of permutation invariants

Let a group `G` act on a finite type `X` and let `k` be a commutative ring. A vector of the
permutation representation `k[X]` is fixed by `G` exactly when its coefficients are constant on
`G`-orbits, so the orbit sums `∑ x ∈ O, x`, one for each orbit `O`, form a basis of the invariant
subspace, with coordinates the coefficients at orbit representatives. No division is involved,
so this works over every commutative ring; over `ℚ` the normalized orbit averages
`TauCeti.ofMulActionOrbitBasis` are its rescaling by the reciprocal orbit sizes.

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
* `TauCeti.ofMulActionOrbitBasis_eq_inv_smul_ofMulActionOrbitSumBasis`: over `ℚ`, the orbit
  averages are the orbit sums divided by the orbit sizes.
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

/-- The coordinates of an invariant vector of `k[X]`: its coefficients at the chosen orbit
representatives. Its inverse spreads a function on orbits out over the points of each orbit. -/
private def orbitSumCoordinates :
    (Representation.ofMulAction k G X).invariants ≃ₗ[k] (orbitRel.Quotient G X → k) where
  toFun w O := w.val.coeff O.out
  invFun z := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ z (Quotient.mk'' x)), fun g ↦ by
    ext x
    simp only [Representation.coeff_ofMulAction, Finsupp.coe_equivFunOnFinite_symm]
    exact congrArg z orbitRel.Quotient.quotient_smul_eq⟩
  left_inv w := Subtype.ext <| eq_of_coeff_out_eq_of_forall_ofMulAction_eq
    (fun g ↦ by
      ext x
      simp only [Representation.coeff_ofMulAction, Finsupp.coe_equivFunOnFinite_symm]
      exact congrArg (fun O : orbitRel.Quotient G X ↦ w.val.coeff O.out)
        orbitRel.Quotient.quotient_smul_eq)
    w.property fun O ↦ by simp
  right_inv z := funext fun O ↦ by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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
  exact h.symm

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

/-- Over `ℚ`, the normalized orbit average `TauCeti.ofMulActionOrbitBasis` of an orbit `O` is the
orbit sum of `O` divided by the size of `O`. -/
theorem ofMulActionOrbitBasis_eq_inv_smul_ofMulActionOrbitSumBasis {Γ I : Type*} [Group Γ]
    [MulAction Γ I] [Fintype I] (O : orbitRel.Quotient Γ I) :
    ofMulActionOrbitBasis Γ I O = (Nat.card O.orbit : ℚ)⁻¹ • ofMulActionOrbitSumBasis ℚ Γ I O := by
  classical
  ext i
  simp [coeff_ofMulActionOrbitSumBasis, Quotient.mk'']

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

/-- **The `I`-invariants of a permutation representation.** For a normal subgroup `I` of `G`
and a finite `G`-set `X`, the representation of `G ⧸ I` on the `I`-invariants of `k[X]` is
equivalent to the permutation representation of `G ⧸ I` on the set of `I`-orbits. The
equivalence sends the basis vector of an `I`-orbit to its orbit sum. -/
def ofMulActionQuotientToInvariantsEquiv :
    (Representation.ofMulAction k (G ⧸ I) (orbitRel.Quotient I X)).Equiv
      ((Representation.ofMulAction k G X).quotientToInvariants I) :=
  .mk ((coeffLinearEquiv k).trans (quotientOrbitSumBasis k G X I).repr.symm) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H g =>
    refine (MonoidAlgebra.basis _ k).ext fun O ↦ Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, basis_apply,
      Representation.ofMulAction_single, Representation.ofQuotient_coe_apply,
      coeffLinearEquiv_apply, coeff_single, Basis.repr_symm_single_one, quotientOrbitSumBasis,
      Basis.map_apply, LinearEquiv.coe_ofEq_apply, Representation.subrepresentation_apply,
      LinearMap.coe_restrict_apply]
    -- As `I` is normal, `g` normalizes `I`, and it permutes the `I`-orbits as its class in
    -- `G ⧸ I` does.
    rw [ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer
      ⟨g, Subgroup.normalizer_eq_top (H := I) ▸ Subgroup.mem_top g⟩]
    induction O using Quotient.inductionOn' with | h x =>
    rw [MulAction.normalizerOrbitRelQuotientMap_apply, MulAction.orbitRel.Quotient.mk_smul_mk]

variable {k G X I}

/-- The equivalence `TauCeti.ofMulActionQuotientToInvariantsEquiv` sends `r` times the basis
vector of an `I`-orbit `O` to `r` times the orbit sum of `O`. -/
@[simp]
theorem coe_ofMulActionQuotientToInvariantsEquiv_single (O : orbitRel.Quotient I X) (r : k) :
    (ofMulActionQuotientToInvariantsEquiv k G X I (single O r) : k[X]) =
      r • (ofMulActionOrbitSumBasis k I X O : k[X]) := by
  simp [ofMulActionQuotientToInvariantsEquiv, quotientOrbitSumBasis]

/-- The inverse of `TauCeti.ofMulActionQuotientToInvariantsEquiv` reads off the coefficient of an
`I`-invariant vector at any point of an `I`-orbit. -/
@[simp]
theorem coeff_ofMulActionQuotientToInvariantsEquiv_symm_apply
    (w : Representation.invariants ((Representation.ofMulAction k G X).comp I.subtype)) (x : X) :
    ((ofMulActionQuotientToInvariantsEquiv k G X I).symm w).coeff (Quotient.mk'' x) =
      w.val.coeff x := by
  simp [ofMulActionQuotientToInvariantsEquiv, quotientOrbitSumBasis]

end Normal

end TauCeti
