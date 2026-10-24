/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.RepresentationTheory.Coinvariants

/-!
# Commuting permutation representations and invariants of permutation representations

If monoids `G` and `H` act on a type `X` and the two actions commute, then the permutation
representations `Representation.ofMulAction k G X` and `Representation.ofMulAction k H X` on the
free `k`-module `k[X]` commute with each other. For the left and right multiplication actions of
a group `G`, that is, commuting actions of `G` and `Gᵐᵒᵖ`, this makes `k[X]` a `k[G]`-bimodule.
On `k[G]` itself, the left regular representation `Representation.ofMulAction k G G` is left
multiplication by the monomials `single g 1`. Its equivariant endomorphism corresponding to
`x : k[G]` under `Rep.leftRegularHomEquiv` is right multiplication by `x`.

When `G` and `H` are groups, `G` permutes the `H`-orbits, and the orbit sums of `k[X]` along the
`H`-orbits are equivariant: the sum of the coefficients of `g • v` along the `H`-orbit of `g • x`
is the sum of the coefficients of `v` along the `H`-orbit of `x`. Hence if `g` fixes
`∑ i ∈ s, h i • v` for a family `h : ι → H` and `#s` is cancellable in `k`, then the `H`-orbit
sums of `v` are invariant under `g`. The orbit sums of `v` are the finitely supported function
`v.coeff.mapDomain (Quotient.mk (MulAction.orbitRel H X))` on the orbit space.

For a finite group `G`, the coefficient of the norm `∑ g, g • v` at `x` is `∑ g, v(g • x)`. In
particular the norm of the basis vector at `x` has coefficient `|G_x|` at `x` and vanishes off the
orbit of `x`, while a vector fixed by `G` has constant coefficients along each orbit, so it is
determined by its coefficients at a set of orbit representatives. These are the inputs of the
computation of the low-degree Tate cohomology of `k[X]`.

Over a commutative ring `k`, the invariants of `k[X]` under a group `I` acting on a finite set `X`
are free on the orbit space `MulAction.orbitRel.Quotient I X`, with the orbit sums as basis. If `I`
is a normal subgroup of a group `D` acting on `X`, then `D ⧸ I` permutes the `I`-orbits, and the
orbit sums identify the permutation representation of `D ⧸ I` on the free module on the `I`-orbits
with the representation of `D ⧸ I` on the `I`-invariants of `k[X]` (Mathlib's
`Representation.quotientToInvariants`). In arithmetic applications `D` and `I` are a
decomposition group and its inertia subgroup, acting on the cosets of a subgroup of a finite
Galois group.

## Main results

* `TauCeti.commute_ofMulAction`: commuting actions on `X` give commuting permutation
  representations on `k[X]`.
* `TauCeti.single_mul_eq_smul_ofMulAction`: on `k[G]`, left multiplication by a monomial
  `single g c` is `c` times the left regular action of `g`.
* `Rep.leftRegularHomEquiv_symm_apply`: equivariant endomorphisms of the left regular
  representation are right multiplications.
* `TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction`: the orbit sums of `k[X]` are invariant
  under the permutation representation.
* `TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction_smul`: for commuting actions of `G` and `H`,
  the `H`-orbit sums of `g • v` at `g • x` are those of `v` at `x`.
* `TauCeti.mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum`: if `g` fixes
  `∑ i ∈ s, h i • v` and `#s` is cancellable, the `H`-orbit sums of `v` are `g`-invariant.
* `TauCeti.coeff_smul_of_forall_ofMulAction_eq`: a fixed vector of `k[X]` has the same coefficient
  at every point of an orbit.
* `TauCeti.eq_of_coeff_out_eq_of_forall_ofMulAction_eq`: two fixed vectors of `k[X]` agreeing at
  the chosen representative of every orbit are equal.
* `TauCeti.coeff_norm_ofMulAction`: the coefficients of the norm of a vector of `k[X]`.
* `TauCeti.coeff_norm_ofMulAction_single_self`,
  `TauCeti.coeff_norm_ofMulAction_single_of_notMem_orbit`: the norm of the basis vector at `x` has
  coefficient `|G_x|` at `x` and vanishes off the orbit of `x`.
* `TauCeti.mem_invariants_ofMulAction_iff`: a vector of `k[X]` is invariant exactly when its
  coefficients are constant along orbits.
* `TauCeti.invariantOrbitSumBasis`: the orbit-sum basis of the invariants of `k[X]`, indexed by
  the orbit space.
* `TauCeti.coeff_invariantOrbitSumBasis`, `TauCeti.invariantOrbitSumBasis_mk_eq_sum`: the basis
  vector at an orbit is the indicator of the orbit, the sum of the basis vectors at its points.
* `TauCeti.ofMulAction_invariantOrbitSumBasis_mk`: an element normalizing `I` sends the sum over
  the `I`-orbit of `x` to the sum over the `I`-orbit of its translate of `x`.
* `TauCeti.orbitSumEquiv`: for a normal subgroup `I`, the permutation representation of `D ⧸ I`
  on the `I`-orbits is equivalent to the representation of `D ⧸ I` on the `I`-invariants.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327. The right coset sums
  `⟨ξ, K⟩` of §3 Theorem 2(a) are the orbit sums for the right action of `PSL(2, ℤ)` on the
  integral matrices of positive determinant, which commutes with the left action.
-/

public section

namespace TauCeti

open Representation

variable {k G H X : Type*} [Semiring k] [Monoid G] [Monoid H] [MulAction G X] [MulAction H X]

/-- If the actions of `G` and `H` on `X` commute, then so do the permutation representations of
`G` and `H` on `k[X]`. -/
theorem commute_ofMulAction [SMulCommClass G H X] (g : G) (h : H) :
    Commute (ofMulAction k G X g) (ofMulAction k H X h) := by
  ext
  simp [smul_comm g h]

/-- On the monoid algebra `k[G]`, left multiplication by the monomial `single g c` is `c` times
the left regular representation of `g`. -/
theorem single_mul_eq_smul_ofMulAction (g : G) (c : k) (a : MonoidAlgebra k G) :
    MonoidAlgebra.single g c * a = c • ofMulAction k G G g a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [mul_add, ha, hb, map_add, smul_add]
  | single g' c' => simp [MonoidAlgebra.single_mul_single, MonoidAlgebra.smul_single]

section LeftRegular

open scoped MonoidAlgebra

variable {k G : Type*} [CommRing k] [Monoid G]

/-- The endomorphism of the left regular representation `k[G]` corresponding to `x`
under `Rep.leftRegularHomEquiv` is right multiplication by `x`. -/
@[simp↓]
theorem _root_.Rep.leftRegularHomEquiv_symm_apply (x a : k[G]) :
    ((Rep.leftRegularHomEquiv (Rep.leftRegular k G)).symm x).hom a = a * x := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, Rep.leftRegularHomEquiv_symm_single,
      TauCeti.single_mul_eq_smul_ofMulAction, one_smul]
  | add a b ha hb => rw [map_add, ha, hb, add_mul]
  | smul c a ha => rw [map_smul, ha, smul_mul_assoc]

end LeftRegular

/-! ### Orbit sums -/

open MonoidAlgebra _root_.MulAction

/-- The orbit sums `k[X] → (X ⧸ G →₀ k)` are invariant under the permutation representation. -/
@[simp]
theorem mapDomain_orbitRel_mk_coeff_ofMulAction {G : Type*} [Group G] [MulAction G X] (g : G)
    (v : k[X]) :
    (ofMulAction k G X g v).coeff.mapDomain (Quotient.mk (orbitRel G X)) =
      v.coeff.mapDomain (Quotient.mk (orbitRel G X)) := by
  induction v using induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.mapDomain_add, hv, hw]
  | single y r => simp [Quotient.sound (s := orbitRel G X) (mem_orbit y g)]

section Commuting

variable {G H : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [SMulCommClass G H X]

open scoped Finset

/-- **Equivariance of orbit sums.** If the actions of `G` and `H` on `X` commute, then the sum of
the coefficients of `g • v` along the `H`-orbit of `g • x` is the sum of the coefficients of `v`
along the `H`-orbit of `x`. -/
@[simp]
theorem mapDomain_orbitRel_mk_coeff_ofMulAction_smul (g : G) (v : k[X]) (x : X) :
    (ofMulAction k G X g v).coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦g • x⟧ =
      v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦x⟧ := by
  classical
  -- `g` maps distinct `H`-orbits to distinct `H`-orbits
  have hmk (y : X) : Quotient.mk (orbitRel H X) (g • y) = Quotient.mk _ (g • x) ↔
      Quotient.mk (orbitRel H X) y = Quotient.mk _ x := by
    simp [Quotient.eq, orbitRel_apply, mem_orbit_iff, ← smul_comm g]
  induction v using induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.mapDomain_add, hv, hw]
  | single y r => simp [Finsupp.single_apply, hmk]

/-- If the actions of `G` and `H` on `X` commute, `h : ι → H`, `#s` is cancellable in `k` and
`g • w = w` for `w = ∑ i ∈ s, h i • v`, then the `H`-orbit sums of `v` are invariant under `g`:
the coefficients of `v` have the same sum along the `H`-orbits of `g • x` and of `x`. -/
theorem mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum {ι : Type*} {s : Finset ι} {h : ι → H}
    {g : G} {v : k[X]} (hs : IsSMulRegular k #s)
    (hfix : ofMulAction k G X g (∑ i ∈ s, ofMulAction k H X (h i) v) =
      ∑ i ∈ s, ofMulAction k H X (h i) v) (x : X) :
    v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦g • x⟧ =
      v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦x⟧ := by
  -- the `H`-orbit sums of `∑ i ∈ s, h i • v` are `#s` times those of `v`
  exact hs <| by simpa [hfix, Finsupp.mapDomain_finsetSum] using
    mapDomain_orbitRel_mk_coeff_ofMulAction_smul (H := H) g (∑ i ∈ s, ofMulAction k H X (h i) v) x

end Commuting

/-! ### Norms and invariant vectors -/

section Norm

variable {G : Type*} [Group G] [MulAction G X]

/-- A vector of `k[X]` fixed by the permutation representation has the same coefficient at every
point of an orbit. -/
theorem coeff_smul_of_forall_ofMulAction_eq {v : k[X]} (hv : ∀ g, ofMulAction k G X g v = v)
    (g : G) (x : X) : v.coeff (g • x) = v.coeff x := by
  conv_rhs => rw [← hv g⁻¹]
  rw [coeff_ofMulAction, inv_inv]

/-- Two vectors of `k[X]` fixed by the permutation representation are equal as soon as they agree
at the chosen representative of every orbit. -/
theorem eq_of_coeff_out_eq_of_forall_ofMulAction_eq {v w : k[X]}
    (hv : ∀ g, ofMulAction k G X g v = v) (hw : ∀ g, ofMulAction k G X g w = w)
    (h : ∀ ω : MulAction.orbitRel.Quotient G X, v.coeff ω.out = w.coeff ω.out) : v = w := by
  ext x
  obtain ⟨g, hg⟩ : ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G X) x).out :=
    Quotient.mk_out (s := MulAction.orbitRel G X) x
  rw [← coeff_smul_of_forall_ofMulAction_eq hv g, ← coeff_smul_of_forall_ofMulAction_eq hw g, hg,
    h]

variable [Fintype G]

/-- The coefficient of the norm `∑ g, g • v` of `v : k[X]` at `x` is the sum of the coefficients of
`v` at the points `g • x`. -/
@[simp]
theorem coeff_norm_ofMulAction (v : k[X]) (x : X) :
    ((ofMulAction k G X).norm v).coeff x = ∑ g : G, v.coeff (g • x) := by
  simp only [Representation.norm, LinearMap.sum_apply, coeff_sum, Finsupp.finsetSum_apply,
    coeff_ofMulAction]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ ↦ rfl

/-- The norm of `single x r` has coefficient `|G_x| • r` at `x`, where `G_x` is the stabilizer
of `x`. -/
theorem coeff_norm_ofMulAction_single_self (x : X) (r : k) :
    ((ofMulAction k G X).norm (single x r)).coeff x = Nat.card (stabilizer G x) • r := by
  classical
  simp only [coeff_norm_ofMulAction, coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  congr 2
  ext g
  simp [eq_comm]

/-- The norm of `single x r` vanishes off the orbit of `x`. -/
theorem coeff_norm_ofMulAction_single_of_notMem_orbit {x y : X} (h : y ∉ orbit G x) (r : k) :
    ((ofMulAction k G X).norm (single x r)).coeff y = 0 := by
  classical
  refine (coeff_norm_ofMulAction _ _).trans (Finset.sum_eq_zero fun g _ ↦ ?_)
  rw [coeff_single, Finsupp.single_apply, ite_eq_right_iff]
  rintro rfl
  exact absurd ⟨g⁻¹, inv_smul_smul g y⟩ h

end Norm

end TauCeti

/-! ### The orbit-sum basis of the invariants -/

namespace TauCeti

open MonoidAlgebra _root_.MulAction Representation

section OrbitSumBasis

variable {k I X : Type*} [CommRing k] [Group I] [MulAction I X]

/-- A vector of `k[X]` is invariant under the permutation representation exactly when its
coefficients are constant along the orbits. -/
theorem mem_invariants_ofMulAction_iff {v : k[X]} :
    v ∈ (ofMulAction k I X).invariants ↔ ∀ (g : I) (x : X), v.coeff (g • x) = v.coeff x := by
  refine ⟨fun hv ↦ coeff_smul_of_forall_ofMulAction_eq hv, fun hv g ↦ ?_⟩
  ext x
  rw [coeff_ofMulAction, hv]

variable (k I X) [Finite X]

/-- The coefficients of an invariant vector of `k[X]`, as a function on the orbit space; the
inverse sends a function on the orbit space to the vector with that coefficient at each point of
the corresponding orbit. -/
private noncomputable def invariantsEquivFun :
    (ofMulAction k I X).invariants ≃ₗ[k] (orbitRel.Quotient I X → k) where
  toFun v ω := Quotient.liftOn' ω (v : k[X]).coeff fun _ _ ⟨g, hg⟩ ↦ by
    rw [← hg]
    exact coeff_smul_of_forall_ofMulAction_eq v.2 g _
  map_add' v w := funext fun ω ↦ Quotient.inductionOn' ω fun _ ↦ rfl
  map_smul' r v := funext fun ω ↦ Quotient.inductionOn' ω fun _ ↦ rfl
  invFun c := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ c ⟦x⟧),
    (mem_invariants_ofMulAction_iff).2 fun g x ↦ by simp⟩
  left_inv v := Subtype.ext <| by ext x; simp [Quotient.liftOn'_mk'']
  right_inv c := funext fun ω ↦ Quotient.inductionOn' ω fun x ↦ by simp [Quotient.liftOn'_mk'']

/-- **The orbit-sum basis.** For a group `I` acting on a finite set `X`, the invariants of the
permutation representation `k[X]` are free on the orbit space: the basis vector at an orbit `ω`
is the orbit sum `∑ x ∈ ω, x` (`TauCeti.invariantOrbitSumBasis_mk_eq_sum`). -/
noncomputable def invariantOrbitSumBasis :
    Module.Basis (orbitRel.Quotient I X) k (ofMulAction k I X).invariants :=
  .ofEquivFun (invariantsEquivFun k I X)

variable {k I X}

/-- The coordinate of an invariant vector at the orbit of `x` is its coefficient at `x`. -/
@[simp]
theorem invariantOrbitSumBasis_repr_mk (v : (ofMulAction k I X).invariants) (x : X) :
    (invariantOrbitSumBasis k I X).repr v ⟦x⟧ = (v : k[X]).coeff x := by
  simp [invariantOrbitSumBasis, invariantsEquivFun, Quotient.liftOn'_mk'']

/-- The basis vector at an orbit `ω` is the indicator function of `ω`. -/
@[simp]
theorem coeff_invariantOrbitSumBasis (ω : orbitRel.Quotient I X) (x : X) :
    (invariantOrbitSumBasis k I X ω : k[X]).coeff x = ω.orbit.indicator 1 x := by
  classical
  simp [invariantOrbitSumBasis, invariantsEquivFun, Set.indicator_apply, Pi.single_apply,
    orbitRel.Quotient.mem_orbit]

/-- The basis vector at the orbit of `x` is the sum of the basis vectors of `k[X]` at the points
of the orbit of `x`. -/
theorem invariantOrbitSumBasis_mk_eq_sum (x : X) [Fintype (orbit I x)] :
    (invariantOrbitSumBasis k I X ⟦x⟧ : k[X]) = ∑ y ∈ (orbit I x).toFinset, single y 1 := by
  classical
  ext y
  simp [coeff_invariantOrbitSumBasis, Set.indicator_apply, coeff_sum, Finsupp.finsetSum_apply,
    coeff_single, Finsupp.single_apply]

end OrbitSumBasis

/-! ### Equivariance of orbit sums under a normal subgroup -/

section Equivariance

variable (k : Type*) {D X : Type*} [CommRing k] [Group D] [MulAction D X] [Finite X]
  (I : Subgroup D)

variable {I} in
/-- **Orbit sums are equivariant.** An element `d` normalizing `I` sends the sum over the
`I`-orbit of `x` to the sum over the `I`-orbit of `d • x`. -/
theorem ofMulAction_invariantOrbitSumBasis_mk {d : D} (hd : d ∈ Subgroup.normalizer (I : Set D))
    (x : X) :
    ofMulAction k D X d (invariantOrbitSumBasis k I X ⟦x⟧) =
      invariantOrbitSumBasis k I X ⟦d • x⟧ := by
  ext y
  rw [coeff_ofMulAction, coeff_invariantOrbitSumBasis, coeff_invariantOrbitSumBasis]
  -- `d` permutes the `I`-orbits, sending the orbit of `d⁻¹ • y` to the orbit of `y`
  have h : (Quotient.mk'' (d⁻¹ • y) : orbitRel.Quotient I X) = ⟦x⟧ ↔
      (Quotient.mk'' y : orbitRel.Quotient I X) = ⟦d • x⟧ := by
    rw [← (MulAction.normalizerOrbitRelQuotientEquiv I ⟨d, hd⟩).apply_eq_iff_eq,
      MulAction.normalizerOrbitRelQuotientEquiv_apply,
      MulAction.normalizerOrbitRelQuotientEquiv_apply, smul_inv_smul]
  classical
  simp only [Set.indicator_apply, orbitRel.Quotient.mem_orbit, h, Pi.one_apply]

variable (X)

omit [Finite X] in
/-- The invariants of `k[X]` under the subgroup `I`, read through the permutation representation
of the ambient group, are those of the permutation representation of `I`. -/
theorem invariants_ofMulAction_comp_subtype :
    invariants ((ofMulAction k D X).comp I.subtype) = (ofMulAction k I X).invariants := by
  ext v
  simp [ofMulAction_subgroup]

/-- The linear isomorphism underlying `TauCeti.orbitSumEquiv`. -/
private noncomputable def orbitSumLinearEquiv :
    k[orbitRel.Quotient I X] ≃ₗ[k] invariants ((ofMulAction k D X).comp I.subtype) :=
  (MonoidAlgebra.basis _ k).equiv ((invariantOrbitSumBasis k I X).map
    (LinearEquiv.ofEq _ _ (invariants_ofMulAction_comp_subtype k X I).symm)) (.refl _)

private theorem coe_orbitSumLinearEquiv_single (ω : orbitRel.Quotient I X) :
    (orbitSumLinearEquiv k X I (single ω 1) : k[X]) = invariantOrbitSumBasis k I X ω := by
  simp [orbitSumLinearEquiv, ← MonoidAlgebra.basis_apply]

variable [I.Normal]

/-- **The orbit-sum equivalence.** For a normal subgroup `I`, the orbit sums identify the
permutation representation of `D ⧸ I` on the `I`-orbits with the representation of `D ⧸ I` on the
`I`-invariants of `k[X]`: the basis vector at an orbit goes to the sum over that orbit. -/
noncomputable def orbitSumEquiv :
    (ofMulAction k (D ⧸ I) (orbitRel.Quotient I X)).Equiv
      ((ofMulAction k D X).quotientToInvariants I) :=
  .mk (orbitSumLinearEquiv k X I) fun σ ↦ by
    induction σ using QuotientGroup.induction_on with | H d => ?_
    refine MonoidAlgebra.lhom_ext' fun ω ↦ LinearMap.ext_ring <| Subtype.ext ?_
    induction ω using Quotient.inductionOn with | h x => ?_
    simp [ofQuotient_coe_apply, coe_orbitSumLinearEquiv_single,
      ofMulAction_invariantOrbitSumBasis_mk k
        (by simp [Subgroup.normalizer_eq_top] : d ∈ Subgroup.normalizer (I : Set D))]

variable {k X I}

/-- The orbit-sum equivalence sends `r` times the basis vector at an orbit to `r` times the sum
over that orbit. -/
@[simp]
theorem coe_orbitSumEquiv_single (ω : orbitRel.Quotient I X) (r : k) :
    (orbitSumEquiv k X I (single ω r) : k[X]) = r • (invariantOrbitSumBasis k I X ω : k[X]) := by
  have hr : single ω r = r • single ω (1 : k) := by simp
  rw [hr, map_smul, Submodule.coe_smul]
  exact congrArg (r • ·) (coe_orbitSumLinearEquiv_single k X I ω)

end Equivariance

end TauCeti
