/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.RepresentationTheory.OfMulAction

/-!
# Orbit-sum bases of permutation invariants

Let a group `Γ` act on a finite type `X` and let `k` be a commutative ring. A vector of the
permutation representation `k[X]` is invariant exactly when its coefficients are constant along
the orbits, so the orbit sums `∑_{x ∈ O} x`, one for each orbit `O`, form a basis of the invariant
subspace, and the coordinate of an invariant vector on `O` is its common coefficient along `O`.
No division is involved: unlike the normalized orbit averages of `TauCeti.ofMulActionOrbitBasis`,
this basis exists over every commutative ring.

Now let `I` be a subgroup of a group `D` acting on `X`. An element of `D` normalizing `I`
permutes the `I`-orbits, and it sends the orbit sum of an `I`-orbit to the orbit sum of the image
orbit. When `I` is normal, the quotient `D ⧸ I` acts on the set of `I`-orbits, and the orbit sums
identify its permutation representation with Mathlib's representation
`Representation.quotientToInvariants` of `D ⧸ I` on the `I`-invariants of `k[X]`. This is how the
invariants of an inertia group in a permutation representation of a decomposition group are
computed.

## Main declarations

* `TauCeti.mem_invariants_ofMulAction_iff`: a vector of `k[X]` is invariant exactly when its
  coefficients are constant along orbits.
* `TauCeti.ofMulActionOrbitSumBasis`: the orbit-sum basis of the invariants of `k[X]`.
* `TauCeti.ofMulActionOrbitSumBasis_repr_mk`: the coordinate of an invariant vector on the orbit
  of `x` is its coefficient at `x`.
* `TauCeti.ofMulActionOrbitSumBasis_eq_sum`: the basis vector of an orbit is the sum of its
  points.
* `TauCeti.ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer`: an element normalizing `I`
  sends orbit sums to orbit sums.
* `TauCeti.ofMulActionOrbitSumEquiv`: for normal `I`, the permutation representation of `D ⧸ I`
  on the `I`-orbits is equivalent to the representation of `D ⧸ I` on the `I`-invariants of
  `k[X]`.
-/

public noncomputable section

open MonoidAlgebra MulAction Representation

namespace TauCeti

variable (k : Type*) {Γ X : Type*} [CommRing k] [Group Γ] [MulAction Γ X]

/-- A vector of the permutation representation `k[X]` is invariant exactly when its coefficients
are constant along orbits. -/
theorem mem_invariants_ofMulAction_iff {v : k[X]} :
    v ∈ (ofMulAction k Γ X).invariants ↔ ∀ (g : Γ) (x : X), v.coeff (g • x) = v.coeff x := by
  refine ⟨coeff_smul_of_forall_ofMulAction_eq, fun hv g ↦ ?_⟩
  ext x
  rw [coeff_ofMulAction, hv]

variable {D : Type*} [Group D] [MulAction D X] (I : Subgroup D)

/-- Restricting the permutation representation of `D` to a subgroup `I` gives the permutation
representation of `I`. -/
theorem ofMulAction_comp_subtype :
    (ofMulAction k D X).comp I.subtype = ofMulAction k I X := by
  ext
  simp [Subgroup.smul_def]

section Finite

variable [Finite X]

/-- The coordinates of an invariant vector of `k[X]`: its coefficient along each orbit. -/
private def orbitSumCoordinates :
    (ofMulAction k Γ X).invariants ≃ₗ[k] (orbitRel.Quotient Γ X → k) where
  toFun w := MulAction.orbitRelQuotientLift w.val.coeff
    ((mem_invariants_ofMulAction_iff k).1 w.property)
  invFun z := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ z (Quotient.mk _ x)),
    (mem_invariants_ofMulAction_iff k).2 fun g x ↦ by
      simp [orbitRel.Quotient.quotient_smul_eq]⟩
  map_add' w v := by
    funext O
    induction O using Quotient.inductionOn with
    | h x => simp
  map_smul' r w := by
    funext O
    induction O using Quotient.inductionOn with
    | h x => simp
  left_inv w := by
    ext x
    simp
  right_inv z := by
    funext O
    induction O using Quotient.inductionOn with
    | h x => simp

variable (Γ X) in
/-- The **orbit-sum basis** of the invariants of the permutation representation `k[X]` of a group
`Γ` acting on a finite type `X`: the basis vector indexed by an orbit `O` is the sum of the points
of `O` (`TauCeti.ofMulActionOrbitSumBasis_eq_sum`). It exists over every commutative ring. -/
def ofMulActionOrbitSumBasis :
    Module.Basis (orbitRel.Quotient Γ X) k (ofMulAction k Γ X).invariants :=
  .ofEquivFun (orbitSumCoordinates k)

/-- The coordinate of an invariant vector on the orbit of `x` is its coefficient at `x`. -/
@[simp]
theorem ofMulActionOrbitSumBasis_repr_mk (w : (ofMulAction k Γ X).invariants) (x : X) :
    (ofMulActionOrbitSumBasis k Γ X).repr w (Quotient.mk _ x) = w.val.coeff x :=
  MulAction.orbitRelQuotientLift_mk x

open Classical in
/-- The basis vector of an orbit `O` has coefficient `1` at the points of `O` and `0`
elsewhere. -/
theorem coeff_ofMulActionOrbitSumBasis (O : orbitRel.Quotient Γ X) (x : X) :
    (ofMulActionOrbitSumBasis k Γ X O).val.coeff x =
      if Quotient.mk (orbitRel Γ X) x = O then 1 else 0 := by
  rw [← ofMulActionOrbitSumBasis_repr_mk, Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

end Finite

/-- The basis vector of an orbit `O` is the sum of the points of `O`. -/
theorem ofMulActionOrbitSumBasis_eq_sum [Fintype X] [DecidableEq (orbitRel.Quotient Γ X)]
    (O : orbitRel.Quotient Γ X) :
    (ofMulActionOrbitSumBasis k Γ X O).val =
      ∑ x ∈ Finset.univ.filter (fun x ↦ Quotient.mk (orbitRel Γ X) x = O), single x 1 := by
  classical
  ext x
  rw [coeff_ofMulActionOrbitSumBasis]
  simp [coeff_sum, Finsupp.single_apply, eq_comm]

/-! ### Orbit sums of a subgroup -/

variable [Finite X]

/-- An element `d` normalizing a subgroup `I` sends the orbit sum of an `I`-orbit `O` to the
orbit sum of the image orbit `d • O`. -/
theorem ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer (d : D)
    (hd : d ∈ Subgroup.normalizer (I : Set D)) (O : orbitRel.Quotient I X) :
    ofMulAction k D X d (ofMulActionOrbitSumBasis k I X O).val =
      (ofMulActionOrbitSumBasis k I X
        (MulAction.normalizerOrbitRelQuotientEquiv I ⟨d, hd⟩ O)).val := by
  classical
  ext x
  have hx : MulAction.normalizerOrbitRelQuotientEquiv I ⟨d, hd⟩
      (Quotient.mk (orbitRel I X) (d⁻¹ • x)) = Quotient.mk (orbitRel I X) x := by
    simp
  rw [coeff_ofMulAction, coeff_ofMulActionOrbitSumBasis, coeff_ofMulActionOrbitSumBasis]
  exact if_congr (by rw [← hx, Equiv.apply_eq_iff_eq]) rfl rfl

/-- For a normal subgroup `I`, an element `d` sends the orbit sum of an `I`-orbit `O` to the orbit
sum of the translated orbit, under the action of `D ⧸ I` on the `I`-orbits. -/
theorem ofMulAction_ofMulActionOrbitSumBasis [I.Normal] (d : D) (O : orbitRel.Quotient I X) :
    ofMulAction k D X d (ofMulActionOrbitSumBasis k I X O).val =
      (ofMulActionOrbitSumBasis k I X ((d : D ⧸ I) • O)).val := by
  rw [ofMulAction_ofMulActionOrbitSumBasis_of_mem_normalizer k I d
    (by simp [Subgroup.normalizer_eq_top])]
  induction O using Quotient.inductionOn with
  | h x => simp

/-- **The invariants of a normal subgroup as a permutation representation.** For a normal
subgroup `I` of `D` acting on a finite type `X`, the representation of `D ⧸ I` on the
`I`-invariants of `k[X]` is equivalent to the permutation representation of `D ⧸ I` on the set of
`I`-orbits, by sending each orbit to its orbit sum. -/
def ofMulActionOrbitSumEquiv [I.Normal] :
    (ofMulAction k (D ⧸ I) (orbitRel.Quotient I X)).Equiv
      ((ofMulAction k D X).quotientToInvariants I) :=
  .mk (coeffLinearEquiv k ≪≫ₗ (ofMulActionOrbitSumBasis k I X).repr.symm ≪≫ₗ
      LinearEquiv.ofEq _ _ (by rw [ofMulAction_comp_subtype])) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H d =>
    refine LinearMap.ext fun v ↦ ?_
    induction v using induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw]
    | single O r =>
      apply Subtype.ext
      simp [ofMulAction_ofMulActionOrbitSumBasis]

/-- The equivalence `TauCeti.ofMulActionOrbitSumEquiv` sends the basis vector of an `I`-orbit `O`,
scaled by `r`, to `r` times the orbit sum of `O`. -/
@[simp]
theorem ofMulActionOrbitSumEquiv_single [I.Normal] (O : orbitRel.Quotient I X) (r : k) :
    (ofMulActionOrbitSumEquiv k I (single O r)).val =
      r • (ofMulActionOrbitSumBasis k I X O).val := by
  simp [ofMulActionOrbitSumEquiv]

/-- The inverse of `TauCeti.ofMulActionOrbitSumEquiv` reads off the coefficient of an `I`-invariant
vector along each `I`-orbit. -/
@[simp]
theorem coeff_ofMulActionOrbitSumEquiv_symm_mk [I.Normal]
    (w : invariants ((ofMulAction k D X).comp I.subtype)) (x : X) :
    ((ofMulActionOrbitSumEquiv k I).symm w).coeff (Quotient.mk _ x) = w.val.coeff x := by
  simp [ofMulActionOrbitSumEquiv]

end TauCeti
