/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.GroupTheory.GroupAction.Orbit.Card
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import Mathlib.RepresentationTheory.Equiv

/-!
# Orbit bases of permutation invariants

For a group acting on a finite type `Y`, a vector of `k[Y]` is invariant exactly when its
coefficients are constant along each orbit, so the invariant subspace is free on the orbit space.
Two normalizations of that basis are recorded here.

Over an arbitrary commutative ring, the basis vector of an orbit is the sum of the standard basis
vectors over that orbit. Over `ℚ`, dividing by the orbit size gives the orbit averages, which are
the images of the standard basis vectors under the projection onto the invariants; for a cyclic
action that projection agrees with averaging over any positive period, including a nonminimal one.
The acting group need not be finite in either case.

The orbit sums are visibly equivariant for anything that permutes the orbits. For a subgroup `N`
of `G`, an element of `G` normalizing `N` carries the sum over an `N`-orbit to the sum over the
translated orbit; when `N` is normal this exhibits the `G ⧸ N`-representation on the
`N`-invariants of `k[Y]`, Mathlib's `Representation.quotientToInvariants`, as the permutation
representation of `G ⧸ N` on the space of `N`-orbits.

## Main declarations

* `TauCeti.ofMulActionOrbitBasis`: the basis of normalized orbit sums over `ℚ`.
* `TauCeti.ofMulActionOrbitProjection`: projection onto the actual invariant subspace.
* `TauCeti.ofMulActionOrbitBasis_repr_projection`: projection coordinates as native
  finitely supported orbit sums.
* `TauCeti.ofMulActionOrbitProjection_eq_average`: the cyclic averaging formula.
* `TauCeti.ofMulActionOrbitSumBasis`: the basis of orbit sums, over any commutative ring, with
  `TauCeti.ofMulActionOrbitSumBasis_eq_sum` identifying its vectors with the orbit sums.
* `TauCeti.finrank_invariants_ofMulAction`: the invariants have rank the number of orbits.
* `TauCeti.ofMulActionOrbitBasis_eq_smul_ofMulActionOrbitSumBasis`: the orbit averages are the
  orbit sums divided by the orbit sizes.
* `TauCeti.ofMulAction_ofMulActionOrbitSumBasis_normalizer`,
  `TauCeti.ofMulAction_ofMulActionOrbitSumBasis_smul`: orbit sums are equivariant for the
  normalizer of the acting subgroup, and for the quotient group when it is normal.
* `TauCeti.quotientToInvariantsOrbitEquiv`: the `N`-invariants of `k[Y]` are the permutation
  representation of `G ⧸ N` on the `N`-orbits.
-/
public noncomputable section

open MonoidAlgebra MulAction Module Representation

namespace TauCeti

variable (Γ I : Type*) [Group Γ] [MulAction Γ I]

variable [Fintype I]

private def orbitCoordinates : (ofMulAction ℚ Γ I).invariants ≃ₗ[ℚ]
    (orbitRel.Quotient Γ I → ℚ) where
  toFun w O := (Nat.card O.orbit : ℚ) * w.val.coeff O.out
  invFun z := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun i ↦
      z (Quotient.mk (orbitRel Γ I) i) /
        (Nat.card (orbitRel.Quotient.orbit (Quotient.mk (orbitRel Γ I) i)) : ℚ)),
    TauCeti.forall_ofMulAction_eq_of_coeff_smul_eq fun g i ↦ by
      simp only [Finsupp.coe_equivFunOnFinite_symm, orbitRel.Quotient.quotient_smul_eq]⟩
  left_inv w := by
    apply Subtype.ext
    apply TauCeti.eq_of_coeff_out_eq_of_forall_ofMulAction_eq (fun g ↦ ?_) w.property
    · intro O
      simp only [Finsupp.coe_equivFunOnFinite_symm, Quotient.out_eq']
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero)
    · exact TauCeti.forall_ofMulAction_eq_of_coeff_smul_eq (fun g i ↦ by
        simp only [Finsupp.coe_equivFunOnFinite_symm, orbitRel.Quotient.quotient_smul_eq]) g
  right_inv z := by
    funext O
    simp only [Finsupp.coe_equivFunOnFinite_symm, Quotient.out_eq']
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero)
  map_add' w v := by
    funext O
    -- Addition in the invariant subtype and coefficient evaluation reduce pointwise.
    change (Nat.card O.orbit : ℚ) * (w.val.coeff O.out + v.val.coeff O.out) = _
    exact mul_add _ _ _
  map_smul' r w := by
    funext O
    -- Scalar multiplication in the invariant subtype reduces to multiplication of coefficients.
    change (Nat.card O.orbit : ℚ) * (r * w.val.coeff O.out) =
      r * ((Nat.card O.orbit : ℚ) * w.val.coeff O.out)
    ring

/-- The normalized orbit sums form a basis of the invariant subspace of the rational
permutation representation. No finiteness assumption on the acting group is needed. -/
def ofMulActionOrbitBasis :
    Basis (orbitRel.Quotient Γ I) ℚ (ofMulAction ℚ Γ I).invariants :=
  Basis.ofEquivFun (orbitCoordinates Γ I)

/-- The coordinate of a fixed vector is its coefficient at an orbit representative,
multiplied by the size of that orbit. -/
theorem ofMulActionOrbitBasis_repr (w : (ofMulAction ℚ Γ I).invariants)
    (O : orbitRel.Quotient Γ I) :
    (ofMulActionOrbitBasis Γ I).repr w O = (Nat.card O.orbit : ℚ) * w.val.coeff O.out := by
  rfl

/-- The orbit coordinate can be computed at any member of the orbit. -/
theorem ofMulActionOrbitBasis_repr_of_mem (w : (ofMulAction ℚ Γ I).invariants)
    (O : orbitRel.Quotient Γ I) (i : I) (hi : Quotient.mk (orbitRel Γ I) i = O) :
    (ofMulActionOrbitBasis Γ I).repr w O = (Nat.card O.orbit : ℚ) * w.val.coeff i := by
  obtain ⟨g, hg⟩ : ∃ g : Γ, g • i = (Quotient.mk (orbitRel Γ I) i).out :=
    Quotient.mk_out (s := orbitRel Γ I) i
  have hc := TauCeti.coeff_smul_of_forall_ofMulAction_eq w.property g i
  rw [hg, hi] at hc
  rw [ofMulActionOrbitBasis_repr, hc]

open Classical in
/-- An orbit-average basis vector has constant coefficient equal to the reciprocal orbit
size on its orbit, and zero coefficient elsewhere. -/
@[simp]
theorem ofMulActionOrbitBasis_coeff (O : orbitRel.Quotient Γ I) (i : I) :
    ((ofMulActionOrbitBasis Γ I O).val).coeff i =
      if Quotient.mk (orbitRel Γ I) i = O then (Nat.card O.orbit : ℚ)⁻¹ else 0 := by
  classical
  have h := ofMulActionOrbitBasis_repr_of_mem Γ I (ofMulActionOrbitBasis Γ I O)
    (Quotient.mk (orbitRel Γ I) i) i rfl
  by_cases hi : Quotient.mk (orbitRel Γ I) i = O
  · simp only [hi, Basis.repr_self, Finsupp.single_eq_same] at h
    rw [ite_eq_left hi]
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero)
    rw [← h, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero)]
  · simp only [Basis.repr_self, Finsupp.single_apply, Ne.symm hi, ite_false] at h
    rw [ite_eq_right hi]
    exact (mul_eq_zero.mp h.symm).resolve_left
      (Nat.cast_ne_zero.mpr (orbitRel.Quotient.card_orbit_ne_zero
        (Quotient.mk (orbitRel Γ I) i)))

open Classical in
/-- An orbit-average basis vector is the normalized sum of its ambient basis vectors. -/
theorem ofMulActionOrbitBasis_eq_sum (O : orbitRel.Quotient Γ I) :
    (ofMulActionOrbitBasis Γ I O).val = (Nat.card O.orbit : ℚ)⁻¹ •
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), single i 1 := by
  classical
  ext i
  rw [ofMulActionOrbitBasis_coeff]
  simp [coeff_sum, Finsupp.single_apply, eq_comm]

/-- The projection onto the invariant subspace sending each standard basis vector to the
average of its orbit. -/
def ofMulActionOrbitProjection : ℚ[I] →ₗ[ℚ] (ofMulAction ℚ Γ I).invariants :=
  (MonoidAlgebra.basis I ℚ).constr ℚ fun i ↦
    ofMulActionOrbitBasis Γ I (Quotient.mk (orbitRel Γ I) i)

/-- The invariant projection sends a single to the corresponding multiple of its orbit average. -/
@[simp]
theorem ofMulActionOrbitProjection_single (i : I) (r : ℚ) :
    ofMulActionOrbitProjection Γ I (single i r) =
      r • ofMulActionOrbitBasis Γ I (Quotient.mk (orbitRel Γ I) i) := by
  have h : single i r = r • MonoidAlgebra.basis I ℚ i := by simp
  rw [h, map_smul]
  congr 1
  exact Basis.constr_basis _ _ _ _

/-- Projection coordinates are the native finitely supported orbit sums of the original
coefficients. -/
theorem ofMulActionOrbitBasis_repr_projection (x : ℚ[I]) :
    (ofMulActionOrbitBasis Γ I).repr (ofMulActionOrbitProjection Γ I x) =
      x.coeff.mapDomain (Quotient.mk (orbitRel Γ I)) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Finsupp.mapDomain_add]
  | single i r => simp

open Classical in
/-- Each projection coordinate is the sum of the original coefficients on that orbit. -/
theorem ofMulActionOrbitBasis_repr_projection_apply (x : ℚ[I])
    (O : orbitRel.Quotient Γ I) :
    (ofMulActionOrbitBasis Γ I).repr (ofMulActionOrbitProjection Γ I x) O =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O), x.coeff i := by
  classical
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Finset.sum_add_distrib]
  | single i r => simp [Finsupp.single_apply, eq_comm]

/-- The orbit projection is the identity on the actual invariant subspace. -/
@[simp]
theorem ofMulActionOrbitProjection_invariant (w : (ofMulAction ℚ Γ I).invariants) :
    ofMulActionOrbitProjection Γ I w.val = w := by
  classical
  apply (ofMulActionOrbitBasis Γ I).repr.injective
  ext O
  rw [ofMulActionOrbitBasis_repr_projection_apply, ofMulActionOrbitBasis_repr]
  have hc (i : I) (hi : Quotient.mk (orbitRel Γ I) i = O) :
      w.val.coeff i = w.val.coeff O.out := by
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero)
    rw [← ofMulActionOrbitBasis_repr_of_mem Γ I w O i hi, ofMulActionOrbitBasis_repr]
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i ↦ Quotient.mk (orbitRel Γ I) i = O),
        w.val.coeff O.out := Finset.sum_congr rfl fun i hi ↦ hc i (Finset.mem_filter.mp hi).2
    _ = _ := by rw [Finset.sum_const, O.card_filter_quotient_mk, nsmul_eq_mul]

/-- For a cyclic action, orbit projection is the average over any positive period of the
permutation representation. The period need not be minimal. -/
theorem ofMulActionOrbitProjection_eq_average (g : Γ)
    (hg : ∀ a, a ∈ Subgroup.zpowers g) (k : ℕ) (hk : 0 < k)
    (hperiod : (ofMulAction ℚ Γ I g) ^ k = 1) (x : ℚ[I]) :
    (ofMulActionOrbitProjection Γ I x).val =
      (k : ℚ)⁻¹ • ∑ r ∈ Finset.range k, ofMulAction ℚ Γ I (g ^ r) x := by
  classical
  let ρ := ofMulAction ℚ Γ I
  have hkx : ρ (g ^ k) x = x := by rw [map_pow, hperiod]; rfl
  have hshift : (∑ r ∈ Finset.range k, ρ (g ^ (r + 1)) x) =
      ∑ r ∈ Finset.range k, ρ (g ^ r) x := by
    apply add_right_cancel (b := x)
    calc
      _ = ∑ r ∈ Finset.range (k + 1), ρ (g ^ r) x := by
        simpa using (Finset.sum_range_succ' (fun r ↦ ρ (g ^ r) x) k).symm
      _ = _ := by rw [Finset.sum_range_succ, hkx]
  let y : ℚ[I] := (k : ℚ)⁻¹ • ∑ r ∈ Finset.range k, ρ (g ^ r) x
  have hy : y ∈ ρ.invariants := by
    apply (ρ.mem_invariants_iff_of_forall_mem_zpowers g hg y).2
    have hstep (r : ℕ) : ρ g (ρ (g ^ r) x) = ρ (g ^ (r + 1)) x := by
      rw [pow_succ', map_mul]
      rfl
    dsimp [y]
    rw [map_smul, map_sum]
    simp_rw [hstep]
    rw [hshift]
  have hproj : ofMulActionOrbitProjection Γ I y = ofMulActionOrbitProjection Γ I x := by
    apply (ofMulActionOrbitBasis Γ I).repr.injective
    rw [ofMulActionOrbitBasis_repr_projection, ofMulActionOrbitBasis_repr_projection]
    simp only [y, ρ, coeff_smul, coeff_sum, Finsupp.mapDomain_smul,
      Finsupp.mapDomain_finsetSum, TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction,
      Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
    exact_mod_cast hk.ne'
  have hid := ofMulActionOrbitProjection_invariant Γ I ⟨y, hy⟩
  exact (congrArg Subtype.val (hproj.symm.trans hid))

/-! ### The orbit-sum basis of the invariants, over an arbitrary commutative ring -/

section OrbitSum

variable (k : Type*) [CommRing k] (G Y : Type*) [Group G] [MulAction G Y] [Finite Y]

/-- Reading off the coefficient at the chosen representative of each orbit identifies the
invariants of the permutation representation `k[Y]` with the functions on the orbit space.
Unlike `TauCeti.orbitCoordinates` this involves no division, so it is available over an
arbitrary commutative ring. -/
private def orbitSumCoordinates :
    (ofMulAction k G Y).invariants ≃ₗ[k] (orbitRel.Quotient G Y → k) where
  toFun w O := w.val.coeff O.out
  invFun z := ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun y ↦
      z (Quotient.mk (orbitRel G Y) y)),
    TauCeti.forall_ofMulAction_eq_of_coeff_smul_eq fun g y ↦ by
      simp only [Finsupp.coe_equivFunOnFinite_symm, orbitRel.Quotient.quotient_smul_eq]⟩
  left_inv w := by
    apply Subtype.ext
    apply TauCeti.eq_of_coeff_out_eq_of_forall_ofMulAction_eq (fun g ↦ ?_) w.property
    · intro O
      simp
    · exact TauCeti.forall_ofMulAction_eq_of_coeff_smul_eq (fun g y ↦ by
        simp only [Finsupp.coe_equivFunOnFinite_symm, orbitRel.Quotient.quotient_smul_eq]) g
  right_inv z := by
    funext O
    simp
  map_add' w v := rfl
  map_smul' r w := rfl

/-- **The orbit sums are a basis of the invariants of a permutation representation.** For a group
`G` acting on a finite type `Y` and any commutative ring `k`, the invariant subspace of `k[Y]` is
free on the orbit space, and `TauCeti.ofMulActionOrbitSumBasis_eq_sum` identifies the basis vector
at an orbit with the sum of the standard basis vectors over that orbit. The acting group need not
be finite. -/
def ofMulActionOrbitSumBasis :
    Basis (orbitRel.Quotient G Y) k (ofMulAction k G Y).invariants :=
  Basis.ofEquivFun (orbitSumCoordinates k G Y)

/-- The orbit-sum coordinate of an invariant vector is its coefficient at an orbit
representative. -/
theorem ofMulActionOrbitSumBasis_repr (w : (ofMulAction k G Y).invariants)
    (O : orbitRel.Quotient G Y) :
    (ofMulActionOrbitSumBasis k G Y).repr w O = w.val.coeff O.out := by
  rfl

/-- The orbit-sum coordinate can be computed at any member of the orbit. -/
theorem ofMulActionOrbitSumBasis_repr_of_mem (w : (ofMulAction k G Y).invariants)
    (O : orbitRel.Quotient G Y) (y : Y) (hy : Quotient.mk (orbitRel G Y) y = O) :
    (ofMulActionOrbitSumBasis k G Y).repr w O = w.val.coeff y := by
  obtain ⟨g, hg⟩ : ∃ g : G, g • y = (Quotient.mk (orbitRel G Y) y).out :=
    Quotient.mk_out (s := orbitRel G Y) y
  have hc := TauCeti.coeff_smul_of_forall_ofMulAction_eq w.property g y
  rw [hg, hy] at hc
  rw [ofMulActionOrbitSumBasis_repr, hc]

open Classical in
/-- An orbit-sum basis vector has coefficient `1` on its orbit and `0` elsewhere. -/
@[simp]
theorem ofMulActionOrbitSumBasis_coeff (O : orbitRel.Quotient G Y) (y : Y) :
    ((ofMulActionOrbitSumBasis k G Y O).val).coeff y =
      if Quotient.mk (orbitRel G Y) y = O then 1 else 0 := by
  classical
  have h := ofMulActionOrbitSumBasis_repr_of_mem k G Y (ofMulActionOrbitSumBasis k G Y O)
    (Quotient.mk (orbitRel G Y) y) y rfl
  rw [Basis.repr_self] at h
  rw [← h]
  simp [Finsupp.single_apply, eq_comm]

/-- **The invariants of a permutation representation have rank the number of orbits.** -/
theorem finrank_invariants_ofMulAction [StrongRankCondition k] :
    Module.finrank k (ofMulAction k G Y).invariants = Nat.card (orbitRel.Quotient G Y) :=
  Module.finrank_eq_nat_card_basis (ofMulActionOrbitSumBasis k G Y)

/-- **The orbit averages are the normalized orbit sums.** The rational orbit-average basis
`TauCeti.ofMulActionOrbitBasis` is the orbit-sum basis divided by the orbit sizes. -/
theorem ofMulActionOrbitBasis_eq_smul_ofMulActionOrbitSumBasis (O : orbitRel.Quotient Γ I) :
    ofMulActionOrbitBasis Γ I O = (Nat.card O.orbit : ℚ)⁻¹ • ofMulActionOrbitSumBasis ℚ Γ I O := by
  classical
  apply Subtype.ext
  ext i
  rw [ofMulActionOrbitBasis_coeff]
  simp [ofMulActionOrbitSumBasis_coeff]

end OrbitSum

section OrbitSumFinset

variable (k : Type*) [CommRing k] (G Y : Type*) [Group G] [MulAction G Y] [Fintype Y]

open Classical in
/-- **The orbit-sum basis vectors are the orbit sums.** -/
theorem ofMulActionOrbitSumBasis_eq_sum (O : orbitRel.Quotient G Y) :
    (ofMulActionOrbitSumBasis k G Y O).val =
      ∑ y ∈ Finset.univ.filter (fun y ↦ Quotient.mk (orbitRel G Y) y = O), single y 1 := by
  classical
  ext y
  rw [ofMulActionOrbitSumBasis_coeff]
  simp [coeff_sum, Finsupp.single_apply, eq_comm]

end OrbitSumFinset

/-! ### Equivariance of the orbit-sum basis -/

section Equivariant

variable (k : Type*) [CommRing k] {G : Type*} [Group G] (N : Subgroup G)
  (Y : Type*) [MulAction G Y] [Finite Y]

omit [Finite Y] in
/-- Restricting the permutation representation of `G` on `k[Y]` to a subgroup `N` is the
permutation representation of `N` on `k[Y]`. -/
theorem ofMulAction_comp_subtype :
    (ofMulAction k G Y).comp N.subtype = ofMulAction k N Y :=
  rfl

/-- **A normalizing element permutes the orbit sums.** An element of `G` normalizing `N` carries
the sum over an `N`-orbit to the sum over the translated orbit. -/
theorem ofMulAction_ofMulActionOrbitSumBasis_normalizer (g : Subgroup.normalizer (N : Set G))
    (O : orbitRel.Quotient N Y) :
    ofMulAction k G Y g (ofMulActionOrbitSumBasis k N Y O).val =
      (ofMulActionOrbitSumBasis k N Y (MulAction.normalizerOrbitRelQuotientMap N g O)).val := by
  classical
  ext y
  have hsymm : (MulAction.normalizerOrbitRelQuotientEquiv N g).symm
      (Quotient.mk (orbitRel N Y) y) = Quotient.mk (orbitRel N Y) ((g : G)⁻¹ • y) :=
    MulAction.normalizerOrbitRelQuotientEquiv_symm_apply N g y
  have happ : MulAction.normalizerOrbitRelQuotientEquiv N g O =
      MulAction.normalizerOrbitRelQuotientMap N g O := by
    induction O using Quotient.inductionOn' with
    | h z => simp
  have hiff : Quotient.mk (orbitRel N Y) ((g : G)⁻¹ • y) = O ↔
      Quotient.mk (orbitRel N Y) y = MulAction.normalizerOrbitRelQuotientMap N g O := by
    rw [← hsymm, ← happ, Equiv.symm_apply_eq]
  rw [coeff_ofMulAction, ofMulActionOrbitSumBasis_coeff, ofMulActionOrbitSumBasis_coeff]
  exact if_congr hiff rfl rfl

/-- **The orbit sums are equivariant for the quotient action.** For a normal subgroup `N` of `G`,
an element `g` of `G` carries the sum over an `N`-orbit to the sum over the orbit translated by
the class of `g` in `G ⧸ N`. -/
theorem ofMulAction_ofMulActionOrbitSumBasis_smul [N.Normal] (g : G)
    (O : orbitRel.Quotient N Y) :
    ofMulAction k G Y g (ofMulActionOrbitSumBasis k N Y O).val =
      (ofMulActionOrbitSumBasis k N Y ((g : G ⧸ N) • O)).val := by
  classical
  ext y
  have hmk : Quotient.mk (orbitRel N Y) (g⁻¹ • y) =
      ((g⁻¹ : G) : G ⧸ N) • Quotient.mk (orbitRel N Y) y :=
    (MulAction.orbitRel.Quotient.mk_smul_mk N g⁻¹ y).symm
  have hiff : Quotient.mk (orbitRel N Y) (g⁻¹ • y) = O ↔
      Quotient.mk (orbitRel N Y) y = (g : G ⧸ N) • O := by
    rw [hmk, QuotientGroup.mk_inv, inv_smul_eq_iff]
  rw [coeff_ofMulAction, ofMulActionOrbitSumBasis_coeff, ofMulActionOrbitSumBasis_coeff]
  exact if_congr hiff rfl rfl

omit [Finite Y] in
/-- The `N`-invariants of `k[Y]` computed through the restricted representation are the
`N`-invariants of the permutation representation of `N`. -/
theorem invariants_comp_subtype :
    Representation.invariants ((ofMulAction k G Y).comp N.subtype) =
      (ofMulAction k N Y).invariants := by
  rw [ofMulAction_comp_subtype]

/-- **The orbit-sum basis of the invariants of a subgroup.** This is
`TauCeti.ofMulActionOrbitSumBasis` for the restriction of the permutation representation of `G` to
a subgroup `N`; the restriction is the permutation representation of `N`, but the two carriers are
only definitionally equal, so the basis is transported explicitly. -/
def compSubtypeOrbitSumBasis :
    Basis (orbitRel.Quotient N Y) k
      (Representation.invariants ((ofMulAction k G Y).comp N.subtype)) :=
  (ofMulActionOrbitSumBasis k N Y).map
    (LinearEquiv.ofEq _ _ (invariants_comp_subtype k N Y).symm)

/-- The subgroup orbit-sum basis vectors are the orbit sums. -/
@[simp]
theorem coe_compSubtypeOrbitSumBasis (O : orbitRel.Quotient N Y) :
    (compSubtypeOrbitSumBasis k N Y O).val = (ofMulActionOrbitSumBasis k N Y O).val := by
  rfl

/-- The `G ⧸ N`-representation on the `N`-invariants of `k[Y]` sends an orbit-sum basis vector to
the orbit-sum basis vector at the translated orbit. -/
theorem quotientToInvariants_compSubtypeOrbitSumBasis [N.Normal] (g : G)
    (O : orbitRel.Quotient N Y) :
    (ofMulAction k G Y).quotientToInvariants N (g : G ⧸ N) (compSubtypeOrbitSumBasis k N Y O) =
      compSubtypeOrbitSumBasis k N Y ((g : G ⧸ N) • O) :=
  Subtype.ext (ofMulAction_ofMulActionOrbitSumBasis_smul k N Y g O)

/-- **The orbit sums identify the `N`-invariants with the permutation representation on
`N`-orbits.** For a normal subgroup `N` of a group `G` acting on a finite type `Y`, the
`G ⧸ N`-representation on the `N`-invariants of `k[Y]` is the permutation representation of
`G ⧸ N` on the space of `N`-orbits, the sum over an orbit corresponding to that orbit's standard
basis vector. -/
def quotientToInvariantsOrbitEquiv [N.Normal] :
    ((ofMulAction k G Y).quotientToInvariants N).Equiv
      (ofMulAction k (G ⧸ N) (orbitRel.Quotient N Y)) :=
  Representation.Equiv.mk
    ((compSubtypeOrbitSumBasis k N Y).equiv (MonoidAlgebra.basis _ k) (Equiv.refl _))
    fun q => by
      induction q using QuotientGroup.induction_on with
      | H g =>
        refine (compSubtypeOrbitSumBasis k N Y).ext fun O => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          quotientToInvariants_compSubtypeOrbitSumBasis, Basis.equiv_apply, Equiv.refl_apply,
          MonoidAlgebra.basis_apply, ofMulAction_single]

/-- The orbit-sum identification sends the sum over an `N`-orbit to that orbit's standard basis
vector. -/
@[simp]
theorem quotientToInvariantsOrbitEquiv_apply [N.Normal] (O : orbitRel.Quotient N Y) :
    quotientToInvariantsOrbitEquiv k N Y (compSubtypeOrbitSumBasis k N Y O) = single O 1 :=
  (compSubtypeOrbitSumBasis k N Y).equiv_apply (b' := MonoidAlgebra.basis _ k)
    (e := Equiv.refl _) (i := O)

end Equivariant

end TauCeti
