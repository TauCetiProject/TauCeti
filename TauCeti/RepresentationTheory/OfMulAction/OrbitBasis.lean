/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction
public import TauCeti.GroupTheory.GroupAction.Orbit.Card

/-!
# Orbit-average bases of permutation invariants

For an action on a finite type, normalized orbit sums form a basis of the invariant
subspace of the rational permutation representation. The acting group need not be finite.
This basis is the orbit-sum basis `TauCeti.invariantOrbitSumBasis` rescaled by the reciprocal
orbit sizes.
The coordinate of an invariant vector is its constant orbit coefficient times the orbit size.
The corresponding projection sums the original coefficients on each orbit. For a cyclic action,
it agrees with averaging over any positive period, including a nonminimal period.

## Main declarations

* `TauCeti.ofMulActionOrbitBasis`: the basis of normalized orbit sums.
* `TauCeti.ofMulActionOrbitBasis_eq_inv_smul_invariantOrbitSumBasis`: the orbit averages are
  the orbit sums divided by the orbit sizes.
* `TauCeti.ofMulActionOrbitProjection`: projection onto the actual invariant subspace.
* `TauCeti.ofMulActionOrbitBasis_repr_projection`: projection coordinates as native
  finitely supported orbit sums.
* `TauCeti.ofMulActionOrbitProjection_eq_average`: the cyclic averaging formula.
-/

public noncomputable section

open MonoidAlgebra MulAction Module Representation

namespace TauCeti

variable (Γ I : Type*) [Group Γ] [MulAction Γ I]

variable [Fintype I]

/-- The normalized orbit sums form a basis of the invariant subspace of the rational
permutation representation. No finiteness assumption on the acting group is needed. -/
def ofMulActionOrbitBasis :
    Basis (orbitRel.Quotient Γ I) ℚ (ofMulAction ℚ Γ I).invariants :=
  (invariantOrbitSumBasis ℚ Γ I).unitsSMul fun O ↦
    (Units.mk0 (Nat.card O.orbit : ℚ) (Nat.cast_ne_zero.mpr O.card_orbit_ne_zero))⁻¹

variable {Γ I} in
/-- The normalized orbit average of an orbit `O` is the orbit sum of `O` divided by the size
of `O`. -/
theorem ofMulActionOrbitBasis_eq_inv_smul_invariantOrbitSumBasis (O : orbitRel.Quotient Γ I) :
    ofMulActionOrbitBasis Γ I O = (Nat.card O.orbit : ℚ)⁻¹ • invariantOrbitSumBasis ℚ Γ I O := by
  simp [ofMulActionOrbitBasis, Basis.unitsSMul_apply, Units.smul_def]

/-- The coordinate of a fixed vector is its coefficient at an orbit representative,
multiplied by the size of that orbit. -/
theorem ofMulActionOrbitBasis_repr (w : (ofMulAction ℚ Γ I).invariants)
    (O : orbitRel.Quotient Γ I) :
    (ofMulActionOrbitBasis Γ I).repr w O = (Nat.card O.orbit : ℚ) * w.val.coeff O.out := by
  have h := invariantOrbitSumBasis_repr_mk w O.out
  rw [Quotient.out_eq] at h
  simp [ofMulActionOrbitBasis, h]

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
  simp [ofMulActionOrbitBasis_eq_inv_smul_invariantOrbitSumBasis, Set.indicator_apply,
    orbitRel.Quotient.mem_orbit]

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

end TauCeti
