/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.PNat.Defs
public import TauCeti.Combinatorics.PermutationTriple.CycleData

/-!
# Orders and geometry types of permutation triples

The order triple of a permutation triple records the orders of its monodromies at the ordered
branch points `0`, `1`, and `∞`.  It is the `abc` invariant used in the classification of
three-point covers.  Each entry is also the least common multiple of the corresponding full
cycle partition.

The reciprocal sum of the three orders determines whether the associated triangle-group
signature is spherical, Euclidean, or hyperbolic.  This file defines that trichotomy using exact
rational arithmetic and proves that both invariants are unchanged by relabeling the sheets or by
inverting all three permutations to change composition convention.

## Main declarations

* `TauCeti.PermutationTriple.orderTriple`: the ordered triple of permutation orders.
* `TauCeti.GeometryType`: the spherical, Euclidean, and hyperbolic trichotomy.
* `TauCeti.GeometryType.ofOrders`: the geometry type determined by three orders.
* `TauCeti.PermutationTriple.geometryType`: the geometry type of a permutation triple.
* `TauCeti.PermutationTriple.geometryType_eq_of_sum_eq`: equality of reciprocal order sums
  determines equality of geometry types.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §2.4.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n m : ℕ}

/-- The ordered triple of the orders of the monodromies at `0`, `1`, and `∞`. -/
noncomputable def orderTriple (t : PermutationTriple n) : ℕ × ℕ × ℕ :=
  (orderOf t.σ0, orderOf t.σ1, orderOf t.σinf)

@[simp]
theorem orderTriple_σ0 (t : PermutationTriple n) : t.orderTriple.1 = orderOf t.σ0 :=
  (rfl)

@[simp]
theorem orderTriple_σ1 (t : PermutationTriple n) : t.orderTriple.2.1 = orderOf t.σ1 :=
  (rfl)

@[simp]
theorem orderTriple_σinf (t : PermutationTriple n) : t.orderTriple.2.2 = orderOf t.σinf :=
  (rfl)

/-- The entries of the order triple are the least common multiples of the corresponding full
cycle partitions. -/
theorem orderTriple_eq_lcm_cycleData (t : PermutationTriple n) :
    t.orderTriple = (t.cycleData.1.lcm, t.cycleData.2.1.lcm, t.cycleData.2.2.lcm) := by
  simp only [orderTriple, cycleData_σ0, cycleData_σ1, cycleData_σinf,
    Equiv.Perm.lcm_parts_partition]

/-- The trivial triple has order triple `(1, 1, 1)`. -/
@[simp]
theorem orderTriple_one : (1 : PermutationTriple n).orderTriple = (1, 1, 1) := by
  simp [orderTriple]

/-- Relabeling the sheets does not change the order triple. -/
@[simp]
theorem orderTriple_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    orderTriple (τ • t) = orderTriple t := by
  simp only [orderTriple, smul_σ0, smul_σ1, smul_σinf, Prod.mk.injEq]
  exact ⟨(SemiconjBy.orderOf_eq τ
      (by simp [SemiconjBy, mul_assoc] : SemiconjBy τ t.σ0 (τ * t.σ0 * τ⁻¹))).symm,
    (SemiconjBy.orderOf_eq τ
      (by simp [SemiconjBy, mul_assoc] : SemiconjBy τ t.σ1 (τ * t.σ1 * τ⁻¹))).symm,
    (SemiconjBy.orderOf_eq τ
      (by simp [SemiconjBy, mul_assoc] :
        SemiconjBy τ t.σinf (τ * t.σinf * τ⁻¹))).symm⟩

/-- Transporting the sheet labels along an equivalence does not change the order triple. -/
@[simp]
theorem orderTriple_transport (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    orderTriple (transport e t) = orderTriple t := by
  simp only [orderTriple, transport_apply_σ0, transport_apply_σ1, transport_apply_σinf,
    Prod.mk.injEq]
  exact ⟨e.permCongrHom.orderOf_eq t.σ0,
    e.permCongrHom.orderOf_eq t.σ1, e.permCongrHom.orderOf_eq t.σinf⟩

/-- Inverting all three components does not change their ordered triple of orders. -/
theorem orderTriple_inv_components (t : PermutationTriple n) :
    (orderOf t.σ0⁻¹, orderOf t.σ1⁻¹, orderOf t.σinf⁻¹) = t.orderTriple := by
  simp [orderTriple, orderOf_inv]

/-- Isomorphic permutation triples have the same order triple. -/
theorem orderTriple_eq_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    orderTriple t = orderTriple t' := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (orderTriple_smul τ t).symm

end PermutationTriple

/-- The geometry type determined by the reciprocal sum of three monodromy orders. -/
inductive GeometryType : Type
  | spherical
  | euclidean
  | hyperbolic
  deriving DecidableEq, Repr

namespace GeometryType

/-- Classify three positive orders as spherical, Euclidean, or hyperbolic according as their
reciprocal sum is greater than, equal to, or less than one. -/
def ofOrders (abc : ℕ+ × ℕ+ × ℕ+) : GeometryType :=
  let s : ℚ := (abc.1 : ℚ)⁻¹ + (abc.2.1 : ℚ)⁻¹ + (abc.2.2 : ℚ)⁻¹
  if 1 < s then .spherical else if s = 1 then .euclidean else .hyperbolic

/-- Three orders have spherical type exactly when their reciprocal sum is greater than one. -/
@[simp]
theorem ofOrders_eq_spherical_iff (abc : ℕ+ × ℕ+ × ℕ+) :
    ofOrders abc = .spherical ↔
      1 < (abc.1 : ℚ)⁻¹ + (abc.2.1 : ℚ)⁻¹ + (abc.2.2 : ℚ)⁻¹ := by
  simp only [ofOrders]
  split_ifs with hgt heq
  · exact ⟨fun _ => hgt, fun _ => rfl⟩
  · exact ⟨False.elim, fun h => (hgt h).elim⟩
  · exact ⟨False.elim, fun h => (hgt h).elim⟩

/-- Three orders have Euclidean type exactly when their reciprocal sum is one. -/
@[simp]
theorem ofOrders_eq_euclidean_iff (abc : ℕ+ × ℕ+ × ℕ+) :
    ofOrders abc = .euclidean ↔
      (abc.1 : ℚ)⁻¹ + (abc.2.1 : ℚ)⁻¹ + (abc.2.2 : ℚ)⁻¹ = 1 := by
  simp only [ofOrders]
  by_cases hgt : 1 < (abc.1 : ℚ)⁻¹ + (abc.2.1 : ℚ)⁻¹ + (abc.2.2 : ℚ)⁻¹
  · simp [hgt, ne_of_gt hgt]
  · simp [hgt]

/-- Three orders have hyperbolic type exactly when their reciprocal sum is less than one. -/
@[simp]
theorem ofOrders_eq_hyperbolic_iff (abc : ℕ+ × ℕ+ × ℕ+) :
    ofOrders abc = .hyperbolic ↔
      (abc.1 : ℚ)⁻¹ + (abc.2.1 : ℚ)⁻¹ + (abc.2.2 : ℚ)⁻¹ < 1 := by
  simp only [ofOrders]
  split_ifs with hgt heq
  · exact ⟨False.elim,
      fun h => (not_lt_of_ge hgt.le h).elim⟩
  · exact ⟨False.elim, fun h => by simp [heq] at h⟩
  · have hlt : (abc.1 : ℚ)⁻¹ + (abc.2.1 : ℚ)⁻¹ + (abc.2.2 : ℚ)⁻¹ < 1 :=
      lt_of_le_of_ne (le_of_not_gt hgt) heq
    exact ⟨fun _ => hlt, fun _ => rfl⟩

end GeometryType

namespace PermutationTriple

variable {n : ℕ}

/-- The spherical, Euclidean, or hyperbolic geometry type of a permutation triple, determined by
the exact rational reciprocal sum of its three component orders. -/
noncomputable def geometryType (t : PermutationTriple n) : GeometryType :=
  GeometryType.ofOrders
    ((⟨orderOf t.σ0, orderOf_pos _⟩ : ℕ+), (⟨orderOf t.σ1, orderOf_pos _⟩ : ℕ+),
      (⟨orderOf t.σinf, orderOf_pos _⟩ : ℕ+))

/-- A permutation triple is spherical exactly when the reciprocal sum of its component orders is
greater than one. -/
@[simp]
theorem geometryType_eq_spherical_iff (t : PermutationTriple n) :
    t.geometryType = .spherical ↔
      1 < (orderOf t.σ0 : ℚ)⁻¹ + (orderOf t.σ1 : ℚ)⁻¹ + (orderOf t.σinf : ℚ)⁻¹ := by
  simp [geometryType]

/-- A permutation triple is Euclidean exactly when the reciprocal sum of its component orders is
one. -/
@[simp]
theorem geometryType_eq_euclidean_iff (t : PermutationTriple n) :
    t.geometryType = .euclidean ↔
      (orderOf t.σ0 : ℚ)⁻¹ + (orderOf t.σ1 : ℚ)⁻¹ + (orderOf t.σinf : ℚ)⁻¹ = 1 := by
  simp [geometryType]

/-- A permutation triple is hyperbolic exactly when the reciprocal sum of its component orders is
less than one. -/
@[simp]
theorem geometryType_eq_hyperbolic_iff (t : PermutationTriple n) :
    t.geometryType = .hyperbolic ↔
      (orderOf t.σ0 : ℚ)⁻¹ + (orderOf t.σ1 : ℚ)⁻¹ + (orderOf t.σinf : ℚ)⁻¹ < 1 := by
  simp [geometryType]

/-- Two permutation triples have the same geometry type if the reciprocal sums of their order
triples are equal. -/
theorem geometryType_eq_of_sum_eq {t t' : PermutationTriple n}
    (h : (t.orderTriple.1 : ℚ)⁻¹ + (t.orderTriple.2.1 : ℚ)⁻¹ + (t.orderTriple.2.2 : ℚ)⁻¹ =
      (t'.orderTriple.1 : ℚ)⁻¹ + (t'.orderTriple.2.1 : ℚ)⁻¹ + (t'.orderTriple.2.2 : ℚ)⁻¹) :
    t.geometryType = t'.geometryType := by
  simp only [orderTriple_σ0, orderTriple_σ1, orderTriple_σinf] at h
  cases h' : t'.geometryType <;> simpa [h] using h'

/-- Relabeling the sheets does not change the geometry type. -/
@[simp]
theorem geometryType_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    geometryType (τ • t) = geometryType t := by
  apply congrArg GeometryType.ofOrders
  apply Prod.ext
  · apply PNat.eq
    exact congrArg Prod.fst (orderTriple_smul τ t)
  · apply Prod.ext <;> apply PNat.eq
    · exact congrArg (fun abc => abc.2.1) (orderTriple_smul τ t)
    · exact congrArg (fun abc => abc.2.2) (orderTriple_smul τ t)

/-- Transporting the sheet labels along an equivalence does not change the geometry type. -/
@[simp]
theorem geometryType_transport {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    geometryType (transport e t) = geometryType t := by
  apply congrArg GeometryType.ofOrders
  apply Prod.ext
  · apply PNat.eq
    exact congrArg Prod.fst (orderTriple_transport e t)
  · apply Prod.ext <;> apply PNat.eq
    · exact congrArg (fun abc => abc.2.1) (orderTriple_transport e t)
    · exact congrArg (fun abc => abc.2.2) (orderTriple_transport e t)

/-- The trivial permutation triple has spherical geometry type. -/
@[simp]
theorem geometryType_one : (1 : PermutationTriple n).geometryType = .spherical := by
  norm_num [geometryType, GeometryType.ofOrders]

/-- Inverting all three components, as in the opposite composition convention, does not change
the geometry type computed from their orders. -/
theorem geometryType_inv_components (t : PermutationTriple n) :
    GeometryType.ofOrders
        ((⟨orderOf t.σ0⁻¹, orderOf_pos _⟩ : ℕ+),
          (⟨orderOf t.σ1⁻¹, orderOf_pos _⟩ : ℕ+),
          (⟨orderOf t.σinf⁻¹, orderOf_pos _⟩ : ℕ+)) =
      t.geometryType := by
  apply congrArg GeometryType.ofOrders
  apply Prod.ext
  · exact PNat.eq (orderOf_inv t.σ0)
  · apply Prod.ext
    · exact PNat.eq (orderOf_inv t.σ1)
    · exact PNat.eq (orderOf_inv t.σinf)

/-- Isomorphic permutation triples have the same geometry type. -/
theorem geometryType_eq_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    geometryType t = geometryType t' := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (geometryType_smul τ t).symm

end PermutationTriple

end TauCeti
