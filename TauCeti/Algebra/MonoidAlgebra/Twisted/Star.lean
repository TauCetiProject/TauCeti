/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.Complex.Order
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Trace
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# The star structure and Parseval positivity on a twisted group algebra

When `G` is a group, `k` is a commutative star semiring, and `α : G → G → kˣ` is a unitary factor
set (`star (α g h : k) = ((α g h)⁻¹ : k)`), `twistedMonoidAlgebra k G α` carries a canonical
conjugate-linear `StarRing` structure `star (of g) = ((α g g⁻¹)⁻¹ : k) • of g⁻¹`, functorial via
`starMap`. The basis `{of g}` is orthonormal for `(x, y) ↦ trace (star x * y)`, giving Parseval's
identity (`trace_star_mul_eq_finsupp_sum`, `trace_star_mul`, `trace_star_mul_self`) and showing
that over `ℂ` the canonical trace is a faithful positive functional (`tracePositiveFunctional`,
`nullSubmodule_tracePositiveFunctional`).

## Main definitions

* `TauCeti.IsUnitaryFactorSet`: class asserting `star (α g h : k) = ((α g h)⁻¹ : k)`.
* `TauCeti.TwistedMonoidAlgebra.instStarRing`, `instStarModule`, `starMap`,
  `tracePositiveFunctional`: canonical star structure, functoriality, and positive functional.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

open scoped ComplexOrder

namespace TauCeti

/-- A factor set `α : G → G → kˣ` is **unitary** with respect to a star structure on `k` when
every value satisfies `star (α g h : k) = ((α g h)⁻¹ : k)`. -/
class IsUnitaryFactorSet {k G : Type*} [CommSemiring k] [StarRing k] [Mul G]
    (α : G → G → kˣ) : Prop where
  /-- Every factor-set value has star equal to its unit inverse. -/
  star_val (g h : G) : star (α g h : k) = (((α g h)⁻¹ : kˣ) : k)

namespace IsUnitaryFactorSet

variable {k G : Type*} [CommSemiring k] [StarRing k] [Mul G] {α : G → G → kˣ}
  [IsUnitaryFactorSet α]

/-- The star of an inverse factor-set value recovers the value itself. -/
theorem star_inv_val (g h : G) : star (((α g h)⁻¹ : kˣ) : k) = (α g h : k) := by
  rw [← star_val (α := α) g h, star_star]

end IsUnitaryFactorSet

namespace TwistedMonoidAlgebra

open MulOpposite

private theorem factor_inv_mul_inv {k G : Type*} [CommSemiring k] [Group G]
    {α : G → G → kˣ} [IsFactorSet α] (g h : G) :
    α h⁻¹ g⁻¹ * α (g * h) (h⁻¹ * g⁻¹) * α g h = α h h⁻¹ * α g g⁻¹ := by
  have hc1 : α (g * h) (h⁻¹ * g⁻¹) * α g h = α h (h⁻¹ * g⁻¹) * α g g⁻¹ := by
    simpa [mul_assoc] using IsFactorSet.cocycle (α := α) g h (h⁻¹ * g⁻¹)
  have hc2 : α h h⁻¹ = α h⁻¹ g⁻¹ * α h (h⁻¹ * g⁻¹) := by
    simpa [IsFactorSet.one_left (α := α)] using IsFactorSet.cocycle (α := α) h h⁻¹ g⁻¹
  rw [mul_assoc, hc1, ← mul_assoc, ← hc2]

section StarRing

variable {k G : Type*} [CommSemiring k] [StarRing k] [Group G]
  {α : G → G → kˣ} [IsFactorSet α] [IsUnitaryFactorSet α]

private noncomputable def starRingHomOp :
    twistedMonoidAlgebra k G α →+* (twistedMonoidAlgebra k G α)ᵐᵒᵖ := by
  letI : Algebra k (twistedMonoidAlgebra k G α)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd k)
  refine (lift (α := α) (fun g ↦ op ((((α g g⁻¹)⁻¹ : kˣ) : k) • (of g⁻¹ :
      twistedMonoidAlgebra k G α)))
    (by simp [IsFactorSet.one_left (α := α)])
    (fun g h ↦ unop_injective ?_)).toRingHom
  have hunit : (α h h⁻¹)⁻¹ * (α g g⁻¹)⁻¹ * α h⁻¹ g⁻¹ =
      (α g h)⁻¹ * (α (g * h) (g * h)⁻¹)⁻¹ := by
    rw [mul_inv_rev, ← mul_inv, ← mul_inv, inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
    simpa [mul_assoc, mul_comm, mul_left_comm] using factor_inv_mul_inv (α := α) g h
  rw [unop_mul, unop_op, unop_op]
  conv_rhs =>
    rw [Algebra.smul_def, Algebra.compHom_algebraMap_apply, starRingEnd_apply,
      MulOpposite.algebraMap_apply, unop_mul, unop_op, unop_op,
      IsUnitaryFactorSet.star_val (α := α), ← Algebra.commutes, ← Algebra.smul_def]
  rw [smul_mul_smul_comm, of_mul_of, ← mul_inv_rev, smul_smul, smul_smul,
    ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hunit]

private theorem starRingHomOp_of (g : G) :
    starRingHomOp (of g : twistedMonoidAlgebra k G α) =
      op ((((α g g⁻¹)⁻¹ : kˣ) : k) • (of g⁻¹ : twistedMonoidAlgebra k G α)) := by
  simp [starRingHomOp]

private theorem starRingHomOp_algebraMap (r : k) :
    starRingHomOp (algebraMap k (twistedMonoidAlgebra k G α) r) =
      op (algebraMap k (twistedMonoidAlgebra k G α) (star r)) := by
  simp [starRingHomOp, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem starRingHomOp_involutive (x : twistedMonoidAlgebra k G α) :
    unop (starRingHomOp (unop (starRingHomOp x))) = x := by
  let f : twistedMonoidAlgebra k G α →ₐ[k] twistedMonoidAlgebra k G α :=
    { toFun x := unop (starRingHomOp (unop (starRingHomOp x)))
      map_one' := by simp
      map_mul' _ _ := by simp [map_mul]
      map_zero' := by simp
      map_add' _ _ := by simp [map_add]
      commutes' _ := by simp [starRingHomOp_algebraMap] }
  have hf : f = AlgHom.id k (twistedMonoidAlgebra k G α) := algHom_ext fun g ↦ by
    change unop (starRingHomOp (unop (starRingHomOp (of g)))) = of g
    rw [starRingHomOp_of, unop_op, Algebra.smul_def, map_mul, starRingHomOp_algebraMap,
      starRingHomOp_of, unop_mul, unop_op, unop_op, inv_inv,
      IsUnitaryFactorSet.star_inv_val (α := α), ← Algebra.commutes, ← Algebra.smul_def,
      smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g,
      mul_inv_cancel, Units.val_one, one_smul]
  exact AlgHom.congr_fun hf x

/-- The canonical conjugate-linear `StarRing` structure on a twisted group algebra with a unitary
factor set: `star (of g) = ((α g g⁻¹)⁻¹ : k) • of g⁻¹`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (twistedMonoidAlgebra k G α) where
  star x := unop (starRingHomOp x)
  star_involutive := starRingHomOp_involutive
  star_mul _ _ := by simp [map_mul]
  star_add _ _ := by simp [map_add]

/-- Formula for `star` on a basis element of a unitary twisted group algebra. -/
@[simp]
theorem star_of (g : G) :
    star (of g : twistedMonoidAlgebra k G α) = (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹ :=
  congrArg unop (starRingHomOp_of g)

/-- When `α g g⁻¹ = 1`, `star` simply inverts the group element: `star (of g) = of g⁻¹`. -/
theorem star_of_eq_of_inv {g : G} (h : α g g⁻¹ = 1) :
    star (of g : twistedMonoidAlgebra k G α) = of g⁻¹ := by
  simp [star_of, h]

private theorem star_algebraMap (r : k) :
    star (algebraMap k (twistedMonoidAlgebra k G α) r) = algebraMap k _ (star r) :=
  congrArg unop (starRingHomOp_algebraMap r)

/-- The canonical star structure on a unitary twisted group algebra is conjugate-linear. -/
instance instStarModule : StarModule k (twistedMonoidAlgebra k G α) where
  star_smul r x := by simp [Algebra.smul_def, star_mul, star_algebraMap, Algebra.commutes]

section Map

variable {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β] [IsUnitaryFactorSet β]
  (f : G →* H) (hα : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))

/-- Every functorial algebra map between unitary twisted group algebras preserves `star`. -/
@[simp]
theorem map_star (x : twistedMonoidAlgebra k G α) :
    map f hα (star x) = star (map f hα x) := by
  have key : (map f hα).toLinearMap.comp (starLinearEquiv k).toLinearMap =
      (starLinearEquiv k).toLinearMap.comp (map f hα).toLinearMap :=
    (basis k G α).ext fun g ↦ by simp [map_inv, hα g g⁻¹]
  exact LinearMap.congr_fun key x

/-- Functoriality of unitary twisted group algebras as a `⋆`-algebra homomorphism. -/
noncomputable def starMap : twistedMonoidAlgebra k G α →⋆ₐ[k] twistedMonoidAlgebra k H β :=
  { map f hα with map_star' := map_star f hα }

/-- The underlying `k`-algebra homomorphism of `starMap f hα` is `map f hα`. -/
@[simp]
theorem toAlgHom_starMap : (starMap f hα).toAlgHom = map f hα := (rfl)

/-- `starMap f hα` sends the basis element `of g` to `of (f g)`. -/
@[simp]
theorem starMap_of (g : G) : starMap f hα (of g) = of (f g) := map_of f hα g

/-- An injective group homomorphism pulling back unitary factor sets induces an injective
`⋆`-algebra homomorphism. -/
theorem starMap_injective (hf : Function.Injective f) : Function.Injective (starMap f hα) :=
  map_injective f hα hf

/-- `starMap f hα` agrees pointwise with `map f hα`. -/
theorem starMap_apply (x : twistedMonoidAlgebra k G α) : starMap f hα x = map f hα x := (rfl)

/-- An injective `starMap` preserves the canonical trace. -/
@[simp]
theorem trace_starMap (hf : Function.Injective f) (x : twistedMonoidAlgebra k G α) :
    trace (starMap f hα x) = trace x := trace_map f hα hf x

/-- Multiplying the image of `starMap f hα` by a basis element outside `Set.range f` yields
canonical trace zero. -/
theorem trace_starMap_mul_of_eq_zero (x : twistedMonoidAlgebra k G α) {h : H}
    (hh : h ∉ Set.range f) : trace (starMap f hα x * of h) = 0 :=
  trace_map_mul_of_eq_zero f hα x hh

end Map

/-! ### Canonical trace and Parseval identities -/

/-- The canonical trace on a unitary twisted group algebra commutes with `star`. -/
@[simp]
theorem trace_star (x : twistedMonoidAlgebra k G α) :
    trace (star x) = star (trace x) := by
  have key : (trace (k := k) (G := G) (α := α)).comp (starLinearEquiv k).toLinearMap =
      (starLinearEquiv k).toLinearMap.comp (trace (k := k) (G := G) (α := α)) :=
    (basis k G α).ext fun g ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, starLinearEquiv_apply, basis_apply,
        star_of, map_smul, smul_eq_mul]
      by_cases hg : g = 1
      · subst hg; simp [IsFactorSet.one_left (α := α)]
      · rw [trace_of_ne_one (inv_ne_one.mpr hg), trace_of_ne_one hg, mul_zero, star_zero]
  exact LinearMap.congr_fun key x

/-- Basis elements are unit vectors for the sesquilinear trace form:
`trace (star (of g) * of g) = 1`. -/
theorem trace_star_of_mul_of_self (g : G) :
    trace (star (of g : twistedMonoidAlgebra k G α) * of g) = 1 := by
  rw [star_of, smul_mul_assoc, of_mul_of, smul_smul, ← Units.val_mul,
    IsFactorSet.apply_inv_eq_inv_apply α g, inv_mul_cancel, Units.val_one, one_smul,
    inv_mul_cancel, of_one, trace_one]

/-- Distinct basis elements are orthogonal for the sesquilinear trace form. -/
theorem trace_star_of_mul_of_ne {g h : G} (hgh : g ≠ h) :
    trace (star (of g : twistedMonoidAlgebra k G α) * of h) = 0 := by
  rw [star_of, smul_mul_assoc, of_mul_of, smul_smul, map_smul, smul_eq_mul,
    trace_of_ne_one (fun h1 ↦ hgh (inv_mul_eq_one.mp h1)), mul_zero]

/-- **Sesquilinear Parseval identity** (general, possibly infinite `G`):
`trace (star x * y)` is the finitely supported inner product of the basis coordinates of `x` and
`y`. -/
theorem trace_star_mul_eq_finsupp_sum (x y : twistedMonoidAlgebra k G α) :
    trace (star x * y) =
      ((basis k G α).repr x).sum fun g c ↦ star c * (basis k G α).repr y g := by
  have hrepr (z : twistedMonoidAlgebra k G α) :
      z = ((basis k G α).repr z).sum fun g c ↦ c • (of g : twistedMonoidAlgebra k G α) := by
    simpa only [Finsupp.linearCombination_apply, basis_apply] using
      ((basis k G α).linearCombination_repr z).symm
  conv_lhs => rw [hrepr x, hrepr y]
  simp only [Finsupp.sum, star_sum, star_smul]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [Finset.mul_sum, map_sum]
  simp only [smul_mul_smul_comm, map_smul, smul_eq_mul]
  by_cases hg : g ∈ ((basis k G α).repr y).support
  · rw [Finset.sum_eq_single g _ (fun hnot ↦ absurd hg hnot), trace_star_of_mul_of_self, mul_one]
    exact fun h _ hhg ↦ by rw [trace_star_of_mul_of_ne hhg.symm, mul_zero]
  · rw [Finsupp.notMem_support_iff.mp hg, mul_zero]
    exact Finset.sum_eq_zero fun h hh ↦ by
      rw [trace_star_of_mul_of_ne (fun (hEq : g = h) ↦ hg (hEq ▸ hh)), mul_zero]

/-- **Sesquilinear Parseval identity** for finite `G`. -/
theorem trace_star_mul [Fintype G] (x y : twistedMonoidAlgebra k G α) :
    trace (star x * y) =
      ∑ g : G, star ((basis k G α).repr x g) * (basis k G α).repr y g := by
  rw [trace_star_mul_eq_finsupp_sum, Finsupp.sum_fintype]
  intro; simp

/-- **Quadratic Parseval identity** for finite `G`. -/
theorem trace_star_mul_self [Fintype G] (x : twistedMonoidAlgebra k G α) :
    trace (star x * x) =
      ∑ g : G, star ((basis k G α).repr x g) * (basis k G α).repr x g :=
  trace_star_mul x x

end StarRing

section Complex

variable {G : Type*} [Group G] {α : G → G → ℂˣ} [IsFactorSet α] [IsUnitaryFactorSet α]

/-- Over `ℂ`, `trace (star x * x)` is real and nonnegative for every element `x`. -/
theorem trace_star_mul_self_nonneg (x : twistedMonoidAlgebra ℂ G α) :
    0 ≤ trace (star x * x) := by
  rw [trace_star_mul_eq_finsupp_sum]
  refine Finset.sum_nonneg fun g _ ↦ ?_
  dsimp only
  rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast sq_nonneg ‖(basis ℂ G α).repr x g‖

/-- Over `ℂ`, the canonical trace is faithful: `trace (star x * x) = 0 ↔ x = 0`. -/
@[simp]
theorem trace_star_mul_self_eq_zero_iff (x : twistedMonoidAlgebra ℂ G α) :
    trace (star x * x) = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  rw [trace_star_mul_eq_finsupp_sum] at hx
  have hsum : ∑ g ∈ ((basis ℂ G α).repr x).support, ‖(basis ℂ G α).repr x g‖ ^ 2 = 0 := by
    have : (((∑ g ∈ ((basis ℂ G α).repr x).support,
        ‖(basis ℂ G α).repr x g‖ ^ 2 : ℝ) : ℂ)) = 0 := by
      simpa only [Finsupp.sum, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow,
        Complex.ofReal_sum] using hx
    exact Complex.ofReal_eq_zero.mp this
  apply (basis ℂ G α).repr.injective
  ext g
  rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hg : g ∈ ((basis ℂ G α).repr x).support
  · exact norm_eq_zero.mp (sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp hsum g hg))
  · exact Finsupp.notMem_support_iff.mp hg

/-- Over `ℂ`, the canonical trace on a unitary twisted group algebra is a
`StarPositiveFunctional`. -/
noncomputable def tracePositiveFunctional :
    StarPositiveFunctional (twistedMonoidAlgebra ℂ G α) where
  toLinearMap := trace
  square_nonneg := trace_star_mul_self_nonneg

/-- The underlying linear map of `tracePositiveFunctional` is `trace`. -/
@[simp]
theorem toLinearMap_tracePositiveFunctional :
    (tracePositiveFunctional (G := G) (α := α)).toLinearMap = trace := (rfl)

/-- Evaluation of `tracePositiveFunctional` agrees with `trace`. -/
@[simp]
theorem tracePositiveFunctional_apply (x : twistedMonoidAlgebra ℂ G α) :
    tracePositiveFunctional x = trace x := (rfl)

/-- The canonical trace on a complex unitary twisted group algebra has trivial GNS null space. -/
@[simp]
theorem nullSubmodule_tracePositiveFunctional :
    (tracePositiveFunctional (G := G) (α := α)).nullSubmodule = ⊥ := by
  ext x; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]

end Complex

end TwistedMonoidAlgebra

end TauCeti
