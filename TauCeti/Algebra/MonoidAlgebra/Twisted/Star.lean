/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.Complex.Order
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Basic.Complex.BigOperators

/-!
# Star structure and Parseval positivity on twisted group algebras

When `G` is a group and `α : G → G → kˣ` is a unitary normalized factor set over a commutative
star semiring `k` — meaning `star (α g h : k) = ((α g h)⁻¹ : kˣ)` for all `g, h : G` — the
twisted group algebra `k_α[G]` carries a canonical conjugate-linear star structure making every
basis element `of g` unitary (`star (of g) = (of g)⁻¹ = (α g g⁻¹)⁻¹ • of g⁻¹`).

The construction uses `TwistedMonoidAlgebra.lift` into the opposite algebra twisted by
`starRingEnd k`, following the same pattern as `TauCeti.TemperleyLieb.instStarRing`. Under this
adjoint:

* `TauCeti.TwistedMonoidAlgebra.map_star`: every compatible monoid homomorphism induces a
  `⋆`-algebra homomorphism (`TauCeti.TwistedMonoidAlgebra.mapStarAlgHom`).
* `TauCeti.TwistedMonoidAlgebra.scalarTrace_star`: the canonical scalar trace `scalarTrace α`
  preserves `star`.
* `TauCeti.TwistedMonoidAlgebra.scalarTrace_star_mul`: the basis `of g` is orthonormal for the
  sesquilinear form `(x, y) ↦ scalarTrace α (star x * y)`.
* Over `ℂ`, `scalarTrace α (star x * x)` is the Parseval sum of squared moduli of the basis
  coordinates (`TauCeti.TwistedMonoidAlgebra.scalarTrace_star_mul_self`), hence nonnegative and
  faithful, yielding `TauCeti.TwistedMonoidAlgebra.scalarTracePositiveFunctional` with trivial
  GNS null space (`TauCeti.TwistedMonoidAlgebra.nullSubmodule_scalarTracePositiveFunctional`).

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

open scoped ComplexOrder
open MulOpposite Module

namespace TauCeti.TwistedMonoidAlgebra

section Unit

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- The unit of `twistedMonoidAlgebra k G α` attached to the basis element `of g`. -/
private noncomputable def unitOf (g : G) : (twistedMonoidAlgebra k G α)ˣ where
  val := of g
  inv := (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹
  val_inv := by simp [smul_smul, ← Units.val_mul]
  inv_val := by simp [smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g]

private theorem unitOf_val (g : G) :
    ((unitOf (k := k) (α := α) g : (twistedMonoidAlgebra k G α)ˣ) :
      twistedMonoidAlgebra k G α) = of g := (rfl)

private theorem unitOf_inv_val (g : G) :
    (((unitOf (k := k) (α := α) g)⁻¹ : (twistedMonoidAlgebra k G α)ˣ) :
      twistedMonoidAlgebra k G α) = (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹ := (rfl)

end Unit

section Construction

variable {k G : Type*} [CommSemiring k] [StarRing k] [Group G]
  {α : G → G → kˣ} [IsFactorSet α]
  [hα : Fact (∀ g h : G, star (α g h : k) = ((α g h)⁻¹ : kˣ))]

/-- The conjugate-linear reversal map on `twistedMonoidAlgebra k G α`, bundled as a ring
homomorphism into the opposite algebra. -/
private noncomputable def conjugateReverse :
    twistedMonoidAlgebra k G α →+* (twistedMonoidAlgebra k G α)ᵐᵒᵖ := by
  letI : Algebra k (twistedMonoidAlgebra k G α)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd k)
  refine (lift (k := k) (G := G) (α := α)
    (fun g ↦ op (((unitOf (k := k) (α := α) g)⁻¹ : (twistedMonoidAlgebra k G α)ˣ) :
      twistedMonoidAlgebra k G α))
    (by
      simp only [unitOf_inv_val, inv_one, IsFactorSet.one_left, of_one, Units.val_one, one_smul]
      rfl)
    fun g h ↦ unop_injective ?_).toRingHom
  have hmul : unitOf (k := k) (α := α) g * unitOf h =
      Units.map (algebraMap k (twistedMonoidAlgebra k G α)).toMonoidHom (α g h) *
        unitOf (g * h) := by
    apply Units.ext
    simp [unitOf_val, Algebra.smul_def]
  have hinv : ((unitOf (k := k) (α := α) h)⁻¹).val * (unitOf g)⁻¹.val =
      (unitOf (g * h))⁻¹.val *
        algebraMap k (twistedMonoidAlgebra k G α) ((α g h)⁻¹ : kˣ) := by
    simpa [mul_inv_rev, ← map_inv] using
      congrArg (fun u : (twistedMonoidAlgebra k G α)ˣ ↦ u⁻¹.val) hmul
  simpa only [unop_mul, unop_op, Algebra.smul_def, Algebra.compHom_algebraMap_apply,
    starRingEnd_apply, MulOpposite.algebraMap_apply, hα.out g h, Algebra.commutes] using hinv

private theorem conjugateReverse_of (g : G) :
    conjugateReverse (k := k) (G := G) (α := α) (of g) =
      op ((((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹) := by
  simp [conjugateReverse, unitOf_inv_val]

private theorem conjugateReverse_algebraMap (r : k) :
    conjugateReverse (k := k) (G := G) (α := α) (algebraMap k _ r) =
      op (algebraMap k _ (star r)) := by
  simp [conjugateReverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem conjugateReverse_smul (r : k) (x : twistedMonoidAlgebra k G α) :
    conjugateReverse (r • x) = op (star r • unop (conjugateReverse x)) := by
  rw [Algebra.smul_def, map_mul, conjugateReverse_algebraMap]
  apply unop_injective
  simp [Algebra.smul_def, Algebra.commutes]

private theorem conjugateReverse_involutive (x : twistedMonoidAlgebra k G α) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  let f : twistedMonoidAlgebra k G α →ₗ[k] twistedMonoidAlgebra k G α :=
    { toFun := fun y ↦ unop (conjugateReverse (unop (conjugateReverse y)))
      map_add' := fun y z ↦ by simp [map_add]
      map_smul' := fun r y ↦ by simp [conjugateReverse_smul] }
  have hf : f = LinearMap.id := by
    refine (basis k G α).ext fun g ↦ ?_
    have hstar : star (((α g g⁻¹)⁻¹ : kˣ) : k) = (α g g⁻¹ : k) := by
      simpa using congrArg star (hα.out g g⁻¹).symm
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply, basis_apply,
      conjugateReverse_of, unop_op, conjugateReverse_smul, smul_smul, inv_inv,
      ← IsFactorSet.apply_inv_eq_inv_apply α g, hstar, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul]
  exact LinearMap.congr_fun hf x

/-- For a unitary normalized factor set on a group `G`, the canonical conjugate-linear star
structure on `twistedMonoidAlgebra k G α` sending `of g` to its inverse `(α g g⁻¹)⁻¹ • of g⁻¹`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (twistedMonoidAlgebra k G α) where
  star x := unop (conjugateReverse x)
  star_involutive := conjugateReverse_involutive
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- The canonical star structure on `twistedMonoidAlgebra k G α` is conjugate-linear. -/
noncomputable instance instStarModule : StarModule k (twistedMonoidAlgebra k G α) where
  star_smul r x := (congrArg unop (conjugateReverse_smul r x)).trans (unop_op _)

/-- The adjoint of a basis element `of g` is its inverse `(α g g⁻¹)⁻¹ • of g⁻¹`. -/
@[simp]
theorem star_of (g : G) :
    star (of g : twistedMonoidAlgebra k G α) = (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹ :=
  congrArg unop (conjugateReverse_of g)

/-- When `α g g⁻¹ = 1`, the adjoint of `of g` is simply `of g⁻¹`. -/
theorem star_of_of_apply_inv_eq_one {g : G} (h : α g g⁻¹ = 1) :
    star (of g : twistedMonoidAlgebra k G α) = of g⁻¹ := by
  simp [h]

/-- Every basis element `of g` is unitary: `star (of g) * of g = 1`. -/
theorem star_of_mul_of (g : G) :
    star (of g : twistedMonoidAlgebra k G α) * of g = 1 := by
  simp [smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g]

/-- Every basis element `of g` is unitary: `of g * star (of g) = 1`. -/
theorem of_mul_star_of (g : G) :
    (of g : twistedMonoidAlgebra k G α) * star (of g) = 1 := by
  simp [smul_smul, ← Units.val_mul]

/-- A compatible monoid homomorphism preserves the canonical star structure. -/
theorem map_star {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) :
    map f hf (star x) = star (map f hf x) := by
  let lhs : twistedMonoidAlgebra k G α →ₛₗ[starRingEnd k] twistedMonoidAlgebra k H β :=
    { toFun := fun y ↦ map f hf (star y)
      map_add' := fun y z ↦ by simp
      map_smul' := fun r y ↦ by simp [starRingEnd_apply] }
  let rhs : twistedMonoidAlgebra k G α →ₛₗ[starRingEnd k] twistedMonoidAlgebra k H β :=
    { toFun := fun y ↦ star (map f hf y)
      map_add' := fun y z ↦ by simp
      map_smul' := fun r y ↦ by simp [starRingEnd_apply] }
  have heq : lhs = rhs := by
    refine (basis k G α).ext fun g ↦ ?_
    simp only [lhs, rhs, LinearMap.coe_mk, AddHom.coe_mk, basis_apply, star_of, map_smul, map_of,
      ← map_inv, hf]
  exact LinearMap.congr_fun heq x

/-- A compatible monoid homomorphism induces a `⋆`-algebra homomorphism between twisted group
algebras with unitary factor sets. -/
noncomputable def mapStarAlgHom {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂) :
    twistedMonoidAlgebra k G α →⋆ₐ[k] twistedMonoidAlgebra k H β :=
  { map f hf with
    map_star' := map_star f hf }

/-- Coercing `mapStarAlgHom` to an algebra homomorphism recovers `map`. -/
@[simp]
theorem toAlgHom_mapStarAlgHom {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂) :
    (mapStarAlgHom f hf).toAlgHom = map f hf := (rfl)

/-- `mapStarAlgHom` acts on basis elements by applying `f`. -/
@[simp]
theorem mapStarAlgHom_of {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂) (g : G) :
    mapStarAlgHom f hf (of g) = of (f g) :=
  map_of f hf g

/-- `mapStarAlgHom` is injective whenever the underlying group homomorphism is injective. -/
theorem mapStarAlgHom_injective {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
    {f : G →* H} (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂)
    (hinj : Function.Injective f) :
    Function.Injective (mapStarAlgHom f hf) :=
  map_injective hf hinj

/-- An injective compatible group homomorphism induces a `mapStarAlgHom` preserving
`scalarTrace`. -/
theorem scalarTrace_mapStarAlgHom {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
    {f : G →* H} (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂)
    (hinj : Function.Injective f) (x : twistedMonoidAlgebra k G α) :
    scalarTrace β (mapStarAlgHom f hf x) = scalarTrace α x :=
  scalarTrace_map α hf hinj x

/-- The scalar trace preserves the canonical star structure. -/
@[simp]
theorem scalarTrace_star (x : twistedMonoidAlgebra k G α) :
    scalarTrace α (star x) = star (scalarTrace α x) := by
  let lhs : twistedMonoidAlgebra k G α →ₛₗ[starRingEnd k] k :=
    { toFun := fun y ↦ scalarTrace α (star y)
      map_add' := fun y z ↦ by simp
      map_smul' := fun r y ↦ by simp [starRingEnd_apply] }
  let rhs : twistedMonoidAlgebra k G α →ₛₗ[starRingEnd k] k :=
    { toFun := fun y ↦ star (scalarTrace α y)
      map_add' := fun y z ↦ by simp
      map_smul' := fun r y ↦ by simp [starRingEnd_apply] }
  have heq : lhs = rhs := by
    refine (basis k G α).ext fun g ↦ ?_
    classical
    simp only [lhs, rhs, LinearMap.coe_mk, AddHom.coe_mk, basis_apply, star_of, map_smul,
      scalarTrace_of, smul_eq_mul, inv_eq_one]
    split_ifs with hg
    · subst hg
      simp [IsFactorSet.one_left]
    · simp
  exact LinearMap.congr_fun heq x

/-- The twisted basis is orthonormal for `(x, y) ↦ scalarTrace α (star x * y)`. -/
theorem scalarTrace_star_of_mul_of [DecidableEq G] (g h : G) :
    scalarTrace α (star (of g) * of h) = if g = h then 1 else 0 := by
  rw [star_of, smul_mul_assoc, map_smul, scalarTrace_of_mul_of, smul_eq_mul]
  simp only [inv_mul_eq_one]
  split_ifs with hgh
  · subst hgh
    rw [IsFactorSet.apply_inv_eq_inv_apply α g, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · simp

/-- Sesquilinear Parseval identity for `scalarTrace`:
`scalarTrace α (star x * y) = ∑ g, star (x_g) * y_g`. -/
theorem scalarTrace_star_mul (x y : twistedMonoidAlgebra k G α) :
    scalarTrace α (star x * y) =
      ((basis k G α).repr x).sum fun g c ↦ star c * (basis k G α).repr y g := by
  classical
  have hterm (g : G) :
      scalarTrace α (star (of g) * y) = (basis k G α).repr y g := by
    have hlin : (scalarTrace α).comp (LinearMap.mulLeft k (star (of g))) =
        (basis k G α).coord g := by
      refine (basis k G α).ext fun h ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Basis.coord_apply, Basis.repr_self]
      rw [basis_apply, scalarTrace_star_of_mul_of]
      simp [Finsupp.single_apply, eq_comm]
    exact LinearMap.congr_fun hlin y
  conv_lhs => rw [← (basis k G α).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, star_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [basis_apply, star_smul, smul_mul_assoc, map_smul, hterm, smul_eq_mul]

end Construction

section ComplexPositivity

variable {G : Type*} [Group G] (α : G → G → ℂˣ) [IsFactorSet α]
  [Fact (∀ g h : G, star (α g h : ℂ) = ((α g h)⁻¹ : ℂˣ))]

/-- **Parseval identity for `scalarTrace` on a complex twisted group algebra with unitary factor
set**: `scalarTrace α (star x * x) = ∑ g, ‖x_g‖²`. -/
theorem scalarTrace_star_mul_self (x : twistedMonoidAlgebra ℂ G α) :
    scalarTrace α (star x * x) =
      ((((basis ℂ G α).repr x).sum fun _ z ↦ Complex.normSq z : ℝ) : ℂ) := by
  rw [scalarTrace_star_mul]
  simpa using (Finsupp.ofReal_sum_normSq_mul ((basis ℂ G α).repr x) (fun _ ↦ (1 : ℝ))).symm

/-- **Positivity of `scalarTrace` on a complex twisted group algebra with unitary factor set.** -/
theorem scalarTrace_star_mul_self_nonneg (x : twistedMonoidAlgebra ℂ G α) :
    0 ≤ scalarTrace α (star x * x) := by
  rw [scalarTrace_star_mul_self]
  exact Complex.zero_le_real.mpr <| by
    simpa using Finsupp.sum_normSq_mul_nonneg ((basis ℂ G α).repr x) (w := fun _ ↦ (1 : ℝ))
      (fun _ ↦ zero_le_one)

/-- **Faithfulness of `scalarTrace`**: `scalarTrace α (star x * x) = 0 ↔ x = 0`. -/
@[simp]
theorem scalarTrace_star_mul_self_eq_zero_iff {x : twistedMonoidAlgebra ℂ G α} :
    scalarTrace α (star x * x) = 0 ↔ x = 0 := by
  rw [scalarTrace_star_mul_self, Complex.ofReal_eq_zero]
  have h := Finsupp.sum_normSq_mul_eq_zero_iff ((basis ℂ G α).repr x) (w := fun _ ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one)
  simp only [mul_one, ne_eq, one_ne_zero, not_false_eq_true, forall_const] at h
  rw [h]
  refine ⟨fun hx ↦ (basis ℂ G α).repr.map_eq_zero_iff.mp (Finsupp.ext fun s ↦ by
    simpa using hx s), fun hx s ↦ by
    rw [hx, LinearEquiv.map_zero, Finsupp.zero_apply]⟩

/-- The canonical scalar trace on a complex twisted group algebra with unitary factor set,
bundled as a `StarPositiveFunctional`. -/
noncomputable def scalarTracePositiveFunctional :
    StarPositiveFunctional (twistedMonoidAlgebra ℂ G α) where
  toLinearMap := scalarTrace α
  square_nonneg := scalarTrace_star_mul_self_nonneg α

/-- The underlying linear map of `scalarTracePositiveFunctional` is `scalarTrace`. -/
@[simp]
theorem toLinearMap_scalarTracePositiveFunctional :
    (scalarTracePositiveFunctional α).toLinearMap = scalarTrace α := (rfl)

/-- Evaluation of `scalarTracePositiveFunctional`. -/
@[simp]
theorem scalarTracePositiveFunctional_apply (x : twistedMonoidAlgebra ℂ G α) :
    scalarTracePositiveFunctional α x = scalarTrace α x := (rfl)

/-- The GNS null space of `scalarTracePositiveFunctional` is trivial. -/
@[simp]
theorem nullSubmodule_scalarTracePositiveFunctional :
    (scalarTracePositiveFunctional α).nullSubmodule = ⊥ := by
  ext x
  simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]

end ComplexPositivity

end TauCeti.TwistedMonoidAlgebra
