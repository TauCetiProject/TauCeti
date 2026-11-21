/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.LinearAlgebra.Exact

/-!
# The `r`-torsion of a linear map

Let `r` be an element of a commutative semiring `R`. A linear map `f : M → N` carries the
`r`-torsion `M[r] = Submodule.torsionBy R M r` into `N[r]`; its restriction
`TauCeti.torsionByMap r f : M[r] →ₗ[R] N[r]` is the action on morphisms of the functor
`M ↦ M[r]`, dual to Mathlib's `QuotSMulTop.map` for `M ↦ M ⧸ rM`. This functor is left exact.

Along an exact sequence `M₁ → M₂ → M₃` the map `M₂[r] → M₃[r]` is injective when `M₁ → M₂` is
injective and multiplication by `r` is injective on `M₁`, and it is surjective when `M₂ → M₃` is
surjective and multiplication by `r` is surjective on `M₁`. Hence a surjection with uniquely
`r`-divisible kernel induces a bijection on `r`-torsion, so every `r`-torsion point lifts uniquely.

The connecting map `M₃[r] → M₁ ⧸ rM₁` of a short exact sequence, and the six-term exact sequence
it completes, are in `TauCeti.Algebra.Module.Torsion.Snake`.

## Main definitions

* `TauCeti.torsionByMap`: the restriction `M[r] →ₗ[R] N[r]` of a linear map.
* `TauCeti.torsionByLinearMap`: `TauCeti.torsionByMap` promoted to an `R ⧸ (r)`-linear map.

## Main results

* `TauCeti.injective_torsionByMap`, `TauCeti.exact_torsionByMap`: `M[r]` is left exact.
* `TauCeti.injective_torsionByMap_of_injective_smul`: along an exact sequence `0 → M₁ → M₂ → M₃`,
  the map `M₂[r] → M₃[r]` is injective when multiplication by `r` is injective on `M₁`.
* `TauCeti.surjective_torsionByMap_of_surjective_smul`: along an exact sequence
  `M₁ → M₂ → M₃ → 0`, the map `M₂[r] → M₃[r]` is surjective when multiplication by `r` is
  surjective on `M₁`.
* `TauCeti.bijective_torsionByMap_of_bijective_ker_smul`,
  `TauCeti.existsUnique_torsion_lift_of_bijective_ker_smul`: a surjection with uniquely
  `r`-divisible kernel induces a bijection on `r`-torsion and lifts `r`-torsion uniquely.
-/

public section

open Function Submodule

namespace TauCeti

section Map

variable {R : Type*} [CommSemiring R] (r : R) {M N P : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- A linear map carries `r`-torsion to `r`-torsion; this is its restriction `M[r] →ₗ[R] N[r]`,
the action on morphisms of the functor `M ↦ M[r]` dual to `QuotSMulTop.map`. -/
def torsionByMap (f : M →ₗ[R] N) : torsionBy R M r →ₗ[R] torsionBy R N r :=
  f.restrict fun x hx ↦ by
    rw [mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero]

@[simp]
theorem coe_torsionByMap_apply (f : M →ₗ[R] N) (x : torsionBy R M r) :
    (torsionByMap r f x : N) = f x :=
  (rfl)

@[simp]
theorem torsionByMap_id : torsionByMap r (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext
  rfl

theorem torsionByMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    torsionByMap r (g ∘ₗ f) = torsionByMap r g ∘ₗ torsionByMap r f := by
  ext
  rfl

/-- The inclusion of the `r`-torsion intertwines `torsionByMap` with the map itself. -/
theorem subtype_comp_torsionByMap (f : M →ₗ[R] N) :
    (torsionBy R N r).subtype ∘ₗ torsionByMap r f = f ∘ₗ (torsionBy R M r).subtype := by
  ext
  rfl

variable (M) in
/-- The `r`-torsion is the kernel of multiplication by `r`. -/
theorem exact_subtype_torsionBy :
    Exact (torsionBy R M r).subtype (DistribSMul.toLinearMap R M r) := fun x ↦
  ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

variable {r}

/-- The restriction of an injective linear map to the `r`-torsion is injective. -/
theorem injective_torsionByMap {f : M →ₗ[R] N} (hf : Injective f) :
    Injective (torsionByMap r f) := fun _ _ h ↦
  Subtype.ext <| hf <| congrArg Subtype.val h

/-- **Left exactness of `r`-torsion**: if `f` is injective and `f`, `g` are exact, then so are
`M[r] → N[r] → P[r]`. Only the injectivity of `f` is used, not the surjectivity of `g`. -/
theorem exact_torsionByMap {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Exact f g) (hf : Injective f) :
    Exact (torsionByMap r f) (torsionByMap r g) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hfg y).1 (congrArg Subtype.val hy)
    have hrx : r • x = 0 := hf <| by
      rw [map_smul, hx, map_zero]
      exact (mem_torsionBy_iff _ _).1 y.property
    exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hrx⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext <| hfg.apply_apply_eq_zero x

end Map

section Exact

variable {R : Type*} [CommSemiring R] {r : R} {M₁ M₂ M₃ : Type*} [AddCommMonoid M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃] {f : M₁ →ₗ[R] M₂}
  {g : M₂ →ₗ[R] M₃}

/-- Along an exact sequence `0 → M₁ → M₂ → M₃`, if multiplication by `r` is injective on `M₁`,
then `M₂[r] → M₃[r]` is injective, since its kernel is the image of `M₁[r] = 0`. -/
theorem injective_torsionByMap_of_injective_smul (hfg : Exact f g) (hf : Injective f)
    (hr : Injective fun x : M₁ ↦ r • x) : Injective (torsionByMap r g) := fun x₁ x₂ h ↦ by
  -- `x₁ - x₂ = f w` by exactness, and `f (r • w) = r • (x₁ - x₂) = 0`, so `w = 0`; as `M₃` need
  -- not be a group, `g (x₁ - x₂) = 0` is computed as `g x₁ + g (-x₂) = g x₂ + g (-x₂) = g 0`
  obtain ⟨w, hw⟩ := (hfg ((x₁ : M₂) - x₂)).1 <| by
    have h' : g x₁ = g x₂ := by simpa using congrArg Subtype.val h
    simpa [sub_eq_add_neg, h'] using (map_add g (x₂ : M₂) (-x₂)).symm
  have hw0 : w = 0 := hr <| hf <| by
    simp [hw, smul_sub, (mem_torsionBy_iff _ _).1 x₁.property,
      (mem_torsionBy_iff _ _).1 x₂.property]
  exact Subtype.ext <| sub_eq_zero.1 <| by simp [← hw, hw0]

/-- Along an exact sequence `M₁ → M₂ → M₃ → 0`, if multiplication by `r` is surjective on `M₁`,
then `M₂[r] → M₃[r]` is surjective. The map `M₁ → M₂` need not be injective. -/
theorem surjective_torsionByMap_of_surjective_smul (hfg : Exact f g) (hg : Surjective g)
    (hr : Surjective fun x : M₁ ↦ r • x) : Surjective (torsionByMap r g) := fun x ↦ by
  -- a lift `y` of `x` has `g (r • y) = 0`; correct it by the image of `M₁ = r • M₁`
  obtain ⟨y, hy⟩ := hg x
  obtain ⟨y', hy', hgy'⟩ := hfg.exists_apply_eq_zero_and_apply_eq_of_surjective
    (α := DistribSMul.toLinearMap R M₁ r) (β := DistribSMul.toLinearMap R M₂ r)
    (γ := DistribSMul.toLinearMap R M₃ r) hfg.linearMap_comp_eq_zero hr
    (LinearMap.ext fun x ↦ (map_smul f r x).symm) (LinearMap.ext fun x ↦ (map_smul g r x).symm)
    (y := y) (by simp [hy])
  exact ⟨⟨y', (mem_torsionBy_iff _ _).2 (by simpa using hy')⟩, Subtype.ext (by simp [hgy', hy])⟩

end Exact

section QuotientLinear

variable {R : Type*} [CommRing R] (r : R) {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]

/-- `TauCeti.torsionByMap` promoted to an `R ⧸ (r)`-linear map on `r`-torsion submodules. -/
noncomputable def torsionByLinearMap (f : M₁ →ₗ[R] M₂) :
    torsionBy R M₁ r →ₗ[R ⧸ Ideal.span {r}] torsionBy R M₂ r :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective (torsionByMap r f)

@[simp]
theorem coe_torsionByLinearMap (f : M₁ →ₗ[R] M₂) :
    ⇑(torsionByLinearMap r f) = ⇑(torsionByMap r f) := (rfl)

@[simp]
theorem torsionByLinearMap_id :
    torsionByLinearMap r (LinearMap.id : M₁ →ₗ[R] M₁) = LinearMap.id :=
  LinearMap.ext fun _ ↦ rfl

theorem torsionByLinearMap_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) :
    torsionByLinearMap r (g ∘ₗ f) = torsionByLinearMap r g ∘ₗ torsionByLinearMap r f :=
  LinearMap.ext fun _ ↦ rfl

end QuotientLinear

section Lift

variable {R : Type*} [CommSemiring R] (r : R) {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A surjective linear map induces a bijection on `r`-torsion when multiplication
by `r` is bijective on its kernel. -/
theorem bijective_torsionByMap_of_bijective_ker_smul (f : M →ₗ[R] N)
    (hf : Surjective f) (hr : Bijective fun x : LinearMap.ker f ↦ r • x) :
    Bijective (torsionByMap r f) :=
  -- Mathlib's `LinearMap.exact_subtype_ker_map` assumes a ring
  have hex : Exact (LinearMap.ker f).subtype f :=
    LinearMap.exact_iff.2 (LinearMap.ker f).range_subtype.symm
  ⟨injective_torsionByMap_of_injective_smul hex (LinearMap.ker f).injective_subtype hr.1,
    surjective_torsionByMap_of_surjective_smul hex hf hr.2⟩

/-- A surjective linear map whose kernel is uniquely divisible by `r` lifts every
`r`-torsion point uniquely to an `r`-torsion point. -/
theorem existsUnique_torsion_lift_of_bijective_ker_smul (f : M →ₗ[R] N)
    (hf : Surjective f) (hr : Bijective fun x : LinearMap.ker f ↦ r • x)
    (y : N) (hy : r • y = 0) : ∃! x : M, r • x = 0 ∧ f x = y := by
  obtain ⟨x, hx, huniq⟩ :=
    (bijective_torsionByMap_of_bijective_ker_smul r f hf hr).existsUnique
      ⟨y, (mem_torsionBy_iff _ _).mpr hy⟩
  refine ⟨x, ⟨(mem_torsionBy_iff _ _).mp x.property, congrArg Subtype.val hx⟩, fun z hz ↦ ?_⟩
  exact congrArg Subtype.val (huniq ⟨z, (mem_torsionBy_iff _ _).mpr hz.1⟩ (Subtype.ext hz.2))

end Lift

end TauCeti
