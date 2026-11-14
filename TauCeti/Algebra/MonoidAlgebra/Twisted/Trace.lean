/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.MapDomain
public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Complex.Order
-- Private: weighted norm-square `Finsupp` identities are used only inside the Parseval proofs.
import TauCeti.Basic.Complex.BigOperators

/-!
# The scalar trace and conjugate-linear reversal on a twisted group algebra

Every twisted monoid algebra `twistedMonoidAlgebra k G α` carries the linear functional
`TauCeti.TwistedMonoidAlgebra.scalarTrace` reading off the coordinate of `1 : G` in
`TauCeti.TwistedMonoidAlgebra.basis`. When `G` is a group, `scalarTrace` is tracial (`α g g⁻¹ =
α g⁻¹ g` by `TauCeti.IsFactorSet.apply_inv_eq_inv_apply`) and its multiplication pairing is
nondegenerate over every commutative semiring, since `α g⁻¹ g` is a unit.

When `G` is a group and `k` is a commutative star semiring, conjugating coordinates and inverting
group elements defines the conjugate-linear involution
`TauCeti.TwistedMonoidAlgebra.conjReverse`. Whenever `star (α g h : k) = (α h⁻¹ g⁻¹ : k)`,
`conjReverse` reverses products; over `ℂ`, when `α g⁻¹ g = 1` for every `g` (as for alternating
bicharacters), `scalarTrace ℂ G α (conjReverse ℂ G α x * x)` is the Parseval sum of squared
moduli `∑_g ‖x_g‖²`, hence nonnegative and vanishing only at `0`.

## Main definitions

* `TauCeti.TwistedMonoidAlgebra.scalarTrace`: the coordinate of `1 : G` in
  `TwistedMonoidAlgebra.basis`, as a `k`-linear functional.
* `TauCeti.TwistedMonoidAlgebra.conjReverse`: the conjugate-linear involution sending
  `∑ z_g • of g` to `∑ star z_g • of g⁻¹`.

## Main results

* `TauCeti.TwistedMonoidAlgebra.scalarTrace_mul_comm` and
  `TauCeti.TwistedMonoidAlgebra.eq_zero_of_forall_scalarTrace_mul_eq_zero`: traciality and
  nondegeneracy of the multiplication pairing of `scalarTrace` for a group `G`.
* `TauCeti.TwistedMonoidAlgebra.conjReverse_mul`: antimultiplicativity of `conjReverse` when
  `star (α g h : k) = (α h⁻¹ g⁻¹ : k)`.
* `TauCeti.TwistedMonoidAlgebra.scalarTrace_conjReverse_mul`,
  `TauCeti.TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_eq_sum_normSq`,
  `TauCeti.TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_nonneg`, and
  `TauCeti.TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_eq_zero_iff`: sesquilinear
  formula, Parseval identity, positivity, and faithfulness over `ℂ`.
* `TauCeti.TwistedMonoidAlgebra.scalarTrace_mapDomain_of_eq_one` and
  `TauCeti.TwistedMonoidAlgebra.scalarTrace_mapDomain_of_injective`: preservation of `scalarTrace`
  along `mapDomain` under trivial kernel (monoids) or injectivity (groups).

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

section Monoid

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

/-- **The scalar trace** on `k_α[G]`: the `k`-linear functional returning the coefficient of `1`
in `TwistedMonoidAlgebra.basis`. -/
noncomputable def scalarTrace : twistedMonoidAlgebra k G α →ₗ[k] k :=
  (basis k G α).coord 1

variable {k G α}

/-- `scalarTrace` evaluates the basis representation at `1`. -/
theorem scalarTrace_apply (x : twistedMonoidAlgebra k G α) :
    scalarTrace k G α x = (basis k G α).repr x 1 :=
  (rfl)

/-- `scalarTrace` is normalized to `1` on the algebra identity. -/
@[simp]
theorem scalarTrace_one : scalarTrace k G α 1 = 1 := by
  rw [← of_one, scalarTrace_apply, basis_repr_of, Finsupp.single_eq_same]

/-- On a basis element `of g`, `scalarTrace` detects `g = 1`. -/
theorem scalarTrace_of (g : G) [Decidable (g = 1)] :
    scalarTrace k G α (of g) = if g = 1 then 1 else 0 := by
  rw [scalarTrace_apply, basis_repr_of, Finsupp.single_apply]

/-- `scalarTrace` vanishes on non-identity basis elements. -/
theorem scalarTrace_of_ne_one {g : G} (hg : g ≠ 1) :
    scalarTrace k G α (of g) = 0 := by
  classical
  simp [scalarTrace_of, hg]

/-- Pushing forward along a monoid homomorphism with trivial kernel preserves `scalarTrace`. -/
theorem scalarTrace_mapDomain_of_eq_one {H : Type*} [Monoid H] {β : H → H → kˣ}
    [IsFactorSet β] {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hf₁ : ∀ g, f g = 1 → g = 1) (x : twistedMonoidAlgebra k G α) :
    scalarTrace k H β (mapDomain f hf x) = scalarTrace k G α x := by
  have hlin : scalarTrace k H β ∘ₗ (mapDomain (k := k) f hf).toLinearMap = scalarTrace k G α :=
    (basis k G α).ext fun g ↦ by
      classical
      have hfg : f g = 1 ↔ g = 1 := ⟨hf₁ g, fun h ↦ h ▸ map_one f⟩
      simp [basis_apply, scalarTrace_of, hfg]
  exact LinearMap.congr_fun hlin x

end Monoid

section Group

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- Pushing forward along an injective group-to-monoid homomorphism preserves `scalarTrace`. -/
@[simp]
theorem scalarTrace_mapDomain_of_injective {H : Type*} [Monoid H] {β : H → H → kˣ}
    [IsFactorSet β] {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hfinj : Function.Injective f) (x : twistedMonoidAlgebra k G α) :
    scalarTrace k H β (mapDomain f hf x) = scalarTrace k G α x :=
  scalarTrace_mapDomain_of_eq_one hf (fun _ hg ↦ hfinj (hg.trans (map_one f).symm)) x

/-- Right-multiplying `x` by `of g` picks out the `g⁻¹`-coordinate of `x`, weighted by `α g⁻¹ g`. -/
@[simp]
theorem scalarTrace_mul_of (x : twistedMonoidAlgebra k G α) (g : G) :
    scalarTrace k G α (x * of g) = (basis k G α).repr x g⁻¹ * (α g⁻¹ g : k) := by
  classical
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem x₀ hx₀ =>
    obtain ⟨h, rfl⟩ := hx₀
    rw [basis_apply, of_mul_of, map_smul, smul_eq_mul, scalarTrace_of, basis_repr_of,
      Finsupp.single_apply, mul_eq_one_iff_eq_inv]
    split_ifs with hh
    · subst hh; simp
    · simp
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
  | smul c x₁ _ hx₁ => simp [mul_assoc, hx₁]

/-- Left-multiplying `x` by `of g` picks out the `g⁻¹`-coordinate of `x`, weighted by `α g g⁻¹`. -/
@[simp]
theorem scalarTrace_of_mul (g : G) (x : twistedMonoidAlgebra k G α) :
    scalarTrace k G α (of g * x) = (α g g⁻¹ : k) * (basis k G α).repr x g⁻¹ := by
  classical
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem x₀ hx₀ =>
    obtain ⟨h, rfl⟩ := hx₀
    rw [basis_apply, of_mul_of, map_smul, smul_eq_mul, scalarTrace_of, basis_repr_of,
      Finsupp.single_apply, mul_eq_one_iff_inv_eq, eq_comm (a := g⁻¹) (b := h)]
    split_ifs with hh
    · subst hh; simp
    · simp
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ => simp [mul_add, hx₁, hx₂]
  | smul c x₁ _ hx₁ => simp [mul_left_comm, hx₁]

/-- **Traciality of `scalarTrace`** on a twisted group algebra: `s(x * y) = s(y * x)`, because
`α g⁻¹ g = α g g⁻¹` for every `g : G`. -/
theorem scalarTrace_mul_comm (x y : twistedMonoidAlgebra k G α) :
    scalarTrace k G α (x * y) = scalarTrace k G α (y * x) := by
  induction (basis k G α).mem_span y using Submodule.span_induction with
  | mem y₀ hy₀ =>
    obtain ⟨g, rfl⟩ := hy₀
    rw [basis_apply, scalarTrace_mul_of, scalarTrace_of_mul,
      IsFactorSet.apply_inv_eq_inv_apply α g, mul_comm]
  | zero => simp
  | add y₁ y₂ _ _ hy₁ hy₂ => simp [mul_add, add_mul, hy₁, hy₂]
  | smul c y₁ _ hy₁ => simp [hy₁]

/-- **Nondegeneracy of the multiplication pairing of `scalarTrace`.** Over every commutative
semiring, an element annihilated under `scalarTrace` by every right factor is `0`. -/
theorem eq_zero_of_forall_scalarTrace_mul_eq_zero {x : twistedMonoidAlgebra k G α}
    (hx : ∀ y, scalarTrace k G α (x * y) = 0) : x = 0 := by
  apply (basis k G α).repr.injective
  ext g
  have hg := hx (of g⁻¹)
  rw [scalarTrace_mul_of, inv_inv] at hg
  simpa [← mul_assoc, mul_assoc _ (α g g⁻¹ : k), ← Units.val_mul] using
    congrArg (· * (((α g g⁻¹)⁻¹ : kˣ) : k)) hg

end Group

section ConjReverse

variable (k G : Type*) [CommSemiring k] [StarRing k] [Group G] (α : G → G → kˣ) [IsFactorSet α]

/-- **Conjugate-linear reversal** on `k_α[G]`: the conjugate-linear involution sending
`∑ z_g • of g` to `∑ star z_g • of g⁻¹`. -/
noncomputable def conjReverse :
    twistedMonoidAlgebra k G α →ₗ⋆[k] twistedMonoidAlgebra k G α where
  toFun x := ((basis k G α).repr x).sum fun g r ↦ star r • of g⁻¹
  map_add' x y := by
    rw [map_add, Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [add_smul])]
  map_smul' c x := by
    rw [map_smul, Finsupp.sum_smul_index' (fun _ ↦ by simp), starRingEnd_apply, Finsupp.smul_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp [smul_smul]

variable {k G α}

/-- `conjReverse` inverts basis elements. -/
@[simp]
theorem conjReverse_of (g : G) :
    conjReverse k G α (of g) = of g⁻¹ := by
  simp [conjReverse]

/-- `conjReverse` fixes `1`. -/
@[simp]
theorem conjReverse_one :
    conjReverse k G α 1 = 1 := by
  rw [← of_one, conjReverse_of, inv_one, of_one]

/-- The `g`-coordinate of `conjReverse x` is the conjugate of the `g⁻¹`-coordinate of `x`. -/
@[simp]
theorem basis_repr_conjReverse (x : twistedMonoidAlgebra k G α) (g : G) :
    (basis k G α).repr (conjReverse k G α x) g = star ((basis k G α).repr x g⁻¹) := by
  classical
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    rw [basis_apply, conjReverse_of, basis_repr_of, basis_repr_of, Finsupp.single_apply,
      Finsupp.single_apply, inv_eq_iff_eq_inv]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx, starRingEnd_apply]

/-- `conjReverse` is an involution. -/
@[simp]
theorem conjReverse_conjReverse (x : twistedMonoidAlgebra k G α) :
    conjReverse k G α (conjReverse k G α x) = x := by
  apply (basis k G α).repr.injective
  ext g
  simp

/-- `scalarTrace` intertwines `conjReverse` with `star`. -/
@[simp]
theorem scalarTrace_conjReverse (x : twistedMonoidAlgebra k G α) :
    scalarTrace k G α (conjReverse k G α x) = star (scalarTrace k G α x) := by
  simp [scalarTrace_apply]

/-- `conjReverse` commutes with `mapDomain` along any factor-set-preserving group homomorphism. -/
theorem conjReverse_mapDomain {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) :
    conjReverse k H β (mapDomain f hf x) = mapDomain f hf (conjReverse k G α x) := by
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    simp [basis_apply]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- When `star (α g h : k) = (α h⁻¹ g⁻¹ : k)`, `conjReverse` reverses multiplication. -/
theorem conjReverse_mul (hα : ∀ g h : G, star (α g h : k) = (α h⁻¹ g⁻¹ : k))
    (x y : twistedMonoidAlgebra k G α) :
    conjReverse k G α (x * y) = conjReverse k G α y * conjReverse k G α x := by
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem x₀ hx₀ =>
    obtain ⟨g, rfl⟩ := hx₀
    rw [basis_apply]
    induction (basis k G α).mem_span y using Submodule.span_induction with
    | mem y₀ hy₀ =>
      obtain ⟨h, rfl⟩ := hy₀
      simp only [basis_apply, of_mul_of, map_smulₛₗ, starRingEnd_apply, hα g h, conjReverse_of,
        mul_inv_rev]
    | zero => simp
    | add y₁ y₂ _ _ hy₁ hy₂ => simp [mul_add, add_mul, hy₁, hy₂]
    | smul c y₁ _ hy₁ => simp [hy₁]
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ => simp [add_mul, mul_add, hx₁, hx₂]
  | smul c x₁ _ hx₁ => simp [hx₁]

/-- `conjReverse` is the unique additive conjugate-linear map inverting every basis element. -/
theorem conjReverse_unique {f : twistedMonoidAlgebra k G α → twistedMonoidAlgebra k G α}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (r : k) x, f (r • x) = star r • f x)
    (hof : ∀ g : G, f (of g) = of g⁻¹) :
    f = conjReverse k G α := by
  funext x
  have hzero : f 0 = 0 := by simpa using hsmul 0 0
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    rw [basis_apply, hof, conjReverse_of]
  | zero => rw [hzero, map_zero]
  | add x y _ _ hx hy => rw [hadd, map_add, hx, hy]
  | smul c x _ hx => rw [hsmul, map_smulₛₗ, starRingEnd_apply, hx]

/-- Sesquilinear coordinate expansion of `scalarTrace k G α (conjReverse k G α x * y)`. -/
theorem scalarTrace_conjReverse_mul (x y : twistedMonoidAlgebra k G α) :
    scalarTrace k G α (conjReverse k G α x * y) =
      ((basis k G α).repr x).sum fun g z ↦ star z * ((α g⁻¹ g : k) * (basis k G α).repr y g) := by
  -- Unfold `conjReverse` on `x` to distribute right multiplication by `y` across `Finsupp.sum`.
  change scalarTrace k G α ((((basis k G α).repr x).sum fun g r ↦ star r • of g⁻¹) * y) = _
  rw [Finsupp.sum, Finset.sum_mul, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [smul_mul_assoc, map_smul, scalarTrace_of_mul, inv_inv, smul_eq_mul]

end ConjReverse

section Complex

open scoped ComplexConjugate ComplexOrder

variable {G : Type*} [Group G] {α : G → G → ℂˣ} [IsFactorSet α]

/-- **Parseval identity** on a complex twisted group algebra whose factor set satisfies
`α g⁻¹ g = 1` for every `g`: `s(x† * x) = ∑_g ‖x_g‖²`. -/
theorem scalarTrace_conjReverse_mul_self_eq_sum_normSq (hdiag : ∀ g : G, α g⁻¹ g = 1)
    (x : twistedMonoidAlgebra ℂ G α) :
    scalarTrace ℂ G α (conjReverse ℂ G α x * x) =
      (((basis ℂ G α).repr x).sum fun _ z ↦ Complex.normSq z : ℝ) := by
  have hsum := Finsupp.ofReal_sum_normSq_mul ((basis ℂ G α).repr x) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, Complex.ofReal_one, one_mul] at hsum
  rw [scalarTrace_conjReverse_mul, hsum]
  refine Finsupp.sum_congr fun g _ ↦ ?_
  simp [hdiag g]

/-- **Positivity of `scalarTrace ℂ G α (conjReverse ℂ G α x * x)`** when `α g⁻¹ g = 1`. -/
theorem scalarTrace_conjReverse_mul_self_nonneg (hdiag : ∀ g : G, α g⁻¹ g = 1)
    (x : twistedMonoidAlgebra ℂ G α) :
    0 ≤ scalarTrace ℂ G α (conjReverse ℂ G α x * x) := by
  rw [scalarTrace_conjReverse_mul_self_eq_sum_normSq hdiag, Complex.zero_le_real]
  simpa using Finsupp.sum_normSq_mul_nonneg ((basis ℂ G α).repr x) (w := fun _ ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one)

/-- **Faithfulness of `scalarTrace ℂ G α (conjReverse ℂ G α x * x)`** when `α g⁻¹ g = 1`:
`s(x† * x) = 0 ↔ x = 0`. -/
theorem scalarTrace_conjReverse_mul_self_eq_zero_iff (hdiag : ∀ g : G, α g⁻¹ g = 1)
    (x : twistedMonoidAlgebra ℂ G α) :
    scalarTrace ℂ G α (conjReverse ℂ G α x * x) = 0 ↔ x = 0 := by
  have h := Finsupp.sum_normSq_mul_eq_zero_iff ((basis ℂ G α).repr x) (w := fun _ ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one)
  simp only [mul_one] at h
  rw [scalarTrace_conjReverse_mul_self_eq_sum_normSq hdiag, Complex.ofReal_eq_zero, h]
  refine ⟨fun hx ↦ (basis ℂ G α).repr.injective (by ext g; simpa using hx g one_ne_zero),
    fun hx g _ ↦ by simp [hx]⟩

end Complex

end TauCeti.TwistedMonoidAlgebra
