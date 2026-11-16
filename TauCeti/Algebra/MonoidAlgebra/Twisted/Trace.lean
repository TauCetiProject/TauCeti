/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# The canonical trace on a twisted monoid algebra

The canonical trace `TauCeti.TwistedMonoidAlgebra.trace` on `k_α[G]` extracts the identity
coordinate in `basis k G α`. It satisfies `trace 1 = 1`, is tracial when `G` is a group
(`trace_mul_comm`), is preserved by injective functorial maps (`trace_map`), and vanishes on
`map f hα x * of h` whenever `h ∉ Set.range f` (`trace_map_mul_of_eq_zero`).

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

section Monoid

variable {k G : Type*} [CommSemiring k] [Monoid G] {α : G → G → kˣ} [IsFactorSet α]

/-- The **canonical trace** on `twistedMonoidAlgebra k G α`, extracting the coefficient of the
identity basis element `of 1 = 1`. -/
noncomputable def trace : twistedMonoidAlgebra k G α →ₗ[k] k :=
  (basis k G α).coord 1

/-- Evaluation of `trace` as the coordinate at `1` in `basis k G α`. -/
theorem trace_apply (x : twistedMonoidAlgebra k G α) :
    trace x = (basis k G α).repr x 1 := (rfl)

/-- The canonical trace is normalized at `1`. -/
@[simp]
theorem trace_one : trace (1 : twistedMonoidAlgebra k G α) = 1 := by
  rw [trace_apply, ← of_one (α := α), ← basis_apply k G α 1, Module.Basis.repr_self,
    Finsupp.single_eq_same]

/-- The canonical trace vanishes on every non-identity basis element. -/
theorem trace_of_ne_one {g : G} (hg : g ≠ 1) :
    trace (of g : twistedMonoidAlgebra k G α) = 0 := by
  rw [trace_apply, ← basis_apply k G α g, Module.Basis.repr_self,
    Finsupp.single_eq_of_ne hg.symm]

/-- Injective functorial maps between twisted monoid algebras preserve the canonical trace. -/
@[simp]
theorem trace_map {H : Type*} [Monoid H] {β : H → H → kˣ} [IsFactorSet β]
    (f : G →* H) (hα : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    (hf : Function.Injective f) (x : twistedMonoidAlgebra k G α) :
    trace (map f hα x) = trace x := by
  rw [trace_apply, trace_apply, ← map_one f, basis_repr_map_apply f hα hf x 1]

end Monoid

section Group

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- The canonical trace on a twisted group algebra is tracial: `trace (x * y) = trace (y * x)`. -/
theorem trace_mul_comm (x y : twistedMonoidAlgebra k G α) :
    trace (x * y) = trace (y * x) := by
  have key : (LinearMap.mul k (twistedMonoidAlgebra k G α)).compr₂ trace =
      ((LinearMap.mul k (twistedMonoidAlgebra k G α)).compr₂ trace).flip := by
    refine (basis k G α).ext fun g ↦ (basis k G α).ext fun h ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.flip_apply, basis_apply,
      of_mul_of, map_smul, smul_eq_mul]
    by_cases hgh : g * h = 1
    · obtain rfl : h = g⁻¹ := eq_inv_of_mul_eq_one_right hgh
      simp [IsFactorSet.apply_inv_eq_inv_apply α g]
    · have hhg : h * g ≠ 1 := fun h1 ↦ hgh (by rw [eq_inv_of_mul_eq_one_right h1, inv_mul_cancel])
      rw [trace_of_ne_one hgh, trace_of_ne_one hhg, mul_zero, mul_zero]
  exact LinearMap.congr_fun₂ key x y

/-- Multiplying an element in the image of a group homomorphism `f : G →* H` by a basis element
`of h` with `h ∉ Set.range f` yields zero canonical trace. -/
theorem trace_map_mul_of_eq_zero {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    (f : G →* H) (hα : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    (x : twistedMonoidAlgebra k G α) {h : H} (hh : h ∉ Set.range f) :
    trace (map f hα x * of h) = 0 := by
  have key : trace.comp ((LinearMap.mulRight k (of h)).comp (map f hα).toLinearMap) = 0 := by
    refine (basis k G α).ext fun g ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply,
      LinearMap.zero_apply, basis_apply, map_of, of_mul_of, map_smul, smul_eq_mul]
    have hne : f g * h ≠ 1 :=
      fun h1 ↦ hh ⟨g⁻¹, by rw [map_inv, eq_inv_of_mul_eq_one_right h1]⟩
    rw [trace_of_ne_one hne, mul_zero]
  exact LinearMap.congr_fun key x

end Group

end TauCeti.TwistedMonoidAlgebra
