/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.MapDomain

/-!
# The scalar trace on a twisted monoid algebra

Every twisted monoid algebra `twistedMonoidAlgebra k G α` carries the linear functional
`TauCeti.TwistedMonoidAlgebra.scalarTrace` reading off the `1 : G` coordinate in `basis`. When `G`
is a group, `scalarTrace` is tracial with nondegenerate multiplication pairing.

## Main definitions

* `TauCeti.TwistedMonoidAlgebra.scalarTrace`.

## Main results

* `TauCeti.TwistedMonoidAlgebra.scalarTrace_mapDomain_of_eq_one`,
  `TauCeti.TwistedMonoidAlgebra.scalarTrace_mapDomain_of_injective`,
  `TauCeti.TwistedMonoidAlgebra.scalarTrace_mul_comm`,
  `TauCeti.TwistedMonoidAlgebra.eq_zero_of_forall_scalarTrace_mul_eq_zero`.

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

theorem scalarTrace_apply (x : twistedMonoidAlgebra k G α) :
    scalarTrace k G α x = (basis k G α).repr x 1 := (rfl)

@[simp] theorem scalarTrace_one : scalarTrace k G α 1 = 1 := by
  rw [← of_one, scalarTrace_apply, repr_of, Finsupp.single_eq_same]

/-- On a basis element `of g`, `scalarTrace` detects `g = 1`. -/
theorem scalarTrace_of (g : G) [Decidable (g = 1)] :
    scalarTrace k G α (of g) = if g = 1 then 1 else 0 := by
  rw [scalarTrace_apply, repr_of, Finsupp.single_apply]

theorem scalarTrace_of_ne_one {g : G} (hg : g ≠ 1) : scalarTrace k G α (of g) = 0 := by
  classical simp [scalarTrace_of, hg]

/-- Pushing forward along a monoid homomorphism with trivial kernel preserves `scalarTrace`. -/
theorem scalarTrace_mapDomain_of_eq_one {H : Type*} [Monoid H] {β : H → H → kˣ}
    [IsFactorSet β] {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hf₁ : ∀ g, f g = 1 → g = 1) (x : twistedMonoidAlgebra k G α) :
    scalarTrace k H β (mapDomain f hf x) = scalarTrace k G α x :=
  LinearMap.congr_fun
    ((basis k G α).ext (f₁ := scalarTrace k H β ∘ₗ (mapDomain (k := k) f hf).toLinearMap)
      (f₂ := scalarTrace k G α) fun g ↦ by
      classical
      have hfg : f g = 1 ↔ g = 1 := ⟨hf₁ g, fun h ↦ h ▸ map_one f⟩
      simp [basis_apply, scalarTrace_of, hfg]) x

/-- Pushing forward along an injective monoid homomorphism preserves `scalarTrace`. -/
@[simp] theorem scalarTrace_mapDomain_of_injective {H : Type*} [Monoid H] {β : H → H → kˣ}
    [IsFactorSet β] {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hfinj : Function.Injective f) (x : twistedMonoidAlgebra k G α) :
    scalarTrace k H β (mapDomain f hf x) = scalarTrace k G α x :=
  scalarTrace_mapDomain_of_eq_one hf (fun _ hg ↦ hfinj (hg.trans (map_one f).symm)) x

end Monoid

section Group

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- Right-multiplying `x` by `of g` picks out the `g⁻¹`-coordinate weighted by `α g⁻¹ g`. -/
@[simp] theorem scalarTrace_mul_of (x : twistedMonoidAlgebra k G α) (g : G) :
    scalarTrace k G α (x * of g) = (basis k G α).repr x g⁻¹ * (α g⁻¹ g : k) := by
  classical
  induction (basis k G α).mem_span x using Submodule.span_induction with
  | mem _ hx₀ =>
    obtain ⟨h, rfl⟩ := hx₀
    rw [basis_apply, of_mul_of, map_smul, smul_eq_mul, scalarTrace_of, repr_of,
      Finsupp.single_apply, mul_eq_one_iff_eq_inv]
    split_ifs with hh <;> simp [hh]
  | zero => simp
  | add _ _ _ _ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
  | smul _ _ _ hx₁ => simp [mul_assoc, hx₁]

/-- Left-multiplying `x` by `of g` picks out the `g⁻¹`-coordinate weighted by `α g g⁻¹`. -/
@[simp] theorem scalarTrace_of_mul (g : G) (x : twistedMonoidAlgebra k G α) :
    scalarTrace k G α (of g * x) = (α g g⁻¹ : k) * (basis k G α).repr x g⁻¹ := by
  rw [scalarTrace_apply, repr_mul_apply_one_comm, ← scalarTrace_apply, scalarTrace_mul_of,
    IsFactorSet.apply_inv_eq_inv_apply α g, mul_comm]

/-- `scalarTrace` is tracial when `G` is a group. -/
theorem scalarTrace_mul_comm (x y : twistedMonoidAlgebra k G α) :
    scalarTrace k G α (x * y) = scalarTrace k G α (y * x) := by
  rw [scalarTrace_apply, scalarTrace_apply, repr_mul_apply_one_comm]

/-- **Nondegeneracy of `scalarTrace`**: an element annihilated by every right factor is `0`. -/
theorem eq_zero_of_forall_scalarTrace_mul_eq_zero {x : twistedMonoidAlgebra k G α}
    (hx : ∀ y, scalarTrace k G α (x * y) = 0) : x = 0 := by
  refine (basis k G α).repr.injective (Finsupp.ext fun g ↦ ?_)
  have hg := hx (of g⁻¹)
  rw [scalarTrace_mul_of, inv_inv] at hg
  simpa [← mul_assoc, mul_assoc _ (α g g⁻¹ : k), ← Units.val_mul] using
    congrArg (· * (((α g g⁻¹)⁻¹ : kˣ) : k)) hg

end Group

end TauCeti.TwistedMonoidAlgebra
