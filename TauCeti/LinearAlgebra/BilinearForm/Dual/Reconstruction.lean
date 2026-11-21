/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.FiniteType

/-!
# Finite dual-family reconstruction for bilinear forms

Over a commutative semiring satisfying the Orzech property (for instance, any commutative ring or
any finite commutative semiring), if a bilinear form `B` on an `R`-module `M` satisfies a finite
left-side reconstruction formula `∑ i ∈ s, B (a i) y • b i = y` for all `y : M`, then `M` is
finitely generated and the Orzech property forces the partner right-side reconstruction formula
`∑ i ∈ s, B x (b i) • a i = x`.

## Main results

* `LinearMap.BilinForm.sum_apply_smul_eq_of_forall`: a finite left-side reconstruction formula
  for a bilinear form over a commutative semiring with the Orzech property implies the partner
  right-side reconstruction formula.
-/

public section

namespace LinearMap.BilinForm

/-- If a bilinear form `B` on an `R`-module `M` over a commutative semiring satisfying the Orzech
property satisfies a finite left-side reconstruction formula `∑ i ∈ s, B (a i) y • b i = y`, then
it satisfies the partner formula `∑ i ∈ s, B x (b i) • a i = x`. -/
theorem sum_apply_smul_eq_of_forall {R M ι : Type*} [CommSemiring R] [OrzechProperty R]
    [AddCommMonoid M] [Module R M]
    (B : LinearMap.BilinForm R M) (s : Finset ι) (a b : ι → M)
    (h : ∀ y : M, ∑ i ∈ s, B (a i) y • b i = y) (x : M) :
    ∑ i ∈ s, B x (b i) • a i = x := by
  have : Module.Finite R M :=
    Module.Finite.of_surjective (Fintype.linearCombination R fun i : s ↦ b i.val)
      fun y ↦ ⟨fun i ↦ B (a i.val) y, by
        rw [Fintype.linearCombination_apply, Finset.univ_eq_attach,
          s.sum_attach fun i ↦ B (a i) y • b i]
        exact h y⟩
  let Ψ : Module.Dual R M →ₗ[R] M :=
    { toFun := fun α ↦ ∑ i ∈ s, α (a i) • b i
      map_add' := fun α β ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r α ↦ by simp [smul_smul, Finset.smul_sum] }
  let Ψ' : Module.Dual R M →ₗ[R] M :=
    { toFun := fun β ↦ ∑ i ∈ s, β (b i) • a i
      map_add' := fun α β ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r α ↦ by simp [smul_smul, Finset.smul_sum] }
  have hΨ : Function.Surjective Ψ := fun y ↦ ⟨B.flip y, h y⟩
  have hBΨ' (β : Module.Dual R M) : B (Ψ' β) = β := by
    ext y
    calc
      B (∑ i ∈ s, β (b i) • a i) y
        = ∑ i ∈ s, β (b i) * B (a i) y := by simp [map_sum]
      _ = β (∑ i ∈ s, B (a i) y • b i) := by simp [map_sum, mul_comm]
      _ = β y := by rw [h y]
  have hB : Function.Surjective B := fun β ↦ ⟨Ψ' β, hBΨ' β⟩
  have hinj : Function.Injective (Ψ ∘ₗ B) :=
    OrzechProperty.injective_of_surjective_endomorphism (Ψ ∘ₗ B) (hΨ.comp hB)
  exact hinj (congrArg Ψ (hBΨ' (B x)))

end LinearMap.BilinForm
