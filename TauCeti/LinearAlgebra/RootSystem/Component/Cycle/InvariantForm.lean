/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Cycle.Enumeration
public import TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Diag
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm

/-!
# Invariant bilinear forms on component cycles

This file relates `σ`-invariant bilinear forms on a root pairing to their restrictions on the
component pairing of a component cycle via `RootPairing.componentCycleDiag`:

* `RootPairing.rootForm_apply_eq_zero_of_mem_componentCycleSpace`: distinct component-cycle
  spaces are orthogonal under `P.RootForm`, over any commutative ring.
* `RootPairing.Equiv.bilinForm_componentCycleSum`, `RootPairing.Equiv.form_componentCycleSum`,
  and `RootPairing.Equiv.rootForm_componentCycleSum`: the cycle sum scales any `σ`-invariant
  bilinear form orthogonal across distinct component spaces (in particular any `InvariantForm`
  or `RootForm` over any commutative ring) by the cycle length.
* `RootPairing.InvariantForm.form_componentCycleDiag` and
  `RootPairing.InvariantForm.cartanRatio_componentCycleDiag`: a `σ`-invariant form scales by the
  cycle length under diagonal transport, preserving Cartan ratios when the cycle length is nonzero.
* `RootPairing.rootForm_componentCycleDiag`,
  `RootPairing.rootForm_cartanRatio_componentCycleDiag`, and
  `RootPairing.rootForm_eq_sum_componentCycleFixedProj`: the canonical `RootForm` scales by the
  cycle length on each cycle and decomposes orthogonally across component cycles.
-/

public section

open Finset Function
open _root_.Equiv.Perm (SameCycle)

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Distinct component-cycle spaces are orthogonal under `P.RootForm`. -/
theorem rootForm_apply_eq_zero_of_mem_componentCycleSpace (P : RootPairing ι R M N) [Fintype ι]
    (σ : P.Aut) {C₁ C₂ : P.Component} (h : ¬SameCycle σ.componentEquiv C₁ C₂) {x y : M}
    (hx : x ∈ P.componentCycleSpace σ C₁) (hy : y ∈ P.componentCycleSpace σ C₂) :
    P.RootForm x y = 0 := by
  have hle :
      Submodule.map₂ P.RootForm (P.componentCycleSpace σ C₁) (P.componentCycleSpace σ C₂) ≤ ⊥ := by
    simp only [componentCycleSpace_eq_biSup_componentCycle, Submodule.map₂_iSup_left,
      Submodule.map₂_iSup_right, mem_componentCycle]
    refine iSup₂_le fun D₁ h₁ ↦ iSup₂_le fun D₂ h₂ ↦ Submodule.map₂_le.mpr fun a ha b hb ↦ ?_
    rw [Submodule.mem_bot]
    refine P.rootForm_apply_eq_zero_of_mem_componentSpace ?_ ha hb
    rintro rfl
    exact h (h₂.trans h₁.symm)
  exact (Submodule.mem_bot R).mp (hle (Submodule.apply_mem_map₂ _ hx hy))

namespace Equiv

/-- **The cycle sum scales any `σ`-invariant bilinear form that vanishes between distinct
component spaces by the length of the cycle.** -/
theorem bilinForm_componentCycleSum {P : RootPairing ι R M N} {σ : P.Aut} {C : P.Component}
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B (σ.weightMap x) (σ.weightMap y) = B x y)
    (horth : ∀ {D E : P.Component}, D ≠ E → ∀ {x y : M},
      x ∈ P.componentSpace D → y ∈ P.componentSpace E → B x y = 0)
    {x y : M} (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    B (σ.componentCycleSum C x) (σ.componentCycleSum C y) =
      minimalPeriod σ.componentEquiv C * B x y := by
  have hpow (r : ℕ) :
      B ((σ ^ r).toHom.weightMap x) ((σ ^ r).toHom.weightMap y) = B x y := by
    rw [σ.weightMap_pow]
    induction r with
    | zero => simp
    | succ r ih => simp only [pow_succ', mul_apply_eq_comp, hB, ih]
  simp_rw [componentCycleSum_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun r hr ↦ by
    rw [sum_eq_single_of_mem r hr (fun s hs hsr ↦ horth
      (fun h ↦ hsr (componentEquiv_pow_injOn σ C (mem_range.mp hs) (mem_range.mp hr) h))
      (weightMap_mem_componentSpace _ hx) (weightMap_mem_componentSpace _ hy)), hpow r],
    sum_const, card_range, nsmul_eq_mul]

/-- **The cycle sum scales invariant forms by the length of the cycle.** For an invariant form `B`
preserved by `σ`, the cycle sums of two vectors of the component space of `C` pair under `B` to
`c` times their pairing, where `c` is the length of the cycle of `C`. -/
theorem form_componentCycleSum [IsDomain R] [NeZero (2 : R)] {P : RootPairing ι R M N}
    {σ : P.Aut} {C : P.Component} (B : P.InvariantForm)
    (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y) {x y : M}
    (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    B.form (σ.componentCycleSum C x) (σ.componentCycleSum C y) =
      minimalPeriod σ.componentEquiv C * B.form x y :=
  bilinForm_componentCycleSum B.form hB
    (fun h _ _ ha hb ↦ B.apply_eq_zero_of_mem_componentSpace h ha hb) hx hy

/-- The cycle sums of two vectors of the component space of `C` pair under the canonical root form
to `c` times their pairing, where `c` is the length of the cycle of `C`. -/
theorem rootForm_componentCycleSum {P : RootPairing ι R M N} [Fintype ι] {σ : P.Aut}
    {C : P.Component} {x y : M} (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    P.RootForm (σ.componentCycleSum C x) (σ.componentCycleSum C y) =
      minimalPeriod σ.componentEquiv C * P.RootForm x y :=
  bilinForm_componentCycleSum P.RootForm (fun a b ↦ σ.toHom.rootForm_weightMap a b)
    (fun h _ _ ha hb ↦ P.rootForm_apply_eq_zero_of_mem_componentSpace h ha hb) hx hy

end Equiv

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

section Finite

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Scaling of a `σ`-invariant `B : P.InvariantForm` along `componentCycleDiag`** (`2 ≠ 0`). -/
theorem InvariantForm.form_componentCycleDiag [NeZero (2 : K)] (B : P.InvariantForm) {σ : P.Aut}
    (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y) (C : P.Component)
    (u v : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (B.restrictComponent C).form u.val v.val := by
  rw [B.restrictComponent_form_apply, P.coe_componentCycleDiag_apply,
    P.coe_componentCycleDiag_apply]
  simp_rw [← σ.weightMap_pow, ← Equiv.componentCycleSum_apply]
  exact Equiv.form_componentCycleSum B hB u.val.property v.val.property

/-- **Cartan ratios for a `σ`-invariant `B : P.InvariantForm` are preserved** when the cycle length
is nonzero in `K`. -/
theorem InvariantForm.cartanRatio_componentCycleDiag (B : P.InvariantForm)
    {σ : P.Aut} (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y)
    (C : P.Component) (hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0)
    (u v : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    2 * B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        B.form ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (B.restrictComponent C).form u.val v.val / (B.restrictComponent C).form v.val v.val := by
  by_cases h2 : (2 : K) = 0
  · simp [h2]
  · have : NeZero (2 : K) := ⟨h2⟩
    rw [B.form_componentCycleDiag P hB C, B.form_componentCycleDiag P hB C, mul_left_comm (2 : K),
      mul_div_mul_left _ _ hc]

end Finite

section RootForm

variable (P : RootPairing ι K M N) [Fintype ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Scaling of `P.RootForm` along `componentCycleDiag`** (without needing `2 ≠ 0`). -/
theorem rootForm_componentCycleDiag [Fintype C.supp]
    (u v : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (P.componentPairing C).RootForm u.val v.val := by
  rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
  simp_rw [← σ.weightMap_pow, ← Equiv.componentCycleSum_apply]
  rw [Equiv.rootForm_componentCycleSum u.val.property v.val.property,
    P.rootForm_componentPairing C, LinearMap.BilinForm.restrict_apply,
    LinearMap.domRestrict_apply]

/-- **Cartan ratios for `P.RootForm` are preserved by `componentCycleDiag`** when the cycle
length is nonzero in `K`. -/
theorem rootForm_cartanRatio_componentCycleDiag [Fintype C.supp]
    (hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0)
    (u v : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    2 * P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        P.RootForm ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (P.componentPairing C).RootForm u.val v.val /
        (P.componentPairing C).RootForm v.val v.val := by
  rw [P.rootForm_componentCycleDiag σ C, P.rootForm_componentCycleDiag σ C, mul_left_comm (2 : K),
    mul_div_mul_left _ _ hc]

/-- **Orthogonal decomposition of `P.RootForm` on `σ`-fixed weights across component cycles.** -/
theorem rootForm_eq_sum_componentCycleFixedProj
    [Fintype (Quotient (SameCycle.setoid σ.componentEquiv))]
    [∀ O : Quotient (SameCycle.setoid σ.componentEquiv), Fintype O.out.supp]
    (x y : LinearMap.fixedSubmodule σ.weightMap) :
    P.RootForm (x : M) (y : M) =
      ∑ O : Quotient (SameCycle.setoid σ.componentEquiv),
        (minimalPeriod σ.componentEquiv O.out : K) *
          (P.componentPairing O.out).RootForm
            (P.componentCycleFixedProj σ O.out x).val
            (P.componentCycleFixedProj σ O.out y).val := by
  conv_lhs =>
    rw [← (P.componentCycleFixedPiEquiv σ).symm_apply_apply x,
      ← (P.componentCycleFixedPiEquiv σ).symm_apply_apply y]
  rw [P.coe_componentCycleFixedPiEquiv_symm_apply, P.coe_componentCycleFixedPiEquiv_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, componentCycleFixedPiEquiv_apply]
  refine Finset.sum_congr rfl fun O _ ↦ ?_
  rw [Finset.sum_eq_single O (fun O' _ hO' ↦ P.rootForm_apply_eq_zero_of_mem_componentCycleSpace σ
    (_root_.Equiv.Perm.not_sameCycle_out_of_ne σ.componentEquiv hO')
    (P.mem_componentCycleFixedSubmodule.mp (P.componentCycleDiag σ O'.out _).property)
    (P.mem_componentCycleFixedSubmodule.mp (P.componentCycleDiag σ O.out _).property)) (by simp)]
  exact P.rootForm_componentCycleDiag σ O.out _ _

end RootForm

end Field

end RootPairing
