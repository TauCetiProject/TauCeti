/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Basic
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm

/-!
# Invariant bilinear forms on component cycles

This file relates `σ`-invariant bilinear forms on a root pairing to their restrictions on the
component pairing of a component cycle via `RootPairing.componentCycleDiag`:

* `RootPairing.rootForm_apply_eq_zero_of_mem_componentCycleSpace`: distinct component-cycle
  spaces are orthogonal under `P.RootForm`, over any commutative ring.
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
  (P : RootPairing ι R M N) [Fintype ι] (σ : P.Aut)

/-- Distinct component-cycle spaces are orthogonal under `P.RootForm`. -/
theorem rootForm_apply_eq_zero_of_mem_componentCycleSpace {C₁ C₂ : P.Component}
    (h : ¬SameCycle σ.componentEquiv C₁ C₂) {x y : M}
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

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

section Finite

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

private theorem bilinear_componentCycleDiag (B : M →ₗ[K] M →ₗ[K] K)
    (hB : ∀ x y, B (σ.weightMap x) (σ.weightMap y) = B x y)
    (horth : ∀ {D E : P.Component}, D ≠ E → ∀ {x y : M},
      x ∈ P.componentSpace D → y ∈ P.componentSpace E → B x y = 0)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    B ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * B (u : M) (v : M) := by
  have hpow (r : ℕ) (x y : M) : B ((σ.weightMap ^ r) x) ((σ.weightMap ^ r) y) = B x y := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, LinearMap.comp_apply, hB, ih]
  have hmem (r : ℕ) {w : M} (hw : w ∈ P.componentSpace C) :
      (σ.weightMap ^ r) w ∈ P.componentSpace ((σ.componentEquiv ^ r) C) := by
    rw [← σ.weightMap_pow, ← σ.componentEquiv_pow]
    exact (σ ^ r).weightMap_mem_componentSpace hw
  rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun s hs ↦ by
    rw [Finset.sum_eq_single s (fun r hr hrs ↦ horth (P.pow_componentEquiv_ne_of_ne_lt σ C
      (Finset.mem_range.mp hr) (Finset.mem_range.mp hs) hrs)
      (hmem r u.val.property) (hmem s v.val.property)) (fun h ↦ absurd hs h), hpow s],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Scaling of a `σ`-invariant `B : P.InvariantForm` along `componentCycleDiag`** (`2 ≠ 0`). -/
theorem InvariantForm.form_componentCycleDiag [NeZero (2 : K)] (B : P.InvariantForm) {σ : P.Aut}
    (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y) (C : P.Component)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (B.restrictComponent C).form u.val v.val := by
  rw [B.restrictComponent_form_apply]
  exact P.bilinear_componentCycleDiag σ C B.form hB
    (fun h _ _ hx hy ↦ B.apply_eq_zero_of_mem_componentSpace h hx hy) u v

/-- **Cartan ratios for a `σ`-invariant `B : P.InvariantForm` are preserved** when the cycle length
is nonzero in `K`. -/
theorem InvariantForm.cartanRatio_componentCycleDiag [NeZero (2 : K)] (B : P.InvariantForm)
    {σ : P.Aut} (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y)
    (C : P.Component) (hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    2 * B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        B.form ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (B.restrictComponent C).form u.val v.val / (B.restrictComponent C).form v.val v.val := by
  rw [B.form_componentCycleDiag P hB C, B.form_componentCycleDiag P hB C, mul_left_comm (2 : K),
    mul_div_mul_left _ _ hc]

end Finite

section RootForm

variable (P : RootPairing ι K M N) [Fintype ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Scaling of `P.RootForm` along `componentCycleDiag`** (without needing `2 ≠ 0`). -/
theorem rootForm_componentCycleDiag [Fintype C.supp]
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (P.componentPairing C).RootForm u.val v.val := by
  rw [P.bilinear_componentCycleDiag σ C P.RootForm (fun x y ↦ σ.toHom.rootForm_weightMap x y)
    (fun h _ _ hx hy ↦ P.rootForm_apply_eq_zero_of_mem_componentSpace h hx hy) u v,
    P.rootForm_componentPairing C]
  rfl

/-- **Cartan ratios for `P.RootForm` are preserved by `componentCycleDiag`** when the cycle
length is nonzero in `K`. -/
theorem rootForm_cartanRatio_componentCycleDiag [Fintype C.supp]
    (hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
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
  have hsum_single :
      (∑ d : Quotient (SameCycle.setoid σ.componentEquiv),
        P.RootForm ((P.componentCycleDiag σ d.out (P.componentCycleFixedProj σ d.out x) :
          LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ O.out (P.componentCycleFixedProj σ O.out y) :
            LinearMap.fixedSubmodule σ.weightMap) : M)) =
        P.RootForm ((P.componentCycleDiag σ O.out (P.componentCycleFixedProj σ O.out x) :
          LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ O.out (P.componentCycleFixedProj σ O.out y) :
            LinearMap.fixedSubmodule σ.weightMap) : M) :=
    Finset.sum_eq_single O (fun O' _ hO' ↦ P.rootForm_apply_eq_zero_of_mem_componentCycleSpace σ
      (C₁ := O'.out) (C₂ := O.out)
      (fun hsc ↦ hO' ((O'.out_eq.symm.trans (Quotient.sound hsc)).trans O.out_eq))
      (P.mem_componentCycleFixedSubmodule.mp (P.componentCycleDiag σ O'.out _).property)
      (P.mem_componentCycleFixedSubmodule.mp (P.componentCycleDiag σ O.out _).property))
      (by simp)
  rw [hsum_single]
  exact P.rootForm_componentCycleDiag σ O.out _ _

end RootForm

end Field

end RootPairing
