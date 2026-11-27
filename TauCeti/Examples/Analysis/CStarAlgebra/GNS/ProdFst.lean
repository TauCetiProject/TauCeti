/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic

/-!
# Checks for the GNS representation of a coordinate trace on `ℂ ⊕ ℂ`

For the tracial state `τ = pr₁` on `A = ℂ × ℂ`:

* the class of `x` vanishes exactly when `x.1 = 0`, and every vector of the GNS space is a multiple
  of the cyclic vector `Ω = [1]`, so `L²(A, τ) = ℂ·Ω`;
* the GNS representation is `π(a) = a.1 • 1`, so `π = pr₁` and its kernel is `0 ⊕ ℂ`;
* `Ω` is separating for `π(A) = ℂ·1`: `π(a)Ω = 0` forces `π(a) = 0`; but `Ω` does not separate
  the algebra `ℂ ⊕ ℂ` itself, since the nonzero `(0, 1)` acts by `0`.
-/

public section

open PositiveLinearMap
open scoped ComplexOrder

namespace TauCeti.GNSProdFstExample

/-- The first coordinate `pr₁` on `ℂ × ℂ`, as a positive linear functional. -/
noncomputable def pr₁ : ℂ × ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (LinearMap.fst ℂ ℂ ℂ) fun _ hx ↦ (Prod.le_def.mp hx).1

@[simp]
theorem pr₁_apply (x : ℂ × ℂ) : pr₁ x = x.1 :=
  (rfl)

/-- The class of `x` in the GNS space of `pr₁` vanishes exactly when `x.1 = 0`. -/
theorem toGNS_eq_zero_iff_fst_eq_zero (x : ℂ × ℂ) : pr₁.toGNS x = 0 ↔ x.1 = 0 := by
  rw [toGNS_eq_zero_iff]
  simp

/-- The class of `x` is `x.1` times the cyclic vector `Ω = [1]`. -/
theorem toGNS_eq_smul_gnsVector (x : ℂ × ℂ) : pr₁.toGNS x = x.1 • pr₁.gnsVector := by
  rw [gnsVector_eq_toGNS_one, ← map_smul, ← sub_eq_zero, ← map_sub,
    toGNS_eq_zero_iff_fst_eq_zero]
  simp

/-- The cyclic vector is nonzero. -/
theorem gnsVector_ne_zero : pr₁.gnsVector ≠ 0 :=
  norm_ne_zero_iff.mp <| by simp [norm_gnsVector]

/-- **`L²(ℂ ⊕ ℂ, pr₁) = ℂ·Ω`.** Every vector of the GNS space is a multiple of `Ω`. -/
theorem exists_eq_smul_gnsVector (v : pr₁.GNS) : ∃ c : ℂ, v = c • pr₁.gnsVector := by
  have hv : v ∈ (ℂ ∙ pr₁.gnsVector : Submodule ℂ pr₁.GNS) :=
    pr₁.denseRange_toGNS.induction_on (p := (· ∈ (ℂ ∙ pr₁.gnsVector : Submodule ℂ pr₁.GNS))) v
      (Submodule.isClosed_of_finiteDimensional _) fun x ↦ by
        rw [toGNS_eq_smul_gnsVector]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  exact ⟨c, hc.symm⟩

/-- **The GNS representation is `pr₁`.** `π(a) = a.1 • 1`. -/
theorem gnsNonUnitalStarAlgHom_eq (a : ℂ × ℂ) : pr₁.gnsNonUnitalStarAlgHom a = a.1 • 1 := by
  refine DFunLike.coe_injective <| pr₁.denseRange_toGNS.equalizer (map_continuous _)
    (map_continuous _) <| funext fun x ↦ ?_
  simp [↓gnsNonUnitalStarAlgHom_apply_toGNS, ↓toGNS_eq_smul_gnsVector, smul_smul]

/-- **The kernel of the GNS representation is `0 ⊕ ℂ`.** -/
theorem gnsNonUnitalStarAlgHom_eq_zero_iff (a : ℂ × ℂ) :
    pr₁.gnsNonUnitalStarAlgHom a = 0 ↔ a.1 = 0 := by
  rw [gnsNonUnitalStarAlgHom_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zero_smul]⟩
  have := congrArg (fun T : pr₁.GNS →L[ℂ] pr₁.GNS ↦ T pr₁.gnsVector) h
  simpa [gnsVector_ne_zero] using this

/-- **`Ω` is separating for `π(ℂ ⊕ ℂ)`.** If `π(a)Ω = 0`, then `π(a) = 0`. -/
theorem gnsNonUnitalStarAlgHom_eq_zero_of_apply_gnsVector_eq_zero {a : ℂ × ℂ}
    (h : pr₁.gnsNonUnitalStarAlgHom a pr₁.gnsVector = 0) : pr₁.gnsNonUnitalStarAlgHom a = 0 := by
  rw [gnsNonUnitalStarAlgHom_eq_zero_iff]
  rw [gnsNonUnitalStarAlgHom_eq] at h
  simpa [gnsVector_ne_zero] using h

/-- **`Ω` does not separate `ℂ ⊕ ℂ` itself.** The nonzero element `(0, 1)` acts by `0`. -/
theorem gnsNonUnitalStarAlgHom_zero_one : pr₁.gnsNonUnitalStarAlgHom ((0, 1) : ℂ × ℂ) = 0 :=
  (gnsNonUnitalStarAlgHom_eq_zero_iff _).mpr rfl

end TauCeti.GNSProdFstExample
