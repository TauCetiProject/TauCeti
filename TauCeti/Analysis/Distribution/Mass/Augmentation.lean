/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Mass bounds for augmentation and point-current minimization

The augmentation of a compactly supported functional is bounded by its mass times the norm
of the constant being tested. Since augmentation vanishes on compactly supported boundaries,
this gives a lower bound for the mass of every boundary perturbation. For a weighted point
current the bound is sharp: its mass is the absolute value of its coefficient, and adding a
compactly supported boundary cannot decrease that mass.

These statements use the existing Euclidean test-form model, including its actual exterior
derivative. They apply to real-linear functionals, so in particular to currents, without a
finite-mass assumption on the competitor. Constants are evaluated only through compactly
supported cutoffs. No constant function is treated as a test on a noncompact domain.

In degree zero this distinguishes boundary perturbations from arbitrary competitors with the
same ordinary boundary: zero has smaller mass than a nonzero point current, but has different
augmentation and cannot be obtained by a compactly supported boundary perturbation.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (mass and boundary of currents).
-/

public section

noncomputable section

open Set Filter TopologicalSpace ContinuousLinearMap
open scoped Distributions Topology ENNReal

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens E} {n : ℕ∞}

/-- The mass bounds augmentation against a constant vector, evaluated using a cutoff near the
compact support. Both sides are meaningful even when the mass is infinite. -/
theorem enorm_augmentation_le_mass_mul {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V]
    [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V] (T : 𝓕) (hT : IsCompact (dsupport T))
    (hTΩ : dsupport T ⊆ Ω) (c : F) :
    ‖augmentation T c‖ₑ ≤ mass T * ‖c‖ₑ := by
  obtain ⟨χ, hχ, hχ01⟩ := TestFunction.exists_eventually_eq_one (n := n) hT hTΩ
  rw [augmentation_eq T hχ]
  refine (enorm_apply_le_mass_mul T _).trans (mul_le_mul_right ?_ _)
  rw [← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  refine (BoundedContinuousFunction.norm_le (norm_nonneg c)).2 fun x => ?_
  simpa [norm_smul, abs_of_nonneg (hχ01 x).1] using
    mul_le_of_le_one_left (norm_nonneg c) (hχ01 x).2

/-- Adding a compactly supported boundary preserves every constant-form augmentation, and hence
its mass lower bound. No mass bound on the filling or the perturbed functional is required. -/
theorem enorm_augmentation_le_mass_add_comp_extDerivCLM_mul {k : ℕ} {𝓕 𝓖 : Type*}
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    [FunLike 𝓖 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) V]
    [LinearMapClass 𝓖 ℝ 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) V] (T : 𝓕) (Q : 𝓖)
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hQ : IsCompact (dsupport Q)) (hQΩ : dsupport Q ⊆ Ω)
    (c : E [⋀^Fin k]→L[ℝ] F) :
    ‖augmentation T c‖ₑ ≤ mass (fun ω => T ω + Q (TestFunction.extDerivCLM ω)) * ‖c‖ₑ := by
  let B := (Q : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →ₗ[ℝ] V).comp (TestFunction.extDerivCLM :
    𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _).toLinearMap
  have hB : dsupport B ⊆ dsupport Q := dsupport_comp_extDerivCLM_subset Q
  have hBc : IsCompact (dsupport B) := hQ.of_isClosed_subset isClosed_dsupport hB
  have hBΩ : dsupport B ⊆ Ω := hB.trans hQΩ
  let A := (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →ₗ[ℝ] V) + B
  have hA : ⇑A = ⇑T + ⇑B := by
    funext ω
    simp [A]
  have hsum : dsupport A ⊆ dsupport T ∪ dsupport B :=
    hA ▸ dsupport_add_subset T B
  have hsumc : IsCompact (dsupport A) :=
    (hT.union hBc).of_isClosed_subset isClosed_dsupport hsum
  have hsumΩ : dsupport A ⊆ Ω := hsum.trans (union_subset hTΩ hBΩ)
  have haug : augmentation A c = augmentation T c := by
    have hzero : augmentation B c = 0 := augmentation_comp_extDerivCLM Q hQ hQΩ c
    rw [hA, augmentation_add T B hT hTΩ hBc hBΩ c, hzero, add_zero]
  have hcoe : (⇑A) = fun ω => T ω + Q (TestFunction.extDerivCLM ω) := by
    funext ω
    simp [A, B]
  have h := enorm_augmentation_le_mass_mul A hsumc hsumΩ c
  rwa [haug, hcoe] at h

/-- A weighted point current minimizes mass against every compactly supported boundary
perturbation, already among real-linear functionals. This includes positive, negative and zero
coefficients, in every ambient dimension. -/
theorem mass_mul_apply_finZero_le_mass_add_comp_extDerivCLM {𝓖 : Type*}
    [FunLike 𝓖 𝓓(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) ℝ]
    [LinearMapClass 𝓖 ℝ 𝓓(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) ℝ]
    {x : E} (hx : x ∈ Ω) (a : ℝ) (Q : 𝓖)
    (hQ : IsCompact (dsupport Q)) (hQΩ : dsupport Q ⊆ Ω) :
    mass (fun ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) => a * ω x ![]) ≤
      mass (fun ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) =>
        a * ω x ![] + Q (TestFunction.extDerivCLM ω)) := by
  let T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun ω := a * ω x ![]
      map_add' ω η := by simp [mul_add]
      map_smul' r ω := by simp [mul_left_comm] }
  have hpoint : (⇑T) = fun ω => a * ω x ![] := by
    funext ω
    simp [T]
  let ℓ : (E [⋀^Fin 0]→L[ℝ] ℝ) →+ ℝ :=
    { toFun ω := a * ω ![]
      map_zero' := by simp
      map_add' ω η := by simp [mul_add] }
  have hTx : dsupport T ⊆ {x} := by
    rw [hpoint]
    simpa [ℓ] using (dsupport_apply_apply_subset (Ω := Ω) (n := ⊤) (x := x) ℓ)
  have hTc : IsCompact (dsupport T) :=
    isCompact_singleton.of_isClosed_subset isClosed_dsupport hTx
  have hTΩ : dsupport T ⊆ Ω := hTx.trans (singleton_subset_iff.2 hx)
  let c := ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
  have hc : ‖c‖ₑ = 1 := by simp [c, ← ofReal_norm]
  have haug : augmentation T c = a := by
    rw [hpoint]
    simpa [ℓ, c] using (augmentation_apply_apply (n := ⊤) hx ℓ c)
  have hmass : mass T = ‖a‖ₑ := by
    have heq : (⇑T) = a • (fun ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) => ω x ![]) := by
      funext ω
      simp [T]
    rw [heq, mass_smul, mass_apply_finZero hx, mul_one]
  have h := enorm_augmentation_le_mass_add_comp_extDerivCLM_mul T Q hTc hTΩ hQ hQΩ c
  rwa [haug, hc, mul_one, ← hmass, hpoint] at h

end Distribution
