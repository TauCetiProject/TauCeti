/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.Support
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak compactness under a mass bound

Real linear functionals on vector-valued test functions with a common finite mass
bound form a compact set for convergence on each test. The topology here is the
product topology on evaluation functions, not the compact-convergence topology on
continuous linear maps. Taking alternating forms as coefficients gives weak
compactness of mass-bounded real currents in a Euclidean open set.

The proof uses Hahn–Banach to extend each functional to bounded continuous
functions with the same bound, then takes the continuous image of a weak-star
compact dual ball. Extensions are not canonical and no extension is chosen as
part of the current's data. Closed support constraints and a uniform boundary mass
bound give closed subsets of this compact set. No support confinement is needed for test-evaluation
compactness: mass may escape to infinity in a weak limit. Neither sequential
compactness nor preservation of integer multiplicities is asserted here.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (mass and weak convergence).
* The formal compactness input is Mathlib's `WeakDual.isCompact_closedBall`;
  extension uses `exists_extension_norm_eq`.
-/

public section

open Set TopologicalSpace ContinuousLinearMap
open scoped Distributions Topology NNReal ENNReal BoundedContinuousFunction

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- A finite mass bound is equivalent to the existence of a bounded linear extension
to bounded continuous functions with that operator-norm bound. Only linearity of
the original functional is required; the extension need not be unique. -/
theorem mass_le_iff_exists_extension {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ]
    [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ] (T : 𝓕) (C : ℝ≥0) :
    mass T ≤ C ↔ ∃ L : StrongDual ℝ (E →ᵇ F),
      ‖L‖ ≤ C ∧ ∀ φ : 𝓓^{n}(Ω, F), L (φ : E →ᵇ F) = T φ := by
  constructor
  · intro hT
    let j : 𝓓^{n}(Ω, F) →ₗ[ℝ] (E →ᵇ F) :=
      (TestFunction.toBoundedContinuousFunctionCLM ℝ).toLinearMap
    have hbound (φ : 𝓓^{n}(Ω, F)) : ‖T φ‖ ≤ C * ‖j φ‖ :=
      norm_apply_le_of_mass_le T hT φ
    let f' := (LinearMap.ofClass T).compLeftInverse j
    obtain ⟨L, hL, hnorm⟩ := exists_extension_norm_eq (LinearMap.range j) f'
    refine ⟨L, hnorm.trans_le (LinearMap.opNorm_compLeftInverse_le C.2 hbound), fun φ => ?_⟩
    calc L (φ : E →ᵇ F) = L (j φ) :=
           congrArg L (TestFunction.toBoundedContinuousFunctionCLM_apply ℝ φ).symm
         _ = f' ⟨j φ, LinearMap.mem_range_self j φ⟩ :=
           hL ⟨j φ, LinearMap.mem_range_self j φ⟩
         _ = T φ :=
           LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨C, hbound⟩ φ (j φ) rfl
  · rintro ⟨L, hL, heq⟩
    refine mass_le_iff.2 fun φ hφ => ?_
    rw [← heq φ]
    have hb : ‖(φ : E →ᵇ F)‖ ≤ 1 := (BoundedContinuousFunction.norm_le (by norm_num)).2 hφ
    have h := (L.le_opNorm (φ : E →ᵇ F)).trans
      ((mul_le_mul_of_nonneg_left hb (norm_nonneg L)).trans (by simpa using hL))
    simpa only [ofReal_norm, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal h

/-- The evaluation functions of real continuous linear functionals with mass at most
`C` form a compact subset of the product of copies of `ℝ` indexed by test functions.
No support confinement is needed for this weak (test-evaluation) compactness. -/
theorem isCompact_image_coe_mass_le (C : ℝ≥0) :
    IsCompact ((fun T : 𝓓^{n}(Ω, F) →L[ℝ] ℝ => (T : 𝓓^{n}(Ω, F) → ℝ)) ''
      {T | mass T ≤ C}) := by
  let r : WeakDual ℝ (E →ᵇ F) → (𝓓^{n}(Ω, F) → ℝ) :=
    fun L φ => L (φ : E →ᵇ F)
  have hr : Continuous r := continuous_pi fun φ => WeakDual.eval_continuous (φ : E →ᵇ F)
  convert (WeakDual.isCompact_closedBall (0 : StrongDual ℝ (E →ᵇ F)) C).image hr using 1
  ext t
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨L, hL, heq⟩ := (mass_le_iff_exists_extension T C).1 hT
    exact ⟨StrongDual.toWeakDual L, by simpa using hL, funext heq⟩
  · rintro ⟨L, hL, rfl⟩
    -- Both equalities below are pointwise restriction: CLM composition evaluates by
    -- composition, the test inclusion preserves values, and toStrongDual only changes topology.
    refine ⟨L.toStrongDual ∘L TestFunction.toBoundedContinuousFunctionCLM ℝ, ?_, rfl⟩
    exact (mass_le_iff_exists_extension _ C).2 ⟨L.toStrongDual, by simpa using hL, fun _ => rfl⟩

variable [FiniteDimensional ℝ E]

/-- The evaluation functions of real continuous linear functionals with mass at most
`C` and distributional support in a closed set `K` form a compact set in the product
topology. The closed set `K` need not be compact. -/
theorem isCompact_image_coe_mass_le_dsupport_subset (C : ℝ≥0) {K : Set E}
    (hK : IsClosed K) :
    IsCompact ((fun T : 𝓓^{n}(Ω, F) →L[ℝ] ℝ => (T : 𝓓^{n}(Ω, F) → ℝ)) ''
      {T | mass T ≤ C ∧ dsupport T ⊆ K}) := by
  have hclosed : IsClosed {t : 𝓓^{n}(Ω, F) → ℝ | IsVanishingOn t Kᶜ} := by
    simp only [IsVanishingOn, ofPred_forall]
    exact isClosed_iInter fun φ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply φ) continuous_const
  convert (isCompact_image_coe_mass_le (Ω := Ω) (n := n) (F := F) C).inter_right hclosed using 1
  ext t
  constructor
  · rintro ⟨T, ⟨hT, hTK⟩, rfl⟩
    exact ⟨⟨T, hT, rfl⟩, (isVanishingOn_compl_dsupport T).mono (compl_subset_compl.2 hTK)⟩
  · rintro ⟨⟨T, hT, rfl⟩, hTK⟩
    have hs : dsupport T ⊆ K := by
      simpa using (hTK.disjoint_dsupport hK.isOpen_compl).subset_compl_left
    exact ⟨T, ⟨hT, hs⟩, rfl⟩

/-- Real currents with uniformly bounded mass and boundary mass and a common closed
support constraint form a weakly compact set of evaluation functions. This does
not assert integral rectifiability of a limit. In degree zero use
`isCompact_image_coe_mass_le_dsupport_subset`, since the boundary is zero. -/
theorem isCompact_image_coe_mass_le_comp_extDerivCLM_le_dsupport_subset
    (k : ℕ) (C C' : ℝ≥0) {K : Set E} (hK : IsClosed K) :
    IsCompact ((fun T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ =>
      (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) → ℝ)) ''
      {T | mass T ≤ C ∧ mass (T ∘L TestFunction.extDerivCLM) ≤ C' ∧ dsupport T ⊆ K}) := by
  have hd : Continuous (fun t : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) → ℝ =>
      t ∘ TestFunction.extDerivCLM (k := k)) :=
    continuous_pi fun φ => continuous_apply (TestFunction.extDerivCLM φ)
  have hclosed : IsClosed ((fun t : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) → ℝ =>
      t ∘ TestFunction.extDerivCLM (k := k)) ⁻¹' {t | mass t ≤ C'}) :=
    (lowerSemicontinuous_mass.isClosed_preimage (C' : ℝ≥0∞)).preimage hd
  have hcompact := (isCompact_image_coe_mass_le_dsupport_subset
    (Ω := Ω) (n := ⊤) (F := E [⋀^Fin (k + 1)]→L[ℝ] F) C hK).inter_right hclosed
  rw [← Set.image_inter_preimage] at hcompact
  simpa only [preimage_ofPred_eq, inter_ofPred_eq_sep, mem_ofPred_eq, coe_comp,
    ← and_assoc, and_right_comm] using hcompact

end Distribution
