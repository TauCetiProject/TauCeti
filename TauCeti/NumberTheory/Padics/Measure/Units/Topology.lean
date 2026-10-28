/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Units.Basic
public import TauCeti.NumberTheory.Padics.Measure.Clopen.Topology

/-!
# Topologies on measures on the p-adic units

The identification of measures on `ℤ_pˣ` with the kernel of psi on measures on `ℤ_p` is a
homeomorphism for both the weak and strong topologies. Intrinsic restriction to the units is
continuous in either topology. For field coefficients it contracts the continuous-dual norm,
and inclusion along `Units.val` preserves that norm exactly.

Thus a unit-supported ambient measure and its intrinsic unit-group measure have the same
convergence properties and operator norm. The weak results allow arbitrary normed commutative
coefficient rings; the strong results require a nontrivially normed field, with no completeness
or ultrametricity assumption. Both topologies are selected explicitly, with the kernel carrying
the induced subtype topology. No global topology or norm instance on measures is introduced.

The proofs use the clopen restriction API and `PadicInt.unitsHomeomorphIsUnit` to transport
between the unit locus and the existing unit group.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  Definitions 3.5 and 3.8, Remark 3.31, Corollary 3.32 and Remark 3.33.
-/

public section

open ContinuousMap TopologicalSpace Topology

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

section Weak

variable {R : Type*} [NormedCommRing R]

/-- Intrinsic restriction to the p-adic units is continuous for the weak measure topologies. -/
theorem continuous_restrictUnits_weak :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]) (R := R) (E := R))
      (WeakTopology (X := ℤ_[p]ˣ) (R := R) (E := R)) restrictUnits := by
  let : TopologicalSpace D(ℤ_[p], R) := WeakTopology
  let : TopologicalSpace D(ℤ_[p]ˣ, R) := WeakTopology
  let : TopologicalSpace D(PadicInt.unitsClopen p, R) := WeakTopology
  have h := ((⟨(PadicInt.unitsHomeomorphIsUnit p).symm,
    (PadicInt.unitsHomeomorphIsUnit p).symm.continuous⟩ :
      C(PadicInt.unitsClopen p, ℤ_[p]ˣ)).continuous_abstractMeasure_map_weak (R := R) (E := R)).comp
        (Clopens.continuous_restrictClopen_weak (PadicInt.unitsClopen p))
  exact h.congr fun μ ↦ by
    rw [restrictUnits_def]
    exact (congrFun (coe_arrowCongrLeft (PadicInt.unitsHomeomorphIsUnit p).symm) _).symm

/-- The unit-group measure equivalence is a homeomorphism onto the psi kernel with its induced
ambient weak topology. -/
theorem isHomeomorph_unitsMeasureEquivKerPsi_weak :
    @IsHomeomorph _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := R) (E := R))
      (@instTopologicalSpaceSubtype D(ℤ_[p], R)
        (fun μ ↦ μ ∈ LinearMap.ker (psiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R)))
        WeakTopology) (unitsMeasureEquivKerPsi (p := p) (R := R)) := by
  let : TopologicalSpace D(ℤ_[p], R) := WeakTopology
  let : TopologicalSpace D(ℤ_[p]ˣ, R) := WeakTopology
  rw [LinearEquiv.isHomeomorph_iff]
  constructor
  · apply Continuous.subtype_mk
    exact (continuous_abstractMeasure_map_weak (R := R) (E := R)
      (⟨Units.val, Units.continuous_val⟩ : C(ℤ_[p]ˣ, ℤ_[p]))).congr
        fun ν ↦ (unitsMeasureEquivKerPsi_apply ν).symm
  · exact ((continuous_restrictUnits_weak (p := p) (R := R)).comp
      continuous_subtype_val).congr fun μ ↦ (unitsMeasureEquivKerPsi_symm_apply μ).symm

end Weak

section Norm

variable {K : Type*} [NontriviallyNormedField K]

/-- Intrinsic restriction to the p-adic units contracts the continuous-dual operator norm. -/
theorem norm_toCLMEquiv_restrictUnits_le (μ : D(ℤ_[p], K)) :
    ‖toCLMEquiv (restrictUnits μ)‖ ≤ ‖toCLMEquiv μ‖ := by
  rw [restrictUnits_def]
  have h := norm_toCLMEquiv_map_le (restrictClopen (PadicInt.unitsClopen p) μ)
    (⟨(PadicInt.unitsHomeomorphIsUnit p).symm,
      (PadicInt.unitsHomeomorphIsUnit p).symm.continuous⟩ :
        C(PadicInt.unitsClopen p, ℤ_[p]ˣ))
  rw [← coe_arrowCongrLeft] at h
  exact h.trans (Clopens.norm_toCLMEquiv_restrictClopen_le (PadicInt.unitsClopen p) μ)

/-- Inclusion from the p-adic unit group preserves the continuous-dual operator norm. -/
-- Apply this before the inner pushforward is rewritten as precomposition.
@[simp↓]
theorem norm_toCLMEquiv_map_unitsVal (ν : D(ℤ_[p]ˣ, K)) :
    ‖toCLMEquiv (map ⟨Units.val, Units.continuous_val⟩ ν)‖ = ‖toCLMEquiv ν‖ := by
  refine le_antisymm (norm_toCLMEquiv_map_le ν _) ?_
  simpa only [restrictUnits_map_unitsVal] using
    norm_toCLMEquiv_restrictUnits_le (map ⟨Units.val, Units.continuous_val⟩ ν)

/-- Intrinsic restriction to the p-adic units is continuous for the strong measure topologies. -/
theorem continuous_restrictUnits_strong :
    @Continuous _ _ (StrongTopology (X := ℤ_[p]) (R := K) (E := K))
      (StrongTopology (X := ℤ_[p]ˣ) (R := K) (E := K)) restrictUnits := by
  let : TopologicalSpace D(ℤ_[p], K) := StrongTopology
  let : TopologicalSpace D(ℤ_[p]ˣ, K) := StrongTopology
  let : TopologicalSpace D(PadicInt.unitsClopen p, K) := StrongTopology
  have h := ((⟨(PadicInt.unitsHomeomorphIsUnit p).symm,
    (PadicInt.unitsHomeomorphIsUnit p).symm.continuous⟩ :
      C(PadicInt.unitsClopen p, ℤ_[p]ˣ)).continuous_abstractMeasure_map_strong
        (R := K) (E := K)).comp (Clopens.continuous_restrictClopen_strong (PadicInt.unitsClopen p))
  exact h.congr fun μ ↦ by
    rw [restrictUnits_def]
    exact (congrFun (coe_arrowCongrLeft (PadicInt.unitsHomeomorphIsUnit p).symm) _).symm

/-- The unit-group measure equivalence is a homeomorphism onto the psi kernel with its induced
ambient strong topology. The coefficient field need not be complete or ultrametric. -/
theorem isHomeomorph_unitsMeasureEquivKerPsi_strong :
    @IsHomeomorph _ _ (StrongTopology (X := ℤ_[p]ˣ) (R := K) (E := K))
      (@instTopologicalSpaceSubtype D(ℤ_[p], K)
        (fun μ ↦ μ ∈ LinearMap.ker (psiMeasure : D(ℤ_[p], K) →ₗ[K] D(ℤ_[p], K)))
        StrongTopology) (unitsMeasureEquivKerPsi (p := p) (R := K)) := by
  let : TopologicalSpace D(ℤ_[p], K) := StrongTopology
  let : TopologicalSpace D(ℤ_[p]ˣ, K) := StrongTopology
  rw [LinearEquiv.isHomeomorph_iff]
  constructor
  · apply Continuous.subtype_mk
    exact (continuous_abstractMeasure_map_strong (R := K) (E := K)
      (⟨Units.val, Units.continuous_val⟩ : C(ℤ_[p]ˣ, ℤ_[p]))).congr
        fun ν ↦ (unitsMeasureEquivKerPsi_apply ν).symm
  · exact ((continuous_restrictUnits_strong (p := p) (K := K)).comp
      continuous_subtype_val).congr fun μ ↦ (unitsMeasureEquivKerPsi_symm_apply μ).symm

end Norm

end AbstractMeasure
