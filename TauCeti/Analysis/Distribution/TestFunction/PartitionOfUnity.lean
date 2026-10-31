/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Finite localization of test functions

A test function can be written as a finite sum of tests subordinate to any open cover of its
support. Consequently, an additive map on test functions which vanishes locally vanishes globally;
continuity of the additive map is not required. Every compact subset of the domain also has a
cutoff test function equal to one on a neighbourhood of it.

Multiplication by a smooth function `χ` whose closed support meets `Ω` only inside an open set `U`
sends tests on `Ω` to tests on `U`. This is `TestFunction.cutoffCLM`, a continuous linear map
`𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(U, F)` for the LF topologies; it is the localization step used to glue
distributions and currents defined on the members of an open cover.

The decomposition uses Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, applied to the
compact support, and the cutoff packages `IsCompact.exists_contDiff_cutoff` as a test function.
This is the partition-of-unity localization of distributions described in Hörmander, *The Analysis
of Linear Partial Differential Operators I*, §2.2 (Localization).
-/

public section

open Set TopologicalSpace Filter
open scoped Distributions ContDiff Manifold Topology

namespace TestFunction

section Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω U : Opens E} {n : ℕ∞} {χ : E → ℝ}

/-- Multiplication `φ ↦ χ φ` by a `C^n` function `χ` whose topological support meets `Ω` only
inside `U`, as a continuous linear map from tests on `Ω` to tests on `U`. When `U = Ω` this is
`TestFunction.smulLeftCLM`. -/
noncomputable def cutoffCLM (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ∩ Ω ⊆ U) :
    𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(U, F) :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ⟨fun x ↦ χ x • φ x, hχ.smul φ.contDiff, φ.hasCompactSupport.smul_left,
      (subset_inter (tsupport_smul_subset_left _ _) (tsupport_smul_subset_right _ _)).trans <|
        (inter_subset_inter_right _ φ.tsupport_subset).trans hχU⟩)
    (fun K hKΩ ↦
      -- On tests supported in `K`, the product is supported in the compact set `K ∩ tsupport χ`,
      -- which lies in `U`. Its structure maps are those of the product in `𝓓^{n}_{K}(E, F)`.
      letI K' : Compacts E := ⟨K ∩ tsupport χ, K.isCompact.inter_right (isClosed_tsupport χ)⟩
      haveI hsupp (f : 𝓓^{n}_{K}(E, F)) : Function.support (fun x ↦ χ x • f x) ⊆ (K' : Set E) :=
        fun _ hx ↦ ⟨f.support_subset (Function.support_smul_subset_right _ _ hx),
          subset_tsupport _ (Function.support_smul_subset_left _ _ hx)⟩
      letI M : 𝓓^{n}_{K}(E, F) →L[ℝ] 𝓓^{n}_{K'}(E, F) :=
        { toFun f := .of_support_subset (hχ.smul f.contDiff) (hsupp f)
          map_add' f g := by ext; simp [ContDiffMapSupportedIn.coe_of_support_subset, smul_add]
          map_smul' c f := by
            ext; simp [ContDiffMapSupportedIn.coe_of_support_subset, smul_comm c]
          cont := by
            refine (ContDiffMapSupportedIn.continuous_iff_comp _).2 fun i ↦ ?_
            refine ((ContDiffMapSupportedIn.structureMapCLM ℝ n i).continuous.comp
              (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ).flip hχ
                (K := K)).continuous).congr fun f ↦ ?_
            have hf : ⇑(ContDiffMapSupportedIn.of_support_subset (hχ.smul f.contDiff) (hsupp f)) =
                fun x ↦ χ x • f x :=
              funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
            ext x : 1
            simp [ContDiffMapSupportedIn.structureMapCLM_apply, hf] }
      ofSupportedInCLM ℝ (K := K') (fun _ hx ↦ hχU ⟨hx.2, hKΩ hx.1⟩) ∘L M)
    (fun _ _ _ ↦ rfl)

@[simp]
theorem cutoffCLM_apply (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ∩ Ω ⊆ U) (φ : 𝓓^{n}(Ω, F))
    (x : E) : cutoffCLM hχ hχU φ x = χ x • φ x := by
  -- This is the pointwise formula defining `cutoffCLM`; its body is not exported, so the
  -- definitional unfolding happens inside the proof.
  exact rfl

end Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {n : ℕ∞}

/-- A test function is a finite sum of test functions supported in members of an open cover
of its topological support. The summands are pointwise no larger in norm than the test function
itself. -/
theorem exists_sum_subordinate (φ : 𝓓^{n}(Ω, F)) {ι : Type*} (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hcover : tsupport φ ⊆ ⋃ i, U i) :
    ∃ (s : Finset ι) (ψ : s → 𝓓^{n}(Ω, F)),
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ ∑ i, ψ i = φ ∧ ∀ i x, ‖ψ i x‖ ≤ ‖φ x‖ := by
  classical
  obtain ⟨s, hs⟩ := φ.hasCompactSupport.elim_finite_subcover U hU hcover
  have hs' : tsupport φ ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E)
    (isClosed_tsupport φ) (fun i : s ↦ U i) (fun i ↦ hU i) hs'
  let ψ : s → 𝓓^{n}(Ω, F) := fun i ↦
    ⟨fun x ↦ ρ i x • φ x,
      ((ρ i).contMDiff.contDiff.of_le (by simp)).smul φ.contDiff,
      φ.hasCompactSupport.smul_left,
      (tsupport_smul_subset_right _ _).trans φ.tsupport_subset⟩
  refine ⟨s, ψ, fun i ↦ (tsupport_smul_subset_left _ _).trans (hρ i), ?_, fun i x ↦ ?_⟩
  · ext x
    simp only [sum_apply]
    by_cases hx : x ∈ tsupport φ
    · have hsum : ∑ i : s, ρ i x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      simp only [ψ, coe_mk, ← Finset.sum_smul, hsum, one_smul]
    · simp [ψ, image_eq_zero_of_notMem_tsupport hx]
  · -- Each summand is `ρ i • φ` with `0 ≤ ρ i ≤ 1`.
    simpa [ψ, norm_smul, abs_of_nonneg (ρ.nonneg i x)] using
      mul_le_of_le_one_left (norm_nonneg (φ x)) (ρ.le_one i x)

/-- Every compact subset of the domain has a test function with values in `[0, 1]` that is equal
to one on a neighbourhood of it. -/
theorem exists_eventually_eq_one {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : 𝓓^{n}(Ω, ℝ), (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨χ, hχ, hχ01, hχ1, hχc, hχΩ⟩ := hK.exists_contDiff_cutoff Ω.isOpen hKΩ
  exact ⟨⟨χ, hχ.of_le (by simp), hχc, hχΩ⟩,
    subset_interior_iff_mem_nhdsSet.1 hχ1, fun x ↦ hχ01 ⟨x, rfl⟩⟩

end TestFunction

namespace AddMonoidHom

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommMonoid G] {Ω : Opens E} {n : ℕ∞}

/-- An additive map on test functions vanishes if every point of the domain has an open
neighborhood on whose supported tests it vanishes. -/
theorem eq_zero_of_locally_vanishing (T : 𝓓^{n}(Ω, F) →+ G)
    (h : ∀ x ∈ Ω, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ U → T φ = 0) : T = 0 := by
  classical
  choose U hU hxU hT using fun x : Ω ↦ h x x.2
  ext φ
  obtain ⟨s, ψ, hψ, hsum, -⟩ := φ.exists_sum_subordinate U hU fun x hx ↦
    mem_iUnion.mpr ⟨⟨x, φ.tsupport_subset hx⟩, hxU _⟩
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hT i (ψ i) (hψ i)

end AddMonoidHom
