/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Basic

/-!
# Profinite flat modules over compact domains

Over a compact integral domain `O`, every `O`-linear functional `φ : M →ₗ[O] O ⧸ I` with open
kernel on a profinite flat `O`-module `M` admits an open submodule `V ≤ ker φ` containing
`(Ideal.span {ϖ} * I) • ⊤` such that `ϖ • m ∈ V` forces `m ∈ ker φ` for any nonzero `ϖ : O`
(`TauCeti.IsProfiniteFlat.exists_open_submodule_ker_of_mul`).
-/

public section

namespace TauCeti.IsProfiniteFlat

section IsDomain

variable {O M : Type*} [CommRing O] [IsDomain O] [TopologicalSpace O] [CompactSpace O]
  [AddCommGroup M] [Module O M] [TopologicalSpace M] (hM : IsProfiniteFlat O M)

include hM in
/-- Given `φ : M →ₗ[O] O ⧸ I` with open kernel on a profinite flat `O`-module `M` over a compact
domain `O`, and a nonzero scalar `ϖ : O`, there is an open submodule `V ≤ ker φ` containing
`(Ideal.span {ϖ} * I) • ⊤` such that `ϖ • m ∈ V` forces `m ∈ ker φ`. -/
theorem exists_open_submodule_ker_of_mul {I : Ideal O} {ϖ : O} (hϖ : ϖ ≠ 0)
    (φ : M →ₗ[O] O ⧸ I) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ V : Submodule O M, IsOpen (V : Set M) ∧ (Ideal.span {ϖ} * I) • (⊤ : Submodule O M) ≤ V ∧
      V ≤ LinearMap.ker φ ∧ ∀ ⦃m : M⦄, ϖ • m ∈ V → m ∈ LinearMap.ker φ := by
  have := hM.isTorsionFree; have ⟨⟨_, _, _, _⟩, _⟩ := hM
  have := hM.t2Space; have := hM.isLinearTopology
  let J₂ : Ideal O := Ideal.span {ϖ} * I
  have hC_closed : IsClosed ((fun m : M ↦ ϖ • m) '' (LinearMap.ker φ : Set M)ᶜ) :=
    (hker.isClosed_compl.isCompact.image (continuous_const.smul continuous_id)).isClosed
  have h0C : (0 : M) ∉ (fun m : M ↦ ϖ • m) '' (LinearMap.ker φ : Set M)ᶜ := by
    rintro ⟨m, hm, hm0⟩
    exact hm (smul_right_injective M hϖ (hm0.trans (smul_zero ϖ).symm) ▸ (LinearMap.ker φ).zero_mem)
  obtain ⟨V₀, hV₀_open, hV₀C⟩ :=
    (IsLinearTopology.hasBasis_open_submodule O).mem_iff.mp (hC_closed.compl_mem_nhds h0C)
  have hI_ker : I • (⊤ : Submodule O M) ≤ LinearMap.ker φ := Submodule.smul_le.mpr fun r hr m _ ↦
    by rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  refine ⟨(V₀ ⊓ LinearMap.ker φ) ⊔ (J₂ • (⊤ : Submodule O M)),
    Submodule.isOpen_mono (fun _ hx ↦ Submodule.mem_sup_left hx) (hV₀_open.inter hker),
    le_sup_right, sup_le inf_le_right
      ((Submodule.smul_mono_left Ideal.mul_le_right).trans hI_ker), fun {m} hm ↦ ?_⟩
  obtain ⟨v₁, hv₁, y, hy, heq⟩ := Submodule.mem_sup.mp hm
  have hy' : y ∈ Ideal.span ({ϖ} : Set O) • (I • (⊤ : Submodule O M)) := by
    simpa [J₂, mul_smul] using hy
  rw [Submodule.ideal_span_singleton_smul] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  have hmz : m - z ∈ LinearMap.ker φ := by
    by_contra hm_ker
    exact hV₀C hv₁.1 ⟨m - z, hm_ker, by simp [smul_sub, ← heq]⟩
  simpa using add_mem hmz (hI_ker hz)

end IsDomain

end TauCeti.IsProfiniteFlat
