/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak boundedness and norm boundedness

In a real or complex seminormed space, a set is norm bounded if and only if every
continuous linear functional has bounded image on it. Equivalently, its image in
`WeakSpace` is von Neumann bounded. In particular, weakly compact sets, weakly
convergent sequences, and sets in which every sequence has a weakly convergent subsequence
are norm bounded. No completeness or separability assumption
on the original space is needed. Conversely the norm is weakly lower semicontinuous
(`TauCeti.lowerSemicontinuous_norm_toWeakSpace_symm`): along a weakly convergent sequence the
norm of the limit is at most the lower limit of the norms.

The proof applies Mathlib's `banach_steinhaus` to the evaluation functionals on the
complete continuous dual, then uses `NormedSpace.inclusionInDoubleDualLi` to recover
the original norms. Weak boundedness uses `Bornology.IsVonNBounded`, rather than a
metric bornology on the weak topology.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.5 (weak topologies).
-/

public section

open Bornology Filter Set Topology

namespace TauCeti.NormedSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A set is norm bounded exactly when all its continuous linear functional images
are bounded. The space itself need not be complete. -/
theorem isBounded_iff_forall_dual_isBounded {s : Set E} :
    IsBounded s ↔ ∀ f : StrongDual 𝕜 E, IsBounded (f '' s) := by
  constructor
  · intro hs f
    exact f.lipschitzWith.isBounded_image hs
  · intro hs
    have hpointwise (f : StrongDual 𝕜 E) :
        ∃ C, ∀ x : s, ‖NormedSpace.inclusionInDoubleDual 𝕜 E x f‖ ≤ C := by
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hs f)
      exact ⟨C, fun x ↦ by simpa using hC (f x) (mem_image_of_mem f x.property)⟩
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun x : s ↦ NormedSpace.inclusionInDoubleDual 𝕜 E x) hpointwise
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx ↦ ?_⟩
    exact (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x ▸ hC ⟨x, hx⟩

/-- A set is bounded for the weak topology exactly when it is norm bounded. -/
@[simp]
theorem isVonNBounded_toWeakSpace_iff {s : Set E} :
    IsVonNBounded 𝕜 (toWeakSpace 𝕜 E '' s) ↔ IsBounded s := by
  constructor
  · intro hs
    apply (isBounded_iff_forall_dual_isBounded 𝕜).mpr
    intro f
    have hf := hs.image (WeakBilin.eval (topDualPairing 𝕜 E).flip f)
    apply (NormedSpace.isVonNBounded_iff 𝕜).mp
    -- Evaluation after the topology change is the original functional.
    convert hf using 1
    rw [image_image]
    congr 1
  · intro hs
    simpa only [toWeakSpaceCLM_eq_toWeakSpace] using
      ((NormedSpace.isVonNBounded_iff 𝕜).mpr hs).image (toWeakSpaceCLM 𝕜 E)

end TauCeti.NormedSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A weakly compact set is norm bounded, even in an incomplete space. -/
theorem IsCompact.isBounded_toWeakSpace_preimage {s : Set (WeakSpace 𝕜 E)}
    (hs : IsCompact s) : IsBounded (toWeakSpace 𝕜 E ⁻¹' s) := by
  rw [← TauCeti.NormedSpace.isVonNBounded_toWeakSpace_iff 𝕜,
    (toWeakSpace 𝕜 E).surjective.image_preimage]
  exact hs.isVonNBounded 𝕜

/-- A weakly convergent sequence is norm bounded, even in an incomplete space. -/
theorem Filter.Tendsto.isBounded_range_of_toWeakSpace {u : ℕ → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    Bornology.IsBounded (range u) := by
  rw [← TauCeti.NormedSpace.isVonNBounded_toWeakSpace_iff 𝕜, ← range_comp]
  exact hu.isVonNBounded_range 𝕜

/-- A set with weakly convergent subsequences for all its sequences is norm bounded.
Subsequential limits need not belong to the set. -/
theorem TauCeti.isBounded_of_forall_tendsto_subseq_toWeakSpace {K : Set E}
    (hK : ∀ u : ℕ → E, (∀ n, u n ∈ K) → ∃ x : E, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    Bornology.IsBounded K := by
  classical
  by_contra h
  rw [isBounded_iff_forall_norm_le] at h
  push Not at h
  choose u hu hnorm using fun n : ℕ ↦ h n
  obtain ⟨x, σ, hσ, hlim⟩ := hK u hu
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hlim.isBounded_range_of_toWeakSpace
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h₁ := hnorm (σ n)
  have h₂ := hC _ (mem_range_self n)
  have h₃ : (n : ℝ) ≤ σ n := by exact_mod_cast hσ.id_le n
  linarith

/-- **The norm is weakly lower semicontinuous.** It is the supremum of the weakly continuous
functions `x ↦ re (g x)` over the functionals `g` of norm at most one (Hahn–Banach). -/
theorem TauCeti.lowerSemicontinuous_norm_toWeakSpace_symm :
    LowerSemicontinuous fun x : WeakSpace 𝕜 E ↦ ‖(toWeakSpace 𝕜 E).symm x‖ := by
  intro x a ha
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 ((toWeakSpace 𝕜 E).symm x)
  have hcont : Continuous fun y : WeakSpace 𝕜 E ↦ RCLike.re (g ((toWeakSpace 𝕜 E).symm y)) :=
    RCLike.continuous_re.comp (WeakBilin.eval_continuous _ g)
  have hx : a < RCLike.re (g ((toWeakSpace 𝕜 E).symm x)) := by
    rwa [hgx, RCLike.ofReal_re]
  filter_upwards [continuousAt_const.eventually_lt hcont.continuousAt hx] with y hy
  calc a < RCLike.re (g ((toWeakSpace 𝕜 E).symm y)) := hy
    _ ≤ ‖g ((toWeakSpace 𝕜 E).symm y)‖ := RCLike.re_le_norm _
    _ ≤ ‖g‖ * ‖(toWeakSpace 𝕜 E).symm y‖ := g.le_opNorm _
    _ ≤ ‖(toWeakSpace 𝕜 E).symm y‖ := by
      simpa using mul_le_mul_of_nonneg_right hg (norm_nonneg ((toWeakSpace 𝕜 E).symm y))
