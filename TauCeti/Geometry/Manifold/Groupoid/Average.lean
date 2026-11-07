/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Average
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Smooth cutoff averaging

A smooth cutoff function on an étale presentation averages smooth object functions to smooth
arrow-invariant functions. Locally the arrow sum is a fixed finite sum in local source
sections. Neither the function being averaged nor its support needs to be compact.

The algebraic projection and support bounds are in
`TauCeti.Topology.CategoryTheory.Groupoid.Average`. This regularity result allows that
projection to average smooth partitions of unity and other smooth invariant data.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2.
-/

public section

open CategoryTheory Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti.Quiver.IsCutoff

variable {E E' A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup A] [NormedSpace ℝ A]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {C : Type*} [Quiver C] [TopologicalSpace C] [ChartedSpace H C] [T2Space C]
  [WeaklyLocallyCompactSpace C] [TopologicalSpace (Quiver.Total C)]
  [ChartedSpace H' (Quiver.Total C)] [T2Space (Quiver.Total C)]
  {c : C → ℝ} {n : ℕ∞ω}

/-- A smooth cutoff average of a smooth function is smooth when source is a local
diffeomorphism and target is smooth. No compact-support hypothesis on the function is needed. -/
theorem contMDiff_average (hc : IsCutoff c) (hcs : ContMDiff I 𝓘(ℝ) n c)
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C))
    {f : C → A} (hf : ContMDiff I 𝓘(ℝ, A) n f) :
    ContMDiff I 𝓘(ℝ, A) n (hc.average f) := by
  intro x₀
  have hsupport : tsupport (fun a : Quiver.Total C ↦ c a.right • f a.right) ⊆
      Quiver.Total.right ⁻¹' tsupport c :=
    (tsupport_smul_subset_left (c ∘ Quiver.Total.right) (f ∘ Quiver.Total.right)).trans
      (tsupport_comp_subset_preimage c ht.continuous)
  obtain ⟨F, hF, hev⟩ := hs.isLocalHomeomorph.eventually_finsum_mem_preimage_singleton_eq_sum
    (f := fun a : Quiver.Total C ↦ c a.right • f a.right)
    (fun K hK ↦ (hc.isCompact_preimage_inter hK).of_isClosed_subset
      ((hK.isClosed.preimage hs.contMDiff.continuous).inter (isClosed_tsupport _))
      (inter_subset_inter_right _ hsupport))
    (σ := fun a ↦ (hs a).localInverse)
    (fun a ↦ (hs a).continuousAt_localInverse)
    (fun a ↦ (hs a).localInverse_left_inv (hs a).localInverse_mem_target)
    (fun a ↦ (hs a).localInverse_eventuallyEq_right) x₀
  have heq : hc.average f =ᶠ[𝓝 x₀] fun x ↦
      ∑ a ∈ F, c ((hs a).localInverse x).right • f ((hs a).localInverse x).right := by
    filter_upwards [hev] with x hx
    rw [average_eq_finsum]
    exact hx
  refine (ContMDiffAt.sum fun a ha ↦ ?_).congr_of_eventuallyEq heq
  rw [← hF a ha]
  have htσ := ht.contMDiffAt.comp _ (hs a).contMDiffAt_localInverse
  exact (hcs.contMDiffAt.comp _ htσ).smul (hf.contMDiffAt.comp _ htσ)

end TauCeti.Quiver.IsCutoff
