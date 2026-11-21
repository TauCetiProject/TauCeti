/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Nowhere-zero C^n sections from continuous ones

Let `V` be a real `C^n` vector bundle, `n ≤ ∞`, over a Hausdorff σ-compact smooth manifold
modelled on a finite-dimensional space, possibly with boundary or corners. A section continuous
and nowhere zero on a closed set `D` gives a global `C^n` section nowhere zero on `D`.
With a continuous fibrewise inner product, the section can instead be chosen to have positive
inner product with the original section on `D`. In a line bundle it can be chosen to be a positive
multiple of the original section on `D`.

These results upgrade sections obtained topologically on closed domains, without requiring a
manifold structure on the domain. In a smooth bundle the resulting section is smooth and nowhere
zero on an open neighbourhood of `D`; for an oriented smooth Riemannian surface, it can be
normalized and completed to a local orthonormal frame. The proofs use Mathlib's convex
partition-of-unity gluing, `exists_contMDiffSection_forall_mem_convex_of_local`, and
Hahn–Banach separation, `exists_dual_vector`.

## Main results

* `TauCeti.exists_contMDiffSection_forall_mem_inner_pos_of_continuousOn`: if `s` is continuous
  and nowhere zero on a closed set `D`, some `C^n` section `t` has `0 < ⟪s x, t x⟫` on `D`.
* `TauCeti.exists_contMDiffSection_forall_mem_ne_zero_of_continuousOn`: some global `C^n`
  section is nowhere zero on `D`, without any metric assumption.
* `TauCeti.exists_contMDiffSection_forall_mem_apply_pos_of_apply_pos`: a `C^n` section `ℓ` of the
  dual bundle positive on some section over `D` is positive on a global `C^n` section over `D`.
* `TauCeti.exists_contMDiffSection_forall_inner_pos_of_continuous`,
  `TauCeti.exists_contMDiffSection_forall_ne_zero_of_continuous`: the case `D = univ`.
* `TauCeti.exists_contMDiffSection_forall_mem_exists_pos_smul_of_continuousOn`,
  `TauCeti.exists_contMDiffSection_forall_exists_pos_smul_of_continuous`: in a line bundle, some
  `C^n` section is a positive multiple of `s` on `D`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 10.
-/

public section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} {V : M → Type*} [TopologicalSpace (TotalSpace F V)]

section InnerProduct

variable
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]
  [IsContinuousRiemannianBundle F V]

/-- A section `s` which is continuous and nowhere zero on a closed set `D` has a global `C^n`
section `t` with `0 < ⟪s x, t x⟫` at every point of `D`. Nothing is required off `D`. -/
theorem exists_contMDiffSection_forall_mem_inner_pos_of_continuousOn {D : Set M} (hD : IsClosed D)
    {s : Π x, V x} (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) D)
    (hne : ∀ x ∈ D, s x ≠ 0) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x ∈ D, 0 < inner ℝ (s x) (t x) := by
  refine exists_contMDiffSection_forall_mem_convex_of_local I V
    (fun x ↦ {v | x ∈ D → 0 < inner ℝ (s x) v}) (fun x ↦ ?_) fun x₀ ↦ ?_
  · by_cases hx : x ∈ D
    · simp only [hx, forall_const]
      exact (convex_Ioi (0 : ℝ)).linear_preimage (innerSL ℝ (s x)).toLinearMap
    · simpa [hx] using convex_univ
  by_cases hx₀ : x₀ ∈ D
  · obtain ⟨t, ht, heq⟩ := FiberBundle.exists_contMDiff_section_eq I F (n : ℕ∞ω) (s x₀)
    have hp : 0 < inner ℝ (s x₀) (t x₀) := by rw [heq]; exact real_inner_self_pos.mpr (hne x₀ hx₀)
    have he : ∀ᶠ x in 𝓝[D] x₀, 0 < inner ℝ (s x) (t x) :=
      ((hs.inner_bundle ht.continuous.continuousOn) x₀ hx₀).eventually (isOpen_Ioi.mem_nhds hp)
    exact ⟨_, eventually_nhdsWithin_iff.mp he, t, ht.contMDiffOn, fun _ hy ↦ hy⟩
  · exact ⟨Dᶜ, hD.isOpen_compl.mem_nhds hx₀, fun _ ↦ 0,
      (contMDiff_zeroSection ℝ V).contMDiffOn, fun _ hy hyD ↦ (hy hyD).elim⟩

/-- A continuous nowhere-zero section `s` has a `C^n` section `t` with `0 < ⟪s x, t x⟫` at
every point. -/
theorem exists_contMDiffSection_forall_inner_pos_of_continuous {s : Π x, V x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x))) (hne : ∀ x, s x ≠ 0) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x, 0 < inner ℝ (s x) (t x) := by
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_mem_inner_pos_of_continuousOn
    (I := I) (n := n) isClosed_univ hs.continuousOn fun x _ ↦ hne x
  exact ⟨t, fun x ↦ ht x (mem_univ x)⟩

end InnerProduct

variable [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

private theorem exists_contMDiffSection_forall_mem_apply_pos_of_continuousOn
    {D : Set M} (hD : IsClosed D)
    {s : Π x, V x} (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) D)
    (hne : ∀ x ∈ D, s x ≠ 0) :
    ∃ ℓ : Cₛ^n⟮I; StrongDual ℝ F, fun x ↦ StrongDual ℝ (V x)⟯,
      ∀ x ∈ D, 0 < ℓ x (s x) := by
  refine exists_contMDiffSection_forall_mem_convex_of_local I (fun x ↦ StrongDual ℝ (V x))
    (fun x ↦ {f | x ∈ D → 0 < f (s x)}) (fun x ↦ ?_) fun x₀ ↦ ?_
  · by_cases hx : x ∈ D
    · simp only [hx, forall_const]
      exact (convex_Ioi (0 : ℝ)).linear_preimage
        ((LinearMap.applyₗ (s x)).comp (ContinuousLinearMap.coeLM ℝ))
    · simpa [hx] using convex_univ
  by_cases hx₀ : x₀ ∈ D
  · let e := (trivializationAt F V x₀).continuousLinearEquivAt ℝ x₀
      (mem_baseSet_trivializationAt F V x₀)
    have hv : e (s x₀) ≠ 0 := by simpa using e.injective.ne (hne x₀ hx₀)
    obtain ⟨f, -, hf⟩ := exists_dual_vector ℝ (e (s x₀)) (norm_ne_zero_iff.mpr hv)
    obtain ⟨ℓ, hℓ, heq⟩ := FiberBundle.exists_contMDiff_section_eq
      (V := fun x ↦ StrongDual ℝ (V x)) I (StrongDual ℝ F)
      (n : ℕ∞ω) (f.comp e.toContinuousLinearMap)
    have hp : 0 < ℓ x₀ (s x₀) := by
      rw [heq]
      simpa [hf] using norm_pos_iff.mpr hv
    have hc : ContinuousOn (fun x ↦ ℓ x (s x)) D :=
      ((Bundle.Trivial.homeomorphProd M ℝ).continuous.comp_continuousOn
        (hℓ.continuous.continuousOn.clm_bundle_apply (E₂ := Trivial M ℝ) hs)).snd
    have he : ∀ᶠ x in 𝓝[D] x₀, 0 < ℓ x (s x) :=
      (hc x₀ hx₀).eventually (isOpen_Ioi.mem_nhds hp)
    exact ⟨_, eventually_nhdsWithin_iff.mp he, ℓ, hℓ.contMDiffOn, fun _ hy ↦ hy⟩
  · exact ⟨Dᶜ, hD.isOpen_compl.mem_nhds hx₀, fun _ ↦ 0,
      (contMDiff_zeroSection ℝ (fun x ↦ StrongDual ℝ (V x))).contMDiffOn,
      fun _ hy hyD ↦ (hy hyD).elim⟩

/-- A `C^n` section `ℓ` of the dual bundle which is positive on some section `s` over a closed set
`D` is positive on a global `C^n` section over `D`. No continuity of `s` is required. -/
theorem exists_contMDiffSection_forall_mem_apply_pos_of_apply_pos {D : Set M} (hD : IsClosed D)
    {s : Π x, V x} {ℓ : Cₛ^n⟮I; StrongDual ℝ F, fun x ↦ StrongDual ℝ (V x)⟯}
    (hℓ : ∀ x ∈ D, 0 < ℓ x (s x)) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x ∈ D, 0 < ℓ x (t x) := by
  refine exists_contMDiffSection_forall_mem_convex_of_local I V
    (fun x ↦ {v | x ∈ D → 0 < ℓ x v}) (fun x ↦ ?_) fun x₀ ↦ ?_
  · by_cases hx : x ∈ D
    · simp only [hx, forall_const]
      exact (convex_Ioi (0 : ℝ)).linear_preimage (ℓ x).toLinearMap
    · simpa [hx] using convex_univ
  by_cases hx₀ : x₀ ∈ D
  · obtain ⟨t, ht, heq⟩ := FiberBundle.exists_contMDiff_section_eq I F (n : ℕ∞ω) (s x₀)
    have hp : 0 < ℓ x₀ (t x₀) := by rw [heq]; exact hℓ x₀ hx₀
    have hc : Continuous (fun x ↦ ℓ x (t x)) :=
      ((Bundle.Trivial.homeomorphProd M ℝ).continuous.comp
        (ℓ.contMDiff.continuous.clm_bundle_apply (E₂ := Trivial M ℝ) ht.continuous)).snd
    have he : ∀ᶠ x in 𝓝 x₀, 0 < ℓ x (t x) :=
      hc.continuousAt.eventually (isOpen_Ioi.mem_nhds hp)
    exact ⟨_, he, t, ht.contMDiffOn, fun _ hy _ ↦ hy⟩
  · exact ⟨Dᶜ, hD.isOpen_compl.mem_nhds hx₀, fun _ ↦ 0,
      (contMDiff_zeroSection ℝ V).contMDiffOn, fun _ hy hyD ↦ (hy hyD).elim⟩

/-- A section of `V` which is continuous and nowhere zero on a closed set `D` gives a global
`C^n` section nowhere zero on `D`. No fibrewise metric is required. -/
theorem exists_contMDiffSection_forall_mem_ne_zero_of_continuousOn {D : Set M} (hD : IsClosed D)
    {s : Π x, V x} (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) D)
    (hne : ∀ x ∈ D, s x ≠ 0) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x ∈ D, t x ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_contMDiffSection_forall_mem_apply_pos_of_continuousOn
    (I := I) (n := n) hD hs hne
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_mem_apply_pos_of_apply_pos hD hℓ
  exact ⟨t, fun x hx h ↦ by simpa [h] using ht x hx⟩

/-- A continuous nowhere-zero section `s` of `V` gives a global nowhere-zero `C^n` section. -/
theorem exists_contMDiffSection_forall_ne_zero_of_continuous {s : Π x, V x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x))) (hne : ∀ x, s x ≠ 0) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x, t x ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_mem_ne_zero_of_continuousOn
    (I := I) (n := n) isClosed_univ hs.continuousOn fun x _ ↦ hne x
  exact ⟨t, fun x ↦ ht x (mem_univ x)⟩

/-- **A continuous nowhere-zero section of a line bundle is a positive multiple of a `C^n`
one.** Let `V` be a `C^n` line bundle, that is, with one-dimensional model fibre `F`. A section `s`
which is continuous and nowhere zero on a closed set `D` has a global `C^n` section `t` with `t x` a
positive multiple of `s x` at every point of `D`. -/
theorem exists_contMDiffSection_forall_mem_exists_pos_smul_of_continuousOn
    (hF : Module.finrank ℝ F = 1) {D : Set M} (hD : IsClosed D) {s : Π x, V x}
    (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) D) (hne : ∀ x ∈ D, s x ≠ 0) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x ∈ D, ∃ c : ℝ, 0 < c ∧ t x = c • s x := by
  obtain ⟨ℓ, hℓ⟩ := exists_contMDiffSection_forall_mem_apply_pos_of_continuousOn
    (I := I) (n := n) hD hs hne
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_mem_apply_pos_of_apply_pos hD hℓ
  refine ⟨t, fun x hx ↦ ?_⟩
  -- The fibre `V x` is a line, so `t x` is a multiple `c • s x`, and `ℓ x` is positive on both.
  have hV : Module.finrank ℝ (V x) = 1 :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).toLinearEquiv.finrank_eq.trans hF
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (s x) (hne x hx)).1 hV (t x)
  have hpos := ht x hx
  rw [← hc, map_smul, smul_eq_mul] at hpos
  exact ⟨c, pos_of_mul_pos_left hpos (hℓ x hx).le, hc.symm⟩

/-- A continuous nowhere-zero section `s` of a `C^n` line bundle is, at every point, a positive
multiple of a global `C^n` section. -/
theorem exists_contMDiffSection_forall_exists_pos_smul_of_continuous
    (hF : Module.finrank ℝ F = 1) {s : Π x, V x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x))) (hne : ∀ x, s x ≠ 0) :
    ∃ t : Cₛ^n⟮I; F, V⟯, ∀ x, ∃ c : ℝ, 0 < c ∧ t x = c • s x := by
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_mem_exists_pos_smul_of_continuousOn
    (I := I) (n := n) hF isClosed_univ hs.continuousOn fun x _ ↦ hne x
  exact ⟨t, fun x ↦ ht x (mem_univ x)⟩

end TauCeti
