/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Regularity of sums and differences of sections along a map

Let `V` be a vector bundle over `B` and `b : X → B` a map. A family `s x ∈ V (b x)` is a section
of `V` along `b`, and its total-space map is `x ↦ ⟨b x, s x⟩`. Fibrewise sums of `C^n` sections
along the same map are `C^n` (`ContMDiff.add_sectionAlong`), and so are fibrewise differences
(`ContMDiff.sub_sectionAlong`); for products with `C^n` functions, see
`ContMDiff.smul_totalSpace`. Finite sums follow (`ContMDiff.sum_sectionAlong`); smoothness of
the base map is assumed so that the empty sum, the zero section along `b`, is covered.
Differences of differentiable sections along a common base map are differentiable as well
(`MDifferentiableWithinAt.sub_sectionAlong`).

These generalize Mathlib's results for sections of `V` itself, the case `b = id`, to sections
along a base map: the `add_sectionAlong`, `sub_sectionAlong` and `sum_sectionAlong` families
generalize Mathlib's `ContMDiff.add_section`, `ContMDiff.sub_section` and
`ContMDiff.sum_section` families, and `MDifferentiable*.sub_sectionAlong` generalize
`mdifferentiableWithinAt_sub_section` and `mdifferentiableAt_sub_section`. The general form
also covers fibre-preserving self-maps of the total space, `p ↦ ⟨p.proj, φ p⟩` with
`φ p ∈ V p.proj`, viewed as sections along the projection `TotalSpace.proj`.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 B X F EB HB EX HX : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX}
  [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] {n : WithTop ℕ∞}

section AddCommMonoid

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  {b : X → B} {s t : ∀ x, V (b x)} {u : Set X} {x₀ : X}

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n` within a set at
a point. -/
theorem ContMDiffWithinAt.add_sectionAlong
    (hs : ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) u x₀)
    (ht : ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) u x₀) :
    ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) u x₀ := by
  rw [contMDiffWithinAt_totalSpace_iff] at hs ht ⊢
  obtain ⟨h, h₀⟩ :=
    (trivializationAt F V (b x₀)).toPretrivialization.snd_apply_mk_op_eventuallyEq_and_eq 𝕜
      (s := s) (t := t) (fun _ g ↦ g.map_add) hs.1.continuousWithinAt
      (FiberBundle.mem_baseSet_trivializationAt' (b x₀))
  exact ⟨hs.1, (hs.2.add ht.2).congr_of_eventuallyEq h h₀⟩

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n` at a point. -/
theorem ContMDiffAt.add_sectionAlong
    (hs : ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) x₀)
    (ht : ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) x₀) :
    ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) x₀ :=
  contMDiffWithinAt_univ.mp (hs.contMDiffWithinAt.add_sectionAlong ht.contMDiffWithinAt)

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n` on a set. -/
theorem ContMDiffOn.add_sectionAlong
    (hs : ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) u)
    (ht : ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) u) :
    ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) u :=
  fun x hx ↦ (hs x hx).add_sectionAlong (ht x hx)

/-- The fibrewise sum of two `C^n` sections along the same map is `C^n`. -/
theorem ContMDiff.add_sectionAlong
    (hs : ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)))
    (ht : ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x))) :
    ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x + t x)) :=
  fun x ↦ (hs x).add_sectionAlong (ht x)

/-- A finite sum of `C^n` sections along a `C^n` map is `C^n` within a set at a point. -/
theorem ContMDiffWithinAt.sum_sectionAlong {ι : Type*} (A : Finset ι) (s : ι → ∀ x, V (b x))
    (hb : ContMDiffWithinAt IX IB n b u x₀)
    (hs : ∀ i ∈ A, ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s i x)) u x₀) :
    ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (∑ i ∈ A, s i x)) u x₀ := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Function.comp_def, zeroSection] using
      (contMDiff_zeroSection 𝕜 V).contMDiffAt.comp_contMDiffWithinAt x₀ hb
  | @insert i A hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hs i (Finset.mem_insert_self i A)).add_sectionAlong
        (ih fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))

/-- A finite sum of `C^n` sections along a `C^n` map is `C^n` at a point. -/
theorem ContMDiffAt.sum_sectionAlong {ι : Type*} (A : Finset ι) (s : ι → ∀ x, V (b x))
    (hb : ContMDiffAt IX IB n b x₀)
    (hs : ∀ i ∈ A, ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s i x)) x₀) :
    ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (∑ i ∈ A, s i x)) x₀ :=
  contMDiffWithinAt_univ.mp <| .sum_sectionAlong A s hb.contMDiffWithinAt fun i hi ↦
    (hs i hi).contMDiffWithinAt

/-- A finite sum of `C^n` sections along a `C^n` map is `C^n` on a set. -/
theorem ContMDiffOn.sum_sectionAlong {ι : Type*} (A : Finset ι) (s : ι → ∀ x, V (b x))
    (hb : ContMDiffOn IX IB n b u)
    (hs : ∀ i ∈ A, ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s i x)) u) :
    ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (∑ i ∈ A, s i x)) u :=
  fun x hx ↦ ContMDiffWithinAt.sum_sectionAlong A s (hb x hx) (fun i hi ↦ hs i hi x hx)

/-- A finite sum of `C^n` sections along a `C^n` map is `C^n`. -/
theorem ContMDiff.sum_sectionAlong {ι : Type*} (A : Finset ι) (s : ι → ∀ x, V (b x))
    (hb : ContMDiff IX IB n b)
    (hs : ∀ i ∈ A, ContMDiff IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s i x))) :
    ContMDiff IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (∑ i ∈ A, s i x)) :=
  fun x ↦ ContMDiffAt.sum_sectionAlong A s (hb x) (fun i hi ↦ hs i hi x)

end AddCommMonoid

section AddCommGroup

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  {b : X → B} {s t : ∀ x, V (b x)} {u : Set X} {x₀ : X}

/-- The fibrewise difference of two `C^n` sections along the same map is `C^n` within a set at
a point. -/
theorem ContMDiffWithinAt.sub_sectionAlong
    (hs : ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) u x₀)
    (ht : ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) u x₀) :
    ContMDiffWithinAt IX (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) u x₀ := by
  rw [contMDiffWithinAt_totalSpace_iff] at hs ht ⊢
  obtain ⟨h, h₀⟩ :=
    (trivializationAt F V (b x₀)).toPretrivialization.snd_apply_mk_op_eventuallyEq_and_eq 𝕜
      (s := s) (t := t) (fun _ g ↦ g.map_sub) hs.1.continuousWithinAt
      (FiberBundle.mem_baseSet_trivializationAt' (b x₀))
  exact ⟨hs.1, (hs.2.sub ht.2).congr_of_eventuallyEq h h₀⟩

/-- The fibrewise difference of two `C^n` sections along the same map is `C^n` at a point. -/
theorem ContMDiffAt.sub_sectionAlong
    (hs : ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) x₀)
    (ht : ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) x₀) :
    ContMDiffAt IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) x₀ :=
  contMDiffWithinAt_univ.mp (hs.contMDiffWithinAt.sub_sectionAlong ht.contMDiffWithinAt)

/-- The fibrewise difference of two `C^n` sections along the same map is `C^n` on a set. -/
theorem ContMDiffOn.sub_sectionAlong
    (hs : ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)) u)
    (ht : ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x)) u) :
    ContMDiffOn IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) u :=
  fun x hx ↦ (hs x hx).sub_sectionAlong (ht x hx)

/-- The fibrewise difference of two `C^n` sections along the same map is `C^n`. -/
theorem ContMDiff.sub_sectionAlong
    (hs : ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x)))
    (ht : ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (t x))) :
    ContMDiff IX (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) :=
  fun x ↦ (hs x).sub_sectionAlong (ht x)

/-- The difference of differentiable sections along the same base map is differentiable within
a set at a point. -/
theorem MDifferentiableWithinAt.sub_sectionAlong
    (hs : MDifferentiableWithinAt IX (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F (b x) (s x)) u x₀)
    (ht : MDifferentiableWithinAt IX (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F (b x) (t x)) u x₀) :
    MDifferentiableWithinAt IX (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) u x₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hs ht ⊢
  obtain ⟨h, h₀⟩ :=
    (trivializationAt F V (b x₀)).toPretrivialization.snd_apply_mk_op_eventuallyEq_and_eq 𝕜
      (s := s) (t := t) (fun _ g ↦ g.map_sub) hs.1.continuousWithinAt
      (FiberBundle.mem_baseSet_trivializationAt' (b x₀))
  exact ⟨hs.1, (hs.2.sub ht.2).congr_of_eventuallyEq h h₀⟩

/-- The difference of differentiable sections along the same base map is differentiable at a
point. -/
theorem MDifferentiableAt.sub_sectionAlong
    (hs : MDifferentiableAt IX (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F (b x) (s x)) x₀)
    (ht : MDifferentiableAt IX (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F (b x) (t x)) x₀) :
    MDifferentiableAt IX (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) x₀ :=
  mdifferentiableWithinAt_univ.mp
    (hs.mdifferentiableWithinAt.sub_sectionAlong ht.mdifferentiableWithinAt)

end AddCommGroup
