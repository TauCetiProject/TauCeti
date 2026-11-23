/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Fiber.BaseChange
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Descent of fibre cohomology loci

Fibre cohomology finranks and vanishing are unchanged by an arbitrary base change of a
family. The finrank is natural-valued and is zero for infinite-dimensional cohomology; it agrees
with the usual dimension in the finite-dimensional case. Upper semicontinuity therefore pulls
back along every base map. When the base map induces the final topology, upper semicontinuity
and local constancy of the finranks, together with openness of the vanishing locus, can also be
checked after base change. In particular, these checks descend through open surjective base maps,
such as the projection from an open cover.

Only quasi-compactness and quasi-separatedness of the original fibres and quasi-coherence of
the restricted coefficients are needed. Quasi-compact quasi-separated families with a
quasi-coherent coefficient sheaf supply these hypotheses by typeclass inference.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Scheme.Modules Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open CategoryTheory.IsPullback

universe u

namespace CategoryTheory.IsPullback

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [∀ s' : S', CompactSpace (f.fiber (g s'))]
  [∀ s' : S', QuasiSeparatedSpace (f.fiber (g s'))]
  (H : IsPullback g' f' f g) (M : X.Modules)
  [∀ s' : S', ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M).IsQuasicoherent]

include H

/-- Upper semicontinuity of the fibre cohomology finrank is preserved by every base change.
When fibre cohomology is finite-dimensional, this is the corresponding dimension statement. -/
theorem upperSemicontinuous_fiberCohomologyFinrank_baseChange (n : ℕ)
    (h : UpperSemicontinuous (fiberCohomologyFinrank M f n)) :
    UpperSemicontinuous (fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n) := by
  have heq : fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n =
      (fiberCohomologyFinrank M f n) ∘ g :=
    funext fun s' ↦ fiberCohomologyFinrank_baseChange H M n s'
  rw [heq]
  exact h.comp g.continuous

/-- Upper semicontinuity of the fibre cohomology finrank can be checked after a base change
inducing the final topology. -/
theorem upperSemicontinuous_fiberCohomologyFinrank_baseChange_iff
    (hg : IsCoinducing (g : S' → S)) (n : ℕ) :
    UpperSemicontinuous (fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n) ↔
      UpperSemicontinuous (fiberCohomologyFinrank M f n) := by
  have heq : fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n =
      (fiberCohomologyFinrank M f n) ∘ g :=
    funext fun s' ↦ fiberCohomologyFinrank_baseChange H M n s'
  rw [heq, upperSemicontinuous_iff_isOpen_preimage, upperSemicontinuous_iff_isOpen_preimage]
  simp only [Set.preimage_comp]
  exact forall_congr' fun _ ↦ hg.isOpen_preimage

/-- Local constancy of the fibre cohomology finrank can be checked after a base change inducing
the final topology. -/
theorem isLocallyConstant_fiberCohomologyFinrank_baseChange_iff
    (hg : IsCoinducing (g : S' → S)) (n : ℕ) :
    IsLocallyConstant (fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n) ↔
      IsLocallyConstant (fiberCohomologyFinrank M f n) := by
  have heq : fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n =
      (fiberCohomologyFinrank M f n) ∘ g :=
    funext fun s' ↦ fiberCohomologyFinrank_baseChange H M n s'
  rw [heq, IsLocallyConstant.iff_isOpen_fiber, IsLocallyConstant.iff_isOpen_fiber]
  simp only [Set.preimage_comp]
  exact forall_congr' fun _ ↦ hg.isOpen_preimage

/-- Openness of the fibre-cohomology vanishing locus can be checked after a base change inducing
the final topology. No finite-dimensionality assumption on the cohomology is needed, because this
statement concerns vanishing directly rather than the finrank zero convention. -/
theorem isOpen_setOf_subsingleton_cohomology_fiber_baseChange_iff
    (hg : IsCoinducing (g : S' → S)) (n : ℕ) :
    IsOpen {s' : S' | Subsingleton (Cohomology
        ((Scheme.Modules.pullback (f'.fiberι s')).obj ((Scheme.Modules.pullback g').obj M)) n)} ↔
      IsOpen {s : S | Subsingleton
        (Cohomology ((Scheme.Modules.pullback (f.fiberι s)).obj M) n)} := by
  rw [← hg.isOpen_preimage]
  have heq : {s' : S' | Subsingleton (Cohomology
      ((Scheme.Modules.pullback (f'.fiberι s')).obj ((Scheme.Modules.pullback g').obj M)) n)} =
      g ⁻¹' {s : S | Subsingleton
        (Cohomology ((Scheme.Modules.pullback (f.fiberι s)).obj M) n)} :=
    Set.ext fun s' ↦ subsingleton_cohomology_fiber_baseChange_iff H M n s'
  rw [heq]

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
  [∀ s, CompactSpace (f.fiber s)] [∀ s, QuasiSeparatedSpace (f.fiber s)]
  [∀ s, ((Scheme.Modules.pullback (f.fiberι s)).obj M).IsQuasicoherent]

/-- Upper semicontinuity of the fibre cohomology finrank can be checked on the actual
base-changed families over the members of any open cover of the base. In the finite-dimensional
case, this is the corresponding dimension statement. -/
theorem upperSemicontinuous_fiberCohomologyFinrank_iff_openCover (𝒰 : S.OpenCover) (n : ℕ) :
    UpperSemicontinuous (fiberCohomologyFinrank M f n) ↔
      ∀ i, UpperSemicontinuous (fiberCohomologyFinrank
        ((Scheme.Modules.pullback (pullback.fst f (𝒰.f i))).obj M)
        (pullback.snd f (𝒰.f i)) n) := by
  constructor
  · intro h i
    exact upperSemicontinuous_fiberCohomologyFinrank_baseChange
      (IsPullback.of_hasPullback f (𝒰.f i)) M n h
  · intro h
    rw [upperSemicontinuous_iff_isOpen_preimage]
    intro r
    have hi (i : 𝒰.I₀) : IsOpen ((𝒰.f i) ⁻¹'
        (fiberCohomologyFinrank M f n ⁻¹' Set.Iio r)) := by
      have heq : fiberCohomologyFinrank
          ((Scheme.Modules.pullback (pullback.fst f (𝒰.f i))).obj M)
          (pullback.snd f (𝒰.f i)) n = (fiberCohomologyFinrank M f n) ∘ 𝒰.f i :=
        funext fun s ↦ fiberCohomologyFinrank_baseChange
          (IsPullback.of_hasPullback f (𝒰.f i)) M n s
      have hr := (h i).isOpen_preimage r
      rwa [heq, Set.preimage_comp] at hr
    rw [isOpen_iff_of_cover (fun i ↦ (𝒰.f i).isOpenEmbedding.isOpen_range) 𝒰.iUnion_range]
    intro i
    rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
    exact (𝒰.f i).isOpenEmbedding.isOpenMap _ (hi i)

end AlgebraicGeometry.Scheme.Hom
