/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair

/-!
# Homomorphisms with locally quasi-finite or finite kernel

A homomorphism of group schemes locally of finite type is locally quasi-finite exactly when its
scheme-theoretic kernel is locally quasi-finite over the base. A proper homomorphism is finite
exactly when its kernel is finite. This criterion is used to characterize isogenies of abelian
varieties.

## References

* J. S. Milne, *Abelian Varieties*, §8, Proposition 8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace CategoryTheory.Grp

/-- A homomorphism of group schemes locally of finite type is locally quasi-finite exactly when
its scheme-theoretic kernel is locally quasi-finite over the base. -/
theorem locallyQuasiFinite_iff_locallyQuasiFinite_kernel {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) [LocallyOfFiniteType f.hom.hom.left] :
    LocallyQuasiFinite f.hom.hom.left ↔ LocallyQuasiFinite (kernel f).X.hom := by
  refine ⟨MorphismProperty.of_isPullback (TauCeti.GroupScheme.isPullback_kernel_left f), ?_⟩
  intro hkernel
  let i : (kernel f).X ⟶ G.X := (kernel.ι f).hom.hom
  let q := snd (kernel f).X G.X
  let p := (fst (kernel f).X G.X ≫ i) * q
  have h : IsPullback p.left q.left f.hom.hom.left f.hom.hom.left :=
    (TauCeti.isPullback_mul_of_isPullback_one f.hom.hom i
      (TauCeti.GroupScheme.isPullback_kernel_hom f)).map (Over.forget S)
  have hq : LocallyQuasiFinite q.left := by
    dsimp only [q, Over.snd_left]
    infer_instance
  apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
  intro y
  by_cases hy : y ∈ Set.range f.hom.hom.left
  · obtain ⟨x, rfl⟩ := hy
    -- The fibre over `x` of the second projection is discrete and has the same dimension.
    have hdim_le : topologicalKrullDim (f.hom.hom.left.fiber (f.hom.hom.left x)) ≤ 0 :=
      (TauCeti.AlgebraicGeometry.topologicalKrullDim_fiber_of_isPullback h x).symm.trans_le
        (topologicalKrullDim_zero_of_discreteTopology (q.left.fiber x))
    have : LocallyOfFiniteType (f.hom.hom.left.fiberToSpecResidueField (f.hom.hom.left x)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
    have : IsLocallyNoetherian (f.hom.hom.left.fiber (f.hom.hom.left x)) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.hom.hom.left.fiberToSpecResidueField _)
    have : IsLocallyArtinian (f.hom.hom.left.fiber (f.hom.hom.left x)) :=
      .of_topologicalKrullDim_le_zero hdim_le
    exact ⟨(f.hom.hom.left.fiberHomeo _).discreteTopology⟩
  · rw [Set.preimage_singleton_eq_empty.mpr hy]
    exact Set.subsingleton_empty.isDiscrete

/-- A proper homomorphism of group schemes is finite exactly when its scheme-theoretic kernel
is finite over the base. -/
theorem isFinite_iff_isFinite_kernel {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
    [IsProper f.hom.hom.left] : IsFinite f.hom.hom.left ↔ IsFinite (kernel f).X.hom := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  have := (locallyQuasiFinite_iff_locallyQuasiFinite_kernel f).mpr inferInstance
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end CategoryTheory.Grp
