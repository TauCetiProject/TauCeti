/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# The topology of the quotient normal bundle of an immersion

Give the total space of the normal classes of an immersion `f : M → N` the quotient topology from
the ambient tangent bundle pulled back along `f`. This construction uses no metric or complement,
and applies to immersions into arbitrary ambient manifolds. Its projection and zero section are
continuous. The fibres are indexed by the source point, so the construction does not need `f` to
be injective.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Bundle Function Topology
open scoped Manifold ContDiff

namespace Manifold.IsImmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H G M N K : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω} {f : M → N}

/-- Take normal classes in the pulled-back ambient tangent bundle. The model parameter
`K` of the target total space does not affect the quotient construction. -/
@[expose] def normalQuotientMap (hf : IsImmersion I J n f) (hn : n ≠ 0)
    (p : TotalSpace F (f *ᵖ (TangentSpace J))) :
    TotalSpace K (fun x => hf.NormalSpace x hn) :=
  ⟨p.proj, hf.normalClass p.proj hn p.snd⟩

/-- The quotient map preserves the base and takes the fibrewise normal class. -/
@[simp] theorem normalQuotientMap_apply (hf : IsImmersion I J n f) (hn : n ≠ 0)
    (p : TotalSpace F (f *ᵖ (TangentSpace J))) :
    hf.normalQuotientMap (K := K) hn p = ⟨p.proj, hf.normalClass p.proj hn p.snd⟩ := (rfl)

/-- Every point of the normal total space has an ambient tangent representative. -/
theorem normalQuotientMap_surjective (hf : IsImmersion I J n f) (hn : n ≠ 0) :
    Surjective (hf.normalQuotientMap (K := K) hn) := by
  rintro ⟨x, w⟩
  obtain ⟨v, rfl⟩ := hf.normalClass_surjective x hn w
  exact ⟨⟨x, v⟩, rfl⟩

variable [IsManifold J 1 N]

/-- The normal total space has the quotient topology from the pulled-back ambient tangent
bundle. -/
instance instTopologicalSpaceNormalBundle (hf : IsImmersion I J n f) (hn : n ≠ 0) :
    TopologicalSpace (TotalSpace K (fun x => hf.NormalSpace x hn)) :=
  TopologicalSpace.coinduced (hf.normalQuotientMap hn) inferInstance

/-- Ambient tangent representatives give a quotient map onto the normal bundle. -/
theorem isQuotientMap_normalQuotientMap (hf : IsImmersion I J n f) (hn : n ≠ 0) :
    IsQuotientMap (hf.normalQuotientMap (K := K) hn) where
  eq_coinduced := rfl
  surjective := hf.normalQuotientMap_surjective hn

/-- A map out of the normal bundle is continuous exactly when its expression on ambient
tangent representatives is continuous. -/
theorem continuous_normalBundle_iff (hf : IsImmersion I J n f) (hn : n ≠ 0)
    {X : Type*} [TopologicalSpace X] {q : TotalSpace K (fun x => hf.NormalSpace x hn) → X} :
    Continuous q ↔ Continuous (q ∘ hf.normalQuotientMap hn) :=
  (hf.isQuotientMap_normalQuotientMap hn).continuous_iff

/-- The normal-bundle projection is continuous. -/
theorem continuous_normalBundle_proj (hf : IsImmersion I J n f) (hn : n ≠ 0) :
    Continuous (π K (fun x => hf.NormalSpace x hn)) := by
  rw [hf.continuous_normalBundle_iff hn]
  exact Pullback.continuous_proj F (TangentSpace J) f

/-- The zero section of the normal bundle is continuous. -/
theorem continuous_normalBundle_zeroSection (hf : IsImmersion I J n f) (hn : n ≠ 0) :
    Continuous (zeroSection K (fun x => hf.NormalSpace x hn)) := by
  -- The pullback bundle structure is that of the pullback along `f` as a continuous map.
  let fc : C(M, N) := ⟨f, hf.contMDiff.continuous⟩
  have hz : Continuous (zeroSection F ((fc : M → N) *ᵖ (TangentSpace J))) :=
    Bundle.Trivialization.continuous_zeroSection 𝕜
  convert (hf.isQuotientMap_normalQuotientMap (K := K) hn).continuous.comp hz using 1
  funext x
  simp only [Function.comp_apply, zeroSection, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk x) (hf.normalClass x hn).map_zero.symm

end Manifold.IsImmersion
