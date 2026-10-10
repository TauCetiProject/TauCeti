/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# The topology of the intrinsic normal bundle

Give the total space of intrinsic normal classes the quotient topology from the ambient
tangent bundle pulled back along the embedding. This construction uses no metric or
complement, and applies to embeddings in arbitrary ambient manifolds. Its projection and
zero section are continuous.

A commuting square with differentiable base map and C¹ ambient map induces a continuous
map of these total spaces: the ambient tangent map descends through the quotient. This is
the topological compatibility needed to express normal-bundle coordinates in different
ambient manifold charts.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24. The fibre maps are the existing `SmoothEmbedding.normalMap`.
-/

public section

noncomputable section

open Bundle Function Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H G M N K : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N] {n : ℕ∞ω}

/-- Take normal classes in the pulled-back ambient tangent bundle. The model parameter
`K` of the target total space does not affect the quotient construction. -/
def normalQuotientMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J))) :
    TotalSpace K (fun x => f.NormalSpace x hn) :=
  ⟨p.proj, f.normalClass p.proj hn p.2⟩

omit [IsManifold J 1 N] in
/-- The quotient map preserves the base and takes the fibrewise normal class. -/
@[simp] theorem normalQuotientMap_apply (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J))) :
    f.normalQuotientMap (K := K) hn p = ⟨p.proj, f.normalClass p.proj hn p.2⟩ := (rfl)

omit [IsManifold J 1 N] in
/-- Every point of the intrinsic normal total space has an ambient tangent representative. -/
theorem normalQuotientMap_surjective (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    Surjective (f.normalQuotientMap (K := K) hn) := by
  rintro ⟨x, w⟩
  obtain ⟨v, rfl⟩ := f.normalClass_surjective x hn w
  exact ⟨⟨x, v⟩, rfl⟩

/-- The intrinsic normal total space has the quotient topology from the pulled-back
ambient tangent bundle. -/
instance instTopologicalSpaceNormalBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    TopologicalSpace (TotalSpace K (fun x => f.NormalSpace x hn)) :=
  TopologicalSpace.coinduced (f.normalQuotientMap hn) inferInstance

/-- Ambient tangent representatives give a quotient map onto the intrinsic normal bundle. -/
theorem isQuotientMap_normalQuotientMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    IsQuotientMap (f.normalQuotientMap (K := K) hn) where
  eq_coinduced := rfl
  surjective := f.normalQuotientMap_surjective hn

/-- A map out of the normal bundle is continuous exactly when its expression on ambient
tangent representatives is continuous. -/
theorem continuous_normalBundle_iff (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {X : Type*} [TopologicalSpace X] {q : TotalSpace K (fun x => f.NormalSpace x hn) → X} :
    Continuous q ↔ Continuous (q ∘ f.normalQuotientMap hn) :=
  (f.isQuotientMap_normalQuotientMap hn).continuous_iff

/-- The intrinsic normal-bundle projection is continuous. -/
theorem continuous_normalBundle_proj (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    Continuous (π K (fun x => f.NormalSpace x hn)) := by
  rw [f.continuous_normalBundle_iff hn]
  exact Pullback.continuous_proj F (TangentSpace J) (f : M → N)

/-- The zero section of the intrinsic normal bundle is continuous. -/
theorem continuous_normalBundle_zeroSection (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    Continuous (zeroSection K (fun x => f.NormalSpace x hn)) := by
  have hz : Continuous (zeroSection F ((f : M → N) *ᵖ (TangentSpace J))) :=
    Bundle.Trivialization.continuous_zeroSection 𝕜
  convert (f.isQuotientMap_normalQuotientMap (K := K) hn).continuous.comp hz using 1
  funext x
  simp only [Function.comp_apply, zeroSection, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk x) (f.normalClass x hn).map_zero.symm

section Map

variable {E' F' H' G' M' N' K' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H'] [TopologicalSpace G']
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N'] {m : ℕ∞ω}

omit [IsManifold J 1 N] in
/-- On an ambient tangent representative, the induced normal-bundle map takes the normal
class of the ambient differential of the representative. -/
theorem normalBundleMap_normalQuotientMap
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' m M' N')
    (hn : n ≠ 0) (hm : m ≠ 0) {u : M → M'} {v : N → N'}
    (hu : MDifferentiable I I' u) (hv : MDifferentiable J J' v)
    (h : v ∘ f = g ∘ u) (p : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J))) :
    f.normalBundleMap (K := K) (K' := K') g hn hm hu hv h (f.normalQuotientMap hn p) =
      g.normalQuotientMap hm (⟨u p.proj, tangentSpaceCast J' (v (f p.proj)) (g (u p.proj))
        (mfderiv J J' v (f p.proj) p.2)⟩ : TotalSpace F' ((g : M' → N') *ᵖ (TangentSpace J'))) := by
  rw [normalBundleMap_apply]
  exact congrArg (TotalSpace.mk (u p.proj))
    (f.normalMap_normalClass g hn hm (hu p.proj) (hv (f p.proj)) (Filter.EventuallyEq.of_eq h) p.2)

/-- A commuting square with differentiable base map and C¹ ambient map induces a continuous
map of intrinsic normal bundles. -/
theorem continuous_normalBundleMap
    [IsManifold J' 1 N']
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' m M' N')
    (hn : n ≠ 0) (hm : m ≠ 0) {u : M → M'} {v : N → N'}
    (hu : MDifferentiable I I' u) (hv : ContMDiff J J' 1 v)
    (h : v ∘ f = g ∘ u) :
    Continuous (f.normalBundleMap (K := K) (K' := K') g hn hm hu
      (hv.mdifferentiable (by simp)) h) := by
  let T : TotalSpace F ((f : M → N) *ᵖ (TangentSpace J)) →
      TotalSpace F' ((g : M' → N') *ᵖ (TangentSpace J')) := fun p =>
    ⟨u p.proj, tangentSpaceCast J' (v (f p.proj)) (g (u p.proj))
      (mfderiv J J' v (f p.proj) p.2)⟩
  have hT : Continuous T := by
    apply (inducing_pullbackTotalSpaceEmbedding F' (TangentSpace J')
      (g : M' → N')).continuous_iff.mpr
    have heq : pullbackTotalSpaceEmbedding g ∘ T =
        fun p => (u p.proj, tangentMap J J' v (Pullback.lift f p)) := by
      funext p
      -- Bundled tangent vectors have equal base points by the commuting square.
      -- After that equality, `tangentSpaceCast` is the identity identification.
      simp only [Function.comp_apply, pullbackTotalSpaceEmbedding, T, tangentMap,
        Pullback.lift]
      congr 1
      apply TotalSpace.ext (congrFun h p.proj).symm
      rfl
    rw [heq]
    exact (hu.continuous.comp (Pullback.continuous_proj F (TangentSpace J) f)).prodMk
      (hv.continuous_tangentMap le_rfl |>.comp (Pullback.continuous_lift F (TangentSpace J) f))
  rw [f.continuous_normalBundle_iff hn]
  convert (g.isQuotientMap_normalQuotientMap (K := K') hm).continuous.comp hT using 1
  funext p
  exact f.normalBundleMap_normalQuotientMap g hn hm hu _ h p

end Map

end TauCeti.SmoothEmbedding
