/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
-- Use the complementary charts chosen by the normal-bundle atlas without exporting their data.
import all TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic

/-!
# Smooth quotient maps to intrinsic normal bundles

For an embedding in an arbitrary finite-dimensional manifold, taking the normal class of an
ambient tangent vector is smooth, with one derivative lost from the embedding. The projection
also admits smooth local right inverses. Consequently a map out of the normal bundle is smooth
exactly when its expression on ambient tangent representatives is smooth.

These results connect the quotient definition of the normal bundle with smooth constructions
on ambient tangent vectors, as used in tubular neighbourhoods. No Riemannian metric, compactness,
or boundarylessness is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle construction
  preceding Theorem 6.24.
-/

public noncomputable section

open Set Function Filter Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

/-- Taking the intrinsic normal class of an ambient tangent vector is `C^m` for a `C^n`
embedding when `m + 1 ≤ n`. Both bundles carry their usual bundle charts. -/
theorem contMDiff_normalQuotientMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, P)) m
      (f.normalQuotientMap (K := P) hn) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le ((le_add_right le_rfl).trans hm)⟩
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  let : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  intro p
  let d := normalChartData f hn hdim p.proj
  let e := d.trivialization f hn
  let a := (trivializationAt V (TangentSpace J) (f p.proj)).pullback f
  have he : MemTrivializationAtlas e := ⟨p.proj, rfl⟩
  have ha : MemTrivializationAtlas a := ⟨_, inferInstance, rfl⟩
  have hpe : f.normalQuotientMap (K := P) hn p ∈ e.source := by
    rw [e.mem_source, d.baseSet_trivialization, normalQuotientMap_apply]
    exact d.mem_baseSet
  have hpa : p ∈ a.source := by
    rw [a.mem_source]
    exact mem_baseSet_trivializationAt V (TangentSpace J) (f p.proj)
  -- In bundle charts the quotient is the smoothly varying complementary projection.
  apply (e.contMDiffAt_iff hpe).mpr
  refine ⟨by simpa only [normalQuotientMap_apply] using
    (contMDiffAt_proj ((f : M → N) *ᵖ (TangentSpace J))), ?_⟩
  have hq := f.contMDiffAt_inTangentCoordinates_quotientRangeCoordinate hm p.proj
    d.complement (d.invertible p.proj d.mem_baseSet)
  have hc := (hq.comp p (contMDiffAt_proj ((f : M → N) *ᵖ (TangentSpace J)))).clm_apply
    ((a.contMDiffOn.contMDiffAt (a.open_source.mem_nhds hpa)).snd)
  apply hc.congr_of_eventuallyEq
  have hbase : ∀ᶠ q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) in 𝓝 p,
      q.proj ∈ d.baseSet :=
    (FiberBundle.continuous_proj V ((f : M → N) *ᵖ (TangentSpace J))).continuousAt.preimage_mem_nhds
      (d.isOpen_baseSet.mem_nhds d.mem_baseSet)
  filter_upwards [hbase] with q hq
  rw [normalQuotientMap_apply]
  simp only [e, NormalChartData.trivialization]
  rw [normalSpaceTrivializationOfComplement_apply _ _ _ _ _ _ _ _ _ _ hq]
  simpa only [a, Trivialization.pullback_apply, Pullback.lift,
    Function.comp_apply] using
    f.normalSpaceEquivOfComplement_normalClass hn
      (d.subset_charts hq).1 (d.subset_charts hq).2 d.complement (d.invertible q.proj hq) q.2

/-- Near each intrinsic normal vector there is a `C^m` choice of ambient tangent
representatives. The right-inverse identity holds on a neighbourhood of that normal vector. -/
theorem exists_contMDiffOn_normalQuotientMap_rightInverse
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (p : TotalSpace P (fun x => f.NormalSpace x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ U : Set (TotalSpace P (fun x => f.NormalSpace x hn)), IsOpen U ∧ p ∈ U ∧
      ∃ s : TotalSpace P (fun x => f.NormalSpace x hn) →
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)),
        ContMDiffOn (I.prod 𝓘(𝕜, P)) (I.prod 𝓘(𝕜, V)) m s U ∧
          EqOn (f.normalQuotientMap hn ∘ s) _root_.id U := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le ((le_add_right le_rfl).trans hm)⟩
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  let d := normalChartData f hn hdim p.proj
  let e := d.trivialization f hn
  let a := (trivializationAt V (TangentSpace J) (f p.proj)).pullback f
  have he : MemTrivializationAtlas e := ⟨p.proj, rfl⟩
  have ha : MemTrivializationAtlas a := ⟨_, inferInstance, rfl⟩
  let s : TotalSpace P (fun x => f.NormalSpace x hn) →
      TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) := fun q =>
    ⟨q.proj, (trivializationAt V (TangentSpace J) (f p.proj)).symm
      (f q.proj) (d.complement (e q).2)⟩
  -- Lift a normal coordinate using the fixed complementary ambient tangent vector.
  let U : Set (TotalSpace P (fun x => f.NormalSpace x hn)) := {q | q.proj ∈ d.baseSet}
  have hU : IsOpen U := d.isOpen_baseSet.preimage (FiberBundle.continuous_proj P _)
  refine ⟨U, hU, d.mem_baseSet, s, ?_, ?_⟩
  · intro q hq
    apply ContMDiffAt.contMDiffWithinAt
    have hqe : q ∈ e.source := by
      rw [e.mem_source, d.baseSet_trivialization]
      exact hq
    apply (a.contMDiffAt_iff ?_).mpr
    · refine ⟨contMDiffAt_proj (fun x => f.NormalSpace x hn), ?_⟩
      have hc : ContMDiffAt (I.prod 𝓘(𝕜, P)) 𝓘(𝕜, V) m
          (fun q => d.complement (e q).2) q :=
        d.complement.contDiff.comp_contMDiffAt
          ((e.contMDiffOn (IB := I) (n := m) |>.contMDiffAt
            (e.open_source.mem_nhds hqe)).snd)
      apply hc.congr_of_eventuallyEq
      have hbase : ∀ᶠ y : TotalSpace P (fun x => f.NormalSpace x hn) in 𝓝 q,
          y.proj ∈ d.baseSet :=
        (FiberBundle.continuous_proj P _).continuousAt.preimage_mem_nhds
          (d.isOpen_baseSet.mem_nhds hq)
      filter_upwards [hbase] with y hy
      simp only [a, Trivialization.pullback_apply, s, Pullback.lift_mk]
      rw [(trivializationAt V (TangentSpace J) (f p.proj)).apply_mk_symm
        (d.subset_charts hy).2]
    · rw [a.mem_source]
      exact (d.subset_charts hq).2
  · intro q hq
    simp only [Function.comp_apply, normalQuotientMap_apply, s, id_eq]
    apply congrArg (TotalSpace.mk q.proj)
    have heq := normalSpaceTrivializationOfComplement_apply f hn p.proj
      d.baseSet d.isOpen_baseSet d.subset_charts d.complement d.invertible
      (d.continuous_coordinate_apply f hn) q hq
    have heq' : (e q).2 = f.normalSpaceEquivOfComplement hn
        (d.subset_charts hq).1 (d.subset_charts hq).2 d.complement
        (d.invertible q.proj hq) q.2 := congrArg Prod.snd heq
    rw [heq', ← f.normalSpaceEquivOfComplement_symm_apply hn
      (d.subset_charts hq).1 (d.subset_charts hq).2 d.complement (d.invertible q.proj hq),
      ContinuousLinearEquiv.symm_apply_apply]

/-- A map out of an intrinsic normal bundle is `C^m` exactly when it is `C^m` on
ambient tangent representatives. This is the smooth descent property of the normal quotient. -/
theorem contMDiff_normalBundle_iff
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace X] [ChartedSpace H' X]
    (q : TotalSpace P (fun x => f.NormalSpace x hn) → X) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(𝕜, P)) I' m q ↔
      ContMDiff (I.prod 𝓘(𝕜, V)) I' m (q ∘ f.normalQuotientMap hn) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  constructor
  · intro h
    exact h.comp (f.contMDiff_normalQuotientMap hn hm hdim)
  · intro h p
    obtain ⟨U, hU, hp, s, hs, hright⟩ :=
      f.exists_contMDiffOn_normalQuotientMap_rightInverse hn hm hdim p
    have hs' := hs.contMDiffAt (hU.mem_nhds hp)
    exact ((h (s p)).comp p hs').congr_of_eventuallyEq
      ((hright.eventuallyEq_of_mem (hU.mem_nhds hp)).fun_comp q).symm

end TauCeti.SmoothEmbedding
