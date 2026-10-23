/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Basic

/-!
# The normal exponential on a fixed fibre

On a fixed orthogonal normal space, the normal exponential is smooth on its natural domain.
Its differential at zero is the inclusion into the ambient tangent space. Moreover, it embeds
an open neighbourhood of zero into the ambient manifold. These are the vertical regularity
and nondegeneracy properties used in the tubular neighbourhood theorem for general ambient
manifolds. They do not assert injectivity between different normal fibres.

The statements use orthogonal representatives of the intrinsic quotient normal space, and
therefore use its existing Riemannian norm without choosing a norm on the quotient bundle.
The local embedding is obtained by restricting the ambient exponential's local inverse.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.

The construction uses `Manifold.isLocalDiffeomorphAt_riemannianExp_zero` and
`SmoothEmbedding.normalExp_normalClass`.
-/

public noncomputable section

open Bundle Manifold Set Function Topology
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.SmoothEmbedding

variable {E V H G M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold J ∞ N] [J.Boundaryless] [T2Space N]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]
  {n : ℕ∞ω}

/-- The natural domain in a fixed orthogonal normal fibre is open. -/
theorem isOpen_normalExpDomain_fiber
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    IsOpen {v : (f.tangentRange x hn)ᗮ |
      (⟨x, f.normalClass x hn v⟩ : TotalSpace P (fun y ↦ f.NormalSpace y hn)) ∈
        f.normalExpDomain hn} := by
  rw [normalExpDomain_fiber_eq_preimage]
  exact (Manifold.isOpen_expDomain (I := J) (f x)).preimage continuous_subtype_val

/-- The normal exponential is smooth in the normal vector at each fixed base point throughout
its natural domain. No smoothness of a choice of normal representatives in the base is assumed. -/
theorem contMDiffOn_normalExp_fiber
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    ContMDiffOn 𝓘(ℝ, (f.tangentRange x hn)ᗮ) J ∞
      (fun v : (f.tangentRange x hn)ᗮ ↦
        f.normalExp (P := P) hn ⟨x, f.normalClass x hn v⟩)
      {v | (⟨x, f.normalClass x hn v⟩ : TotalSpace P (fun y ↦ f.NormalSpace y hn)) ∈
        f.normalExpDomain hn} := by
  simp_rw [normalExp_normalClass_orthogonal]
  rw [normalExpDomain_fiber_eq_preimage]
  exact (Manifold.contMDiffOn_riemannianExp (I := J) (f x)).comp
    ((f.tangentRange x hn)ᗮ.subtypeL.contDiff.contMDiff.contMDiffOn)
    (fun _ hv ↦ hv)

/-- The vertical differential of the normal exponential along its zero section is the
inclusion of the orthogonal normal space into the ambient tangent space. -/
-- Not a simp lemma: the dependent target tangent space contains the coercion of the
-- normal-space zero, which simp normalizes before this computation rule can match.
theorem mfderiv_normalExp_fiber_zero_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M)
    (v : TangentSpace 𝓘(ℝ, (f.tangentRange x hn)ᗮ) (0 : (f.tangentRange x hn)ᗮ)) :
    mfderiv 𝓘(ℝ, (f.tangentRange x hn)ᗮ) J
      (fun w : (f.tangentRange x hn)ᗮ ↦
        f.normalExp (P := P) hn ⟨x, f.normalClass x hn w⟩) 0 v =
      ((NormedSpace.fromTangentSpace (0 : (f.tangentRange x hn)ᗮ)) v :
        TangentSpace J (f x)) := by
  have hfun : (fun w : (f.tangentRange x hn)ᗮ ↦
      f.normalExp (P := P) hn ⟨x, f.normalClass x hn w⟩) =
      Manifold.riemannianExp J N (f x) ∘ (f.tangentRange x hn)ᗮ.subtypeL :=
    funext fun v ↦ f.normalExp_normalClass_orthogonal hn x v
  rw [hfun, mfderiv_comp (I' := 𝓘(ℝ, TangentSpace J (f x)))]
  · simp only [ContinuousLinearMap.mfderiv_eq]
    exact Manifold.mfderiv_riemannianExp_apply_zero (I := J) (f x)
      ((NormedSpace.fromTangentSpace (0 : (f.tangentRange x hn)ᗮ)) v)
  · simpa only [map_zero] using
      (Manifold.contMDiffAt_riemannianExp (I := J)
        (Manifold.zero_mem_expDomain (f x))).mdifferentiableAt (by simp)
  · exact (f.tangentRange x hn)ᗮ.subtypeL.mdifferentiableAt

/-- Each fixed normal fibre has an open neighbourhood of zero on which the normal exponential
is an embedding. The neighbourhood lies in the natural normal-exponential domain. Together
with `contMDiffOn_normalExp_fiber`, this supplies a smooth map that is a topological embedding
of an open neighbourhood of zero. -/
theorem exists_isEmbedding_normalExp_fiber
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    ∃ U : TopologicalSpace.Opens ((f.tangentRange x hn)ᗮ), (0 : (f.tangentRange x hn)ᗮ) ∈ U ∧
      (∀ v ∈ U, (⟨x, f.normalClass x hn v⟩ : TotalSpace P (fun y ↦ f.NormalSpace y hn)) ∈
        f.normalExpDomain hn) ∧
      IsEmbedding (fun v : U ↦
        f.normalExp (P := P) hn ⟨x, f.normalClass x hn (v : (f.tangentRange x hn)ᗮ)⟩) := by
  have hd := Manifold.isLocalDiffeomorphAt_riemannianExp_zero (I := J) (f x)
  let S := hd.localInverse.target ∩
    (Manifold.expDomain J N (f x) ∩
      Manifold.riemannianExp J N (f x) ⁻¹' hd.localInverse.source)
  have hS : IsOpen S := hd.localInverse.open_target.inter
    ((Manifold.continuousOn_riemannianExp (I := J) (f x)).isOpen_inter_preimage
      (Manifold.isOpen_expDomain (I := J) (f x)) hd.localInverse.open_source)
  let U : TopologicalSpace.Opens ((f.tangentRange x hn)ᗮ) :=
    ⟨Subtype.val ⁻¹' S, hS.preimage continuous_subtype_val⟩
  let F : U → hd.localInverse.source := fun v ↦
    ⟨Manifold.riemannianExp J N (f x) (v.val : TangentSpace J (f x)), v.property.2.2⟩
  have hF : Continuous F :=
    ((Manifold.continuousOn_riemannianExp (I := J) (f x)).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun v ↦ v.property.2.1)).subtype_mk _
  have hcomp : hd.localInverse.source.domRestrict hd.localInverse ∘ F =
      (fun v : U ↦ (v.val : TangentSpace J (f x))) := by
    funext v
    simp only [Function.comp_apply, Set.domRestrict_apply]
    exact hd.localInverse_left_inv v.property.1
  have hemb : IsEmbedding F := .of_comp hF
    hd.contMDiffOn_localInverse.continuousOn.domRestrict
    (by
      rw [hcomp]
      exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
  refine ⟨U, ⟨hd.localInverse_mem_target, Manifold.zero_mem_expDomain (f x), ?_⟩, ?_, ?_⟩
  · simpa only [mem_preimage, Submodule.coe_zero, Manifold.riemannianExp_zero] using
      hd.localInverse_mem_source
  · intro v hv
    exact (Set.ext_iff.mp (normalExpDomain_fiber_eq_preimage (P := P) f hn x) v).mpr hv.2.1
  · simp_rw [normalExp_normalClass_orthogonal]
    exact IsEmbedding.subtypeVal.comp hemb

end TauCeti.SmoothEmbedding
