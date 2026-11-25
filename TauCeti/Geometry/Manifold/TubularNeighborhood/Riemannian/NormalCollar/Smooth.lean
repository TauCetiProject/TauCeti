/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.VectorBundle.UnitSection
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Neighborhood

/-!
# The smooth normal collar of a two-sided compact hypersurface

Let `f : M → N` be a smooth embedding of a compact manifold into a Riemannian manifold, of
codimension one, and `ν` a smooth field of unit normal vectors along `f`. The normal collar
`c_ν (x, t) = exp_{f x} (t ν x)` (`TauCeti.SmoothEmbedding.exists_isOpenEmbedding_normalCollar`)
is, for some `ε > 0`, a smooth diffeomorphism of `M × (-ε, ε)` onto an open neighbourhood `U` of
`f M`: `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalCollar` gives it as a
`PartialDiffeomorph` with source `M × (-ε, ε)`. Its inverse is smooth on `U`, so in particular the
collar coordinate `t : U → (-ε, ε)`, the second component of the inverse, is smooth.

The proof composes the smooth trivialization `(x, t) ↦ t • ν x` of the normal line bundle
(`TauCeti.VectorBundle.unitSectionDiffeomorph`) with smooth normal exponential coordinates around
`f M` (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`), whose source
contains every normal vector shorter than a positive smooth radius; `M` being compact, `ε` can be
taken below that radius everywhere.
-/

public section

open Bundle Manifold Set Topology Function

open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- **The smooth normal collar.** Let `f : M → N` be a smooth embedding of a compact manifold, of
codimension one, into a Riemannian manifold, and `ν` a smooth unit normal field along `f`. For some
`ε > 0` the normal collar `(x, t) ↦ exp_{f x} (t ν x)` is a smooth diffeomorphism of
`M × (-ε, ε)` onto an open subset of `N`: it is a `PartialDiffeomorph` with source
`M × (-ε, ε)`, and it sends `(x, 0)` to `f x`. -/
theorem exists_partialDiffeomorph_normalCollar
    [Nonempty M] (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hP : Module.finrank ℝ P = 1) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∀ u : (x : M) → ν x,
      ContMDiff I (I.prod 𝓘(ℝ, P)) ∞ (fun x ↦ TotalSpace.mk' P x (u x)) → (∀ x, ‖u x‖ = 1) →
      ∃ ε > 0, ∃ c : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (M × ℝ) N ∞,
        c.source = univ ×ˢ Ioo (-ε) ε ∧
        (∀ p ∈ c.source, c p = f.normalExp hn (TotalSpace.mk' P p.1 (p.2 • u p.1))) ∧
        ∀ x, c (x, 0) = f x := by
  intro hn ν u hu hu1
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let := f.isContMDiffRiemannianBundle_normalRiemannianMetric (m := ∞) hn (by simp) hdim
  let : IsContinuousRiemannianBundle P ν :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have : T2Space M := f.isEmbedding.t2Space
  obtain ⟨Φ, hzero, -, -, -, hΦ⟩ :=
    f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn (by simp) (by simp) hdim
      isOpen_univ (subset_univ _)
  obtain ⟨r, hr, -, hdisc⟩ := Φ.open_source.exists_contMDiffMap_norm_le_subset_bundle
    (I := I) (V := ν) (n := ⊤) hzero (continuous_const (y := (1 : ℝ)))
    (fun _ => zero_lt_one)
  -- On the compact `M`, the positive radius `r` is bounded below by some `ε > 0`.
  obtain ⟨x₀, -, hx₀⟩ :=
    isCompact_univ.exists_isMinOn univ_nonempty r.contMDiff.continuous.continuousOn
  set ε := r x₀
  have hε : 0 < ε := hr x₀
  let ψ := TauCeti.VectorBundle.unitSectionDiffeomorph I P ν hP hu hu1
  let S : Set (M × ℝ) := univ ×ˢ Ioo (-ε) ε
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hψS : ∀ p ∈ S, ψ p ∈ Φ.source := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    rw [TauCeti.VectorBundle.unitSectionDiffeomorph_apply]
    refine hdisc x (t • u x) ?_
    simpa [norm_smul, hu1] using (abs_lt.mpr ht).le.trans (hx₀ (mem_univ x))
  let c := (ψ.toPartialDiffeomorph.restrOpen S hS).trans Φ
  have hc : ∀ p, c p = Φ (ψ p) := fun p ↦ by
    simp only [c, PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_restrOpen,
      Diffeomorph.coe_toPartialDiffeomorph, comp_apply]
  have hsource : c.source = S := by
    simp only [c, PartialDiffeomorph.trans_source, PartialDiffeomorph.restrOpen_source,
      PartialDiffeomorph.coe_restrOpen, Diffeomorph.toPartialDiffeomorph_toPartialEquiv,
      Equiv.toPartialEquiv_source, univ_inter]
    exact inter_eq_left.mpr hψS
  refine ⟨ε, hε, c, hsource, fun p _ ↦ ?_, fun x ↦ ?_⟩
  · rw [hc, hΦ, TauCeti.VectorBundle.unitSectionDiffeomorph_apply]
  · rw [hc, hΦ, TauCeti.VectorBundle.unitSectionDiffeomorph_apply, zero_smul]
    exact f.normalExp_zeroSection hn x

end TauCeti.SmoothEmbedding
