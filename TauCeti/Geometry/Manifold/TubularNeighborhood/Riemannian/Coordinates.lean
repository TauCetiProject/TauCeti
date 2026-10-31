/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Differential
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section
public import TauCeti.Topology.FiberBundle.Countable
public import TauCeti.Topology.FiberBundle.Separation
public import Mathlib.Geometry.Manifold.Metrizable
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Neighborhood

/-!
# Smooth normal-exponential coordinates

The normal exponential of an embedding into a Riemannian manifold is a local diffeomorphism
at every zero normal vector. These local inverses assemble to a single smooth inverse on an
open neighbourhood of the entire zero section. The ambient neighbourhood can be kept inside
any prescribed open neighbourhood of the embedded image. Neither compactness nor closedness
of the image nor a global normal framing is required.

Smooth radial compression also identifies the whole intrinsic normal bundle with an open
ambient neighbourhood, fixing its zero section. An auxiliary smooth fibre metric is chosen only
for compression; the normal exponential uses the given ambient Riemannian metric.

The construction uses the previously computed invertible differential of the normal exponential,
and `IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section` for global injectivity and
smoothness of the inverse.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set Function Topology TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]
  {n m : ℕ∞ω} [ENat.LEInfty m] [IsManifold I (m + 1) M]

/-- The normal exponential is a `C^m` local diffeomorphism at every zero normal vector,
for a `C^n` embedding with `1 ≤ m` and `m + 1 ≤ n`. -/
theorem isLocalDiffeomorphAt_normalExp_zeroSection
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) (x : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J m (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.NormalSpace x hn) x) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have : IsManifold I (1 + 1) M := .of_le (n := m + 1) h2m
  have hminfty : m + 1 ≤ ∞ := by
    lift m to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
    exact_mod_cast le_top
  have : IsManifold J (m + 1) N := .of_le (n := ∞) hminfty
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  have : IsManifold I m M := .of_le (n := m + 1) le_self_add
  obtain ⟨e, he⟩ := f.isInvertible_mfderiv_normalExp_zeroSection hn
    (h2m.trans hm) hdim x
  exact isLocalDiffeomorphAt_of_mfderiv_eq (f.contMDiffOn_normalExp hn hm hdim)
    (f.isOpen_normalExpDomain hn hdim) (f.zeroSection_mem_normalExpDomain hn x)
    BoundarylessManifold.isInteriorPoint hm1 he

/-- Normal exponential coordinates around an entire embedded submanifold have a single `C^m`
inverse. Their source lies in the natural exponential domain, contains the whole zero section,
and their target lies inside the prescribed open neighbourhood of the image.
Nonemptiness is used only for values of the partial inverse outside its target. -/
theorem exists_partialDiffeomorph_normalExp_subset [SecondCountableTopology N] [Nonempty M]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) J
        (TotalSpace P (fun x ↦ f.NormalSpace x hn)) N m,
      (∀ x, zeroSection P (fun x ↦ f.NormalSpace x hn) x ∈ Φ.source) ∧
      Φ.source ⊆ f.normalExpDomain hn ∧ Φ.target ⊆ O ∧
      Φ.target = f.normalExp hn '' Φ.source ∧ ⇑Φ = f.normalExp hn := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space M := f.isEmbedding.t2Space
  have : SecondCountableTopology M := f.isEmbedding.isInducing.secondCountableTopology
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  have : LocallyCompactSpace (ModelProd H P) := (I.prod 𝓘(ℝ, P)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace P (fun x ↦ f.NormalSpace x hn)) :=
    ChartedSpace.locallyCompactSpace (ModelProd H P) _
  have : MetrizableSpace N := Manifold.metrizableSpace J N
  have : MetrizableSpace (TotalSpace P (fun x ↦ f.NormalSpace x hn)) :=
    Manifold.metrizableSpace (I.prod 𝓘(ℝ, P)) _
  have : Nonempty (TotalSpace P (fun x ↦ f.NormalSpace x hn)) :=
    Nonempty.map (zeroSection P (fun x ↦ f.NormalSpace x hn)) inferInstance
  let A := f.normalExp (P := P) hn
  let U := {p | IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J m A p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun _ hp => hp.eventually
  let S := (U ∩ f.normalExpDomain (P := P) hn) ∩ A ⁻¹' O
  have hS : IsOpen S :=
    ContinuousOn.isOpen_inter_preimage
      ((f.contMDiffOn_normalExp hn hm hdim).continuousOn.mono inter_subset_right)
      (hU.inter (f.isOpen_normalExpDomain hn hdim)) hO
  have hzero : range (zeroSection P (fun x ↦ f.NormalSpace x hn)) ⊆ S := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨f.isLocalDiffeomorphAt_normalExp_zeroSection hn hm hm1 hdim x,
      f.zeroSection_mem_normalExpDomain hn x⟩, by simpa [A] using hfO (mem_range_self x)⟩
  have hlocal : IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, P)) J m A S := fun p => p.property.1.1
  have hcore : A ∘ zeroSection P (fun x ↦ f.NormalSpace x hn) = f :=
    funext (f.normalExp_zeroSection hn)
  obtain ⟨Φ, hzeroΦ, hΦS, htarget, hΦ⟩ := hlocal.exists_partialDiffeomorph_near_section
    hS hzero (_root_.Bundle.Trivialization.continuous_zeroSection ℝ)
    (π P (fun x ↦ f.NormalSpace x hn))
    (FiberBundle.continuous_proj _ _) (fun _ => rfl) (hcore ▸ f.isEmbedding.isInducing)
  refine ⟨Φ, fun x => hzeroΦ (mem_range_self x), fun p hp => (hΦS hp).1.2, ?_,
    htarget, hΦ⟩
  rw [htarget]
  rintro _ ⟨p, hp, rfl⟩
  exact (hΦS hp).2

omit [ENat.LEInfty m] [IsManifold I (m + 1) M] in
/-- **Smooth Riemannian tubular neighbourhood theorem.** The entire intrinsic normal bundle
of a smooth embedding is diffeomorphic to an open neighbourhood inside any prescribed open
neighbourhood of its image. The zero section is sent to the original embedding. Neither
compactness nor closedness of the embedded image nor completeness of the ambient metric
is required. -/
theorem exists_diffeomorph_normalBundle_riemannian_subset
    [IsManifold I ∞ M] [SecondCountableTopology N]
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧
      ∃ Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W,
        ∀ x, (Φ (zeroSection P (fun x ↦ f.NormalSpace x hn) x) : N) = f x := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  cases isEmpty_or_nonempty M with
  | inl hM =>
    let W : TopologicalSpace.Opens N := ⊥
    have : IsEmpty (TotalSpace P (fun x ↦ f.NormalSpace x hn)) := ⟨fun p => hM.false p.proj⟩
    have : IsEmpty W := ⟨fun y => y.property⟩
    let Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W :=
      { Equiv.equivOfIsEmpty _ _ with
        contMDiff_toFun := fun p => (hM.false p.proj).elim
        contMDiff_invFun := fun y => (IsEmpty.false y).elim }
    exact ⟨W, empty_subset O, Φ, fun x => (hM.false x).elim⟩
  | inr hM =>
    let := hM
    have : T2Space M := f.isEmbedding.t2Space
    have : SecondCountableTopology M := f.isEmbedding.isInducing.secondCountableTopology
    have : LocallyCompactSpace H := I.locallyCompactSpace
    have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    obtain ⟨Ψ, hzero, -, htarget, -, hΨ⟩ :=
      f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn (by simp) (by simp) hdim hO hfO
    -- A smooth auxiliary metric provides fibrewise radial compression, without changing
    -- the quotient topology or the complementary-coordinate atlas of the normal bundle.
    obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := P)
      (E := fun x ↦ f.NormalSpace x hn)
    -- Name the family so instance search can infer it before selecting a particular fibre.
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    let : RiemannianBundle ν := ⟨g.toRiemannianMetric⟩
    let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
    let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
    let : IsContMDiffRiemannianBundle I ∞ P ν := Bundle.instIsContMDiffRiemannianBundle g
    let : IsContinuousRiemannianBundle P ν :=
      Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    obtain ⟨r, hr, -, hdisc⟩ := Ψ.open_source.exists_contMDiffMap_norm_le_subset_bundle
      (I := I) (V := ν) (n := ⊤) hzero (continuous_const (y := (1 : ℝ))) (fun _ => zero_lt_one)
    let R := vectorBundleRadialPartialDiffeomorphOfRadius (F := P) (V := ν) r.contMDiff hr
    have hRsource : R.source = univ := vectorBundleRadialPartialDiffeomorphOfRadius_source _ _
    have hRtarget : R.target ⊆ Ψ.source := by
      rw [vectorBundleRadialPartialDiffeomorphOfRadius_target]
      exact fun p hp => hdisc p.proj p.2 hp.le
    have hsource : (R.trans Ψ).source = univ := by
      have hpreimage : R ⁻¹' Ψ.source = univ :=
        eq_univ_of_forall fun p => hRtarget (R.map_source (hRsource ▸ mem_univ p))
      simp [hRsource, hpreimage]
    let Θ := R.trans Ψ
    have hforward : ContMDiff (I.prod 𝓘(ℝ, P)) J ∞ Θ := by
      rw [← contMDiffOn_univ, ← hsource]
      exact Θ.contMDiffOn
    let W : TopologicalSpace.Opens N := ⟨Θ.target, Θ.open_target⟩
    let Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W :=
      { toFun := fun p => ⟨Θ p, Θ.toPartialEquiv.map_source (hsource ▸ mem_univ p)⟩
        invFun := fun y => Θ.toPartialEquiv.symm y
        left_inv := fun p => Θ.toPartialEquiv.left_inv (hsource ▸ mem_univ p)
        right_inv := fun y => Subtype.ext (Θ.toPartialEquiv.right_inv y.property)
        contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff W _).mp hforward
        contMDiff_invFun := Θ.contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val
          (fun y => y.property) }
    refine ⟨W, fun y hy => htarget hy.1, Φ, ?_⟩
    intro x
    have hΦ (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) : (Φ p : N) = Ψ (R p) := rfl
    have hRzero : R (zeroSection P (fun x ↦ f.NormalSpace x hn) x) =
        zeroSection P (fun x ↦ f.NormalSpace x hn) x := by
      simp only [R, vectorBundleRadialPartialDiffeomorphOfRadius_apply,
        TotalSpace.radialMap_zeroSection, vectorBundleScalarDiffeomorph_apply]
      exact congrArg (fun v : ν x => (⟨x, v⟩ : TotalSpace P ν)) (smul_zero (r x))
    rw [hΦ, hRzero]
    exact (congrFun hΨ _).trans (f.normalExp_zeroSection hn x)

end TauCeti.SmoothEmbedding
