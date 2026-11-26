/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.FixedPoints
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Noncompact

import TauCeti.Geometry.Manifold.Riemannian.Invariant

/-!
# Equivariant tubular neighbourhoods of submanifolds of fixed points

Let a group `K` act on a Riemannian manifold `N` by smooth maps whose differentials preserve the
metric, and let `f : M → N` be a smooth embedding of a submanifold of fixed points:
`k • f x = f x` for every `k` and `x`. No topology or Lie group structure on `K` is used. At each
point `f x` the differentials of the action fix the tangent space of the submanifold, so `K` acts
linearly on the normal space `T_(f x) N / df_x (T_x M)` by the isotropy representation
`TauCeti.SmoothEmbedding.fixedNormalRepresentation`. This file shows that the normal exponential
tubular neighbourhood of `f` is equivariant for this action.

* **Orthogonal representatives are equivariant.** The differential of `k` at `f x` is a linear
  isometry fixing the tangent space of the submanifold, so it preserves its orthogonal complement.
  Hence the orthogonal representative of `k • ν` is `d(k •)_(f x)` applied to the orthogonal
  representative of `ν`
  (`TauCeti.SmoothEmbedding.normalRepresentative_fixedNormalRepresentation`), and `K` acts by
  isometries of the induced metric on the normal spaces
  (`TauCeti.SmoothEmbedding.normalRiemannianMetric_inner_fixedNormalRepresentation`).
* **The normal exponential is equivariant.** Isometries intertwine Riemannian exponential maps, so
  `exp^⊥(k • ν) = k • exp^⊥(ν)` for every normal vector `ν`
  (`TauCeti.SmoothEmbedding.normalExp_fixedNormalRepresentation`).
* **Equivariant tubular neighbourhood.** There is a positive smooth radius `r` on `M` such that the
  normal exponential is a diffeomorphism from the open disc bundle `{ν | ‖ν‖ < r}` onto an open
  neighbourhood of `f(M)` inside any prescribed open neighbourhood
  (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_norm_lt_subset`). Since `K` acts on
  the normal spaces by isometries, the disc bundle is invariant, and so is its image; the
  diffeomorphism and its inverse intertwine the linear action of `K` on the normal bundle with its
  action on `N`
  (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_fixedNormalRepresentation`).
  Neither compactness of `M` or `K`, nor closedness of `f(M)`, nor completeness of the metric is
  used.
* **Compact groups.** A compact Lie group acting smoothly preserves a metric obtained by averaging
  (`TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`). Hence for a smooth action of a
  compact Lie group, with no metric given, a neighbourhood of a submanifold of fixed points is
  equivariantly diffeomorphic to a neighbourhood of the zero section of its normal bundle, with
  the linear isotropy action
  (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_fixedNormalRepresentation_of_compactSpace`).

So near a submanifold of fixed points the action of a group of isometries, or of a compact Lie
group, is its linear isotropy representation on the normal bundle. This applies to the fixed
components of torus actions: the components of the fixed set of a group of isometries are embedded
submanifolds (`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`).

## Main results

* `TauCeti.SmoothEmbedding.normalRepresentative_fixedNormalRepresentation`: orthogonal normal
  representatives are equivariant.
* `TauCeti.SmoothEmbedding.normalRiemannianMetric_inner_fixedNormalRepresentation`: the isotropy
  representation preserves the induced metric on the normal spaces.
* `TauCeti.SmoothEmbedding.normalExp_fixedNormalRepresentation`: the normal exponential is
  equivariant.
* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_fixedNormalRepresentation`: the
  equivariant tubular neighbourhood theorem for a group of isometries.
* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_fixedNormalRepresentation_of_compactSpace`:
  the equivariant tubular neighbourhood theorem for a smooth action of a compact Lie group.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press, 1972,
  Chapter VI, §2 (equivariant tubular neighbourhoods by the exponential map of an invariant
  metric).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed points of a group of symplectic isometries).
-/

public noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

section Normal

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {n : ℕ∞ω} {K : Type*} [Group K] [MulAction K N]
  (f : SmoothEmbedding I J n M N) (hf : ∀ (k : K) (x : M), k • f x = f x)

include hf in
/-- **Orthogonal normal representatives are equivariant.** On a submanifold of fixed points of a
group whose differentials at `f x` preserve the metric, the orthogonal representative of `k • ν`
is the image under `d(k •)_(f x)` of the orthogonal representative of `ν`. -/
theorem normalRepresentative_fixedNormalRepresentation (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (hK : ∀ (k : K) (u w : TangentSpace J (f x)),
      inner ℝ (mfderiv J J (k • ·) (f x) u) (mfderiv J J (k • ·) (f x) w) = inner ℝ u w)
    (k : K) (ν : f.isImmersion.NormalSpace x hn) :
    f.normalRepresentative x hn (f.fixedNormalRepresentation hf x hn hd k ν) =
      mfderiv J J (fun y : N ↦ k • y) (f x) (f.normalRepresentative x hn ν) := by
  refine (f.normalRepresentative_eq_iff x hn _ _).2 ⟨?_, ?_⟩
  · -- `d(k •)` fixes the tangent space and preserves the metric, so it preserves the complement.
    refine (Submodule.mem_orthogonal _ _).2 fun u hu ↦ ?_
    rw [← f.mfderiv_smul_eq_self_of_mem_tangentRange hf (hd k) hn hu]
    exact (inner_mfderiv_smul_of_smul_eq (hf k x) (hK k) _ _).trans
      (Submodule.inner_right_of_mem_orthogonal hu (f.normalRepresentative_mem_orthogonal x hn ν))
  · rw [← fixedNormalRepresentation_normalClass, normalClass_normalRepresentative]

include hf in
/-- **The isotropy representation acts by isometries on the normal spaces.** On a submanifold of
fixed points of a group whose differentials at `f x` preserve the metric, the representation of
`K` on the normal space at `x` preserves the metric induced by orthogonal representatives. -/
theorem normalRiemannianMetric_inner_fixedNormalRepresentation (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (hK : ∀ (k : K) (u w : TangentSpace J (f x)),
      inner ℝ (mfderiv J J (k • ·) (f x) u) (mfderiv J J (k • ·) (f x) w) = inner ℝ u w)
    (k : K) (ν μ : f.isImmersion.NormalSpace x hn) :
    (f.normalRiemannianMetric hn).inner x (f.fixedNormalRepresentation hf x hn hd k ν)
        (f.fixedNormalRepresentation hf x hn hd k μ) =
      (f.normalRiemannianMetric hn).inner x ν μ := by
  rw [normalRiemannianMetric_inner, normalRiemannianMetric_inner,
    f.normalRepresentative_fixedNormalRepresentation hf x hn hd hK,
    f.normalRepresentative_fixedNormalRepresentation hf x hn hd hK]
  exact inner_mfderiv_smul_of_smul_eq (hf k x) (hK k) _ _

variable [IsManifold J ∞ N] [J.Boundaryless] [T2Space N]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)] [ContMDiffConstSMul J ∞ K N]

include hf in
/-- **The normal exponential is equivariant.** For a group acting on `N` by smooth maps preserving
the metric, the normal exponential of a submanifold of fixed points intertwines the isotropy
representation on the normal spaces with the action on `N`: `exp^⊥(k • ν) = k • exp^⊥(ν)`. -/
theorem normalExp_fixedNormalRepresentation {P : Type*} (hn : n ≠ 0)
    (hK : ∀ (k : K) (y : N) (u w : TangentSpace J y),
      inner ℝ (mfderiv J J (k • ·) y u) (mfderiv J J (k • ·) y w) = inner ℝ u w)
    (x : M) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (k : K)
    (ν : f.isImmersion.NormalSpace x hn) :
    f.normalExp (P := P) hn ⟨x, f.fixedNormalRepresentation hf x hn hd k ν⟩ =
      k • f.normalExp (P := P) hn ⟨x, ν⟩ := by
  rw [normalExp_apply, normalExp_apply,
    f.normalRepresentative_fixedNormalRepresentation hf x hn hd (fun g ↦ hK g (f x)) k ν]
  exact riemannianExp_mfderiv_smul_of_smul_eq (hK k) (hf k x) _

end Normal

section Tubular

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]
  {K : Type*} [Group K] [MulAction K N] [ContMDiffConstSMul J ∞ K N]

/-- **Equivariant tubular neighbourhood of a submanifold of fixed points.** Let a group `K` act on
a Riemannian manifold `N` by smooth maps preserving the metric, and let `f` be a smooth embedding
of a submanifold of fixed points. Then there are a positive smooth radius `r` on `M` and a partial
diffeomorphism `Φ`, equal to the normal exponential, from the open disc bundle
`{ν | ‖ν‖ < r}` of the normal bundle, for the metric induced by orthogonal representatives, onto
an open subset of any prescribed open neighbourhood `O` of `f(M)`. Its source and target are
invariant under `K`, acting on the normal bundle by the isotropy representation `ρ`, and `Φ`
intertwines the two actions: `Φ (k • ν) = k • Φ ν`, and `Φ⁻¹ (k • y) = k • Φ⁻¹ y` on the target.
Nonemptiness of `M` is used only to define the inverse away from the target. -/
theorem exists_partialDiffeomorph_normalExp_fixedNormalRepresentation [Nonempty M]
    (f : SmoothEmbedding I J ∞ M N) (hf : ∀ (k : K) (x : M), k • f x = f x)
    (hK : ∀ (k : K) (y : N) (u w : TangentSpace J y),
      inner ℝ (mfderiv J J (k • ·) y u) (mfderiv J J (k • ·) y w) = inner ℝ u w)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.isImmersion.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    let ρ : K → TotalSpace P ν → TotalSpace P ν := fun k p ↦
      ⟨p.proj, f.fixedNormalRepresentation hf p.proj hn
        (fun g ↦ ContMDiffConstSMul.mdifferentiable_const_smul (n := ∞) (by simp) g _) k p.snd⟩
    ∃ (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) J (TotalSpace P ν) N ∞)
        (r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯),
      ⇑Φ = f.normalExp hn ∧ (∀ x, 0 < r x) ∧
      Φ.source = {p : TotalSpace P ν | ‖p.snd‖ < r p.proj} ∧ Φ.target ⊆ O ∧
      (∀ k p, ρ k p ∈ Φ.source ↔ p ∈ Φ.source) ∧ (∀ (k : K) y, k • y ∈ Φ.target ↔ y ∈ Φ.target) ∧
      (∀ k p, Φ (ρ k p) = k • Φ p) ∧
      ∀ (k : K), ∀ y ∈ Φ.target, Φ.symm (k • y) = ρ k (Φ.symm y) := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let ν : M → Type _ := fun x ↦ f.isImmersion.NormalSpace x hn
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x ↦ inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x ↦ inferInstance
  let ρ : K → TotalSpace P ν → TotalSpace P ν := fun k p ↦
    ⟨p.proj, f.fixedNormalRepresentation hf p.proj hn
      (fun g ↦ ContMDiffConstSMul.mdifferentiable_const_smul (n := ∞) (by simp) g _) k p.snd⟩
  obtain ⟨Φ, r, hΦ, hr, hsource, hΦO⟩ := f.exists_partialDiffeomorph_normalExp_norm_lt_subset hdim
    hO hfO
  -- The isotropy representation preserves the fibre norms, so the disc bundle is invariant.
  have hnorm (k : K) (p : TotalSpace P ν) : ‖(ρ k p).snd‖ = ‖p.snd‖ := by
    have h := f.normalRiemannianMetric_inner_fixedNormalRepresentation hf p.proj hn
      (fun g ↦ ContMDiffConstSMul.mdifferentiable_const_smul (n := ∞) (by simp) g _)
      (fun g ↦ hK g (f p.proj)) k p.snd p.snd
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    exact h
  have hsmul_source (k : K) (p : TotalSpace P ν) : ρ k p ∈ Φ.source ↔ p ∈ Φ.source := by
    rw [hsource]
    exact iff_of_eq (congrArg (· < r p.proj) (hnorm k p))
  have hequiv (k : K) (p : TotalSpace P ν) : Φ (ρ k p) = k • Φ p := by
    rw [hΦ]
    exact f.normalExp_fixedNormalRepresentation hf hn hK p.proj _ k p.snd
  -- The target is the image of the invariant source, hence invariant.
  have hsmul_target (k : K) {y : N} (hy : y ∈ Φ.target) : k • y ∈ Φ.target := by
    rw [← Φ.toPartialEquiv.image_source_eq_target] at hy ⊢
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨ρ k p, (hsmul_source k p).2 hp, hequiv k p⟩
  refine ⟨Φ, r, hΦ, hr, hsource, hΦO, hsmul_source,
    fun k y ↦ ⟨fun hy ↦ by simpa using hsmul_target k⁻¹ hy, hsmul_target k⟩, hequiv,
    fun k y hy ↦ ?_⟩
  -- Apply the inverse to `Φ (k • p) = k • Φ p = k • y`, with `p = Φ⁻¹ y`.
  have h : Φ (ρ k (Φ.symm y)) = k • y := (hequiv k _).trans (congrArg (k • ·) (Φ.right_inv hy))
  rw [← h]
  exact Φ.left_inv ((hsmul_source k _).2 (Φ.map_target hy))

end Tubular

section Compact

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  {EK HK K : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [TopologicalSpace HK]
  {IK : ModelWithCorners ℝ EK HK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [T2Space K] [ChartedSpace HK K] [IsManifold IK ∞ K]
  [MulAction K N] [ContMDiffSMul IK J ∞ K N]

variable (IK) in
/-- **Equivariant tubular neighbourhood for a compact group.** Let a compact Lie group `K` act
smoothly on a second countable manifold `N`, and let `f` be a smooth embedding of a submanifold of
fixed points. Then a neighbourhood of `f(M)` inside any prescribed open neighbourhood `O` is
equivariantly diffeomorphic to a neighbourhood of the zero section of the normal bundle, on which
`K` acts linearly by the isotropy representation `ρ`: there is a partial diffeomorphism `Φ` whose
source contains the zero section and is `K`-invariant, sending the zero normal vector at `x` to
`f x`, with `K`-invariant target in `O`, and intertwining `ρ` with the action on `N`, as does its
inverse. No metric is given: `Φ` is the normal exponential of a `K`-invariant metric obtained by
averaging. Nonemptiness of `M` is used only to define the inverse away from the target. -/
theorem exists_partialDiffeomorph_fixedNormalRepresentation_of_compactSpace [Nonempty M]
    (f : SmoothEmbedding I J ∞ M N) (hf : ∀ (k : K) (x : M), k • f x = f x)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.isImmersion.NormalSpace x hn
    let ρ : K → TotalSpace P ν → TotalSpace P ν := fun k p ↦
      ⟨p.proj, f.fixedNormalRepresentation hf p.proj hn
        (fun g ↦ ContMDiffSMul.mdifferentiable_const_smul (I := IK) (n := ∞) (by simp) g _) k
        p.snd⟩
    ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) J (TotalSpace P ν) N ∞,
      (∀ x, zeroSection P ν x ∈ Φ.source ∧ Φ (zeroSection P ν x) = f x) ∧ Φ.target ⊆ O ∧
      (∀ k p, ρ k p ∈ Φ.source ↔ p ∈ Φ.source) ∧
      (∀ (k : K) y, k • y ∈ Φ.target ↔ y ∈ Φ.target) ∧ (∀ k p, Φ (ρ k p) = k • Φ p) ∧
      ∀ (k : K), ∀ y ∈ Φ.target, Φ.symm (k • y) = ρ k (Φ.symm y) := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let ν : M → Type _ := fun x ↦ f.isImmersion.NormalSpace x hn
  have : ContMDiffConstSMul J ∞ K N := ContMDiffSMul.contMDiffConstSMul IK
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  -- Prove it for a `K`-invariant smooth metric, obtained by averaging.
  refine of_forall_riemannianBundle_inner_mfderiv (I := J) (M := N) IK K fun hK ↦ ?_
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x ↦ inferInstance
  obtain ⟨Φ, r, hΦ, hr, hsource, htarget, hsrc, htgt, hequiv, hsymm⟩ :=
    f.exists_partialDiffeomorph_normalExp_fixedNormalRepresentation hf hK hdim hO hfO
  -- The zero section lies in the open disc bundle of positive radius.
  refine ⟨Φ, fun x ↦ ⟨?_, ?_⟩, htarget, hsrc, htgt, hequiv, hsymm⟩
  · rw [hsource]
    exact (norm_zero (E := ν x)).trans_lt (hr x)
  · rw [hΦ]
    exact f.normalExp_zeroSection hn x

end Compact

end TauCeti.SmoothEmbedding
