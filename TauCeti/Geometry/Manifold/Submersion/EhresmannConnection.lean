/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Ehresmann connections on submersions

An **Ehresmann connection** on a map `f : P → B` is a distribution `D` on `P`, the *horizontal*
distribution, which is complementary to the vertical space `ker (df_x)` at every point `x` of
a differentiable map with surjective derivative, and is a `C^n` distribution of rank `dim B`
(`TauCeti.IsEhresmannConnection`). At every point the derivative `df_x` then restricts to a
linear isomorphism from the horizontal space `D x` onto `T_(f x) B`; its inverse is the
**horizontal lift** of tangent vectors of the base
(`TauCeti.IsEhresmannConnection.horizontalLift`). Integrating these pointwise lifts lifts paths
of the base horizontally, which is how a connection transports fibres along paths.

Every submersion carries Ehresmann connections. For a Riemannian metric on `P`, the orthogonal
complements `(ker df_x)ᗮ` of the vertical spaces of a `C^n` submersion form a `C^m` Ehresmann
connection when `m + 1 ≤ n` and the metric is `C^m`
(`Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker_mfderiv`). Its local frames are
gradients: in normal-form charts the submersion reads as a linear projection `u ↦ (L u).1` onto the
model space of `B`, and the gradients of the coordinates of this projection span the orthogonal
complement of its kernel (`TauCeti.isDistributionFrameOn_mgradient_coord`). No metric on `B` is
used. As a σ-compact Hausdorff smooth manifold carries a smooth Riemannian metric, every submersion
from such a manifold has an Ehresmann connection
(`Manifold.IsSubmersion.exists_isEhresmannConnection`).

## Main definitions

* `TauCeti.IsEhresmannConnection I J n f D`: `D` is a `C^n` Ehresmann connection on `f`.
* `TauCeti.IsEhresmannConnection.horizontalLift`: the horizontal lift `T_(f x) B ≃ D x`, inverse
  to the restriction of `df_x`.

## Main results

* `TauCeti.isDistributionFrameOn_mgradient_coord`: the gradients of the coordinates of a map to a
  vector space whose derivative is surjective form a local frame of the orthogonal complements of
  the kernels of its derivative.
* `Manifold.IsSubmersion.isContMDiffDistribution_orthogonal_ker_mfderiv`: the orthogonal
  complements of the vertical spaces of a submersion form a `C^m` distribution of rank `dim B`.
* `Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker_mfderiv`: they form an Ehresmann
  connection.
* `Manifold.IsSubmersion.exists_isEhresmannConnection`: every submersion from a σ-compact
  Hausdorff smooth manifold has an Ehresmann connection.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.3 (connections on fibred manifolds as horizontal complements of the vertical bundle)
  and §9.4 (their existence, from a Riemannian metric).
* C. Ehresmann, *Les connexions infinitésimales dans un espace fibré différentiable*, Colloque de
  topologie (espaces fibrés), Bruxelles (1950), 29–55.
-/

public section

noncomputable section

open Set Function Module Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Definition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {n : ℕ∞ω}

variable (I J n) in
/-- A distribution `D` on `P` is a `C^n` **Ehresmann connection** on `f : P → B` when `f` is
differentiable, at every point `x` the derivative `df_x` is surjective and the horizontal space
`D x` is a complement of the vertical space `ker (df_x)` in `T_x P`, and `D` is a `C^n`
distribution of rank `dim B`, the dimension of the model space `F` of `B`. -/
@[mk_iff]
structure IsEhresmannConnection (f : P → B) (D : Π x : P, Submodule 𝕜 (TangentSpace I x)) :
    Prop where
  /-- The map `f` is differentiable, so that `df_x` is its actual derivative. -/
  mdifferentiable : MDifferentiable I J f
  /-- The horizontal space at `x` is a complement of the vertical space `ker (df_x)`. -/
  isCompl_ker (x : P) : IsCompl (D x) (mfderiv I J f x).ker
  /-- The derivative of `f` is surjective at every point, so that every tangent vector of the
  base has a horizontal lift. -/
  surjective_mfderiv (x : P) : Surjective (mfderiv I J f x)
  /-- The horizontal spaces form a `C^n` distribution of rank `dim B`. -/
  isContMDiffDistribution : IsContMDiffDistribution I n (finrank 𝕜 F) D

namespace IsEhresmannConnection

variable {f : P → B} {D : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

include hD

/-- The horizontal spaces of an Ehresmann connection are finite-dimensional. -/
theorem finiteDimensional (x : P) : FiniteDimensional 𝕜 (D x) := by
  obtain ⟨U, -, hx, X, hX⟩ := isContMDiffDistribution_iff.1 hD.isContMDiffDistribution x
  exact (hX.isSubbundleFrameOn.basis hx).finiteDimensional_of_finite

/-- The horizontal spaces of an Ehresmann connection have the dimension of the base. -/
theorem finrank_eq (x : P) : finrank 𝕜 (D x) = finrank 𝕜 F :=
  hD.isContMDiffDistribution.finrank_eq x

/-- The restriction of `df_x` to the horizontal space `D x` is injective, as `D x` meets the
vertical space only in `0`. -/
theorem injective_mfderiv_comp_subtype (x : P) :
    Injective ((mfderiv I J f x : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x)) ∘ₗ
      (D x).subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  exact Subtype.ext ((Submodule.disjoint_def.1 (hD.isCompl_ker x).disjoint) w w.property
    (LinearMap.mem_ker.2 hw))

/-- The restriction of `df_x` to the horizontal space `D x` is surjective, as `df_x` is surjective
and vanishes on the vertical complement of `D x`. -/
theorem surjective_mfderiv_comp_subtype (x : P) :
    Surjective ((mfderiv I J f x : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x)) ∘ₗ
      (D x).subtype) := by
  intro v
  obtain ⟨u, rfl⟩ := hD.surjective_mfderiv x v
  obtain ⟨w, k, hw, hk, rfl⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.1 (hD.isCompl_ker x).codisjoint u
  have hk' : mfderiv I J f x k = 0 := LinearMap.mem_ker.1 hk
  exact ⟨⟨w, hw⟩, by simp [hk']⟩

/-- The **horizontal lift** of tangent vectors of the base at a point `x` of `P`: the linear
isomorphism `T_(f x) B ≃ D x` inverse to the restriction of `df_x` to the horizontal space. -/
def horizontalLift (x : P) : TangentSpace J (f x) ≃ₗ[𝕜] D x :=
  (LinearEquiv.ofBijective _
    ⟨hD.injective_mfderiv_comp_subtype x, hD.surjective_mfderiv_comp_subtype x⟩).symm

/-- The horizontal lift of a tangent vector of the base projects back to it. -/
@[simp]
theorem mfderiv_horizontalLift (x : P) (v : TangentSpace J (f x)) :
    mfderiv I J f x (hD.horizontalLift x v) = v :=
  (hD.horizontalLift x).symm_apply_apply v

/-- A horizontal vector is the horizontal lift of its projection. -/
@[simp]
theorem horizontalLift_mfderiv (x : P) (w : D x) :
    hD.horizontalLift x (mfderiv I J f x w) = w :=
  (hD.horizontalLift x).apply_symm_apply w

/-- The inverse of the horizontal lift is the restriction of `df_x` to the horizontal space. -/
@[simp]
theorem horizontalLift_symm_apply (x : P) (w : D x) :
    (hD.horizontalLift x).symm w = mfderiv I J f x w :=
  (LinearEquiv.symm_apply_eq _).2 (hD.horizontalLift_mfderiv x w).symm

/-- The horizontal lift of `v` is the unique horizontal vector projecting to `v`. -/
theorem eq_horizontalLift_iff {x : P} {v : TangentSpace J (f x)} {w : D x} :
    w = hD.horizontalLift x v ↔ mfderiv I J f x w = v := by
  refine ⟨fun h ↦ h ▸ hD.mfderiv_horizontalLift x v, fun h ↦ ?_⟩
  rw [← h, hD.horizontalLift_mfderiv]

end IsEhresmannConnection

end Definition

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  [RiemannianBundle (fun x : P ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞ω}

open _root_.TauCeti.Manifold in
/-- **Gradient frames of orthogonal complements of kernels.** Let `g : P → F` be a `C^(n+1)` map
into a vector space whose derivative is surjective at every point of an open set `U`, and let `b`
be a basis of `F`. For a `C^n` Riemannian metric on `P`, the gradients of the coordinates
`y ↦ b.coord i (g y)` form a `C^n` local frame on `U` of the orthogonal complements of the
kernels of the derivatives of `g`. -/
theorem isDistributionFrameOn_mgradient_coord [IsManifold I (n + 1) P]
    [IsContMDiffRiemannianBundle I n E (fun x : P ↦ TangentSpace I x)] {ι : Type*} [Finite ι]
    {g : P → F} {U : Set P} (hU : IsOpen U) (hg : ContMDiffOn I 𝓘(ℝ, F) (n + 1) g U)
    (hsurj : ∀ y ∈ U, Surjective (mvfderiv I g y)) (b : Basis ι ℝ F) :
    IsDistributionFrameOn I n (fun y ↦ (mvfderiv I g y).kerᗮ)
      (fun i ↦ mgradient I (fun y ↦ b.coord i (g y))) U := by
  classical
  have := Fintype.ofFinite ι
  have := b.finiteDimensional_of_finite
  have hgd {y : P} (hy : y ∈ U) : MDifferentiableAt I 𝓘(ℝ, F) g y :=
    ((hg.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
  have hinner {y : P} (hy : y ∈ U) (i : ι) (v : TangentSpace I y) :
      inner ℝ (mgradient I (fun y ↦ b.coord i (g y)) y) v = b.coord i (mvfderiv I g y v) :=
    (b.coord i).toContinuousLinearMap.inner_mgradient_comp (hgd hy) v
  -- The inner products of the frame against vectors mapped to the basis are the Kronecker delta.
  have hdelta {y : P} (hy : y ∈ U) (i j : ι) {w : TangentSpace I y}
      (hw : mvfderiv I g y w = b j) :
      inner ℝ (mgradient I (fun y ↦ b.coord i (g y)) y) w = if j = i then 1 else 0 := by
    rw [hinner hy i, hw, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
  have hli {y : P} (hy : y ∈ U) :
      LinearIndependent ℝ (fun i ↦ mgradient I (fun y ↦ b.coord i (g y)) y) := by
    refine Fintype.linearIndependent_iff.2 fun a ha i ↦ ?_
    obtain ⟨w, hw⟩ := hsurj y hy (b i)
    have hj (j : ι) : inner ℝ (mgradient I (fun y ↦ b.coord j (g y)) y) w =
        if i = j then 1 else 0 := hdelta hy j i hw
    have := congrArg (fun u ↦ inner ℝ u w) ha
    simpa only [sum_inner, real_inner_smul_left, hj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, inner_zero_left] using this
  refine ⟨fun i y hy ↦ ?_, hli, fun {y} hy ↦ ?_⟩
  · have hci : ContMDiffAt I 𝓘(ℝ) (n + 1) (fun y ↦ b.coord i (g y)) y :=
      (b.coord i).toContinuousLinearMap.contMDiff.contMDiffAt.comp y
        (hg.contMDiffAt (hU.mem_nhds hy))
    exact (contMDiffAt_mgradient hci).contMDiffWithinAt
  · have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
    -- The gradients are orthogonal to the kernel.
    have hle : Submodule.span ℝ (range fun i ↦ mgradient I (fun y ↦ b.coord i (g y)) y) ≤
        (mvfderiv I g y).kerᗮ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine (Submodule.mem_orthogonal' _ _).2 fun u hu ↦ ?_
      have hu' : mvfderiv I g y u = 0 := LinearMap.mem_ker.1 hu
      rw [hinner hy i, hu', map_zero]
    -- Both spaces have dimension `dim F`, by rank–nullity for the surjective derivative.
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have hrange : LinearMap.range (mvfderiv I g y : TangentSpace I y →ₗ[ℝ] F) = ⊤ :=
      LinearMap.range_eq_top.2 (hsurj y hy)
    have hnull := LinearMap.finrank_range_add_finrank_ker
      (mvfderiv I g y : TangentSpace I y →ₗ[ℝ] F)
    have horth := Submodule.finrank_add_finrank_orthogonal (mvfderiv I g y).ker
    rw [hrange, finrank_top] at hnull
    rw [finrank_span_eq_card (hli hy), ← finrank_eq_card_basis b]
    omega

end Gradient

end TauCeti

namespace Manifold.IsSubmersion

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {m n : ℕ∞ω} {f : P → B}

section Metric

variable [RiemannianBundle (fun x : P ↦ TangentSpace I x)]

/-- **The horizontal distribution of a submersion.** For a `C^n` submersion `f : P → B` from a
manifold modelled on a finite-dimensional real space and a `C^m` Riemannian metric on `P`, with
`m + 1 ≤ n`, the orthogonal complements `(ker df_x)ᗮ` of the vertical spaces form a `C^m`
distribution of rank `dim B`. Near each point it is spanned by the gradients of the coordinates
of `f` read in normal-form charts. -/
theorem isContMDiffDistribution_orthogonal_ker_mfderiv [IsManifold I (m + 1) P]
    [IsContMDiffRiemannianBundle I m E (fun x : P ↦ TangentSpace I x)]
    (hf : IsSubmersion I J n f) (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution I m (finrank ℝ F) (fun x ↦ (mfderiv I J f x).kerᗮ) := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hmn
  refine isContMDiffDistribution_iff.2 fun x ↦ ?_
  -- The model space of `B` is finite-dimensional, as `df_x` maps `T_x P` onto it.
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : FiniteDimensional ℝ F := Module.Finite.of_surjective
    (mfderiv I J f x : TangentSpace I x →ₗ[ℝ] TangentSpace J (f x)) (hf.surjective_mfderiv hn x)
  let h := (hf.isSubmersionAt x).isSubmersionAtOfComplement_complement
  -- In the normal-form charts `φ`, `ψ` of `f` at `x`, `f` reads as `g = (L ∘ φ).1`.
  let g : P → F := h.projection ∘ h.domChart.extend I
  have hφ : h.domChart ∈ IsManifold.maximalAtlas I (m + 1) P :=
    IsManifold.maximalAtlas_subset_of_le hmn h.domChart_mem_maximalAtlas
  have hg : ContMDiffOn I 𝓘(ℝ, F) (m + 1) g h.domChart.source := fun y hy ↦
    (h.projection.contMDiff.contMDiffAt.comp y
      (h.domChart.contMDiffAt_extend hφ hy)).contMDiffWithinAt
  have hgφ {y : P} (hy : y ∈ h.domChart.source) (v : TangentSpace I y) :
      mvfderiv I g y v = h.projection (mvfderiv I (h.domChart.extend I) y v) :=
    h.projection.mvfderiv_comp_apply
      ((h.domChart.contMDiffAt_extend hφ hy).mdifferentiableAt (by simp)) v
  have hsurj : ∀ y ∈ h.domChart.source, Surjective (mvfderiv I g y) := fun y hy w ↦ by
    obtain ⟨e, he⟩ := isInvertible_mfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le (by simp) hφ) hy
    obtain ⟨u, hu⟩ := h.equiv.surjective (w, 0)
    have heu : mvfderiv I (h.domChart.extend I) y (e.symm u) = u := by
      rw [mvfderiv_apply_eq_mfderiv_apply, ← he]
      exact e.apply_symm_apply u
    exact ⟨e.symm u, by rw [hgφ hy, heu, h.projection_apply, hu]⟩
  have hker {y : P} (hy : y ∈ h.domChart.source) :
      (mvfderiv I g y).ker = (mfderiv I J f y).ker := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hgφ hy,
      h.projection_apply]
    exact (h.mfderiv_eq_zero_iff hn hy v).symm
  have hX := isDistributionFrameOn_mgradient_coord h.domChart.open_source hg hsurj
    (Module.finBasis ℝ F)
  exact ⟨h.domChart.source, h.domChart.open_source, h.mem_domChart_source, _,
    ⟨hX.contMDiffOn, hX.linearIndependent, fun hy ↦ (hX.span_eq hy).trans (by rw [hker hy])⟩⟩

/-- **Ehresmann connections from metrics.** For a `C^n` submersion `f` and a `C^m` Riemannian
metric on `P`, with `m + 1 ≤ n`, the orthogonal complements `(ker df_x)ᗮ` of the vertical spaces
form a `C^m` Ehresmann connection on `f`. -/
theorem isEhresmannConnection_orthogonal_ker_mfderiv [IsManifold I (m + 1) P]
    [IsContMDiffRiemannianBundle I m E (fun x : P ↦ TangentSpace I x)]
    (hf : IsSubmersion I J n f) (hmn : m + 1 ≤ n) :
    IsEhresmannConnection I J m f (fun x ↦ (mfderiv I J f x).kerᗮ) where
  mdifferentiable := hf.contMDiff.mdifferentiable fun h ↦ by simp [h] at hmn
  isCompl_ker x := by
    have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    exact (Submodule.isCompl_orthogonal (mfderiv I J f x).ker).symm
  surjective_mfderiv := hf.surjective_mfderiv fun h ↦ by simp [h] at hmn
  isContMDiffDistribution := hf.isContMDiffDistribution_orthogonal_ker_mfderiv hmn

end Metric

/-- **Existence of Ehresmann connections.** A `C^n` submersion from a σ-compact Hausdorff smooth
manifold modelled on a finite-dimensional real space has a `C^m` Ehresmann connection for every
`m ≤ ∞` with `m + 1 ≤ n`: the orthogonal complements of its vertical spaces for a `C^m`
Riemannian metric. -/
theorem exists_isEhresmannConnection [T2Space P] [SigmaCompactSpace P] [IsManifold I ∞ P]
    {m : ℕ∞} (hf : IsSubmersion I J n f) (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ∃ D : Π x : P, Submodule ℝ (TangentSpace I x), IsEhresmannConnection I J m f D := by
  have : IsManifold I ((m : ℕ∞ω) + 1) P := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : ContMDiffVectorBundle m E (TangentSpace I : P → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := m) (F := E)
    (E := fun x : P ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : P ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I m E (fun x : P ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  exact ⟨_, hf.isEhresmannConnection_orthogonal_ker_mfderiv hmn⟩

end Manifold.IsSubmersion
