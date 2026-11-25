/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Distribution
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Geometry.Manifold.Distribution.Complement
import TauCeti.Geometry.Manifold.Distribution.Submersion
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
(`TauCeti.IsEhresmannConnection.horizontalLift`). The horizontal part of a tangent vector `v`,
its projection onto `D x` along the vertical space, is the horizontal lift of `df_x v`
(`TauCeti.IsEhresmannConnection.projection_apply_eq_horizontalLift`). Integrating these pointwise
lifts lifts paths of the base horizontally, which is how a connection transports fibres along
paths.

Every submersion carries Ehresmann connections. For a Riemannian metric on `P`, the orthogonal
complements `(ker df_x)ᗮ` of the vertical spaces of a `C^n` submersion form a `C^m` Ehresmann
connection when `m + 1 ≤ n` and the metric is `C^m`
(`Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker_mfderiv`): they are the orthogonal
complements of the kernel distribution of the submersion
(`TauCeti.IsContMDiffDistribution.orthogonal`). No metric on `B` is used. As a σ-compact
Hausdorff smooth manifold carries a smooth Riemannian metric, every submersion from such a
manifold has an Ehresmann connection (`Manifold.IsSubmersion.exists_isEhresmannConnection`).

## Main definitions

* `TauCeti.IsEhresmannConnection I J n f D`: `D` is a `C^n` Ehresmann connection on `f`.
* `TauCeti.IsEhresmannConnection.horizontalLift`: the horizontal lift `T_(f x) B ≃ D x`, inverse
  to the restriction of `df_x`.

## Main results

* `TauCeti.IsEhresmannConnection.projection_apply_eq_horizontalLift`,
  `TauCeti.IsEhresmannConnection.projection_ker_apply`: the horizontal part of a tangent vector `v`
  is the horizontal lift of `df_x v`, and its vertical part is `v` minus that lift.
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

/-- **The horizontal part** of a tangent vector `v`, its projection onto the horizontal space along
the vertical space, is the horizontal lift of its image `df_x v`. -/
theorem projection_apply_eq_horizontalLift (x : P) (v : TangentSpace I x) :
    (D x).projection (mfderiv I J f x).ker (hD.isCompl_ker x) v =
      (hD.horizontalLift x (mfderiv I J f x v) : TangentSpace I x) := by
  have hker : mfderiv I J f x ((mfderiv I J f x).ker.projection (D x)
      (hD.isCompl_ker x).symm v) = 0 :=
    LinearMap.mem_ker.1 (Submodule.projection_apply_mem _ _)
  have hv := congrArg (mfderiv I J f x)
    (Submodule.projection_add_projection_eq_self (hD.isCompl_ker x) v)
  rw [map_add, hker, add_zero] at hv
  exact congrArg Subtype.val
    ((hD.eq_horizontalLift_iff (w := ⟨_, Submodule.projection_apply_mem _ v⟩)).2 hv)

/-- **The vertical part** of a tangent vector `v`, its projection onto the vertical space along the
horizontal space, is `v` minus the horizontal lift of `df_x v`. -/
theorem projection_ker_apply (x : P) (v : TangentSpace I x) :
    (mfderiv I J f x).ker.projection (D x) (hD.isCompl_ker x).symm v =
      v - (hD.horizontalLift x (mfderiv I J f x v) : TangentSpace I x) := by
  rw [Submodule.projection_eq_self_sub_projection (hD.isCompl_ker x),
    hD.projection_apply_eq_horizontalLift]

end IsEhresmannConnection

end Definition

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
distribution of rank `dim B`. -/
theorem isContMDiffDistribution_orthogonal_ker_mfderiv [IsManifold I (m + 1) P]
    [IsContMDiffRiemannianBundle I m E (fun x : P ↦ TangentSpace I x)]
    (hf : IsSubmersion I J n f) (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution I m (finrank ℝ F) (fun x ↦ (mfderiv I J f x).kerᗮ) := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hmn
  refine isContMDiffDistribution_iff.2 fun x ↦ ?_
  -- The model space of `B` is finite-dimensional, as `df_x` maps `T_x P` onto it.
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hsurj := hf.surjective_mfderiv hn x
  have : FiniteDimensional ℝ F := Module.Finite.of_surjective
    (mfderiv I J f x : TangentSpace I x →ₗ[ℝ] TangentSpace J (f x)) hsurj
  have hle : finrank ℝ F ≤ finrank ℝ E := LinearMap.finrank_le_finrank_of_surjective
    (f := (mfderiv I J f x : TangentSpace I x →ₗ[ℝ] TangentSpace J (f x))) hsurj
  -- The orthogonal complements of the kernel distribution, of rank `dim E - dim F`.
  have hD := (hf.isContMDiffDistribution_ker_mfderiv hmn).orthogonal
  rw [Nat.sub_sub_self hle] at hD
  exact isContMDiffDistribution_iff.1 hD x

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
