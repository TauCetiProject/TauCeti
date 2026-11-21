/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Orthogonal
public import TauCeti.Geometry.Manifold.Distribution.Submersion
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Ehresmann connections

Let `f : M → N` be a map between manifolds modelled on finite-dimensional spaces `E` and `E'`. An
**Ehresmann connection** for `f` (`TauCeti.IsEhresmannConnection`) is a `C^n` distribution `Hz` on
`M` of rank `dim E'`, the *horizontal distribution*, which is complementary at every point to the
*vertical space*, the kernel of the derivative of `f` (Kolář–Michor–Slovák §9.3). It splits every
tangent vector of `M` uniquely into a vertical and a horizontal part: these are the projections
`Submodule.projection` along the splitting, which sum to the identity
(`Submodule.projection_add_projection_eq_self`).

The derivative of `f` is injective on the horizontal space, which has the dimension of `N`, so it
maps the horizontal space at `x` isomorphically onto the tangent space at `f x`
(`TauCeti.IsEhresmannConnection.mfderivEquiv`). In particular `f` has surjective derivative at every
point (`TauCeti.IsEhresmannConnection.surjective_mfderiv`): only maps with surjective derivative
carry Ehresmann connections. The inverse isomorphism is the **horizontal lift**
(`TauCeti.IsEhresmannConnection.horizontalLift`): the unique horizontal vector at `x` with given
image under the derivative (`TauCeti.IsEhresmannConnection.eq_horizontalLift_iff`). The horizontal
part of a tangent vector `v` is the horizontal lift of its image `df v`
(`TauCeti.IsEhresmannConnection.projection_apply_eq_horizontalLift`), and its vertical part is
`v` minus that lift (`TauCeti.IsEhresmannConnection.projection_ker_apply`).

Conversely, a `C^n` submersion has Ehresmann connections of class `C^m` for `m + 1 ≤ n`. For a
`C^m` Riemannian metric on `M`, the orthogonal complement of the kernel distribution of `f` is one
(`Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker`): the kernel distribution is a `C^m`
distribution of rank `dim E - dim E'`
(`Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`), so its orthogonal complement is a
`C^m` distribution of rank `dim E'` (`TauCeti.IsContMDiffDistribution.orthogonal`). For
`m ≤ ∞`, a `C^m` metric exists on a σ-compact Hausdorff `C^∞` manifold
(`TauCeti.nonempty_contMDiffRiemannianMetric`), so there every `C^n` submersion has an Ehresmann
connection of class `C^m` for every `m ≤ ∞` with `m + 1 ≤ n`
(`Manifold.IsSubmersion.exists_isEhresmannConnection`). The analytic case `m = ω` is not covered.
No surjectivity, properness or connectedness is assumed: these enter only the transport along
horizontal lifts of curves and Ehresmann's fibration theorem, which are not proved here.

## Main definitions

* `TauCeti.IsEhresmannConnection`: a horizontal distribution complementary to the kernel of the
  derivative.
* `TauCeti.IsEhresmannConnection.mfderivEquiv`: the derivative as an isomorphism from the horizontal
  space onto the tangent space of the target.
* `TauCeti.IsEhresmannConnection.horizontalLift`: the horizontal lift of tangent vectors of the
  target.

## Main results

* `TauCeti.IsEhresmannConnection.surjective_mfderiv`: a map with an Ehresmann connection has
  surjective derivative everywhere.
* `TauCeti.IsEhresmannConnection.eq_horizontalLift_iff`: the horizontal lift of `w` is the unique
  horizontal vector with image `w`.
* `TauCeti.IsEhresmannConnection.range_horizontalLift`: the horizontal lifts fill the horizontal
  space.
* `TauCeti.IsEhresmannConnection.projection_apply_eq_horizontalLift`,
  `TauCeti.IsEhresmannConnection.projection_ker_apply`: the horizontal and vertical parts of a
  tangent vector.
* `Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker`: the orthogonal complement of the
  vertical distribution of a submersion is an Ehresmann connection.
* `Manifold.IsSubmersion.exists_isEhresmannConnection`: existence of Ehresmann connections on
  σ-compact Hausdorff manifolds.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §9.3 (connections on fibred manifolds).
* C. Ehresmann, *Les connexions infinitésimales dans un espace fibré différentiable*, Colloque de
  topologie (espaces fibrés), Bruxelles, 1950, 29–55.
-/

public section

noncomputable section

open Bundle Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {Hz : Π x : M, Submodule 𝕜 (TangentSpace I x)}

variable (I J n) in
/-- **Ehresmann connections.** An Ehresmann connection of class `C^n` for a map `f : M → N` is a
`C^n` distribution `Hz` on `M` of rank the dimension of the model of `N`, the horizontal
distribution, which is complementary at every point to the kernel of the derivative of `f`, the
vertical space. -/
structure IsEhresmannConnection (f : M → N) (Hz : Π x : M, Submodule 𝕜 (TangentSpace I x)) :
    Prop where
  /-- The horizontal distribution is a `C^n` distribution of rank `dim N`. -/
  isContMDiffDistribution : IsContMDiffDistribution I n (finrank 𝕜 E') Hz
  /-- At every point the horizontal space is complementary to the vertical space. -/
  isCompl_ker (x : M) : IsCompl (mfderiv I J f x).ker (Hz x)

namespace IsEhresmannConnection

variable (h : IsEhresmannConnection I J n f Hz) (x : M)

include h

/-- The derivative of `f` is injective on the horizontal space. -/
theorem injective_mfderiv_comp_subtype :
    Injective ((mfderiv I J f x : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x)) ∘ₗ
      (Hz x).subtype) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ Subtype.ext ?_
  have hmem : (v : TangentSpace I x) ∈ (mfderiv I J f x).ker ⊓ Hz x := ⟨hv, v.2⟩
  rwa [(h.isCompl_ker x).inf_eq_bot, Submodule.mem_bot] at hmem

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']

/-- The derivative of `f` maps the horizontal space onto the tangent space of the target, which
has the same dimension. -/
theorem surjective_mfderiv_comp_subtype :
    Surjective ((mfderiv I J f x : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x)) ∘ₗ
      (Hz x).subtype) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((h.isContMDiffDistribution.finrank_eq x).trans
      (finrank_tangentSpace (I := J) (f x)).symm)).1 (h.injective_mfderiv_comp_subtype x)

/-- **A map with an Ehresmann connection has surjective derivative** at every point. -/
theorem surjective_mfderiv : Surjective (mfderiv I J f x) := fun w ↦
  let ⟨v, hv⟩ := h.surjective_mfderiv_comp_subtype x w
  ⟨v, hv⟩

/-- The derivative of `f` maps the horizontal space at `x` isomorphically onto the tangent space
of `N` at `f x`. -/
def mfderivEquiv : Hz x ≃ₗ[𝕜] TangentSpace J (f x) :=
  LinearEquiv.ofBijective _
    ⟨h.injective_mfderiv_comp_subtype x, h.surjective_mfderiv_comp_subtype x⟩

@[simp]
theorem mfderivEquiv_apply (v : Hz x) : h.mfderivEquiv x v = mfderiv I J f x v :=
  (rfl)

/-- **The horizontal lift** of tangent vectors of `N` at `f x` to horizontal tangent vectors of `M`
at `x`: the inverse of the derivative on the horizontal space. -/
def horizontalLift : TangentSpace J (f x) →ₗ[𝕜] TangentSpace I x :=
  (Hz x).subtype ∘ₗ (h.mfderivEquiv x).symm.toLinearMap

/-- The inverse of `TauCeti.IsEhresmannConnection.mfderivEquiv` is the horizontal lift. -/
@[simp]
theorem coe_mfderivEquiv_symm_apply (w : TangentSpace J (f x)) :
    ((h.mfderivEquiv x).symm w : TangentSpace I x) = h.horizontalLift x w :=
  (rfl)

/-- The horizontal lift is horizontal. -/
theorem horizontalLift_mem (w : TangentSpace J (f x)) : h.horizontalLift x w ∈ Hz x :=
  ((h.mfderivEquiv x).symm w).2

/-- The horizontal lift is a right inverse of the derivative. -/
@[simp]
theorem mfderiv_horizontalLift (w : TangentSpace J (f x)) :
    mfderiv I J f x (h.horizontalLift x w) = w :=
  (h.mfderivEquiv x).apply_symm_apply w

/-- **Characterization of the horizontal lift**: the horizontal lift of `w` is the unique
horizontal tangent vector whose image under the derivative is `w`. -/
theorem eq_horizontalLift_iff {v : TangentSpace I x} {w : TangentSpace J (f x)} :
    v = h.horizontalLift x w ↔ v ∈ Hz x ∧ mfderiv I J f x v = w := by
  refine ⟨fun hv ↦ hv ▸ ⟨h.horizontalLift_mem x w, h.mfderiv_horizontalLift x w⟩,
    fun ⟨hv, hw⟩ ↦ ?_⟩
  have : (⟨v, hv⟩ : Hz x) = (h.mfderivEquiv x).symm w :=
    (h.mfderivEquiv x).eq_symm_apply.2 hw
  exact congrArg Subtype.val this

/-- A horizontal tangent vector is the horizontal lift of its image under the derivative. -/
theorem horizontalLift_mfderiv_of_mem {v : TangentSpace I x} (hv : v ∈ Hz x) :
    h.horizontalLift x (mfderiv I J f x v) = v :=
  ((h.eq_horizontalLift_iff x).2 ⟨hv, rfl⟩).symm

/-- The horizontal lifts at `x` fill the horizontal space: an Ehresmann connection is determined
by its horizontal lifts. -/
theorem range_horizontalLift : LinearMap.range (h.horizontalLift x) = Hz x := by
  ext v
  exact ⟨fun ⟨w, hw⟩ ↦ hw ▸ h.horizontalLift_mem x w,
    fun hv ↦ ⟨_, h.horizontalLift_mfderiv_of_mem x hv⟩⟩

/-- **The horizontal part** of a tangent vector `v`, its projection onto the horizontal space along
the vertical space, is the horizontal lift of its image `df v`. -/
theorem projection_apply_eq_horizontalLift (v : TangentSpace I x) :
    (Hz x).projection (mfderiv I J f x).ker (h.isCompl_ker x).symm v =
      h.horizontalLift x (mfderiv I J f x v) := by
  refine (h.eq_horizontalLift_iff x).2 ⟨Submodule.projection_apply_mem _ _, ?_⟩
  have hv := Submodule.projection_add_projection_eq_self (h.isCompl_ker x).symm v
  have hker : mfderiv I J f x ((mfderiv I J f x).ker.projection (Hz x)
      (h.isCompl_ker x).symm.symm v) = 0 :=
    LinearMap.mem_ker.1 (Submodule.projection_apply_mem _ _)
  conv_rhs => rw [← hv]
  rw [map_add, hker, add_zero]

/-- **The vertical part** of a tangent vector `v`, its projection onto the vertical space along the
horizontal space, is `v` minus the horizontal lift of `df v`. -/
theorem projection_ker_apply (v : TangentSpace I x) :
    (mfderiv I J f x).ker.projection (Hz x) (h.isCompl_ker x) v =
      v - h.horizontalLift x (mfderiv I J f x v) := by
  rw [Submodule.projection_eq_self_sub_projection (h.isCompl_ker x).symm,
    h.projection_apply_eq_horizontalLift]

end IsEhresmannConnection

end TauCeti

namespace Manifold

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {m n : ℕ∞ω} {f : M → N}

/-- **The orthogonal Ehresmann connection of a submersion.** For a `C^n` submersion `f : M → N`
between manifolds modelled on finite-dimensional real spaces, with `m + 1 ≤ n`, and a `C^m`
Riemannian metric on the `C^(m+1)` manifold `M`, the orthogonal complements of the kernels of the
derivative of `f` form an Ehresmann connection of class `C^m`. -/
theorem IsSubmersion.isEhresmannConnection_orthogonal_ker
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I (m + 1) M]
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    (hf : IsSubmersion I J n f) (hmn : m + 1 ≤ n) :
    IsEhresmannConnection I J m f fun x ↦ (mfderiv I J f x).kerᗮ := by
  have hn : n ≠ 0 := (zero_lt_one.trans_le (le_add_self.trans hmn)).ne'
  refine ⟨isContMDiffDistribution_iff.mpr fun x ↦ ?_,
    fun x ↦ (mfderiv I J f x).ker.isCompl_orthogonal⟩
  -- The kernel distribution has rank `dim E - dim E'`, and `dim E' ≤ dim E` since the derivative
  -- at `x` is surjective.
  have hle : finrank ℝ E' ≤ finrank ℝ E :=
    LinearMap.finrank_le_finrank_of_surjective
      (f := (mfderiv I J f x : TangentSpace I x →ₗ[ℝ] TangentSpace J (f x)))
      (hf.surjective_mfderiv hn x)
  have h := isContMDiffDistribution_iff.mp
    (hf.isContMDiffDistribution_ker_mfderiv hmn).orthogonal x
  rwa [Nat.sub_sub_self hle] at h

/-- **Existence of Ehresmann connections.** A `C^n` submersion from a σ-compact Hausdorff smooth
manifold modelled on a finite-dimensional real space has an Ehresmann connection of class `C^k`
for every `k ≤ ∞` with `k + 1 ≤ n`. -/
theorem IsSubmersion.exists_isEhresmannConnection {k : ℕ∞} [T2Space M] [SigmaCompactSpace M]
    [IsManifold I ∞ M] (hf : IsSubmersion I J n f) (hkn : k + 1 ≤ n) :
    ∃ Hz : Π x : M, Submodule ℝ (TangentSpace I x), IsEhresmannConnection I J k f Hz := by
  have : IsManifold I (k + 1) M := .of_le (n := ∞) (by exact_mod_cast le_top)
  have := TangentBundle.contMDiffVectorBundle (n := k) (I := I) (M := M)
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := k) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  exact ⟨_, hf.isEhresmannConnection_orthogonal_ker hkn⟩

end Manifold
