/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Normal

/-!
# The normal space of a Lagrangian submanifold is its cotangent space

Let `σ` be a fiberwise nondegenerate two-form on a finite-dimensional manifold `M` and let
`f : N → M` be a smooth embedding (`TauCeti.SmoothEmbedding`). Its normal space at `x` is the
quotient `T_(f x) M ⧸ df_x(T_x N)` (`TauCeti.SmoothEmbedding.NormalSpace`). An ambient tangent
vector `v` pairs with the tangent vectors of `N` through `σ`, giving the covector

`u ↦ σ(df_x u, v)`

on `T_x N`. When the tangent image `df_x(T_x N)` is isotropic, this pairing vanishes on the tangent
image and descends to a continuous linear map from the normal space to the cotangent space
`T*_x N`, the fibre of `TauCeti.CotangentBundle` at `x`
(`TauCeti.SmoothEmbedding.normalSpaceToCotangentOfIsIsotropic`). It is surjective, and its kernel
consists of the classes of the symplectic complement `(df_x(T_x N))^σ`. So the normal space of an
isotropic submanifold is an extension of its cotangent space by the symplectic normal space
`(df_x(T_x N))^σ ⧸ df_x(T_x N)`.

The map is injective exactly when the tangent image is Lagrangian. Then `[v] ↦ σ(df_x ·, v)` is a
continuous linear equivalence from the normal space of `f` at `x` to `T*_x N`
(`TauCeti.SmoothEmbedding.normalSpaceEquivCotangentOfIsLagrangian`). This identifies the normal
bundle of a Lagrangian submanifold `Q` with its cotangent bundle `T*Q`, fibre by fibre; it is the
linear identification on which Weinstein's Lagrangian neighbourhood theorem is built. Neither
closedness of `σ` nor compactness is needed. The hypotheses are pointwise, in the form of
`TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap` and
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap` at `x`.

The underlying linear algebra is in `TauCeti.Geometry.Symplectic.Lagrangian.Normal`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalSpaceToCotangentOfIsIsotropic`: the map `[v] ↦ σ(df_x ·, v)`
  from the normal space of an isotropic embedding at `x` to `T*_x N`.
* `TauCeti.SmoothEmbedding.normalSpaceEquivCotangentOfIsLagrangian`: the same map, as an
  equivalence, for a Lagrangian embedding.

## Main results

* `TauCeti.SmoothEmbedding.normalSpaceToCotangentOfIsIsotropic_normalClass`,
  `TauCeti.SmoothEmbedding.normalSpaceEquivCotangentOfIsLagrangian_normalClass`: the value on
  the class of `v` is the covector `u ↦ σ(df_x u, v)`.
* `TauCeti.SmoothEmbedding.normalSpaceToCotangentOfIsIsotropic_normalClass_eq_zero_iff`: the
  kernel consists of the classes of the symplectic complement of the tangent image.
* `TauCeti.SmoothEmbedding.normalSpaceToCotangentOfIsIsotropic_surjective`: every covector arises.
* `TauCeti.SmoothEmbedding.normalSpaceToCotangentOfIsIsotropic_injective_iff`: the map is
  injective exactly for a Lagrangian tangent image.
* `TauCeti.SmoothEmbedding.normalSpaceEquivCotangentOfIsLagrangian_symm_apply_eq_iff`: the normal
  vector corresponding to a covector `p` is the class of any `v` with `σ(df_x ·, v) = p`.

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 8 (the normal bundle of a Lagrangian submanifold).
-/

public section

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothEmbedding

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {n : ℕ∞ω}
  (f : SmoothEmbedding J I n N M) (x : N) (hn : n ≠ 0)

/-! ### Isotropic embeddings -/

/-- **The cotangent projection of the normal space of an isotropic submanifold.** At a point `x`
where the tangent image of the embedding `f` is isotropic for the nondegenerate two-form `σ`, the
pairing `[v] ↦ σ(df_x ·, v)` is a well-defined continuous linear map from the normal space of `f`
at `x` to the cotangent space `T*_x N`. -/
def normalSpaceToCotangentOfIsIsotropic
    (hI : (hσ.symplecticFormAt (f x)).IsIsotropic (LinearMap.range (mfderiv J I f x).toLinearMap)) :
    f.NormalSpace x hn →L[ℝ] (TangentSpace J x →L[ℝ] ℝ) :=
  haveI : FiniteDimensional ℝ (TangentSpace J x) :=
    Module.Finite.of_injective _ (f.isImmersion.mfderiv_injective hn x)
  f.normalLiftL x hn (LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
        (hσ.symplecticFormAt (f x)).normalPairing (mfderiv J I f x).toLinearMap))
    fun v hv ↦ by
      -- A tangent vector `df_x u` pairs to zero with the isotropic tangent image.
      obtain ⟨u, rfl⟩ := (f.mem_tangentRange_iff x hn v).mp hv
      have h0 : (hσ.symplecticFormAt (f x)).normalPairing (mfderiv J I f x).toLinearMap
          (mfderiv J I f x u) = 0 :=
        ((hσ.symplecticFormAt (f x)).normalPairing_eq_zero_iff _).mpr
          (SymplecticForm.isIsotropic_iff_le.mp hI ⟨u, rfl⟩)
      rw [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, h0, map_zero]

variable {f x hn}

/-- The covector of the normal class of `v` is `u ↦ σ(df_x u, v)`. -/
@[simp]
theorem normalSpaceToCotangentOfIsIsotropic_normalClass
    (hI : (hσ.symplecticFormAt (f x)).IsIsotropic (LinearMap.range (mfderiv J I f x).toLinearMap))
    (v : TangentSpace I (f x)) (u : TangentSpace J x) :
    f.normalSpaceToCotangentOfIsIsotropic x hn hI (f.normalClass x hn v) u =
      SmoothBundleForm.eval₂ σ (f x) (mfderiv J I f x u) v := by
  have : FiniteDimensional ℝ (TangentSpace J x) :=
    Module.Finite.of_injective _ (f.isImmersion.mfderiv_injective hn x)
  rw [normalSpaceToCotangentOfIsIsotropic, ← normalClassL_apply, ← ContinuousLinearMap.comp_apply,
    normalLiftL_comp_normalClassL, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.coe_toContinuousLinearMap', SymplecticForm.normalPairing_apply,
    SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, ContinuousLinearMap.coe_coe]

/-- The normal class of `v` has zero covector exactly when `v` lies in the symplectic complement
of the tangent image. So the kernel of the cotangent projection is the symplectic normal space
`(df_x(T_x N))^σ ⧸ df_x(T_x N)`. -/
theorem normalSpaceToCotangentOfIsIsotropic_normalClass_eq_zero_iff
    (hI : (hσ.symplecticFormAt (f x)).IsIsotropic (LinearMap.range (mfderiv J I f x).toLinearMap))
    (v : TangentSpace I (f x)) :
    f.normalSpaceToCotangentOfIsIsotropic x hn hI (f.normalClass x hn v) = 0 ↔
      v ∈ (hσ.symplecticFormAt (f x)).orthogonal
        (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [← SymplecticForm.normalPairing_eq_zero_iff, ContinuousLinearMap.ext_iff, LinearMap.ext_iff]
  simp only [normalSpaceToCotangentOfIsIsotropic_normalClass, zero_apply,
    SymplecticForm.normalPairing_apply, SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
    ContinuousLinearMap.coe_coe, LinearMap.zero_apply]

/-- Every covector of `N` at `x` is the pairing of a normal vector. -/
theorem normalSpaceToCotangentOfIsIsotropic_surjective
    (hI : (hσ.symplecticFormAt (f x)).IsIsotropic (LinearMap.range (mfderiv J I f x).toLinearMap)) :
    Function.Surjective (f.normalSpaceToCotangentOfIsIsotropic x hn hI) := by
  intro p
  obtain ⟨v, hv⟩ := (hσ.symplecticFormAt (f x)).normalPairing_surjective _
    (f.isImmersion.mfderiv_injective hn x) p.toLinearMap
  refine ⟨f.normalClass x hn v, ContinuousLinearMap.ext fun u ↦ ?_⟩
  rw [normalSpaceToCotangentOfIsIsotropic_normalClass, ← ContinuousLinearMap.coe_coe p, ← hv,
    SymplecticForm.normalPairing_apply, SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
    ContinuousLinearMap.coe_coe]

/-- The cotangent projection of an isotropic tangent image is injective exactly when the tangent
image is Lagrangian. -/
theorem normalSpaceToCotangentOfIsIsotropic_injective_iff
    (hI : (hσ.symplecticFormAt (f x)).IsIsotropic (LinearMap.range (mfderiv J I f x).toLinearMap)) :
    Function.Injective (f.normalSpaceToCotangentOfIsIsotropic x hn hI) ↔
      (hσ.symplecticFormAt (f x)).IsLagrangian (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [SymplecticForm.isLagrangian_iff, SymplecticForm.isCoisotropic_iff, injective_iff_map_eq_zero]
  refine ⟨fun hinj ↦ ⟨hI, fun v hv ↦ ?_⟩, fun hL q hq ↦ ?_⟩
  · have h0 := hinj _ ((normalSpaceToCotangentOfIsIsotropic_normalClass_eq_zero_iff hI v).mpr hv)
    obtain ⟨u, hu⟩ := (f.mem_tangentRange_iff x hn v).mp ((f.normalClass_eq_zero_iff x hn v).mp h0)
    exact ⟨u, hu⟩
  · obtain ⟨v, rfl⟩ := f.normalClass_surjective x hn q
    obtain ⟨u, hu⟩ :=
      hL.2 v ((normalSpaceToCotangentOfIsIsotropic_normalClass_eq_zero_iff hI v).mp hq)
    rw [← hu]
    exact normalClass_mfderiv f x hn u

/-! ### Lagrangian embeddings -/

variable (f x hn) in
/-- **The normal space of a Lagrangian submanifold is its cotangent space.** At a point `x` where
the tangent image of the embedding `f` is Lagrangian for the nondegenerate two-form `σ`, the map
`[v] ↦ σ(df_x ·, v)` is a continuous linear equivalence from the normal space of `f` at `x` to
the cotangent space `T*_x N`. -/
def normalSpaceEquivCotangentOfIsLagrangian
    (hL : (hσ.symplecticFormAt (f x)).IsLagrangian
      (LinearMap.range (mfderiv J I f x).toLinearMap)) :
    f.NormalSpace x hn ≃L[ℝ] (TangentSpace J x →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (f.normalSpaceToCotangentOfIsIsotropic x hn hL.isIsotropic).toLinearMap
    ⟨(normalSpaceToCotangentOfIsIsotropic_injective_iff hL.isIsotropic).mpr hL,
      normalSpaceToCotangentOfIsIsotropic_surjective hL.isIsotropic⟩).toContinuousLinearEquiv

/-- As a continuous linear map, the equivalence is the cotangent projection. -/
@[simp]
theorem coe_normalSpaceEquivCotangentOfIsLagrangian
    (hL : (hσ.symplecticFormAt (f x)).IsLagrangian
      (LinearMap.range (mfderiv J I f x).toLinearMap)) :
    (f.normalSpaceEquivCotangentOfIsLagrangian x hn hL : f.NormalSpace x hn →L[ℝ] _) =
      f.normalSpaceToCotangentOfIsIsotropic x hn hL.isIsotropic := by
  ext q u
  simp only [normalSpaceEquivCotangentOfIsLagrangian, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv']
  exact congrArg (fun p : TangentSpace J x →L[ℝ] ℝ ↦ p u) (LinearEquiv.ofBijective_apply _ q)

/-- The covector of the normal class of `v` is `u ↦ σ(df_x u, v)`. -/
@[simp]
theorem normalSpaceEquivCotangentOfIsLagrangian_normalClass
    (hL : (hσ.symplecticFormAt (f x)).IsLagrangian
      (LinearMap.range (mfderiv J I f x).toLinearMap))
    (v : TangentSpace I (f x)) (u : TangentSpace J x) :
    f.normalSpaceEquivCotangentOfIsLagrangian x hn hL (f.normalClass x hn v) u =
      SmoothBundleForm.eval₂ σ (f x) (mfderiv J I f x u) v := by
  rw [← ContinuousLinearEquiv.coe_coe, coe_normalSpaceEquivCotangentOfIsLagrangian,
    normalSpaceToCotangentOfIsIsotropic_normalClass]

/-- The normal vector corresponding to a covector `p` is the class of any ambient tangent vector
`v` with `σ(df_x u, v) = p u` for every `u`. -/
theorem normalSpaceEquivCotangentOfIsLagrangian_symm_apply_eq_iff
    (hL : (hσ.symplecticFormAt (f x)).IsLagrangian
      (LinearMap.range (mfderiv J I f x).toLinearMap))
    (p : TangentSpace J x →L[ℝ] ℝ) (v : TangentSpace I (f x)) :
    (f.normalSpaceEquivCotangentOfIsLagrangian x hn hL).symm p = f.normalClass x hn v ↔
      ∀ u, SmoothBundleForm.eval₂ σ (f x) (mfderiv J I f x u) v = p u := by
  rw [ContinuousLinearEquiv.symm_apply_eq, eq_comm, ContinuousLinearMap.ext_iff]
  simp only [normalSpaceEquivCotangentOfIsLagrangian_normalClass]

end SmoothEmbedding

end TauCeti
