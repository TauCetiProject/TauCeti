/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TwoForm.Kernel
public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Isotropic

/-!
# The presymplectic form of a coisotropic submanifold

Let `σ` be a fiberwise nondegenerate smooth two-form on `M` and `f : N → M` a smooth map. At each
point `x` of `N`, the kernel of the pulled-back form `f^* σ` consists of the tangent vectors whose
image under `df_x` is `σ`-orthogonal to the whole tangent image `df_x(T_x N)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.ker_bilinFormAt_mpullback_eq_comap_orthogonal`).

For a coisotropic map this kernel is carried onto the symplectic orthogonal `(df_x(T_x N))^σ`, and
when `df_x` is injective it therefore has the codimension of `N`:

`dim ker (f^* σ)_x + dim N = dim M`

(`TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback_add`).
So the kernel rank of the form induced on an immersed, in particular an embedded, coisotropic
submanifold is automatically constant, equal to its codimension, with no rank hypothesis
(`IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback`,
`IsCoisotropicEmbedding.finrank_ker_bilinFormAt_mpullback`). When `σ` is closed, `f^* σ` is then
presymplectic, and its kernels are the tangent distribution of the *characteristic foliation* of
the coisotropic immersion (`IsCoisotropicMap.characteristicFoliation`), whose leaves are tangent
to the symplectic orthogonals of the tangent spaces of `N`
(`IsCoisotropicMap.map_characteristicFoliation_distribution`). Unqualified names here and below
are in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`.

Pointwise, the ambient tangent space along a coisotropic immersion is determined by the induced
presymplectic form alone: for any projection `P` of `T_x N` onto `K = ker (f^* σ)_x`, the
differential `df_x` extends to a linear symplectomorphism from the linear coisotropic model
`T_x N × K*` (`LinearMap.BilinForm.IsAlt.coisotropicModel`) onto `(T_(f x) M, σ_(f x))`
(`IsCoisotropicMap.exists_isSymplectomorphism_coisotropicModel`).
This is the first-order form of Gotay's coisotropic embedding theorem.

## References

* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 7.
-/

public noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}

/-- The pullback `f^* σ` evaluates through the differential of `f`. -/
private theorem symplecticFormAt_mfderiv_mfderiv (hf : ContMDiff J I ∞ f) (x : N)
    (v w : TangentSpace J x) :
    hσ.symplecticFormAt (f x) ((mfderiv J I f x).toLinearMap v)
        ((mfderiv J I f x).toLinearMap w) =
      (SmoothForm.mpullback f hf σ).bilinFormAt x v w := by
  simp only [ContinuousLinearMap.coe_coe, symplecticFormAt_apply, SmoothForm.bilinFormAt_apply,
    SmoothForm.eval₂_mpullback]

variable (hσ) in
/-- The kernel of the pullback `f^* σ` at `x` consists of the tangent vectors `v` such that
`df_x v` is `σ`-orthogonal to the tangent image `df_x(T_x N)`. -/
theorem ker_bilinFormAt_mpullback_eq_comap_orthogonal (hf : ContMDiff J I ∞ f) (x : N) :
    LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x) =
      ((hσ.symplecticFormAt (f x)).orthogonal
        (LinearMap.range (mfderiv J I f x).toLinearMap)).comap (mfderiv J I f x).toLinearMap :=
  (hσ.symplecticFormAt (f x)).ker_eq_comap_orthogonal_range
    (symplecticFormAt_mfderiv_mfderiv hf x)

/-- For a coisotropic map, the differential carries the kernel of the pullback `f^* σ` at `x`
onto the symplectic orthogonal of the tangent image `df_x(T_x N)`. -/
theorem IsCoisotropicMap.map_ker_bilinFormAt_mpullback (h : hσ.IsCoisotropicMap J f)
    (hf : ContMDiff J I ∞ f) (x : N) :
    (LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)).map
        (mfderiv J I f x).toLinearMap =
      (hσ.symplecticFormAt (f x)).orthogonal (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  (hσ.symplecticFormAt (f x)).map_ker_eq_orthogonal_range
    (symplecticFormAt_mfderiv_mfderiv hf x) (isCoisotropicMap_iff.1 h x)

/-- **The kernel rank of a coisotropic submanifold is its codimension.** At a point where the
differential of a coisotropic map `f` is injective, the kernel of `f^* σ` satisfies
`dim ker (f^* σ)_x + dim N = dim M`. -/
theorem IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback_add [FiniteDimensional ℝ E]
    (h : hσ.IsCoisotropicMap J f) (hf : ContMDiff J I ∞ f) {x : N}
    (hx : Function.Injective (mfderiv J I f x)) :
    finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)) + finrank ℝ F =
      finrank ℝ E :=
  (hσ.symplecticFormAt (f x)).finrank_ker_add_finrank_of_isCoisotropic hx
    (symplecticFormAt_mfderiv_mfderiv hf x) (isCoisotropicMap_iff.1 h x)

/-- **Pointwise coisotropic normal form.** At a point where the differential of a coisotropic map
`f` is injective, let `K` be the kernel of `f^* σ` at `x` and `P` a projection of `T_x N` onto
`K`. Then `df_x` extends to a linear symplectomorphism from the linear coisotropic model
`T_x N × K*` of the presymplectic form `(f^* σ)_x` onto `(T_(f x) M, σ_(f x))`. -/
theorem IsCoisotropicMap.exists_isSymplectomorphism_coisotropicModel [FiniteDimensional ℝ E]
    (h : hσ.IsCoisotropicMap J f) (hf : ContMDiff J I ∞ f) {x : N}
    (hx : Function.Injective (mfderiv J I f x))
    {P : TangentSpace J x →ₗ[ℝ] LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)}
    (hP : ∀ k : LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x), P k = k) :
    ∃ e : (TangentSpace J x × Module.Dual ℝ
        (LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x))) ≃ₗ[ℝ] TangentSpace I (f x),
      SymplecticForm.IsSymplectomorphism
          ((SmoothForm.isAlt_bilinFormAt _ x).coisotropicModel P hP) (hσ.symplecticFormAt (f x))
          e ∧
        ∀ v, e (v, 0) = mfderiv J I f x v :=
  (SmoothForm.isAlt_bilinFormAt _ x).exists_isSymplectomorphism_coisotropicModel hP
    (hσ.symplecticFormAt (f x)) hx (symplecticFormAt_mfderiv_mfderiv hf x)
    (isCoisotropicMap_iff.1 h x)

/-! ### Coisotropic immersions -/

/-- The form induced on an immersed coisotropic submanifold has constant kernel rank, equal to the
codimension: `dim ker (f^* σ)_x = dim M - dim N` at every point. -/
theorem IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback [FiniteDimensional ℝ E]
    (h : hσ.IsCoisotropicMap J f) (hi : IsImmersion J I ∞ f) (hf : ContMDiff J I ∞ f) (x : N) :
    finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)) =
      finrank ℝ E - finrank ℝ F := by
  have := h.finrank_ker_bilinFormAt_mpullback_add hf (hi.mfderiv_injective (by simp) x)
  omega

/-- The **characteristic foliation** of a coisotropic immersion `f : N → M` for a closed
nondegenerate two-form `σ`: the foliation of `N`, of rank `dim M - dim N`, whose tangent
distribution is the field of kernels of the presymplectic form `f^* σ`. -/
def IsCoisotropicMap.characteristicFoliation [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : hσ.IsCoisotropicMap J f) (hi : IsImmersion J I ∞ f) (hf : ContMDiff J I ∞ f)
    (hσc : σ.IsClosed) {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold J (n + 1) N] (hn : 1 ≤ n) :
    Foliation J n N (finrank ℝ E - finrank ℝ F) :=
  (SmoothForm.mpullback f hf σ).characteristicFoliation (hσc.mpullback f hf)
    (h.finrank_ker_bilinFormAt_mpullback hi hf) hn

/-- The tangent distribution of the characteristic foliation of a coisotropic immersion is the
field of kernels of the induced presymplectic form. -/
@[simp]
theorem IsCoisotropicMap.characteristicFoliation_distribution [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (h : hσ.IsCoisotropicMap J f) (hi : IsImmersion J I ∞ f)
    (hf : ContMDiff J I ∞ f) (hσc : σ.IsClosed) {n : ℕ∞ω} [ENat.LEInfty n]
    [IsManifold J (n + 1) N] (hn : 1 ≤ n) (x : N) :
    (h.characteristicFoliation hi hf hσc hn).distribution x =
      LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x) :=
  SmoothForm.characteristicFoliation_distribution _ _ _ hn x

/-- The leaves of the characteristic foliation of a coisotropic immersion are tangent to the
symplectic orthogonals of the submanifold: the differential carries the tangent space of the
foliation at `x` onto `(df_x(T_x N))^σ`. -/
theorem IsCoisotropicMap.map_characteristicFoliation_distribution [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (h : hσ.IsCoisotropicMap J f) (hi : IsImmersion J I ∞ f)
    (hf : ContMDiff J I ∞ f) (hσc : σ.IsClosed) {n : ℕ∞ω} [ENat.LEInfty n]
    [IsManifold J (n + 1) N] (hn : 1 ≤ n) (x : N) :
    ((h.characteristicFoliation hi hf hσc hn).distribution x).map (mfderiv J I f x).toLinearMap =
      (hσ.symplecticFormAt (f x)).orthogonal (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [characteristicFoliation_distribution]
  exact h.map_ker_bilinFormAt_mpullback hf x

/-- An embedded coisotropic submanifold has constant kernel rank equal to its codimension. -/
theorem IsCoisotropicEmbedding.finrank_ker_bilinFormAt_mpullback [FiniteDimensional ℝ E]
    (h : hσ.IsCoisotropicEmbedding J f) (hf : ContMDiff J I ∞ f) (x : N) :
    finrank ℝ (LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)) =
      finrank ℝ E - finrank ℝ F :=
  h.isCoisotropicMap.finrank_ker_bilinFormAt_mpullback h.isImmersion hf x

end TauCeti.SmoothTwoForm.IsNondegenerate
