/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The symplectic normal bundle of a symplectic submanifold

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `N`, and let
`f : M → N` be a smooth embedding whose tangent images `df_x(T_x M)` are symplectic subspaces of
`(T_(f x) N, σ_(f x))` (`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages`), so
that `f` parametrizes a symplectic submanifold. Each ambient tangent space then splits as

`T_(f x) N = df_x(T_x M) ⊕ df_x(T_x M)^σ`,

and the second summand, the *symplectic normal space* `(T M)^σ`, is a canonical complement of the
tangent space. This file identifies the intrinsic normal space `T_(f x) N / df_x(T_x M)` of the
embedding with it: every normal class contains exactly one vector of the symplectic complement,
its **symplectic representative** (`TauCeti.SmoothEmbedding.symplecticNormalRepresentative`).

The symplectic complement is itself a symplectic subspace, so `σ` restricts to a linear symplectic
form on it. Transported to the normal space, this is the **normal symplectic form**
(`TauCeti.SmoothEmbedding.symplecticNormalForm`): two normal classes pair as their symplectic
representatives under `σ`. With this fibrewise form the normal bundle is the symplectic normal
bundle of the submanifold, the data on which the symplectic neighbourhood theorem is stated: two
symplectic submanifolds have symplectomorphic neighbourhood germs when their normal bundles are
isomorphic as symplectic vector bundles, compatibly with a symplectomorphism of the submanifolds.

Concretely, the symplectic representative of the class of `v` is `v - df_x u`, where `u` is the
tangent vector of `M` with `(f^* σ)(u, ·) = σ(v, df_x ·)`; it exists and is unique because
`f^* σ` is nondegenerate
(`TauCeti.SmoothEmbedding.symplecticNormalRepresentative_normalClass_eq_sub_mfderiv_inverse`).
Inverting the flat map of the pulled-back form `f^* σ` along `M` therefore makes the
representatives depend smoothly on the base point and the normal vector: for a `C^n` embedding
the map from the normal bundle to the ambient tangent bundle is `C^m` when `m + 1 ≤ n`
(`TauCeti.SmoothEmbedding.contMDiff_symplecticNormalRepresentative`). This parallels the
orthogonal representatives of a Riemannian metric
(`TauCeti.SmoothEmbedding.contMDiff_normalRepresentative`), with the flat map of `f^* σ` in place of
the induced metric. No compactness of `M` and no closedness of `σ` is used.

## Main definitions

* `TauCeti.SmoothEmbedding.normalSpaceSymplecticComplementEquiv`: the normal space at `x` is
  isomorphic to the symplectic complement of the tangent space.
* `TauCeti.SmoothEmbedding.symplecticNormalRepresentative`: the symplectic representative of a
  normal class, as a continuous linear map into the ambient tangent space.
* `TauCeti.SmoothEmbedding.symplecticNormalForm`: the linear symplectic form on each normal space.

## Main results

* `TauCeti.SmoothEmbedding.symplecticNormalRepresentative_eq_iff`: the symplectic representative is
  the unique vector of the symplectic complement in its normal class.
* `TauCeti.SmoothEmbedding.range_symplecticNormalRepresentative`: the representatives fill the
  symplectic complement.
* `TauCeti.SmoothEmbedding.symplecticNormalForm_apply`,
  `TauCeti.SmoothEmbedding.symplecticNormalForm_normalClass`: the normal symplectic form pairs
  normal classes as their representatives, equivalently as any representative of the first class
  against the symplectic representative of the second.
* `TauCeti.SmoothEmbedding.contMDiff_symplecticNormalRepresentative_normalClass`,
  `TauCeti.SmoothEmbedding.contMDiff_symplecticNormalRepresentative`: the symplectic
  representatives are smooth on the normal bundle.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 3.4 (the symplectic normal bundle and the symplectic
  neighbourhood theorem, Theorem 3.4.10).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 7.
-/

public section

noncomputable section

open Bundle Manifold Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

open SmoothTwoForm

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {n : ℕ∞ω} {σ : SmoothTwoForm J N} {hσ : σ.IsNondegenerate}

/-! ### Symplectic representatives of normal classes -/

section Pointwise

omit [FiniteDimensional ℝ V] in
/-- The tangent space of the embedding at `x` is a symplectic subspace. -/
private theorem isSymplectic_tangentRange (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    (hσ.symplecticFormAt (f x)).IsSymplectic (f.tangentRange x hn) :=
  IsNondegenerate.hasSymplecticTangentImages_iff_forall.1 h x

/-- In a finite-dimensional manifold, a symplectic tangent space and its symplectic complement
are topological complements. -/
private theorem isTopCompl_tangentRange_orthogonal (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    Submodule.IsTopCompl (f.tangentRange x hn)
      ((hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn)) := by
  have : FiniteDimensional ℝ (TangentSpace J (f x)) := inferInstanceAs (FiniteDimensional ℝ V)
  exact ⟨(isSymplectic_tangentRange f h x hn).isCompl,
    LinearMap.continuous_of_finiteDimensional _⟩

/-- Symplectic representatives identify the intrinsic normal space of a symplectic submanifold
embedding with the symplectic complement of its tangent space. -/
def normalSpaceSymplecticComplementEquiv (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    f.NormalSpace x hn ≃L[ℝ] (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn) :=
  (f.tangentRange x hn).quotientEquivOfIsTopCompl _
    (isTopCompl_tangentRange_orthogonal f h x hn)

/-- The inverse of the symplectic-representative equivalence takes the normal class of a vector of
the symplectic complement. -/
@[simp]
theorem normalSpaceSymplecticComplementEquiv_symm_apply (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0)
    (v : (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn)) :
    (f.normalSpaceSymplecticComplementEquiv h x hn).symm v = f.normalClass x hn v := by
  rw [normalClass_def]
  exact Submodule.quotientEquivOfIsTopCompl_symm_apply _ v

/-- The **symplectic representative** of a normal class of a symplectic submanifold embedding:
the unique vector of the class lying in the symplectic complement of the tangent space. -/
def symplecticNormalRepresentative (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    f.NormalSpace x hn →L[ℝ] TangentSpace J (f x) :=
  ((hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn)).subtypeL.comp
    (f.normalSpaceSymplecticComplementEquiv h x hn).toContinuousLinearMap

/-- The symplectic representative is the vector given by the symplectic-representative
equivalence. -/
theorem symplecticNormalRepresentative_apply (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn) :
    f.symplecticNormalRepresentative h x hn v = f.normalSpaceSymplecticComplementEquiv h x hn v :=
  (rfl)

/-- Taking the normal class of the symplectic representative recovers the original class. -/
@[simp]
theorem normalClass_symplecticNormalRepresentative (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn) :
    f.normalClass x hn (f.symplecticNormalRepresentative h x hn v) = v := by
  rw [symplecticNormalRepresentative_apply,
    ← f.normalSpaceSymplecticComplementEquiv_symm_apply h x hn,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Symplectic representatives lie in the symplectic complement of the tangent space. -/
theorem symplecticNormalRepresentative_mem_orthogonal (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn) :
    f.symplecticNormalRepresentative h x hn v ∈
      (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn) := by
  rw [symplecticNormalRepresentative_apply]
  exact (f.normalSpaceSymplecticComplementEquiv h x hn v).property

/-- The symplectic representative is the unique vector of the symplectic complement of the tangent
space in its normal class. -/
theorem symplecticNormalRepresentative_eq_iff (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn)
    (w : TangentSpace J (f x)) :
    f.symplecticNormalRepresentative h x hn v = w ↔
      w ∈ (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn) ∧
        f.normalClass x hn w = v := by
  constructor
  · rintro rfl
    exact ⟨f.symplecticNormalRepresentative_mem_orthogonal h x hn v,
      f.normalClass_symplecticNormalRepresentative h x hn v⟩
  · rintro ⟨hw, rfl⟩
    rw [symplecticNormalRepresentative_apply,
      ← f.normalSpaceSymplecticComplementEquiv_symm_apply h x hn ⟨w, hw⟩,
      ContinuousLinearEquiv.apply_symm_apply]

/-- A vector of the symplectic complement is the symplectic representative of its own normal
class. -/
@[simp]
theorem symplecticNormalRepresentative_normalClass_of_mem (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) {w : TangentSpace J (f x)}
    (hw : w ∈ (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn)) :
    f.symplecticNormalRepresentative h x hn (f.normalClass x hn w) = w :=
  (f.symplecticNormalRepresentative_eq_iff h x hn _ w).2 ⟨hw, rfl⟩

/-- The symplectic representatives fill the symplectic complement of the tangent space. -/
theorem range_symplecticNormalRepresentative (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    LinearMap.range (f.symplecticNormalRepresentative h x hn).toLinearMap =
      (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn) := by
  ext w
  refine ⟨?_, fun hw ↦ ⟨f.normalClass x hn w,
    f.symplecticNormalRepresentative_normalClass_of_mem h x hn hw⟩⟩
  rintro ⟨v, rfl⟩
  exact f.symplecticNormalRepresentative_mem_orthogonal h x hn v

/-- Taking symplectic representatives is injective. -/
theorem injective_symplecticNormalRepresentative (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    Injective (f.symplecticNormalRepresentative h x hn) :=
  LeftInverse.injective (f.normalClass_symplecticNormalRepresentative h x hn)

/-- A symplectic representative pairs to zero under `σ` with every tangent vector of the
embedded submanifold. -/
theorem eval₂_symplecticNormalRepresentative_mfderiv (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn)
    (w : TangentSpace I x) :
    SmoothBundleForm.eval₂ σ (f x) (f.symplecticNormalRepresentative h x hn v)
      (mfderiv I J f x w) = 0 := by
  rw [← IsNondegenerate.symplecticFormAt_apply hσ]
  exact SymplecticForm.mem_orthogonal_iff'.1
    (f.symplecticNormalRepresentative_mem_orthogonal h x hn v) _ ⟨w, rfl⟩

/-- Every tangent vector of the embedded submanifold pairs to zero under `σ` with a symplectic
representative. -/
theorem eval₂_mfderiv_symplecticNormalRepresentative (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn)
    (w : TangentSpace I x) :
    SmoothBundleForm.eval₂ σ (f x) (mfderiv I J f x w)
      (f.symplecticNormalRepresentative h x hn v) = 0 := by
  rw [← IsNondegenerate.symplecticFormAt_apply hσ]
  exact SymplecticForm.mem_orthogonal_iff.1
    (f.symplecticNormalRepresentative_mem_orthogonal h x hn v) _ ⟨w, rfl⟩

omit [FiniteDimensional ℝ V] in
/-- The flat map of the pulled-back form `f^* σ` at a point is invertible: a tangent vector `u`
with `σ(df_x u, df_x ·) = 0` has `df_x u` in the tangent space and in its symplectic complement,
so `df_x u = 0`, and `df_x` is injective. -/
private theorem isInvertible_of_eval₂_mfderiv [FiniteDimensional ℝ E]
    (f : SmoothEmbedding I J n M N) (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0)
    (a : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (ha : ∀ u w, a u w = SmoothBundleForm.eval₂ σ (f x) (mfderiv I J f x u) (mfderiv I J f x w)) :
    a.IsInvertible := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ContinuousLinearMap.isInvertible_of_separatingLeft (E := E) fun u hu ↦ ?_
  have hdu : mfderiv I J f x u = 0 := by
    refine Submodule.disjoint_def.1
      (SymplecticForm.isSymplectic_iff_disjoint.1 (isSymplectic_tangentRange f h x hn)) _
      ⟨u, rfl⟩ (SymplecticForm.mem_orthogonal_iff'.2 ?_)
    rintro _ ⟨w, rfl⟩
    rw [ContinuousLinearMap.coe_coe, IsNondegenerate.symplecticFormAt_apply]
    exact (ha u w).symm.trans (hu w)
  exact (injective_iff_map_eq_zero _).1 (f.isImmersion.mfderiv_injective hn x) u hdu

/-- **The symplectic representative as a tangential correction.** Let `a` be the flat map of the
pulled-back form at `x`, `a u w = σ(df_x u, df_x w)`, which is invertible because `f^* σ` is
nondegenerate. The symplectic representative of the class of `v` is `v - df_x u`, where
`u = a⁻¹ (σ(v, df_x ·))` is the tangent vector whose image carries the pairings of `v` with the
tangent space. -/
theorem symplecticNormalRepresentative_normalClass_eq_sub_mfderiv_inverse
    [FiniteDimensional ℝ E] (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0)
    (a : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (ha : ∀ u w, a u w = SmoothBundleForm.eval₂ σ (f x) (mfderiv I J f x u) (mfderiv I J f x w))
    (v : TangentSpace J (f x)) :
    f.symplecticNormalRepresentative h x hn (f.normalClass x hn v) =
      v - mfderiv I J f x (a.inverse ((flat σ (f x) v).comp (mfderiv I J f x))) := by
  set d := mfderiv I J f x
  have hinv := isInvertible_of_eval₂_mfderiv f h x hn a ha
  apply (f.symplecticNormalRepresentative_eq_iff h x hn _ _).2
  refine ⟨SymplecticForm.mem_orthogonal_iff'.2 ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [ContinuousLinearMap.coe_coe]
    have hpair := DFunLike.congr_fun (hinv.self_apply_inverse ((flat σ (f x) v).comp d)) w
    rw [ContinuousLinearMap.comp_apply, flat_apply, ha] at hpair
    rw [IsNondegenerate.symplecticFormAt_apply, ← flat_apply, map_sub, sub_apply, flat_apply,
      flat_apply]
    exact sub_eq_zero.2 hpair.symm
  · rw [map_sub, normalClass_mfderiv, sub_zero]

end Pointwise

/-! ### The normal symplectic form -/

section NormalForm

/-- The symplectic complement of a symplectic tangent space is symplectic, so `σ` restricts to it
nondegenerately. -/
private theorem nondegenerate_restrict_orthogonal (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    ((hσ.symplecticFormAt (f x)).toBilinForm.restrict
      ((hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn))).Nondegenerate :=
  (SymplecticForm.isSymplectic_orthogonal_iff.2
    (isSymplectic_tangentRange f h x hn)).nondegenerate_restrict

/-- The **normal symplectic form** of a symplectic submanifold embedding at `x`: the linear
symplectic form on the normal space under which two normal classes pair as their symplectic
representatives under `σ`. It is the restriction of `σ` to the symplectic complement of the
tangent space, transported to the normal space. -/
def symplecticNormalForm (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) :
    SymplecticForm (f.NormalSpace x hn) :=
  ((hσ.symplecticFormAt (f x)).restrict _ (nondegenerate_restrict_orthogonal f h x hn)).transport
    (f.normalSpaceSymplecticComplementEquiv h x hn).symm.toLinearEquiv

/-- The normal symplectic form pairs two normal classes as their symplectic representatives. -/
@[simp]
theorem symplecticNormalForm_apply (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v w : f.NormalSpace x hn) :
    f.symplecticNormalForm h x hn v w =
      SmoothBundleForm.eval₂ σ (f x) (f.symplecticNormalRepresentative h x hn v)
        (f.symplecticNormalRepresentative h x hn w) := by
  rw [symplecticNormalForm, SymplecticForm.transport_apply, SymplecticForm.restrict_apply,
    IsNondegenerate.symplecticFormAt_apply]
  rfl

/-- The normal symplectic form evaluates on the class of any ambient tangent vector `v` as `σ` on
`v` and the symplectic representative of the second class: the tangential part of `v` pairs to
zero with the symplectic complement. -/
theorem symplecticNormalForm_normalClass (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : TangentSpace J (f x))
    (w : f.NormalSpace x hn) :
    f.symplecticNormalForm h x hn (f.normalClass x hn v) w =
      SmoothBundleForm.eval₂ σ (f x) v (f.symplecticNormalRepresentative h x hn w) := by
  rw [symplecticNormalForm_apply]
  -- The two representatives of the class of `v` differ by a tangent vector `d u`.
  obtain ⟨u, hu⟩ := (f.normalClass_eq_iff x hn _ _).1
    (f.normalClass_symplecticNormalRepresentative h x hn (f.normalClass x hn v))
  rw [← sub_add_cancel (f.symplecticNormalRepresentative h x hn (f.normalClass x hn v)) v,
    ← hu, ContinuousLinearMap.coe_coe]
  simp only [← flat_apply, map_add, add_apply]
  rw [flat_apply, eval₂_mfderiv_symplecticNormalRepresentative, zero_add]

/-- On classes of vectors of the symplectic complement, the normal symplectic form is `σ`. -/
theorem symplecticNormalForm_normalClass_normalClass (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (x : M) (hn : n ≠ 0) (v : TangentSpace J (f x))
    {w : TangentSpace J (f x)}
    (hw : w ∈ (hσ.symplecticFormAt (f x)).orthogonal (f.tangentRange x hn)) :
    f.symplecticNormalForm h x hn (f.normalClass x hn v) (f.normalClass x hn w) =
      SmoothBundleForm.eval₂ σ (f x) v w := by
  rw [symplecticNormalForm_normalClass,
    symplecticNormalRepresentative_normalClass_of_mem _ h x hn hw]

end NormalForm

/-! ### Smoothness of the symplectic representatives -/

section Smooth

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] {m : ℕ∞ω}

/-- **Smooth symplectic projection.** The symplectic representative of the normal class of an
ambient tangent vector, the projection onto the symplectic complement of the tangent space along
it, is `C^m` on the pulled-back ambient tangent bundle for a `C^n` symplectic submanifold
embedding with `m + 1 ≤ n`. Both the base point and the ambient tangent vector may vary. -/
theorem contMDiff_symplecticNormalRepresentative_normalClass (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f p.proj, f.symplecticNormalRepresentative h p.proj hn (f.normalClass p.proj hn p.2)⟩ :
          TangentBundle J N)) := by
  have hmtop : m ≤ ∞ := le_self_add.trans hm'
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold J 1 N := .of_le (n := ∞) (by simp)
  have : IsManifold I (m + 1) M := .of_le hm'
  have : IsManifold J (m + 1) N := .of_le hm'
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  have hbase : ContMDiff (I.prod 𝓘(ℝ, V)) I m
      (π V ((f : M → N) *ᵖ (TangentSpace J))) := contMDiff_proj _
  have hlift : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (Pullback.lift (f : M → N)) :=
    ((Pullback.contMDiff_iff fc fc.contMDiff
      (E := fun y : N ↦ TangentSpace J y)).mp contMDiff_id).2
  -- The flat map of the pulled-back form `f^* σ` is a `C^m` section, invertible at every point.
  let τ := TauCeti.mpullback I J f σ.1
  have hτ : IsSmoothForm I m τ :=
    IsSmoothForm.mpullback ((isSmoothForm_def m σ.1).2 ((SmoothForm.contMDiff σ).of_le hmtop))
      (f.contMDiff.of_le hm)
  let a : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun x ↦ ContinuousAlternatingMap.flatL ℝ E ℝ (τ x)
  have ha (x : M) (u w : TangentSpace I x) :
      a x u w = SmoothBundleForm.eval₂ σ (f x) (mfderiv I J f x u) (mfderiv I J f x w) := by
    refine ((ContinuousAlternatingMap.flatL_apply_apply (E := E) (τ x) u w).trans
      (mpullback_apply_pair f σ.1 x u w)).trans ?_
    rw [SmoothBundleForm.eval₂_apply]
  have hacont : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (a x)) :=
    fun x₀ ↦ contMDiffAt_sectionAlong_flatL (b := fun x ↦ x) (σ := τ) (hτ.contMDiff x₀)
  have hainv (x : M) : (a x).IsInvertible := isInvertible_of_eval₂_mfderiv f h x hn (a x) (ha x)
  -- Pair the ambient vector with the differential under `σ`, then pull the covector back.
  let φ := fun (x : M) (v : TangentSpace J (f x)) ↦ (flat σ (f x) v).comp (mfderiv I J f x)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, φ p.proj p.2⟩ : CotangentBundle I M)) :=
    CotangentBundle.contMDiff_mk_comp_mfderiv
      (Ψ := fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f q.proj, flat σ (f q.proj) q.2⟩ : CotangentBundle J N))
      (fun _ ↦ rfl)
      (((contMDiff_flat σ).of_le hmtop |>.comp (fc.contMDiff.comp hbase)).clm_bundle_apply hlift)
      hbase f.contMDiff hm
  -- Invert the flat map and push the resulting tangential component forward.
  let u := fun (x : M) (v : TangentSpace J (f x)) ↦ (a x).inverse (φ x v)
  have hu : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, u p.proj p.2⟩ : TangentBundle I M)) :=
    ((hacont.clm_bundle_inverse hainv).comp hbase).clm_bundle_apply hφ
  have ht := (f.contMDiff.contMDiff_tangentMap (by simpa using hm)).comp hu
  have hneg := (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace ht
  have hsub := hlift.add_sectionAlong hneg
  have hformula (x : M) (v : TangentSpace J (f x)) :
      f.symplecticNormalRepresentative h x hn (f.normalClass x hn v) =
        v + (-1 : ℝ) • mfderiv I J f x (u x v) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact f.symplecticNormalRepresentative_normalClass_eq_sub_mfderiv_inverse h x hn (a x)
      (ha x) v
  exact hsub.congr fun p ↦ congrArg (TotalSpace.mk (f p.proj)) (hformula p.proj p.2)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Smooth symplectic representatives.** The map taking an intrinsic normal vector of a
symplectic submanifold embedding to its symplectic representative in the ambient tangent bundle
is `C^m` for a `C^n` embedding with `m + 1 ≤ n`. -/
theorem contMDiff_symplecticNormalRepresentative (f : SmoothEmbedding I J n M N)
    (h : hσ.HasSymplecticTangentImages I f) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm' : m + 1 ≤ ∞)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := ∞) (by simp)
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨f p.proj, f.symplecticNormalRepresentative h p.proj hn p.2⟩ : TangentBundle J N)) := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold I (m + 1) M := .of_le hm'
  have : IsManifold J (m + 1) N := .of_le hm'
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  convert f.contMDiff_symplecticNormalRepresentative_normalClass h hn hm hm' using 1
  funext p
  rw [Function.comp_apply, normalQuotientMap_apply]

end Smooth

end TauCeti.SmoothEmbedding
