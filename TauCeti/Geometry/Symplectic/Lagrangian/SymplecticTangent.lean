/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

/-!
# Maps with symplectic tangent images

Let `σ` be a fiberwise nondegenerate smooth two-form on `M`, so that every tangent space
`T_y M` carries the linear symplectic form `hσ.symplecticFormAt y`. A map `f : N → M` **has
symplectic tangent images** when, at every point `x` of `N`, its tangent image `df_x(T_x N)`, the
range of the differential, is a symplectic subspace of `T_(f x) M` in the sense of
`TauCeti.SymplecticForm.IsSymplectic`: it meets its symplectic complement only in zero,
equivalently `σ` restricts to it nondegenerately. This is the fourth of the tangent-image
predicates, beside the isotropic, coisotropic and Lagrangian maps of
`TauCeti.Geometry.Symplectic.Lagrangian.Manifold`. It is not called a *symplectic map*, a term
which conventionally means a map pulling one symplectic form back to another.

As for the other three predicates, the differential is `mfderiv`, which is `0` where `f` is not
differentiable, the source is an arbitrary charted space, and `f` need not be injective, so the
predicate applies to embedded and immersed submanifolds alike, through any parametrization.

* Pointwise, `f` has symplectic tangent images exactly when a tangent vector `df_x v` pairing to
  zero with every `df_x w` is itself zero
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_iff`).
* A smooth map pulls `σ` back to a nondegenerate form exactly when its differentials are injective
  and its tangent images are symplectic (`isNondegenerate_mpullback_iff`). So an immersion with
  symplectic tangent images pulls a symplectic form back to a symplectic form; for embeddings
  this is the condition defining symplectic submanifolds.
* The predicate depends only on the tangent images, hence not on the parametrization, and it is
  transported by symplectomorphisms of the target.
* A symplectic tangent image has even dimension, so a map with symplectic tangent images and an
  injective differential at some point comes from an even-dimensional manifold. In a
  finite-dimensional target each tangent image splits off together with its symplectic complement,
  `T_(f x) M = df_x(T_x N) ⊕ df_x(T_x N)^σ`; for an embedding these complements are the fibres of
  the symplectic normal bundle.
* A map with surjective differentials, such as a local diffeomorphism, has symplectic tangent
  images. In a finite-dimensional symplectic vector space with its constant form, a continuous
  linear map has symplectic tangent images exactly when its range is a symplectic subspace; for
  instance the inclusion of the first factor of a direct sum of symplectic vector spaces does.

## Main declarations

* `TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages`: the predicate.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isNondegenerate_mpullback_iff`: a smooth map pulls `σ`
  back to a nondegenerate form exactly when its differentials are injective and its tangent images
  are symplectic.
* `TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.isSymplectic_mpullback`: such a
  map pulls a symplectic form back to a symplectic form.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_comp_diffeomorph_iff` and
  `hasSymplecticTangentImages_diffeomorph_comp_iff`: reparametrization and transport.
* `TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.even_finrank`: the source
  dimension is even.
* `TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.isCompl`: the splitting of the
  ambient tangent space.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (symplectic subspaces and complements).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Chapters 1 and 3.
-/

public section

noncomputable section

open Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : N → M}

variable (J) in
/-- A map `f : N → M` **has symplectic tangent images** for a nondegenerate two-form `σ` when
every tangent image `df_x(T_x N)` is a symplectic subspace of `(T_(f x) M, σ_(f x))`: it meets its
symplectic complement only in zero, equivalently `σ_(f x)` restricts to it nondegenerately.

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not
differentiable; the zero subspace is symplectic, so there the condition holds trivially. -/
def HasSymplecticTangentImages (f : N → M) : Prop :=
  ∀ x, (hσ.symplecticFormAt (f x)).IsSymplectic (LinearMap.range (mfderiv J I f x).toLinearMap)

variable {hσ}

/-- Having symplectic tangent images is the pointwise condition on the tangent images. -/
theorem hasSymplecticTangentImages_iff_forall :
    hσ.HasSymplecticTangentImages J f ↔
      ∀ x, (hσ.symplecticFormAt (f x)).IsSymplectic
        (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  Iff.rfl

/-- A map has symplectic tangent images exactly when, at every point, a pushed-forward tangent
vector on which `σ` pairs to zero with every pushed-forward tangent vector is itself zero. -/
theorem hasSymplecticTangentImages_iff :
    hσ.HasSymplecticTangentImages J f ↔
      ∀ x (v : TangentSpace J x),
        (∀ w, SmoothBundleForm.eval₂ σ (f x) (mfderiv J I f x v) (mfderiv J I f x w) = 0) →
          mfderiv J I f x v = 0 := by
  refine forall_congr' fun x ↦ ?_
  simp only [SymplecticForm.isSymplectic_iff_disjoint, Submodule.disjoint_def,
    LinearMap.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    SymplecticForm.mem_orthogonal_iff', symplecticFormAt_apply, ContinuousLinearMap.coe_coe]

/-- **Symplectic tangent images and the pulled-back form.** A smooth map pulls `σ` back to a
nondegenerate form exactly when its differentials are injective and its tangent images are
symplectic. In particular an immersion has symplectic tangent images exactly when the pulled-back
form is nondegenerate. -/
theorem isNondegenerate_mpullback_iff [IsManifold J ∞ N] (hf : ContMDiff J I ∞ f) :
    SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback f hf σ) ↔
      hσ.HasSymplecticTangentImages J f ∧ ∀ x, Function.Injective (mfderiv J I f x) := by
  simp only [isNondegenerate_iff_separatingLeft, hasSymplecticTangentImages_iff,
    SmoothForm.eval₂_mpullback, ← forall_and]
  refine forall_congr' fun x ↦ ⟨fun h ↦ ⟨fun v hv ↦ ?_, ?_⟩,
    fun ⟨hs, hinj⟩ v hv ↦ (injective_iff_map_eq_zero _).1 hinj v (hs v hv)⟩
  · rw [h v hv, map_zero]
  · -- A vector killed by the differential pairs to zero with everything, so it is zero.
    refine (injective_iff_map_eq_zero _).2 fun v hv ↦ h v fun w ↦ ?_
    rw [hv, ← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply]

/-- A smooth map with injective differentials and symplectic tangent images pulls a symplectic form
back to a symplectic form. -/
theorem HasSymplecticTangentImages.isSymplectic_mpullback [IsManifold J ∞ N]
    (h : hσ.HasSymplecticTangentImages J f) (hσs : σ.IsSymplectic) (hf : ContMDiff J I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback f hf σ) :=
  ⟨hσs.isClosed.mpullback f hf, (isNondegenerate_mpullback_iff hf).2 ⟨h, hinj⟩⟩

/-- A map whose differentials are all surjective, such as a local diffeomorphism, has symplectic
tangent images. -/
theorem hasSymplecticTangentImages_of_surjective
    (hf : ∀ x, Function.Surjective (mfderiv J I f x)) : hσ.HasSymplecticTangentImages J f :=
  fun x ↦ by
    rw [LinearMap.range_eq_top.2 (hf x)]
    exact SymplecticForm.isSymplectic_top

/-! ### Reparametrization and transport -/

section Reparametrization

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map has symplectic tangent images. -/
theorem hasSymplecticTangentImages_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    hσ.HasSymplecticTangentImages K (f ∘ φ) ↔ hσ.HasSymplecticTangentImages J f := by
  simp only [HasSymplecticTangentImages, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

end Reparametrization

section Transport

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate}

/-- **Transport by symplectomorphisms.** If `ψ` pulls `σ₂` back to `σ`, then `ψ ∘ f` has
symplectic tangent images for `σ₂` exactly when `f` has symplectic tangent images for `σ`. -/
theorem hasSymplecticTangentImages_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.HasSymplecticTangentImages J (ψ ∘ f) ↔ hσ.HasSymplecticTangentImages J f := by
  refine forall_congr' fun x ↦ ?_
  rw [ψ.range_mfderiv_diffeomorph_comp (by simp), Function.comp_apply,
    ← hσ.symplecticFormAt_transport ψ hψ, SymplecticForm.isSymplectic_map_transport_iff]

end Transport

/-! ### Dimension and the symplectic complement -/

/-- A symplectic tangent image of a map from a finite-dimensional manifold has even dimension. -/
theorem HasSymplecticTangentImages.even_finrank_range [FiniteDimensional ℝ E']
    (h : hσ.HasSymplecticTangentImages J f) (x : N) :
    Even (finrank ℝ (LinearMap.range (mfderiv J I f x).toLinearMap)) :=
  ((hσ.symplecticFormAt (f x)).restrict _ (h x).nondegenerate_restrict).even_finrank

/-- A map with symplectic tangent images and an injective differential at some point comes from an
even-dimensional manifold. -/
theorem HasSymplecticTangentImages.even_finrank [FiniteDimensional ℝ E']
    (h : hσ.HasSymplecticTangentImages J f) {x : N}
    (hx : Function.Injective (mfderiv J I f x)) : Even (finrank ℝ E') := by
  have := h.even_finrank_range x
  rwa [LinearMap.finrank_range_of_inj hx, finrank_tangentSpace] at this

/-- In a finite-dimensional manifold, each symplectic tangent image splits the ambient tangent
space together with its symplectic complement, `T_(f x) M = df_x(T_x N) ⊕ df_x(T_x N)^σ`. -/
theorem HasSymplecticTangentImages.isCompl [FiniteDimensional ℝ E]
    (h : hσ.HasSymplecticTangentImages J f) (x : N) :
    IsCompl (LinearMap.range (mfderiv J I f x).toLinearMap)
      ((hσ.symplecticFormAt (f x)).orthogonal (LinearMap.range (mfderiv J I f x).toLinearMap)) :=
  (h x).isCompl

end IsNondegenerate

end SmoothTwoForm

/-! ### Linear maps of symplectic vector spaces -/

namespace SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- In a finite-dimensional symplectic vector space with its constant symplectic form, a
continuous linear map has symplectic tangent images exactly when its range is a symplectic
subspace. -/
theorem hasSymplecticTangentImages_continuousLinearMap_iff (σ₀ : SymplecticForm W)
    (L : V →L[ℝ] W) :
    (isNondegenerate_constSmooth σ₀).HasSymplecticTangentImages 𝓘(ℝ, V) L ↔
      σ₀.IsSymplectic (LinearMap.range L.toLinearMap) := by
  simp only [SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages,
    isNondegenerate_constSmooth_symplecticFormAt, ContinuousLinearMap.mfderiv_eq]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- The inclusion `v ↦ (v, 0)` of the first factor of a direct sum of finite-dimensional
symplectic vector spaces has symplectic tangent images for the constant direct-sum form. -/
theorem hasSymplecticTangentImages_inl [FiniteDimensional ℝ V] (ω₁ : SymplecticForm V)
    (ω₂ : SymplecticForm W) :
    (isNondegenerate_constSmooth (ω₁.prod ω₂)).HasSymplecticTangentImages 𝓘(ℝ, V)
      (ContinuousLinearMap.inl ℝ V W) := by
  rw [hasSymplecticTangentImages_continuousLinearMap_iff, ContinuousLinearMap.coe_inl,
    LinearMap.range_eq_map, Submodule.map_inl]
  exact isSymplectic_top.prod isSymplectic_bot

end SymplecticForm

end TauCeti
