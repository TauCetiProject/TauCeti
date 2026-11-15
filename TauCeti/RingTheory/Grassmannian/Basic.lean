/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Grassmannian

-- Proof-only: the body of `Module.Grassmannian.baseChangeMkQ` is not exposed.
import all Mathlib.RingTheory.Grassmannian

/-!
# Complements to Mathlib's Grassmannian

Let `M` be a module over a commutative ring `R`. Mathlib's `Module.Grassmannian R M k`, written
`G(k, M; R)`, is the set of submodules `N ≤ M` whose quotient `M ⧸ N` is finite projective of
constant rank `k`. This file adds general facts about it: the kernel of a surjection onto a
finite projective module of constant rank `k` is a point of `G(k, M; R)`, a point of the
Grassmannian of a finite module is finitely generated, and the behaviour of
`Module.Grassmannian.baseChangeMkQ`, the map underlying base change of points, on pure tensors and
on vectors coming from `A ⊗[R] M`. In particular a vector of a point maps into each of its base
changes, and, when `B` is an `A`-algebra, the base change of `N` along the structure map is the
kernel of `baseChangeMkQ B N` for the given algebra structure on `B`, and in general the base
change of `N` is spanned by the image of `N`. Base change along an injective map is injective on
points.

A linear equivalence `M ≃ M'` identifies `G(k, M; R)` with `G(k, M'; R)`. For an `R`-algebra `R'`
and an `R'`-algebra `A`, the isomorphism `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M` therefore identifies the
points over `A` of the Grassmannian of the base change `R' ⊗[R] M` with those of the Grassmannian
of `M`, naturally in `A`. This is the functorial form of base change of the Grassmannian scheme.

## Main definitions

* `Module.Grassmannian.ofSurjective`: the kernel of a surjection onto a finite projective module
  of constant rank `k`, as a point of `G(k, M; R)`.
* `LinearEquiv.grassmannianCongr`: a linear equivalence `M ≃ₗ[R] M'` identifies `G(k, M; R)` with
  `G(k, M'; R)`.
* `Module.Grassmannian.baseChangeEquiv`: the points of the Grassmannian of `R' ⊗[R] M` over an
  `R'`-algebra `A` are the points of the Grassmannian of `M` over `A`.

## Main results

* `Module.Grassmannian.fg_toSubmodule`: over a finite module, every point is finitely generated.
* `Module.Grassmannian.baseChangeMkQ_tmul`: `baseChangeMkQ B N` sends `b ⊗ₜ m` to
  `b ⊗ₜ [1 ⊗ₜ m]`.
* `Module.Grassmannian.baseChangeMkQ_rTensor`: `baseChangeMkQ B N` sends the image of
  `x ∈ A ⊗[R] M` to `1 ⊗ₜ [x]`.
* `Module.Grassmannian.ker_baseChangeMkQ`: the kernel of `baseChangeMkQ B N` is spanned by the
  image of `N`, and `Module.Grassmannian.ker_baseChangeMkQ_le_ker_iff`: a linear map vanishes on it
  exactly when it vanishes on the image of `N`.
* `Module.Grassmannian.map_toAlgHom_toSubmodule`: the base change of a point along the structure
  map of an `A`-algebra `B` is the kernel of `baseChangeMkQ B N`.
* `Module.Grassmannian.map_toSubmodule_eq_span`: the base change of a point is spanned by its
  image.
* `Module.Grassmannian.rTensor_mem_map`: a vector of a point maps into every base change of it.
* `Module.Grassmannian.rTensor_mem_map_iff_of_injective` and
  `Module.Grassmannian.map_injective`: along an injective map, a point is recovered from its base
  change.
* `Module.Grassmannian.baseChangeEquiv_map`: `baseChangeEquiv` is natural in the algebra.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section OfSurjective

variable {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]

/-- The kernel of a surjection `φ : M → P` onto a finite projective module `P` of constant rank
`k`, as a point of `G(k, M; R)`. -/
noncomputable def ofSurjective (φ : M →ₗ[R] P) (hφ : Function.Surjective φ)
    (hP : ∀ p, rankAtStalk (R := R) P p = k) : G(k, M; R) where
  toSubmodule := LinearMap.ker φ
  finite_quotient := Module.Finite.equiv (φ.quotKerEquivOfSurjective hφ).symm
  projective_quotient := Module.Projective.of_equiv (φ.quotKerEquivOfSurjective hφ).symm
  rankAtStalk_eq p := by
    rw [rankAtStalk_eq_of_equiv (φ.quotKerEquivOfSurjective hφ)]
    exact hP p

@[simp]
theorem toSubmodule_ofSurjective (φ : M →ₗ[R] P) (hφ : Function.Surjective φ)
    (hP : ∀ p, rankAtStalk (R := R) P p = k) :
    (ofSurjective φ hφ hP).toSubmodule = LinearMap.ker φ :=
  (rfl)

end OfSurjective

/-- For `M` finite over `R`, a point `N` of `G(k, M; R)` is a finitely generated submodule: its
quotient is finite projective, hence finitely presented. -/
theorem fg_toSubmodule [Module.Finite R M] (N : G(k, M; R)) : N.toSubmodule.FG := by
  have : Module.FinitePresentation R (M ⧸ N.toSubmodule) :=
    Module.finitePresentation_of_projective _ _
  simpa using Module.FinitePresentation.fg_ker N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective

@[simp]
theorem baseChangeMkQ_tmul {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M)) (b : B) (m : M) :
    baseChangeMkQ B N (b ⊗ₜ m) = b ⊗ₜ Submodule.Quotient.mk (1 ⊗ₜ m) := by
  simp [baseChangeMkQ]

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The base change map `B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ N)` sends the image of `x ∈ A ⊗[R] M`
to `1 ⊗ₜ [x]`. -/
@[simp]
theorem baseChangeMkQ_rTensor [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M))
    (x : A ⊗[R] M) :
    baseChangeMkQ B N ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x) =
      (1 : B) ⊗ₜ N.mkQ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, tmul_add]

/-- By right exactness of the tensor product, the kernel of `baseChangeMkQ B N` is spanned over `B`
by the image of `N`. -/
theorem ker_baseChangeMkQ [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M)) :
    LinearMap.ker (baseChangeMkQ B N) =
      Submodule.span B ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M '' N) := by
  have hker : LinearMap.ker (N.mkQ.baseChange B) = N.baseChange B := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_lTensor, ← LinearMap.mem_ker, lTensor_mkQ,
      Submodule.baseChange, LinearMap.mem_range, LinearMap.mem_range]
    simp only [LinearMap.baseChange_eq_lTensor]
  have hcancel (x : A ⊗[R] M) : AlgebraTensorModule.cancelBaseChange R A B B M ((1 : B) ⊗ₜ x) =
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => simp [Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => simp [tmul_add, hx, hy]
  rw [baseChangeMkQ, LinearMap.ker_comp, hker, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.symm_symm, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    ← Set.image_comp]
  exact congrArg _ (Set.image_congr fun x _ ↦ hcancel x)

/-- A `B`-linear map `Φ` out of `B ⊗[R] M` vanishes on the kernel of `baseChangeMkQ B N` exactly
when it vanishes on the image of `N`. -/
theorem ker_baseChangeMkQ_le_ker_iff [Algebra A B] [IsScalarTower R A B]
    (N : Submodule A (A ⊗[R] M)) {Y : Type*} [AddCommMonoid Y] [Module B Y]
    (Φ : B ⊗[R] M →ₗ[B] Y) :
    LinearMap.ker (baseChangeMkQ B N) ≤ LinearMap.ker Φ ↔
      ∀ x ∈ N, Φ ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x) = 0 := by
  simp only [ker_baseChangeMkQ, Submodule.span_le, Set.subset_def, SetLike.mem_coe,
    LinearMap.mem_ker, Set.forall_mem_image]

/-- With an algebra structure in place, the base change `map f N` along the structure map
`f : A → B` is the kernel of `baseChangeMkQ B N`. -/
theorem map_toAlgHom_toSubmodule [Algebra A B] [IsScalarTower R A B] (N : G(k, A ⊗[R] M; A)) :
    (map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      LinearMap.ker (baseChangeMkQ B N.toSubmodule) := by
  have h : (IsScalarTower.toAlgHom R A B).toRingHom.toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [map_toSubmodule]
  -- the two sides differ only in the algebra structure, `f.toAlgebra` against the given one, and
  -- in the proofs of `IsScalarTower` built on it
  congr 2 <;> first | rw [h] | exact proof_irrel_heq _ _

/-- **The base change of a point is spanned by its image.** For `f : A →ₐ[R] B`, the base change
`map f N` of `N ∈ G(k, A ⊗[R] M; A)` is the `B`-submodule of `B ⊗[R] M` spanned by the image of
`N` under `f ⊗ id`. -/
theorem map_toSubmodule_eq_span (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    (map f N).toSubmodule = Submodule.span B (f.toLinearMap.rTensor M '' N.toSubmodule) := by
  algebraize [f.toRingHom]
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  rw [← hf, map_toAlgHom_toSubmodule, ker_baseChangeMkQ]

/-- A vector of `A ⊗[R] M` lying in a point `N` of the Grassmannian maps into every base change
of `N`. -/
theorem rTensor_mem_map (f : A →ₐ[R] B) {N : G(k, A ⊗[R] M; A)} {x : A ⊗[R] M}
    (hx : x ∈ N.toSubmodule) : f.toLinearMap.rTensor M x ∈ (map f N).toSubmodule := by
  algebraize [f.toRingHom]
  rw [map_toSubmodule, LinearMap.mem_ker]
  -- `algebraize` makes `f` the structure map of `B` as an `A`-algebra, so `f` is the map
  -- `IsScalarTower.toAlgHom R A B` that appears in `baseChangeMkQ_rTensor`
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  have := baseChangeMkQ_rTensor (B := B) N.toSubmodule x
  rw [hf] at this
  rw [this, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx, tmul_zero]

/-- **A point is recovered from its base change along an injective map.** For an injective
`f : A →ₐ[R] B`, a vector of `A ⊗[R] M` lies in `N` exactly when its image lies in the base change
of `N` to `B`. -/
theorem rTensor_mem_map_iff_of_injective {f : A →ₐ[R] B} (hf : Function.Injective f)
    {N : G(k, A ⊗[R] M; A)} {x : A ⊗[R] M} :
    f.toLinearMap.rTensor M x ∈ (map f N).toSubmodule ↔ x ∈ N.toSubmodule := by
  algebraize [f.toRingHom]
  have hf' : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  have hmk := baseChangeMkQ_rTensor (B := B) N.toSubmodule x
  rw [hf'] at hmk
  rw [map_toSubmodule, LinearMap.mem_ker, hmk]
  -- `q ↦ 1 ⊗ₜ q` is injective on the flat quotient, so `1 ⊗ₜ [x]` vanishes exactly when `[x]` does
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  simpa using map_eq_zero_iff _
    (Module.Flat.tensorProduct_mk_injective (R := A) (S := B) _) (x := N.mkQ x)

/-- **Base change along an injective map is injective on points.** -/
theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) :
    Function.Injective (map (k := k) (M := M) f) := fun N N' h ↦ by
  ext x
  rw [← rTensor_mem_map_iff_of_injective hf, h, rTensor_mem_map_iff_of_injective hf]

end BaseChange

section Congr

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- **Transport of points along a linear equivalence.** A linear equivalence `e : M ≃ₗ[R] M'`
identifies `G(k, M; R)` with `G(k, M'; R)` by sending `N` to its image `e(N)`
(`LinearEquiv.toSubmodule_grassmannianCongr_apply`), whose quotient is isomorphic to `M ⧸ N`. -/
noncomputable def _root_.LinearEquiv.grassmannianCongr (e : M ≃ₗ[R] M') :
    G(k, M; R) ≃ G(k, M'; R) where
  toFun N := ofSurjective (N.toSubmodule.mkQ ∘ₗ e.symm.toLinearMap)
    (N.toSubmodule.mkQ_surjective.comp e.symm.surjective) N.rankAtStalk_eq
  invFun N := ofSurjective (N.toSubmodule.mkQ ∘ₗ e.toLinearMap)
    (N.toSubmodule.mkQ_surjective.comp e.surjective) N.rankAtStalk_eq
  left_inv N := by ext; simp [LinearMap.ker_comp]
  right_inv N := by ext; simp [LinearMap.ker_comp]

@[simp]
theorem _root_.LinearEquiv.toSubmodule_grassmannianCongr_apply (e : M ≃ₗ[R] M')
    (N : G(k, M; R)) :
    (e.grassmannianCongr N).toSubmodule = N.toSubmodule.map e.toLinearMap := by
  simp [LinearEquiv.grassmannianCongr, LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]

@[simp]
theorem _root_.LinearEquiv.grassmannianCongr_symm (e : M ≃ₗ[R] M') :
    (e.grassmannianCongr (k := k)).symm = e.symm.grassmannianCongr :=
  Equiv.ext fun N ↦ Module.Grassmannian.ext <| by
    simp [LinearEquiv.grassmannianCongr, LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]

end Congr

section BaseChangeEquiv

variable (R' : Type*) [CommRing R'] [Algebra R R'] {A B : Type w} [CommRing A] [Algebra R A]
  [Algebra R' A] [IsScalarTower R R' A] [CommRing B] [Algebra R B] [Algebra R' B]
  [IsScalarTower R R' B]

/-- **Points of the Grassmannian of a base change.** For an `R`-algebra `R'` and an
`R'`-algebra `A`, the points of the Grassmannian of `R' ⊗[R] M` over `A` are the points of the
Grassmannian of `M` over `A`, through the isomorphism `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`. This
bijection is natural in `A` (`Module.Grassmannian.baseChangeEquiv_map`). -/
noncomputable def baseChangeEquiv :
    G(k, A ⊗[R'] (R' ⊗[R] M); A) ≃ G(k, A ⊗[R] M; A) :=
  (AlgebraTensorModule.cancelBaseChange R R' A A M).grassmannianCongr

@[simp]
theorem toSubmodule_baseChangeEquiv (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    (baseChangeEquiv R' N).toSubmodule =
      N.toSubmodule.map (AlgebraTensorModule.cancelBaseChange R R' A A M).toLinearMap :=
  LinearEquiv.toSubmodule_grassmannianCongr_apply _ N

/-- **Naturality of `baseChangeEquiv`.** Base change of points along an `R'`-algebra map
`f : A → B` corresponds to base change along `f` as an `R`-algebra map. -/
theorem baseChangeEquiv_map (f : A →ₐ[R'] B) (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    baseChangeEquiv R' (map f N) = map (f.restrictScalars R) (baseChangeEquiv R' N) := by
  ext : 1
  simp only [toSubmodule_baseChangeEquiv, map_toSubmodule_eq_span, Submodule.map_span,
    Submodule.map_coe, ← Set.image_comp]
  refine congrArg _ (Set.image_congr' fun x ↦ ?_)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  | tmul a y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [Function.comp_apply, tmul_add, map_add] at hy hz ⊢; rw [hy, hz]
    | tmul r m => simp

end BaseChangeEquiv

end Module.Grassmannian
