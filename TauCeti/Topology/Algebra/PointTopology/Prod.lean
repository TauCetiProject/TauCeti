/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Point topology for products of coefficient algebras and base change

For an affine `k`-algebra `A`, taking `k`-algebra homomorphisms into a binary product `R₁ × R₂` or
an indexed product `∀ i, R i` of topological `k`-algebras identifies the evaluation point space
with the product of the factor point spaces, with no finiteness, separation, or topological-semiring
hypotheses on `A` or the coefficient algebras. When the source is a `k`-bialgebra `H`, the same
identifications respect the convolution multiplication and upgrade to topological monoid (hence
topological group, when `H` is a Hopf algebra) isomorphisms on `WithConv`.

This file also upgrades two coordinate-side point equivalences to topological monoid isomorphisms:

* `BialgEquiv.mapDomainContinuousMulEquiv`: contravariant transport of points along a bialgebra
  isomorphism `H₁ ≃ₐc[k] H₂`.
* `TauCeti.PointTopology.baseChangePointsContinuousMulEquiv`: the scalar-extension adjunction
  `WithConv (A →ₐ[k] R) ≃ₜ* WithConv (K ⊗[k] A →ₐ[K] R)` over a topological semiring `R`.

## Main declarations

* `TauCeti.PointTopology.prodHomeomorph`, `TauCeti.PointTopology.piHomeomorph`: homeomorphisms for
  points valued in binary and indexed products of coefficient algebras.
* `TauCeti.PointTopology.prodPointsMulEquiv`, `TauCeti.PointTopology.prodPointsContinuousMulEquiv`:
  convolution monoid and topological monoid isomorphisms for binary products of coefficient
  algebras, with factor embeddings `inlPoints` and `inrPoints`.
* `TauCeti.PointTopology.piPointsMulEquiv`, `TauCeti.PointTopology.piPointsContinuousMulEquiv`:
  convolution monoid and topological monoid isomorphisms for indexed products of coefficient
  algebras.
* `BialgEquiv.mapDomainContinuousMulEquiv`: topological monoid isomorphism induced on points by a
  bialgebra equivalence.
* `TauCeti.PointTopology.baseChangePointsContinuousMulEquiv`: topological monoid isomorphism for
  base change of bialgebra points.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
-/

public section

open Topology TensorProduct WithConv

namespace TauCeti.PointTopology

section Semiring

variable (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]

section Prod

variable (R₁ R₂ : Type*) [Semiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [Semiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

/-- Points valued in a binary product of topological algebras are homeomorphic to the product of
the two point spaces. -/
noncomputable def prodHomeomorph :
    (A →ₐ[k] R₁ × R₂) ≃ₜ (A →ₐ[k] R₁) × (A →ₐ[k] R₂) where
  toEquiv := (AlgHom.prodEquiv (R := k) (A := A) (B := R₁) (C := R₂)).symm
  continuous_toFun :=
    (continuous_map_codomain (AlgHom.fst k R₁ R₂) continuous_fst).prodMk
      (continuous_map_codomain (AlgHom.snd k R₁ R₂) continuous_snd)
  continuous_invFun := continuous_iff.2 fun a ↦
    ((continuous_eval a).comp continuous_fst).prodMk
      ((continuous_eval a).comp continuous_snd)

/-- Projecting `prodHomeomorph` to the first factor reads the first coordinate of a point. -/
@[simp]
theorem prodHomeomorph_apply_fst (x : A →ₐ[k] R₁ × R₂) (a : A) :
    (prodHomeomorph k A R₁ R₂ x).1 a = (x a).1 :=
  (rfl)

/-- Projecting `prodHomeomorph` to the second factor reads the second coordinate of a point. -/
@[simp]
theorem prodHomeomorph_apply_snd (x : A →ₐ[k] R₁ × R₂) (a : A) :
    (prodHomeomorph k A R₁ R₂ x).2 a = (x a).2 :=
  (rfl)

/-- The inverse of `prodHomeomorph` pairs two points coordinatewise. -/
@[simp]
theorem prodHomeomorph_symm_apply (p : (A →ₐ[k] R₁) × (A →ₐ[k] R₂)) (a : A) :
    (prodHomeomorph k A R₁ R₂).symm p a = (p.1 a, p.2 a) :=
  (rfl)

end Prod

section Pi

variable {ι : Type*} (R : ι → Type*) [∀ i, Semiring (R i)] [∀ i, Algebra k (R i)]
  [∀ i, TopologicalSpace (R i)]

/-- Points valued in an indexed product of topological algebras are homeomorphic to the indexed
product of the factor point spaces. -/
noncomputable def piHomeomorph :
    (A →ₐ[k] ∀ i, R i) ≃ₜ ∀ i, (A →ₐ[k] R i) where
  toFun x i := (Pi.evalAlgHom k R i).comp x
  invFun f := AlgHom.pi f
  left_inv _ := AlgHom.ext fun _ ↦ funext fun _ ↦ rfl
  right_inv _ := funext fun _ ↦ AlgHom.ext fun _ ↦ rfl
  continuous_toFun := continuous_pi fun i ↦
    continuous_map_codomain (Pi.evalAlgHom k R i) (continuous_apply i)
  continuous_invFun := continuous_iff.2 fun a ↦
    continuous_pi fun i ↦ (continuous_eval a).comp (continuous_apply i)

/-- Evaluating `piHomeomorph` at index `i` reads the `i`-th coordinate of a point. -/
@[simp]
theorem piHomeomorph_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) (a : A) :
    piHomeomorph k A R x i a = x a i :=
  (rfl)

/-- The inverse of `piHomeomorph` assembles a family of points coordinatewise. -/
@[simp]
theorem piHomeomorph_symm_apply (f : ∀ i, A →ₐ[k] R i) (a : A) (i : ι) :
    (piHomeomorph k A R).symm f a i = f i a :=
  (rfl)

end Pi

end Semiring

section BialgebraProd

variable (k H R₁ R₂ : Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [CommSemiring R₂] [Algebra k R₂]

/-- Convolution points of a bialgebra valued in `R₁ × R₂` split as the product of the convolution
monoids valued in `R₁` and `R₂`. -/
noncomputable def prodPointsMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toFun f := (AlgHom.mapValue (AlgHom.fst k R₁ R₂) f, AlgHom.mapValue (AlgHom.snd k R₁ R₂) f)
  invFun p := toConv (p.1.ofConv.prod p.2.ofConv)
  left_inv f := ofConv_injective <| AlgHom.ext fun h ↦ by simp
  right_inv p := Prod.ext
    (ofConv_injective <| AlgHom.ext fun h ↦ by simp)
    (ofConv_injective <| AlgHom.ext fun h ↦ by simp)
  map_mul' f g := Prod.ext (map_mul _ f g) (map_mul _ f g)

/-- The first component of `prodPointsMulEquiv` is post-composition with `AlgHom.fst`. -/
@[simp]
theorem prodPointsMulEquiv_fst (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsMulEquiv k H R₁ R₂ f).1 = AlgHom.mapValue (AlgHom.fst k R₁ R₂) f := by
  rw [prodPointsMulEquiv]
  rfl

/-- The second component of `prodPointsMulEquiv` is post-composition with `AlgHom.snd`. -/
@[simp]
theorem prodPointsMulEquiv_snd (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsMulEquiv k H R₁ R₂ f).2 = AlgHom.mapValue (AlgHom.snd k R₁ R₂) f := by
  rw [prodPointsMulEquiv]
  rfl

/-- The inverse of `prodPointsMulEquiv` pairs two points coordinatewise. -/
@[simp]
theorem prodPointsMulEquiv_symm_ofConv_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    ((prodPointsMulEquiv k H R₁ R₂).symm p).ofConv h = (p.1.ofConv h, p.2.ofConv h) := by
  rw [prodPointsMulEquiv]
  rfl

/-- Embedding the first factor `x ↦ (x, 1)` into convolution points valued in `R₁ × R₂`. -/
noncomputable def inlPoints :
    WithConv (H →ₐ[k] R₁) →* WithConv (H →ₐ[k] R₁ × R₂) :=
  (prodPointsMulEquiv k H R₁ R₂).symm.toMonoidHom.comp (MonoidHom.inl _ _)

/-- Embedding the second factor `y ↦ (1, y)` into convolution points valued in `R₁ × R₂`. -/
noncomputable def inrPoints :
    WithConv (H →ₐ[k] R₂) →* WithConv (H →ₐ[k] R₁ × R₂) :=
  (prodPointsMulEquiv k H R₁ R₂).symm.toMonoidHom.comp (MonoidHom.inr _ _)

@[simp]
theorem inlPoints_apply (x : WithConv (H →ₐ[k] R₁)) :
    inlPoints k H R₁ R₂ x = (prodPointsMulEquiv k H R₁ R₂).symm (x, 1) := by
  rw [inlPoints]
  rfl

@[simp]
theorem inrPoints_apply (y : WithConv (H →ₐ[k] R₂)) :
    inrPoints k H R₁ R₂ y = (prodPointsMulEquiv k H R₁ R₂).symm (1, y) := by
  rw [inrPoints]
  rfl

theorem fst_inlPoints (x : WithConv (H →ₐ[k] R₁)) :
    AlgHom.mapValue (AlgHom.fst k R₁ R₂) (inlPoints k H R₁ R₂ x) = x := by
  rw [inlPoints_apply, ← prodPointsMulEquiv_fst, MulEquiv.apply_symm_apply]

theorem snd_inlPoints (x : WithConv (H →ₐ[k] R₁)) :
    AlgHom.mapValue (AlgHom.snd k R₁ R₂) (inlPoints k H R₁ R₂ x) = 1 := by
  rw [inlPoints_apply, ← prodPointsMulEquiv_snd, MulEquiv.apply_symm_apply]

theorem fst_inrPoints (y : WithConv (H →ₐ[k] R₂)) :
    AlgHom.mapValue (AlgHom.fst k R₁ R₂) (inrPoints k H R₁ R₂ y) = 1 := by
  rw [inrPoints_apply, ← prodPointsMulEquiv_fst, MulEquiv.apply_symm_apply]

theorem snd_inrPoints (y : WithConv (H →ₐ[k] R₂)) :
    AlgHom.mapValue (AlgHom.snd k R₁ R₂) (inrPoints k H R₁ R₂ y) = y := by
  rw [inrPoints_apply, ← prodPointsMulEquiv_snd, MulEquiv.apply_symm_apply]

/-- Any pair of factor points decomposes in `WithConv (H →ₐ[k] R₁ × R₂)` as the convolution product
of its `inlPoints` and `inrPoints` images. -/
theorem inlPoints_mul_inrPoints (x : WithConv (H →ₐ[k] R₁)) (y : WithConv (H →ₐ[k] R₂)) :
    inlPoints k H R₁ R₂ x * inrPoints k H R₁ R₂ y =
      (prodPointsMulEquiv k H R₁ R₂).symm (x, y) := by
  simp [← map_mul]

variable [TopologicalSpace R₁] [TopologicalSpace R₂]

/-- Topological monoid isomorphism splitting convolution points valued in `R₁ × R₂` as the product
of the factor point spaces. -/
noncomputable def prodPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toMulEquiv := prodPointsMulEquiv k H R₁ R₂
  continuous_toFun :=
    ((AlgHom.continuous_mapValue continuous_fst).prodMk
      (AlgHom.continuous_mapValue continuous_snd)).congr fun f ↦
      Prod.ext (prodPointsMulEquiv_fst k H R₁ R₂ f).symm
        (prodPointsMulEquiv_snd k H R₁ R₂ f).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦ by
    simpa only [MulEquiv.invFun_eq_symm, prodPointsMulEquiv_symm_ofConv_apply,
      Function.comp_apply] using
      ((continuous_eval_ofConv h).comp continuous_fst).prodMk
        ((continuous_eval_ofConv h).comp continuous_snd)

@[simp]
theorem coe_prodPointsContinuousMulEquiv :
    (prodPointsContinuousMulEquiv k H R₁ R₂ :
      WithConv (H →ₐ[k] R₁ × R₂) ≃* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) =
      prodPointsMulEquiv k H R₁ R₂ := by
  rw [prodPointsContinuousMulEquiv]
  rfl

@[simp]
theorem prodPointsContinuousMulEquiv_fst (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsContinuousMulEquiv k H R₁ R₂ f).1 = AlgHom.mapValue (AlgHom.fst k R₁ R₂) f := by
  rw [prodPointsContinuousMulEquiv]
  exact prodPointsMulEquiv_fst k H R₁ R₂ f

@[simp]
theorem prodPointsContinuousMulEquiv_snd (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsContinuousMulEquiv k H R₁ R₂ f).2 = AlgHom.mapValue (AlgHom.snd k R₁ R₂) f := by
  rw [prodPointsContinuousMulEquiv]
  exact prodPointsMulEquiv_snd k H R₁ R₂ f

@[simp]
theorem prodPointsContinuousMulEquiv_symm_ofConv_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    ((prodPointsContinuousMulEquiv k H R₁ R₂).symm p).ofConv h = (p.1.ofConv h, p.2.ofConv h) := by
  rw [prodPointsContinuousMulEquiv]
  exact prodPointsMulEquiv_symm_ofConv_apply k H R₁ R₂ p h

/-- The first-factor embedding `inlPoints` is continuous. -/
@[continuity, fun_prop]
theorem continuous_inlPoints : Continuous (inlPoints k H R₁ R₂) :=
  ((prodPointsContinuousMulEquiv k H R₁ R₂).symm.continuous.comp
    (continuous_id.prodMk (continuous_const (y := (1 : WithConv (H →ₐ[k] R₂)))))).congr fun x ↦ by
    rw [Function.comp_apply, id_eq, inlPoints_apply, prodPointsContinuousMulEquiv]
    rfl

/-- The second-factor embedding `inrPoints` is continuous. -/
@[continuity, fun_prop]
theorem continuous_inrPoints : Continuous (inrPoints k H R₁ R₂) :=
  ((prodPointsContinuousMulEquiv k H R₁ R₂).symm.continuous.comp
    ((continuous_const (y := (1 : WithConv (H →ₐ[k] R₁)))).prodMk continuous_id)).congr fun y ↦ by
    rw [Function.comp_apply, id_eq, inrPoints_apply, prodPointsContinuousMulEquiv]
    rfl

/-- The first-factor embedding `inlPoints` is a closed embedding when `R₂` is T1. -/
theorem isClosedEmbedding_inlPoints [T1Space R₂] :
    IsClosedEmbedding (inlPoints k H R₁ R₂) := by
  have : T1Space (WithConv (H →ₐ[k] R₂)) :=
    (isEmbedding_coeFn.comp isHomeomorph_ofConv.isEmbedding).t1Space
  have hmk : IsClosedEmbedding (fun x : WithConv (H →ₐ[k] R₁) ↦
      (x, (1 : WithConv (H →ₐ[k] R₂)))) := by
    refine ⟨isEmbedding_prodMkLeft _, ?_⟩
    convert isClosed_singleton (x := (1 : WithConv (H →ₐ[k] R₂))).preimage continuous_snd
    ext ⟨x, y⟩
    simp [eq_comm]
  convert (prodPointsContinuousMulEquiv k H R₁ R₂).symm.isClosedEmbedding.comp hmk using 1
  funext x
  rw [Function.comp_apply, inlPoints_apply, prodPointsContinuousMulEquiv]
  rfl

/-- The second-factor embedding `inrPoints` is a closed embedding when `R₁` is T1. -/
theorem isClosedEmbedding_inrPoints [T1Space R₁] :
    IsClosedEmbedding (inrPoints k H R₁ R₂) := by
  have : T1Space (WithConv (H →ₐ[k] R₁)) :=
    (isEmbedding_coeFn.comp isHomeomorph_ofConv.isEmbedding).t1Space
  have hmk : IsClosedEmbedding (fun y : WithConv (H →ₐ[k] R₂) ↦
      ((1 : WithConv (H →ₐ[k] R₁)), y)) := by
    refine ⟨isEmbedding_prodMkRight _, ?_⟩
    convert isClosed_singleton (x := (1 : WithConv (H →ₐ[k] R₁))).preimage continuous_fst
    ext ⟨x, y⟩
    simp [eq_comm]
  convert (prodPointsContinuousMulEquiv k H R₁ R₂).symm.isClosedEmbedding.comp hmk using 1
  funext y
  rw [Function.comp_apply, inrPoints_apply, prodPointsContinuousMulEquiv]
  rfl

end BialgebraProd

section BialgebraPi

variable (k H : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)]

/-- Convolution points of a bialgebra valued in an indexed product `∀ i, R i` split as the
indexed product of the factor convolution monoids. -/
noncomputable def piPointsMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃* ∀ i, WithConv (H →ₐ[k] R i) where
  toFun f i := AlgHom.mapValue (Pi.evalAlgHom k R i) f
  invFun f := toConv (AlgHom.pi fun i ↦ (f i).ofConv)
  left_inv _ := ofConv_injective <| AlgHom.ext fun _ ↦ funext fun _ ↦ by simp
  right_inv _ := funext fun _ ↦ ofConv_injective <| AlgHom.ext fun _ ↦ by simp
  map_mul' f g := funext fun i ↦ map_mul _ f g

/-- Evaluating `piPointsMulEquiv` at `i` is post-composition with `Pi.evalAlgHom k R i`. -/
@[simp]
theorem piPointsMulEquiv_apply (f : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsMulEquiv k H R f i = AlgHom.mapValue (Pi.evalAlgHom k R i) f := by
  rw [piPointsMulEquiv]
  rfl

/-- The inverse of `piPointsMulEquiv` assembles a family of points coordinatewise. -/
@[simp]
theorem piPointsMulEquiv_symm_ofConv_apply
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h := by
  rw [piPointsMulEquiv]
  rfl

variable [∀ i, TopologicalSpace (R i)]

/-- Topological monoid isomorphism splitting convolution points valued in `∀ i, R i` as the
indexed product of the factor point spaces. -/
noncomputable def piPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := piPointsMulEquiv k H R
  continuous_toFun := (continuous_pi fun i ↦
    AlgHom.continuous_mapValue (continuous_apply i)).congr fun f ↦
    funext fun i ↦ (piPointsMulEquiv_apply k H R f i).symm
  continuous_invFun := continuous_withConv_iff.2 fun h ↦ continuous_pi fun i ↦ by
    simpa only [MulEquiv.invFun_eq_symm, piPointsMulEquiv_symm_ofConv_apply,
      Function.comp_def] using
      (continuous_eval_ofConv h).comp (continuous_apply i)

@[simp]
theorem coe_piPointsContinuousMulEquiv :
    (piPointsContinuousMulEquiv k H R :
      WithConv (H →ₐ[k] ∀ i, R i) ≃* ∀ i, WithConv (H →ₐ[k] R i)) =
      piPointsMulEquiv k H R := by
  rw [piPointsContinuousMulEquiv]
  rfl

@[simp]
theorem piPointsContinuousMulEquiv_apply (f : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsContinuousMulEquiv k H R f i = AlgHom.mapValue (Pi.evalAlgHom k R i) f := by
  rw [piPointsContinuousMulEquiv]
  exact piPointsMulEquiv_apply k H R f i

@[simp]
theorem piPointsContinuousMulEquiv_symm_ofConv_apply
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsContinuousMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h := by
  rw [piPointsContinuousMulEquiv]
  exact piPointsMulEquiv_symm_ofConv_apply k H R f h i

end BialgebraPi

section BaseChange

variable (k K A R : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
  [Semiring A] [Bialgebra k A] [CommSemiring R] [Algebra k R] [Algebra K R]
  [IsScalarTower k K R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- The scalar-extension adjunction is a topological monoid isomorphism on convolution points over
a topological semiring `R`. -/
noncomputable def baseChangePointsContinuousMulEquiv :
    WithConv (A →ₐ[k] R) ≃ₜ* WithConv (K ⊗[k] A →ₐ[K] R) where
  toMulEquiv := TauCeti.AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)
  continuous_toFun := isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
    continuous_of_continuous_tmul _ fun c a ↦ by
      simpa only [Function.comp_apply, MulEquiv.toFun_eq_coe,
        TauCeti.AlgHom.baseChangePointsMulEquiv_apply_ofConv, AlgHom.liftEquiv_tmul,
        Algebra.smul_def] using
        (continuous_const (y := algebraMap K R c)).fun_mul (continuous_eval_ofConv a)
  continuous_invFun := continuous_withConv_iff.2 fun a ↦ by
    simpa only [MulEquiv.invFun_eq_symm, TauCeti.AlgHom.baseChangePointsMulEquiv_symm_apply] using
      continuous_eval_ofConv (1 ⊗ₜ[k] a)

@[simp]
theorem coe_baseChangePointsContinuousMulEquiv :
    (baseChangePointsContinuousMulEquiv k K A R :
      WithConv (A →ₐ[k] R) ≃* WithConv (K ⊗[k] A →ₐ[K] R)) =
      TauCeti.AlgHom.baseChangePointsMulEquiv := by
  rw [baseChangePointsContinuousMulEquiv]
  rfl

@[simp]
theorem baseChangePointsContinuousMulEquiv_apply_tmul
    (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    (baseChangePointsContinuousMulEquiv k K A R f).ofConv (s ⊗ₜ[k] a) = s • f.ofConv a := by
  rw [baseChangePointsContinuousMulEquiv]
  exact TauCeti.AlgHom.baseChangePointsMulEquiv_apply_tmul f s a

@[simp]
theorem baseChangePointsContinuousMulEquiv_symm_apply
    (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    ((baseChangePointsContinuousMulEquiv k K A R).symm f).ofConv a = f.ofConv (1 ⊗ₜ[k] a) := by
  rw [baseChangePointsContinuousMulEquiv]
  exact TauCeti.AlgHom.baseChangePointsMulEquiv_symm_apply f a

end BaseChange

end TauCeti.PointTopology

section BialgEquiv

open TauCeti.PointTopology

variable {k H₁ H₂ : Type*} (R : Type*) [CommSemiring k] [Semiring H₁] [Bialgebra k H₁]
  [Semiring H₂] [Bialgebra k H₂] [CommSemiring R] [Algebra k R] [TopologicalSpace R]

/-- A bialgebra equivalence induces a topological monoid isomorphism on convolution points, for
every topology on the coefficient algebra `R`. -/
noncomputable def BialgEquiv.mapDomainContinuousMulEquiv (e : H₁ ≃ₐc[k] H₂) :
    WithConv (H₂ →ₐ[k] R) ≃ₜ* WithConv (H₁ →ₐ[k] R) where
  toMulEquiv := e.mapDomainMulEquiv (A := R)
  continuous_toFun := (BialgHom.continuous_mapDomain (e : H₁ →ₐc[k] H₂)).congr fun f ↦
    (e.mapDomainMulEquiv_apply f).symm
  continuous_invFun := (BialgHom.continuous_mapDomain (e.symm : H₂ →ₐc[k] H₁)).congr fun f ↦
    (e.mapDomainMulEquiv_symm_apply f).symm

@[simp]
theorem BialgEquiv.coe_mapDomainContinuousMulEquiv (e : H₁ ≃ₐc[k] H₂) :
    (e.mapDomainContinuousMulEquiv R : WithConv (H₂ →ₐ[k] R) ≃* WithConv (H₁ →ₐ[k] R)) =
      e.mapDomainMulEquiv := by
  rw [BialgEquiv.mapDomainContinuousMulEquiv]
  rfl

@[simp]
theorem BialgEquiv.mapDomainContinuousMulEquiv_apply (e : H₁ ≃ₐc[k] H₂)
    (f : WithConv (H₂ →ₐ[k] R)) :
    e.mapDomainContinuousMulEquiv R f = BialgHom.mapDomain (e : H₁ →ₐc[k] H₂) f := by
  rw [BialgEquiv.mapDomainContinuousMulEquiv]
  exact e.mapDomainMulEquiv_apply f

@[simp]
theorem BialgEquiv.mapDomainContinuousMulEquiv_symm_apply (e : H₁ ≃ₐc[k] H₂)
    (f : WithConv (H₁ →ₐ[k] R)) :
    (e.mapDomainContinuousMulEquiv R).symm f = BialgHom.mapDomain (e.symm : H₂ →ₐc[k] H₁) f := by
  rw [BialgEquiv.mapDomainContinuousMulEquiv]
  exact e.mapDomainMulEquiv_symm_apply f

end BialgEquiv
