/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints.Prod
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Point topology for binary and indexed products of coefficient algebras

For an affine `k`-algebra `A`, taking `k`-algebra homomorphisms into a binary product `R₁ × R₂` or
an indexed product `∀ i, R i` of topological `k`-algebras identifies the evaluation point space
(carrying the scoped `TauCeti.PointTopology` instance) with the product of the factor point spaces,
with no finiteness, separation, or topological-semiring hypotheses on `A` or the coefficient
algebras.

When the source is a `k`-bialgebra `H`, the algebraic convolution-monoid splittings from
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints.Prod` upgrade to topological monoid (hence
topological group, when `H` is a Hopf algebra) isomorphisms on `WithConv`. The factor inclusions
`inlPoints` and `inrPoints` are continuous in general, and are closed topological embeddings when
the complementary factor is T1 (`T1Space R₂` for `inlPoints`, `T1Space R₁` for `inrPoints`). Over a
number field `F`, these splittings decompose full adelic points `G(𝔸_F) = G(F_∞ × 𝔸_{F,f})` into
`G(F_∞) × G(𝔸_{F,f})` and archimedean points `G(F_∞)` into the product of `G(F_w)` over infinite
places `w`.

## Main declarations

* `TauCeti.PointTopology.prodHomeomorph`, `TauCeti.PointTopology.piHomeomorph`: homeomorphisms for
  points valued in binary and indexed products of coefficient algebras (using the scoped
  `TauCeti.PointTopology.topology` instance).
* `TauCeti.AlgHom.prodPointsContinuousMulEquiv`, `TauCeti.AlgHom.piPointsContinuousMulEquiv`:
  topological convolution-monoid isomorphisms for binary and indexed products of coefficient
  algebras, upgrading `prodPointsMulEquiv` and `piPointsMulEquiv`.
* `TauCeti.AlgHom.continuous_inlPoints`, `TauCeti.AlgHom.continuous_inrPoints`,
  `TauCeti.AlgHom.isClosedEmbedding_inlPoints`, `TauCeti.AlgHom.isClosedEmbedding_inrPoints`:
  continuity of the factor homomorphisms `inlPoints` and `inrPoints`, and closed-embedding theorems
  under `T1Space R₂` (for `inlPoints`) and `T1Space R₁` (for `inrPoints`).

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
-/

public section

open Topology WithConv

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
    (prodHomeomorph k A R₁ R₂ x).1 a = (x a).1 := by
  rw [← Homeomorph.coe_toEquiv]
  simp [prodHomeomorph]

/-- Projecting `prodHomeomorph` to the second factor reads the second coordinate of a point. -/
@[simp]
theorem prodHomeomorph_apply_snd (x : A →ₐ[k] R₁ × R₂) (a : A) :
    (prodHomeomorph k A R₁ R₂ x).2 a = (x a).2 := by
  rw [← Homeomorph.coe_toEquiv]
  simp [prodHomeomorph]

/-- The inverse of `prodHomeomorph` pairs two points coordinatewise. -/
@[simp]
theorem prodHomeomorph_symm_apply (p : (A →ₐ[k] R₁) × (A →ₐ[k] R₂)) (a : A) :
    (prodHomeomorph k A R₁ R₂).symm p a = (p.1 a, p.2 a) := by
  rw [← Homeomorph.coe_symm_toEquiv]
  simp [prodHomeomorph]

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
    piHomeomorph k A R x i a = x a i := by
  simp [piHomeomorph]

/-- The inverse of `piHomeomorph` assembles a family of points coordinatewise. -/
@[simp]
theorem piHomeomorph_symm_apply (f : ∀ i, A →ₐ[k] R i) (a : A) (i : ι) :
    (piHomeomorph k A R).symm f a i = f i a := by
  simp [piHomeomorph]

end Pi

end Semiring

end TauCeti.PointTopology

namespace TauCeti.AlgHom

open TauCeti.PointTopology

section BialgebraProd

variable (k H R₁ R₂ : Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [CommSemiring R₁] [Algebra k R₁] [TopologicalSpace R₁]
  [CommSemiring R₂] [Algebra k R₂] [TopologicalSpace R₂]

/-- Topological monoid isomorphism splitting convolution points valued in `R₁ × R₂` as the product
of the factor point spaces. -/
noncomputable def prodPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] R₁ × R₂) ≃ₜ* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂) where
  toMulEquiv := prodPointsMulEquiv k H R₁ R₂
  continuous_toFun :=
    (isHomeomorph_ofConv.isEmbedding.isInducing.prodMap
      isHomeomorph_ofConv.isEmbedding.isInducing).continuous_iff.2 <|
      ((prodHomeomorph k H R₁ R₂).continuous.comp isHomeomorph_ofConv.continuous).congr
        fun f ↦ Prod.ext (AlgHom.ext fun h ↦ by simp) (AlgHom.ext fun h ↦ by simp)
  continuous_invFun := isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
    ((prodHomeomorph k H R₁ R₂).symm.continuous.comp
      (isHomeomorph_ofConv.continuous.prodMap isHomeomorph_ofConv.continuous)).congr
      fun p ↦ AlgHom.ext fun h ↦ by simp

@[simp]
theorem prodPointsContinuousMulEquiv_fst (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsContinuousMulEquiv k H R₁ R₂ f).1 = AlgHom.mapValue (AlgHom.fst k R₁ R₂) f := by
  simp [prodPointsContinuousMulEquiv]

@[simp]
theorem prodPointsContinuousMulEquiv_snd (f : WithConv (H →ₐ[k] R₁ × R₂)) :
    (prodPointsContinuousMulEquiv k H R₁ R₂ f).2 = AlgHom.mapValue (AlgHom.snd k R₁ R₂) f := by
  simp [prodPointsContinuousMulEquiv]

@[simp]
theorem coe_prodPointsContinuousMulEquiv :
    (prodPointsContinuousMulEquiv k H R₁ R₂ :
      WithConv (H →ₐ[k] R₁ × R₂) ≃* WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) =
      prodPointsMulEquiv k H R₁ R₂ :=
  MulEquiv.ext fun f ↦ Prod.ext
    ((prodPointsContinuousMulEquiv_fst k H R₁ R₂ f).trans (prodPointsMulEquiv_fst k H R₁ R₂ f).symm)
    ((prodPointsContinuousMulEquiv_snd k H R₁ R₂ f).trans (prodPointsMulEquiv_snd k H R₁ R₂ f).symm)

theorem prodPointsContinuousMulEquiv_symm_eq
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) :
    (prodPointsContinuousMulEquiv k H R₁ R₂).symm p =
      (prodPointsMulEquiv k H R₁ R₂).symm p :=
  (prodPointsContinuousMulEquiv k H R₁ R₂).symm_apply_eq.mpr <| by
    simp [prodPointsContinuousMulEquiv]

@[simp]
theorem prodPointsContinuousMulEquiv_symm_ofConv_apply
    (p : WithConv (H →ₐ[k] R₁) × WithConv (H →ₐ[k] R₂)) (h : H) :
    ((prodPointsContinuousMulEquiv k H R₁ R₂).symm p).ofConv h = (p.1.ofConv h, p.2.ofConv h) := by
  rw [prodPointsContinuousMulEquiv_symm_eq, prodPointsMulEquiv_symm_ofConv_apply]

/-- The first-factor embedding `inlPoints` is continuous. -/
@[continuity, fun_prop]
theorem continuous_inlPoints : Continuous (inlPoints k H R₁ R₂) :=
  ((map_continuous (prodPointsContinuousMulEquiv k H R₁ R₂).symm).comp
    (continuous_id.prodMk (continuous_const (y := (1 : WithConv (H →ₐ[k] R₂)))))).congr fun x ↦ by
    rw [inlPoints_apply, ← prodPointsContinuousMulEquiv_symm_eq, Function.comp_apply, id_eq]

/-- The second-factor embedding `inrPoints` is continuous. -/
@[continuity, fun_prop]
theorem continuous_inrPoints : Continuous (inrPoints k H R₁ R₂) :=
  ((map_continuous (prodPointsContinuousMulEquiv k H R₁ R₂).symm).comp
    ((continuous_const (y := (1 : WithConv (H →ₐ[k] R₁)))).prodMk continuous_id)).congr fun y ↦ by
    rw [inrPoints_apply, ← prodPointsContinuousMulEquiv_symm_eq, Function.comp_apply, id_eq]

/-- The first-factor embedding `inlPoints` is a closed embedding when `R₂` is T1. -/
theorem isClosedEmbedding_inlPoints [T1Space R₂] :
    IsClosedEmbedding (inlPoints k H R₁ R₂) := by
  have : T1Space (WithConv (H →ₐ[k] R₂)) :=
    (isEmbedding_coeFn.comp isHomeomorph_ofConv.isEmbedding).t1Space
  have hmk : IsClosedEmbedding (fun x : WithConv (H →ₐ[k] R₁) ↦
      (x, (1 : WithConv (H →ₐ[k] R₂)))) :=
    .of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft _) (isClosedMap_prodMk_right _)
  convert (Homeomorph.ofClass (prodPointsContinuousMulEquiv k H R₁ R₂).symm).isClosedEmbedding.comp
    hmk using 1
  funext x
  rw [Function.comp_apply, Homeomorph.coe_ofClass, prodPointsContinuousMulEquiv_symm_eq,
    inlPoints_apply]

/-- The second-factor embedding `inrPoints` is a closed embedding when `R₁` is T1. -/
theorem isClosedEmbedding_inrPoints [T1Space R₁] :
    IsClosedEmbedding (inrPoints k H R₁ R₂) := by
  have : T1Space (WithConv (H →ₐ[k] R₁)) :=
    (isEmbedding_coeFn.comp isHomeomorph_ofConv.isEmbedding).t1Space
  have hmk : IsClosedEmbedding (fun y : WithConv (H →ₐ[k] R₂) ↦
      ((1 : WithConv (H →ₐ[k] R₁)), y)) :=
    .of_isEmbedding_isClosedMap (isEmbedding_prodMkRight _) (isClosedMap_prodMk_left _)
  convert (Homeomorph.ofClass (prodPointsContinuousMulEquiv k H R₁ R₂).symm).isClosedEmbedding.comp
    hmk using 1
  funext y
  rw [Function.comp_apply, Homeomorph.coe_ofClass, prodPointsContinuousMulEquiv_symm_eq,
    inrPoints_apply]

end BialgebraProd

section BialgebraPi

variable (k H : Type*) {ι : Type*} (R : ι → Type*) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [∀ i, CommSemiring (R i)] [∀ i, Algebra k (R i)] [∀ i, TopologicalSpace (R i)]

/-- Topological monoid isomorphism splitting convolution points valued in `∀ i, R i` as the
indexed product of the factor point spaces. -/
noncomputable def piPointsContinuousMulEquiv :
    WithConv (H →ₐ[k] ∀ i, R i) ≃ₜ* ∀ i, WithConv (H →ₐ[k] R i) where
  toMulEquiv := piPointsMulEquiv k H R
  continuous_toFun := continuous_pi fun i ↦
    isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
      ((continuous_apply i).comp
        ((piHomeomorph k H R).continuous.comp isHomeomorph_ofConv.continuous)).congr
        fun f ↦ AlgHom.ext fun h ↦ by simp
  continuous_invFun := isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
    ((piHomeomorph k H R).symm.continuous.comp
      (continuous_pi fun i ↦ isHomeomorph_ofConv.continuous.comp (continuous_apply i))).congr
      fun f ↦ AlgHom.ext fun h ↦ funext fun i ↦ by simp

@[simp]
theorem piPointsContinuousMulEquiv_apply (f : WithConv (H →ₐ[k] ∀ i, R i)) (i : ι) :
    piPointsContinuousMulEquiv k H R f i = AlgHom.mapValue (Pi.evalAlgHom k R i) f := by
  simp [piPointsContinuousMulEquiv]

@[simp]
theorem coe_piPointsContinuousMulEquiv :
    (piPointsContinuousMulEquiv k H R :
      WithConv (H →ₐ[k] ∀ i, R i) ≃* ∀ i, WithConv (H →ₐ[k] R i)) =
      piPointsMulEquiv k H R :=
  MulEquiv.ext fun f ↦ funext fun i ↦
    (piPointsContinuousMulEquiv_apply k H R f i).trans (piPointsMulEquiv_apply k H R f i).symm

@[simp]
theorem piPointsContinuousMulEquiv_symm_ofConv_apply
    (f : ∀ i, WithConv (H →ₐ[k] R i)) (h : H) (i : ι) :
    ((piPointsContinuousMulEquiv k H R).symm f).ofConv h i = (f i).ofConv h := by
  have hsymm : (piPointsContinuousMulEquiv k H R).symm f = (piPointsMulEquiv k H R).symm f :=
    (piPointsContinuousMulEquiv k H R).symm_apply_eq.mpr <| by
      simp [piPointsContinuousMulEquiv]
  rw [hsymm, piPointsMulEquiv_symm_ofConv_apply]

end BialgebraPi

end TauCeti.AlgHom
