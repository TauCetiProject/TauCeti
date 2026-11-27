/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Cohomology
public import TauCeti.Algebra.Homology.DG.Algebra.TensorProduct
public import TauCeti.AlgebraicTopology.RationalHomotopy.PolynomialInterval

import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist

/-!
# Polynomial homotopies of differential graded algebra maps

Two morphisms `f₀ f₁ : M → A` of differential graded algebras over a field `K` are homotopic when
there is a morphism `H : M → A ⊗ Λ(t, dt)` into the tensor product with the polynomial interval
whose two ends `t = 0` and `t = 1` are `f₀` and `f₁`. This is the notion of homotopy of rational
homotopy theory, used to compare maps out of Sullivan algebras. Reflexivity, symmetry and
compatibility with composition hold for arbitrary differential graded algebras and are proved
here; transitivity is special to maps out of Sullivan algebras, where it follows from the lifting
lemma.

The ends of `H` are obtained with the evaluation `id_A ⊗ ε_a : A ⊗ Λ(t, dt) → A`,
`x ⊗ y ↦ y (a) x`. Integration along the fibre,

`∫ₐᵇ : A ⊗ Λ(t, dt) → A`, `x ⊗ q dt ↦ (-1) ^ |x| (∫ₐᵇ q) x`, `x ⊗ p ↦ 0`,

lowers degrees by one and, in characteristic zero, satisfies the homotopy formula
`d ∫ₐᵇ + ∫ₐᵇ d = (id ⊗ ε_b) - (id ⊗ ε_a)`. Applied to `H`, it is a chain homotopy between the two
ends, so homotopic maps induce the same map on cohomology.

## Main definitions

* `TauCeti.PolynomialInterval.tensorEval`: the evaluation `id_A ⊗ ε_a : A ⊗ Λ(t, dt) → A`, a
  morphism of differential graded algebras.
* `TauCeti.PolynomialInterval.tensorIntegral`: integration along the fibre
  `∫ₐᵇ : A ⊗ Λ(t, dt) → A`.
* `TauCeti.DGAlgHom.Homotopic`: two morphisms `M → A` are homotopic when they are the two ends of
  a morphism `M → A ⊗ Λ(t, dt)`.

## Main results

* `TauCeti.PolynomialInterval.map_tensorIntegral_add_tensorIntegral_dgTensorDifferential`: the
  homotopy formula `d ∫ₐᵇ + ∫ₐᵇ d = (id ⊗ ε_b) - (id ⊗ ε_a)`.
* `TauCeti.PolynomialInterval.cohomologyMap_tensorEval_comp`: in characteristic zero the
  evaluations of a morphism `M → A ⊗ Λ(t, dt)` at any two points agree on cohomology.
* `TauCeti.DGAlgHom.Homotopic.refl`, `TauCeti.DGAlgHom.Homotopic.symm`,
  `TauCeti.DGAlgHom.Homotopic.comp_left` and `TauCeti.DGAlgHom.Homotopic.comp_right`: homotopy is
  reflexive and symmetric, and compatible with composition on either side.
* `TauCeti.DGAlgHom.Homotopic.cohomologyMap_eq`: in characteristic zero homotopic morphisms induce
  the same map on cohomology.
* `TauCeti.PolynomialInterval.homotopic_eval`: any two evaluations `ε_a, ε_b : Λ(t, dt) → K` are
  homotopic.

## References

* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, Publ. Math. IHÉS 48
  (1978), §5, before Proposition 5.5, and Proposition 5.5.
* K. Hess, *Rational homotopy theory: a brief introduction*, Proposition 1.14.
* D. Sullivan, *Infinitesimal computations in topology*, Publ. Math. IHÉS 47 (1977), §3.
-/

public section

open Polynomial TrivSqZeroExt
open scoped TensorProduct

namespace TauCeti

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {𝒜 : ℤ → Submodule K A}
  [GradedAlgebra 𝒜] {dA : A →ₗ[K] A}

namespace PolynomialInterval

/-- The evaluation `id_A ⊗ ε_a : A ⊗ Λ(t, dt) → A` at a point `a : K`, followed by the
identification `A ⊗ K = A`: the morphism of differential graded algebras sending `x ⊗ y` to
`y (a) x`. The composites of a homotopy `H : M → A ⊗ Λ(t, dt)` with `tensorEval hA 0` and
`tensorEval hA 1` are its two ends. -/
noncomputable def tensorEval (hA : IsDGAlgebra 𝒜 dA) (a : K) :
    DGAlgHom (isDGAlgebra_gradedTensorGrading hA (isDGAlgebra K)) hA :=
  dgTensorLift (DGAlgHom.id hA) (hA.unitHom.comp (eval a)) fun i j x y ↦ by
    by_cases hj : j = 0
    · subst hj
      simp [Algebra.commutes]
    · simp [fst_eq_zero_of_mem_trivSqZeroExtGrading y.property hj]

/-- The evaluation `id_A ⊗ ε_a` sends `x ⊗ y` to `y (a) x`. -/
@[simp]
theorem tensorEval_tmul (hA : IsDGAlgebra 𝒜 dA) (a : K) (x : A) (y : PolynomialInterval K) :
    tensorEval hA a (x ᵍ⊗ₜ[K] y) = eval a y • x := by
  simp [tensorEval, Algebra.smul_def, Algebra.commutes]

/-- The evaluation of the constant family `x ⊗ 1` is `x`. -/
@[simp]
theorem tensorEval_comp_dgTensorIncludeLeft (hA : IsDGAlgebra 𝒜 dA) (a : K) :
    (tensorEval hA a).comp (dgTensorIncludeLeft hA (isDGAlgebra K)) = DGAlgHom.id hA :=
  DGAlgHom.ext fun _ ↦ by simp

/-- The evaluation of `1 ⊗ y` is the scalar `y (a)`. -/
@[simp]
theorem tensorEval_comp_dgTensorIncludeRight (hA : IsDGAlgebra 𝒜 dA) (a : K) :
    (tensorEval hA a).comp (dgTensorIncludeRight hA (isDGAlgebra K)) = hA.unitHom.comp (eval a) :=
  DGAlgHom.ext fun _ ↦ by simp [Algebra.smul_def]

/-- Evaluating at `a` after applying `ψ ⊗ s*` is applying `ψ` after evaluating at `s (a)`, where
`s*` is the pullback of forms along the polynomial map `s`. -/
@[simp]
theorem tensorEval_comp_dgTensorMap {B : Type*} [Ring B] [Algebra K B] {ℬ : ℤ → Submodule K B}
    [GradedAlgebra ℬ] {dB : B →ₗ[K] B} {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
    (ψ : DGAlgHom hA hB) (s : K[X]) (a : K) :
    (tensorEval hB a).comp (dgTensorMap ψ (pullback s)) = ψ.comp (tensorEval hA (s.eval a)) :=
  dgTensorAlgHom_ext (hA := hA) (hB := isDGAlgebra K) (DGAlgHom.ext fun _ ↦ by simp)
    (DGAlgHom.ext fun _ ↦ by simp [Algebra.smul_def, AlgHomClass.commutes])

/-- Evaluating at `a` after applying `ψ ⊗ id` is applying `ψ` after evaluating at `a`. -/
@[simp]
theorem tensorEval_comp_dgTensorMap_id {B : Type*} [Ring B] [Algebra K B]
    {ℬ : ℤ → Submodule K B} [GradedAlgebra ℬ] {dB : B →ₗ[K] B} {hA : IsDGAlgebra 𝒜 dA}
    {hB : IsDGAlgebra ℬ dB} (ψ : DGAlgHom hA hB) (a : K) :
    (tensorEval hB a).comp (dgTensorMap ψ (DGAlgHom.id (isDGAlgebra K))) =
      ψ.comp (tensorEval hA a) := by
  simpa using tensorEval_comp_dgTensorMap ψ X a

variable (𝒜) in
/-- Integration along the fibre `∫ₐᵇ : A ⊗ Λ(t, dt) → A` from `a` to `b`: it sends `x ⊗ y` to
`(-1) ^ |x| (∫ₐᵇ y) x` for homogeneous `x`, so that `x ⊗ p` integrates to `0` and `x ⊗ q dt` to
`(-1) ^ |x| (∫ₐᵇ q(t) dt) x`. The sign is the Koszul sign of moving the integral, of degree `-1`,
past `x`. -/
noncomputable def tensorIntegral (a b : K) :
    (𝒜 ᵍ⊗[K] trivSqZeroExtGrading K K[X] K[X]) →ₗ[K] A :=
  TensorProduct.lift (LinearMap.smulRightₗ (integral a b) ∘ₗ
      (InternalGrading.ofDecomposition 𝒜).koszulTwist 1) ∘ₗ
    (GradedTensorProduct.of K 𝒜 (trivSqZeroExtGrading K K[X] K[X])).symm.toLinearMap

/-- Integration along the fibre sends `x ⊗ y` to `(∫ₐᵇ y) σ x`, where `σ x = (-1) ^ |x| x` is the
Koszul twist. -/
@[simp]
theorem tensorIntegral_tmul (a b : K) (x : A) (y : PolynomialInterval K) :
    tensorIntegral 𝒜 a b (x ᵍ⊗ₜ[K] y) =
      integral a b y • (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 x := by
  simp [tensorIntegral, GradedTensorProduct.tmul]

/-- Integration along the fibre of `x ⊗ y`, for `x` homogeneous of degree `p`, is
`(-1) ^ p (∫ₐᵇ y) x`. -/
theorem tensorIntegral_tmul_of_mem (a b : K) {p : ℤ} {x : A} (hx : x ∈ 𝒜 p)
    (y : PolynomialInterval K) :
    tensorIntegral 𝒜 a b (x ᵍ⊗ₜ[K] y) = p.negOnePow • integral a b y • x := by
  rw [tensorIntegral_tmul, InternalGrading.koszulTwist_ofDecomposition_apply_of_mem 𝒜 hx, one_mul,
    smul_comm, Units.smul_def, Int.cast_smul_eq_zsmul]

/-- Integration along the fibre lowers degrees by one. -/
theorem tensorIntegral_mem (a b : K) {n : ℤ}
    {z : 𝒜 ᵍ⊗[K] trivSqZeroExtGrading K K[X] K[X]}
    (hz : z ∈ gradedTensorGrading 𝒜 (trivSqZeroExtGrading K K[X] K[X]) n) :
    tensorIntegral 𝒜 a b z ∈ 𝒜 (n - 1) := by
  refine gradedTensorGrading_le 𝒜 _ (C := (𝒜 (n - 1)).comap (tensorIntegral 𝒜 a b))
    (fun p x hx y hy ↦ ?_) hz
  rw [Submodule.mem_comap, tensorIntegral_tmul_of_mem a b hx]
  by_cases hp : n - p = 1
  · exact Submodule.smul_of_tower_mem _ _ (Submodule.smul_mem _ _ (by
      rwa [show n - 1 = p by omega]))
  · simp [snd_eq_zero_of_mem_trivSqZeroExtGrading hy hp, integral_apply]

/-- **The homotopy formula** for integration along the fibre: in characteristic zero,
`d ∫ₐᵇ z + ∫ₐᵇ d z = (id ⊗ ε_b) z - (id ⊗ ε_a) z` for every `z ∈ A ⊗ Λ(t, dt)`. -/
theorem map_tensorIntegral_add_tensorIntegral_dgTensorDifferential [CharZero K]
    (hA : IsDGAlgebra 𝒜 dA) (a b : K) (z : 𝒜 ᵍ⊗[K] trivSqZeroExtGrading K K[X] K[X]) :
    dA (tensorIntegral 𝒜 a b z) + tensorIntegral 𝒜 a b
        (dgTensorDifferential 𝒜 _ dA (derivative' (R := K)).trivSqZeroExtDifferential z) =
      tensorEval hA b z - tensorEval hA a z := by
  have key : dA ∘ₗ tensorIntegral 𝒜 a b + tensorIntegral 𝒜 a b ∘ₗ
      dgTensorDifferential 𝒜 _ dA (derivative' (R := K)).trivSqZeroExtDifferential =
      (tensorEval hA b).toGradedAlgHom.toAlgHom.toLinearMap -
        (tensorEval hA a).toGradedAlgHom.toAlgHom.toLinearMap :=
    gradedTensor_linearMap_ext _ _ fun _ _ x _ y _ ↦ by
      simp [hA.toIsNonUnitalDGAlgebra.koszulTwist_map, integral_inr_derivative, sub_smul]
  simpa using LinearMap.congr_fun key z

variable {M : Type*} [Ring M] [Algebra K M] {ℳ : ℤ → Submodule K M} [GradedAlgebra ℳ]
  {dM : M →ₗ[K] M} {hM : IsDGAlgebra ℳ dM}

/-- In characteristic zero the evaluations at any two points `a` and `b` of a morphism
`H : M → A ⊗ Λ(t, dt)` induce the same map on cohomology. -/
theorem cohomologyMap_tensorEval_comp [CharZero K] {hA : IsDGAlgebra 𝒜 dA}
    (H : DGAlgHom hM (isDGAlgebra_gradedTensorGrading hA (isDGAlgebra K))) (a b : K) :
    ((tensorEval hA a).comp H).cohomologyMap = ((tensorEval hA b).comp H).cohomologyMap := by
  refine (DGAlgHom.cohomologyMap_eq_of_homotopy _ _
    (tensorIntegral 𝒜 a b ∘ₗ H.toGradedAlgHom.toAlgHom.toLinearMap) fun m ↦ ?_).symm
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
    DGAlgHom.coe_toGradedAlgHom, DGAlgHom.comp_apply, ← H.map_d]
  exact (map_tensorIntegral_add_tensorIntegral_dgTensorDifferential hA a b (H m)).symm

end PolynomialInterval

namespace DGAlgHom

open PolynomialInterval

variable {M : Type*} [Ring M] [Algebra K M] {ℳ : ℤ → Submodule K M} [GradedAlgebra ℳ]
  {dM : M →ₗ[K] M} {hM : IsDGAlgebra ℳ dM} {hA : IsDGAlgebra 𝒜 dA}

/-- Two morphisms `f₀ f₁ : M → A` of differential graded algebras are **homotopic** when they are
the two ends of a polynomial homotopy: a morphism `H : M → A ⊗ Λ(t, dt)` whose evaluations at
`t = 0` and `t = 1` are `f₀` and `f₁`. -/
def Homotopic (f₀ f₁ : DGAlgHom hM hA) : Prop :=
  ∃ H : DGAlgHom hM (isDGAlgebra_gradedTensorGrading hA (isDGAlgebra K)),
    (tensorEval hA 0).comp H = f₀ ∧ (tensorEval hA 1).comp H = f₁

/-- Two morphisms `f₀ f₁ : M → A` are homotopic if and only if there is a morphism
`H : M → A ⊗ Λ(t, dt)` whose evaluations at `t = 0` and `t = 1` are `f₀` and `f₁`. -/
theorem homotopic_iff {f₀ f₁ : DGAlgHom hM hA} :
    f₀.Homotopic f₁ ↔ ∃ H : DGAlgHom hM (isDGAlgebra_gradedTensorGrading hA (isDGAlgebra K)),
      (tensorEval hA 0).comp H = f₀ ∧ (tensorEval hA 1).comp H = f₁ :=
  Iff.rfl

namespace Homotopic

/-- Every morphism is homotopic to itself, through the constant homotopy `m ↦ f m ⊗ 1`. -/
@[refl]
theorem refl (f : DGAlgHom hM hA) : f.Homotopic f :=
  ⟨(dgTensorIncludeLeft hA (isDGAlgebra K)).comp f, by simp [← comp_assoc],
    by simp [← comp_assoc]⟩

/-- Homotopy is symmetric: reversing a homotopy along the reflection `t ↦ 1 - t` of the interval
exchanges its two ends. -/
@[symm]
theorem symm {f₀ f₁ : DGAlgHom hM hA} (h : f₀.Homotopic f₁) : f₁.Homotopic f₀ := by
  obtain ⟨H, h₀, h₁⟩ := h
  refine ⟨(dgTensorMap (DGAlgHom.id hA) (pullback (1 - X))).comp H, ?_, ?_⟩ <;>
    simp [← comp_assoc, h₀, h₁]

/-- Homotopy is compatible with composition on the left: if `f₀` and `f₁` are homotopic, so are
`ψ ∘ f₀` and `ψ ∘ f₁`. -/
theorem comp_left {B : Type*} [Ring B] [Algebra K B] {ℬ : ℤ → Submodule K B} [GradedAlgebra ℬ]
    {dB : B →ₗ[K] B} {hB : IsDGAlgebra ℬ dB} {f₀ f₁ : DGAlgHom hM hA} (h : f₀.Homotopic f₁)
    (ψ : DGAlgHom hA hB) : (ψ.comp f₀).Homotopic (ψ.comp f₁) := by
  obtain ⟨H, h₀, h₁⟩ := h
  exact ⟨(dgTensorMap ψ (DGAlgHom.id (isDGAlgebra K))).comp H,
    by rw [← comp_assoc, tensorEval_comp_dgTensorMap_id, comp_assoc, h₀],
    by rw [← comp_assoc, tensorEval_comp_dgTensorMap_id, comp_assoc, h₁]⟩

/-- Homotopy is compatible with composition on the right: if `f₀` and `f₁` are homotopic, so are
`f₀ ∘ φ` and `f₁ ∘ φ`. -/
theorem comp_right {N : Type*} [Ring N] [Algebra K N] {𝒩 : ℤ → Submodule K N} [GradedAlgebra 𝒩]
    {dN : N →ₗ[K] N} {hN : IsDGAlgebra 𝒩 dN} {f₀ f₁ : DGAlgHom hM hA} (h : f₀.Homotopic f₁)
    (φ : DGAlgHom hN hM) : (f₀.comp φ).Homotopic (f₁.comp φ) := by
  obtain ⟨H, h₀, h₁⟩ := h
  exact ⟨H.comp φ, by rw [← comp_assoc, h₀], by rw [← comp_assoc, h₁]⟩

/-- In characteristic zero homotopic morphisms induce the same map on cohomology. -/
theorem cohomologyMap_eq [CharZero K] {f₀ f₁ : DGAlgHom hM hA} (h : f₀.Homotopic f₁) :
    f₀.cohomologyMap = f₁.cohomologyMap := by
  obtain ⟨H, rfl, rfl⟩ := h
  exact cohomologyMap_tensorEval_comp H 0 1

end Homotopic

end DGAlgHom

namespace PolynomialInterval

/-- Any two evaluations `ε_a, ε_b : Λ(t, dt) → K` of the polynomial interval are homotopic. In
positive characteristic `p` they can differ on cohomology: `ε_0` and `ε_1` send the cycle `t ^ p`
to `0` and `1`, so `TauCeti.DGAlgHom.Homotopic.cohomologyMap_eq` needs characteristic zero. -/
theorem homotopic_eval (a b : K) : (eval a).Homotopic (eval b) := by
  refine ⟨(dgTensorIncludeRight (isDGAlgebra_trivialGrading K) (isDGAlgebra K)).comp
    (pullback (C a + C (b - a) * X)), ?_, ?_⟩ <;>
    exact DGAlgHom.ext fun _ ↦ by simp

end PolynomialInterval

end TauCeti
