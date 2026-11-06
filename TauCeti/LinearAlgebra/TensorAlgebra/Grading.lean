/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading

/-!
# The input-degree grading of a tensor algebra

An internal `ℤ`-grading `G` of a module `M` induces a grading of the tensor algebra
`TensorAlgebra R M` by input degree: a product `ι x₁ * ⋯ * ι xₙ` of homogeneous generators of
degrees `d₁, …, dₙ` has degree `d₁ + ⋯ + dₙ`. Unlike Mathlib's `TensorAlgebra.gradedAlgebra`,
which grades by word length, this grading sees the degrees of the generators, and it can be
negative. It is the grading that descends to quotients of the tensor algebra by homogeneous
relations, such as the Koszul sign relations defining free graded-commutative algebras.

The degree-`p` piece `TauCeti.tensorAlgebraPiece G p` is transported from the total-letter-degree
piece `TauCeti.TensorWords.gradedPiece G p` of the direct sum of tensor powers along Eric Wieser's
algebra isomorphism `TensorAlgebra.equivDirectSum`. Internality and multiplicativity therefore
come from the corresponding facts for tensor words, and no freeness or flatness assumption on
`M` is needed.

The universal property of the tensor algebra is compatible with the grading: a linear map into a
graded algebra preserving degrees lifts to a graded algebra map, and graded algebra maps out of
the tensor algebra are determined by their values on generators.

## Main definitions

* `TauCeti.tensorAlgebraPiece`: the degree-`p` piece of the input-degree grading.
* `TauCeti.tensorAlgebraGradedLift`: the graded algebra map induced by a degree-preserving linear
  map into a graded algebra.

## Main results

* `TauCeti.tensorAlgebraPiece_eq_span`: the degree-`p` piece is spanned by the products of
  homogeneous generators of total degree `p`.
* `TauCeti.isInternal_tensorAlgebraPiece`: the pieces form an internal direct sum.
* The instance `GradedAlgebra (tensorAlgebraPiece G)`.
* `TauCeti.decompose_tensorAlgebra_ι`: the homogeneous components of a generator are the
  generators of its homogeneous components.
* `TauCeti.isHomogeneous_tensorAlgebraLift`: the lift of a degree-preserving linear map into a
  graded algebra preserves input degree.
* `TauCeti.tensorAlgebraGradedAlgHom_ext`: graded algebra maps out of the tensor algebra agree
  when they agree on generators.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uM uA

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree-`p` piece of the input-degree grading of `TensorAlgebra R M` induced by an
internal grading `G` of `M`. It is spanned by the products `ι x₁ * ⋯ * ι xₙ` of homogeneous
generators whose degrees add up to `p` (`tensorAlgebraPiece_eq_span`). -/
noncomputable def tensorAlgebraPiece (G : InternalGrading R M) (p : ℤ) :
    Submodule R (TensorAlgebra R M) :=
  ((TensorWords.grading G).map TensorAlgebra.equivDirectSum.symm.toLinearEquiv).piece p

/-- The input-degree pieces of the tensor algebra form an internal direct sum. -/
theorem isInternal_tensorAlgebraPiece (G : InternalGrading R M) :
    DirectSum.IsInternal (tensorAlgebraPiece G) :=
  ((TensorWords.grading G).map TensorAlgebra.equivDirectSum.symm.toLinearEquiv).isInternal

/-- An element of the tensor algebra has input degree `p` exactly when its image in the direct sum
of tensor powers has total letter degree `p`. -/
theorem mem_tensorAlgebraPiece_iff {G : InternalGrading R M} {p : ℤ} {x : TensorAlgebra R M} :
    x ∈ tensorAlgebraPiece G p ↔ TensorAlgebra.toDirectSum x ∈ TensorWords.gradedPiece G p := by
  simp only [tensorAlgebraPiece, InternalGrading.mem_map_piece_iff, TensorWords.grading_piece,
    AlgEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm, AlgEquiv.toLinearEquiv_apply,
    TensorAlgebra.equivDirectSum_apply]

/-- A product of homogeneous generators lies in the piece of the sum of their degrees. -/
theorem tprod_mem_tensorAlgebraPiece (G : InternalGrading R M) {n : ℕ} (d : Fin n → ℤ)
    (x : Fin n → M) (hx : ∀ i, x i ∈ G.piece (d i)) :
    TensorAlgebra.tprod R M n x ∈ tensorAlgebraPiece G (∑ i, d i) := by
  rw [mem_tensorAlgebraPiece_iff, TensorAlgebra.toDirectSum_tensorPower_tprod,
    ← DirectSum.lof_eq_of R, ← TensorWords.of_def]
  exact TensorWords.mem_gradedPiece_of_tprod G x d hx

/-- A generator of degree `p` lies in the degree-`p` piece of the tensor algebra. -/
theorem ι_mem_tensorAlgebraPiece (G : InternalGrading R M) {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) : TensorAlgebra.ι R x ∈ tensorAlgebraPiece G p := by
  rw [mem_tensorAlgebraPiece_iff, TensorAlgebra.toDirectSum_ι, ← DirectSum.lof_eq_of R,
    ← TensorWords.of_def]
  simpa only [Fin.sum_univ_one] using
    TensorWords.mem_gradedPiece_of_tprod G (fun _ : Fin 1 ↦ x) (fun _ ↦ p) fun _ ↦ hx

/-- The degree-`p` piece of the tensor algebra is spanned by the products of homogeneous
generators whose degrees add up to `p`. -/
theorem tensorAlgebraPiece_eq_span (G : InternalGrading R M) (p : ℤ) :
    tensorAlgebraPiece G p = Submodule.span R {z | ∃ (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M),
      (∀ i, x i ∈ G.piece (d i)) ∧ ∑ i, d i = p ∧ z = TensorAlgebra.tprod R M n x} := by
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.2 ?_)
  · rw [mem_tensorAlgebraPiece_iff] at hz
    rw [← TensorAlgebra.ofDirectSum_toDirectSum z]
    refine TensorWords.gradedPiece_induction
      (motive := fun w ↦ TensorAlgebra.ofDirectSum w ∈ Submodule.span R _) hz ?_
      (by simp) (fun u v _ _ hu hv ↦ by simpa only [map_add] using add_mem hu hv)
      (fun r u _ hu ↦ by simpa only [map_smul] using Submodule.smul_mem _ r hu)
    intro n d x hx hd
    rw [TensorWords.of_def, DirectSum.lof_eq_of, TensorAlgebra.ofDirectSum_of_tprod]
    exact Submodule.subset_span ⟨n, d, x, hx, hd, rfl⟩
  · rintro _ ⟨n, d, x, hx, rfl, rfl⟩
    exact tprod_mem_tensorAlgebraPiece G d x hx

/-- A submodule containing every product of homogeneous generators of total degree `p` contains
the degree-`p` piece of the tensor algebra. -/
theorem tensorAlgebraPiece_le {G : InternalGrading R M} {p : ℤ}
    {C : Submodule R (TensorAlgebra R M)}
    (h : ∀ (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M), (∀ i, x i ∈ G.piece (d i)) →
      ∑ i, d i = p → TensorAlgebra.tprod R M n x ∈ C) :
    tensorAlgebraPiece G p ≤ C := by
  rw [tensorAlgebraPiece_eq_span, Submodule.span_le]
  rintro _ ⟨n, d, x, hx, hd, rfl⟩
  exact h n d x hx hd

/-- Multiplication in the tensor algebra adds input degrees. -/
instance (G : InternalGrading R M) : SetLike.GradedMonoid (tensorAlgebraPiece G) where
  one_mem := by
    rw [mem_tensorAlgebraPiece_iff, map_one]
    exact TensorWords.one_mem_gradedPiece G
  mul_mem _ _ _ _ ha hb := by
    rw [mem_tensorAlgebraPiece_iff] at ha hb ⊢
    rw [map_mul]
    exact TensorWords.mul_mem_gradedPiece G ha hb

/-- The tensor algebra is a `ℤ`-graded algebra for the input-degree grading. -/
noncomputable instance (G : InternalGrading R M) : GradedAlgebra (tensorAlgebraPiece G) :=
  (isInternal_tensorAlgebraPiece G).gradedAlgebra

/-- The inclusion of generators preserves degrees. -/
theorem isHomogeneous_tensorAlgebra_ι (G : InternalGrading R M) :
    LinearMap.IsHomogeneous (TensorAlgebra.ι R) G.piece (tensorAlgebraPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using ι_mem_tensorAlgebraPiece G hx

/-- The degree-`p` component of a generator is the generator of the degree-`p` component. -/
@[simp]
theorem decompose_tensorAlgebra_ι (G : InternalGrading R M) (x : M) (p : ℤ) :
    (DirectSum.decompose (tensorAlgebraPiece G) (TensorAlgebra.ι R x) p : TensorAlgebra R M) =
      TensorAlgebra.ι R (DirectSum.decompose G.piece x p : M) := by
  have h := (isHomogeneous_tensorAlgebra_ι G).map_decompose p x
  rw [add_zero] at h
  exact h.symm

section Lift

variable {A : Type uA} [Semiring A] [Algebra R A]

/-- The algebra map out of the tensor algebra induced by a degree-preserving linear map into a
graded algebra preserves input degree. -/
theorem isHomogeneous_tensorAlgebraLift (G : InternalGrading R M) (𝒜 : ℤ → Submodule R A)
    [SetLike.GradedMonoid 𝒜] {f : M →ₗ[R] A} (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) :
    LinearMap.IsHomogeneous (TensorAlgebra.lift R f).toLinearMap (tensorAlgebraPiece G) 𝒜 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_
  rw [add_zero]
  refine tensorAlgebraPiece_le (C := (𝒜 p).comap (TensorAlgebra.lift R f).toLinearMap)
    (fun n d x hx hd ↦ ?_) hz
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, TensorAlgebra.tprod_apply, map_list_prod,
    List.map_ofFn, ← hd, ← List.sum_ofFn]
  refine SetLike.list_prod_ofFn_mem_graded d _ fun i ↦ ?_
  simpa only [Function.comp_apply, TensorAlgebra.lift_ι_apply, add_zero] using hf.map_mem (hx i)

variable (G : InternalGrading R M) (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The graded algebra map out of the tensor algebra induced by a degree-preserving linear map into
a graded algebra. Its underlying algebra map is `TensorAlgebra.lift R f`. -/
noncomputable def tensorAlgebraGradedLift (f : M →ₗ[R] A)
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) : tensorAlgebraPiece G →ₐᵍ[R] 𝒜 where
  toAlgHom := TensorAlgebra.lift R f
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
      (isHomogeneous_tensorAlgebraLift G 𝒜 hf).map_mem hx

/-- The graded lift has the same underlying function as the ungraded lift. -/
@[simp]
theorem coe_tensorAlgebraGradedLift (f : M →ₗ[R] A)
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) :
    ⇑(tensorAlgebraGradedLift G 𝒜 f hf) = TensorAlgebra.lift R f :=
  (rfl)

/-- The graded lift extends the given linear map. -/
theorem tensorAlgebraGradedLift_ι (f : M →ₗ[R] A)
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) (x : M) :
    tensorAlgebraGradedLift G 𝒜 f hf (TensorAlgebra.ι R x) = f x := by
  simp

variable {G 𝒜} in
/-- Graded algebra maps out of the tensor algebra agree as soon as they agree on generators. -/
@[ext]
theorem tensorAlgebraGradedAlgHom_ext {φ ψ : tensorAlgebraPiece G →ₐᵍ[R] 𝒜}
    (h : ∀ x : M, φ (TensorAlgebra.ι R x) = ψ (TensorAlgebra.ι R x)) : φ = ψ := by
  have hφψ : φ.toAlgHom = ψ.toAlgHom := TensorAlgebra.hom_ext (LinearMap.ext h)
  exact GradedAlgHom.ext fun z ↦ DFunLike.congr_fun hφψ z

end Lift

end TauCeti
