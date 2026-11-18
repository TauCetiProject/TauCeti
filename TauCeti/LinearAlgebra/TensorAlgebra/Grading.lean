/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading
import TauCeti.Algebra.DirectSum.Internal

/-!
# The input-degree grading of a tensor algebra

An internal `ι`-grading `G` of a module `M`, indexed by an additive commutative monoid `ι` with
decidable equality, induces a grading of the tensor algebra `TensorAlgebra R M` by input degree:
a product `ι x₁ * ⋯ * ι xₙ` of homogeneous generators of degrees `d₁, …, dₙ` has degree
`d₁ + ⋯ + dₙ`. Unlike Mathlib's `TensorAlgebra.gradedAlgebra`, which grades by word length, this
grading sees the degrees of the generators; for `ι = ℤ` it can be negative, and for `ι = ZMod 2`
it records generator parity. It is the grading that descends to quotients of the tensor algebra
by homogeneous relations, such as the Koszul sign relations defining free supercommutative
algebras.

The degree-`p` piece `TauCeti.tensorAlgebraPiece G p` is the `R`-span of products
`TensorAlgebra.tprod R M n x` of homogeneous generators whose degrees add up to `p`. Following
Eric Wieser's construction of `TensorAlgebra.gradedAlgebra` in
`Mathlib.LinearAlgebra.TensorAlgebra.Grading`, internality and compatibility with multiplication
are established through `GradedAlgebra.ofAlgHom` by lifting the graded generator inclusion out of
`TensorAlgebra R M`, over any commutative semiring and with no freeness or flatness assumption on
`M`. Over a commutative ring with `ι = ℤ`, `TauCeti.mem_tensorAlgebraPiece_iff` identifies this
grading with the total-letter-degree grading of `TauCeti.TensorWords` along
`TensorAlgebra.equivDirectSum`.

Coarsening the grading of `M` along an additive homomorphism `f : ι →+ κ` coarsens the
input-degree grading of `TensorAlgebra R M` along `f`
(`TauCeti.coarsenGrading_tensorAlgebraPiece`). The universal property of the tensor algebra is
also compatible with input degree: a degree-preserving linear map into a graded algebra lifts to
a graded algebra map, and graded algebra maps out of the tensor algebra are determined by their
values on generators.

## Main definitions

* `TauCeti.tensorAlgebraPiece`: the degree-`p` piece of the input-degree grading.
* `TauCeti.tensorAlgebraGradedLift`: the graded algebra map induced by a degree-preserving linear
  map into a graded algebra.

## Main results

* `TauCeti.tensorAlgebraPiece_eq_span`: the degree-`p` piece is spanned by the products of
  homogeneous generators of total degree `p`.
* `TauCeti.isInternal_tensorAlgebraPiece`: the pieces form an internal direct sum.
* The instance `GradedAlgebra (tensorAlgebraPiece G)`.
* `TauCeti.coarsenGrading_tensorAlgebraPiece` and `TauCeti.parityGrading_tensorAlgebraPiece`:
  coarsening the input grading coarsens the tensor-algebra grading.
* `TauCeti.decompose_tensorAlgebra_ι`: the homogeneous components of a generator are the
  generators of its homogeneous components.
* `TauCeti.mem_tensorAlgebraPiece_iff`: for `ι = ℤ`, membership agrees with total letter degree in
  `TauCeti.TensorWords`.
* `TauCeti.koszulTwist_tensorAlgebraPiece_ι`: the Koszul twist of the `ℤ`-graded tensor algebra
  twists each generator.
* `TauCeti.isHomogeneous_tensorAlgebraLift`: the lift of a degree-preserving linear map into a
  graded algebra preserves input degree.
* `TauCeti.tensorAlgebraGradedAlgHom_ext`: graded algebra maps out of the tensor algebra agree
  when they agree on generators.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uM uA

section Semiring

variable {R : Type uR} {M : Type uM} {ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] [AddCommMonoid ι]

/-- The degree-`p` piece of the input-degree grading of `TensorAlgebra R M` induced by an
internal grading `G` of `M`. It is spanned by the products `ι x₁ * ⋯ * ι xₙ` of homogeneous
generators whose degrees add up to `p` (`tensorAlgebraPiece_eq_span`). -/
def tensorAlgebraPiece (G : InternalGrading R M ι) (p : ι) :
    Submodule R (TensorAlgebra R M) :=
  Submodule.span R {z | ∃ (n : ℕ) (d : Fin n → ι) (x : Fin n → M),
    (∀ i, x i ∈ G.piece (d i)) ∧ ∑ i, d i = p ∧ z = TensorAlgebra.tprod R M n x}

/-- The degree-`p` piece of the tensor algebra is spanned by the products of homogeneous
generators whose degrees add up to `p`. -/
theorem tensorAlgebraPiece_eq_span (G : InternalGrading R M ι) (p : ι) :
    tensorAlgebraPiece G p = Submodule.span R {z | ∃ (n : ℕ) (d : Fin n → ι) (x : Fin n → M),
      (∀ i, x i ∈ G.piece (d i)) ∧ ∑ i, d i = p ∧ z = TensorAlgebra.tprod R M n x} :=
  (rfl)

/-- A product of homogeneous generators lies in the piece of the sum of their degrees. -/
theorem tprod_mem_tensorAlgebraPiece (G : InternalGrading R M ι) {n : ℕ} (d : Fin n → ι)
    (x : Fin n → M) (hx : ∀ i, x i ∈ G.piece (d i)) :
    TensorAlgebra.tprod R M n x ∈ tensorAlgebraPiece G (∑ i, d i) :=
  Submodule.subset_span ⟨n, d, x, hx, rfl, rfl⟩

/-- A generator of degree `p` lies in the degree-`p` piece of the tensor algebra. -/
theorem ι_mem_tensorAlgebraPiece (G : InternalGrading R M ι) {p : ι} {x : M}
    (hx : x ∈ G.piece p) : TensorAlgebra.ι R x ∈ tensorAlgebraPiece G p := by
  have h := tprod_mem_tensorAlgebraPiece G (fun _ : Fin 1 ↦ p) (fun _ ↦ x) fun _ ↦ hx
  simpa only [Fin.sum_univ_one, TensorAlgebra.tprod_apply, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one] using h

/-- A submodule containing every product of homogeneous generators of total degree `p` contains
the degree-`p` piece of the tensor algebra. -/
theorem tensorAlgebraPiece_le {G : InternalGrading R M ι} {p : ι}
    {C : Submodule R (TensorAlgebra R M)}
    (h : ∀ (n : ℕ) (d : Fin n → ι) (x : Fin n → M), (∀ i, x i ∈ G.piece (d i)) →
      ∑ i, d i = p → TensorAlgebra.tprod R M n x ∈ C) :
    tensorAlgebraPiece G p ≤ C := by
  rw [tensorAlgebraPiece_eq_span, Submodule.span_le]
  rintro _ ⟨n, d, x, hx, hd, rfl⟩
  exact h n d x hx hd

private theorem ι_mul_mem_tensorAlgebraPiece (G : InternalGrading R M ι) {p q : ι} {x : M}
    {z : TensorAlgebra R M} (hx : x ∈ G.piece p) (hz : z ∈ tensorAlgebraPiece G q) :
    TensorAlgebra.ι R x * z ∈ tensorAlgebraPiece G (p + q) := by
  refine Submodule.span_induction (p := fun z _ ↦
      TensorAlgebra.ι R x * z ∈ tensorAlgebraPiece G (p + q))
    (fun _ hmem ↦ ?_) (by simp)
    (fun u v _ _ hu hv ↦ by rw [mul_add]; exact add_mem hu hv)
    (fun r u _ hu ↦ by rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu) hz
  obtain ⟨n, d, y, hy, rfl, rfl⟩ := hmem
  have hcons : ∀ i : Fin (n + 1),
      Fin.cons (α := fun _ ↦ M) x y i ∈ G.piece (Fin.cons (α := fun _ ↦ ι) p d i) :=
    Fin.cases hx hy
  simpa only [Fin.sum_cons, TensorAlgebra.tprod_apply, List.ofFn_succ, Fin.cons_zero,
    Fin.cons_succ, List.prod_cons] using
    tprod_mem_tensorAlgebraPiece G (Fin.cons (α := fun _ ↦ ι) p d)
      (Fin.cons (α := fun _ ↦ M) x y) hcons

/-- Multiplication in the tensor algebra adds input degrees. -/
instance (G : InternalGrading R M ι) : SetLike.GradedMonoid (tensorAlgebraPiece G) where
  one_mem := by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, TensorAlgebra.tprod_apply,
      List.ofFn_zero, List.prod_nil] using
      tprod_mem_tensorAlgebraPiece G Fin.elim0 Fin.elim0 fun i ↦ Fin.elim0 i
  mul_mem p q a b ha hb := by
    refine Submodule.span_induction (p := fun a _ ↦ a * b ∈ tensorAlgebraPiece G (p + q))
      (fun _ hmem ↦ ?_) (by simp)
      (fun u v _ _ hu hv ↦ by rw [add_mul]; exact add_mem hu hv)
      (fun r u _ hu ↦ by rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hu) ha
    clear a ha
    obtain ⟨n, d, x, hx, rfl, rfl⟩ := hmem
    induction n with
    | zero =>
      simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, TensorAlgebra.tprod_apply,
        List.ofFn_zero, List.prod_nil, one_mul] using hb
    | succ n ih =>
      rw [Fin.sum_univ_succ, add_assoc]
      have hprod : TensorAlgebra.tprod R M (n + 1) x * b =
          TensorAlgebra.ι R (x 0) * (TensorAlgebra.tprod R M n (fun i ↦ x i.succ) * b) := by
        simp only [TensorAlgebra.tprod_apply, List.ofFn_succ, List.prod_cons, mul_assoc]
      rw [hprod]
      exact ι_mul_mem_tensorAlgebraPiece G (hx 0)
        (ih (fun i ↦ d i.succ) (fun i ↦ x i.succ) fun i ↦ hx i.succ)

/-- Auxiliary graded generator map sending each homogeneous component `x_p ∈ G.piece p` to the
degree-`p` summand of `⨁ q, tensorAlgebraPiece G q`, following `TensorAlgebra.GradedAlgebra.ι` in
`Mathlib.LinearAlgebra.TensorAlgebra.Grading`. -/
private noncomputable def tensorAlgebraGradedι (G : InternalGrading R M ι) :
    M →ₗ[R] ⨁ p : ι, tensorAlgebraPiece G p :=
  (DirectSum.toModule R ι _ fun p ↦
    DirectSum.lof R ι (fun q ↦ tensorAlgebraPiece G q) p ∘ₗ
      (TensorAlgebra.ι R ∘ₗ (G.piece p).subtype).codRestrict _
        (fun x ↦ ι_mem_tensorAlgebraPiece G x.2)) ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

private theorem tensorAlgebraGradedι_of_mem (G : InternalGrading R M ι) {p : ι} {x : M}
    (hx : x ∈ G.piece p) :
    tensorAlgebraGradedι G x =
      DirectSum.of (fun q ↦ ↥(tensorAlgebraPiece G q)) p
        ⟨TensorAlgebra.ι R x, ι_mem_tensorAlgebraPiece G hx⟩ := by
  simp only [tensorAlgebraGradedι, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem G.piece hx,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

private theorem lift_tensorAlgebraGradedι_of_mem (G : InternalGrading R M ι) (p : ι)
    (x : tensorAlgebraPiece G p) :
    TensorAlgebra.lift R (tensorAlgebraGradedι G) x =
      DirectSum.lof R ι (fun q ↦ ↥(tensorAlgebraPiece G q)) p x := by
  obtain ⟨z, hz⟩ := x
  refine Submodule.span_induction
    (p := fun z hz ↦ TensorAlgebra.lift R (tensorAlgebraGradedι G) z =
      DirectSum.lof R ι (fun q ↦ ↥(tensorAlgebraPiece G q)) p ⟨z, hz⟩)
    (fun _ hmem ↦ ?_)
    (by rw [map_zero]; exact (map_zero _).symm)
    (fun u v hu hv ihu ihv ↦ by rw [map_add, ihu, ihv, ← map_add]; rfl)
    (fun r u hu ihu ↦ by rw [AlgHom.map_smul_of_tower, ihu, ← map_smul]; rfl) hz
  clear z hz
  obtain ⟨n, d, x, hx, rfl, rfl⟩ := hmem
  induction n with
  | zero =>
    simp only [TensorAlgebra.tprod_apply, List.ofFn_zero, List.prod_nil, map_one,
      DirectSum.lof_eq_of]
    rfl
  | succ n ih =>
    have hprod : TensorAlgebra.tprod R M (n + 1) x =
        TensorAlgebra.ι R (x 0) * TensorAlgebra.tprod R M n (fun i ↦ x i.succ) := by
      simp only [TensorAlgebra.tprod_apply, List.ofFn_succ, List.prod_cons]
    simp only [DirectSum.lof_eq_of] at ih ⊢
    have hstep := ih (fun i ↦ d i.succ) (fun i ↦ x i.succ) fun i ↦ hx i.succ
    calc
      TensorAlgebra.lift R (tensorAlgebraGradedι G) (TensorAlgebra.tprod R M (n + 1) x) =
          TensorAlgebra.lift R (tensorAlgebraGradedι G) (TensorAlgebra.ι R (x 0)) *
            TensorAlgebra.lift R (tensorAlgebraGradedι G)
              (TensorAlgebra.tprod R M n fun i ↦ x i.succ) := by
        rw [hprod, map_mul]
      _ = DirectSum.of (fun q ↦ ↥(tensorAlgebraPiece G q)) (d 0)
            ⟨TensorAlgebra.ι R (x 0), ι_mem_tensorAlgebraPiece G (hx 0)⟩ *
          DirectSum.of (fun q ↦ ↥(tensorAlgebraPiece G q)) (∑ i : Fin n, d i.succ)
            ⟨TensorAlgebra.tprod R M n fun i ↦ x i.succ,
              tprod_mem_tensorAlgebraPiece G (fun i ↦ d i.succ) (fun i ↦ x i.succ)
                fun i ↦ hx i.succ⟩ := by
        rw [TensorAlgebra.lift_ι_apply, tensorAlgebraGradedι_of_mem G (hx 0), hstep]
      _ = _ := by
        rw [DirectSum.of_mul_of]
        exact DirectSum.of_eq_of_gradedMonoid_eq
          (Sigma.subtype_ext (Fin.sum_univ_succ d).symm hprod.symm)

/-- The input-degree pieces of the tensor algebra form an internal direct sum, established via
`GradedAlgebra.ofAlgHom` following Eric Wieser's `TensorAlgebra.gradedAlgebra`. -/
theorem isInternal_tensorAlgebraPiece (G : InternalGrading R M ι) :
    DirectSum.IsInternal (tensorAlgebraPiece G) := by
  let _ : GradedAlgebra (tensorAlgebraPiece G) :=
    GradedAlgebra.ofAlgHom (tensorAlgebraPiece G)
      (TensorAlgebra.lift R (tensorAlgebraGradedι G))
      (by
        apply TensorAlgebra.hom_ext
        refine G.linearMap_ext fun p x hx ↦ ?_
        simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
          TensorAlgebra.lift_ι_apply, tensorAlgebraGradedι_of_mem G hx, DirectSum.coeAlgHom_of,
          AlgHom.id_apply])
      (lift_tensorAlgebraGradedι_of_mem G)
  exact DirectSum.Decomposition.isInternal (tensorAlgebraPiece G)

/-- The tensor algebra is an `ι`-graded algebra for the input-degree grading. -/
noncomputable instance (G : InternalGrading R M ι) : GradedAlgebra (tensorAlgebraPiece G) :=
  (isInternal_tensorAlgebraPiece G).gradedAlgebra

/-- Coarsening the input grading of `M` along an additive homomorphism coarsens the input-degree
grading of `TensorAlgebra R M` along the same homomorphism. -/
theorem coarsenGrading_tensorAlgebraPiece (G : InternalGrading R M ι) {κ : Type*}
    [DecidableEq κ] [AddCommMonoid κ] (f : ι →+ κ) :
    coarsenGrading (tensorAlgebraPiece G) f = tensorAlgebraPiece (G.coarsen f) := by
  refine DirectSum.Decomposition.eq_of_subset
    (coarsenGrading (tensorAlgebraPiece G) f) (tensorAlgebraPiece (G.coarsen f))
    fun j ↦ coarsenGrading_le_iff.2 fun p hp ↦ ?_
  refine tensorAlgebraPiece_le fun n d x hx hd ↦ ?_
  have hsum : ∑ i, f (d i) = j := by rw [← map_sum, hd, hp]
  refine hsum ▸ tprod_mem_tensorAlgebraPiece (G.coarsen f) (fun i ↦ f (d i)) x fun i ↦ ?_
  rw [InternalGrading.coarsen_piece]
  exact mem_coarsenGrading_of_mem f (hx i)

/-- The inclusion of generators preserves degrees. -/
theorem isHomogeneous_tensorAlgebra_ι (G : InternalGrading R M ι) :
    LinearMap.IsHomogeneous (TensorAlgebra.ι R) G.piece (tensorAlgebraPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using ι_mem_tensorAlgebraPiece G hx

/-- The degree-`p` component of a generator is the generator of the degree-`p` component. -/
@[simp]
theorem decompose_tensorAlgebra_ι (G : InternalGrading R M ι) (x : M) (p : ι) :
    (DirectSum.decompose (tensorAlgebraPiece G) (TensorAlgebra.ι R x) p : TensorAlgebra R M) =
      TensorAlgebra.ι R (DirectSum.decompose G.piece x p : M) :=
  (DirectSum.map_decompose_shift G.piece (tensorAlgebraPiece G) (TensorAlgebra.ι R).toAddMonoidHom
    id Function.injective_id (fun _ _ hx ↦ ι_mem_tensorAlgebraPiece G hx) p x).symm

section Lift

variable {A : Type uA} [Semiring A] [Algebra R A]

/-- The algebra map out of the tensor algebra induced by a degree-preserving linear map into a
graded algebra preserves input degree. -/
theorem isHomogeneous_tensorAlgebraLift (G : InternalGrading R M ι) (𝒜 : ι → Submodule R A)
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

variable (G : InternalGrading R M ι) (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

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

omit [DecidableEq ι] [AddCommMonoid ι] in
/-- Reducing an integer input grading modulo two coarsens the tensor-algebra input-degree grading
to its parity grading. -/
theorem parityGrading_tensorAlgebraPiece (G : InternalGrading R M ℤ) :
    parityGrading (tensorAlgebraPiece G) = tensorAlgebraPiece G.parity := by
  rw [parityGrading_eq_coarsenGrading, InternalGrading.parity_eq_coarsen]
  exact coarsenGrading_tensorAlgebraPiece G (Int.castAddHom (ZMod 2))

end Semiring

section Int

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- An element of the tensor algebra has integer input degree `p` exactly when its image in the
direct sum of tensor powers has total letter degree `p`. -/
theorem mem_tensorAlgebraPiece_iff {G : InternalGrading R M ℤ} {p : ℤ} {x : TensorAlgebra R M} :
    x ∈ tensorAlgebraPiece G p ↔ TensorAlgebra.toDirectSum x ∈ TensorWords.gradedPiece G p := by
  have hpiece : tensorAlgebraPiece G =
      ((TensorWords.grading G).map TensorAlgebra.equivDirectSum.symm.toLinearEquiv).piece := by
    refine DirectSum.Decomposition.eq_of_subset (tensorAlgebraPiece G)
      ((TensorWords.grading G).map TensorAlgebra.equivDirectSum.symm.toLinearEquiv).piece
      fun q ↦ tensorAlgebraPiece_le fun n d y hy hd ↦ ?_
    simp only [InternalGrading.mem_map_piece_iff, TensorWords.grading_piece,
      AlgEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm, AlgEquiv.toLinearEquiv_apply,
      TensorAlgebra.equivDirectSum_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
      ← DirectSum.lof_eq_of R, ← TensorWords.of_def, ← hd]
    exact TensorWords.mem_gradedPiece_of_tprod G y d hy
  simp only [congrFun hpiece p, InternalGrading.mem_map_piece_iff, TensorWords.grading_piece,
    AlgEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm, AlgEquiv.toLinearEquiv_apply,
    TensorAlgebra.equivDirectSum_apply]

/-- The Koszul twist of the tensor algebra, graded by input degree, twists each generator by the
Koszul twist of the grading of the generators.  This is the value on generators of the Koszul
automorphism `koszulTwistAlgEquiv (tensorAlgebraPiece G) n`. -/
@[simp]
theorem koszulTwist_tensorAlgebraPiece_ι (G : InternalGrading R M ℤ) (n : ℤ) (x : M) :
    (InternalGrading.ofDecomposition (tensorAlgebraPiece G)).koszulTwist n (TensorAlgebra.ι R x) =
      TensorAlgebra.ι R (G.koszulTwist n x) := by
  have h : (InternalGrading.ofDecomposition (tensorAlgebraPiece G)).koszulTwist n ∘ₗ
      TensorAlgebra.ι R = TensorAlgebra.ι R ∘ₗ G.koszulTwist n :=
    G.linearMap_ext fun p x hx ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ (ι_mem_tensorAlgebraPiece G hx),
        G.koszulTwist_apply_of_mem hx, map_smul]
  exact LinearMap.congr_fun h x

end Int

end TauCeti
