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

/-!
# The input-degree grading of a tensor algebra

An internal grading `G` of a module `M` by an additive commutative monoid `ι` induces a grading of
the tensor algebra `TensorAlgebra R M` by input degree: a product `ι x₁ * ⋯ * ι xₙ` of homogeneous
generators of degrees `d₁, …, dₙ` has degree `d₁ + ⋯ + dₙ`. Unlike Mathlib's
`TensorAlgebra.gradedAlgebra`, which grades by word length, this grading sees the degrees of the
generators, such as integer degrees or parities in `ZMod 2`. It is the grading that descends to
quotients of the tensor algebra by homogeneous relations, such as the Koszul sign relations
defining free graded-commutative algebras.

The degree-`p` piece `TauCeti.tensorAlgebraPiece G p` is the submodule spanned by the products of
homogeneous generators of total degree `p`. Internality is proved from the universal property of
the tensor algebra via `GradedAlgebra.ofAlgHom`, over any commutative semiring and with no freeness
or flatness assumption on `M`. For integer gradings over a commutative ring, this agrees with the
total-letter-degree piece `TauCeti.TensorWords.gradedPiece G p` transported along Eric Wieser's
isomorphism `TensorAlgebra.equivDirectSum` (`TauCeti.mem_tensorAlgebraPiece_iff`).

The universal property of the tensor algebra is compatible with the grading: a linear map into a
graded algebra preserving degrees lifts to a graded algebra map, and graded algebra maps out of
the tensor algebra are determined by their values on generators. Coarsening the generator grading
along an additive homomorphism coarsens the tensor-algebra grading accordingly.

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
  coarsening the input-degree grading agrees with the input-degree grading of the coarsened module.
* `TauCeti.decompose_tensorAlgebra_ι`: the homogeneous components of a generator are the
  generators of its homogeneous components.
* `TauCeti.koszulTwist_tensorAlgebraPiece_ι`: for `ℤ`-gradings, the Koszul twist of the tensor
  algebra twists each generator.
* `TauCeti.isHomogeneous_tensorAlgebraLift`: the lift of a degree-preserving linear map into a
  graded algebra preserves input degree.
* `TauCeti.tensorAlgebraGradedAlgHom_ext`: graded algebra maps out of the tensor algebra agree
  when they agree on generators.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uM uA uι

section Semiring

variable {R : Type uR} {M : Type uM} {ι : Type uι} [CommSemiring R] [AddCommMonoid M] [Module R M]
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
  simpa [TensorAlgebra.tprod_apply] using
    tprod_mem_tensorAlgebraPiece G (fun _ : Fin 1 ↦ p) (fun _ ↦ x) fun _ ↦ hx

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
    {b : TensorAlgebra R M} (hx : x ∈ G.piece p) (hb : b ∈ tensorAlgebraPiece G q) :
    TensorAlgebra.ι R x * b ∈ tensorAlgebraPiece G (p + q) := by
  refine tensorAlgebraPiece_le
    (C := (tensorAlgebraPiece G (p + q)).comap (LinearMap.mulLeft R (TensorAlgebra.ι R x)))
    (fun n d y hy hd ↦ ?_) hb
  have hmul : TensorAlgebra.ι R x * TensorAlgebra.tprod R M n y =
      TensorAlgebra.tprod R M (n + 1) (Fin.cons x y) := by
    simp [TensorAlgebra.tprod_apply, List.ofFn_succ]
  have hsum : ∑ i, Fin.cons p d i = p + q := by
    rw [Fin.sum_univ_succ, Fin.cons_zero, ← hd]
    rfl
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, hmul, ← hsum]
  exact tprod_mem_tensorAlgebraPiece G (Fin.cons p d) (Fin.cons x y) (Fin.cases hx hy)

/-- Multiplication in the tensor algebra adds input degrees. -/
instance (G : InternalGrading R M ι) : SetLike.GradedMonoid (tensorAlgebraPiece G) where
  one_mem := by
    simpa [TensorAlgebra.tprod_apply] using
      tprod_mem_tensorAlgebraPiece G Fin.elim0 Fin.elim0 fun i ↦ i.elim0
  mul_mem p q a b ha hb := by
    refine tensorAlgebraPiece_le
      (C := (tensorAlgebraPiece G (p + q)).comap (LinearMap.mulRight R b))
      (fun n d x hx hd ↦ ?_) ha
    clear ha
    subst hd
    rw [Submodule.mem_comap, LinearMap.mulRight_apply]
    induction n with
    | zero => simpa [TensorAlgebra.tprod_apply] using hb
    | succ n ih =>
      have hmul : TensorAlgebra.tprod R M (n + 1) x * b =
          TensorAlgebra.ι R (x 0) * (TensorAlgebra.tprod R M n (x ∘ Fin.succ) * b) := by
        simp [TensorAlgebra.tprod_apply, List.ofFn_succ, mul_assoc]
      rw [hmul, Fin.sum_univ_succ, add_assoc]
      exact ι_mul_mem_tensorAlgebraPiece G (hx 0)
        (ih (d ∘ Fin.succ) (x ∘ Fin.succ) fun i ↦ hx i.succ)

private noncomputable def gradedι (G : InternalGrading R M ι) :
    M →ₗ[R] ⨁ p, tensorAlgebraPiece G p :=
  DirectSum.lmap
    (fun p ↦ LinearMap.codRestrict (tensorAlgebraPiece G p)
      ((TensorAlgebra.ι R).comp (G.piece p).subtype) fun x ↦ ι_mem_tensorAlgebraPiece G x.2) ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

private theorem gradedι_of_mem (G : InternalGrading R M ι) {p : ι} {x : M} (hx : x ∈ G.piece p) :
    gradedι G x =
      DirectSum.of (fun q ↦ ↥(tensorAlgebraPiece G q)) p
        ⟨TensorAlgebra.ι R x, ι_mem_tensorAlgebraPiece G hx⟩ := by
  simp only [gradedι, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe G.piece p ⟨x, hx⟩, DirectSum.lmap_lof,
    DirectSum.lof_eq_of]
  rfl

private theorem lift_gradedι_tprod (G : InternalGrading R M ι) :
    ∀ {n : ℕ} (d : Fin n → ι) (x : Fin n → M) (hx : ∀ i, x i ∈ G.piece (d i)),
      TensorAlgebra.lift R (gradedι G) (TensorAlgebra.tprod R M n x) =
        DirectSum.of (fun q ↦ ↥(tensorAlgebraPiece G q)) (∑ i, d i)
          ⟨TensorAlgebra.tprod R M n x, tprod_mem_tensorAlgebraPiece G d x hx⟩
  | 0, d, x, _ => by
    simp only [TensorAlgebra.tprod_apply, List.ofFn_zero, List.prod_nil, Fin.sum_univ_zero, map_one,
      DirectSum.one_def]
    rfl
  | n + 1, d, x, hx => by
    have hmul : TensorAlgebra.tprod R M (n + 1) x =
        TensorAlgebra.ι R (x 0) * TensorAlgebra.tprod R M n (x ∘ Fin.succ) := by
      simp [TensorAlgebra.tprod_apply, List.ofFn_succ]
    simp only [hmul, map_mul, TensorAlgebra.lift_ι_apply, gradedι_of_mem G (hx 0),
      lift_gradedι_tprod G (d ∘ Fin.succ) (x ∘ Fin.succ) (fun i ↦ hx i.succ),
      DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (Sigma.subtype_ext (Fin.sum_univ_succ d).symm rfl)

/-- The input-degree pieces of the tensor algebra form an internal direct sum. -/
theorem isInternal_tensorAlgebraPiece (G : InternalGrading R M ι) :
    DirectSum.IsInternal (tensorAlgebraPiece G) :=
  (GradedAlgebra.ofAlgHom (tensorAlgebraPiece G) (TensorAlgebra.lift R (gradedι G))
    (TensorAlgebra.hom_ext <| G.linearMap_ext fun p x hx ↦ by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        TensorAlgebra.lift_ι_apply]
      rw [gradedι_of_mem G hx, DirectSum.coeAlgHom_of]
      rfl)
    fun p z ↦ by
      obtain ⟨w, hw⟩ := z
      rw [← DirectSum.lof_eq_of R]
      refine Submodule.span_induction
        (p := fun w hw ↦ TensorAlgebra.lift R (gradedι G) w =
          DirectSum.lof R ι (fun q ↦ ↥(tensorAlgebraPiece G q)) p ⟨w, hw⟩)
        (fun w hw ↦ ?_) (by rw [map_zero]; symm; exact map_zero _)
        (fun u v _ _ ihu ihv ↦ by rw [map_add, ihu, ihv, ← map_add]; rfl)
        (fun r u _ ihu ↦ by rw [AlgHom.map_smul_of_tower, ihu, ← map_smul]; rfl) hw
      obtain ⟨n, d, x, hx, rfl, rfl⟩ := hw
      rw [DirectSum.lof_eq_of]
      exact lift_gradedι_tprod G d x hx).toDecomposition.isInternal

/-- The tensor algebra is a graded algebra for the input-degree grading. -/
noncomputable instance (G : InternalGrading R M ι) : GradedAlgebra (tensorAlgebraPiece G) :=
  (isInternal_tensorAlgebraPiece G).gradedAlgebra

/-- Coarsening the input-degree grading of a tensor algebra along an additive homomorphism of
index monoids agrees with the input-degree grading of the coarsened generator grading. -/
theorem coarsenGrading_tensorAlgebraPiece {κ F : Type*} [DecidableEq κ] [AddCommMonoid κ]
    [FunLike F ι κ] [AddMonoidHomClass F ι κ] (G : InternalGrading R M ι) (f : F) :
    coarsenGrading (tensorAlgebraPiece G) f = tensorAlgebraPiece (G.coarsen f) := by
  have hle : ∀ k, coarsenGrading (tensorAlgebraPiece G) f k ≤
      tensorAlgebraPiece (G.coarsen f) k := fun k ↦
    coarsenGrading_le_iff.2 fun p hp ↦ tensorAlgebraPiece_le fun n d x hx hd ↦ by
      rw [← hp, ← hd, map_sum]
      exact tprod_mem_tensorAlgebraPiece (G.coarsen f) (f ∘ d) x fun i ↦
        mem_coarsenGrading_of_mem f (hx i)
  funext k
  refine le_antisymm (hle k) fun z hz ↦ ?_
  have hdec := DirectSum.map_decompose_shift
    (coarsenGrading (tensorAlgebraPiece G) f) (tensorAlgebraPiece (G.coarsen f))
    (AddMonoidHom.id _) id Function.injective_id (fun j _ hy ↦ hle j hy) k z
  rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, id_eq,
    DirectSum.decompose_of_mem_same _ hz] at hdec
  exact hdec ▸ (DirectSum.decompose (coarsenGrading (tensorAlgebraPiece G) f) z k).property

/-- The parity grading of the input-degree grading of a tensor algebra is the input-degree
grading of the parity-graded generating module. -/
theorem parityGrading_tensorAlgebraPiece (G : InternalGrading R M ℤ) :
    parityGrading (tensorAlgebraPiece G) = tensorAlgebraPiece G.parity :=
  coarsenGrading_tensorAlgebraPiece G (Int.castAddHom (ZMod 2))

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
  (DirectSum.map_decompose_shift G.piece (tensorAlgebraPiece G)
    (TensorAlgebra.ι R).toAddMonoidHom id Function.injective_id
    (fun _ _ hx ↦ ι_mem_tensorAlgebraPiece G hx) p x).symm

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

end Semiring

section Int

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- An element of the tensor algebra has integer input degree `p` exactly when its image in the
direct sum of tensor powers has total letter degree `p`. -/
theorem mem_tensorAlgebraPiece_iff {G : InternalGrading R M ℤ} {p : ℤ} {x : TensorAlgebra R M} :
    x ∈ tensorAlgebraPiece G p ↔ TensorAlgebra.toDirectSum x ∈ TensorWords.gradedPiece G p := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine tensorAlgebraPiece_le
      (C := (TensorWords.gradedPiece G p).comap TensorAlgebra.toDirectSum.toLinearMap)
      (fun n d y hy hd ↦ ?_) hx
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
      ← DirectSum.lof_eq_of R, ← TensorWords.of_def, ← hd]
    exact TensorWords.mem_gradedPiece_of_tprod G y d hy
  · rw [← TensorAlgebra.ofDirectSum_toDirectSum x]
    refine TensorWords.gradedPiece_induction
      (motive := fun w ↦ TensorAlgebra.ofDirectSum w ∈ tensorAlgebraPiece G p) hx
      (fun n d y hy hd ↦ ?_) (by simp)
      (fun u v _ _ hu hv ↦ by simpa only [map_add] using add_mem hu hv)
      (fun r u _ hu ↦ by simpa only [map_smul] using Submodule.smul_mem _ r hu)
    rw [TensorWords.of_def, DirectSum.lof_eq_of, TensorAlgebra.ofDirectSum_of_tprod, ← hd]
    exact tprod_mem_tensorAlgebraPiece G d y hy

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
