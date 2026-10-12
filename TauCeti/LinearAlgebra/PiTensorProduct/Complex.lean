/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Differential
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# Total-degree tensor complexes in characteristic two

The degree-`n` tensor piece is spanned by pure tensors of homogeneous factors whose degrees sum
to `n`. The finite tensor differential raises total degree by one. Over a ground ring of
characteristic two it therefore defines a cochain complex whenever the factor differentials
square to zero. A tensor of degree-`q` elements lies in degree `#ι * q`; tensors of cycles are
cycles. This is the degree multiplication in the tensor construction of the Evens norm.

The construction accepts families of submodules, without requiring a direct-sum decomposition:
its terms are precisely their total-degree tensor spans. In applications to graded modules,
these are the usual total-degree pieces.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

namespace TauCeti.PiTensorProduct

universe u v w

variable {R : Type u} {ι : Type v} [Fintype ι] {M : ι → Type w}

section Semiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The total-degree tensor piece: the span of pure tensors with homogeneous factor degrees
summing to `n`. -/
noncomputable def degreePiece (ℳ : ∀ i, ℤ → Submodule R (M i)) (n : ℤ) :
    Submodule R (⨂[R] i, M i) :=
  Submodule.span R {z | ∃ (q : ι → ℤ) (x : ∀ i, M i),
    (∑ i, q i) = n ∧ (∀ i, x i ∈ ℳ i (q i)) ∧ _root_.PiTensorProduct.tprod R x = z}

/-- The defining span of a total-degree tensor piece. -/
theorem degreePiece_def (ℳ : ∀ i, ℤ → Submodule R (M i)) (n : ℤ) :
    degreePiece ℳ n = Submodule.span R {z | ∃ (q : ι → ℤ) (x : ∀ i, M i),
      (∑ i, q i) = n ∧ (∀ i, x i ∈ ℳ i (q i)) ∧ _root_.PiTensorProduct.tprod R x = z} :=
  (rfl)

/-- A pure tensor of homogeneous factors belongs to the piece of their total degree. -/
theorem tprod_mem_degreePiece (ℳ : ∀ i, ℤ → Submodule R (M i)) (q : ι → ℤ)
    (x : ∀ i, M i) (hx : ∀ i, x i ∈ ℳ i (q i)) :
    _root_.PiTensorProduct.tprod R x ∈ degreePiece ℳ (∑ i, q i) :=
  Submodule.subset_span ⟨q, x, rfl, hx, rfl⟩

/-- A linear map sends the degree-`n` tensor piece into a submodule exactly when it sends
each homogeneous pure tensor of total degree `n` into that submodule. -/
theorem degreePiece_le_comap_iff {N : Type*} [AddCommMonoid N] [Module R N]
    (ℳ : ∀ i, ℤ → Submodule R (M i)) (n : ℤ) (f : (⨂[R] i, M i) →ₗ[R] N)
    (P : Submodule R N) :
    degreePiece ℳ n ≤ P.comap f ↔
      ∀ (q : ι → ℤ) (x : ∀ i, M i), (∑ i, q i) = n →
        (∀ i, x i ∈ ℳ i (q i)) → f (_root_.PiTensorProduct.tprod R x) ∈ P := by
  rw [degreePiece_def, Submodule.span_le]
  constructor
  · intro h q x hq hx
    exact h ⟨q, x, hq, hx, rfl⟩
  · rintro h z ⟨q, x, hq, hx, rfl⟩
    exact h q x hq hx

/-- Applying degree-zero maps factorwise preserves total degree. -/
theorem map_mem_degreePiece {N : ι → Type*} [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (N i)] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (𝒩 : ∀ i, ℤ → Submodule R (N i)) (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (ℳ i) (𝒩 i) 0) {n : ℤ}
    {z : ⨂[R] i, M i} (hz : z ∈ degreePiece ℳ n) :
    _root_.PiTensorProduct.map f z ∈ degreePiece 𝒩 n := by
  refine (degreePiece_le_comap_iff ℳ n (_root_.PiTensorProduct.map f) (degreePiece 𝒩 n)).2
    (fun q x hq hx ↦ ?_) hz
  rw [_root_.PiTensorProduct.map_tprod, ← hq]
  exact tprod_mem_degreePiece 𝒩 q _ fun i ↦ by
    simpa only [add_zero] using (hf i).map_mem (hx i)

/-- Reindexing a graded family preserves total degree. -/
theorem reindex_mem_degreePiece {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (ℳ : ∀ i, ℤ → Submodule R (M i)) {n : ℤ}
    {z : ⨂[R] i, M i} (hz : z ∈ degreePiece ℳ n) :
    _root_.PiTensorProduct.reindex R M e z ∈
      degreePiece (fun j ↦ ℳ (e.symm j)) n := by
  refine (degreePiece_le_comap_iff ℳ n
    (_root_.PiTensorProduct.reindex R M e).toLinearMap
    (degreePiece (fun j ↦ ℳ (e.symm j)) n)).2 (fun q x hq hx ↦ ?_) hz
  rw [LinearEquiv.coe_coe, _root_.PiTensorProduct.reindex_tprod,
    ← hq, ← Equiv.sum_comp e.symm]
  exact tprod_mem_degreePiece (fun j ↦ ℳ (e.symm j)) (fun j ↦ q (e.symm j)) _ fun j ↦ hx _

/-- Equal factor degrees multiply by the number of tensor factors. -/
theorem tprod_mem_degreePiece_const (ℳ : ∀ i, ℤ → Submodule R (M i)) (q : ℤ)
    (x : ∀ i, M i) (hx : ∀ i, x i ∈ ℳ i q) :
    _root_.PiTensorProduct.tprod R x ∈ degreePiece ℳ ((Fintype.card ι : ℤ) * q) := by
  simpa using tprod_mem_degreePiece ℳ (fun _ ↦ q) x hx

/-- The tensor differential raises total degree by one if every factor differential does. -/
theorem isHomogeneous_differential (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1) :
    LinearMap.IsHomogeneous (differential d) (degreePiece ℳ) (degreePiece ℳ) 1 := by
  classical
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (degreePiece_le_comap_iff ℳ n (differential d) (degreePiece ℳ (n + 1))).2
    (fun q x hq hx ↦ ?_) hz
  rw [differential_tprod]
  apply Submodule.sum_mem
  intro i _
  have hsum : (∑ j, Function.update q i (q i + 1) j) = n + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hq
    omega
  rw [← hsum]
  apply tprod_mem_degreePiece
  intro j
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact (hdeg j).map_mem (hx j)
  · simpa only [Function.update_of_ne h] using hx j

/-- A tensor of cycles is a cycle for the finite tensor differential. -/
theorem differential_tprod_eq_zero (d : ∀ i, Module.End R (M i))
    (x : ∀ i, M i) (hx : ∀ i, d i (x i) = 0) :
    differential d (_root_.PiTensorProduct.tprod R x) = 0 := by
  classical
  rw [differential_tprod]
  apply Finset.sum_eq_zero
  intro i _
  rw [hx i]
  exact (_root_.PiTensorProduct.tprod R).map_update_zero x i

end Semiring

section Ring

open CategoryTheory

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The total-degree tensor cochain complex in characteristic two. Its terms are the tensor
pieces and its differential is the restriction of the sum of the factor differentials. -/
noncomputable def cochainComplex [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex (degreePiece ℳ) (differential d) (isHomogeneous_differential ℳ d hdeg)
    (fun _ x ↦ LinearMap.congr_fun (differential_comp_self d hd) x)

/-- The degree-`n` term is the total-degree tensor piece. -/
@[simp]
theorem cochainComplex_X [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).X n = ModuleCat.of R (degreePiece ℳ n) := by
  rw [cochainComplex, gradedCochainComplex_X]

/-- The complex differential is the restricted tensor differential, transported along the
identifications of its source and target degree pieces. -/
@[simp]
theorem cochainComplex_d [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).d n (n + 1) =
      eqToHom (cochainComplex_X ℳ d hdeg hd n) ≫
        ModuleCat.ofHom ((differential d).restrict
          (p := degreePiece ℳ n) (q := degreePiece ℳ (n + 1))
          fun _ hz ↦ (isHomogeneous_differential ℳ d hdeg).map_mem hz) ≫
        eqToHom (cochainComplex_X ℳ d hdeg hd (n + 1)).symm :=
  gradedCochainComplex_d n

/-- Under the degree-piece identification, the complex differential applies the finite tensor
differential to the underlying tensor. -/
theorem cochainComplex_d_apply [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) (z : degreePiece ℳ n) :
    CategoryTheory.eqToHom (cochainComplex_X ℳ d hdeg hd (n + 1))
        ((cochainComplex ℳ d hdeg hd).d n (n + 1)
          (CategoryTheory.eqToHom (cochainComplex_X ℳ d hdeg hd n).symm z)) =
      (⟨differential d z, (isHomogeneous_differential ℳ d hdeg).map_mem z.2⟩ :
        degreePiece ℳ (n + 1)) :=
  gradedCochainComplex_d_apply n z

/-- The degree-`n` term of the tensor cochain complex identified with its total-degree piece
as a linear equivalence. -/
noncomputable def cochainComplexXEquiv [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).X n ≃ₗ[R] degreePiece ℳ n :=
  gradedCochainComplexXEquiv (hdeg := isHomogeneous_differential ℳ d hdeg)
    (hsq := fun _ x ↦ LinearMap.congr_fun (differential_comp_self d hd) x) n

/-- Under the degree-piece equivalence, the complex differential applies the finite tensor
differential to the underlying tensor. -/
theorem cochainComplexXEquiv_d [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) (z : (cochainComplex ℳ d hdeg hd).X n) :
    (cochainComplexXEquiv ℳ d hdeg hd (n + 1)
        (((cochainComplex ℳ d hdeg hd).d n (n + 1)).hom z) : ⨂[R] i, M i) =
      differential d (cochainComplexXEquiv ℳ d hdeg hd n z) := by
  dsimp only [cochainComplexXEquiv]
  exact gradedCochainComplexXEquiv_d n z

end Ring

end TauCeti.PiTensorProduct
