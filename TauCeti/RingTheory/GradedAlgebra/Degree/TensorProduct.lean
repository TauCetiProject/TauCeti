/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Decomposition
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.GradedAlgebra.Degree.Filtration

/-!
# Total-degree tensor filtrations of nonnegatively graded algebras

For two nonnegatively graded `R`-algebras `A` and `B`, the total-degree tensor filtration
`AlgFiltration.tensorProduct` of their `GradedAlgebra.degreeFiltration`s agrees with the bidegree
`DirectSum.degreeTail` associated to the internal tensor decomposition `A i ⊗ B j` of `A ⊗[R] B`.
Consequently, a tensor lies in filtration order `k` precisely when all of its bidegree projections
`TensorProduct.map (GradedAlgebra.proj 𝒜 i) (GradedAlgebra.proj ℬ j)` of total degree below `k`
vanish, and two tensors are equal as soon as all of their bidegree projections agree. No flatness,
freeness, or commutativity of `A` or `B` is assumed.

## Main results

* `TauCeti.GradedAlgebra.tensorProduct_ext`: tensors in a tensor product of graded algebras are
  determined by their bidegree projections.
* `TauCeti.GradedAlgebra.map_proj_eq_zero_of_mem_ne`: a bidegree projection vanishes on any
  pure-degree tensor summand of a different bidegree.
* `TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff`: membership in the
  total-degree tensor ideal is the vanishing of all bidegree projections below the cutoff.
-/

public section

open scoped TensorProduct

namespace TauCeti.GradedAlgebra

variable {R A B ι κ : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [AddMonoid ι] [AddMonoid κ] [DecidableEq ι] [DecidableEq κ]
  (𝒜 : ι → Submodule R A) (ℬ : κ → Submodule R B)
  [_root_.GradedAlgebra 𝒜] [_root_.GradedAlgebra ℬ]

private abbrev bidegreeSubmodule (p : ι × κ) : Submodule R (A ⊗[R] B) :=
  Submodule.map₂ (TensorProduct.mk R A B) (𝒜 p.1) (ℬ p.2)

@[instance_reducible]
private noncomputable def bidegreeDecomposition :
    _root_.DirectSum.Decomposition (bidegreeSubmodule 𝒜 ℬ) :=
  (_root_.DirectSum.IsInternal.tensorProduct 𝒜 ℬ
    (_root_.DirectSum.Decomposition.isInternal 𝒜)
    (_root_.DirectSum.Decomposition.isInternal ℬ)).chooseDecomposition

private theorem coe_decompose_tensorProduct (t : A ⊗[R] B) (i : ι) (j : κ) :
    letI := bidegreeDecomposition 𝒜 ℬ
    (_root_.DirectSum.decompose (bidegreeSubmodule 𝒜 ℬ) t (i, j) : A ⊗[R] B) =
      TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) t := by
  let _ := bidegreeDecomposition 𝒜 ℬ
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    induction a using _root_.DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]
    | @homogeneous i' a =>
      induction b using _root_.DirectSum.Decomposition.inductionOn ℬ with
      | zero => simp
      | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
      | @homogeneous j' b =>
        have hab : (a : A) ⊗ₜ[R] (b : B) ∈ bidegreeSubmodule 𝒜 ℬ (i', j') :=
          Submodule.apply_mem_map₂ _ a.property b.property
        by_cases hp : (i', j') = (i, j)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
          rw [_root_.DirectSum.decompose_of_mem_same _ hab, TensorProduct.map_tmul,
            _root_.GradedAlgebra.proj_apply, _root_.GradedAlgebra.proj_apply,
            _root_.DirectSum.decompose_of_mem_same 𝒜 a.property,
            _root_.DirectSum.decompose_of_mem_same ℬ b.property]
        · rw [_root_.DirectSum.decompose_of_mem_ne _ hab hp, TensorProduct.map_tmul,
            _root_.GradedAlgebra.proj_apply, _root_.GradedAlgebra.proj_apply]
          by_cases hi : i' = i
          · rw [_root_.DirectSum.decompose_of_mem_ne ℬ b.property (fun hj => hp (Prod.ext hi hj)),
              TensorProduct.tmul_zero]
          · rw [_root_.DirectSum.decompose_of_mem_ne 𝒜 a.property hi, TensorProduct.zero_tmul]

/-- Elements of the tensor product of two graded algebras are determined by their bidegree
projections. -/
theorem tensorProduct_ext {t s : A ⊗[R] B}
    (h : ∀ i j,
      TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) t =
        TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) s) :
    t = s := by
  let _ := bidegreeDecomposition 𝒜 ℬ
  refine (_root_.DirectSum.decomposeLinearEquiv (bidegreeSubmodule 𝒜 ℬ)).injective (DirectSum.ext
    fun ⟨i, j⟩ => Subtype.ext ?_)
  exact (coe_decompose_tensorProduct 𝒜 ℬ t i j).trans
    ((h i j).trans (coe_decompose_tensorProduct 𝒜 ℬ s i j).symm)

/-- A bidegree projection vanishes on any pure-degree tensor summand of a different bidegree. -/
theorem map_proj_eq_zero_of_mem_ne {p : ι × κ} {t : A ⊗[R] B}
    (ht : t ∈ Submodule.map₂ (TensorProduct.mk R A B) (𝒜 p.1) (ℬ p.2))
    {i : ι} {j : κ} (hp : p ≠ (i, j)) :
    TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) t = 0 := by
  let _ := bidegreeDecomposition 𝒜 ℬ
  rw [← coe_decompose_tensorProduct 𝒜 ℬ t i j]
  exact _root_.DirectSum.decompose_of_mem_ne (bidegreeSubmodule 𝒜 ℬ) ht hp

variable (dA : ι →+ ℤ) (hnegA : ∀ i, dA i < 0 → 𝒜 i = ⊥)
  (dB : κ →+ ℤ) (hnegB : ∀ j, dB j < 0 → ℬ j = ⊥)

/-- Restricting scalars on the total-degree tensor ideal of two degree filtrations recovers the
bidegree `DirectSum.degreeTail`. -/
theorem tensorProduct_degreeFiltration_ideal_restrictScalars (k : ℕ) :
    (((degreeFiltration 𝒜 dA hnegA).tensorProduct R
        (degreeFiltration ℬ dB hnegB)).ideal k).restrictScalars R =
      TauCeti.DirectSum.degreeTail
        (fun p : ι × κ => Submodule.map₂ (TensorProduct.mk R A B) (𝒜 p.1) (ℬ p.2))
        (fun p => dA p.1 + dB p.2) k := by
  ext t
  simp only [Submodule.restrictScalars_mem, AlgFiltration.mem_tensorProduct_ideal_iff,
    degreeFiltration_ideal, degreeIdeal_restrictScalars,
    TauCeti.DirectSum.tensorFiltrationTail_degreeTail_eq 𝒜 dA hnegA ℬ dB hnegB k]

/-- Membership in the total-degree tensor ideal of two degree filtrations is the vanishing of all
bidegree projections of total degree below `k`. -/
theorem mem_tensorProduct_degreeFiltration_ideal_iff {k : ℕ} {t : A ⊗[R] B} :
    t ∈ ((degreeFiltration 𝒜 dA hnegA).tensorProduct R
        (degreeFiltration ℬ dB hnegB)).ideal k ↔
      ∀ i j, dA i + dB j < k →
        TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) t =
          0 := by
  let _ := bidegreeDecomposition 𝒜 ℬ
  rw [← Submodule.restrictScalars_mem R,
    tensorProduct_degreeFiltration_ideal_restrictScalars 𝒜 ℬ dA hnegA dB hnegB k,
    TauCeti.DirectSum.mem_degreeTail_iff]
  simp only [Prod.forall, coe_decompose_tensorProduct]

end TauCeti.GradedAlgebra
