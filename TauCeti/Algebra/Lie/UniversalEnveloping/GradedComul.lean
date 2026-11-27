/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.GradedAlgebra.TensorProduct

/-!
# The comultiplication of a graded enveloping algebra

Let `L` be a Lie algebra graded by `ℕ`, and grade its enveloping algebra `U` by total Lie degree,
with homogeneous projections `π n`. The comultiplication `Δ` of `U` is homogeneous: it sends the
degree-`n` piece of `U` into the span of the tensors `a ⊗ b` with `a` and `b` homogeneous of
degrees adding to `n`. Consequently the bihomogeneous component `(π i ⊗ π j) (Δ a)` depends only
on the degree-`(i + j)` component of `a`, and the comultiplication of `π n a` is the sum of these
bihomogeneous components over `i + j = n`.

This gives a componentwise criterion for primitivity: if `Δ a` agrees with `1 ⊗ a + a ⊗ 1` in all
bidegrees `(i, j)` with `i + j = n`, then `π n a` is primitive. For the total-degree filtration
`F` of `U`, the comultiplication carries `F k` into the total-degree filtration of `U ⊗ U`, and
the bihomogeneous components in bidegrees of total degree below `k` vanish on that filtration
term. Hence an element whose comultiplication agrees with `1 ⊗ a + a ⊗ 1` modulo filtration
order `k` has primitive components in every degree below `k`. Over a rational algebra, where
primitive elements are exactly the image of the Lie algebra, this is the truncated form of
Friedrichs' criterion that identifies logarithms of group-like elements with Lie elements.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.isHomogeneous_comul`: the comultiplication is homogeneous
  of degree `0` for the total-degree grading of `U ⊗ U`.
* `TauCeti.UniversalEnvelopingAlgebra.map_proj_comul`: the bihomogeneous component
  `(π i ⊗ π j) (Δ a)` equals `(π i ⊗ π j) (Δ (π (i + j) a))`.
* `TauCeti.UniversalEnvelopingAlgebra.comul_proj`: `Δ (π n a)` is the sum of the bihomogeneous
  components `(π i ⊗ π j) (Δ a)` over `i + j = n`.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_proj`: the componentwise primitivity
  criterion.
* `TauCeti.UniversalEnvelopingAlgebra.comul_mem_tensorProduct_ideal`: the comultiplication
  preserves total-degree filtration orders.
* `TauCeti.UniversalEnvelopingAlgebra.map_proj_eq_zero_of_mem_tensorProduct_ideal`: bihomogeneous
  components of total degree below `k` vanish on the order-`k` filtration term of `U ⊗ U`.

## References

* K. O. Friedrichs, *Mathematical aspects of the quantum theory of fields V*, Comm. Pure Appl.
  Math. 6 (1953), for the criterion that primitive elements of the free associative algebra are
  Lie elements.
* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), §1.4 and Theorem 3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open Finset

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ℕ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒜" => homogeneousSubmodule ℒ
local notation "π" => _root_.GradedAlgebra.proj (homogeneousSubmodule ℒ)
-- The grading of `U` as an internal grading, and the total-degree grading of `U ⊗ U`, whose
-- degree-`n` piece is spanned by the tensors `a ⊗ b` with `a` and `b` homogeneous of degrees
-- adding to `n`.
local notation "𝒢" => InternalGrading.ofDecomposition (homogeneousSubmodule ℒ)
local notation "𝒯" => InternalGrading.piece (InternalGrading.tensorProduct 𝒢 𝒢)

attribute [local instance 100] LieRing.ofAssociativeRing

section Comul

variable [GradedLieAlgebra ℒ]

/-- The comultiplication is homogeneous of degree `0` for the total-degree grading of `U ⊗ U`:
it sends the degree-`n` piece into the span of the tensors `a ⊗ b` with `a` and `b` homogeneous
of degrees adding to `n`. -/
theorem isHomogeneous_comul :
    LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := U)) 𝒜 𝒯 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n a ha
  rw [add_zero]
  refine (homogeneousSubmodule_le_iff ℒ n ((𝒯 n).comap (Coalgebra.comul (R := R)))).mpr
    (fun l hl => ?_) ha
  clear ha a
  have h1 := SetLike.one_mem_graded 𝒜
  rw [Submodule.mem_comap]
  induction l generalizing n with
  | nil =>
    subst hl
    simpa only [List.map_nil, List.prod_nil, List.sum_nil, Bialgebra.comul_one] using
      SetLike.one_mem_graded 𝒯
  | cons x l ih =>
    subst hl
    have hx := ι_mem_homogeneousSubmodule ℒ x.2.property
    have hl := ih _ rfl
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul, comul_ι,
      add_mul]
    refine Submodule.add_mem _ ?_ ?_
    · simpa only [add_zero] using SetLike.mul_mem_graded
        (InternalGrading.tmul_mem_tensorProduct_ofDecomposition 𝒜 𝒜 hx h1) hl
    · simpa only [zero_add] using SetLike.mul_mem_graded
        (InternalGrading.tmul_mem_tensorProduct_ofDecomposition 𝒜 𝒜 h1 hx) hl

/-- The bihomogeneous component `(π i ⊗ π j) (Δ a)` depends only on the component of `a` of
degree `i + j`. -/
theorem map_proj_comul (i j : ℕ) (a : U) :
    TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) a) =
      TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) (π (i + j) a)) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum, map_sum, Finset.sum_eq_single (i + j)]
  · rw [_root_.GradedAlgebra.proj_apply]
  · intro m _ hm
    exact TauCeti.GradedAlgebra.map_proj_eq_zero_of_mem_tensorProduct 𝒜 𝒜
      ((isHomogeneous_comul ℒ).map_mem (DirectSum.decompose 𝒜 a m).property) (Ne.symm hm)
  · intro h
    rw [DFinsupp.notMem_support_iff.mp h]
    simp

/-- The comultiplication of the degree-`n` component is the sum of the bihomogeneous components
of the comultiplication in bidegrees `(i, j)` with `i + j = n`. -/
theorem comul_proj (n : ℕ) (a : U) :
    Coalgebra.comul (R := R) (π n a) =
      ∑ p ∈ antidiagonal n, TensorProduct.map (π p.1) (π p.2) (Coalgebra.comul (R := R) a) := by
  conv_lhs => rw [← TauCeti.GradedAlgebra.sum_map_proj_of_mem_tensorProduct 𝒜 𝒜
    ((isHomogeneous_comul ℒ).map_mem (TauCeti.GradedAlgebra.proj_mem 𝒜 n a))]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_proj_comul ℒ p.1 p.2 a, mem_antidiagonal.mp hp]

/-- **Componentwise primitivity.** If the comultiplication of `a` agrees with
`1 ⊗ a + a ⊗ 1` in every bidegree `(i, j)` with `i + j = n`, then the degree-`n` component of `a`
is primitive. -/
theorem isPrimitiveElem_proj {a : U} {n : ℕ}
    (h : ∀ i j, i + j = n → TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) a) =
      TensorProduct.map (π i) (π j) (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1)) :
    Bialgebra.IsPrimitiveElem R (π n a) := by
  have h1 : ∀ k, k ≠ 0 → π k (1 : U) = 0 := fun k hk =>
    TauCeti.GradedAlgebra.proj_of_mem_ne (SetLike.one_mem_graded 𝒜) (Ne.symm hk)
  have h0 : π 0 (1 : U) = 1 := TauCeti.GradedAlgebra.proj_of_mem_same (SetLike.one_mem_graded 𝒜)
  rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, comul_proj,
    Finset.sum_congr rfl fun p hp => h p.1 p.2 (mem_antidiagonal.mp hp)]
  simp only [map_add, TensorProduct.map_tmul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single (0, n) (fun p hp hne => ?_) (by simp)]
    · simp [h0]
    · rw [mem_antidiagonal] at hp
      rw [h1 p.1 (fun h0 => hne (Prod.ext h0 (by omega))), TensorProduct.zero_tmul]
  · rw [Finset.sum_eq_single (n, 0) (fun p hp hne => ?_) (by simp)]
    · simp [h0]
    · rw [mem_antidiagonal] at hp
      rw [h1 p.2 (fun h0 => hne (Prod.ext (by omega) h0)), TensorProduct.tmul_zero]

end Comul

section Filtration

variable [GradedLieAlgebra ℒ]

local notation "𝓕" => degreeFiltration ℒ (Nat.castAddMonoidHom ℤ)
  (fun n hn => absurd hn (not_lt.mpr (Int.natCast_nonneg n)))

/-- The comultiplication preserves total-degree filtration orders: it sends the order-`k` term
of the enveloping algebra into the order-`k` term of the total-degree filtration of `U ⊗ U`. -/
theorem comul_mem_tensorProduct_ideal {k : ℕ} {a : U} (ha : a ∈ (𝓕).ideal k) :
    Coalgebra.comul (R := R) a ∈ ((𝓕).tensorProduct R 𝓕).ideal k := by
  classical
  rw [mem_degreeFiltration_ideal_iff] at ha
  rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  by_cases hm : m < k
  · rw [ha m (by simpa using hm), map_zero]
    exact Submodule.zero_mem _
  · have hle : 𝒯 m ≤ (((𝓕).tensorProduct R 𝓕).ideal k).restrictScalars R := by
      refine InternalGrading.tensorProduct_piece_le_of_add_eq _ _ fun i j hij x hx y hy => ?_
      rw [InternalGrading.ofDecomposition_piece] at hx hy
      exact (𝓕).tmul_mem_tensorProduct_ideal R 𝓕 (a := i) (b := j) (by omega)
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ _ _ hx (by simp))
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ _ _ hy (by simp))
    exact hle ((isHomogeneous_comul ℒ).map_mem (DirectSum.decompose 𝒜 a m).property)

/-- The bihomogeneous component in a bidegree of total degree below `k` vanishes on the
order-`k` term of the total-degree filtration of `U ⊗ U`. -/
theorem map_proj_eq_zero_of_mem_tensorProduct_ideal {k i j : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ ((𝓕).tensorProduct R 𝓕).ideal k) (hij : i + j < k) :
    TensorProduct.map (π i) (π j) t = 0 := by
  have hproj : ∀ {a : ℕ} {x : U}, x ∈ (𝓕).ideal a → ∀ m, m < a → π m x = 0 := by
    intro a x hx m hm
    rw [_root_.GradedAlgebra.proj_apply]
    exact (mem_degreeFiltration_ideal_iff ℒ _ _).mp hx m (by simpa using hm)
  have hle : tensorFiltrationTail (fun n => ((𝓕).ideal n).restrictScalars R)
      (fun n => ((𝓕).ideal n).restrictScalars R) k ≤
        LinearMap.ker (TensorProduct.map (π i) (π j)) := by
    refine (tensorFiltrationTail_le_iff _ _).mpr fun a b hab x hx y hy => ?_
    rw [LinearMap.mem_ker, TensorProduct.map_tmul]
    by_cases hia : i < a
    · rw [hproj (a := a) hx i hia, TensorProduct.zero_tmul]
    · rw [hproj (a := b) hy j (by omega), TensorProduct.tmul_zero]
  exact hle (((𝓕).mem_tensorProduct_ideal_iff R 𝓕).mp ht)

end Filtration

end TauCeti.UniversalEnvelopingAlgebra
