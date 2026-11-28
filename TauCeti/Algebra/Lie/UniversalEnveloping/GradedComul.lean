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

Let `L` be a Lie algebra graded by an additive commutative monoid `Γ`, and grade its enveloping
algebra `U` by total Lie degree, with homogeneous projections `π n`. The comultiplication `Δ` of
`U` is homogeneous: it sends the degree-`n` piece of `U` into the span of the tensors `a ⊗ b` with
`a` and `b` homogeneous of degrees adding to `n`. Consequently the bihomogeneous component
`(π i ⊗ π j) (Δ a)` depends only on the degree-`(i + j)` component of `a`, and (when `Γ` has
finite antidiagonals) the comultiplication of `π n a` is the sum of these bihomogeneous components
over `i + j = n`.

This gives a componentwise criterion for primitivity: if `Δ a` agrees with `1 ⊗ a + a ⊗ 1` in all
bidegrees `(i, j)` with `i + j = n`, then `π n a` is primitive. When `Γ` carries an additive degree
`d : Γ →+ ℤ` and all negative-degree pieces of `L` vanish, the total-degree filtration `F` of `U`
satisfies two dual properties: the comultiplication carries `F k` into the total-degree filtration
of `U ⊗ U`, and the bihomogeneous components in bidegrees of total `d`-degree below `k` vanish on
that filtration term. Hence an element whose comultiplication agrees with `1 ⊗ a + a ⊗ 1` modulo
filtration order `k` has primitive components in every degree with `d n < k`. Over a rational
algebra, where primitive elements are exactly the image of the Lie algebra, this is the truncated
form of Friedrichs' criterion that identifies logarithms of group-like elements with Lie elements.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.isHomogeneous_comul`: the comultiplication is homogeneous
  of degree `0` for the total-degree grading of `U ⊗ U`.
* `TauCeti.UniversalEnvelopingAlgebra.map_proj_comul`: the bihomogeneous component
  `(π i ⊗ π j) (Δ a)` equals `(π i ⊗ π j) (Δ (π (i + j) a))`.
* `TauCeti.UniversalEnvelopingAlgebra.comul_proj`: `Δ (π n a)` is the sum of the bihomogeneous
  components `(π i ⊗ π j) (Δ a)` over `i + j = n`.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_proj`: the componentwise primitivity
  criterion.
* `TauCeti.UniversalEnvelopingAlgebra.tensorProduct_piece_le_tensorProduct_ideal`: a total-degree
  tensor piece of degree at least `k` lies in the order-`k` tensor filtration ideal.
* `TauCeti.UniversalEnvelopingAlgebra.comul_mem_tensorProduct_ideal`: the comultiplication
  preserves total-degree filtration orders when negative-degree pieces vanish.
* `TauCeti.UniversalEnvelopingAlgebra.map_proj_eq_zero_of_mem_tensorProduct_ideal`: bihomogeneous
  components of total `d`-degree below `k` vanish on the order-`k` filtration term of `U ⊗ U`.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_proj_of_comul_sub_mem`: a homogeneous
  component of `d`-degree below `k` of an element primitive modulo order `k` is primitive.

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

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

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

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

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
theorem map_proj_comul (i j : Γ) (a : U) :
    TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) a) =
      TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) (π (i + j) a)) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum, map_sum, Finset.sum_eq_single (i + j)]
  · rw [_root_.GradedAlgebra.proj_apply]
  · intro m _ hm
    have hmem : Coalgebra.comul (R := R) (DirectSum.decompose 𝒜 a m : U) ∈ 𝒯 m := by
      simpa only [add_zero] using
        (isHomogeneous_comul ℒ).map_mem (DirectSum.decompose 𝒜 a m).property
    exact TauCeti.GradedAlgebra.map_proj_eq_zero_of_mem_tensorProduct 𝒜 𝒜 hmem (Ne.symm hm)
  · intro h
    rw [DFinsupp.notMem_support_iff.mp h]
    simp

/-- The comultiplication of the degree-`n` component is the sum of the bihomogeneous components
of the comultiplication in bidegrees `(i, j)` with `i + j = n`. -/
theorem comul_proj [Finset.HasAntidiagonal Γ] (n : Γ) (a : U) :
    Coalgebra.comul (R := R) (π n a) =
      ∑ p ∈ antidiagonal n, TensorProduct.map (π p.1) (π p.2) (Coalgebra.comul (R := R) a) := by
  have hmem : Coalgebra.comul (R := R) (π n a) ∈ 𝒯 n := by
    simpa only [add_zero] using
      (isHomogeneous_comul ℒ).map_mem (TauCeti.GradedAlgebra.proj_mem 𝒜 n a)
  conv_lhs => rw [← TauCeti.GradedAlgebra.sum_map_proj_of_mem_tensorProduct 𝒜 𝒜 hmem]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_proj_comul ℒ p.1 p.2 a, mem_antidiagonal.mp hp]

private theorem eq_zero_of_forall_map_proj_eq_zero {z : U ⊗[R] U}
    (hz : ∀ i j : Γ, TensorProduct.map (π i) (π j) z = 0) : z = 0 := by
  let C : Γ × Γ → Submodule R (U ⊗[R] U) := fun p =>
    Submodule.map₂ (TensorProduct.mk R U U) (𝒜 p.1) (𝒜 p.2)
  let _ : _root_.DirectSum.Decomposition C :=
    (_root_.DirectSum.IsInternal.tensorProduct 𝒜 𝒜
      (isInternal_homogeneousSubmodule ℒ) (isInternal_homogeneousSubmodule ℒ)).chooseDecomposition
  have hcomp (w : U ⊗[R] U) (i j : Γ) :
      (DirectSum.decompose C w (i, j) : U ⊗[R] U) = TensorProduct.map (π i) (π j) w := by
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ h₁ h₂ => simp [map_add, h₁, h₂]
    | tmul x y =>
      induction x using _root_.DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add x₁ x₂ h₁ h₂ => simp [TensorProduct.add_tmul, map_add, h₁, h₂]
      | @homogeneous p x =>
        induction y using _root_.DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add y₁ y₂ h₁ h₂ => simp [TensorProduct.tmul_add, map_add, h₁, h₂]
        | @homogeneous q y =>
          have hxy : (x : U) ⊗ₜ[R] (y : U) ∈ C (p, q) :=
            Submodule.apply_mem_map₂ (TensorProduct.mk R U U) x.property y.property
          by_cases hpq : (p, q) = (i, j)
          · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpq
            rw [DirectSum.decompose_of_mem_same C hxy, TensorProduct.map_tmul,
              TauCeti.GradedAlgebra.proj_of_mem_same x.property,
              TauCeti.GradedAlgebra.proj_of_mem_same y.property]
          · rw [DirectSum.decompose_of_mem_ne C hxy hpq, TensorProduct.map_tmul]
            rcases ne_or_eq p i with hpi | rfl
            · rw [TauCeti.GradedAlgebra.proj_of_mem_ne x.property hpi, TensorProduct.zero_tmul]
            · have hqj : q ≠ j := fun h => hpq (Prod.ext rfl h)
              rw [TauCeti.GradedAlgebra.proj_of_mem_ne y.property hqj, TensorProduct.tmul_zero]
  apply (DirectSum.decomposeLinearEquiv C).injective
  rw [map_zero, _root_.DirectSum.decomposeLinearEquiv_apply]
  ext ⟨i, j⟩
  rw [hcomp z i j, hz i j]
  rfl

/-- **Componentwise primitivity.** If the comultiplication of `a` agrees with
`1 ⊗ a + a ⊗ 1` in every bidegree `(i, j)` with `i + j = n`, then the degree-`n` component of `a`
is primitive. -/
theorem isPrimitiveElem_proj {a : U} {n : Γ}
    (h : ∀ i j : Γ, i + j = n → TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) a) =
      TensorProduct.map (π i) (π j) (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1)) :
    Bialgebra.IsPrimitiveElem R (π n a) := by
  rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, ← sub_eq_zero]
  refine eq_zero_of_forall_map_proj_eq_zero ℒ fun i j => ?_
  rw [map_sub]
  by_cases hij : i + j = n
  · rw [← hij, ← map_proj_comul ℒ i j a, hij, h i j hij]
    have h1 : ∀ k : Γ, k ≠ 0 → π k (1 : U) = 0 := fun k hk =>
      TauCeti.GradedAlgebra.proj_of_mem_ne (SetLike.one_mem_graded 𝒜) (Ne.symm hk)
    have hproj : ∀ k : Γ, π k (π n a) = if k = n then π n a else 0 := fun k => by
      split_ifs with hk
      · rw [hk]
        exact TauCeti.GradedAlgebra.proj_of_mem_same (TauCeti.GradedAlgebra.proj_mem 𝒜 n a)
      · exact TauCeti.GradedAlgebra.proj_of_mem_ne (TauCeti.GradedAlgebra.proj_mem 𝒜 n a)
          (Ne.symm hk)
    simp only [map_add, TensorProduct.map_tmul, hproj]
    have hL : π i (1 : U) ⊗ₜ[R] (if j = n then π n a else 0) = π i (1 : U) ⊗ₜ[R] π j a := by
      by_cases hi : i = 0
      · have hj : j = n := by simpa [hi] using hij
        simp [hj, _root_.GradedAlgebra.proj_apply]
      · simp [h1 i hi]
    have hR : (if i = n then π n a else 0) ⊗ₜ[R] π j (1 : U) = π i a ⊗ₜ[R] π j (1 : U) := by
      by_cases hj : j = 0
      · have hi : i = n := by simpa [hj] using hij
        simp [hi, _root_.GradedAlgebra.proj_apply]
      · simp [h1 j hj]
    rw [hL, hR, sub_self]
  · have hmem : Coalgebra.comul (R := R) (π n a) ∈ 𝒯 n := by
      simpa only [add_zero] using
        (isHomogeneous_comul ℒ).map_mem (TauCeti.GradedAlgebra.proj_mem 𝒜 n a)
    have hc := TauCeti.GradedAlgebra.map_proj_eq_zero_of_mem_tensorProduct 𝒜 𝒜 hmem hij
    have hprim : 1 ⊗ₜ[R] π n a + π n a ⊗ₜ[R] 1 ∈ 𝒯 n := add_mem
      (by
        simpa only [zero_add] using InternalGrading.tmul_mem_tensorProduct_ofDecomposition
          𝒜 𝒜 (SetLike.one_mem_graded 𝒜) (TauCeti.GradedAlgebra.proj_mem 𝒜 n a))
      (by
        simpa only [add_zero] using InternalGrading.tmul_mem_tensorProduct_ofDecomposition
          𝒜 𝒜 (TauCeti.GradedAlgebra.proj_mem 𝒜 n a) (SetLike.one_mem_graded 𝒜))
    rw [hc, TauCeti.GradedAlgebra.map_proj_eq_zero_of_mem_tensorProduct 𝒜 𝒜 hprim hij, sub_zero]

end Comul

section Filtration

variable (d : Γ →+ ℤ) [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "𝓕" => degreeFiltration ℒ d hneg

/-- When negative-degree pieces of `L` vanish, every total-degree tensor piece of `d`-degree at
least `k` lies in the order-`k` term of the total-degree filtration of `U ⊗ U`. -/
theorem tensorProduct_piece_le_tensorProduct_ideal {m : Γ} {k : ℕ} (hm : (k : ℤ) ≤ d m) :
    𝒯 m ≤ (((𝓕).tensorProduct R 𝓕).ideal k).restrictScalars R := by
  refine InternalGrading.tensorProduct_piece_le_of_add_eq _ _ fun i j hij x hx y hy => ?_
  rw [InternalGrading.ofDecomposition_piece] at hx hy
  by_cases hi : d i < 0
  · rw [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hi, Submodule.mem_bot] at hx
    simp [hx]
  · by_cases hj : d j < 0
    · rw [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hj, Submodule.mem_bot] at hy
      simp [hy]
    · have hdeg : k ≤ (d i).toNat + (d j).toNat := by
        have hsum : d i + d j = d m := by rw [← map_add, hij]
        omega
      exact (𝓕).tmul_mem_tensorProduct_ideal R 𝓕 hdeg
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hx (by omega))
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hy (by omega))

/-- When negative-degree pieces of `L` vanish, the comultiplication preserves total-degree
filtration orders: it sends the order-`k` term of `U` into the order-`k` term of `U ⊗ U`. -/
theorem comul_mem_tensorProduct_ideal {k : ℕ} {a : U} (ha : a ∈ (𝓕).ideal k) :
    Coalgebra.comul (R := R) a ∈ ((𝓕).tensorProduct R 𝓕).ideal k :=
  ((degreeFiltration_ideal_le_iff ℒ d hneg k
    ((((𝓕).tensorProduct R 𝓕).ideal k).comap (Bialgebra.comulAlgHom R U))).mpr
    fun _ hm _ hx => tensorProduct_piece_le_tensorProduct_ideal ℒ d hneg hm
      (by simpa only [add_zero, Bialgebra.comulAlgHom_apply] using
        (isHomogeneous_comul ℒ).map_mem hx)) ha

/-- The bihomogeneous component in a bidegree of total `d`-degree below `k` vanishes on the
order-`k` term of the total-degree filtration of `U ⊗ U`. -/
theorem map_proj_eq_zero_of_mem_tensorProduct_ideal {k : ℕ} {i j : Γ} {t : U ⊗[R] U}
    (ht : t ∈ ((𝓕).tensorProduct R 𝓕).ideal k) (hij : d i + d j < k) :
    TensorProduct.map (π i) (π j) t = 0 := by
  have hproj : ∀ {a : ℕ} {x : U}, x ∈ (𝓕).ideal a → ∀ m, d m < a → π m x = 0 := by
    intro a x hx m hm
    rw [_root_.GradedAlgebra.proj_apply]
    exact (mem_degreeFiltration_ideal_iff ℒ d hneg).mp hx m hm
  have hle : tensorFiltrationTail (fun n => ((𝓕).ideal n).restrictScalars R)
      (fun n => ((𝓕).ideal n).restrictScalars R) k ≤
        LinearMap.ker (TensorProduct.map (π i) (π j)) := by
    refine (tensorFiltrationTail_le_iff _ _).mpr fun a b hab x hx y hy => ?_
    rw [LinearMap.mem_ker, TensorProduct.map_tmul]
    by_cases hia : d i < a
    · rw [hproj (a := a) hx i hia, TensorProduct.zero_tmul]
    · rw [hproj (a := b) hy j (by omega), TensorProduct.tmul_zero]
  exact hle (((𝓕).mem_tensorProduct_ideal_iff R 𝓕).mp ht)

/-- If `Δ a` agrees with `1 ⊗ a + a ⊗ 1` modulo filtration order `k`, then every homogeneous
component of `a` of `d`-degree below `k` is primitive. -/
theorem isPrimitiveElem_proj_of_comul_sub_mem {k : ℕ} {a : U}
    (ha : Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈
      ((𝓕).tensorProduct R 𝓕).ideal k)
    {n : Γ} (hn : d n < k) :
    Bialgebra.IsPrimitiveElem R (π n a) :=
  isPrimitiveElem_proj ℒ fun i j hij => by
    rw [← sub_eq_zero, ← map_sub]
    exact map_proj_eq_zero_of_mem_tensorProduct_ideal ℒ d hneg ha
      (by rw [← map_add, hij]; exact hn)

end Filtration

end TauCeti.UniversalEnvelopingAlgebra
