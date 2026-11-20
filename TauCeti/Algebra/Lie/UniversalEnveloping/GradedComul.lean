/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic

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

attribute [local instance 100] LieRing.ofAssociativeRing

section Comul

/-- The span of the tensors `a ⊗ b` with `a` and `b` homogeneous of degrees adding to `n`. -/
private def tensorPiece (n : ℕ) : Submodule R (U ⊗[R] U) :=
  ⨆ p ∈ antidiagonal n, Submodule.map₂ (TensorProduct.mk R U U) (𝒜 p.1) (𝒜 p.2)

private theorem tensorPiece_le_iff {n : ℕ} {P : Submodule R (U ⊗[R] U)} :
    tensorPiece ℒ n ≤ P ↔ ∀ i j, i + j = n → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, a ⊗ₜ[R] b ∈ P := by
  simp [tensorPiece, Submodule.map₂_le]

private theorem tmul_mem_tensorPiece {i j : ℕ} {a b : U} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    a ⊗ₜ[R] b ∈ tensorPiece ℒ (i + j) :=
  Submodule.mem_iSup_of_mem (i, j) <| Submodule.mem_iSup_of_mem (mem_antidiagonal.mpr rfl) <|
    Submodule.apply_mem_map₂ _ ha hb

/-- Left multiplication by a bihomogeneous pure tensor raises the total degree. -/
private theorem tmul_mul_mem_tensorPiece {i j m : ℕ} {u v : U} (hu : u ∈ 𝒜 i) (hv : v ∈ 𝒜 j)
    {t : U ⊗[R] U} (ht : t ∈ tensorPiece ℒ m) :
    (u ⊗ₜ[R] v) * t ∈ tensorPiece ℒ (i + j + m) := by
  have hle : tensorPiece ℒ m ≤
      (tensorPiece ℒ (i + j + m)).comap (LinearMap.mulLeft R (u ⊗ₜ[R] v)) := by
    refine (tensorPiece_le_iff ℒ).mpr fun k l hkl a ha b hb => ?_
    have hdeg : i + k + (j + l) = i + j + m := by omega
    simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, hdeg] using
      tmul_mem_tensorPiece ℒ (SetLike.mul_mem_graded hu ha) (SetLike.mul_mem_graded hv hb)
  exact hle ht

/-- The comultiplication sends the degree-`n` piece into the bihomogeneous tensors of total
degree `n`. -/
private theorem homogeneousSubmodule_le_comap_comul (n : ℕ) :
    𝒜 n ≤ (tensorPiece ℒ n).comap (Coalgebra.comul (R := R)) := by
  refine (homogeneousSubmodule_le_iff ℒ n _).mpr fun l hl => ?_
  have h1 := SetLike.one_mem_graded 𝒜
  rw [Submodule.mem_comap]
  induction l generalizing n with
  | nil =>
    subst hl
    simpa only [List.map_nil, List.prod_nil, List.sum_nil, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, add_zero] using tmul_mem_tensorPiece ℒ h1 h1
  | cons x l ih =>
    subst hl
    have hx := ι_mem_homogeneousSubmodule ℒ x.2.property
    have hl := ih _ rfl
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul, comul_ι,
      add_mul]
    refine Submodule.add_mem _ ?_ ?_
    · simpa only [add_zero] using tmul_mul_mem_tensorPiece ℒ hx h1 hl
    · simpa only [zero_add] using tmul_mul_mem_tensorPiece ℒ h1 hx hl

private theorem comul_mem_tensorPiece {n : ℕ} {a : U} (ha : a ∈ 𝒜 n) :
    Coalgebra.comul (R := R) a ∈ tensorPiece ℒ n :=
  homogeneousSubmodule_le_comap_comul ℒ n ha

variable [GradedLieAlgebra ℒ]

/-- A bihomogeneous projection of total degree other than `n` kills the bihomogeneous tensors
of total degree `n`. -/
private theorem map_proj_eq_zero_of_mem_tensorPiece {n i j : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ tensorPiece ℒ n) (hij : i + j ≠ n) : TensorProduct.map (π i) (π j) t = 0 := by
  have hle : tensorPiece ℒ n ≤ LinearMap.ker (TensorProduct.map (π i) (π j)) := by
    refine (tensorPiece_le_iff ℒ).mpr fun k l hkl a ha b hb => ?_
    rw [LinearMap.mem_ker, TensorProduct.map_tmul]
    by_cases hik : k = i
    · simp [_root_.GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_ne 𝒜 hb (show l ≠ j by omega)]
    · simp [_root_.GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 ha hik]
  exact hle ht

/-- The bihomogeneous projections of total degree `n` recover the bihomogeneous tensors of total
degree `n`. -/
private theorem sum_map_proj_of_mem_tensorPiece {n : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ tensorPiece ℒ n) :
    ∑ p ∈ antidiagonal n, TensorProduct.map (π p.1) (π p.2) t = t := by
  have hle : tensorPiece ℒ n ≤
      LinearMap.eqLocus (∑ p ∈ antidiagonal n, TensorProduct.map (π p.1) (π p.2))
        LinearMap.id := by
    refine (tensorPiece_le_iff ℒ).mpr fun k l hkl a ha b hb => ?_
    rw [LinearMap.mem_eqLocus, LinearMap.sum_apply, Finset.sum_eq_single (k, l)]
    · simp [_root_.GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜 ha, DirectSum.decompose_of_mem_same 𝒜 hb]
    · rintro ⟨i, j⟩ hp hne
      rw [mem_antidiagonal] at hp
      rw [TensorProduct.map_tmul]
      by_cases hik : k = i
      · simp [_root_.GradedAlgebra.proj_apply,
          DirectSum.decompose_of_mem_ne 𝒜 hb (show l ≠ j by grind)]
      · simp [_root_.GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 ha hik]
    · exact fun h => absurd (mem_antidiagonal.mpr hkl) h
  simpa [LinearMap.sum_apply] using hle ht

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
    exact map_proj_eq_zero_of_mem_tensorPiece ℒ
      (comul_mem_tensorPiece ℒ (DirectSum.decompose 𝒜 a m).property) (Ne.symm hm)
  · intro h
    rw [DFinsupp.notMem_support_iff.mp h]
    simp

/-- The comultiplication of the degree-`n` component is the sum of the bihomogeneous components
of the comultiplication in bidegrees `(i, j)` with `i + j = n`. -/
theorem comul_proj (n : ℕ) (a : U) :
    Coalgebra.comul (R := R) (π n a) =
      ∑ p ∈ antidiagonal n, TensorProduct.map (π p.1) (π p.2) (Coalgebra.comul (R := R) a) := by
  have hn : π n a ∈ 𝒜 n := by
    rw [_root_.GradedAlgebra.proj_apply]
    exact (DirectSum.decompose 𝒜 a n).property
  conv_lhs => rw [← sum_map_proj_of_mem_tensorPiece ℒ (comul_mem_tensorPiece ℒ hn)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_proj_comul ℒ p.1 p.2 a, mem_antidiagonal.mp hp]

/-- **Componentwise primitivity.** If the comultiplication of `a` agrees with
`1 ⊗ a + a ⊗ 1` in every bidegree `(i, j)` with `i + j = n`, then the degree-`n` component of `a`
is primitive. -/
theorem isPrimitiveElem_proj {a : U} {n : ℕ}
    (h : ∀ i j, i + j = n → TensorProduct.map (π i) (π j) (Coalgebra.comul (R := R) a) =
      TensorProduct.map (π i) (π j) (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1)) :
    Bialgebra.IsPrimitiveElem R (π n a) := by
  have h1 : ∀ k, k ≠ 0 → π k (1 : U) = 0 := by
    intro k hk
    rw [_root_.GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_ne 𝒜 (SetLike.one_mem_graded 𝒜) (Ne.symm hk)]
  have h0 : π 0 (1 : U) = 1 := by
    rw [_root_.GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)]
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
  · have hle : tensorPiece ℒ m ≤ (((𝓕).tensorProduct R 𝓕).ideal k).restrictScalars R := by
      refine (tensorPiece_le_iff ℒ).mpr fun i j hij x hx y hy => ?_
      exact (𝓕).tmul_mem_tensorProduct_ideal R 𝓕 (a := i) (b := j) (by omega)
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ _ _ hx (by simp))
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ _ _ hy (by simp))
    exact hle (comul_mem_tensorPiece ℒ (DirectSum.decompose 𝒜 a m).property)

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
