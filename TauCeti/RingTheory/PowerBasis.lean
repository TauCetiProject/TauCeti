/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.PowerBasis

/-!
# The constant coordinate of a power basis, and multiplication by the generator

An `R`-algebra `S` with a power basis `1, x, …, x ^ (d - 1)` retracts onto `R`: the coordinate
along `x ^ 0 = 1` is an `R`-linear map `S → R` sending `1` to `1`. So `R · 1` is a direct summand of
`S`, which is what it takes to descend a span over `S` back to a span over `R`
(`TauCeti.mem_of_mem_span_of_mem_span_range`).

## Main statements

* `PowerBasis.exists_linearMap_apply_one`: an algebra with a power basis retracts onto its scalars.
* `PowerBasis.exists_algebraMap_eq_of_algebraMap_eq_smul`: the scalars are saturated with respect
  to nonzerodivisors: if `n • x` is a scalar for a nonzerodivisor `n`, then so is `x`.
* `PowerBasis.charpoly_lmul_gen`: multiplication by the generator of a power basis has
  characteristic polynomial the minimal polynomial of the generator. This is the endomorphism form
  of Mathlib's `charpoly_leftMulMatrix`.
* `PowerBasis.roots_map_minpoly_eq_map_algHom`: in a domain `E`, the roots of the minimal
  polynomial of the generator are the images of the generator under the `R`-algebra embeddings
  `S →ₐ[R] E`, each counted once.
-/

public section

/-- **An algebra with a power basis retracts onto its scalars**: the coordinate along
`pb.gen ^ 0 = 1` is an `R`-linear map `S → R` sending `1` to `1`. -/
theorem PowerBasis.exists_linearMap_apply_one {R S : Type*} [CommRing R] [Ring S] [Nontrivial S]
    [Algebra R S] (pb : PowerBasis R S) : ∃ t : S →ₗ[R] R, t 1 = 1 := by
  refine ⟨pb.basis.coord ⟨0, pb.dim_pos⟩, ?_⟩
  have h : pb.basis ⟨0, pb.dim_pos⟩ = 1 := by rw [pb.basis_eq_pow, pow_zero]
  rw [← h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- **The scalars are saturated in an algebra with a power basis**: if `n • x` lies in the image of
`R` for a nonzerodivisor `n` of `R`, then so does `x`, namely as its coordinate along
`pb.gen ^ 0 = 1`. -/
theorem PowerBasis.exists_algebraMap_eq_of_algebraMap_eq_smul {R S : Type*} [CommRing R] [Ring S]
    [Algebra R S] (pb : PowerBasis R S) {n : R} (hn : n ∈ nonZeroDivisors R) {x : S} {c : R}
    (h : algebraMap R S c = n • x) : ∃ a : R, algebraMap R S a = x := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ⟨0, Subsingleton.elim _ _⟩
  set j₀ : Fin pb.dim := ⟨0, pb.dim_pos⟩
  have hrepr (c : R) : pb.basis.repr (algebraMap R S c) = Finsupp.single j₀ c := by
    have hj₀ : pb.basis j₀ = 1 := by rw [pb.basis_eq_pow, pow_zero]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← hj₀, pb.basis.repr_self,
      Finsupp.smul_single_one]
  refine ⟨pb.basis.repr x j₀, pb.basis.ext_elem fun j ↦ ?_⟩
  rw [hrepr]
  obtain rfl | hj := eq_or_ne j j₀
  · simp
  · have := congr(pb.basis.repr $h j)
    rw [hrepr, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_of_ne hj] at this
    rw [Finsupp.single_eq_of_ne hj, (mul_left_mem_nonZeroDivisors_eq_zero_iff hn).mp this.symm]

/-- For a power basis of `S` over `R`, the characteristic polynomial of multiplication by the
generator is the minimal polynomial of the generator. -/
theorem PowerBasis.charpoly_lmul_gen {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (pb : PowerBasis R S) :
    (Algebra.lmul R S pb.gen).charpoly = minpoly R pb.gen := by
  rw [← LinearMap.charpoly_toMatrix _ pb.basis, ← Algebra.leftMulMatrix_apply,
    charpoly_leftMulMatrix]

open Polynomial in
/-- The roots in a domain `E` of the minimal polynomial of the generator of a power basis are the
images of the generator under the `R`-algebra embeddings `S →ₐ[R] E`, each counted once, for any
numbering `e` of the embeddings by `Fin pb.dim`. -/
theorem PowerBasis.roots_map_minpoly_eq_map_algHom {R S E : Type*} [CommRing R] [Ring S]
    [CommRing E] [IsDomain E] [Algebra R S] [Algebra R E] (pb : PowerBasis R S)
    (e : Fin pb.dim ≃ (S →ₐ[R] E)) :
    ((minpoly R pb.gen).map (algebraMap R E)).roots =
      Finset.univ.val.map fun i ↦ e i pb.gen := by
  have := (algebraMap R E).domain_nontrivial
  have hrnodup : (Finset.univ.val.map fun i ↦ e i pb.gen).Nodup := by
    rw [Multiset.nodup_map_iff_of_injective]
    · exact Finset.univ.nodup
    · intro i j hij
      exact e.injective (pb.algHom_ext hij)
  have hle : Finset.univ.val.map (fun i ↦ e i pb.gen) ≤
      ((minpoly R pb.gen).map (algebraMap R E)).roots :=
    (Multiset.le_iff_subset hrnodup).2 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
      exact (pb.liftEquiv' (e i)).2)
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  exact (card_roots' _).trans (by
    rw [(minpoly.monic pb.isIntegral_gen).natDegree_map (algebraMap R E), pb.natDegree_minpoly])
