/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Mackey
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Artinian.Module
import TauCeti.FieldTheory.Finite.MinpolyOrbit
import TauCeti.FieldTheory.Minpoly.Dvd
import TauCeti.LinearAlgebra.Charpoly.Aeval.Comp
import TauCeti.LinearAlgebra.Charpoly.Degree
import TauCeti.LinearAlgebra.Charpoly.Quotient
import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Semisimple

/-!
# The inverse `μ` of `𝟙` and Green's cuspidal functions

Let `k` be a finite field. In the Hall algebra `TauCeti.HallAlgebra k` of class functions on all
square matrices over `k`, `μ = TauCeti.HallAlgebra.moebius` is the inverse of the constant
function `𝟙` for the induction product, and Green's cuspidal function of `η : K → ℂ` is
`C_η = (β_η · μ) ∗ 𝟙` (`TauCeti.HallAlgebra.greenCuspidal`), with `β_η` the eigenvalue sum and `·`
the pointwise product.

Evaluated at `g`, the relation `μ ∗ 𝟙 = 1` says that `U ↦ μ(g|_U)` is the Möbius function
`U ↦ μ(⊥, U)` of the lattice of `g`-invariant subspaces
(`Module.End.sum_moebius_ofEnd_invtRestrict`), and `μ(g) ≠ 0` forces `g` to be semisimple
(`Module.End.isSemisimple_of_moebius_ne_zero`). So block averages of `B · μ` only see the block
diagonal class, and from this and Mackey's formula `C_η` is
cuspidal. A cuspidal function vanishes off the classes whose characteristic polynomial is a power
of an irreducible polynomial: for an irreducible factor `P` of the minimal polynomial, all block
maps with diagonal blocks `g` on the Fitting component `ker P(g)^N` and on the quotient are
similar to `g`, since the Sylvester map `y ↦ g y - y g` between the two blocks is invertible.

## Main results

* `TauCeti.HallAlgebra.blockAverage_moebius`: `δμ(a, ·) = μ(a) · μ`.
* `TauCeti.HallAlgebra.blockAverage_fun_mul_moebius`: `δ(B · μ)(a, b) = μ(a) μ(b) B(a ⊕ b)`.
* `TauCeti.HallAlgebra.conj_moebius`: `μ` is real.
* `TauCeti.HallAlgebra.greenCuspidal_mul_constOne`: `C_η ∗ 𝟙 = -β_η`.
* `TauCeti.HallAlgebra.greenCuspidal_eq_zero_of_dim_eq_zero`,
  `TauCeti.HallAlgebra.isCuspidal_greenCuspidal`: `C_η` vanishes in size `0` and is cuspidal.
* `TauCeti.HallAlgebra.IsCuspidal.exists_charpoly_eq_pow`: if `A` is cuspidal and `A(g) ≠ 0`, the
  characteristic polynomial of `g` is a power of an irreducible polynomial.
* `TauCeti.HallAlgebra.greenCuspidal_ofEnd_eq_mul`: `C_η(g)` only depends on `η` at the elements
  whose Frobenius orbit lists the eigenvalues of `g`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447, Theorem 1.
* T. A. Springer, *Characters of special groups*, Séminaire Bourbaki 441 (1973/74), 1.1–1.7.
* Adapted from `src/Lib/LocalGL/Green/CuspidalFunctions.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.Hall.moebius_eq_one_of_dim_eq_zero`, `New.Hall.blockAverage_mulMoebius`,
  `New.Hall.conj_moebius`, `New.Hall.greenCuspidal_mul_constOne`,
  `New.Hall.greenCuspidal_eq_zero_of_dim_lt_one`, `New.Hall.isCuspidal_greenCuspidal`,
  `New.Hall.IsCuspidal.exists_charpoly_eq_pow` and `New.greenCuspidal_simClassOf_eq_mul`. The
  pointwise product `New.Hall.mulMoebius` is written out here, and the irreducible factor `P` is
  taken from the minimal polynomial. The similarity of a semisimple block triangular map with its
  block diagonal part is `TauCeti.SimilarityClass.ofEnd_blockTriangular_of_isSemisimple`, and the
  Sylvester equation on a Fitting component is `Module.End.exists_sylvester_eq`.
-/

public section

open Module TauCeti.SimilarityClass ComplexConjugate Polynomial
open scoped BigOperators

open Module.End (blockTriangular blockTriangular_apply)

namespace TauCeti.HallAlgebra

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

/-! ### The inverse `μ` of `𝟙` -/

section Moebius

variable [Finite k]

omit [Finite k] in
/-- The lattice of `g`-invariant subspaces is trivial exactly when `g` acts on the zero space. -/
private theorem top_eq_bot_iff_finrank_eq_zero (g : Module.End k V) :
    (⊤ : g.invtSubmodule) = ⊥ ↔ finrank k V = 0 := by
  rw [← finrank_top k V, Submodule.finrank_eq_zero, ← Subtype.coe_inj]
  rfl

/-- `μ` is `1` on the class of size `0`. -/
theorem moebius_eq_one_of_dim_eq_zero {o : SimilarityClass k} (h : o.dim = 0) : moebius o = 1 := by
  have := Fintype.ofFinite o.rep.invtSubmodule
  -- `μ ∗ 𝟙 = 1` at the class of `o.rep` on `⊥`, which is `o`, has the single term `μ(o)`.
  have key := o.rep.sum_moebius_ofEnd_invtRestrict ⊥
  simp only [le_bot_iff, Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]
    at key
  rwa [eq_of_dim_eq_zero (c := ofEnd (o.rep.invtRestrict (⊥ : o.rep.invtSubmodule).prop)) (by simp)
    h] at key

/-- `μ` takes real values. -/
@[simp]
theorem conj_moebius (c : SimilarityClass k) : conj (moebius c) = moebius c := by
  -- `c ↦ conj (μ c)` is also an inverse of `𝟙`, as `𝟙` and `1` are real.
  let μ' : HallAlgebra k := fun c ↦ conj (moebius c)
  have h : μ' * constOne = moebius * constOne := by
    refine ext_ofEnd fun _ g ↦ ?_
    have := Fintype.ofFinite g.invtSubmodule
    -- `μ ∗ 𝟙 = 1` at the class of `g`.
    have key := g.sum_moebius_ofEnd_invtRestrict ⊤
    simp only [le_top, Finset.filter_true, top_eq_bot_iff_finrank_eq_zero] at key
    have key' := congrArg conj key
    rw [map_sum] at key'
    rw [mul_ofEnd_eq_sum, mul_ofEnd_eq_sum]
    simpa [μ', apply_ite conj, key] using key'
  exact congrArg (· c) (isUnit_constOne.mul_right_cancel h)

end Moebius

/-! ### Block averages of `μ` -/

section BlockAverage

variable [Fintype k]

/-- The block average of `μ`: `δμ(a, ·) = μ(a) · μ`. -/
theorem blockAverage_moebius (c : SimilarityClass k) :
    blockAverage moebius c = moebius c • moebius := by
  -- Cancel `𝟙` in the second and then in the first variable: by Mackey's formula, both sides
  -- become `1 ⊗ 1` after multiplying by `𝟙` in both variables.
  refine isUnit_constOne.mul_right_cancel (ext_ofEnd fun _ y ↦ ?_)
  let F : HallAlgebra k := fun c ↦ (blockAverage moebius c * constOne : HallAlgebra k) (ofEnd y)
  let F' : HallAlgebra k := fun c ↦ (moebius c • moebius * constOne : HallAlgebra k) (ofEnd y)
  suffices h : F * constOne = F' * constOne from congrArg (· c) (isUnit_constOne.mul_right_cancel h)
  refine ext_ofEnd fun _ x ↦ ?_
  have := Fintype.ofFinite x.invtSubmodule
  have hx := x.sum_moebius_ofEnd_invtRestrict ⊤
  simp only [le_top, Finset.filter_true, top_eq_bot_iff_finrank_eq_zero] at hx
  have h_mackey := blockAverage_mul x y moebius constOne
  rw [moebius_mul_constOne, blockAverage_one_ofEnd, finsum_eq_sum_of_fintype] at h_mackey
  simp only [blockAverage_constOne] at h_mackey
  rw [mul_ofEnd_eq_sum, mul_ofEnd_eq_sum]
  simp only [F, F', constOne_apply, mul_one, smul_mul_assoc, smul_apply,
    moebius_mul_constOne, ← Finset.sum_mul, hx]
  simpa [one_apply] using h_mackey.symm

variable [Finite k] in
omit [Fintype k] in
/-- `B · μ` at a block triangular map is `B` at the block diagonal map times `μ`. -/
private theorem mul_moebius_blockTriangular (B : HallAlgebra k) (a : Module.End k V)
    (b : Module.End k W) (x : W →ₗ[k] V) :
    B (ofEnd (blockTriangular a b x)) * moebius (ofEnd (blockTriangular a b x)) =
      B (ofEnd (a.prodMap b)) * moebius (ofEnd (blockTriangular a b x)) := by
  by_cases h : moebius (ofEnd (blockTriangular a b x)) = 0
  · simp [h]
  · rw [ofEnd_blockTriangular_of_isSemisimple (Module.End.isSemisimple_of_moebius_ne_zero _ h)]

/-- The block averages of `B · μ` only see the block diagonal class:
`δ(B · μ)(a, b) = μ(a) μ(b) B(a ⊕ b)`. -/
theorem blockAverage_fun_mul_moebius (B : HallAlgebra k) (a : Module.End k V) (b : Module.End k W) :
    blockAverage (fun c ↦ B c * moebius c) (ofEnd a) (ofEnd b) =
      moebius (ofEnd a) * moebius (ofEnd b) * B (ofEnd (a.prodMap b)) := by
  have : Finite (W →ₗ[k] V) := Module.finite_of_finite k
  have := Fintype.ofFinite (W →ₗ[k] V)
  have h_mu := congrArg (· (ofEnd b)) (blockAverage_moebius (ofEnd a))
  simp only [smul_apply] at h_mu
  rw [blockAverage_ofEnd] at h_mu ⊢
  simp_rw [mul_moebius_blockTriangular B a b]
  rw [← Finset.mul_expect, h_mu, mul_comm]

end BlockAverage

/-! ### Supports of cuspidal functions -/

section CuspidalSupport

variable [Fintype k]

/-- For `A` cuspidal with `A(g) ≠ 0` and `P(g)` not invertible, `P(g)` is nilpotent: every block map
with diagonal blocks `g` on the Fitting component `C = ker P(g)^N` and on `V / C` is similar to
`g`, so the block average of `A` there is `A(g) ≠ 0` and one block is zero; it is not `C`. -/
private theorem isNilpotent_aeval_of_isCuspidal {A : HallAlgebra k} (hA : A.IsCuspidal)
    {g : Module.End k V} (hg : A (ofEnd g) ≠ 0) {P : k[X]} (h_not_unit : ¬IsUnit (aeval g P)) :
    IsNilpotent (aeval g P) := by
  obtain ⟨N, hN, hN₀⟩ : ∃ N : ℕ, IsCompl (LinearMap.ker (aeval g P ^ N))
      (LinearMap.range (aeval g P ^ N)) ∧ N ≠ 0 :=
    ((aeval g P).eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ne_atTop 0)).exists
  set T := aeval g P ^ N
  have hT (Y : Module.End k V) (hY : Commute Y g) : Commute Y T :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton k g)
      hY).pow_right N
  have hgT := hT g (Commute.refl g)
  have hC : LinearMap.ker T ∈ g.invtSubmodule := (Module.End.mem_invtSubmodule _).2 fun v hv ↦ by
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
    rw [← mul_apply_eq_comp, ← hgT.eq, mul_apply_eq_comp, hv, map_zero]
  -- The block average of `A` at the two blocks is `A(g) ≠ 0`.
  have : Finite ((V ⧸ LinearMap.ker T) →ₗ[k] LinearMap.ker T) := Module.finite_of_finite k
  have := Fintype.ofFinite ((V ⧸ LinearMap.ker T) →ₗ[k] LinearMap.ker T)
  have h_avg : blockAverage A (ofEnd (g.invtRestrict hC)) (ofEnd (g.invtQuot hC)) ≠ 0 := by
    rw [blockAverage_ofEnd]
    refine fun h ↦ hg ?_
    rw [← h, Finset.expect_congr rfl fun x _ ↦ by
      obtain ⟨y, hy⟩ := Module.End.exists_sylvester_eq hC rfl hN hT x
      rw [ofEnd_blockTriangular_eq_of_sylvester hC rfl hN hgT hy]]
    simp
  by_cases hC₀ : Module.finrank k (LinearMap.ker T) = 0
  · -- Then `T`, hence `P(g)`, is invertible.
    refine absurd ?_ h_not_unit
    have hT_inj : Function.Injective T :=
      LinearMap.ker_eq_bot.1 (Submodule.finrank_eq_zero.1 hC₀)
    have hT_unit : IsUnit T :=
      (Module.End.isUnit_iff T).2 ⟨hT_inj, LinearMap.injective_iff_surjective.1 hT_inj⟩
    exact (isUnit_pow_iff hN₀).1 hT_unit
  · have hQ₀ : Module.finrank k (V ⧸ LinearMap.ker T) = 0 := by
      by_contra hQ₀
      exact h_avg (hA.blockAverage_eq_zero (by simpa using hC₀) (by simpa using hQ₀))
    have hT₀ : T = 0 := by
      refine LinearMap.ker_eq_top.1 (Submodule.eq_top_of_finrank_eq ?_)
      have := (LinearMap.ker T).finrank_quotient_add_finrank
      omega
    exact ⟨N, hT₀⟩

/-- **Supports of cuspidal functions.** If `A` is cuspidal and `A(g) ≠ 0`, the characteristic
polynomial of `g` is a power of an irreducible polynomial. -/
theorem IsCuspidal.exists_charpoly_eq_pow {A : HallAlgebra k} (hA : A.IsCuspidal)
    {g : Module.End k V} (hg : A (ofEnd g) ≠ 0) :
    ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ g.charpoly = P ^ j := by
  by_cases hV : Module.finrank k V = 0
  · have := Module.finrank_zero_iff.1 hV
    exact ⟨X, 0, irreducible_X, by rw [pow_zero, LinearMap.charpoly_eq_one_of_subsingleton]⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hV)
  -- For an irreducible factor `P` of the minimal polynomial, `P(g)` is not invertible, hence
  -- nilpotent.
  obtain ⟨P, hP_monic, hP, hP_dvd⟩ := exists_monic_irreducible_factor _ (minpoly.not_isUnit k g)
  obtain ⟨j, hj⟩ := g.exists_charpoly_eq_pow_of_isNilpotent_aeval hP hP_monic
    (isNilpotent_aeval_of_isCuspidal hA hg (minpoly.not_isUnit_aeval_of_dvd
      (Algebra.IsIntegral.isIntegral g) hP.natDegree_pos hP_dvd))
  exact ⟨P, j, hP, hj⟩

end CuspidalSupport

/-! ### Green's cuspidal functions -/

section Green

variable (K : Type*) [Field K] [Algebra k K] (η : K → ℂ)

variable [Finite k]

/-- `C_η = -(μ ∗ β_η)`: at `g`, the terms `β(g|_U) μ(g|_U) + μ(g|_U) β(g|_{V/U}) = β(g) μ(g|_U)`
add up to `β(g) · 1(g) = 0`. -/
private theorem greenCuspidal_eq_neg_moebius_mul :
    (greenCuspidal K η : HallAlgebra k) = -(moebius * eigenvalueSum K η) := by
  refine ext_ofEnd fun _ g ↦ ?_
  have := Fintype.ofFinite g.invtSubmodule
  rw [neg_apply, eq_neg_iff_add_eq_zero, greenCuspidal_ofEnd, mul_ofEnd_eq_sum,
    finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  have h_terms (U : g.invtSubmodule) :
      eigenvalueSum K η (ofEnd (g.invtRestrict U.prop)) * moebius (ofEnd (g.invtRestrict U.prop)) +
        moebius (ofEnd (g.invtRestrict U.prop)) * eigenvalueSum K η (ofEnd (g.invtQuot U.prop)) =
      eigenvalueSum K η (ofEnd g) * moebius (ofEnd (g.invtRestrict U.prop)) := by
    rw [eigenvalueSum_ofEnd_eq_add K η U.prop]
    ring
  have key := g.sum_moebius_ofEnd_invtRestrict ⊤
  simp only [le_top, Finset.filter_true, top_eq_bot_iff_finrank_eq_zero] at key
  simp only [h_terms, ← Finset.mul_sum, key]
  split_ifs with h
  · simp [eigenvalueSum_eq_zero_of_dim_eq_zero K η (o := ofEnd g) (by simpa using h)]
  · simp

/-- **`C_η ∗ 𝟙 = -β_η`.** -/
@[simp]
theorem greenCuspidal_mul_constOne :
    (greenCuspidal K η * constOne : HallAlgebra k) = -eigenvalueSum K η := by
  rw [greenCuspidal_eq_neg_moebius_mul, neg_mul, mul_comm moebius, mul_assoc,
    moebius_mul_constOne, mul_one]

/-- `C_η` vanishes on the class of size `0`. -/
theorem greenCuspidal_eq_zero_of_dim_eq_zero {o : SimilarityClass k} (h : o.dim = 0) :
    greenCuspidal K η o = 0 := by
  have := Fintype.ofFinite o.rep.invtSubmodule
  have : Subsingleton (Fin o.dim → k) := by rw [h]; infer_instance
  rw [← ofEnd_rep o, greenCuspidal_ofEnd, finsum_eq_sum_of_fintype]
  refine Finset.sum_eq_zero fun U _ ↦ ?_
  rw [eigenvalueSum_eq_zero_of_dim_eq_zero K η (by simp [Module.finrank_zero_of_subsingleton]),
    zero_mul]

end Green

section GreenFintype

variable (K : Type*) [Field K] [Algebra k K] (η : K → ℂ) [Fintype k]

/-- **`C_η` is cuspidal.** -/
theorem isCuspidal_greenCuspidal : (greenCuspidal K η : HallAlgebra k).IsCuspidal := by
  -- By Mackey's formula and the block averages of `β_η · μ`, the block average of `C_η` at
  -- `(a, b)` is a sum of terms each with a factor `Σ_U μ(c|_U) = 1(c)`, `c = a` or `c = b`, which
  -- vanishes as `a` and `b` have positive size.
  refine isCuspidal_iff.2 fun a b ha hb ↦ ?_
  rw [← ofEnd_rep a, ← ofEnd_rep b]
  have := Fintype.ofFinite a.rep.invtSubmodule
  have := Fintype.ofFinite b.rep.invtSubmodule
  rw [greenCuspidal_eq_mul_constOne K η (F := fun c ↦ eigenvalueSum K η c * moebius c)
    (fun _ ↦ rfl), blockAverage_mul, finsum_eq_sum_of_fintype]
  simp only [blockAverage_constOne, mul_ofEnd_eq_sum, constOne_apply, mul_one,
    blockAverage_fun_mul_moebius, eigenvalueSum_ofEnd_prodMap]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    mul_assoc, mul_comm (moebius _) (eigenvalueSum K η _)]
  -- Each part has a factor `Σ_U μ(c|_U) = 1(c)` with `c = a` or `c = b`, of positive size.
  have ka := a.rep.sum_moebius_ofEnd_invtRestrict ⊤
  have kb := b.rep.sum_moebius_ofEnd_invtRestrict ⊤
  simp only [le_top, Finset.filter_true, top_eq_bot_iff_finrank_eq_zero] at ka kb
  simp [ka, kb, ha, hb]

variable {K} in
/-- **`C_η` only sees the Frobenius orbits of the eigenvalues.** Let `g` act on a space of
dimension `d`, and suppose `η′(z) = a η(z)` at every `z ∈ K` with `z ^ q ^ d = z` whose
Frobenius orbit `z, z ^ q, …, z ^ q ^ (d - 1)` lists the eigenvalues of `g` with multiplicity.
Then `C_{η′}(g) = a C_η(g)`. If some `C_θ(g)` is nonzero, the characteristic polynomial of `g` is a
power of an irreducible polynomial, since `C_θ` is cuspidal, and then every eigenvalue of `g`, and
of `g` on an invariant subspace, has this property. -/
theorem greenCuspidal_ofEnd_eq_mul {η η' : K → ℂ} {a : ℂ} {g : Module.End k V}
    (h : ∀ z : K, g.charpoly.aroots K =
        (Multiset.range (Module.finrank k V)).map (fun i ↦ z ^ Fintype.card k ^ i) →
      z ^ Fintype.card k ^ Module.finrank k V = z → η' z = a * η z) :
    greenCuspidal K η' (ofEnd g) = a * greenCuspidal K η (ofEnd g) := by
  by_cases h₀ : ∀ θ : K → ℂ, greenCuspidal K θ (ofEnd g) = 0
  · simp [h₀]
  obtain ⟨θ, hθ⟩ := not_forall.1 h₀
  obtain ⟨P, j, hP, hg⟩ := (isCuspidal_greenCuspidal K θ).exists_charpoly_eq_pow hθ
  -- Every eigenvalue `z` of `g` has the property of `h`.
  have h_root (z : K) (hz : aeval z g.charpoly = 0) : η' z = a * η z := by
    rw [hg, map_pow] at hz
    have hz := eq_zero_of_pow_eq_zero hz
    have h₁ := TauCeti.FiniteField.aroots_pow_eq_map_pow_card_pow hP hz j
    have h₂ := (TauCeti.FiniteField.pow_card_pow_eq_self_iff hP hz).2
      (natDegree_pow P j ▸ dvd_mul_left P.natDegree j)
    have h_deg : (P ^ j).natDegree = Module.finrank k V := by
      rw [← hg, LinearMap.charpoly_natDegree]
    rw [h_deg, ← hg] at h₁
    rw [h_deg] at h₂
    exact h z h₁ h₂
  have := Fintype.ofFinite g.invtSubmodule
  rw [greenCuspidal_ofEnd, greenCuspidal_ofEnd, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  -- The eigenvalues of `g` on `W` are eigenvalues of `g`.
  have h_map : ((g.invtRestrict W.prop).charpoly.aroots K).map η' =
      ((g.invtRestrict W.prop).charpoly.aroots K).map (fun z ↦ a * η z) := by
    refine Multiset.map_congr rfl fun z hz ↦ h_root z ?_
    rw [← Module.End.charpoly_invtRestrict_mul_charpoly_invtQuot W.prop, map_mul,
      (mem_aroots.1 hz).2, zero_mul]
  rw [eigenvalueSum_ofEnd, eigenvalueSum_ofEnd, h_map, Multiset.sum_map_mul_left, mul_assoc]

end GreenFintype

end TauCeti.HallAlgebra
