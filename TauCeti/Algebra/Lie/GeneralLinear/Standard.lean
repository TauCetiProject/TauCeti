/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Dual
public import TauCeti.Algebra.Lie.GeneralLinear.Carrier

/-!
# The standard `gl n`-module and its dual

The standard module of `gl n R = Matrix n n R` is the coordinate space `n → R`, with a matrix
acting by multiplication on vectors; this is Mathlib's `Matrix.instLieRingModule`, whose bracket
is `Matrix.lie_apply : ⁅A, v⁆ = A *ᵥ v`. Its dual `Module.Dual R (n → R)` carries the
contragredient action `⁅A, f⁆ v = - f (A *ᵥ v)` of `Module.Dual.instLieRingModule`. This file
computes the action of the matrix units on both, and identifies both with named irreducible
carriers `TauCeti.glIrreducible`.

Writing `εₜ = Pi.single t 1` for the coordinate tuples, the standard basis vector `Pi.single t 1`
of `n → R` has weight `εₜ` and the dual basis functional `LinearMap.proj t` has weight `-εₜ`. The
identity matrix spans the centre of `gl n R` and acts by `1` on the standard module and by `-1` on
its dual, so away from characteristic two the two modules are not isomorphic
(`TauCeti.isEmpty_lieModuleEquiv_dual_pi`). This is why the dual standard module needs a Pieri rule
of its own.

In the matrix unit positive system of `TauCeti/Algebra/Lie/GeneralLinear/Borel.lean` the raising
matrix units move a standard basis vector *down* the order and a dual basis functional *up* it. The
highest weight vector of the standard module is therefore the basis vector at the least index, of
weight `ε_first`, while the highest weight vector of the dual is the functional at the *greatest*
index, of weight `-ε_last`. Both modules are irreducible — the standard one because the matrix unit
`E_{st}` carries a vector with nonzero `t`-th coordinate to a multiple of the `s`-th basis vector,
the dual one by `TauCeti.LieModule.isIrreducible_dual` — so for `Fin (N + 1)` over a
characteristic-zero field each is *the* irreducible of its highest weight:

`Fin (N + 1) → K ≅ L(ε₀)` and `Module.Dual K (Fin (N + 1) → K) ≅ L(-ε_last)`.

Both weights are dominant: dominance of `gl` weights is a condition on consecutive differences, and
`ε₀` drops by one at the first step while `-ε_last` rises by one at the last.

## Main results

* `TauCeti.lie_single_one_pi` and `TauCeti.lie_single_one_dual`: the action of the matrix unit
  `Eᵢⱼ` on a vector of the standard module and on a dual basis functional.
* `TauCeti.one_lie_pi` and `TauCeti.one_lie_dual_pi`: the identity matrix, which spans the centre
  of `gl n R`, acts by `1` on the standard module and by `-1` on its dual.
* `TauCeti.isGlHighestWeightVector_pi_single` and `TauCeti.isGlHighestWeightVector_proj`: the basis
  vector at a least index is a highest weight vector of weight `εₜ`, and the dual basis functional
  at a greatest index is one of weight `-εₜ`.
* `TauCeti.isIrreducible_pi` and `TauCeti.isIrreducible_dual_pi`: **both modules are irreducible**
  over a field, as soon as the index type is nonempty.
* `TauCeti.isEmpty_lieModuleEquiv_dual_pi`: **the standard module is not isomorphic to its dual**
  outside characteristic two.
* `TauCeti.isGlDominantIntegral_pi_single_zero` and
  `TauCeti.isGlDominantIntegral_neg_pi_single_last`: the two highest weights are dominant integral.
* `TauCeti.nonempty_lieModuleEquiv_glIrreducible_pi` and
  `TauCeti.nonempty_lieModuleEquiv_glIrreducible_dual_pi`: **the standard module is `L(ε₀)` and its
  dual is `L(-ε_last)`**, with `TauCeti.finrank_glIrreducible_pi_single_zero` and
  `TauCeti.finrank_glIrreducible_neg_pi_single_last` reading off that both have dimension `N + 1`.

## Roadmap

The dual standard module is the first factor of the **dual-standard Pieri rule**
`V* ⊗ L(μ) ≅ ⨁ₜ L(μ - εₜ)` of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which pins the standard module as
Mathlib's `Fin n → K` instance and `εₜ` as `Pi.single t 1`. This file supplies that factor: what
`V*` is as a `gl n`-module, that it is irreducible, and which named carrier it is. The Pieri
decomposition itself is not proved here.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §15.1 and
  §15.3.
-/

public section

namespace TauCeti

open Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

/-! ### The matrix units on the standard module and on its dual -/

section CommRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **A matrix unit on the standard module.** The matrix unit `Eᵢⱼ` sends a vector `v` of `n → R`
to the `j`-th coordinate of `v` placed in the `i`-th slot. -/
theorem lie_single_one_pi (i j : n) (v : n → R) :
    ⁅(Matrix.single i j (1 : R) : Matrix n n R), v⁆ = Pi.single i (v j) := by
  rw [Matrix.lie_apply, Matrix.single_mulVec_eq, one_mul,
    ← Pi.single_smul' i (v j) (1 : R), smul_eq_mul, mul_one]

/-- **A matrix unit on the dual standard module.** Against the contragredient action the matrix
unit `Eᵢⱼ` sends the dual basis functional at `i` to minus the one at `j`, and kills the dual basis
functional at every other index. -/
theorem lie_single_one_dual (i j t : n) :
    ⁅(Matrix.single i j (1 : R) : Matrix n n R), (LinearMap.proj t : Dual R (n → R))⁆ =
      if i = t then -(LinearMap.proj j : Dual R (n → R)) else 0 := by
  refine LinearMap.ext fun v => ?_
  rw [Module.Dual.lie_apply, lie_single_one_pi]
  by_cases h : i = t
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- **The identity matrix acts by one on the standard module.** The identity spans the centre of
`gl n R`, so this is the central weight of the standard module. -/
theorem one_lie_pi (v : n → R) : ⁅(1 : Matrix n n R), v⁆ = v := by
  rw [Matrix.lie_apply, Matrix.one_mulVec]

/-- **The identity matrix acts by minus one on the dual standard module**: the central weight of
the dual is the negative of that of the standard module. -/
theorem one_lie_dual_pi (f : Dual R (n → R)) : ⁅(1 : Matrix n n R), f⁆ = -f := by
  refine LinearMap.ext fun v => ?_
  rw [Module.Dual.lie_apply, one_lie_pi, LinearMap.neg_apply]

/-- **The weight of a standard basis vector.** The diagonal matrix unit `Eᵢᵢ` scales the basis
vector `Pi.single t 1` by the `i`-th entry of the coordinate tuple `εₜ = Pi.single t 1`, so that
basis vector is a weight vector of weight `εₜ`. -/
theorem lie_single_self_pi_single (i t : n) :
    ⁅(Matrix.single i i (1 : R) : Matrix n n R), (Pi.single t (1 : R) : n → R)⁆ =
      (Pi.single t (1 : R) : n → R) i • (Pi.single t (1 : R) : n → R) := by
  rw [lie_single_one_pi, Pi.single_apply]
  by_cases h : i = t
  · subst h
    simp
  · simp [h]

/-- **The weight of a dual basis functional.** The diagonal matrix unit `Eᵢᵢ` scales the dual basis
functional at `t` by the `i`-th entry of `-εₜ`, so that functional is a weight vector of weight
`-εₜ`. -/
theorem lie_single_self_proj (i t : n) :
    ⁅(Matrix.single i i (1 : R) : Matrix n n R), (LinearMap.proj t : Dual R (n → R))⁆ =
      (-(Pi.single t (1 : R)) : n → R) i • (LinearMap.proj t : Dual R (n → R)) := by
  refine LinearMap.ext fun v => ?_
  rw [Module.Dual.lie_apply, lie_single_one_pi]
  by_cases h : i = t
  · subst h
    simp
  · simp [h, Ne.symm h]

variable [Nontrivial R] [LinearOrder n]

/-- **The highest weight vector of the standard module.** The raising matrix units move a standard
basis vector down the order, so the basis vector at a least index `t` is annihilated by all of
them, and is a highest weight vector of weight `εₜ`. -/
theorem isGlHighestWeightVector_pi_single {t : n} (ht : ∀ i, t ≤ i) :
    IsGlHighestWeightVector (Pi.single t (1 : R)) (Pi.single t (1 : R) : n → R) := by
  refine isGlHighestWeightVector_iff.mpr
    ⟨fun h => ?_, fun i => lie_single_self_pi_single i t, ?_⟩
  · simpa using congrFun h t
  · intro i j hij
    rw [lie_single_one_pi, Pi.single_eq_of_ne ((ht i).trans_lt hij).ne', Pi.single_zero]

/-- **The highest weight vector of the dual standard module.** The raising matrix units move a dual
basis functional up the order, so the functional at a greatest index `t` is annihilated by all of
them, and is a highest weight vector of weight `-εₜ`. -/
theorem isGlHighestWeightVector_proj {t : n} (ht : ∀ i, i ≤ t) :
    IsGlHighestWeightVector (-(Pi.single t (1 : R)))
      (LinearMap.proj t : Dual R (n → R)) := by
  refine isGlHighestWeightVector_iff.mpr
    ⟨fun h => ?_, fun i => lie_single_self_proj i t, ?_⟩
  · simpa using congr($h (Pi.single t (1 : R)))
  · intro i j hij
    rw [lie_single_one_dual, ite_eq_right (hij.trans_le (ht j)).ne]

end CommRing

/-! ### Irreducibility -/

section Field

variable {K : Type u} [Field K] {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]

/-- **The standard module is irreducible.** A nonzero vector `v` of a Lie submodule has some
nonzero coordinate `v t`, and the matrix unit `E_{st}` carries `v` to `v t` times the `s`-th basis
vector; dividing by `v t` puts every basis vector in the submodule. -/
theorem isIrreducible_pi : _root_.LieModule.IsIrreducible K (Matrix n n K) (n → K) := by
  refine _root_.LieModule.IsIrreducible.mk fun N hN => ?_
  obtain ⟨v, hvN, hv⟩ : ∃ v, v ∈ N ∧ v ≠ 0 := by
    by_contra hcon
    refine hN ((LieSubmodule.eq_bot_iff N).mpr fun m hm => ?_)
    by_contra hm0
    exact hcon ⟨m, hm, hm0⟩
  obtain ⟨t, ht⟩ : ∃ t, v t ≠ 0 := by
    rw [Function.ne_iff] at hv
    simpa using hv
  have hbasis (s : n) : (Pi.single s (1 : K) : n → K) ∈ N := by
    have hlie : ⁅(Matrix.single s t (1 : K) : Matrix n n K), v⁆ ∈ N := N.lie_mem hvN
    have hmem := SMulMemClass.smul_mem (v t)⁻¹ hlie
    rwa [lie_single_one_pi, ← Pi.single_smul' s (v t)⁻¹ (v t), smul_eq_mul,
      inv_mul_cancel₀ ht] at hmem
  rw [← LieSubmodule.toSubmodule_eq_top]
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun s _ => ?_
  have hmem := SMulMemClass.smul_mem (x s) (hbasis s)
  rwa [← Pi.single_smul' s (x s) (1 : K), smul_eq_mul, mul_one] at hmem

/-- **The dual standard module is irreducible**, by irreducibility of the standard module and
`TauCeti.LieModule.isIrreducible_dual`. -/
theorem isIrreducible_dual_pi :
    _root_.LieModule.IsIrreducible K (Matrix n n K) (Dual K (n → K)) :=
  have := isIrreducible_pi (K := K) (n := n)
  TauCeti.LieModule.isIrreducible_dual

/-- **The standard module is not isomorphic to its dual** away from characteristic two. The
identity matrix acts by `1` on the standard module and by `-1` on its dual, so an equivalence
would halve every vector to zero. -/
theorem isEmpty_lieModuleEquiv_dual_pi (h2 : (2 : K) ≠ 0) :
    IsEmpty ((n → K) ≃ₗ⁅K, Matrix n n K⁆ Dual K (n → K)) := by
  refine ⟨fun e => ?_⟩
  have hv : (Pi.single (Classical.arbitrary n) (1 : K) : n → K) ≠ 0 := fun h => by
    simpa using congrFun h (Classical.arbitrary n)
  have hlie := LieModuleHom.map_lie (e : (n → K) →ₗ⁅K, Matrix n n K⁆ Dual K (n → K))
    (1 : Matrix n n K) (Pi.single (Classical.arbitrary n) (1 : K))
  simp only [LieModuleEquiv.coe_coe] at hlie
  rw [one_lie_pi, one_lie_dual_pi] at hlie
  have h0 : (2 : K) • e (Pi.single (Classical.arbitrary n) (1 : K)) = 0 := by
    rw [two_smul, ← sub_neg_eq_add, ← hlie, sub_self]
  refine hv (e.injective ?_)
  rw [map_zero]
  exact (smul_eq_zero.mp h0).resolve_left h2

end Field

/-! ### The two named irreducible carriers -/

section Carrier

variable {K : Type u} [Field K] [CharZero K] (N : ℕ)

/-- **The highest weight of the standard module is dominant**: `ε₀` drops by one at the first
consecutive step and is constant afterwards. -/
theorem isGlDominantIntegral_pi_single_zero :
    IsGlDominantIntegral (Pi.single (0 : Fin (N + 1)) (1 : K)) := by
  rw [isGlDominantIntegral_iff]
  intro i j hij
  have hj : j ≠ 0 := fun h => by simp [h] at hij
  by_cases hi : i = 0
  · exact ⟨1, by simp [hi, hj]⟩
  · exact ⟨0, by simp [hi, hj]⟩

/-- **The highest weight of the dual standard module is dominant**: `-ε_last` is constant and then
rises by one at the last consecutive step. -/
theorem isGlDominantIntegral_neg_pi_single_last :
    IsGlDominantIntegral (-(Pi.single (Fin.last N) (1 : K))) := by
  rw [isGlDominantIntegral_iff]
  intro i j hij
  have hi : i ≠ Fin.last N := by
    intro h
    have := j.isLt
    rw [h, Fin.val_last] at hij
    omega
  by_cases hj : j = Fin.last N
  · exact ⟨1, by simp [hi, hj]⟩
  · exact ⟨0, by simp [hi, hj]⟩

/-- **The standard module is the named irreducible `L(ε₀)`.** -/
theorem nonempty_lieModuleEquiv_glIrreducible_pi :
    Nonempty ((Fin (N + 1) → K) ≃ₗ⁅K, Matrix (Fin (N + 1)) (Fin (N + 1)) K⁆
      glIrreducible (N + 1) (Pi.single (0 : Fin (N + 1)) (1 : K))) :=
  have := isIrreducible_pi (K := K) (n := Fin (N + 1))
  nonempty_lieModuleEquiv_glIrreducible (isGlDominantIntegral_pi_single_zero N)
    (isGlHighestWeightVector_pi_single Fin.zero_le)

/-- **The dual standard module is the named irreducible `L(-ε_last)`.** -/
theorem nonempty_lieModuleEquiv_glIrreducible_dual_pi :
    Nonempty (Dual K (Fin (N + 1) → K) ≃ₗ⁅K, Matrix (Fin (N + 1)) (Fin (N + 1)) K⁆
      glIrreducible (N + 1) (-(Pi.single (Fin.last N) (1 : K)))) :=
  have := isIrreducible_dual_pi (K := K) (n := Fin (N + 1))
  nonempty_lieModuleEquiv_glIrreducible (isGlDominantIntegral_neg_pi_single_last N)
    (isGlHighestWeightVector_proj Fin.le_last)

/-- `L(ε₀)` for `gl (N + 1)` has dimension `N + 1`: it is the standard module. -/
theorem finrank_glIrreducible_pi_single_zero :
    finrank K (glIrreducible (N + 1) (Pi.single (0 : Fin (N + 1)) (1 : K))) = N + 1 := by
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_glIrreducible_pi (K := K) N
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]

/-- `L(-ε_last)` for `gl (N + 1)` has dimension `N + 1`: it is the dual standard module. -/
theorem finrank_glIrreducible_neg_pi_single_last :
    finrank K (glIrreducible (N + 1) (-(Pi.single (Fin.last N) (1 : K)))) = N + 1 := by
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_glIrreducible_dual_pi (K := K) N
  rw [← e.toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq, Module.finrank_fin_fun]

end Carrier

end TauCeti
