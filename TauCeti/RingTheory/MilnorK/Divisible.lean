/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Polynomial.Splits
public import TauCeti.LinearAlgebra.Multilinear.Bilinear
public import TauCeti.LinearAlgebra.PiTensorProduct.Divisible
public import TauCeti.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.MilnorK.Homogeneous
public import TauCeti.RingTheory.Regular.IsSMulRegular

/-!
# Unique divisibility of Milnor K-groups

Let `R` be a commutative ring and write the unit group additively, `U = Additive Rˣ`. The
degree-two relations of Milnor K-theory are the *Steinberg tensors* `a ⊗ b ∈ U ⊗[ℤ] U` for units
`a, b` with `a + b = 1`. This file proves that if `Xⁿ - a` splits into linear factors over `R`,
the Steinberg tensor `a ⊗ b` is `n` times a sum of Steinberg tensors, and deduces that the Milnor
K-groups `K_nᴹ(F)` of an algebraically closed field `F` are uniquely divisible for `n ≥ 2`.

The argument is the root factorization of `Xⁿ - a`. Write `Xⁿ - a = ∏ (X - cᵢ)`, with roots
counted with multiplicity. Evaluating at `1` gives `b = 1 - a = ∏ (1 - cᵢ)`. Each root is a unit
with `cᵢⁿ = a`, and each `1 - cᵢ` divides the unit `b`, so it is a unit with
`cᵢ + (1 - cᵢ) = 1`. Hence

`a ⊗ b = ∑ᵢ a ⊗ (1 - cᵢ) = ∑ᵢ cᵢⁿ ⊗ (1 - cᵢ) = n • ∑ᵢ cᵢ ⊗ (1 - cᵢ)`.

Now let `m ≠ 0` be the multiplier and suppose every `Xᵐ - a` splits. Placing the identity above,
with `m` in place of `n`, in two neighbouring entries of a pure tensor shows that every Steinberg
relation module `R_n ⊆ U^{⊗ n}` of `TauCeti.MilnorK.steinbergRelations` is `m`-divisible. By
`TauCeti.MilnorK.degreeEquiv`, `K_nᴹ(R)` is the quotient `U^{⊗ n} / R_n`. For `n ≥ 2` the tensor
power has at least two `m`-divisible factors, so multiplication by `m` is bijective on it
(`TauCeti.LinearAlgebra.PiTensorProduct.Divisible`), and it stays bijective on the quotient by
the `m`-divisible submodule `R_n` (`TauCeti.RingTheory.Regular.IsSMulRegular`). Over a field of
characteristic `p` the roots of `Xᵖ - a` all coincide, and the argument uses them with their
multiplicity. Degree one is genuinely excluded: `Fˣ` is divisible but contains the roots of
unity.

## Main results

* `TauCeti.exists_ofMul_tmul_ofMul_eq_nsmul_sum`: if `a + b = 1` and `Xⁿ - a` splits, then
  `a ⊗ b = n • ∑ᵢ cᵢ ⊗ dᵢ` for finitely many unit pairs with `cᵢ + dᵢ = 1` and `cᵢⁿ = a`; here
  `n` is the multiplier.
* `TauCeti.MilnorK.steinbergRelations_le_smul`: if every `Xᵐ - a` splits, the Steinberg relation
  modules `R_n` are `m`-divisible.
* `TauCeti.MilnorK.bijective_nsmul_degree`: if every `Xᵐ - a` splits, multiplication by `m ≠ 0`
  is bijective on `K_nᴹ(R)` for `n ≥ 2`.
* `TauCeti.MilnorK.bijective_nsmul_degree_of_isAlgClosed`: the Milnor K-groups of an
  algebraically closed field are uniquely divisible in degrees at least two.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Proposition 6.4.1, Example 7.2(b) and Exercise 7.3.
-/

public section

open Polynomial
open scoped TensorProduct Pointwise

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **Root factorization of a Steinberg tensor.** Let `a, b` be units of a commutative ring
with `a + b = 1`, and suppose `Xⁿ - a` splits for some `n ≠ 0`. Then in
`Additive Rˣ ⊗[ℤ] Additive Rˣ` the Steinberg tensor `a ⊗ b` is `n` times a finite sum of Steinberg
tensors `c ⊗ d` of unit pairs with `c + d = 1` and `cⁿ = a`. -/
theorem exists_ofMul_tmul_ofMul_eq_nsmul_sum {n : ℕ} (hn : n ≠ 0) {a b : Rˣ}
    (hab : (a : R) + b = 1) (hsplit : (X ^ n - C (a : R)).Splits) :
    ∃ s : Multiset (Rˣ × Rˣ), (∀ x ∈ s, (x.1 : R) + x.2 = 1 ∧ x.1 ^ n = a) ∧
      Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b =
        n • (s.map fun x ↦ Additive.ofMul x.1 ⊗ₜ[ℤ] Additive.ofMul x.2).sum := by
  classical
  -- A factorization `Xⁿ - a = ∏ (X - c)`, with the roots `c` counted with multiplicity.
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.1 hsplit
  rw [(monic_X_pow_sub_C (a : R) hn).leadingCoeff, C_1, one_mul] at hm
  have heval (x : R) : x ^ n - a = (m.map (x - ·)).prod := by
    simpa [eval_multiset_prod, Multiset.map_map, Function.comp_def] using congrArg (eval x) hm
  have hpow (c : R) (hc : c ∈ m) : c ^ n = a := by
    rw [← sub_eq_zero, heval]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨c, hc, sub_self c⟩)
  -- Evaluating the factorization at `1` gives `b = ∏ (1 - c)`.
  have hprod : (m.map (1 - ·)).prod = (b : R) := by
    rw [← heval, one_pow, ← hab, add_sub_cancel_left]
  -- Every root is a unit, since its `n`th power is the unit `a`.
  lift m to Multiset Rˣ using fun c hc ↦ (isUnit_pow_iff hn).1 (hpow c hc ▸ a.isUnit)
  simp only [Multiset.map_map, Function.comp_def] at hprod
  replace hpow (c : Rˣ) (hc : c ∈ m) : c ^ n = a :=
    Units.ext (by simpa using hpow c (Multiset.mem_map_of_mem _ hc))
  -- Every `1 - c` divides the unit `b`, so it is a unit `d c`.
  have hunit (c : Rˣ) (hc : c ∈ m) : ∃ d : Rˣ, (d : R) = 1 - c :=
    isUnit_of_dvd_unit (Multiset.dvd_prod (Multiset.mem_map_of_mem (fun c : Rˣ ↦ 1 - (c : R)) hc))
      (hprod ▸ b.isUnit)
  choose! d hd using hunit
  have hb : b = (m.map d).prod := Units.ext <| by
    rw [← hprod, ← Units.coeHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun c hc ↦ (hd c hc).symm)
  refine ⟨m.map fun c ↦ (c, d c), ?_, ?_⟩
  · simp only [Multiset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨by simp [hd c hc], hpow c hc⟩
  · simp only [hb, ofMul_multiset_prod, TensorProduct.tmul_multiset_sum, Multiset.map_map,
      Function.comp_def, ← Multiset.sum_map_nsmul]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun c hc ↦ ?_)
    rw [← hpow c hc, ofMul_pow, TensorProduct.smul_tmul']

namespace MilnorK

open Function

/-- If `Xᵐ - a` splits for every unit `a`, the Steinberg relation modules are `m`-divisible. -/
theorem steinbergRelations_le_smul {m : ℕ} (hm : m ≠ 0)
    (hsplit : ∀ a : Rˣ, (X ^ m - C (a : R)).Splits) (n : ℕ) :
    steinbergRelations R n ≤ (m : ℤ) • steinbergRelations R n := by
  conv_lhs => rw [steinbergRelations_eq_span]
  rw [Submodule.span_le]
  rintro _ ⟨f, i, hi, h, rfl⟩
  set i' : Fin n := ⟨i, Nat.lt_of_succ_lt hi⟩
  set j' : Fin n := ⟨i + 1, hi⟩
  have hij : i' ≠ j' := by simp [i', j', Fin.ext_iff]
  obtain ⟨s, hs, hsum⟩ := exists_ofMul_tmul_ofMul_eq_nsmul_sum hm h (hsplit _)
  -- Place both sides of `hsum` into the entries `i` and `i + 1` of the pure tensor of `f`.
  have key := congrArg (TensorProduct.lift
    ((PiTensorProduct.tprod ℤ).toLinearMap₂ (fun k ↦ Additive.ofMul (f k)) hij)) hsum
  rw [TensorProduct.lift.tmul, MultilinearMap.toLinearMap₂_apply, update_eq_self, update_eq_self,
    map_nsmul, map_multiset_sum, Multiset.map_map] at key
  rw [key, ← natCast_zsmul]
  refine Submodule.smul_mem_pointwise_smul _ _ _ (multiset_sum_mem _ ?_)
  simp only [Multiset.mem_map, comp_apply, TensorProduct.lift.tmul,
    MultilinearMap.toLinearMap₂_apply]
  rintro _ ⟨x, hx, rfl⟩
  have e : update (update (fun k ↦ Additive.ofMul (f k)) j' (Additive.ofMul x.2)) i'
      (Additive.ofMul x.1) = fun k ↦ Additive.ofMul (update (update f j' x.2) i' x.1 k) := by
    ext k
    simp only [update_apply]
    split_ifs <;> rfl
  rw [e]
  exact tprod_mem_steinbergRelations (update (update f j' x.2) i' x.1) i hi (by
    simpa [i', j', update_apply, Fin.ext_iff] using (hs x hx).1)

/-- If `Xᵐ - a` splits for every unit `a` and `m ≠ 0`, every unit has an `m`-th root. -/
private theorem surjective_zsmul_of_splits {m : ℕ} (hm : m ≠ 0)
    (hsplit : ∀ a : Rˣ, (X ^ m - C (a : R)).Splits) :
    Function.Surjective fun u : Additive Rˣ ↦ (m : ℤ) • u := by
  intro u
  obtain ⟨v, hv⟩ := Units.exists_pow_eq_of_splits hm (hsplit u.toMul)
  exact ⟨Additive.ofMul v, by dsimp only; rw [natCast_zsmul, ← ofMul_pow, hv, ofMul_toMul]⟩

/-- **Unique divisibility of Milnor K-groups.** If every polynomial `Xᵐ - a`, `a` a unit, splits,
then multiplication by `m ≠ 0` is bijective on the Milnor K-group `K_nᴹ(R)` of every degree
`n ≥ 2`. -/
theorem bijective_nsmul_degree {m : ℕ} (hm : m ≠ 0)
    (hsplit : ∀ a : Rˣ, (X ^ m - C (a : R)).Splits) {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective fun x : degree R n ↦ m • x := by
  have hU := surjective_zsmul_of_splits hm hsplit
  -- Multiplication by `m` is bijective on `T_n` and `R_n` is `m`-divisible, so it is bijective on
  -- the quotient `T_n / R_n`.
  have hQ : Function.Bijective
      fun q : (⨂[ℤ]^n (Additive Rˣ)) ⧸ steinbergRelations R n ↦ (m : ℤ) • q := by
    refine ⟨(PiTensorProduct.isSMulRegular_of_surjective_smul (i₀ := ⟨0, by omega⟩)
      (i₁ := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) hU hU).quotient_of_le_smul
      (steinbergRelations_le_smul hm hsplit n), fun q ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨y, rfl⟩ := PiTensorProduct.surjective_smul_of_surjective ⟨0, by omega⟩ hU x
    exact ⟨Submodule.Quotient.mk y, (Submodule.Quotient.mk_smul _ _ _).symm⟩
  have h : (fun x : degree R n ↦ m • x) =
      degreeEquiv R n ∘ (fun q ↦ (m : ℤ) • q) ∘ (degreeEquiv R n).symm := by
    ext x
    simp
  rw [h]
  exact (degreeEquiv R n).bijective.comp (hQ.comp (degreeEquiv R n).symm.bijective)

/-- **Milnor K-groups of an algebraically closed field are uniquely divisible** in every degree
`n ≥ 2`: multiplication by every `m ≠ 0` is bijective on `K_nᴹ(F)`. -/
theorem bijective_nsmul_degree_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] {m : ℕ}
    (hm : m ≠ 0) {n : ℕ} (hn : 2 ≤ n) : Function.Bijective fun x : degree F n ↦ m • x :=
  bijective_nsmul_degree hm (fun _ ↦ IsAlgClosed.splits _) hn

end MilnorK

end TauCeti
