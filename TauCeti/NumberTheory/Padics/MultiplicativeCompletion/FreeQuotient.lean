/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
import TauCeti.Algebra.Module.Torsion.FreeQuotient
import TauCeti.NumberTheory.LocalField.DeepUnits
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.LocalField.IntegerRing
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Finite

/-!
# The free quotient of the p-adic completion of units

For a finite extension `L` of `ℚ_[p]`, the `p`-adic completion `A(L) = lim_m Lˣ/(Lˣ)^(p^m)` of
`TauCeti.padicCompletionUnits` is, modulo its `ℤ_p`-torsion, a free `ℤ_p`-module of rank
`[L : ℚ_p] + 1`. The `[L : ℚ_p]` comes from the principal units and the `1` from the valuation.
Together with the computation of the torsion (`TauCeti.torsion_padicCompletionUnits`), this
determines `A(L)` as a `ℤ_p`-module.

The free part is exhibited by an explicit lattice of finite index. Choose a depth `i` beyond the
convergence radius of the logarithm, so that the exponential identifies the additive group
`𝓂[L] ^ i` with the deep units `U(L,i)` (`TauCeti.deepUnitExpLogEquiv`). Let `b` be a basis of
the ring of integers `𝒪[L]` over that of `ℚ_[p]`, which is `ℤ_[p]`. The classes in `A(L)` of `p`
and of the deep units `exp (p ^ i * b_k)` define a `ℤ_p`-linear map
`ℤ_p ^ ([L : ℚ_p] + 1) → A(L)`, using that the class of `exp (c • x)` is `c` times the class of
`exp x` for `c ∈ ℤ_p`. This map is injective: a relation in `A(L)` is, at each finite level, an
equation `p ^ a * exp x = y ^ (p ^ m)` in `Lˣ`, and a fixed power `y ^ M` lies in
`U(L,i) · p ^ ℤ` (`TauCeti.exists_forall_pow_eq_mem_unitFiltration_mul_zpow`), so comparing
valuations and logarithms forces the coefficients to be divisible by arbitrarily large powers of
`p`. Conversely, the same power `M` times `p ^ i` carries the class of every unit, hence all of
`A(L)`, into its image. The algebraic conclusion is
`TauCeti.nonempty_quotient_torsion_linearEquiv_of_injective_of_smul_mem_range`.

## Main results

* `TauCeti.padicCompletionUnits_quotient_torsion_linearEquiv`: for a finite extension `L` of
  `ℚ_[p]`, `A(L)` modulo its `ℤ_p`-torsion is `ℤ_p`-linearly isomorphic to
  `ℤ_p ^ ([L : ℚ_p] + 1)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.7).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.4.
-/

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FinitePadicExtension L p] {i : ℕ}

/-! ### The deep exponential, read in `A(L)` -/

section DeepExp

variable (hi : absoluteRamificationIndex L p < (p - 1) * i)

variable (p) in
/-- The exponential of a deep element, as a unit of `L`. -/
private noncomputable def deepExp (x : (𝓂[L] ^ i : Ideal 𝒪[L])) : Lˣ :=
  (deepUnitExpLogEquiv L hi).symm (Multiplicative.ofAdd x)

private theorem deepExp_add (x y : (𝓂[L] ^ i : Ideal 𝒪[L])) :
    deepExp p hi (x + y) = deepExp p hi x * deepExp p hi y := by
  simp [deepExp, ofAdd_add]

private theorem deepExp_nsmul (n : ℕ) (x : (𝓂[L] ^ i : Ideal 𝒪[L])) :
    deepExp p hi (n • x) = deepExp p hi x ^ n := by
  simp [deepExp, ofAdd_nsmul]

private theorem deepExp_injective : Function.Injective (deepExp p hi) := fun _ _ h ↦
  Multiplicative.ofAdd.injective ((deepUnitExpLogEquiv L hi).symm.injective (Subtype.ext h))

private theorem exists_deepExp_eq {w : Lˣ} (hw : w ∈ unitFiltration L i) :
    ∃ z, deepExp p hi z = w :=
  ⟨(deepUnitExpLogEquiv L hi ⟨w, hw⟩).toAdd, by simp [deepExp]⟩

private theorem normalizedValuation_deepExp (x : (𝓂[L] ^ i : Ideal 𝒪[L])) :
    normalizedValuation L (deepExp p hi x) = 1 := by
  rw [← MonoidHom.mem_ker, ker_normalizedValuation]
  exact unitFiltration_antitone (Nat.zero_le i)
    ((deepUnitExpLogEquiv L hi).symm (Multiplicative.ofAdd x)).2

variable (p) in
/-- The class in `A(L)` of the exponential of a deep element. -/
private noncomputable def deepExpClass :
    (𝓂[L] ^ i : Ideal 𝒪[L]) →+ Additive ↑(padicCompletionUnits p L) where
  toFun x := Additive.ofMul (padicCompletionUnitsOf p L (deepExp p hi x))
  map_zero' := by simp [deepExp]
  map_add' x y := by simp [deepExp_add]

private theorem deepExpClass_apply (x : (𝓂[L] ^ i : Ideal 𝒪[L])) :
    deepExpClass p hi x = Additive.ofMul (padicCompletionUnitsOf p L (deepExp p hi x)) :=
  (rfl)

/-- The class of `exp (d • x)` is `d` times the class of `exp x`, for `d ∈ 𝒪[ℚ_[p]] = ℤ_[p]`: at
level `m` both are the class of `exp x ^ (d mod p ^ m)`. -/
private theorem deepExpClass_smul (d : 𝒪[ℚ_[p]]) (x : (𝓂[L] ^ i : Ideal 𝒪[L])) :
    deepExpClass p hi (d • x) = Padic.integerRingEquiv p d • deepExpClass p hi x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  funext m
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.appr_spec m (Padic.integerRingEquiv p d))
  have hd : d = ((Padic.integerRingEquiv p d).appr m : 𝒪[ℚ_[p]]) +
      (p : 𝒪[ℚ_[p]]) ^ m * (Padic.integerRingEquiv p).symm t := by
    apply (Padic.integerRingEquiv p).injective
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast, RingEquiv.apply_symm_apply,
      mul_comm, ht]
    ring
  have hx : d • x = (Padic.integerRingEquiv p d).appr m • x +
      p ^ m • ((Padic.integerRingEquiv p).symm t • x) := by
    conv_lhs => rw [hd]
    rw [add_smul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hx, map_add, map_nsmul (deepExpClass p hi), map_nsmul (deepExpClass p hi),
    padicCompletionUnits_smul_apply]
  simp only [toMul_add, toMul_nsmul, Subgroup.coe_mul, Subgroup.coe_pow, Pi.mul_apply,
    Pi.pow_apply]
  rw [QuotientGroup.pow_eq_one_quotient_range_powMonoidHom]
  -- As in `padicCompletionUnits_add_pow_smul_apply`, `mul_one` needs the reduced type.
  exact mul_one (_ : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range)

end DeepExp

/-! ### Relations at a finite level -/

variable (p L) in
/-- The residue prime `p`, as a unit of `L`. -/
private noncomputable abbrev primeUnit : Lˣ :=
  Units.mk0 (p : L) (by
    have := FinitePadicExtension.charZero L p
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

private theorem normalizedValuation_primeUnit :
    normalizedValuation L (primeUnit p L) =
      Multiplicative.ofAdd (absoluteRamificationIndex L p : ℤ) := by
  rw [primeUnit, normalizedValuation_natCast, absoluteRamificationIndex_eq_natCastValuation]

private theorem normalizedValuation_primeUnit_ne_one :
    normalizedValuation L (primeUnit p L) ≠ 1 := by
  rw [normalizedValuation_primeUnit, Ne, ofAdd_eq_one, Nat.cast_eq_zero]
  exact (absoluteRamificationIndex_pos L p).ne'

/-- If `y ^ (p ^ m) = p ^ a * exp x` in `Lˣ` and every `u ^ M` lies in `U(L,i) · p ^ ℤ`, then
`p ^ m` divides `M * a` and `M • x` is `p ^ m` times a deep element. -/
private theorem dvd_and_exists_of_pow_eq (hi : absoluteRamificationIndex L p < (p - 1) * i)
    {M : ℕ} (hM : ∀ u : Lˣ, ∃ w ∈ unitFiltration L i, ∃ k : ℤ, u ^ M = w * primeUnit p L ^ k)
    {m a : ℕ} {x : (𝓂[L] ^ i : Ideal 𝒪[L])} {y : Lˣ}
    (hy : y ^ p ^ m = primeUnit p L ^ a * deepExp p hi x) :
    (p ^ m : ℤ) ∣ M * a ∧ ∃ z, M • x = p ^ m • z := by
  obtain ⟨w, hw, k, hk⟩ := hM y
  obtain ⟨z, rfl⟩ := exists_deepExp_eq hi hw
  -- Raise `hy` to the `M`-th power and compare with the `p ^ m`-th power of `hk`.
  have h : primeUnit p L ^ ((M * a : ℕ) : ℤ) * deepExp p hi (M • x) =
      primeUnit p L ^ (k * p ^ m) * deepExp p hi (p ^ m • z) := by
    rw [deepExp_nsmul, deepExp_nsmul, zpow_natCast, mul_comm M a, pow_mul, ← mul_pow, ← hy,
      ← pow_mul, mul_comm (p ^ m) M, pow_mul, hk, mul_pow, mul_comm, zpow_mul]
    norm_cast
  -- The deep exponentials are units, so the powers of `p` have the same valuation.
  have hval := congrArg (fun u ↦ (normalizedValuation L u).toAdd) h
  simp only [map_mul, map_zpow, normalizedValuation_deepExp, normalizedValuation_primeUnit,
    toAdd_mul, toAdd_zpow, toAdd_ofAdd, toAdd_one, add_zero, smul_eq_mul] at hval
  have hMa : ((M * a : ℕ) : ℤ) = k * p ^ m :=
    mul_right_cancel₀ (by exact_mod_cast (absoluteRamificationIndex_pos L p).ne') hval
  refine ⟨⟨k, by rw [← Nat.cast_mul, hMa, mul_comm]⟩, z, deepExp_injective hi ?_⟩
  rwa [hMa, mul_right_inj] at h

/-! ### The lattice map -/

variable (p L) in
/-- A basis of `𝒪[L]` over the ring of integers of `ℚ_[p]`, indexed by `Fin [L : ℚ_[p]]`. -/
private noncomputable abbrev integerBasis :
    Module.Basis (Fin (Module.finrank ℚ_[p] L)) 𝒪[ℚ_[p]] 𝒪[L] :=
  -- Instance search for `Nontrivial 𝒪[ℚ_[p]]` is slow; the domain structure provides it.
  letI : StrongRankCondition 𝒪[ℚ_[p]] := @commRing_strongRankCondition _ _ IsDomain.toNontrivial
  Module.finBasisOfFinrankEq 𝒪[ℚ_[p]] 𝒪[L] (finrank_integerRing ℚ_[p] L)

/-- The deep lattice vectors `p ^ i * b_k`. -/
private noncomputable def deepLatticeVector (i : ℕ) (k : Fin (Module.finrank ℚ_[p] L)) :
    (𝓂[L] ^ i : Ideal 𝒪[L]) :=
  ⟨(p : 𝒪[L]) ^ i * integerBasis p L k,
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (natCast_mem_maximalIdeal L p) i)⟩

private theorem coe_deepLatticeVector (k : Fin (Module.finrank ℚ_[p] L)) :
    ((deepLatticeVector i k : (𝓂[L] ^ i : Ideal 𝒪[L])) : 𝒪[L]) =
      (p : 𝒪[L]) ^ i * integerBasis p L k :=
  (rfl)

private theorem coe_sum_smul_deepLatticeVector (d : Fin (Module.finrank ℚ_[p] L) → 𝒪[ℚ_[p]]) :
    (((∑ k, d k • deepLatticeVector i k : (𝓂[L] ^ i : Ideal 𝒪[L])) : 𝒪[L])) =
      (p : 𝒪[L]) ^ i * ∑ k, d k • integerBasis p L k := by
  simp [coe_deepLatticeVector, Finset.mul_sum]

private theorem integerBasis_repr_deepLatticeVector (k : Fin (Module.finrank ℚ_[p] L)) :
    (integerBasis p L).repr (deepLatticeVector i k : 𝒪[L]) =
      Finsupp.single k ((p : 𝒪[ℚ_[p]]) ^ i) := by
  have : ((deepLatticeVector i k : (𝓂[L] ^ i : Ideal 𝒪[L])) : 𝒪[L]) =
      ((p : 𝒪[ℚ_[p]]) ^ i) • integerBasis p L k := by
    rw [Algebra.smul_def, map_pow, map_natCast, coe_deepLatticeVector]
  rw [this, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

section LatticeMap

variable (hi : absoluteRamificationIndex L p < (p - 1) * i)

variable (p L) in
/-- The `ℤ_p`-linear map `ℤ_p ^ ([L : ℚ_p] + 1) → A(L)` sending the basis vectors to the classes
of `p` and of the deep units `exp (p ^ i * b_k)`. -/
private noncomputable def latticeMap :
    (Fin (Module.finrank ℚ_[p] L + 1) → ℤ_[p]) →ₗ[ℤ_[p]] Additive ↑(padicCompletionUnits p L) :=
  Fintype.linearCombination ℤ_[p]
    (Fin.cons (Additive.ofMul (padicCompletionUnitsOf p L (primeUnit p L)))
      fun k ↦ deepExpClass p hi (deepLatticeVector i k))

private theorem latticeMap_natCast (N : Fin (Module.finrank ℚ_[p] L + 1) → ℕ) :
    latticeMap p L hi (fun j ↦ (N j : ℤ_[p])) =
      Additive.ofMul (padicCompletionUnitsOf p L (primeUnit p L ^ N 0 *
        deepExp p hi (∑ k, N k.succ • deepLatticeVector i k))) := by
  rw [latticeMap, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, padicCompletionUnits_natCast_smul]
  have h : ∑ k, N k.succ • deepExpClass p hi (deepLatticeVector i k) =
      deepExpClass p hi (∑ k, N k.succ • deepLatticeVector i k) := by
    simp [map_sum, map_nsmul]
  rw [h, deepExpClass_apply, map_mul, map_pow, ofMul_mul, ofMul_pow]

/-- At level `m`, the image of `c` is the class of a unit built from the approximations
`(c j).appr m`. -/
private theorem latticeMap_apply_level (c : Fin (Module.finrank ℚ_[p] L + 1) → ℤ_[p]) (m : ℕ) :
    (latticeMap p L hi c).toMul.1 m =
      (QuotientGroup.mk (primeUnit p L ^ (c 0).appr m *
        deepExp p hi (∑ k, (c k.succ).appr m • deepLatticeVector i k)) :
          Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) := by
  choose t ht using fun j ↦ Ideal.mem_span_singleton'.mp (PadicInt.appr_spec m (c j))
  have hc : c = (fun j ↦ ((c j).appr m : ℤ_[p])) + (p : ℤ_[p]) ^ m • t := by
    funext j
    simp [mul_comm, ht j]
  conv_lhs => rw [hc, map_add, map_smul, padicCompletionUnits_add_pow_smul_apply,
    latticeMap_natCast]
  simp

private theorem latticeMap_injective : Function.Injective (latticeMap p L hi) := by
  obtain ⟨M, hM0, hM⟩ := exists_forall_pow_eq_mem_unitFiltration_mul_zpow i
    (normalizedValuation_primeUnit_ne_one (p := p) (L := L))
  -- A `p`-adic integer `c` with `r * c ≡ 0` modulo every `p ^ m`, read on the approximations
  -- `c.appr m`, vanishes when `r ≠ 0` (Krull's intersection theorem in `ℤ_[p]`).
  have hzero {r : ℕ} (hr : r ≠ 0) {c : ℤ_[p]}
      (h : ∀ m, ((r * c.appr m : ℕ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ m}) : c = 0 := by
    have hrc : (r : ℤ_[p]) * c ∈ ⨅ m, Ideal.span {(p : ℤ_[p])} ^ m :=
      Submodule.mem_iInf _ |>.mpr fun m ↦ by
        rw [Ideal.span_singleton_pow, ← sub_add_cancel c (c.appr m), mul_add]
        exact add_mem (Ideal.mul_mem_left _ _ (PadicInt.appr_spec m c)) (by exact_mod_cast h m)
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ (by
      rw [← PadicInt.maximalIdeal_eq_span_p]
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top), Ideal.mem_bot] at hrc
    exact (mul_eq_zero.mp hrc).resolve_left (Nat.cast_ne_zero.mpr hr)
  refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_
  -- At every level `m`, the relation `latticeMap c = 0` is an equation between units of `L`.
  have key (m : ℕ) : (p ^ m : ℤ) ∣ M * (c 0).appr m ∧
      ∃ z, M • (∑ k, (c k.succ).appr m • deepLatticeVector i k) = p ^ m • z := by
    have h := latticeMap_apply_level hi c m
    rw [hc, toMul_zero, OneMemClass.coe_one, Pi.one_apply, eq_comm,
      QuotientGroup.eq_one_iff] at h
    obtain ⟨y, hy⟩ := h
    exact dvd_and_exists_of_pow_eq hi hM hy
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · refine hzero hM0 fun m ↦ ?_
    obtain ⟨q, hq⟩ := (key m).1
    exact Ideal.mem_span_singleton.mpr ⟨q, by exact_mod_cast hq⟩
  · refine hzero (r := M * p ^ i)
      (mul_ne_zero hM0 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)) fun m ↦ ?_
    obtain ⟨z, hz⟩ := (key m).2
    -- Read the `k`-th coordinate of `hz` in the basis `b`.
    have h := congrArg (fun x : (𝓂[L] ^ i : Ideal 𝒪[L]) ↦ (integerBasis p L).repr x k) hz
    simp only [Submodule.coe_smul_of_tower, Submodule.coe_sum, map_nsmul, map_sum,
      integerBasis_repr_deepLatticeVector, Finsupp.smul_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    simp only [nsmul_eq_mul] at h
    have h' := congrArg (Padic.integerRingEquiv p) h
    simp only [map_mul, map_natCast, map_pow] at h'
    refine Ideal.mem_span_singleton'.mpr
      ⟨Padic.integerRingEquiv p ((integerBasis p L).repr z k), ?_⟩
    push_cast at h' ⊢
    rw [mul_comm, ← h']
    ring

private theorem exists_smul_mem_range_latticeMap :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ a, (M : ℤ_[p]) • a ∈ LinearMap.range (latticeMap p L hi) := by
  obtain ⟨M, hM0, hM⟩ := exists_forall_pow_eq_mem_unitFiltration_mul_zpow i
    (normalizedValuation_primeUnit_ne_one (p := p) (L := L))
  refine ⟨M * p ^ i, mul_ne_zero hM0 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), fun a ↦ ?_⟩
  have := finiteIndex_range_powMonoidHom (primeUnit p L).ne_zero
  -- The classes of units span `A(L)`, so it suffices to treat the class of a unit `u`.
  suffices h : Submodule.span ℤ_[p]
      (Set.range fun u : Lˣ ↦ Additive.ofMul (padicCompletionUnitsOf p L u)) ≤
      (LinearMap.range (latticeMap p L hi)).comap (((M * p ^ i : ℕ) : ℤ_[p]) • LinearMap.id) by
    rw [span_range_padicCompletionUnitsOf_eq_top] at h
    exact h Submodule.mem_top
  rw [Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  -- Write `u ^ M = exp z * p ^ k`; then `u ^ (M * p ^ i) = exp (p ^ i • z) * p ^ (k * p ^ i)`,
  -- and `p ^ i • z` is a `𝒪[ℚ_[p]]`-combination of the deep lattice vectors.
  obtain ⟨w, hw, k, hk⟩ := hM u
  obtain ⟨z, rfl⟩ := exists_deepExp_eq hi hw
  have hz : p ^ i • z = ∑ k, (integerBasis p L).repr z k • deepLatticeVector i k := by
    apply Subtype.ext
    rw [coe_sum_smul_deepLatticeVector, (integerBasis p L).sum_repr,
      Submodule.coe_smul_of_tower, nsmul_eq_mul, Nat.cast_pow]
  refine ⟨Fin.cons ((k * p ^ i : ℤ) : ℤ_[p])
    fun j ↦ Padic.integerRingEquiv p ((integerBasis p L).repr z j), ?_⟩
  rw [latticeMap, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, ← deepExpClass_smul, ← map_sum, ← hz,
    LinearMap.smul_apply, LinearMap.id_apply, padicCompletionUnits_natCast_smul]
  have h : (M * p ^ i) • Additive.ofMul (padicCompletionUnitsOf p L u) =
      Additive.ofMul (padicCompletionUnitsOf p L (deepExp p hi (p ^ i • z))) +
        (k * p ^ i : ℤ) • Additive.ofMul (padicCompletionUnitsOf p L (primeUnit p L)) := by
    rw [← ofMul_pow, ← map_pow, pow_mul, hk, deepExp_nsmul, ← ofMul_zpow, ← map_zpow,
      ← ofMul_mul, ← map_mul, mul_pow, zpow_mul]
    norm_cast
  rw [h, Int.cast_smul_eq_zsmul, add_comm, deepExpClass_apply]

end LatticeMap

variable (p L) in
private theorem nonempty_quotient_torsion_linearEquiv_of_finitePadicExtension :
    Nonempty ((Additive ↑(padicCompletionUnits p L) ⧸
        Submodule.torsion ℤ_[p] (Additive ↑(padicCompletionUnits p L))) ≃ₗ[ℤ_[p]]
      (Fin (Module.finrank ℚ_[p] L + 1) → ℤ_[p])) := by
  have hi : absoluteRamificationIndex L p < (p - 1) * (absoluteRamificationIndex L p + 1) :=
    (Nat.lt_succ_self _).trans_le
      (Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
  obtain ⟨M, hM0, hM⟩ := exists_smul_mem_range_latticeMap hi
  exact nonempty_quotient_torsion_linearEquiv_of_injective_of_smul_mem_range
    (latticeMap_injective hi) (Nat.cast_ne_zero.mpr hM0) hM

variable (p) in
/-- **The free quotient of `A(L)`.** For a finite extension `L` of `ℚ_[p]`, the `p`-adic
completion `A(L) = lim_m Lˣ/(Lˣ)^(p^m)` of its multiplicative group is, modulo its `ℤ_p`-torsion,
a free `ℤ_p`-module of rank `[L : ℚ_p] + 1`. -/
public theorem padicCompletionUnits_quotient_torsion_linearEquiv (L : Type*) [Field L]
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] :
    Nonempty ((Additive ↑(padicCompletionUnits p L) ⧸
        Submodule.torsion ℤ_[p] (Additive ↑(padicCompletionUnits p L))) ≃ₗ[ℤ_[p]]
      (Fin (Module.finrank ℚ_[p] L + 1) → ℤ_[p])) := by
  -- Give `L` the local-field structure extending that of `ℚ_[p]`; the statement does not see it.
  let _ := finiteExtensionValuativeRel ℚ_[p] L
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_valuativeExtension ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  exact nonempty_quotient_torsion_linearEquiv_of_finitePadicExtension p L

end TauCeti
