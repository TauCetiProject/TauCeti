/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Comparison
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic
import TauCeti.FieldTheory.FunctionField.Differential.LocalComponent
import TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Residue
import TauCeti.FieldTheory.FunctionField.Different.Divisor
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Trace

/-!
# The local components of `dt` at a zero of `t` are residues

Let `F / k` be an algebraic function field and `t ∈ F` a separating element, and let `dt` be the
Weil differential `TauCeti.weilDifferentialOfSeparating`, the cotrace to `F` of the canonical
differential `η` of `k(t)`. At a rational place `P` of `F` at which `t` is a prime element,
`ord_P t = 1`, the local component of `dt` is the residue in `t`:

`(dt)_P (u) = res_{P,t} (u)` for every `u ∈ F`.

This is Stichtenoth's Theorem 4.3.2(d), `(z · δ(x))_P (u) = res_P (u z dx)`, for `x = t` a prime
element at `P` and `z = 1`. It identifies the abstract local components of Weil differentials with
the classical residues of Laurent expansions.

The proof transports the rational-function-field case
(`TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C`) along the
cotrace. The place `P` lies over the zero `P₀` of `t` in `k(t)` with `e(P ∣ P₀) = f(P ∣ P₀) = 1`,
and `dt` is regular at every place over `P₀` because the different is effective. Weak
approximation moves `u`, without changing its principal part at `P`, to a function that is regular
at the other places over `P₀`; for such a function the local components of the cotrace over `P₀`
(`TauCeti.trace_finsum_repartitionDualComponent_weilDifferentialCotrace`) give
`(dt)_P (u) = η_{P₀} (Tr u) = res_{P₀,t} (Tr u)`. Finally the trace is the identity near `P`
(`TauCeti.Place.algebraMap_trace_sub_mem_filtration`), so `Tr u` and `u` have the same residue at
`P`.

## Main results

* `TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential`: for a finite
  separable extension `F` of `k(t)`, the local component of the cotrace of `η` at a rational place
  where `t` is a prime element is `res_{P,t}`.
* `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`: `(dt)_P = res_{P,t}`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2(d).
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-! ### The place below a rational place at which `t` is a prime element -/

section Below

variable {P : Place k F} (hP : P.degree = 1) (ht : P.ord (algebraMap (RatFunc k) F RatFunc.X) = 1)
include ht

/-- A place at which `t` is a prime element is unramified over `k(t)`, and `t` is a prime element
at the place below. -/
private theorem ramificationIdx_eq_one_and_ord_X_eq_one :
    ramificationIdx (RatFunc k) P = 1 ∧ (P.restrict k (RatFunc k)).ord RatFunc.X = 1 := by
  have hord := ord_algebraMap_restrict k (RatFunc k) P RatFunc.X
  rw [ht] at hord
  have he : ramificationIdx (RatFunc k) P = 1 := by
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) hord.symm
  rw [he, Nat.cast_one, one_mul] at hord
  exact ⟨he, hord.symm⟩

include hP

/-- A rational place at which `t` is a prime element lies over the zero `P₀` of `t`. -/
private theorem restrict_eq_adicOfIrreducible_X_sub_C_zero :
    P.restrict k (RatFunc k) = adicOfIrreducible (Polynomial.irreducible_X_sub_C (0 : k)) := by
  have hX₀ := (ramificationIdx_eq_one_and_ord_X_eq_one ht).2
  rcases eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C (Nat.eq_one_of_mul_eq_one_right
    (hP ▸ degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P).symm) with h | ⟨a, h⟩
  · rw [h, ord_infty, RatFunc.intDegree_X] at hX₀
    omega
  · -- `a = X - (X - a)` would vanish at the place below, so the constant `a` is zero.
    obtain rfl : a = 0 := by
      by_contra ha
      have h1 := (adicOfIrreducible (Polynomial.irreducible_X_sub_C a)).mem_filtration_ord
        (RatFunc.X - RatFunc.C a)
      rw [ord_adicOfIrreducible_X_sub_C_self, ← h] at h1
      have h2 := (P.restrict k (RatFunc k)).mem_filtration_ord RatFunc.X
      rw [hX₀] at h2
      have h3 := sub_mem h2 h1
      rw [sub_sub_cancel, ← RatFunc.algebraMap_eq_C,
        (P.restrict k (RatFunc k)).mem_filtration_iff_le_ord ((map_ne_zero _).mpr ha),
        ord_algebraMap] at h3
      omega
    exact h

/-- Residues of rational functions at the zero of `X`, in `X`, are residues at `P` in `t`. -/
private theorem residue_adicOfIrreducible_X_sub_C_zero (y : RatFunc k) :
    (adicOfIrreducible (Polynomial.irreducible_X_sub_C (0 : k))).residue
        (degree_adicOfIrreducible_X_sub_C 0) (ord_adicOfIrreducible_X_sub_C_self 0) y =
      P.residue hP ht (algebraMap (RatFunc k) F y) := by
  have hP₀ := restrict_eq_adicOfIrreducible_X_sub_C_zero hP ht
  -- Both sides are `k`-linear in `y`, vanish on the functions regular at `P₀`, and agree on the
  -- powers of `X`, whose image in `F` is `t`.
  refine LinearMap.congr_fun (g := P.residue hP ht ∘ₗ
    (IsScalarTower.toAlgHom k (RatFunc k) F).toLinearMap) ?_ y
  refine (adicOfIrreducible (Polynomial.irreducible_X_sub_C (0 : k))).linearMap_ext_zpow
    (degree_adicOfIrreducible_X_sub_C 0) (ord_adicOfIrreducible_X_sub_C_self 0) (m := 0)
    (fun y hy ↦ ?_) (fun j _ ↦ ?_)
  · rw [mem_filtration_zero_iff] at hy
    have hy₀ : y ∈ (P.restrict k (RatFunc k)).integers := hP₀ ▸ hy
    rw [residue_eq_zero_of_mem_integers _ _ _ hy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', residue_eq_zero_of_mem_integers _ _ _
        ((mem_integers_restrict_iff k (RatFunc k) P y).mp hy₀)]
  · have hXC : (RatFunc.X - RatFunc.C (0 : k) : RatFunc k) = RatFunc.X := by simp
    rw [residue_zpow_uniformizer, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', map_zpow₀, hXC, residue_zpow_uniformizer]

/-- **Moving a function off the other places over `P₀`**: every `u` agrees at `P`, modulo
functions regular there, with a function `v` that is regular at the other places over `P₀` and
whose trace to `k(t)` agrees with it at `P` modulo regular functions. -/
private theorem exists_sub_mem_integers_forall_mem_integers_and_trace_sub_mem_integers
    [Algebra.IsSeparable (RatFunc k) F] (hF : IsFunctionField k F) (u : F) :
    ∃ v : F, v - u ∈ P.integers ∧
      (∀ Q : Place k F, Q.restrict k (RatFunc k) = P.restrict k (RatFunc k) → Q ≠ P →
        v ∈ Q.integers) ∧
      algebraMap (RatFunc k) F (Algebra.trace (RatFunc k) F v) - v ∈ P.integers := by
  classical
  obtain ⟨he, hX₀⟩ := ramificationIdx_eq_one_and_ord_X_eq_one ht
  set P₀ := P.restrict k (RatFunc k)
  set t := algebraMap (RatFunc k) F RatFunc.X with htdef
  have ht0 : t ≠ 0 := by
    rintro h
    rw [h, ord_zero] at ht
    omega
  -- `t` has order `e(Q ∣ P₀)` at every place `Q` over `P₀`.
  have htpow (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P₀) (n : ℤ) :
      t ^ n ∈ Q.filtration (ramificationIdx (RatFunc k) Q * n) := by
    have := Q.mem_filtration_ord (t ^ n)
    rwa [Q.ord_zpow, htdef, ord_algebraMap_restrict k (RatFunc k) Q, hQ, hX₀, mul_one,
      mul_comm] at this
  -- By weak approximation, `w ≡ 1` at `P` and `w ≡ 0` at the other places over `P₀`, to orders
  -- making `(w - 1) u` regular at `P` and `w u` small at the other places over `P₀`.
  set r := (-P.ord u).toNat
  have hfin := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k) P₀).to_subtype
  obtain ⟨w, hw⟩ := exists_forall_ord_sub_eq
    (P := fun Q : {Q : Place k F | Q.restrict k (RatFunc k) = P₀} ↦ (Q : Place k F))
    Subtype.val_injective (fun Q ↦ if (Q : Place k F) = P then 1 else 0)
    (fun Q ↦ if (Q : Place k F) = P then (r : ℤ) else
      ramificationIdx (RatFunc k) (Q : Place k F) * r + (-(Q : Place k F).ord u).toNat)
  have hw1 : w - 1 ∈ P.filtration r := by
    have := P.mem_filtration_ord (w - 1)
    have h := hw ⟨P, rfl⟩
    simp only [ite_true] at h
    rwa [h] at this
  have hw0 (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P₀) (hne : Q ≠ P) :
      w ∈ Q.filtration (ramificationIdx (RatFunc k) Q * r + (-Q.ord u).toNat) := by
    have := Q.mem_filtration_ord w
    have h := hw ⟨Q, hQ⟩
    simp only [hne, ite_false, sub_zero] at h
    rwa [h] at this
  have hu := P.mem_filtration_ord u
  have hwu (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P₀) (hne : Q ≠ P) :
      w * u ∈ Q.filtration (ramificationIdx (RatFunc k) Q * r) :=
    Q.filtration_antitone (by omega) (Q.mul_mem_filtration (hw0 Q hQ hne) (Q.mem_filtration_ord u))
  refine ⟨w * u, ?_, fun Q hQ hne ↦ Q.mem_filtration_zero_iff.mp
    (Q.filtration_antitone (by positivity) (hwu Q hQ hne)), ?_⟩
  · rw [← sub_one_mul, ← mem_filtration_zero_iff]
    exact P.filtration_antitone (by omega) (P.mul_mem_filtration hw1 hu)
  -- The trace is the identity near `P`, applied to `t ^ r * w * u`.
  have hwP : w ∈ P.filtration 0 := by
    simpa using add_mem (P.filtration_antitone (by omega) hw1)
      (P.mem_filtration_zero_iff.mpr P.integers.one_mem)
  have hz : t ^ (r : ℤ) * (w * u) ∈ P.integers := by
    rw [← mem_filtration_zero_iff]
    refine P.filtration_antitone ?_ (P.mul_mem_filtration (htpow P rfl r)
      (P.mul_mem_filtration hwP hu))
    rw [he]
    omega
  have hzQ (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P₀) (hne : Q ≠ P) :
      t ^ (r : ℤ) * (w * u) ∈ Q.filtration (ramificationIdx (RatFunc k) Q * r) := by
    have h0 : w * u ∈ Q.filtration 0 := Q.filtration_antitone (by positivity) (hwu Q hQ hne)
    have := Q.mul_mem_filtration (htpow Q hQ r) h0
    rwa [add_zero] at this
  have hf : relativeDegree k (RatFunc k) P = 1 := Nat.eq_one_of_mul_eq_one_left
    (hP ▸ degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P).symm
  have htr := algebraMap_trace_sub_mem_filtration k (RatFunc k) P hF he hf r hz hzQ
  -- `Tr (t ^ r * w u) = X ^ r * Tr (w u)`, so dividing by `t ^ r` gives the claim.
  rw [htdef, ← map_zpow₀, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, map_mul,
    Algebra.smul_def, ← mul_sub, map_zpow₀, ← htdef] at htr
  rw [← mem_filtration_zero_iff]
  have := P.mul_mem_filtration (htpow P rfl (-r)) htr
  rwa [← mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, one_mul, he, Nat.cast_one,
    one_mul, neg_add_cancel] at this

end Below

variable [Algebra.IsSeparable (RatFunc k) F]

/-- **The local component of `dt` at a zero of `t` is the residue in `t`** (Stichtenoth,
Theorem 4.3.2(d)): for a finite separable extension `F` of `k(t)` and a rational place `P` of `F`
at which the image of `t` is a prime element, the local component at `P` of the cotrace of the
canonical differential `η = dt` of `k(t)` is `res_{P,t}`. -/
theorem repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential
    (hF : IsFunctionField k F) {P : Place k F} (hP : P.degree = 1)
    (ht : P.ord (algebraMap (RatFunc k) F RatFunc.X) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) P u =
      P.residue hP ht u := by
  classical
  set η : ↥(weilDifferentialSpace k (RatFunc k)) :=
    ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ with hη
  set ω := weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF η with hω
  have hP₀ := restrict_eq_adicOfIrreducible_X_sub_C_zero hP ht
  -- `dt` is regular at every place over `P₀`, since the different is effective.
  have hkill (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)) {v : F}
      (hv : v ∈ Q.integers) : repartitionDualComponent (ω : Module.Dual k _) Q v = 0 := by
    refine repartitionDualComponent_apply_eq_zero_of_le
      (weilDifferentialCotrace_mem_weilDifferentialFiltration (IsFunctionField.ratFunc k) hF η
        (isGreatest_ratFuncWeilDifferential k).1) Q ?_
    simp only [WeilDivisor.coeff_add, Divisor.coeff_conorm, WeilDivisor.coeff_zsmul, hQ, hP₀,
      WeilDivisor.coeff_ofPoint_of_ne (adicOfIrreducible_ne_infty _), mul_zero, zero_add,
      Divisor.coeff_different]
    exact (Q.mem_integers_iff.mp hv).trans (by simp)
  obtain ⟨v, hvu, hvQ, hvtr⟩ :=
    exists_sub_mem_integers_forall_mem_integers_and_trace_sub_mem_integers hP ht hF u
  -- Over `P₀`, only `P` contributes to the local components of `dt` at `v`.
  have hsum : (∑ᶠ (Q : Place k F) (_ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)),
      repartitionDualComponent (ω : Module.Dual k _) Q v) =
        repartitionDualComponent (ω : Module.Dual k _) P v := by
    rw [finsum_eq_single _ P fun Q hne ↦ ?_]
    · simp
    · by_cases hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)
      · simp [hQ, hkill Q hQ (hvQ Q hQ hne)]
      · simp [hQ]
  have hfib := trace_finsum_repartitionDualComponent_weilDifferentialCotrace
    (IsFunctionField.ratFunc k) hF η (P.restrict k (RatFunc k)) v
  rw [← hω, Algebra.trace_self_apply, hsum, hη, hP₀,
    repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C,
    residue_adicOfIrreducible_X_sub_C_zero hP ht] at hfib
  calc repartitionDualComponent (ω : Module.Dual k _) P u
      = repartitionDualComponent (ω : Module.Dual k _) P v := by
        rw [← sub_eq_zero, ← map_sub, hkill P rfl (by simpa using neg_mem hvu)]
    _ = P.residue hP ht v := hfib.trans (residue_eq_of_sub_mem_integers _ _ _ hvtr)
    _ = P.residue hP ht u := residue_eq_of_sub_mem_integers _ _ _ hvu

end RatFunc

/-- **The local component of `dt` at a zero of `t` is the residue in `t`** (Stichtenoth,
Theorem 4.3.2(d)): for a separating element `t` of `F / k` and a rational place `P` at which `t` is
a prime element, the Weil differential `dt` has local component `(dt)_P = res_{P,t}`. -/
theorem repartitionDualComponent_weilDifferentialOfSeparating (hF : IsFunctionField k F) {t : F}
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] {P : Place k F} (hP : P.degree = 1)
    (ht : P.ord t = 1) (u : F) :
    repartitionDualComponent (weilDifferentialOfSeparating hF htr :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.residue hP ht u := by
  let _ := ratFuncAlgebraOfTranscendental htr
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental htr
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental htr
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X htr
  -- The residue only depends on the uniformizer, not on the proof that it is one.
  have hres {s : F} (hs : s = t) (hs₁ : P.ord s = 1) : P.residue hP hs₁ = P.residue hP ht := by
    subst hs
    rfl
  rw [weilDifferentialOfSeparating_def,
    repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential hF hP (hX ▸ ht),
    hres hX]

end TauCeti
