/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Comparison
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.CoefficientField
import TauCeti.FieldTheory.FunctionField.Differential.LocalComponent
import TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Residue
import TauCeti.FieldTheory.FunctionField.Different.Divisor
import TauCeti.FieldTheory.FunctionField.Place.Extension.Trace

/-!
# The local components of `dt` at a zero of `t - a` are residues

Let `F / k` be an algebraic function field and `t ∈ F` a separating element, and let `dt` be the
Weil differential `TauCeti.weilDifferentialOfSeparating`, the cotrace to `F` of the canonical
differential `η` of `k(t)`. At a place `P` of `F` whose residue field `F_P` is separable over `k`
and at which `t - a` is a prime element for some constant `a ∈ k`, `ord_P (t - a) = 1`, the local
component of `dt` is the trace residue in `t - a`:

`(dt)_P (u) = Tr_{F_P/k} (res_{P,t-a} (u))` for every `u ∈ F`.

At a rational place the trace is the identity and this is the residue `res_{P,t-a} (u)`. This is
Stichtenoth's Theorem 4.3.2(d), `(z · δ(x))_P (u) = res_P (u z dx)`, in its form for places of
arbitrary degree (Remark 4.3.7(d)), for `x = t` with `t - a` a prime element at `P` and `z = 1`.
It identifies the abstract local components of Weil differentials with the classical residues of
Laurent expansions.

The proof transports the rational-function-field case
(`TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C`) along the
cotrace. The place `P` lies over the zero `P_a` of `t - a` in `k(t)` with `e(P ∣ P_a) = 1`, and
`dt` is regular at every place over `P_a` because the different is effective. Weak approximation
moves `u`, without changing its principal part at `P`, to a function that is regular at the other
places over `P_a`; for such a function the local components of the cotrace over `P_a`
(`TauCeti.trace_finsum_repartitionDualComponent_weilDifferentialCotrace`) give
`(dt)_P (u) = η_{P_a} (Tr u) = res_{P_a,t-a} (Tr u)`. Finally the residue of the trace is the
trace residue (`TauCeti.Place.residue_trace`).

## Main results

* `repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue`:
  for a finite separable extension `F` of `k(t)`, the local component of the cotrace of `η` at a
  place with separable residue field where `t - a` is a prime element is `Tr ∘ res_{P,t-a}`.
* `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue`:
  `(dt)_P = Tr ∘ res_{P,t-a}`.
* `TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential` and
  `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`: at a rational place,
  `(dt)_P = res_{P,t-a}`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2(d) and Remark 4.3.7(d).
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-! ### The place below a place at which `t - a` is a prime element -/

section Below

variable {P : Place k F} {a : k}
  (ht : P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1)
include ht

/-- A place at which `t - a` is a prime element is unramified over `k(t)`, and `t - a` is a prime
element at the place below. -/
private theorem ramificationIdx_eq_one_and_ord_X_sub_C_eq_one :
    ramificationIdx (RatFunc k) P = 1 ∧
      (P.restrict k (RatFunc k)).ord (RatFunc.X - RatFunc.C a) = 1 := by
  have hord := ord_algebraMap_restrict k (RatFunc k) P (RatFunc.X - RatFunc.C a)
  rw [ht] at hord
  have he : ramificationIdx (RatFunc k) P = 1 := by
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) hord.symm
  rw [he, Nat.cast_one, one_mul] at hord
  exact ⟨he, hord.symm⟩

/-- A place at which `t - a` is a prime element lies over the zero `P_a` of `t - a`. -/
private theorem restrict_eq_adicOfIrreducible_X_sub_C :
    P.restrict k (RatFunc k) = adicOfIrreducible (Polynomial.irreducible_X_sub_C a) := by
  have hX₀ := (ramificationIdx_eq_one_and_ord_X_sub_C_eq_one ht).2
  rcases eq_infty_or_exists_eq_adicOfIrreducible (P.restrict k (RatFunc k)) with h | ⟨q, hq, h⟩
  · -- `t - a` has a pole at infinity.
    rw [h, ord_infty, ← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub,
      RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C] at hX₀
    omega
  · -- `t - a` is a unit at the place of `q` unless `q` is associated to `X - a`.
    rw [h] at hX₀ ⊢
    by_contra hne
    rw [ord_adicOfIrreducible_X_sub_C_of_not_associated hq fun hassoc ↦
      hne ((adicOfIrreducible_eq_adicOfIrreducible_iff hq _).mpr hassoc)] at hX₀
    omega

omit ht in
/-- **Moving a function off the other places over `P₀`**: every `u` agrees at `P`, modulo
functions regular there, with a function `v` that is regular at the other places over `P₀`. -/
private theorem exists_sub_mem_integers_forall_mem_integers (u : F) :
    ∃ v : F, v - u ∈ P.integers ∧
      ∀ Q : Place k F, Q.restrict k (RatFunc k) = P.restrict k (RatFunc k) → Q ≠ P →
        v ∈ Q.integers := by
  classical
  have hfin := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k)
    (P.restrict k (RatFunc k))).to_subtype
  -- By weak approximation, `v ≡ u` at `P` and `v ≡ 0` at the other places over `P₀`.
  obtain ⟨v, hv⟩ := exists_forall_ord_sub_eq
    (P := fun Q : {Q : Place k F | Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)} ↦
      (Q : Place k F))
    Subtype.val_injective (fun Q ↦ if (Q : Place k F) = P then u else 0) (fun _ ↦ 0)
  have hvQ (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)) :
      v - (if Q = P then u else 0) ∈ Q.integers := by
    rw [mem_integers_iff_ord_nonneg, hv ⟨Q, hQ⟩]
  exact ⟨v, by simpa using hvQ P rfl, fun Q hQ hne ↦ by simpa [hne] using hvQ Q hQ⟩

end Below

variable [Algebra.IsSeparable (RatFunc k) F]

/-- **The local component of `dt` at a zero of `t - a` is the trace residue in `t - a`**
(Stichtenoth, Theorem 4.3.2(d) and Remark 4.3.7(d)): for a finite separable extension `F` of
`k(t)` and a place `P` of `F` with residue field separable over `k`, at which the image of `t - a`
is a prime element, the local component at `P` of the cotrace of the canonical differential
`η = dt` of `k(t)` is `Tr_{F_P/k} ∘ res_{P,t-a}`. -/
theorem repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue
    (hF : IsFunctionField k F) {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {a : k}
    (ht : P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) P u =
      P.traceResidue ht u := by
  classical
  set η : ↥(weilDifferentialSpace k (RatFunc k)) :=
    ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ with hη
  set ω := weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF η with hω
  have hP₀ := restrict_eq_adicOfIrreducible_X_sub_C ht
  -- `dt` is regular at every place over `P_a`, since the different is effective.
  have hkill (Q : Place k F) (hQ : Q.restrict k (RatFunc k) = P.restrict k (RatFunc k)) {v : F}
      (hv : v ∈ Q.integers) : repartitionDualComponent (ω : Module.Dual k _) Q v = 0 := by
    refine repartitionDualComponent_apply_eq_zero_of_le
      (weilDifferentialCotrace_mem_weilDifferentialFiltration (IsFunctionField.ratFunc k) hF η
        (isGreatest_ratFuncWeilDifferential k).1) Q ?_
    simp only [WeilDivisor.coeff_add, Divisor.coeff_conorm, WeilDivisor.coeff_zsmul, hQ, hP₀,
      WeilDivisor.coeff_ofPoint_of_ne (adicOfIrreducible_ne_infty _), mul_zero, zero_add,
      Divisor.coeff_different]
    exact (Q.mem_integers_iff.mp hv).trans (by simp)
  obtain ⟨v, hvu, hvQ⟩ := exists_sub_mem_integers_forall_mem_integers (P := P) u
  -- Over `P_a`, only `P` contributes to the local components of `dt` at `v`.
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
    residue_trace P hP₀ (ord_adicOfIrreducible_X_sub_C_self a) ht hF
      (degree_adicOfIrreducible_X_sub_C a) fun Q hQ hne ↦ hvQ Q (hQ.trans hP₀.symm) hne] at hfib
  calc repartitionDualComponent (ω : Module.Dual k _) P u
      = repartitionDualComponent (ω : Module.Dual k _) P v := by
        rw [← sub_eq_zero, ← map_sub, hkill P rfl (by simpa using neg_mem hvu)]
    _ = P.traceResidue ht v := hfib
    _ = P.traceResidue ht u := by
        rw [traceResidue_apply, traceResidue_apply,
          P.residueResidueField_eq_of_sub_mem_integers ht hvu]

/-- **The local component of `dt` at a zero of `t - a` is the residue in `t - a`** (Stichtenoth,
Theorem 4.3.2(d)): for a finite separable extension `F` of `k(t)` and a rational place `P` of `F`
at which the image of `t - a` is a prime element, the local component at `P` of the cotrace of the
canonical differential `η = dt` of `k(t)` is `res_{P,t-a}`. -/
theorem repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential
    (hF : IsFunctionField k F) {P : Place k F} (hP : P.degree = 1) {a : k}
    (ht : P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) P u =
      P.residue hP ht u := by
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue hF
    ht, P.traceResidue_eq_residue ht hP]

end RatFunc

/-- **The local component of `dt` at a zero of `t - a` is the trace residue in `t - a`**
(Stichtenoth, Theorem 4.3.2(d) and Remark 4.3.7(d)): for a separating element `t` of `F / k` and a
place `P` with residue field separable over `k` at which `t - a` is a prime element, the Weil
differential `dt` has local component `(dt)_P = Tr_{F_P/k} ∘ res_{P,t-a}`. -/
theorem repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue
    (hF : IsFunctionField k F) {t : F} (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {a : k}
    (ht : P.ord (t - algebraMap k F a) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialOfSeparating hF htr :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.traceResidue ht u := by
  let _ := ratFuncAlgebraOfTranscendental htr
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental htr
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental htr
  have hX : algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a) = t - algebraMap k F a := by
    rw [map_sub, algebraMap_ratFuncAlgebraOfTranscendental_X, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply]
  -- The trace residue only depends on the uniformizer, not on the proof that it is one.
  have hres {s : F} (hs : s = t - algebraMap k F a) (hs₁ : P.ord s = 1) :
      P.traceResidue hs₁ = P.traceResidue ht := by
    subst hs
    rfl
  rw [weilDifferentialOfSeparating_def,
    repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue hF
      (hX ▸ ht), hres hX]

/-- **The local component of `dt` at a zero of `t - a` is the residue in `t - a`** (Stichtenoth,
Theorem 4.3.2(d)): for a separating element `t` of `F / k` and a rational place `P` at which
`t - a` is a prime element, the Weil differential `dt` has local component `(dt)_P = res_{P,t-a}`.
-/
theorem repartitionDualComponent_weilDifferentialOfSeparating (hF : IsFunctionField k F) {t : F}
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] {P : Place k F} (hP : P.degree = 1)
    {a : k} (ht : P.ord (t - algebraMap k F a) = 1) (u : F) :
    repartitionDualComponent (weilDifferentialOfSeparating hF htr :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.residue hP ht u := by
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue hF htr ht,
    P.traceResidue_eq_residue ht hP]

end TauCeti
