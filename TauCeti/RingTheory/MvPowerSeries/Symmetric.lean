/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Eval
public import TauCeti.RingTheory.MvPowerSeries.Order
public import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Symmetric multivariable formal power series and evaluation at the roots of `Z ^ n - X`

A multivariable formal power series `f : MvPowerSeries σ R` is symmetric
(`MvPowerSeries.IsSymmetric`) if it is invariant under every permutation of the variable set `σ`
via `MvPowerSeries.rename`. Symmetric power series form an `R`-subalgebra
`MvPowerSeries.symmetricSubalgebra σ R`.

When `σ` is finite and nonempty of cardinality `n`, every degree-`m` homogeneous component of a
symmetric power series is a symmetric homogeneous polynomial of degree `m`. Evaluating the
degree-`(k * n)` component under `MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R` — which sends
the `j`-th elementary symmetric polynomial to `0` for `1 ≤ j < n` and the `n`-th elementary
symmetric polynomial to `(-1) ^ (n - 1) * X` — extracts a single coefficient at `X ^ k`. Assembling
these coefficients defines an `R`-algebra homomorphism

`MvPowerSeries.symmetricSubalgebra.evalTopEsymm σ R : symmetricSubalgebra σ R →ₐ[R] PowerSeries R`

extending polynomial `evalTopEsymm` (`evalTopEsymm_coe`), commuting with coefficient ring
homomorphisms (`map_evalTopEsymm`) and with formal power series substitution
(`evalTopEsymm_subst`), and sending the symmetric coordinate sum `∑ i : σ, γ(Xᵢ)` — whose degree-`m`
homogeneous component is `coeff m γ • psum σ R m`
(`homogeneousComponentPolynomial_sum_toMvPowerSeries`) — to `n • PowerSeries.cartier R n 0 γ`
(`evalTopEsymm_sum_toMvPowerSeries`). This last property is the power-series input to Cartier's
Frobenius operators on curves of formal group laws.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.2.
-/

public section

namespace MvPowerSeries

variable {σ τ R S : Type*}

/-- A multivariable formal power series `f` is symmetric if it is invariant under permutations of
its variables via `MvPowerSeries.rename`. -/
def IsSymmetric [CommSemiring R] (f : MvPowerSeries σ R) : Prop :=
  ∀ e : Equiv.Perm σ, rename e f = f

theorem isSymmetric_iff [CommSemiring R] {f : MvPowerSeries σ R} :
    f.IsSymmetric ↔ ∀ e : Equiv.Perm σ, rename e f = f :=
  Iff.rfl

/-- The subalgebra of symmetric multivariable formal power series. -/
noncomputable def symmetricSubalgebra (σ R : Type*) [CommSemiring R] :
    Subalgebra R (MvPowerSeries σ R) where
  carrier := Set.ofPred IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha e, hb e]
  add_mem' ha hb e := by rw [map_add, ha e, hb e]

@[simp]
theorem mem_symmetricSubalgebra [CommSemiring R] (f : MvPowerSeries σ R) :
    f ∈ symmetricSubalgebra σ R ↔ f.IsSymmetric :=
  Iff.rfl

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {f g : MvPowerSeries σ R}

@[simp]
theorem C (r : R) : IsSymmetric (C r : MvPowerSeries σ R) :=
  (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]
theorem zero : IsSymmetric (0 : MvPowerSeries σ R) :=
  (symmetricSubalgebra σ R).zero_mem

@[simp]
theorem one : IsSymmetric (1 : MvPowerSeries σ R) :=
  (symmetricSubalgebra σ R).one_mem

theorem add (hf : IsSymmetric f) (hg : IsSymmetric g) : IsSymmetric (f + g) :=
  (symmetricSubalgebra σ R).add_mem hf hg

theorem mul (hf : IsSymmetric f) (hg : IsSymmetric g) : IsSymmetric (f * g) :=
  (symmetricSubalgebra σ R).mul_mem hf hg

theorem pow (hf : IsSymmetric f) (n : ℕ) : IsSymmetric (f ^ n) :=
  (symmetricSubalgebra σ R).pow_mem hf n

theorem smul (r : R) (hf : IsSymmetric f) : IsSymmetric (r • f) :=
  (symmetricSubalgebra σ R).smul_mem hf r

theorem sum {ι : Type*} (s : Finset ι) {a : ι → MvPowerSeries σ R}
    (ha : ∀ i ∈ s, (a i).IsSymmetric) : (∑ i ∈ s, a i).IsSymmetric :=
  (symmetricSubalgebra σ R).sum_mem ha

theorem prod {ι : Type*} (s : Finset ι) {a : ι → MvPowerSeries σ R}
    (ha : ∀ i ∈ s, (a i).IsSymmetric) : (∏ i ∈ s, a i).IsSymmetric :=
  (symmetricSubalgebra σ R).prod_mem ha

@[simp]
theorem map (hf : IsSymmetric f) (φ : R →+* S) : IsSymmetric (map φ f) := fun e ↦ by
  rw [rename_map, hf e]

protected theorem rename (hf : f.IsSymmetric) (e : σ ≃ τ) : (rename e f).IsSymmetric := fun e' ↦ by
  let g : Equiv.Perm σ := (e.trans e').trans e.symm
  have hcomp : (⇑e' ∘ ⇑e : σ → τ) = ⇑e ∘ ⇑g := funext fun x ↦ by simp [g]
  conv_rhs => rw [← hf g]
  simp only [rename_rename, hcomp]

@[simp]
theorem _root_.MvPowerSeries.isSymmetric_rename {e : σ ≃ τ} :
    (rename e f).IsSymmetric ↔ f.IsSymmetric :=
  ⟨fun h ↦ by simpa using h.rename e.symm, (·.rename e)⟩

@[simp]
theorem _root_.MvPowerSeries.isSymmetric_coe {p : MvPolynomial σ R} :
    IsSymmetric (p : MvPowerSeries σ R) ↔ p.IsSymmetric := by
  simp [IsSymmetric, MvPolynomial.IsSymmetric, rename_coe, MvPolynomial.coe_inj]

theorem sum_toMvPowerSeries [Fintype σ] (γ : PowerSeries R) :
    (∑ i : σ, γ.toMvPowerSeries i).IsSymmetric := fun e ↦ by
  rw [map_sum]
  simp_rw [rename_toMvPowerSeries]
  exact Equiv.sum_comp e fun i ↦ γ.toMvPowerSeries i

end CommSemiring

section CommRing

variable [CommRing R] {f g : MvPowerSeries σ R}

theorem neg (hf : IsSymmetric f) : IsSymmetric (-f) :=
  (symmetricSubalgebra σ R).neg_mem hf

theorem sub (hf : IsSymmetric f) (hg : IsSymmetric g) : IsSymmetric (f - g) :=
  (symmetricSubalgebra σ R).sub_mem hf hg

/-- Substituting symmetric power series into an arbitrary power series produces a symmetric power
series. -/
theorem subst {g : MvPowerSeries τ R} {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (hsym : ∀ t, (a t).IsSymmetric) : (g.subst a).IsSymmetric := fun e ↦ by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]
  congr 1
  funext t
  rw [← rename_eq_subst, hsym t e]

end CommRing

end IsSymmetric

section Homogeneous

variable [CommSemiring R]

theorem IsSymmetric.homogeneousComponent {f : MvPowerSeries σ R} (hf : f.IsSymmetric) (m : ℕ) :
    (homogeneousComponent m f).IsSymmetric := fun e ↦ by
  rw [rename_homogeneousComponent, hf e]

theorem IsSymmetric.homogeneousComponentPolynomial [Finite σ] {f : MvPowerSeries σ R}
    (hf : f.IsSymmetric) (m : ℕ) :
    (homogeneousComponentPolynomial m f).IsSymmetric := fun e ↦ by
  rw [rename_homogeneousComponentPolynomial, hf e]

theorem IsSymmetric.truncTotal [Finite σ] {f : MvPowerSeries σ R} (hf : f.IsSymmetric) (N : ℕ) :
    (truncTotal N f).IsSymmetric := fun e ↦ by
  rw [rename_truncTotal, hf e]

/-- The degree-`m` homogeneous component of the coordinate sum `∑ i : σ, γ(Xᵢ)` is
`coeff m γ • psum σ R m`. -/
theorem homogeneousComponentPolynomial_sum_toMvPowerSeries [Fintype σ] (m : ℕ)
    (γ : PowerSeries R) :
    homogeneousComponentPolynomial m (∑ i : σ, γ.toMvPowerSeries i) =
      PowerSeries.coeff m γ • MvPolynomial.psum σ R m := by
  classical
  apply MvPolynomial.coe_inj.mp
  rw [coe_homogeneousComponentPolynomial, MvPolynomial.coe_smul, MvPolynomial.psum,
    ← MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    map_sum MvPolynomial.coeToMvPowerSeries.ringHom]
  ext d
  rw [coeff_homogeneousComponent, map_sum (coeff d), coeff_smul, map_sum (coeff d), Finset.mul_sum]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow,
      MvPolynomial.coe_X, X_pow_eq, PowerSeries.coeff_toMvPowerSeries]
    by_cases hdi : d = Finsupp.single i m
    · subst hdi
      simp
    · have hne : d ≠ Finsupp.single i (d i) := fun h ↦ hdi <| by
        have hdeg : d i = m := by
          simpa [Finsupp.degree_single] using (congrArg Finsupp.degree h).symm.trans hd
        rwa [← hdeg]
      rw [ite_eq_right hne, coeff_monomial_ne hdi, mul_zero]
  · refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow,
      MvPolynomial.coe_X, X_pow_eq]
    have hne : d ≠ Finsupp.single i m := fun h ↦ hd (by rw [h, Finsupp.degree_single])
    rw [coeff_monomial_ne hne, mul_zero]

end Homogeneous

namespace symmetricSubalgebra

/-- Every element of `symmetricSubalgebra σ R` is symmetric. -/
theorem isSymmetric [CommSemiring R] (P : symmetricSubalgebra σ R) : P.1.IsSymmetric :=
  (mem_symmetricSubalgebra P.1).mp P.2

section EvalTopEsymm

variable [Fintype σ] [CommRing R]

private noncomputable def symmHomogeneousComponent (m : ℕ)
    (P : symmetricSubalgebra σ R) : MvPolynomial.symmetricSubalgebra σ R :=
  ⟨homogeneousComponentPolynomial m P.1,
    (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).homogeneousComponentPolynomial m)⟩

private noncomputable def symmTruncTotal (N : ℕ)
    (P : symmetricSubalgebra σ R) : MvPolynomial.symmetricSubalgebra σ R :=
  ⟨truncTotal N P.1,
    (MvPolynomial.mem_symmetricSubalgebra _).mpr ((isSymmetric P).truncTotal N)⟩

/-- Underlying function of `evalTopEsymm` on symmetric formal power series. -/
private noncomputable def evalTopEsymmFun (P : symmetricSubalgebra σ R) : PowerSeries R :=
  PowerSeries.mk fun k ↦
    (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
      (symmHomogeneousComponent (k * Fintype.card σ) P)).coeff k

/-- For `N > k * Fintype.card σ`, the `k`-th coefficient of `evalTopEsymmFun P` equals the `k`-th
coefficient of polynomial `evalTopEsymm` applied to `truncTotal N P`. -/
private theorem coeff_evalTopEsymmFun_eq_coeff_truncTotal (P : symmetricSubalgebra σ R)
    {k N : ℕ} (hN : k * Fintype.card σ < N) :
    PowerSeries.coeff k (evalTopEsymmFun P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R (symmTruncTotal N P)).coeff k := by
  rw [evalTopEsymmFun, PowerSeries.coeff_mk]
  have hdecomp : symmTruncTotal N P = ∑ m ∈ Finset.range N, symmHomogeneousComponent m P :=
    Subtype.ext (by
      simpa [symmTruncTotal, symmHomogeneousComponent] using
        truncTotal_eq_sum_homogeneousComponentPolynomial N P.1)
  rw [hdecomp, map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single (k * Fintype.card σ)]
  · intro m _ hm
    rcases isEmpty_or_nonempty σ with hσ | hσ
    · rw [Fintype.card_eq_zero, mul_zero] at hm
      have hsub : symmHomogeneousComponent m P = 0 := Subtype.ext <| MvPolynomial.coe_inj.mp <| by
        dsimp only [symmHomogeneousComponent]
        rw [ZeroMemClass.coe_zero, coe_homogeneousComponentPolynomial, MvPolynomial.coe_zero]
        ext d
        rw [Subsingleton.elim d 0]
        simp [coeff_homogeneousComponent, hm.symm]
      simp [hsub]
    · exact MvPolynomial.symmetricSubalgebra.coeff_evalTopEsymm_eq_zero
        (isHomogeneous_homogeneousComponentPolynomial m P.1) hm.symm
  · exact fun hk ↦ absurd (Finset.mem_range.mpr hN) hk

/-- If two symmetric polynomials have the same `N`-truncation as power series with
`k * Fintype.card σ < N`, then their images under `evalTopEsymm` agree at `X ^ k`. -/
private theorem coeff_poly_evalTopEsymm_eq_of_truncTotal_eq
    {p q : MvPolynomial.symmetricSubalgebra σ R} {k N : ℕ} (hN : k * Fintype.card σ < N)
    (htrunc : truncTotal N (p.1 : MvPowerSeries σ R) = truncTotal N (q.1 : MvPowerSeries σ R)) :
    (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R p).coeff k =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R q).coeff k := by
  let P : symmetricSubalgebra σ R :=
    ⟨p.1, (mem_symmetricSubalgebra _).mpr (isSymmetric_coe.mpr
      ((MvPolynomial.mem_symmetricSubalgebra _).mp p.2))⟩
  let Q : symmetricSubalgebra σ R :=
    ⟨q.1, (mem_symmetricSubalgebra _).mpr (isSymmetric_coe.mpr
      ((MvPolynomial.mem_symmetricSubalgebra _).mp q.2))⟩
  let M := max N (max (p.1.totalDegree + 1) (q.1.totalDegree + 1))
  have hM : k * Fintype.card σ < M := hN.trans_le (le_max_left _ _)
  have hM0 : M ≠ 0 := by omega
  have hpM : symmTruncTotal M P = p :=
    Subtype.ext ((truncTotal_coe_eq_self_iff p.1 hM0).mpr (by omega))
  have hqM : symmTruncTotal M Q = q :=
    Subtype.ext ((truncTotal_coe_eq_self_iff q.1 hM0).mpr (by omega))
  have hpqN : symmTruncTotal N P = symmTruncTotal N Q := Subtype.ext htrunc
  rw [← hpM, ← coeff_evalTopEsymmFun_eq_coeff_truncTotal P hM,
    coeff_evalTopEsymmFun_eq_coeff_truncTotal P hN, hpqN,
    ← coeff_evalTopEsymmFun_eq_coeff_truncTotal Q hN,
    coeff_evalTopEsymmFun_eq_coeff_truncTotal Q hM, hqM]

variable (σ R) in
/-- Evaluating a symmetric formal power series `P(X₁, …, Xₙ)` (`n = Fintype.card σ`) at the formal
roots of `Z ^ n - X`, extending `MvPolynomial.symmetricSubalgebra.evalTopEsymm` componentwise. -/
noncomputable def evalTopEsymm : symmetricSubalgebra σ R →ₐ[R] PowerSeries R where
  toFun := evalTopEsymmFun
  map_one' := by
    ext k
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal 1 (Nat.lt_succ_self _)]
    have h1 : symmTruncTotal (k * Fintype.card σ + 1) (1 : symmetricSubalgebra σ R) = 1 :=
      Subtype.ext (truncTotal_one (Nat.succ_ne_zero _))
    rw [h1, map_one, Polynomial.coeff_one, PowerSeries.coeff_one]
  map_mul' P Q := by
    -- Truncating at `N = k * card σ + 1` captures every degree contributing to `X ^ k` in `P * Q`
    -- as well as in each antidiagonal factor of `coeff k (evalTopEsymm P * evalTopEsymm Q)`.
    ext k
    let N := k * Fintype.card σ + 1
    have hN : k * Fintype.card σ < N := Nat.lt_succ_self _
    have h0 : N ≠ 0 := Nat.succ_ne_zero _
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal (P * Q) hN]
    have htrunc : truncTotal N ((symmTruncTotal N (P * Q)).1 : MvPowerSeries σ R) =
        truncTotal N ((symmTruncTotal N P * symmTruncTotal N Q).1 : MvPowerSeries σ R) := by
      dsimp only [symmTruncTotal]
      rw [(truncTotal_coe_eq_self_iff _ h0).mpr (totalDegree_truncTotal_lt _ h0)]
      ext d
      by_cases hd : d.degree < N
      · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, Subalgebra.coe_mul, Subalgebra.coe_mul,
          MvPolynomial.coeff_coe, coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hd]
      · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd), coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
    rw [coeff_poly_evalTopEsymm_eq_of_truncTotal_eq hN htrunc, map_mul, Polynomial.coeff_mul,
      PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun ab hab ↦ ?_
    rw [Finset.mem_antidiagonal] at hab
    have haN : ab.1 * Fintype.card σ < N :=
      (Nat.mul_le_mul_right _ (by omega : ab.1 ≤ k)).trans_lt hN
    have hbN : ab.2 * Fintype.card σ < N :=
      (Nat.mul_le_mul_right _ (by omega : ab.2 ≤ k)).trans_lt hN
    rw [← coeff_evalTopEsymmFun_eq_coeff_truncTotal P haN,
      ← coeff_evalTopEsymmFun_eq_coeff_truncTotal Q hbN]
  map_zero' := by
    ext k
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal 0 (Nat.lt_succ_self _)]
    have h0 : symmTruncTotal (k * Fintype.card σ + 1) (0 : symmetricSubalgebra σ R) = 0 :=
      Subtype.ext (map_zero _)
    rw [h0, map_zero, Polynomial.coeff_zero, map_zero (PowerSeries.coeff k)]
  map_add' P Q := by
    ext k
    rw [evalTopEsymmFun, evalTopEsymmFun, evalTopEsymmFun, PowerSeries.coeff_mk, map_add,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← Polynomial.coeff_add, ← map_add]
    have hsub : symmHomogeneousComponent (k * Fintype.card σ) (P + Q) =
        symmHomogeneousComponent (k * Fintype.card σ) P +
          symmHomogeneousComponent (k * Fintype.card σ) Q :=
      Subtype.ext <| MvPolynomial.coe_inj.mp <| by
        simp [symmHomogeneousComponent, coe_homogeneousComponentPolynomial]
    rw [hsub]
  commutes' r := by
    ext k
    rw [coeff_evalTopEsymmFun_eq_coeff_truncTotal (algebraMap R _ r) (Nat.lt_succ_self _)]
    have hr : symmTruncTotal (k * Fintype.card σ + 1)
        (algebraMap R (symmetricSubalgebra σ R) r) = algebraMap R _ r := by
      apply Subtype.ext
      dsimp only [symmTruncTotal]
      rw [Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, OneMemClass.coe_one,
        smul_eq_C_mul, mul_one, ← MvPolynomial.coe_C,
        (truncTotal_coe_eq_self_iff _ (Nat.succ_ne_zero _)).mpr
          (MvPolynomial.totalDegree_C r ▸ Nat.zero_lt_succ _),
        Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, OneMemClass.coe_one,
        MvPolynomial.smul_eq_C_mul, mul_one]
    rw [hr, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.coeff_C,
      PowerSeries.algebraMap_apply, PowerSeries.coeff_C, Algebra.algebraMap_self_apply]

theorem coeff_evalTopEsymm (P : symmetricSubalgebra σ R) (k : ℕ) :
    PowerSeries.coeff k (evalTopEsymm σ R P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
        ⟨homogeneousComponentPolynomial (k * Fintype.card σ) P.1,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr
            ((isSymmetric P).homogeneousComponentPolynomial _)⟩).coeff k := by
  simp [evalTopEsymm, evalTopEsymmFun, symmHomogeneousComponent]

private theorem coeff_evalTopEsymm_eq_coeff_truncTotal (P : symmetricSubalgebra σ R)
    {k N : ℕ} (hN : k * Fintype.card σ < N) :
    PowerSeries.coeff k (evalTopEsymm σ R P) =
      (MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R (symmTruncTotal N P)).coeff k :=
  coeff_evalTopEsymmFun_eq_coeff_truncTotal P hN

@[simp]
theorem constantCoeff_evalTopEsymm (P : symmetricSubalgebra σ R) :
    PowerSeries.constantCoeff (evalTopEsymm σ R P) = constantCoeff P.1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_evalTopEsymm, zero_mul]
  have hsub : symmHomogeneousComponent 0 P = algebraMap R _ (constantCoeff P.1) := by
    apply Subtype.ext
    apply MvPolynomial.coe_inj.mp
    simp [symmHomogeneousComponent, coe_homogeneousComponentPolynomial, homogeneousComponent_zero,
      Algebra.algebraMap_eq_smul_one, MvPolynomial.smul_eq_C_mul]
  dsimp only [symmHomogeneousComponent] at hsub
  rw [hsub, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.coeff_C_zero]

/-- On symmetric polynomials coerced to symmetric power series, `evalTopEsymm` agrees with
polynomial `evalTopEsymm` coerced to `PowerSeries R`. -/
theorem evalTopEsymm_coe (p : MvPolynomial.symmetricSubalgebra σ R) :
    evalTopEsymm σ R
        ⟨p.1, (mem_symmetricSubalgebra _).mpr
          (isSymmetric_coe.mpr ((MvPolynomial.mem_symmetricSubalgebra _).mp p.2))⟩ =
      ((MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R p : Polynomial R) : PowerSeries R) := by
  ext k
  let P : symmetricSubalgebra σ R :=
    ⟨p.1, (mem_symmetricSubalgebra _).mpr
      (isSymmetric_coe.mpr ((MvPolynomial.mem_symmetricSubalgebra _).mp p.2))⟩
  let N := max (p.1.totalDegree + 1) (k * Fintype.card σ + 1)
  have hN : k * Fintype.card σ < N := (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  have hsub : symmTruncTotal N P = p :=
    Subtype.ext ((truncTotal_coe_eq_self_iff p.1 (by omega)).mpr (by omega))
  rw [coeff_evalTopEsymm_eq_coeff_truncTotal P hN, hsub, Polynomial.coeff_coe]

/-- `evalTopEsymm` commutes with changing coefficients along a ring homomorphism `f : R →+* S`. -/
theorem map_evalTopEsymm [CommRing S] (f : R →+* S) (P : symmetricSubalgebra σ R) :
    PowerSeries.map f (evalTopEsymm σ R P) =
      evalTopEsymm σ S ⟨map f P.1, (mem_symmetricSubalgebra _).mpr ((isSymmetric P).map f)⟩ := by
  ext k
  rw [PowerSeries.coeff_map, coeff_evalTopEsymm, coeff_evalTopEsymm,
    ← Polynomial.coeff_map, MvPolynomial.symmetricSubalgebra.map_evalTopEsymm]
  congr 2
  congr 1
  apply Subtype.ext
  ext d
  rw [MvPolynomial.coeff_map, ← MvPolynomial.coeff_coe, coe_homogeneousComponentPolynomial,
    ← MvPolynomial.coeff_coe, coe_homogeneousComponentPolynomial,
    coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- `evalTopEsymm` commutes with formal power series substitution. -/
theorem evalTopEsymm_subst [Nonempty σ] [Finite τ] (g : MvPowerSeries τ R)
    (a : τ → symmetricSubalgebra σ R) (ha : ∀ t, constantCoeff (a t).1 = 0) :
    evalTopEsymm σ R
        ⟨g.subst (fun t ↦ (a t).1),
          (mem_symmetricSubalgebra _).mpr
            (IsSymmetric.subst (hasSubst_of_constantCoeff_zero ha) fun t ↦ isSymmetric (a t))⟩ =
      g.subst (fun t ↦ evalTopEsymm σ R (a t)) := by
  ext k
  let PS : symmetricSubalgebra σ R :=
    ⟨g.subst (fun t ↦ (a t).1),
      (mem_symmetricSubalgebra _).mpr
        (IsSymmetric.subst (hasSubst_of_constantCoeff_zero ha) fun t ↦ isSymmetric (a t))⟩
  let N := k * Fintype.card σ + 1
  have hN : k * Fintype.card σ < N := Nat.lt_succ_self _
  have hcard : 0 < Fintype.card σ := Fintype.card_pos
  have hkN : k + 1 ≤ N := by nlinarith
  rw [coeff_evalTopEsymm_eq_coeff_truncTotal PS hN]
  -- Step 1: Truncating `g.subst a` at total degree `N = k * card σ + 1` reduces to polynomial
  -- evaluation `Q = aeval aN (truncTotal N g)` modulo total degree `N`.
  let aN : τ → MvPolynomial.symmetricSubalgebra σ R := fun t ↦ symmTruncTotal N (a t)
  let Q : MvPolynomial.symmetricSubalgebra σ R := MvPolynomial.aeval aN (truncTotal N g)
  have hQ_val : Q.1 = MvPolynomial.aeval (fun t ↦ (aN t).1) (truncTotal N g) :=
    MvPolynomial.comp_aeval_apply aN (MvPolynomial.symmetricSubalgebra σ R).val (truncTotal N g)
  have htrunc_lhs : truncTotal N ((symmTruncTotal N PS).1 : MvPowerSeries σ R) =
      truncTotal N (Q.1 : MvPowerSeries σ R) := by
    have h0 : N ≠ 0 := Nat.succ_ne_zero _
    have hPS : (symmTruncTotal N PS).1 = truncTotal N (g.subst fun t ↦ (a t).1) := (rfl)
    have haN : (fun t ↦ ((aN t).1 : MvPowerSeries σ R)) =
        fun t ↦ (truncTotal N (a t).1 : MvPowerSeries σ R) := (rfl)
    rw [hPS, (truncTotal_coe_eq_self_iff _ h0).mpr (totalDegree_truncTotal_lt _ h0),
      truncTotal_subst ha, hQ_val, ← subst_coe_eq_coe_aeval, haN]
  -- Step 2: Push polynomial `evalTopEsymm` through `aeval` into univariate power-series `subst`.
  let Φ : MvPolynomial.symmetricSubalgebra σ R →ₐ[R] Polynomial R :=
    MvPolynomial.symmetricSubalgebra.evalTopEsymm σ R
  have hΦQ : Φ Q = MvPolynomial.aeval (fun t ↦ Φ (aN t)) (truncTotal N g) :=
    MvPolynomial.comp_aeval_apply aN Φ (truncTotal N g)
  have hcoe_aeval :
      ((MvPolynomial.aeval (fun t ↦ Φ (aN t)) (truncTotal N g) : Polynomial R) : PowerSeries R) =
        (truncTotal N g : MvPowerSeries τ R).subst
          (fun t ↦ ((Φ (aN t) : Polynomial R) : PowerSeries R)) := by
    let Ψ : Polynomial R →ₐ[R] PowerSeries R := Polynomial.coeToPowerSeries.algHom R
    have hΨ : ∀ q : Polynomial R, Ψ q = (q : PowerSeries R) := fun q ↦ by
      simp [Ψ, Polynomial.coeToPowerSeries.algHom_apply]
    rw [subst_coe, ← hΨ, MvPolynomial.comp_aeval_apply _ Ψ]
    simp_rw [hΨ]
  rw [coeff_poly_evalTopEsymm_eq_of_truncTotal_eq hN htrunc_lhs, hΦQ, ← Polynomial.coeff_coe,
    hcoe_aeval]
  -- Step 3: Compare univariate substitutions modulo degree `k + 1` (using `k + 1 ≤ N`).
  have hb0 : ∀ t, constantCoeff (evalTopEsymm σ R (a t) : MvPowerSeries Unit R) = 0 := fun t ↦ by
    rw [← PowerSeries.constantCoeff_eq, constantCoeff_evalTopEsymm, ha t]
  have hc0 : ∀ t, constantCoeff (((Φ (aN t) : Polynomial R) : PowerSeries R) :
      MvPowerSeries Unit R) = 0 := fun t ↦ by
    rw [← PowerSeries.constantCoeff_eq, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, ← coeff_evalTopEsymm_eq_coeff_truncTotal (a t) (by simp [N]),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_evalTopEsymm, ha t]
  have htrunc_a : ∀ t,
      truncTotal (k + 1) (((Φ (aN t) : Polynomial R) : PowerSeries R) : MvPowerSeries Unit R) =
        truncTotal (k + 1) (evalTopEsymm σ R (a t) : MvPowerSeries Unit R) := fun t ↦ by
    ext d
    by_cases hd : d.degree < k + 1
    · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, ← PowerSeries.coeff_def rfl,
        Polynomial.coeff_coe]
      have hd_le : d () ≤ k := Nat.lt_succ_iff.mp ((Finsupp.le_degree () d).trans_lt hd)
      have hdN : d () * Fintype.card σ < N :=
        (Nat.mul_le_mul_right _ hd_le).trans_lt hN
      exact (coeff_evalTopEsymm_eq_coeff_truncTotal (a t) hdN).symm
    · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd), coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
  have htrunc_unit :
      truncTotal (k + 1)
          ((truncTotal N g : MvPowerSeries τ R).subst
            fun t ↦ (((Φ (aN t) : Polynomial R) : PowerSeries R) : MvPowerSeries Unit R)) =
        truncTotal (k + 1)
          (g.subst fun t ↦ (evalTopEsymm σ R (a t) : MvPowerSeries Unit R)) := by
    rw [truncTotal_subst hc0, truncTotal_subst hb0, truncTotal_truncTotal_coe hkN g]
    simp_rw [htrunc_a]
  have hdeg : (Finsupp.single () k : Unit →₀ ℕ).degree < k + 1 := by
    simp [Finsupp.degree_single]
  rw [← PowerSeries.coeff_coeToMvPowerSeries, ← PowerSeries.coeff_coeToMvPowerSeries,
    ← coeff_truncTotal _ hdeg, htrunc_unit, coeff_truncTotal _ hdeg]

/-- Evaluating the symmetric coordinate sum `∑ i : σ, γ(Xᵢ)` under `evalTopEsymm` extracts the
degree-multiples of `n = Fintype.card σ` multiplied by `n`, i.e. `n • PowerSeries.cartier R n 0 γ`.
-/
theorem evalTopEsymm_sum_toMvPowerSeries [Nonempty σ] (γ : PowerSeries R) :
    evalTopEsymm σ R
        ⟨∑ i : σ, γ.toMvPowerSeries i,
          (mem_symmetricSubalgebra _).mpr (IsSymmetric.sum_toMvPowerSeries γ)⟩ =
      (Fintype.card σ : R) • PowerSeries.cartier R (Fintype.card σ) 0 γ := by
  have hn : 0 < Fintype.card σ := Fintype.card_pos
  -- Each homogeneous component of `∑ i, γ(Xᵢ)` is `coeff m γ` times the `m`-th power sum `psum`.
  have hcomp : ∀ m : ℕ,
      (⟨homogeneousComponentPolynomial m (∑ i : σ, γ.toMvPowerSeries i),
        (MvPolynomial.mem_symmetricSubalgebra _).mpr
          ((IsSymmetric.sum_toMvPowerSeries γ).homogeneousComponentPolynomial m)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) =
      PowerSeries.coeff m γ •
        ⟨MvPolynomial.psum σ R m,
          (MvPolynomial.mem_symmetricSubalgebra _).mpr (MvPolynomial.psum_isSymmetric σ R m)⟩ :=
    fun m ↦ Subtype.ext (homogeneousComponentPolynomial_sum_toMvPowerSeries m γ)
  ext k
  rw [coeff_evalTopEsymm, hcomp, map_smul, Polynomial.coeff_smul, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, add_zero, smul_eq_mul, smul_eq_mul, mul_comm (Fintype.card σ) k]
  rcases eq_or_ne k 0 with rfl | hk
  · -- For `k = 0`, `psum σ R 0 = card σ`.
    have hp0 : (⟨MvPolynomial.psum σ R 0,
        (MvPolynomial.mem_symmetricSubalgebra _).mpr (MvPolynomial.psum_isSymmetric σ R 0)⟩ :
        MvPolynomial.symmetricSubalgebra σ R) = algebraMap R _ (Fintype.card σ : R) :=
      Subtype.ext (by simp [MvPolynomial.psum_zero])
    rw [zero_mul, hp0, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.coeff_C_zero, mul_comm]
  · -- For `k ≠ 0`, `evalTopEsymm` sends `psum σ R (k * card σ)` to `card σ * X ^ k`.
    have hkn : 0 < k * Fintype.card σ := Nat.mul_pos (Nat.pos_of_ne_zero hk) hn
    rw [MvPolynomial.symmetricSubalgebra.evalTopEsymm_psum hkn, ite_eq_left (dvd_mul_left _ _),
      Nat.mul_div_cancel _ hn, Polynomial.coeff_natCast_mul, Polynomial.coeff_X_pow_self, mul_one,
      mul_comm]

end EvalTopEsymm

end symmetricSubalgebra

end MvPowerSeries
