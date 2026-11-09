/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
import Mathlib.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.FunctionField.Place.Extension.Kummer
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.RingTheory.Polynomial.Monic.Factorization

/-!
# The extension `k(t)[Y] / (Y ^ n - t)`

For `n ≠ 0`, the polynomial `Y ^ n - t` is irreducible over the rational function field `k(t)`,
since `t` has order one at the place `t = 0`. So `k(t)[Y] / (Y ^ n - t)` is a field extension of
`k(t)` of degree `n`, and it is separable when `n` is invertible in `k`. It is the function field
of the source of the power map `u ↦ u ^ n` of the projective line.

## Main results

* `TauCeti.irreducible_X_pow_sub_C_X`: `Y ^ n - t` is irreducible over `k(t)`.
* `TauCeti.finrank_adjoinRoot_X_pow_sub_C_X`: `k(t)[Y] / (Y ^ n - t)` has degree `n` over `k(t)`.
* `TauCeti.isSeparable_adjoinRoot_X_pow_sub_C_X`: it is separable over `k(t)` when `n` is
  invertible in `k`.
* `TauCeti.isTotallyRamified_adjoinRoot_X_pow_sub_C_X` and
  `TauCeti.ramificationIdx_adjoinRoot_X_pow_sub_C_X_eq_one`: when `n` is invertible in `k`, it is
  totally ramified over `t = 0` and `t = ∞` and unramified elsewhere.
* `TauCeti.exists_equiv_restrict_eq_adicOfIrreducible_X_sub_one`: when `n` is invertible in `k`,
  the places over `t = 1` correspond to the monic irreducible factors `q` of `X ^ n - 1` over `k`,
  with relative degree `deg q`. This is Kummer's theorem
  (`TauCeti.Place.exists_equiv_restrict_eq_of_prod_eq_map_residue`): `Y ^ n - t` reduces to
  `Y ^ n - 1` at `t = 1`, which is separable.
* `TauCeti.exists_setOf_restrict_eq_adicOfIrreducible_X_sub_one_eq_pair`: when `X ^ 2 + X + 1` is
  irreducible over `k`, as over `ℚ`, the extension `k(t)[Y] / (Y ^ 3 - t)` has two places over
  `t = 1`, of relative degrees `1` and `2`. The ramification indices over `t = 1` therefore do not
  add up to the degree; only the ramification indices weighted by the relative degrees do.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.3.7.
-/

public section

open Polynomial

namespace TauCeti

variable (k : Type*) [Field k] (n : ℕ) [NeZero n]

/-- `Y ^ n - t` is irreducible over `k(t)`, because `t` has order one at the place `t = 0`. -/
theorem irreducible_X_pow_sub_C_X : Irreducible (X ^ n - C (RatFunc.X : RatFunc k)) :=
  (Place.adicOfIrreducible (irreducible_X (R := k))).valuation
    |>.X_pow_sub_C_irreducible_of_gcd_ord_eq_one (NeZero.ne n) (by
      rw [Place.ord_valuation, Place.ord_adicOfIrreducible_X_self, Int.gcd_one_right])

instance : Fact (Irreducible (X ^ n - C (RatFunc.X : RatFunc k))) :=
  ⟨irreducible_X_pow_sub_C_X k n⟩

instance : FiniteDimensional (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) :=
  (monic_X_pow_sub_C _ (NeZero.ne n)).finite_adjoinRoot

/-- `k(t)[Y] / (Y ^ n - t)` has degree `n` over `k(t)`. -/
theorem finrank_adjoinRoot_X_pow_sub_C_X :
    Module.finrank (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) = n := by
  rw [(AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (NeZero.pos n) _)).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

/-- `k(t)[Y] / (Y ^ n - t)` is separable over `k(t)` when `n` is invertible in `k`. -/
theorem isSeparable_adjoinRoot_X_pow_sub_C_X (hn : (n : k) ≠ 0) :
    Algebra.IsSeparable (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) := by
  have hn' : (n : RatFunc k) ≠ 0 := by
    rwa [← map_natCast (algebraMap k (RatFunc k)), _root_.map_ne_zero]
  exact isSeparable_of_pow_eq_of_adjoin_eq_top hn' RatFunc.X_ne_zero
    (by simpa [AdjoinRoot.algebraMap_eq] using root_X_pow_sub_C_pow n (RatFunc.X : RatFunc k))
    (IntermediateField.adjoin_root_eq_top _)

/-- The root of `Y ^ n - t` is an `n`-th root of `t`, written in the form
`y ^ n = c t ^ a (t - 1) ^ b` with `c = 1`, `a = 1` and `b = 0`. -/
private theorem root_pow_eq :
    AdjoinRoot.root (X ^ n - C (RatFunc.X : RatFunc k)) ^ n =
      algebraMap (RatFunc k) (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)))
        (algebraMap k (RatFunc k) 1 * RatFunc.X ^ (1 : ℤ) * (RatFunc.X - 1) ^ (0 : ℤ)) := by
  simpa [AdjoinRoot.algebraMap_eq] using root_X_pow_sub_C_pow n (RatFunc.X : RatFunc k)

/-- **The power map is totally ramified over `0` and `∞`**: if `n` is invertible in `k`, every
place of `k(t)[Y] / (Y ^ n - t)` over `t = 0` or `t = ∞` has ramification index `n`, so it is the
only place over that point and has relative degree one. -/
theorem isTotallyRamified_adjoinRoot_X_pow_sub_C_X (hn : (n : k) ≠ 0)
    {P : Place k (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)))}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X (R := k)) ∨
      P.restrict k (RatFunc k) = Place.infty k) :
    Place.IsTotallyRamified (RatFunc k) P := by
  have := isSeparable_adjoinRoot_X_pow_sub_C_X k n hn
  rw [Place.isTotallyRamified_iff, finrank_adjoinRoot_X_pow_sub_C_X,
    Place.ramificationIdx_eq_of_pow_eq k (RatFunc k) (IntermediateField.adjoin_root_eq_top _)
      (root_pow_eq k n) hn
      (RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero one_ne_zero 1 0)]
  rcases hP with hP | hP <;> rw [hP]
  · rw [Place.ord_adicOfIrreducible_X_algebraMap_mul_X_zpow_mul_X_sub_one_zpow one_ne_zero,
      Int.gcd_one_right, Nat.div_one]
  · rw [Place.ord_infty_algebraMap_mul_X_zpow_mul_X_sub_one_zpow one_ne_zero, add_zero,
      Int.gcd_neg, Int.gcd_one_right, Nat.div_one]

/-- **The power map is unramified away from `0` and `∞`**: if `n` is invertible in `k`, every
place of `k(t)[Y] / (Y ^ n - t)` over a place of `k(t)` other than `t = 0` and `t = ∞`, in
particular over `t = 1`, has ramification index `1`. -/
theorem ramificationIdx_adjoinRoot_X_pow_sub_C_X_eq_one (hn : (n : k) ≠ 0)
    {P : Place k (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k)))}
    (hP0 : P.restrict k (RatFunc k) ≠ Place.adicOfIrreducible (irreducible_X (R := k)))
    (hPinf : P.restrict k (RatFunc k) ≠ Place.infty k) :
    Place.ramificationIdx (RatFunc k) P = 1 := by
  have := isSeparable_adjoinRoot_X_pow_sub_C_X k n hn
  refine Place.ramificationIdx_eq_one_of_pow_eq_of_dvd_ord k (RatFunc k)
    (IntermediateField.adjoin_root_eq_top _) (root_pow_eq k n) hn
    (RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero one_ne_zero 1 0) ?_
  rw [Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow _ one_ne_zero,
    Place.ord_X_eq_zero_of_ne hP0 hPinf]
  simp

/-! ### The places over `t = 1` -/

section XSubOne

open UniqueFactorizationMonoid

open scoped Classical in
/-- **The places of the power map over `t = 1`**: if `n` is invertible in `k`, the places of
`k(t)[Y] / (Y ^ n - t)` over `t = 1` correspond to the monic irreducible factors `q` of
`X ^ n - 1` in `k[X]`, the place attached to `q` having relative degree `deg q`. They are
unramified (`TauCeti.ramificationIdx_adjoinRoot_X_pow_sub_C_X_eq_one`), so the local data of the
power map over `t = 1` is `{(1, deg q)}`.

In particular all the places over `t = 1` have relative degree one exactly when `X ^ n - 1`
splits over `k`. When it does not, as for `k = ℚ` and `n = 3`, there are fewer places than the
degree (`TauCeti.exists_setOf_restrict_eq_adicOfIrreducible_X_sub_one_eq_pair`). -/
theorem exists_equiv_restrict_eq_adicOfIrreducible_X_sub_one (hn : (n : k) ≠ 0) :
    ∃ e : (normalizedFactors (X ^ n - 1 : k[X])).toFinset ≃
        {P : Place k (AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc k))) //
          P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (1 : k))},
      ∀ q, Place.relativeDegree k (RatFunc k) (e q).1 = (q : k[X]).natDegree := by
  set P := Place.adicOfIrreducible (irreducible_X_sub_C (1 : k))
  have hX : (RatFunc.X : RatFunc k) ∈ P.integers := Place.X_mem_integers_adicOfIrreducible _
  -- The residue field of `t = 1` is `k`.
  let σ : k ≃+* P.ResidueField :=
    (P.residueFieldEquivOfDegreeEqOne (Place.degree_adicOfIrreducible_X_sub_C 1)).toRingEquiv
  -- `Y ^ n - t` has coefficients regular at `t = 1`, and reduces to `Y ^ n - 1` there.
  set φ : P.integers[X] := X ^ n - C ⟨RatFunc.X, hX⟩
  have hmin : φ.map (algebraMap P.integers (RatFunc k)) =
      minpoly (RatFunc k) (AdjoinRoot.root (X ^ n - C (RatFunc.X : RatFunc k))) := by
    have hφ : φ.map (algebraMap P.integers (RatFunc k)) = X ^ n - C RatFunc.X := by
      simp [φ]
    rw [hφ]
    exact minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C_X k n)
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (monic_X_pow_sub_C _ (NeZero.ne n))
  have hres : IsLocalRing.residue P.integers ⟨RatFunc.X, hX⟩ = 1 :=
    (Place.residue_X_adicOfIrreducible_X_sub_C (1 : k)).trans (map_one _)
  have hφres : φ.map (IsLocalRing.residue P.integers) = (X ^ n - 1 : k[X]).map σ := by
    simp [φ, hres]
  -- `X ^ n - 1` is separable, so it is the product of its distinct monic irreducible factors.
  have hsep : (X ^ n - 1 : k[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : k) hn one_ne_zero
  have hmonic₁ : (X ^ n - 1 : k[X]).Monic := by
    simpa using monic_X_pow_sub_C (1 : k) (NeZero.ne n)
  have hmonic (q : (normalizedFactors (X ^ n - 1 : k[X])).toFinset) : (q : k[X]).Monic := by
    have hq := Multiset.mem_toFinset.mp q.2
    rw [← normalize_normalized_factor _ hq]
    exact monic_normalize (ne_zero_of_mem_normalizedFactors hq)
  have hprod : ∏ q : (normalizedFactors (X ^ n - 1 : k[X])).toFinset,
      (q : k[X]).map (σ : k →+* P.ResidueField) = φ.map (IsLocalRing.residue P.integers) := by
    rw [hφres, ← Polynomial.map_prod, Finset.prod_coe_sort _ fun q ↦ q,
      hmonic₁.prod_toFinset_normalizedFactors_of_squarefree hsep.squarefree]
  obtain ⟨e, he⟩ := Place.exists_equiv_restrict_eq_of_prod_eq_map_residue (k' := k)
    (IsFunctionField.ratFunc k) P (IntermediateField.adjoin_root_eq_top _) hmin
    (γ := fun q : (normalizedFactors (X ^ n - 1 : k[X])).toFinset ↦
      (q : k[X]).map (σ : k →+* P.ResidueField)) (fun q ↦ (hmonic q).map _)
    (fun q ↦ by simpa using (irreducible_of_normalized_factor _
      (Multiset.mem_toFinset.mp q.2)).map (mapEquiv σ))
    (fun q r h ↦ Subtype.ext (map_injective _ σ.injective h)) hprod
  exact ⟨e, fun q ↦ (he q).trans (natDegree_map _)⟩

/-- **A cube map with two places over `t = 1`**: if `X ^ 2 + X + 1` is irreducible over `k`, as it
is over `ℚ`, where it is the cyclotomic polynomial `Φ₃` (`Polynomial.cyclotomic.irreducible_rat`),
then `k(t)[Y] / (Y ^ 3 - t)` has exactly two places over `t = 1`, of relative degrees `1` and `2`,
the factors of `X ^ 3 - 1 = (X - 1) (X ^ 2 + X + 1)`. Both are unramified, so the ramification
indices over `t = 1` add up to `2` rather than to the degree `3`, while the ramification indices
weighted by the relative degrees add up to `1 · 1 + 1 · 2 = 3`. -/
theorem exists_setOf_restrict_eq_adicOfIrreducible_X_sub_one_eq_pair
    (hq : Irreducible (X ^ 2 + X + 1 : k[X])) :
    ∃ P₁ P₂ : Place k (AdjoinRoot (X ^ 3 - C (RatFunc.X : RatFunc k))), P₁ ≠ P₂ ∧
      {P | P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (1 : k))} =
        {P₁, P₂} ∧
      Place.relativeDegree k (RatFunc k) P₁ = 1 ∧ Place.relativeDegree k (RatFunc k) P₂ = 2 := by
  classical
  have hdeg₂ : (X ^ 2 + X + 1 : k[X]).natDegree = 2 := by compute_degree!
  have hq₁ : (X - C 1 : k[X]).Monic := monic_X_sub_C 1
  have hq₂ : (X ^ 2 + X + 1 : k[X]).Monic := by monicity!
  -- In characteristic `3` the quadratic factor would be `(X - 1) ^ 2`.
  have h3 : ((3 : ℕ) : k) ≠ 0 := fun h3 ↦ by
    have h : (X ^ 2 + X + 1 : k[X]) = (X - 1) ^ 2 := by
      have h3' : (3 : k[X]) = 0 := by
        rw [← map_ofNat C 3, ← Nat.cast_ofNat, h3, map_zero]
      linear_combination (X : k[X]) * h3'
    exact not_irreducible_pow (by norm_num) (h ▸ hq)
  have hfac : normalizedFactors (X ^ 3 - 1 : k[X]) = {X - C 1, X ^ 2 + X + 1} := by
    have h : (X ^ 3 - 1 : k[X]) = (X - C 1) * (X ^ 2 + X + 1) := by
      simp only [map_one]
      ring
    rw [h, normalizedFactors_mul hq₁.ne_zero hq₂.ne_zero,
      normalizedFactors_irreducible (irreducible_X_sub_C 1), normalizedFactors_irreducible hq,
      hq₁.normalize_eq_self, hq₂.normalize_eq_self]
    rfl
  obtain ⟨e, he⟩ := exists_equiv_restrict_eq_adicOfIrreducible_X_sub_one k 3 h3
  have h₁ : (X - C 1 : k[X]) ∈ (normalizedFactors (X ^ 3 - 1 : k[X])).toFinset := by simp [hfac]
  have h₂ : (X ^ 2 + X + 1 : k[X]) ∈ (normalizedFactors (X ^ 3 - 1 : k[X])).toFinset := by
    simp [hfac]
  have hne : (X - C 1 : k[X]) ≠ X ^ 2 + X + 1 := fun h ↦ by
    have h' := congrArg natDegree h
    rw [natDegree_X_sub_C, hdeg₂] at h'
    omega
  refine ⟨(e ⟨_, h₁⟩).1, (e ⟨_, h₂⟩).1, fun h ↦ hne ?_, ?_, ?_, ?_⟩
  · simpa using e.injective (Subtype.ext h)
  · ext P
    refine ⟨fun hP ↦ ?_, ?_⟩
    · have hmem := (e.symm ⟨P, hP⟩).2
      have hP' : P = (e (e.symm ⟨P, hP⟩)).1 := by simp
      simp only [hfac, Multiset.insert_eq_cons, Multiset.toFinset_cons,
        Multiset.toFinset_singleton, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · left
        rw [hP']
        congr 2
        exact Subtype.ext h
      · right
        rw [Set.mem_singleton_iff, hP']
        congr 2
        exact Subtype.ext h
    · rintro (rfl | rfl)
      exacts [(e _).2, (e _).2]
  · rw [he]
    exact natDegree_X_sub_C 1
  · rw [he]
    exact hdeg₂

end XSubOne

end TauCeti
