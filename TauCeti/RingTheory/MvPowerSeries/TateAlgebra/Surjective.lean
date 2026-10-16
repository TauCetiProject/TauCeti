/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.ControlledClosure
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Surjectivity of maps of Tate algebras from lifts of generators

Let `Φ : R{Y/d} → S{X/c}` be a ring homomorphism between rings of restricted power series with
their Gauss norms, over ultrametric normed rings `R` and `S`, with `R{Y/d}` complete (for
instance when `R` is complete), and suppose that `Φ` does not increase norms. If every constant
from a dense additive subgroup `D ⊆ S` and every variable `Xᵢ` has a preimage of no larger norm,
then `Φ` is surjective.

Indeed, the polynomials with coefficients in `D` lift without increasing the norm, since the
Gauss norm of a polynomial is the largest weighted norm of its terms. These polynomials are dense
(`MvPowerSeries.dense_closure_monomial`), so the successive approximation argument of Mathlib's
`controlled_closure_of_complete` lifts every element of `S{X/c}`.

This is how one presents rings of convergent functions on annuli as quotients of Tate algebras at
real radii, as in Kedlaya's Lemma 4.9 for the interval rings of the Fargues–Fontaine curve: the
lifts of the constants come from an explicit Laurent expansion.

## Main results

* `MvPowerSeries.surjective_of_exists_lift`: a norm-nonincreasing ring homomorphism of Tate
  algebras with a complete source is surjective when the constants from a dense additive subgroup
  and the variables lift without increasing the norm.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Lemma 4.9.
-/

public section

namespace MvPowerSeries

variable {σ τ R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {c : σ → ℝ} [∀ i, Fact (0 < c i)]
  {d : τ → ℝ} [∀ j, Fact (0 < d j)]
  {Φ : IsRestricted.subring (R := R) d →+* IsRestricted.subring (R := S) c}

/-- A polynomial with lifted coefficients lifts without increasing the norm: lift each monomial
`aₜ Xᵗ` to the product of the lifts of `aₜ` and of the variables. -/
private theorem exists_lift_of_finite {D : AddSubgroup S}
    (hC : ∀ a ∈ D, ∃ f, Φ f = algebraMap S _ a ∧ ‖f‖ ≤ ‖a‖)
    (hX : ∀ i, ∃ f, Φ f = ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ ∧ ‖f‖ ≤ c i)
    {h : IsRestricted.subring (R := S) c}
    (hfin : {t | coeff t (h : MvPowerSeries σ S) ≠ 0}.Finite)
    (hD : ∀ t, coeff t (h : MvPowerSeries σ S) ∈ D) :
    ∃ f, Φ f = h ∧ ‖f‖ ≤ ‖h‖ := by
  classical
  choose a ha han using fun t ↦ hC _ (hD t)
  choose x hx hxn using hX
  -- the lift `xᵗ` of the monomial `Xᵗ`
  set T : (σ →₀ ℕ) → IsRestricted.subring (R := R) d := fun t ↦ t.prod fun i n ↦ x i ^ n
  have hT (t : σ →₀ ℕ) : Φ (T t) = ⟨monomial t 1, isRestricted_monomial c t 1⟩ := by
    simp [T, map_finsuppProd, hx, mk_monomial_eq_algebraMap_mul_prod]
  -- `R` need not satisfy `‖1‖ = 1`, so only nonempty products are bounded factorwise
  have hTn {t : σ →₀ ℕ} (ht : t ≠ 0) : ‖T t‖ ≤ t.prod (c · ^ ·) :=
    (Finset.norm_prod_le' _ (Finsupp.support_nonempty_iff.mpr ht) _).trans
      (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i hi ↦
        (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
          (pow_le_pow_left₀ (norm_nonneg _) (hxn i) _))
  refine ⟨∑ t ∈ hfin.toFinset, a t * T t, ?_, ?_⟩
  · apply Subtype.ext
    ext s
    simp only [map_sum, map_mul, ha, hT, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul,
      coe_algebraMap_isRestrictedSubring, map_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset]
    split_ifs with hs
    · rfl
    · exact (not_not.mp hs).symm
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg h) fun t _ ↦
      le_trans ?_ (norm_coeff_mul_prod_le h t)
    rcases eq_or_ne t 0 with rfl | ht
    · simpa [T] using han 0
    · exact (norm_mul_le _ _).trans (mul_le_mul (han t) (hTn ht) (norm_nonneg _) (norm_nonneg _))

variable [CompleteSpace (IsRestricted.subring (R := R) d)]

/-- **Surjectivity from lifts of generators.** Let `Φ : R{Y/d} → S{X/c}` be a ring homomorphism
of Tate algebras that does not increase the Gauss norm, with `R{Y/d}` complete. If every constant
from a dense additive subgroup `D` of `S` and every variable `Xᵢ` is the image of an element of
no larger norm, then `Φ` is surjective. -/
theorem surjective_of_exists_lift (hΦ : ∀ f, ‖Φ f‖ ≤ ‖f‖) {D : AddSubgroup S}
    (hDense : Dense (D : Set S)) (hC : ∀ a ∈ D, ∃ f, Φ f = algebraMap S _ a ∧ ‖f‖ ≤ ‖a‖)
    (hX : ∀ i, ∃ f, Φ f = ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ ∧ ‖f‖ ≤ c i) :
    Function.Surjective Φ := by
  let Ψ := Φ.toAddMonoidHom.mkNormedAddGroupHom 1 fun f ↦ by
    rw [one_mul]
    exact hΦ f
  -- the polynomials with coefficients in `D`, which are dense
  set K := AddSubgroup.closure ((fun x : (σ →₀ ℕ) × S ↦
    (⟨monomial x.1 x.2, isRestricted_monomial c x.1 x.2⟩ : IsRestricted.subring (R := S) c)) ''
      (Set.univ ×ˢ (D : Set S)))
  have hK : Ψ.SurjectiveOnWith K 1 := by
    intro h hh
    -- an element of `K` has finitely many nonzero coefficients, all in `D`
    have hP : {t | coeff t (h : MvPowerSeries σ S) ≠ 0}.Finite ∧
        ∀ t, coeff t (h : MvPowerSeries σ S) ∈ D := by
      classical
      induction hh using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨⟨t, b⟩, ⟨-, hb⟩, rfl⟩ := hx
        refine ⟨(Set.finite_singleton t).subset fun s hs ↦ Set.mem_singleton_iff.mpr ?_,
          fun s ↦ ?_⟩
        · by_contra h'
          exact hs (by simp [coeff_monomial, h'])
        · simp only [coeff_monomial]
          split_ifs
          exacts [hb, D.zero_mem]
      | zero => exact ⟨by simp, fun _ ↦ by simp⟩
      | add x y _ _ hx hy =>
        refine ⟨(hx.1.union hy.1).subset fun s hs ↦ ?_, fun s ↦ ?_⟩
        · by_contra h'
          simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h'
          exact hs (by simp [h'.1, h'.2])
        · simpa using D.add_mem (hx.2 s) (hy.2 s)
      | neg x _ hx => exact ⟨by simpa using hx.1, fun s ↦ by simpa using D.neg_mem (hx.2 s)⟩
    obtain ⟨f, hf, hfn⟩ := exists_lift_of_finite hC hX hP.1 hP.2
    exact ⟨f, hf, by simpa using hfn⟩
  have hdense : K.topologicalClosure = ⊤ := by
    rw [eq_top_iff, ← SetLike.coe_subset_coe, AddSubgroup.topologicalClosure_coe,
      (dense_closure_monomial (c := c) hDense).closure_eq]
    exact fun _ _ ↦ Set.mem_univ _
  intro h
  obtain ⟨f, hf, -⟩ := controlled_closure_of_complete one_pos one_pos hK h (hdense ▸ trivial)
  exact ⟨f, hf⟩

end MvPowerSeries
