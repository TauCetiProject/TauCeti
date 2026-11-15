/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Moments
public import TauCeti.Probability.Distributions.Gaussian.MomentRecursion
public import TauCeti.LinearAlgebra.Matrix.Permanent
import TauCeti.MeasureTheory.Integral.Bochner.Star
import TauCeti.Data.Finset.Sum
import TauCeti.Algebra.BigOperators.Fin

/-!
# Wick's formula for proper complex Gaussian vectors

Centered products of proper complex Gaussian coordinates contract only with conjugated
coordinates. Iterating this recursion gives the permanent of the cross-covariance matrix
when the two degrees agree; moments of unequal holomorphic and antiholomorphic degree vanish.
Coordinates may repeat, and the covariance may be singular. The noncentered formula sums over
partial matchings, multiplying by the means at unpaired positions. `HasLaw` versions apply the
formulas directly to random vectors on an arbitrary measurable sample space.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ComplexOrder ComplexConjugate

namespace TauCeti.Probability

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι]

/-- Any finite product of affinely shifted coordinates and their conjugates is
integrable under a proper complex Gaussian law. -/
theorem integrable_prod_mul_prod_conj_sub_properComplexGaussianMeasure
    (m c : ι → ℂ) (C : Matrix ι ι ℂ) (s : Finset α) (t : Finset β)
    (f : α → ι) (g : β → ι) :
    Integrable (fun z ↦ (∏ i ∈ s, (z (f i) - c (f i))) *
      ∏ j ∈ t, star (z (g j) - c (g j))) (properComplexGaussianMeasure m C) := by
  classical
  let L : α ⊕ β → (ι → ℂ) →L[ℝ] ℂ := Sum.elim
    (fun i ↦ ContinuousLinearMap.proj (f i))
    (fun j ↦ Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (g j)))
  simpa [L, Finset.prod_disjSum, map_sub, sub_eq_add_neg] using
    IsGaussian.integrable_prod_clm (properComplexGaussianMeasure m C)
      (s.disjSum t) L (fun i ↦ -L i c)

private theorem integral_clm_mul_prod_sub_properComplexGaussianMeasure
    (m : ι → ℂ) (C : Matrix ι ι ℂ) [DecidableEq α] (s : Finset α)
    (L₀ : (ι → ℂ) →L[ℝ] ℂ) (L : α → (ι → ℂ) →L[ℝ] ℂ) :
    (∫ z, L₀ (z - m) * ∏ i ∈ s, L i (z - m) ∂properComplexGaussianMeasure m C) =
      ∑ i ∈ s, (∫ z, L₀ (z - m) * L i (z - m) ∂properComplexGaussianMeasure m C) *
        ∫ z, ∏ j ∈ s.erase i, L j (z - m) ∂properComplexGaussianMeasure m C := by
  let e := complexToRealEuclidean ι
  have hpush (F : (ι → ℂ) → ℂ) (hF : Continuous F) :
      ∫ z, F (z - m) ∂properComplexGaussianMeasure m C =
        ∫ x, F (e.symm (x - e m))
          ∂multivariateGaussian (e m) (complexGaussianRealCovariance C) := by
    rw [properComplexGaussianMeasure_def, integral_map (by fun_prop) (by fun_prop)]
    simp only [e, map_sub, ContinuousLinearEquiv.symm_apply_apply]
  rw [hpush (fun z ↦ L₀ z * ∏ i ∈ s, L i z) (by fun_prop)]
  have hpair (i : α) := hpush (fun z ↦ L₀ z * L i z) (by fun_prop)
  have hprod (t : Finset α) := hpush (fun z ↦ ∏ i ∈ t, L i z) (by fun_prop)
  simp_rw [hpair, hprod]
  exact integral_clm_mul_prod_sub_multivariateGaussian (e m)
    (complexGaussianRealCovariance C) s (L₀.comp e.symm.toContinuousLinearMap)
      (fun i ↦ (L i).comp e.symm.toContinuousLinearMap)

/-- The complex Gaussian contraction recursion. A distinguished centered coordinate pairs
with each conjugated coordinate, and has zero contraction with the holomorphic factors. -/
theorem integral_sub_mul_prod_mul_prod_conj_sub_properComplexGaussianMeasure
    (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → ι) (g : β → ι) (k : ι) :
    (∫ z, (z k - m k) * (∏ i ∈ s, (z (f i) - m (f i))) *
      ∏ j ∈ t, star (z (g j) - m (g j)) ∂properComplexGaussianMeasure m C) =
      ∑ j ∈ t, C k (g j) * ∫ z, (∏ i ∈ s, (z (f i) - m (f i))) *
        ∏ l ∈ t.erase j, star (z (g l) - m (g l)) ∂properComplexGaussianMeasure m C := by
  classical
  let L : α ⊕ β → (ι → ℂ) →L[ℝ] ℂ := Sum.elim
    (fun i ↦ ContinuousLinearMap.proj (f i))
    (fun j ↦ Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (g j)))
  have hp (z : ι → ℂ) (u : Finset (α ⊕ β)) :
      (∏ i ∈ u, L i (z - m)) =
        (∏ i ∈ u.toLeft, (z (f i) - m (f i))) *
          ∏ j ∈ u.toRight, star (z (g j) - m (g j)) := by
    rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
    rfl
  have hc (a : α ⊕ β) :
      (∫ z, (z k - m k) * L a (z - m) ∂properComplexGaussianMeasure m C) =
        Sum.elim (fun _ ↦ 0) (fun j ↦ C k (g j)) a := by
    cases a with
    | inl i => exact integral_mul_sub_properComplexGaussianMeasure m hC k (f i)
    | inr j => exact integral_mul_conj_sub_properComplexGaussianMeasure m hC k (g j)
  have h := integral_clm_mul_prod_sub_properComplexGaussianMeasure m C (s.disjSum t)
    (ContinuousLinearMap.proj k) L
  simp only [ContinuousLinearMap.proj_apply, Pi.sub_apply, hc, hp, sum_disjSum,
    Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, zero_add,
    toLeft_disjSum, toRight_disjSum] at h
  simpa [Finset.toLeft_erase_inr, Finset.toRight_erase_inr, mul_assoc] using h

/-- A nonempty purely holomorphic centered moment of a proper complex Gaussian vanishes. -/
theorem integral_prod_sub_properComplexGaussianMeasure_eq_zero
    (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    (s : Finset α) (hs : s.Nonempty) (f : α → ι) :
    (∫ z, ∏ i ∈ s, (z (f i) - m (f i)) ∂properComplexGaussianMeasure m C) = 0 := by
  classical
  obtain ⟨k, hk⟩ := hs
  have h := integral_sub_mul_prod_mul_prod_conj_sub_properComplexGaussianMeasure m hC
    (s.erase k) (∅ : Finset α) f f (f k)
  simp only [prod_empty, mul_one, sum_empty] at h
  convert h using 1
  congr 1
  funext z
  exact (mul_prod_erase s (fun i ↦ z (f i) - m (f i)) hk).symm

private theorem integral_prod_mul_prod_conj_sub_fin_succ
    (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) {n r : ℕ}
    (f : Fin (n + 1) → ι) (g : Fin (r + 1) → ι) :
    (∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
      ∂properComplexGaussianMeasure m C) =
      ∑ j, C (f 0) (g j) * ∫ z, (∏ i : Fin n, (z (f i.succ) - m (f i.succ))) *
        ∏ l : Fin r, star (z (g (Equiv.swap 0 j l.succ)) -
          m (g (Equiv.swap 0 j l.succ))) ∂properComplexGaussianMeasure m C := by
  have h := integral_sub_mul_prod_mul_prod_conj_sub_properComplexGaussianMeasure m hC
    (univ : Finset (Fin n)) (univ : Finset (Fin (r + 1))) (fun i ↦ f i.succ) g (f 0)
  simpa only [← Fin.prod_univ_swap_succ, Fin.prod_univ_succ] using h

private theorem integral_prod_mul_prod_conj_sub_fin_eq_permanent
    (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (n : ℕ)
    (f g : Fin n → ι) :
    (∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
      ∂properComplexGaussianMeasure m C) =
      (Matrix.of fun i j ↦ C (f j) (g i)).permanent := by
  induction n with
  | zero => simp [Matrix.permanent_isEmpty]
  | succ n ih =>
    rw [integral_prod_mul_prod_conj_sub_fin_succ m hC, Matrix.permanent_fin_succ]
    exact sum_congr rfl fun j _ ↦ congrArg (C (f 0) (g j) * ·)
      (ih (fun i ↦ f i.succ) (fun l ↦ g (Equiv.swap 0 j l.succ)))

private theorem integral_prod_mul_prod_conj_sub_eq_permanent
    [Fintype α] [DecidableEq α] (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    (f g : α → ι) :
    (∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
      ∂properComplexGaussianMeasure m C) =
      (Matrix.of fun i j ↦ C (f j) (g i)).permanent := by
  let e := Fintype.equivFin α
  have hp (h : α → ℂ) : ∏ i, h i = ∏ j, h (e.symm j) := (e.symm.prod_comp h).symm
  calc
    _ = ∫ z, (∏ i, (z (f (e.symm i)) - m (f (e.symm i)))) *
        ∏ j, star (z (g (e.symm j)) - m (g (e.symm j)))
          ∂properComplexGaussianMeasure m C := by simp_rw [hp]
    _ = ((Matrix.of fun i j ↦ C (f j) (g i)).submatrix e.symm e.symm).permanent :=
      integral_prod_mul_prod_conj_sub_fin_eq_permanent m hC _ _ _
    _ = _ := Matrix.permanent_submatrix_equiv _ e.symm

private theorem integral_prod_mul_prod_conj_sub_fin_eq_zero
    (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (n r : ℕ) (hnr : n ≠ r)
    (f : Fin n → ι) (g : Fin r → ι) :
    (∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
      ∂properComplexGaussianMeasure m C) = 0 := by
  induction n generalizing r with
  | zero =>
    have hr : (univ : Finset (Fin r)).Nonempty := by
      exact univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hnr.symm))
    simp only [Fin.prod_univ_zero, one_mul, ← star_prod, integral_star,
      integral_prod_sub_properComplexGaussianMeasure_eq_zero m hC univ hr g, star_zero]
  | succ n ih =>
    cases r with
    | zero =>
      simpa using integral_prod_sub_properComplexGaussianMeasure_eq_zero m hC
        univ (univ_nonempty) f
    | succ r =>
      rw [integral_prod_mul_prod_conj_sub_fin_succ m hC]
      apply sum_eq_zero
      intro j _
      rw [ih r (by omega), mul_zero]

/-- Centered moments with different holomorphic and antiholomorphic degrees vanish.
The position types may have different cardinalities, and coordinates may repeat. -/
theorem integral_prod_mul_prod_conj_sub_properComplexGaussianMeasure_eq_zero
    [Fintype α] [Fintype β] (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    (hαβ : Fintype.card α ≠ Fintype.card β) (f : α → ι) (g : β → ι) :
    (∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
      ∂properComplexGaussianMeasure m C) = 0 := by
  let e := Fintype.equivFin α
  let d := Fintype.equivFin β
  have hp (h : α → ℂ) : ∏ i, h i = ∏ j, h (e.symm j) := (e.symm.prod_comp h).symm
  have hq (h : β → ℂ) : ∏ i, h i = ∏ j, h (d.symm j) := (d.symm.prod_comp h).symm
  simp_rw [hp, hq]
  exact integral_prod_mul_prod_conj_sub_fin_eq_zero m hC _ _ hαβ _ _

/-- **The complex Wick formula.** A centered product of proper complex Gaussian coordinates
and conjugated coordinates is the sum of covariance products over all bijections between their
positions. For unequal degrees the sum is empty; for equal degrees it is a permanent.
The empty moment is one. Singular covariance matrices and repeated coordinates are allowed. -/
theorem integral_prod_mul_prod_conj_sub_properComplexGaussianMeasure
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    (f : α → ι) (g : β → ι) :
    (∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
      ∂properComplexGaussianMeasure m C) = ∑ e : α ≃ β, ∏ i, C (f i) (g (e i)) := by
  classical
  by_cases h : Fintype.card α = Fintype.card β
  · let e := Fintype.equivOfCardEq h
    have hp (z : ι → ℂ) :
        ∏ j, star (z (g j) - m (g j)) = ∏ i, star (z (g (e i)) - m (g (e i))) :=
      (e.prod_comp _).symm
    simp_rw [hp]
    rw [integral_prod_mul_prod_conj_sub_eq_permanent m hC]
    unfold Matrix.permanent
    refine Fintype.sum_equiv (Equiv.equivCongr (Equiv.refl α) e) _ _ fun σ ↦ ?_
    simp [Equiv.equivCongr]
  · have : IsEmpty (α ≃ β) := ⟨fun e ↦ h (Fintype.card_congr e)⟩
    rw [integral_prod_mul_prod_conj_sub_properComplexGaussianMeasure_eq_zero m hC h]
    simp

/-- The noncentered complex Wick formula. Choose the positions contracted by covariance,
pair those positions bijectively, and multiply by the means at all remaining positions. -/
theorem integral_prod_mul_prod_conj_properComplexGaussianMeasure
    [DecidableEq α] [DecidableEq β] (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    (s : Finset α) (t : Finset β) (f : α → ι) (g : β → ι) :
    (∫ z, (∏ i ∈ s, z (f i)) * ∏ j ∈ t, star (z (g j))
      ∂properComplexGaussianMeasure m C) =
      ∑ p ∈ s.powerset, ∑ q ∈ t.powerset,
        ((∏ i ∈ s \ p, m (f i)) * ∏ j ∈ t \ q, star (m (g j))) *
          ∑ e : p ≃ q, ∏ i : p, C (f i) (g (e i)) := by
  have hterm (p : Finset α) (q : Finset β) :=
    integrable_prod_mul_prod_conj_sub_properComplexGaussianMeasure m m C p q f g
  have hexpand (z : ι → ℂ) :
      (∏ i ∈ s, z (f i)) * (∏ j ∈ t, star (z (g j))) =
        ∑ p ∈ s.powerset, ∑ q ∈ t.powerset,
          ((∏ i ∈ s \ p, m (f i)) * ∏ j ∈ t \ q, star (m (g j))) *
            ((∏ i ∈ p, (z (f i) - m (f i))) *
              ∏ j ∈ q, star (z (g j) - m (g j))) := by
    have hs := prod_add (fun i ↦ z (f i) - m (f i)) (fun i ↦ m (f i)) s
    have ht := prod_add (fun j ↦ star (z (g j) - m (g j))) (fun j ↦ star (m (g j))) t
    simp only [sub_add_cancel] at hs
    simp only [star_sub, sub_add_cancel] at ht
    rw [hs, ht, sum_mul]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    simp only [star_sub]
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun p _ ↦ integrable_finsetSum _
    (fun q _ ↦ (hterm p q).const_mul _))]
  apply sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ ↦ (hterm p q).const_mul _)]
  apply sum_congr rfl
  intro q _
  rw [integral_const_mul]
  congr 1
  have hp (z : ι → ℂ) := p.prod_attach (fun i ↦ z (f i) - m (f i))
  have hq (z : ι → ℂ) := q.prod_attach (fun j ↦ star (z (g j) - m (g j)))
  have h := integral_prod_mul_prod_conj_sub_properComplexGaussianMeasure m hC
    (fun i : p ↦ f i) (fun j : q ↦ g j)
  simpa only [univ_eq_attach, hp, hq] using h

/-- Products of squared moduli of centered coordinates have moments equal to the permanent
of their covariance submatrix, including repeated coordinates. -/
theorem integral_prod_norm_sq_sub_properComplexGaussianMeasure
    [Fintype α] [DecidableEq α] (m : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef)
    (f : α → ι) :
    (∫ z, ∏ i, (‖z (f i) - m (f i)‖ ^ 2 : ℂ) ∂properComplexGaussianMeasure m C) =
      (C.submatrix f f).permanent := by
  have hp (z : ι → ℂ) :
      (∏ i, (‖z (f i) - m (f i)‖ ^ 2 : ℂ)) =
        (∏ i, (z (f i) - m (f i))) * ∏ i, star (z (f i) - m (f i)) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [hp]
  rw [integral_prod_mul_prod_conj_sub_eq_permanent m hC]
  exact Matrix.permanent_transpose (C.submatrix f f)

/-- Mixed moments of a standard circular complex Gaussian: equal degrees give a factorial,
and unequal degrees give zero. In particular its holomorphic moments of positive degree vanish. -/
@[simp]
theorem integral_pow_mul_conj_pow_properComplexGaussianScalar (n r : ℕ) :
    (∫ z, z ^ n * conj z ^ r ∂properComplexGaussianScalar) =
      if n = r then (n.factorial : ℂ) else 0 := by
  rw [properComplexGaussianScalar_def,
    integral_map (measurable_pi_apply ()).aemeasurable (by fun_prop)]
  split_ifs with h
  · subst r
    simpa [Matrix.permanent, Fintype.card_perm] using
      integral_prod_mul_prod_conj_sub_fin_eq_permanent (fun _ : Unit ↦ (0 : ℂ))
        (Matrix.PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef) n
        (fun _ ↦ ()) (fun _ ↦ ())
  · simpa using integral_prod_mul_prod_conj_sub_fin_eq_zero (fun _ : Unit ↦ (0 : ℂ))
      (Matrix.PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef) n r h
      (fun _ ↦ ()) (fun _ ↦ ())

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability
open scoped ComplexOrder

variable {Ω ι α β : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ} {C : Matrix ι ι ℂ}

/-- Affinely shifted coordinate products and their conjugates are integrable for a random
vector with a proper complex Gaussian law, on any underlying sample space. -/
theorem integrable_prod_mul_prod_conj_sub_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (c : ι → ℂ)
    (s : Finset α) (t : Finset β) (f : α → ι) (g : β → ι) :
    Integrable (fun ω ↦ (∏ i ∈ s, (Z ω (f i) - c (f i))) *
      ∏ j ∈ t, star (Z ω (g j) - c (g j))) P :=
  hZ.integrable_comp
    (TauCeti.Probability.integrable_prod_mul_prod_conj_sub_properComplexGaussianMeasure
      m c C s t f g)

/-- The complex Wick formula for a random vector with a proper complex Gaussian law.
The bijections pair holomorphic with antiholomorphic positions, including repeated coordinates. -/
theorem integral_prod_mul_prod_conj_sub_properComplexGaussianMeasure
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef)
    (f : α → ι) (g : β → ι) :
    (∫ ω, (∏ i, (Z ω (f i) - m (f i))) * ∏ j, star (Z ω (g j) - m (g j)) ∂P) =
      ∑ e : α ≃ β, ∏ i, C (f i) (g (e i)) := by
  calc
    _ = ∫ z, (∏ i, (z (f i) - m (f i))) * ∏ j, star (z (g j) - m (g j))
        ∂properComplexGaussianMeasure m C := hZ.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_prod_mul_prod_conj_sub_properComplexGaussianMeasure
      m hC f g

/-- The noncentered Wick formula for a proper complex Gaussian random vector. Every partial
matching contributes its covariance product times the means at the unpaired positions. -/
theorem integral_prod_mul_prod_conj_properComplexGaussianMeasure
    [DecidableEq α] [DecidableEq β]
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef)
    (s : Finset α) (t : Finset β) (f : α → ι) (g : β → ι) :
    (∫ ω, (∏ i ∈ s, Z ω (f i)) * ∏ j ∈ t, star (Z ω (g j)) ∂P) =
      ∑ p ∈ s.powerset, ∑ q ∈ t.powerset,
        ((∏ i ∈ s \ p, m (f i)) * ∏ j ∈ t \ q, star (m (g j))) *
          ∑ e : p ≃ q, ∏ i : p, C (f i) (g (e i)) := by
  calc
    _ = ∫ z, (∏ i ∈ s, z (f i)) * ∏ j ∈ t, star (z (g j))
        ∂properComplexGaussianMeasure m C := hZ.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_prod_mul_prod_conj_properComplexGaussianMeasure
      m hC s t f g

end ProbabilityTheory.HasLaw
