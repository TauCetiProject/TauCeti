/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.SupSeminorm

import TauCeti.RingTheory.Affinoid.Integral.Equation
import TauCeti.RingTheory.Algebraic.Basic
import TauCeti.RingTheory.Dagger.AnalyticSubst
import TauCeti.RingTheory.Dagger.FaithfullyFlat
import TauCeti.RingTheory.Dagger.NoetherNormalization
import TauCeti.RingTheory.Dagger.Noetherian
import TauCeti.RingTheory.Dagger.Weierstrass
import TauCeti.RingTheory.Ideal.KrullIntersection
import TauCeti.RingTheory.Ideal.Quotient.Integral
import TauCeti.RingTheory.RingHom.Flat

/-!
# Weak completeness of dagger algebras

Let `K` be a complete nontrivially normed ultrametric field and `C` a `K`-dagger algebra. This
file shows that `C` is *weakly complete*: for elements `x₁, …, xₙ ∈ C` with supremum seminorm
`|xᵢ|sup ≤ 1` there is exactly one `K`-algebra homomorphism `K⟨X₁, …, Xₙ⟩† → C` sending each
`Xᵢ` to `xᵢ`. Conversely every `K`-algebra homomorphism from the Monsky–Washnitzer algebra into
`C` sends the variables to elements of supremum seminorm at most `1`. So homomorphisms
`K⟨X⟩† → C` are the same as families of elements of the unit ball of `|·|sup`, and no continuity
needs to be imposed on them.

*Uniqueness.* Two homomorphisms agreeing on the variables agree modulo every power `m ^ k` of a
maximal ideal of `C`, since `C ⧸ m ^ k` is finite-dimensional over `K` and homomorphisms into it
are determined by the variables (`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral`).
Krull's intersection theorem (`Ideal.iInf_isMaximal_pow_eq_bot`) gives equality. This holds for
every noetherian target whose residue fields at maximal ideals are integral over `K`.

*Existence.* Choose a presentation `π : W_m ↠ C` with kernel `I`, and let `f ∈ C` with
`|f|sup ≤ 1`.

* The image of `f` in the affinoid algebra `T_m ⧸ I T_m` has supremum seminorm at most `1`, so
  it is a root of a monic polynomial over the Tate algebra `T_m` whose coefficients have Gauss
  norm at most `1` (`TauCeti.IsAffinoidAlgebra.exists_monic_aeval_eq_zero_supSeminorm_coeff_le`).
* This equation descends to `W_m`. The difference between it and the monic equation
  `(Y - g) ^ d` of a preimage `g` of `f` is a solution over `T_m` of a linear equation with
  coefficients in `W_m`. Since `T_m` is flat over `W_m`, it is a `T_m`-combination of solutions
  over `W_m` (`RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq_zero`), and approximating the
  coefficients of this combination by elements of the dense subring `W_m` gives a monic
  equation over `W_m` with coefficients of Gauss norm at most `1`.
* Such a polynomial `Q` is distinguished, so overconvergent Weierstrass division identifies
  `W_m[Y] ⧸ (Q)` with `K⟨X, Y⟩† ⧸ (Q)` (`TauCeti.Dagger.washnitzerAlgebra.polynomialQuotientEquiv`).
  Sending `Y` to `f` therefore extends `π` to `K⟨X, Y⟩† → C`.

Adjoining the elements one at a time and substituting variables
(`TauCeti.Dagger.washnitzerAlgebra.analyticSubst`) gives the homomorphism.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.lift`: the homomorphism `K⟨X⟩† → C` sending `Xᵢ` to `xᵢ`, for
  a dagger algebra `C` and elements with `|xᵢ|sup ≤ 1`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isNoetherianRing`: homomorphisms from
  `K⟨X⟩†` into a noetherian algebra whose residue fields are integral over `K` are determined by
  the variables; `TauCeti.Dagger.washnitzerAlgebra.algHom_ext` is the case of a dagger algebra.
* `TauCeti.Dagger.washnitzerAlgebra.supSeminorm_apply_X_le_one`: homomorphisms into a dagger
  algebra send the variables into the unit ball of `|·|sup`.
* `TauCeti.Dagger.washnitzerAlgebra.exists_monic_eval₂_eq_zero_of_supSeminorm_le_one`: for a
  presentation `π : W_n ↠ C`, an element of supremum seminorm at most `1` is a root of a monic
  polynomial over `W_n` whose coefficients have Gauss norm at most `1`.
* `TauCeti.Dagger.washnitzerAlgebra.lift_X`: the lift sends `Xᵢ` to `xᵢ`, and
  `TauCeti.Dagger.washnitzerAlgebra.lift_unique` says it is the only such homomorphism.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, 1.9.
* P. Monsky, G. Washnitzer, *Formal cohomology I*, Ann. of Math. 88 (1968), for weakly
  complete algebras.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries Polynomial

section Ext

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {B : Type*} [CommRing B] [Algebra K B]

/-- **Homomorphisms are determined by the variables.** Two `K`-algebra homomorphisms from the
Monsky–Washnitzer algebra in finitely many variables into a noetherian `K`-algebra whose residue
fields at maximal ideals are integral over `K` agree as soon as they agree on every variable. No
continuity is assumed. -/
theorem algHom_ext_of_isNoetherianRing [IsNoetherianRing B]
    (hB : ∀ m : Ideal B, m.IsMaximal → Algebra.IsIntegral K (B ⧸ m))
    {φ ψ : washnitzerAlgebra σ K →ₐ[K] B} (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  ext f
  -- By Krull's intersection theorem it suffices to compare the maps modulo every `m ^ k`.
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm k _
  -- Modulo `m ^ k` the two maps agree, since `B ⧸ m ^ k` is integral over `K`.
  have := (hB m hm).quotient_pow k
  have hk := algHom_ext_of_isIntegral (φ := (Ideal.Quotient.mkₐ K (m ^ k)).comp φ)
    (ψ := (Ideal.Quotient.mkₐ K (m ^ k)).comp ψ) fun i ↦ by simp [h i]
  rw [← Ideal.Quotient.eq]
  simpa using AlgHom.congr_fun hk f

/-- **Homomorphisms into a dagger algebra are determined by the variables.** -/
@[ext]
theorem algHom_ext [IsDaggerAlgebra K B] {φ ψ : washnitzerAlgebra σ K →ₐ[K] B}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ :=
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := B)
  algHom_ext_of_isNoetherianRing (fun m _ ↦
    have := IsDaggerAlgebra.finite_quotient_of_isMaximal K m
    inferInstance) h

end Ext

section Lift

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {C : Type*} [CommRing C] [Algebra K C]

local notation "W " σ:max => washnitzerAlgebra σ K
local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- **The variables map into the unit ball.** Every `K`-algebra homomorphism from the
Monsky–Washnitzer algebra into a dagger algebra sends each variable to an element of supremum
seminorm at most `1`. -/
theorem supSeminorm_apply_X_le_one [IsDaggerAlgebra K C] {σ : Type*} [Finite σ]
    (φ : W σ →ₐ[K] C) (i : σ) : supSeminorm K (φ (X σ K i)) ≤ 1 := by
  refine supSeminorm_le zero_le_one fun y ↦ ?_
  -- The pullback of a classical point of `C` is a classical point of `W`, with the same values.
  let := Ideal.Quotient.field y.asIdeal
  have := IsDaggerAlgebra.finite_quotient_of_isMaximal K y.asIdeal
  have hy : (y.asIdeal.comap φ).IsMaximal := by
    have h := ((Ideal.Quotient.mkₐ K y.asIdeal).comp φ).ker_isMaximal_of_isAlgebraic
    have hker : RingHom.ker ((Ideal.Quotient.mkₐ K y.asIdeal).comp φ) = y.asIdeal.comap φ := by
      ext
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rwa [hker] at h
  rw [← pointNorm_comap φ y hy]
  exact (pointNorm_le_norm _ _).trans (norm_X i).le

/-- The image of an element of supremum seminorm at most `1` in the completion `T_n ⧸ I T_n` of a
presentation `π : W_n ↠ C` with kernel `I` is a root of a monic polynomial over `T_n` with
coefficients of Gauss norm at most `1`. -/
private theorem exists_monic_eval_mem_map_toTate {n : ℕ} {π : W (Fin n) →ₐ[K] C}
    (hπ : Function.Surjective π) {g : W (Fin n)} (hg : supSeminorm K (π g) ≤ 1) :
    ∃ p : (T (Fin n))[X], p.Monic ∧
      p.eval (toTate (Fin n) K g) ∈ (RingHom.ker π).map (toTate (Fin n) K) ∧
      ∀ i, ‖p.coeff i‖ ≤ 1 := by
  have := IsDaggerAlgebra.of_surjective_washnitzerAlgebra π hπ
  set J := (RingHom.ker π).map (toTate (Fin n) K)
  have hB : IsAffinoidAlgebra K (T (Fin n) ⧸ J) := isAffinoidAlgebra_tate.quotient J
  -- The induced map `C → T_n ⧸ I T_n` pulls classical points back to classical points.
  let ι : C →ₐ[K] T (Fin n) ⧸ J :=
    (Ideal.quotientMapₐ J (toTate (Fin n) K) Ideal.le_comap_map).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hι : ι (π g) = Ideal.Quotient.mk J (toTate (Fin n) K g) := by simp [ι]
  have hsup : supSeminorm K (Ideal.Quotient.mk J (toTate (Fin n) K g)) ≤ 1 := by
    refine supSeminorm_le zero_le_one fun y ↦ ?_
    rw [← hι, ← pointNorm_comap ι y (hB.comap_isMaximal ι y.asIdeal)]
    exact (IsDaggerAlgebra.pointNorm_le_supSeminorm _ _).trans hg
  obtain ⟨p, hp, hpf, hpc⟩ :=
    (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).exists_monic_aeval_eq_zero_supSeminorm_coeff_le
      hB (Ideal.Quotient.mk J (toTate (Fin n) K g))
  refine ⟨p, hp, ?_, fun i ↦ ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq,
      ← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact hpf
  · rw [← TauCeti.MvPowerSeries.supSeminorm_eq_norm]
    exact (hpc i).trans (pow_le_one₀ (supSeminorm_nonneg _) hsup)

/-- Solutions over `T` of a linear equation with coefficients in `W` are limits of solutions
over `W`: as `T` is flat over `W`, a solution over `T` is a `T`-combination of solutions over `W`,
and the coefficients of the combination can be approximated in the dense subring `W`. -/
private theorem exists_sum_mul_eq_zero_norm_sub_lt {σ : Type*} [Finite σ] {ι : Type*}
    [Fintype ι] (f : ι → W σ) (x : ι → T σ) (hx : ∑ i, toTate σ K (f i) * x i = 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ x' : ι → W σ, ∑ i, f i * x' i = 0 ∧ ∀ i, ‖toTate σ K (x' i) - x i‖ < ε := by
  obtain ⟨k, a, y, hxy, ha⟩ :=
    RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq_zero faithfullyFlat_toTate.flat hx
  -- Approximate the `y j` by elements of `W`, to within `δ = ε / (1 + ∑ ‖a i j‖)`.
  set S := ∑ i, ∑ j, ‖a i j‖
  have hS : 0 ≤ S := by positivity
  have haS (i : ι) (j : Fin k) : ‖a i j‖ ≤ S :=
    (Finset.single_le_sum (f := fun j ↦ ‖a i j‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖)
        (fun _ _ ↦ by positivity) (Finset.mem_univ i))
  set δ := ε / (1 + S)
  have hδ : 0 < δ := by positivity
  have hSδ : S * δ < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  choose y' hy' using fun j ↦ denseRange_toTate.exists_dist_lt (y j) hδ
  refine ⟨fun i ↦ ∑ j, a i j * y' j, ?_, fun i ↦ ?_⟩
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp [← Finset.sum_mul, ha]
  · rw [hxy i, map_sum]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, ← Finset.sum_sub_distrib,
      ← mul_sub]
    refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hS hδ.le)
      fun j _ ↦ ?_).trans_lt hSδ
    calc ‖toTate σ K (a i j) * (toTate σ K (y' j) - y j)‖
        ≤ ‖a i j‖ * ‖toTate σ K (y' j) - y j‖ := by rw [← norm_toTate]; exact norm_mul_le _ _
      _ ≤ S * δ := by
        rw [← dist_eq_norm, dist_comm]
        exact mul_le_mul (haS i j) (hy' j).le dist_nonneg hS

omit [CompleteSpace K] in
/-- A monic polynomial `Y ^ d + ∑_{i < d} cᵢ Y ^ i` over `W` with `‖cᵢ‖ ≤ 1` has all coefficients
of Gauss norm at most `1`. -/
private theorem norm_coeff_X_pow_add_sum_le_one {σ : Type*} {d : ℕ} {c : Fin d → W σ}
    (hc : ∀ i, ‖c i‖ ≤ 1) (m : ℕ) : ‖(Polynomial.X ^ d +
      ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).coeff m‖ ≤ 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · split_ifs <;> simp
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
    split_ifs
    · exact hc i
    · simp

/-- If `g ∈ W` is a root modulo `I T` of a monic polynomial `p` over `T` of positive degree `d`,
then there are `cᵢ ∈ W`, each at distance less than `1` from the coefficient `pᵢ`, with
`g ^ d + ∑_{i < d} cᵢ g ^ i ∈ I`. -/
private theorem exists_pow_add_sum_mem_of_toTate {σ : Type*} [Finite σ] {I : Ideal (W σ)}
    {g : W σ} {p : (T σ)[X]} (hp : p.Monic) (hd0 : 0 < p.natDegree)
    (hpI : p.eval (toTate σ K g) ∈ I.map (toTate σ K)) :
    ∃ c : Fin p.natDegree → W σ, (∀ i : Fin p.natDegree, ‖toTate σ K (c i) - p.coeff i‖ < 1) ∧
      g ^ p.natDegree + ∑ i : Fin p.natDegree, g ^ (i : ℕ) * c i ∈ I := by
  set d := p.natDegree
  obtain ⟨r, h, rfl⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  rw [Ideal.submodule_span_eq, Ideal.map_span, ← Set.range_comp,
    Ideal.mem_span_range_iff_exists_fun] at hpI
  obtain ⟨e, he⟩ := hpI
  -- The equation `(Y - g) ^ d = 0` over `W` and the equation `p` over `T`.
  set q : (W σ)[X] := (Polynomial.X - Polynomial.C g) ^ d
  have hq : q.Monic := (monic_X_sub_C g).pow d
  have hqg : g ^ d + ∑ i : Fin d, g ^ (i : ℕ) * q.coeff i = 0 := by
    have h0 : q.eval g = 0 := by simp [q, zero_pow hd0.ne']
    rw [hq.as_sum, show q.natDegree = d by simp [q]] at h0
    simpa [eval_finsetSum, Finset.sum_range, mul_comm (q.coeff _)] using h0
  have hpx : p.eval (toTate σ K g) =
      toTate σ K g ^ d + ∑ i : Fin d, toTate σ K g ^ (i : ℕ) * p.coeff i := by
    conv_lhs => rw [hp.as_sum]
    simp [eval_finsetSum, Finset.sum_range, d, mul_comm (p.coeff _)]
  -- Their difference is a solution over `T` of a linear equation with coefficients in `W`.
  let f : Fin d ⊕ Fin r → W σ := Sum.elim (fun i ↦ g ^ (i : ℕ)) h
  let y : Fin d ⊕ Fin r → T σ :=
    Sum.elim (fun i ↦ p.coeff i - toTate σ K (q.coeff i)) (fun l ↦ -e l)
  have hfy : ∑ i, toTate σ K (f i) * y i = 0 := by
    have hqx := congrArg (toTate σ K) hqg
    simp only [map_add, map_pow, map_sum, map_mul, map_zero] at hqx
    simp only [Function.comp_apply, mul_comm (e _)] at he
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, f, y, map_pow, mul_sub,
      mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    linear_combination -hpx - he - hqx
  -- Perturb `(Y - g) ^ d` by an approximate solution over `W`.
  obtain ⟨y', hy'0, hy'⟩ := exists_sum_mul_eq_zero_norm_sub_lt f y hfy one_pos
  refine ⟨fun i : Fin d ↦ q.coeff i + y' (.inl i), fun i ↦ ?_, ?_⟩
  · convert hy' (.inl i) using 2
    simp only [y, map_add, Sum.elim_inl]
    ring
  · have hrel : ∑ i : Fin d, g ^ (i : ℕ) * y' (.inl i) = -∑ l, h l * y' (.inr l) := by
      simpa [Fintype.sum_sum_type, f, add_eq_zero_iff_eq_neg] using hy'0
    have hev : g ^ d + ∑ i : Fin d, g ^ (i : ℕ) * (q.coeff i + y' (.inl i)) =
        -∑ l, y' (.inr l) * h l := by
      simp only [mul_add, Finset.sum_add_distrib, mul_comm (y' _)]
      linear_combination hqg + hrel
    rw [hev]
    exact neg_mem (Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩))

/-- **Descent of small integral equations.** If `g ∈ W` is a root modulo `I T` of a monic
polynomial over `T` with coefficients of Gauss norm at most `1`, then it is a root modulo `I` of a
monic polynomial over `W` with coefficients of Gauss norm at most `1`. -/
private theorem exists_monic_eval_mem_of_toTate {σ : Type*} [Finite σ] {I : Ideal (W σ)}
    {g : W σ} {p : (T σ)[X]} (hp : p.Monic) (hpI : p.eval (toTate σ K g) ∈ I.map (toTate σ K))
    (hpc : ∀ i, ‖p.coeff i‖ ≤ 1) :
    ∃ Q : (W σ)[X], Q.Monic ∧ Q.eval g ∈ I ∧ ∀ i, ‖Q.coeff i‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos p.natDegree with hd0 | hd0
  · -- An equation of degree zero forces `I = W`.
    rw [hp.natDegree_eq_zero] at hd0
    rw [hd0, eval_one] at hpI
    have hI : I = ⊤ := by
      rw [← Ideal.comap_map_toTate I, (Ideal.eq_top_iff_one _).mpr hpI, Ideal.comap_top]
    exact ⟨1, monic_one, by simp [hI], fun i ↦ by
      rw [Polynomial.coeff_one]; split_ifs <;> simp⟩
  obtain ⟨c, hcp, hcI⟩ := exists_pow_add_sum_mem_of_toTate hp hd0 hpI
  have hc (i : Fin p.natDegree) : ‖c i‖ ≤ 1 := by
    rw [← norm_toTate, ← add_sub_cancel (p.coeff i) (toTate σ K (c i))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hpc i) (hcp i).le)
  refine ⟨Polynomial.X ^ p.natDegree + ∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ),
    monic_X_pow_add (degree_sum_fin_lt c), ?_, norm_coeff_X_pow_add_sum_le_one hc⟩
  simpa [eval_finsetSum, mul_comm (c _)] using hcI

/-- **Small integral equations.** Let `π : W_n ↠ C` be a presentation. An element `f ∈ C` with
`|f|sup ≤ 1` is a root of a monic polynomial over `W_n`, acting on `C` through `π`, whose
coefficients have Gauss norm at most `1`. -/
theorem exists_monic_eval₂_eq_zero_of_supSeminorm_le_one {n : ℕ} {π : W (Fin n) →ₐ[K] C}
    (hπ : Function.Surjective π) {f : C} (hf : supSeminorm K f ≤ 1) :
    ∃ Q : (W (Fin n))[X], Q.Monic ∧ Q.eval₂ (π : W (Fin n) →+* C) f = 0 ∧
      ∀ i, ‖Q.coeff i‖ ≤ 1 := by
  obtain ⟨g, rfl⟩ := hπ f
  obtain ⟨p, hp, hpI, hpc⟩ := exists_monic_eval_mem_map_toTate hπ hf
  obtain ⟨Q, hQ, hQI, hQc⟩ := exists_monic_eval_mem_of_toTate hp hpI hpc
  refine ⟨Q, hQ, ?_, hQc⟩
  have h := eval₂_at_apply (p := Q) (π : W (Fin n) →+* C) g
  rw [RingHom.coe_coe] at h
  rw [h, RingHom.mem_ker.mp hQI]

/-- **Adjoining a root of a small monic equation.** If `f ∈ C` is a root of a monic polynomial
over `W`, acting through `ψ : W → C`, whose coefficients have Gauss norm at most `1`, then `ψ`
extends to `K⟨X, Y⟩† → C` sending the new variable `Y` to `f`. -/
private theorem exists_algHom_comp_optionC_eq {τ : Type*} (ψ : W τ →ₐ[K] C) {f : C}
    {Q : (W τ)[X]} (hQ : Q.Monic) (hQc : ∀ i, ‖Q.coeff i‖ ≤ 1)
    (hQf : Q.eval₂ (ψ : W τ →+* C) f = 0) :
    ∃ ψ' : W (Option τ) →ₐ[K] C, ψ'.comp optionC = ψ ∧ ψ' (X (Option τ) K none) = f := by
  have hm : Q.IsMonicOfDegree Q.natDegree := ⟨rfl, hQ⟩
  -- `Q` is distinguished at the unit radius, so Weierstrass division applies to it.
  have hd : PowerSeries.IsDistinguished 1 Q.natDegree
      (Q.map (toTate τ K).toRingHom : PowerSeries (T τ)) :=
    PowerSeries.isDistinguished_of_isMonicOfDegree one_pos
      ⟨by rw [hQ.natDegree_map], hQ.map _⟩ fun k _ ↦ by
        simpa [Polynomial.coeff_map, norm_toTate] using hQc k
  let e := polynomialQuotientEquiv hd hm
  let g : AdjoinRoot Q →ₐ[K] C := AdjoinRoot.liftAlgHom Q ψ f hQf
  refine ⟨(g.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ K _), AlgHom.ext fun a ↦ ?_, ?_⟩
  · have : e.symm (Ideal.Quotient.mk _ (optionC a)) = AdjoinRoot.of Q a := by
      rw [AlgEquiv.symm_apply_eq, ← AdjoinRoot.mk_C, polynomialQuotientEquiv_mk,
        polynomialToOption_C]
    simp [this, g]
  · have : e.symm (Ideal.Quotient.mk _ (X (Option τ) K none)) = AdjoinRoot.root Q := by
      rw [AlgEquiv.symm_apply_eq, ← AdjoinRoot.mk_X, polynomialQuotientEquiv_mk,
        polynomialToOption_X]
    simp [this, g]

/-- Elements of supremum seminorm at most `1` are, after adjoining finitely many variables to a
presentation `π : W_n ↠ C`, images of variables. -/
private theorem exists_algHom_forall_mem {n : ℕ} {π : W (Fin n) →ₐ[K] C}
    (hπ : Function.Surjective π) (s : Finset C) (hs : ∀ c ∈ s, supSeminorm K c ≤ 1) :
    ∃ (τ : Type) (_ : Finite τ) (ι : W (Fin n) →ₐ[K] W τ) (φ : W τ →ₐ[K] C),
      (∀ a, ‖ι a‖ ≤ ‖a‖) ∧ φ.comp ι = π ∧ ∀ c ∈ s, ∃ j, φ (X τ K j) = c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Fin n, inferInstance, AlgHom.id K _, π, fun _ ↦ le_rfl, rfl, by simp⟩
  | insert c s _ ih =>
    obtain ⟨τ, _, ι, φ, hι, hφι, hmem⟩ := ih fun c' h ↦ hs c' (Finset.mem_insert_of_mem h)
    obtain ⟨Q, hQ, hQf, hQc⟩ :=
      exists_monic_eval₂_eq_zero_of_supSeminorm_le_one hπ (hs c (Finset.mem_insert_self c s))
    -- The equation of `c` over `W_n` is also an equation over `W_τ`, through `ι`.
    obtain ⟨ψ, hψ, hψc⟩ := exists_algHom_comp_optionC_eq φ (f := c)
      (Q := Q.map (ι : W (Fin n) →+* W τ)) (hQ.map _)
      (fun i ↦ by rw [Polynomial.coeff_map]; exact (hι _).trans (hQc i))
      (by rw [eval₂_map, ← AlgHom.comp_toRingHom, hφι]; exact hQf)
    refine ⟨Option τ, inferInstance, optionC.comp ι, ψ, fun a ↦ ?_, ?_, fun c' hc' ↦ ?_⟩
    · simpa [norm_optionC] using hι a
    · rw [← AlgHom.comp_assoc, hψ, hφι]
    · rcases Finset.mem_insert.mp hc' with rfl | hc'
      · exact ⟨none, hψc⟩
      · obtain ⟨j, hj⟩ := hmem c' hc'
        exact ⟨some j, by rw [← optionC_X, ← AlgHom.comp_apply, hψ, hj]⟩

private theorem exists_algHom_apply_X [IsDaggerAlgebra K C] {σ : Type*} [Finite σ] (x : σ → C)
    (hx : ∀ i, supSeminorm K (x i) ≤ 1) : ∃ φ : W σ →ₐ[K] C, ∀ i, φ (X σ K i) = x i := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨n, π, hπ⟩ := IsDaggerAlgebra.exists_surjective (K := K) (A := C)
  obtain ⟨τ, _, -, φ, -, -, hmem⟩ :=
    exists_algHom_forall_mem hπ (Finset.univ.image x) (by simpa using hx)
  choose j hj using fun i ↦ hmem (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))
  -- Substitute `X (j i)` for `Xᵢ`.
  let e := Fintype.equivFin σ
  let s : W (Fin (Fintype.card σ)) →ₐ[K] W τ :=
    analyticSubst (fun l ↦ X τ K (j (e.symm l))) fun l ↦ by rw [norm_toTate, norm_X]
  refine ⟨(φ.comp s).comp (renameAlgEquiv e).toAlgHom, fun i ↦ ?_⟩
  simp [s, analyticSubst_X, hj]

/-- **Weak completeness of dagger algebras.** For elements `xᵢ` of a dagger algebra `C` with
`|xᵢ|sup ≤ 1`, the `K`-algebra homomorphism `K⟨X⟩† → C` sending each variable `Xᵢ` to `xᵢ`. It is
the only one, by `TauCeti.Dagger.washnitzerAlgebra.algHom_ext`. -/
noncomputable def lift [IsDaggerAlgebra K C] {σ : Type*} [Finite σ] (x : σ → C)
    (hx : ∀ i, supSeminorm K (x i) ≤ 1) : W σ →ₐ[K] C :=
  (exists_algHom_apply_X x hx).choose

/-- The lift sends the variable `Xᵢ` to `xᵢ`. -/
@[simp]
theorem lift_X [IsDaggerAlgebra K C] {σ : Type*} [Finite σ] (x : σ → C)
    (hx : ∀ i, supSeminorm K (x i) ≤ 1) (i : σ) : lift x hx (X σ K i) = x i :=
  (exists_algHom_apply_X x hx).choose_spec i

/-- The lift is the only homomorphism sending each variable `Xᵢ` to `xᵢ`. -/
theorem lift_unique [IsDaggerAlgebra K C] {σ : Type*} [Finite σ] {x : σ → C}
    {hx : ∀ i, supSeminorm K (x i) ≤ 1} (φ : W σ →ₐ[K] C) (h : ∀ i, φ (X σ K i) = x i) :
    φ = lift x hx :=
  algHom_ext fun i ↦ by rw [h, lift_X]

/-- Every homomorphism into a dagger algebra is the lift of its values on the variables. -/
@[simp]
theorem lift_apply_X_eq [IsDaggerAlgebra K C] {σ : Type*} [Finite σ] (φ : W σ →ₐ[K] C) :
    lift (fun i ↦ φ (X σ K i)) (supSeminorm_apply_X_le_one φ) = φ :=
  (lift_unique φ fun _ ↦ rfl).symm

end Lift

end TauCeti.Dagger.washnitzerAlgebra
