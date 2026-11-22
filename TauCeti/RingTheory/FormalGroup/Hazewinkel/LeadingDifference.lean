/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hazewinkel.NSMul
public import TauCeti.RingTheory.FormalGroup.Logarithm.LeadingDifference
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic

/-!
# The leading difference of two Hazewinkel formal group laws

Let `p` be a prime and let `F_v` be Hazewinkel's formal group law
(`TauCeti.hazewinkelIntegralFormalGroup p v`) at a family `v = (v₁, v₂, …)` of elements of a
commutative ring `R`. If `v` and `w` agree below the index `n`, then `F_v` and `F_w` agree below
degree `pⁿ` (`TauCeti.coeff_hazewinkelIntegralFormalGroup_congr`), and their degree-`pⁿ` parts
differ by the Lazard cocycle `C_(pⁿ) = ((X + Y)^(pⁿ) - X^(pⁿ) - Y^(pⁿ)) / p`:

  `F_v - F_w ≡ (wₙ - vₙ) C_(pⁿ)` modulo terms of degree greater than `pⁿ`

(`TauCeti.homogeneousComponent_hazewinkelIntegralFormalGroup_sub`). Over a `ℚ`-algebra this is
read off the logarithms: `log F_v - log F_w ≡ ((vₙ - wₙ) / p) X^(pⁿ)`, and a change `a X^N` of the
logarithm changes the degree-`N` part of the law by `-a ((X + Y)^N - X^N - Y^N)`
(`FormalGroup.homogeneousComponent_sub_of_log_sub`). The integral identity follows by comparison
with the universal family over `ℤ[v₁, v₂, …]`.

Since `r C_(pⁿ) = 0` forces `r = 0` over every commutative ring, the family `v` is determined by the
formal group law `F_v`, even over rings with torsion
(`TauCeti.hazewinkelIntegralFormalGroup_injective`). The same identity lets one read the generators
`vₙ` off the law one at a time, which is how `TauCeti.RingTheory.FormalGroup.Typical.Universal`
shows that every `p`-typical law over a `ℤ_(p)`-algebra is Hazewinkel's.

## Main results

* `TauCeti.hazewinkelLogCoeff_sub_of_forall_lt`: `mₙ(v) - mₙ(w) = (vₙ - wₙ) / p` when `v` and `w`
  agree below `n`.
* `TauCeti.homogeneousComponent_hazewinkelFormalGroup_sub`,
  `TauCeti.homogeneousComponent_hazewinkelIntegralFormalGroup_sub`: the degree-`pⁿ` part of
  `F_v - F_w` is `(wₙ - vₙ) C_(pⁿ)`.
* `TauCeti.hazewinkelIntegralFormalGroup_injective`: `v ↦ F_v` is injective over every commutative
  ring.

## References

* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §§2–5.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), Appendix A2.1.
-/

public section

noncomputable section

open MvPowerSeries Finset

namespace TauCeti

section Rational

variable {K : Type*} [CommRing K] [Algebra ℚ K] {p : ℕ}

/-- If `v` and `w` agree below `n`, Hazewinkel's logarithm coefficients satisfy
`mₙ(v) - mₙ(w) = (vₙ - wₙ) / p`. -/
theorem hazewinkelLogCoeff_sub_of_forall_lt {v w : ℕ+ → K} (n : ℕ+) (hvw : ∀ i < n, v i = w i) :
    hazewinkelLogCoeff p v n - hazewinkelLogCoeff p w n = (p : ℚ)⁻¹ • (v n - w n) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero n.ne_zero
  have hmn : m.succPNat = n := PNat.eq (by rw [Nat.succPNat_coe, ← hm])
  have hle : ∀ i : ℕ+, (i : ℕ) ≤ m → v i = w i := fun i hi ↦ hvw i (by
    rw [← PNat.coe_lt_coe]; omega)
  rw [hm, hazewinkelLogCoeff_succ, hazewinkelLogCoeff_succ, ← smul_sub, ← sum_sub_distrib,
    sum_eq_single 0]
  · simp [hmn]
  · intro i hi hi0
    rw [mem_range] at hi
    rw [hazewinkelLogCoeff_congr hle (by omega : i ≤ m),
      hle _ (by rw [Nat.succPNat_coe]; omega), sub_self]
  · simp

/-- **The leading difference of Hazewinkel's laws over a `ℚ`-algebra.** If `v` and `w` agree below
`n`, the degree-`pⁿ` part of `F_v - F_w` is `(wₙ - vₙ) C_(pⁿ)`. -/
theorem homogeneousComponent_hazewinkelFormalGroup_sub (hp : p.Prime) {v w : ℕ+ → K} (n : ℕ+)
    (hvw : ∀ i < n, v i = w i) :
    homogeneousComponent (p ^ (n : ℕ))
        ((hazewinkelFormalGroup p v).toPowerSeries - (hazewinkelFormalGroup p w).toPowerSeries) =
      (((w n - v n) • lazardCocycle (p ^ (n : ℕ)) K : MvPolynomial (Fin 2) K) :
        MvPowerSeries (Fin 2) K) := by
  set N := p ^ (n : ℕ)
  have hN : N ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hle : ∀ i : ℕ+, (i : ℕ) ≤ (n : ℕ) - 1 → v i = w i := fun i hi ↦ hvw i (by
    rw [← PNat.coe_lt_coe]; have := n.pos; omega)
  have hpow : p ^ ((n : ℕ) - 1 + 1) = N := by rw [Nat.sub_add_cancel n.pos]
  -- the logarithms differ by `a Xᴺ` modulo higher terms, with `a = (vₙ - wₙ) / p`
  set a : K := (p : ℚ)⁻¹ • (v n - w n)
  have hlog : ((N + 1 : ℕ) : ℕ∞) ≤ ((hazewinkelFormalGroup p v).log -
      (hazewinkelFormalGroup p w).log - a • PowerSeries.X ^ N).order := by
    refine PowerSeries.nat_le_order _ _ fun k hk ↦ ?_
    rw [log_hazewinkelFormalGroup, log_hazewinkelFormalGroup]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk | rfl
    · have hlog := coeff_hazewinkelLog_congr (p := p) hle (k := k) (hpow ▸ hk)
      simp [hlog, PowerSeries.coeff_X_pow, hk.ne]
    · simp only [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_self, smul_eq_mul,
        mul_one, N, coeff_hazewinkelLog_pow _ hp.one_lt, hazewinkelLogCoeff_sub_of_forall_lt n hvw,
        a, sub_self]
  rw [FormalGroup.homogeneousComponent_sub_of_log_sub _ _ hN a hlog,
    ← lazardGcd_nsmul_lazardCocycle hN, lazardGcd_prime_pow hp n.ne_zero]
  -- `a • (p • C_N) = (vₙ - wₙ) • C_N`
  have ha : a * (p : K) = v n - w n := by
    rw [show a = (p : ℚ)⁻¹ • (v n - w n) from rfl, Algebra.smul_def, mul_comm, ← mul_assoc,
      ← map_natCast (algebraMap ℚ K) p, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero),
      map_one, one_mul]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ha]
  ext e
  simp only [map_neg, MvPolynomial.coeff_coe]
  simp [sub_mul]

end Rational

section Integral

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- Coefficientwise form of the leading difference between `F_v` and the law of the truncated
family `(v₁, …, v_(n - 1), 0, 0, …)`. -/
private theorem coeff_sub_truncate (v : ℕ+ → R) (n : ℕ+) (e : Fin 2 →₀ ℕ) :
    (if e.degree = p ^ (n : ℕ) then
        coeff e (hazewinkelIntegralFormalGroup p v).toPowerSeries -
          coeff e (hazewinkelIntegralFormalGroup p fun i ↦ if i < n then v i else 0).toPowerSeries
      else 0) =
      -v n * (lazardCocycle (p ^ (n : ℕ)) R).coeff e := by
  set t : ℕ+ → MvPolynomial ℕ+ ℤ := fun i ↦ if i < n then MvPolynomial.X i else 0
  set ψ : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  -- the universal case, over `ℤ[v₁, v₂, …]`, compared with `ℚ[v₁, v₂, …]`
  have huniv : (if e.degree = p ^ (n : ℕ) then
        coeff e (universalHazewinkelIntegralFormalGroup p).toPowerSeries -
          coeff e (hazewinkelIntegralFormalGroup p t).toPowerSeries else 0) =
      -MvPolynomial.X n * (lazardCocycle (p ^ (n : ℕ)) (MvPolynomial ℕ+ ℤ)).coeff e := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    have hrat := congrArg (coeff e) (homogeneousComponent_hazewinkelFormalGroup_sub hp.out
      (v := MvPolynomial.X) (w := MvPolynomial.map (Int.castRingHom ℚ) ∘ t) n
      fun i hi ↦ by simp [t, hi])
    rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe, map_sub] at hrat
    have hU : ψ (coeff e (universalHazewinkelIntegralFormalGroup p).toPowerSeries) =
        coeff e (hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → _)).toPowerSeries := by
      rw [← coeff_map, ← FormalGroup.map_toPowerSeries,
        map_intCast_universalHazewinkelIntegralFormalGroup]
    have ht : ψ (coeff e (hazewinkelIntegralFormalGroup p t).toPowerSeries) =
        coeff e (hazewinkelFormalGroup p (ψ ∘ t)).toPowerSeries := by
      rw [← coeff_map, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup,
        hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
    rw [apply_ite ψ, map_zero, map_sub, hU, ht, hrat, map_mul, map_neg, MvPolynomial.map_X,
      ← MvPolynomial.coeff_map, map_lazardCocycle]
    simp [t]
  set φ := MvPolynomial.eval₂Hom (Int.castRingHom R) v
  have hv : coeff e (hazewinkelIntegralFormalGroup p v).toPowerSeries =
      φ (coeff e (universalHazewinkelIntegralFormalGroup p).toPowerSeries) := by
    rw [hazewinkelIntegralFormalGroup_def, FormalGroup.map_toPowerSeries, coeff_map]
  have htv :
      coeff e (hazewinkelIntegralFormalGroup p fun i ↦ if i < n then v i else 0).toPowerSeries =
        φ (coeff e (hazewinkelIntegralFormalGroup p t).toPowerSeries) := by
    rw [← coeff_map, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup]
    congr 3
    funext i
    simp only [Function.comp_apply, t]
    split_ifs <;> simp [φ]
  rw [hv, htv, ← map_sub, ← map_zero φ, ← apply_ite φ, huniv, map_mul, map_neg,
    ← MvPolynomial.coeff_map, map_lazardCocycle]
  simp [φ]

/-- **The leading difference of Hazewinkel's laws.** If `v` and `w` agree below `n`, the
degree-`pⁿ` part of `F_v - F_w` is `(wₙ - vₙ) C_(pⁿ)`, over every commutative ring. -/
theorem homogeneousComponent_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} (n : ℕ+)
    (hvw : ∀ i < n, v i = w i) :
    homogeneousComponent (p ^ (n : ℕ))
        ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
      (((w n - v n) • lazardCocycle (p ^ (n : ℕ)) R : MvPolynomial (Fin 2) R) :
        MvPowerSeries (Fin 2) R) := by
  have htrunc : (fun i ↦ if i < n then v i else 0) = fun i ↦ if i < n then w i else 0 := by
    funext i
    split_ifs with hi
    exacts [hvw i hi, rfl]
  ext e
  have hv := coeff_sub_truncate p v n e
  have hw := coeff_sub_truncate p w n e
  rw [htrunc] at hv
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe, map_sub]
  split_ifs at hv hw ⊢ <;>
  · rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
    linear_combination hv - hw

/-- **Hazewinkel's generators are determined by the law.** Over every commutative ring, including
rings with torsion, `F_v = F_w` implies `v = w`. -/
theorem hazewinkelIntegralFormalGroup_injective :
    Function.Injective (hazewinkelIntegralFormalGroup p : (ℕ+ → R) → FormalGroup R) := by
  intro v w h
  funext n
  induction n using PNat.strongInductionOn with
  | _ n ih =>
    have hn := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p n ih
    rw [h, sub_self, map_zero, eq_comm, MvPolynomial.coe_eq_zero_iff,
      smul_lazardCocycle_eq_zero_iff (hp.out.two_le.trans (Nat.le_self_pow n.ne_zero p))] at hn
    exact (sub_eq_zero.mp hn).symm

end Integral

end TauCeti
