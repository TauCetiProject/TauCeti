/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.Analysis.Polynomial.DominantTerm
public import TauCeti.RingTheory.RootsOfUnity.Ultrametric

/-!
# Values of polynomials at `ζ - 1` for roots of unity of a well-chosen order

Let `g` be a polynomial over an ultrametric normed field. At a radius `r` where one weighted
coefficient norm `‖g_k‖ rᵏ` is strictly larger than all the others, the value at a point of norm
`r ≤ 1` is at least `‖g_d‖ r ^ D` for `d ≤ D` (`Polynomial.norm_coeff_mul_pow_le_norm_eval`),
and the radii in `(0, 1)` without such a dominant term are at most `d + #S` if `g_d ≠ 0` and the
coefficient norms at least `‖g_d‖` lie in a finite set `S`
(`Polynomial.card_le_of_forall_not_exists_norm_coeff_mul_pow_lt`); both are in
`TauCeti.Analysis.Polynomial.DominantTerm`.

A primitive root of unity `ζ` of order `p ^ m`, `m ≥ 1`, satisfies
`‖ζ - 1‖ = ‖p‖ ^ (1 / φ(p ^ m))` (`IsPrimitiveRoot.norm'_sub_one_pow_totient_prime_pow`), and
these radii are pairwise distinct when `0 < ‖p‖ < 1`. So among `#ι (D + #S) + 1` consecutive
levels one avoids the radii without a dominant term of each of the polynomials `f j`, `j : ι`,
which gives `TauCeti.exists_level_le_norm_eval_sub_one`: for a fixed finite index type `ι` there
is a bound `M₁`, depending only on `p`, `ε`, `D`, `#S` and `#ι` and not on the polynomials or
their degrees, such that for every family `f : ι → K[X]` with a coefficient of norm at least `c`
in degree at most `D` and with their coefficient norms at least `c` in `S`, some level
`1 ≤ m ≤ M₁` with `1 / φ(p ^ m) ≤ ε` has `f j (ζ - 1) ≠ 0` and `c ‖p‖ ^ ε ≤ ‖f j (ζ - 1)‖` for
every `j` and every primitive `p ^ m`-th root of unity `ζ`. With the valuation `v` normalised by
`v(p) = 1` and `c = ‖p‖ ^ v₀`, this reads `v(f j (ζ - 1)) ≤ v₀ + ε` and `v(ζ - 1) ≤ ε`.
`TauCeti.exists_level_le_norm_eval_sub_one_of_norm_coeff_eq_pow` gives the case where the
nonzero coefficient norms are powers of a real number `q` with `|q| ≤ 1`, and
`TauCeti.exists_level_le_norm_eval₂_sub_one` the case of polynomials over a discrete valuation
ring `O` mapped into the closed unit ball of `K`, such as the ring of integers of a finite
extension of `ℚ_[p]` inside `ℂ_[p]`, or `ℤ_[p]` in a normed `ℚ_[p]`-algebra. The statements
quantify over primitive roots `ζ` in `K` itself; they say something only when `K` contains them,
for instance when `K` is algebraically closed.

## Main results

* `TauCeti.exists_level_le_norm_eval_sub_one`,
  `TauCeti.exists_level_le_norm_eval_sub_one_of_norm_coeff_eq_pow` and
  `TauCeti.exists_level_le_norm_eval₂_sub_one`: one level of roots of unity at which finitely
  many polynomials are nonzero and not too small.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4 (Newton polygons).
* The formal proof https://github.com/leanprover-community/riemann-hypothesis states a related
  choice of levels for polynomials of a second kind,
  `GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants`.
-/

public section

open Polynomial

namespace TauCeti

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ}

/-- Beyond some level, `D + 1 ≤ ε φ(p ^ (m + 1))`. -/
private lemma exists_add_one_le_mul_totient (hp : p.Prime) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℕ, ∀ m, a ≤ m → (D : ℝ) + 1 ≤ ε * (p ^ (m + 1)).totient := by
  obtain ⟨a, ha⟩ := exists_nat_gt (((D : ℝ) + 1) / ε)
  refine ⟨a, fun m hm ↦ ?_⟩
  have h1 : m < (p ^ (m + 1)).totient := by
    rw [Nat.totient_prime_pow_succ hp]
    exact (Nat.lt_pow_self (n := m) hp.one_lt).trans_le
      (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hp.one_lt))
  have h2 : ((D : ℝ) + 1) / ε < (p ^ (m + 1)).totient :=
    ha.trans_le (by exact_mod_cast hm.trans h1.le)
  rw [div_lt_iff₀ hε] at h2
  linarith

omit [IsUltrametricDist K] in
/-- **Pigeonhole over a window of levels.** If `0 < ‖p‖ < 1`, among the levels `m + 1` for `m`
in a window of `#ι (D + #S) + 1` consecutive integers, one has, for each `f j`, a strictly
dominant weighted coefficient norm at the radius `‖p‖ ^ (1 / φ(p ^ (m + 1)))`. -/
private lemma exists_mem_Ico_forall_exists_lt [Fact p.Prime] (hp0 : 0 < ‖(p : K)‖)
    (hp : ‖(p : K)‖ < 1) {ι : Type*} [Fintype ι] {D : ℕ} {S : Finset ℝ} {c : ℝ} (hc : 0 < c)
    (a : ℕ) (f : ι → K[X]) (hf : ∀ j, ∃ d ≤ D, c ≤ ‖(f j).coeff d‖)
    (hfS : ∀ j i, c ≤ ‖(f j).coeff i‖ → ‖(f j).coeff i‖ ∈ S) :
    ∃ m ∈ Finset.Ico a (a + (Fintype.card ι * (D + S.card) + 1)), ∀ j, ∃ k, ∀ i ≠ k,
      ‖(f j).coeff i‖ * (‖(p : K)‖ ^ (((p ^ (m + 1)).totient : ℝ)⁻¹)) ^ i <
        ‖(f j).coeff k‖ * (‖(p : K)‖ ^ (((p ^ (m + 1)).totient : ℝ)⁻¹)) ^ k := by
  classical
  have hp' : p.Prime := Fact.out
  set ρ : ℕ → ℝ := fun m ↦ ‖(p : K)‖ ^ (((p ^ (m + 1)).totient : ℝ)⁻¹)
  have hφ : ∀ m, (0 : ℝ) < (p ^ (m + 1)).totient := fun m ↦
    Nat.cast_pos.2 (Nat.totient_pos.2 (pow_pos hp'.pos _))
  -- the totients `φ(p ^ (m + 1)) = p ^ m (p - 1)` grow strictly with `m`
  have htot : StrictMono fun m ↦ (p ^ (m + 1)).totient := fun m m' h ↦ by
    simp only [Nat.totient_prime_pow_succ hp']
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hp'.one_lt h)
      (Nat.sub_pos_of_lt hp'.one_lt)
  have hρmono : StrictMono ρ := fun m m' h ↦ Real.rpow_lt_rpow_of_exponent_gt hp0 hp
    ((inv_lt_inv₀ (hφ m') (hφ m)).2 (by exact_mod_cast htot h))
  by_contra hcon
  set W := Finset.Ico a (a + (Fintype.card ι * (D + S.card) + 1)) with hW
  let Bad : ι → Finset ℕ := fun j ↦ W.filter fun m ↦
    ¬∃ k, ∀ i ≠ k, ‖(f j).coeff i‖ * ρ m ^ i < ‖(f j).coeff k‖ * ρ m ^ k
  have hsub : W ⊆ Finset.univ.biUnion Bad := fun m hm ↦ by
    obtain ⟨j, hj⟩ := not_forall.1 fun h ↦ hcon ⟨m, hm, h⟩
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_filter.2 ⟨hm, hj⟩⟩
  have hbad : ∀ j, (Bad j).card ≤ D + S.card := fun j ↦ by
    obtain ⟨d, hdD, hcd⟩ := hf j
    rw [← Finset.card_image_of_injective _ hρmono.injective]
    refine (card_le_of_forall_not_exists_norm_coeff_mul_pow_lt
      (hc.trans_le hcd) (fun i hi ↦ hfS j i (hcd.trans hi)) ?_).trans
      (by omega)
    intro r hr
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨Real.rpow_pos_of_pos hp0 _, Real.rpow_lt_one hp0.le hp (inv_pos.2 (hφ m)),
      (Finset.mem_filter.1 hm).2⟩
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ ↦ hbad j))
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, hW, Nat.card_Ico] at hcard
  omega

/-- **One level of roots of unity for finitely many polynomials.** Let `K` be an ultrametric
normed field, `p` a prime with `‖p‖ < 1` and `ι` a finite type. Fix `D`, a finite set `S` of
reals, `c > 0` and `ε > 0`. There is `M₁`, depending only on `p`, `ε`, `D`, `#S` and `#ι`, such
that for every family `f : ι → K[X]` of polynomials, each with a coefficient of norm at least `c`
in some degree at most `D`, and all of whose coefficient norms at least `c` lie in `S`, some level
`1 ≤ m ≤ M₁` with `1 / φ(p ^ m) ≤ ε` satisfies, for every primitive `p ^ m`-th root of unity `ζ`
and every `j`, `f j (ζ - 1) ≠ 0` and `c ‖p‖ ^ ε ≤ ‖f j (ζ - 1)‖`. The bound `M₁` does not
depend on the polynomials, nor on their degrees, and `m ≤ M₁` gives a level `m ≤ M` for every
`M ≥ M₁`. For the valuation `v` with `v(p) = 1` and `c = ‖p‖ ^ v₀`, the last conclusion says
`v(f j (ζ - 1)) ≤ v₀ + ε`; the level condition says `v(ζ - 1) ≤ ε`, as
`v(ζ - 1) = 1 / φ(p ^ m)` by `IsPrimitiveRoot.norm'_sub_one_pow_totient_prime_pow`. The roots
`ζ` range over `K`: if `K` has no primitive `p ^ m`-th root of unity, the last conclusion is
vacuous. -/
theorem exists_level_le_norm_eval_sub_one [Fact p.Prime] (hp : ‖(p : K)‖ < 1) {ι : Type*}
    [Finite ι] (D : ℕ) (S : Finset ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₁ : ℕ, ∀ f : ι → K[X], (∀ j, ∃ d ≤ D, c ≤ ‖(f j).coeff d‖) →
      (∀ j i, c ≤ ‖(f j).coeff i‖ → ‖(f j).coeff i‖ ∈ S) →
      ∃ m, 1 ≤ m ∧ m ≤ M₁ ∧ ((p ^ m).totient : ℝ)⁻¹ ≤ ε ∧
        ∀ ζ : K, IsPrimitiveRoot ζ (p ^ m) → ∀ j,
          (f j).eval (ζ - 1) ≠ 0 ∧ c * ‖(p : K)‖ ^ ε ≤ ‖(f j).eval (ζ - 1)‖ := by
  have hp' : p.Prime := Fact.out
  have := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := exists_add_one_le_mul_totient hp' D hε
  refine ⟨a + (Fintype.card ι * (D + S.card) + 1), fun f hf hfS ↦ ?_⟩
  obtain ⟨m, hmW, hgood⟩ : ∃ m ∈ Finset.Ico a (a + (Fintype.card ι * (D + S.card) + 1)),
      0 < ‖(p : K)‖ → ∀ j, ∃ k, ∀ i ≠ k,
        ‖(f j).coeff i‖ * (‖(p : K)‖ ^ (((p ^ (m + 1)).totient : ℝ)⁻¹)) ^ i <
          ‖(f j).coeff k‖ * (‖(p : K)‖ ^ (((p ^ (m + 1)).totient : ℝ)⁻¹)) ^ k := by
    rcases (norm_nonneg (p : K)).eq_or_lt with h0 | h0
    · exact ⟨a, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩, fun h ↦ (h.ne h0).elim⟩
    · obtain ⟨m, hm, h⟩ := exists_mem_Ico_forall_exists_lt h0 hp hc a f hf hfS
      exact ⟨m, hm, fun _ ↦ h⟩
  obtain ⟨ham, hmlt⟩ := Finset.mem_Ico.1 hmW
  have hφ₀ : 0 < (p ^ (m + 1)).totient := Nat.totient_pos.2 (pow_pos hp'.pos _)
  have hφ : (0 : ℝ) < (p ^ (m + 1)).totient := Nat.cast_pos.2 hφ₀
  have hD : ((p ^ (m + 1)).totient : ℝ)⁻¹ * D ≤ ε :=
    (inv_mul_le_iff₀ hφ).2 (by linarith [ha m ham])
  refine ⟨m + 1, by omega, by omega, ?_, fun ζ hζ j ↦ ?_⟩
  · simpa using (inv_mul_le_iff₀ hφ).2 (show (1 : ℝ) ≤ _ * ε by linarith [ha m ham])
  -- `‖ζ - 1‖ ^ φ(p ^ (m + 1)) = ‖p‖`, and `ζ ≠ 1`
  have hp0 : 0 < ‖(p : K)‖ := by
    rw [← hζ.norm'_sub_one_pow_totient_prime_pow]
    exact pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one
      (Nat.one_lt_pow (Nat.succ_ne_zero m) hp'.one_lt)))) _
  have hρ : ‖ζ - 1‖ = ‖(p : K)‖ ^ (((p ^ (m + 1)).totient : ℝ)⁻¹) := by
    rw [← hζ.norm'_sub_one_pow_totient_prime_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) hφ₀.ne']
  obtain ⟨k, hk⟩ := hgood hp0 j
  obtain ⟨d, hdD, hcd⟩ := hf j
  rw [← hρ] at hk
  have hx1 : ‖ζ - 1‖ ≤ 1 := hρ ▸ Real.rpow_le_one hp0.le hp.le (inv_pos.2 hφ).le
  have hpow : ‖(p : K)‖ ^ ε ≤ ‖ζ - 1‖ ^ D := by
    rw [hρ, ← Real.rpow_mul_natCast hp0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hp0 hp.le hD
  have hle : c * ‖(p : K)‖ ^ ε ≤ ‖(f j).eval (ζ - 1)‖ :=
    (mul_le_mul hcd hpow (Real.rpow_nonneg hp0.le _) (norm_nonneg _)).trans
      (norm_coeff_mul_pow_le_norm_eval hdD hx1 hk)
  exact ⟨norm_pos_iff.1 ((mul_pos hc (Real.rpow_pos_of_pos hp0 _)).trans_le hle), hle⟩

/-- Powers `q ^ n` with `|q| ≤ 1` that are at least `c > 0` take finitely many values. -/
private lemma exists_forall_pow_eq {q c : ℝ} (hq : |q| ≤ 1) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, c ≤ q ^ n → ∃ n' < N, q ^ n' = q ^ n := by
  rcases hq.lt_or_eq with hq1 | hq1
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc hq1
    refine ⟨N, fun n hn ↦ ⟨n, ?_, rfl⟩⟩
    by_contra! h
    have hle : q ^ n ≤ |q| ^ N := (le_abs_self _).trans
      ((abs_pow q n).trans_le (pow_le_pow_of_le_one (abs_nonneg q) hq h))
    exact (hn.trans hle).not_gt hN
  · -- `q ^ 2 = |q| ^ 2 = 1`, so `q ^ n = q ^ (n % 2)`
    refine ⟨2, fun n _ ↦ ⟨n % 2, Nat.mod_lt _ two_pos, ?_⟩⟩
    conv_rhs => rw [← Nat.mod_add_div n 2]
    rw [pow_add, pow_mul, ← sq_abs, hq1, one_pow, one_pow, mul_one]

/-- **One level of roots of unity, for coefficients with discrete norms.** The case of
`TauCeti.exists_level_le_norm_eval_sub_one` in which every nonzero coefficient of every `f j`
has norm a power of a real number `q` with `|q| ≤ 1`, as for coefficients in a discrete
valuation ring with uniformiser of norm `q`: for a finite type `ι` there is `M₁`, depending only
on `p`, `ε`, `D`, `c`, `q` and `#ι`, such that for every family `f : ι → K[X]` of such
polynomials, each with a coefficient of norm at least `c > 0` in some degree at most `D`, some
level `1 ≤ m ≤ M₁` with `1 / φ(p ^ m) ≤ ε` satisfies `f j (ζ - 1) ≠ 0` and
`c ‖p‖ ^ ε ≤ ‖f j (ζ - 1)‖` for every primitive `p ^ m`-th root of unity `ζ` and every `j`. -/
theorem exists_level_le_norm_eval_sub_one_of_norm_coeff_eq_pow [Fact p.Prime]
    (hp : ‖(p : K)‖ < 1) {ι : Type*} [Finite ι] (D : ℕ) {q : ℝ} (hq : |q| ≤ 1) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₁ : ℕ, ∀ f : ι → K[X], (∀ j, ∃ d ≤ D, c ≤ ‖(f j).coeff d‖) →
      (∀ j i, (f j).coeff i = 0 ∨ ∃ n : ℕ, ‖(f j).coeff i‖ = q ^ n) →
      ∃ m, 1 ≤ m ∧ m ≤ M₁ ∧ ((p ^ m).totient : ℝ)⁻¹ ≤ ε ∧
        ∀ ζ : K, IsPrimitiveRoot ζ (p ^ m) → ∀ j,
          (f j).eval (ζ - 1) ≠ 0 ∧ c * ‖(p : K)‖ ^ ε ≤ ‖(f j).eval (ζ - 1)‖ := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_pow_eq hq hc
  obtain ⟨M₁, hM₁⟩ := exists_level_le_norm_eval_sub_one (ι := ι) hp D
    ((Finset.range N).image (q ^ ·)) hc hε
  refine ⟨M₁, fun f hf hfq ↦ hM₁ f hf fun j i hi ↦ ?_⟩
  rcases hfq j i with h0 | ⟨n, hn⟩
  · rw [h0, norm_zero] at hi
    exact (hc.not_ge hi).elim
  · obtain ⟨n', hn', heq⟩ := hN n (hn ▸ hi)
    exact Finset.mem_image.2 ⟨n', Finset.mem_range.2 hn', heq.trans hn.symm⟩

/-- **One level of roots of unity, for polynomials over a discrete valuation ring.** Let `O` be
a discrete valuation ring and `φ : O →+* K` a ring map into the closed unit ball, for instance
the inclusion of the ring of integers of a finite extension of `ℚ_[p]` into `ℂ_[p]`, and let `ι`
be a finite type. There is `M₁`, depending only on `p`, `ε`, `D`, `c`, `φ` and `#ι`, such that
for every family `f : ι → O[X]` of polynomials, each with a coefficient `a` with `c ≤ ‖φ a‖` in
some degree at most `D`, some level `1 ≤ m ≤ M₁` with `1 / φ(p ^ m) ≤ ε` satisfies
`f j (ζ - 1) ≠ 0` and `c ‖p‖ ^ ε ≤ ‖f j (ζ - 1)‖`, evaluated through `φ`, for every primitive
`p ^ m`-th root of unity `ζ` in `K` and every `j`. The nonzero elements of `O` are units times
powers of a uniformiser `ϖ`, so this is the case of
`TauCeti.exists_level_le_norm_eval_sub_one_of_norm_coeff_eq_pow` for `q = ‖φ ϖ‖`. -/
theorem exists_level_le_norm_eval₂_sub_one [Fact p.Prime] (hp : ‖(p : K)‖ < 1) {ι : Type*}
    [Finite ι] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : O →+* K)
    (hφ : ∀ a, ‖φ a‖ ≤ 1) (D : ℕ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₁ : ℕ, ∀ f : ι → O[X], (∀ j, ∃ d ≤ D, c ≤ ‖φ ((f j).coeff d)‖) →
      ∃ m, 1 ≤ m ∧ m ≤ M₁ ∧ ((p ^ m).totient : ℝ)⁻¹ ≤ ε ∧
        ∀ ζ : K, IsPrimitiveRoot ζ (p ^ m) → ∀ j,
          (f j).eval₂ φ (ζ - 1) ≠ 0 ∧ c * ‖(p : K)‖ ^ ε ≤ ‖(f j).eval₂ φ (ζ - 1)‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hunit (u : Oˣ) : ‖φ u‖ = 1 := by
    refine le_antisymm (hφ u) ?_
    calc 1 = ‖φ u‖ * ‖φ ↑u⁻¹‖ := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
      _ ≤ ‖φ u‖ * 1 := by gcongr; exact hφ _
      _ = ‖φ u‖ := mul_one _
  obtain ⟨M₁, hM₁⟩ := exists_level_le_norm_eval_sub_one_of_norm_coeff_eq_pow (ι := ι) hp D
    ((abs_norm _).trans_le (hφ ϖ)) hc hε
  refine ⟨M₁, fun f hf ↦ ?_⟩
  simp only [← eval_map]
  refine hM₁ (fun j ↦ (f j).map φ) (fun j ↦ by simpa only [coeff_map] using hf j) fun j i ↦ ?_
  rw [coeff_map]
  by_cases h0 : (f j).coeff i = 0
  · exact Or.inl (by rw [h0, map_zero])
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    exact Or.inr ⟨n, by rw [hu, map_mul, map_pow, norm_mul, norm_pow, hunit, one_mul]⟩

end TauCeti
