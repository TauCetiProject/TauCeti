/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.Dagger.OptionSeries
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division

/-!
# Multivariable overconvergent Weierstrass division

Let `K` be a complete ultrametric normed field. A series in `K⟨X, Y⟩†`, with `Y = X none`,
which is distinguished of degree `s` in `Y` at unit radius and has a unit coefficient in
degree `s`, divides every overconvergent series. The quotient is overconvergent in all
variables and the remainder is a polynomial in `Y` of degree less than `s`, with coefficients
in `K⟨X⟩†`. The decomposition is unique.

Existence uses unequal radii: first select `1 < ρ ≤ r` preserving distinguishedness, then
apply fixed-radius division over the Banach ring `K{X/ρ}` at radius `r` in `Y`. The quotient
is restricted at these polyradii, hence overconvergent. Uniqueness is checked in the
unit-radius Tate algebra. These are the division statements used in the ideal theory of
Monsky–Washnitzer algebras.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(i).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2.

The fixed-radius division is `TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq`;
the radius selection is `TauCeti.Dagger.exists_isDistinguished_isUnit_of_isDistinguished_one`.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open TauCeti.MvPowerSeries (isRestricted_of_le)
open washnitzerAlgebra (optionSeries toTate)

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" => washnitzerAlgebra σ K
local notation "W'" => washnitzerAlgebra (Option σ) K
local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- Transport fixed-polyradius division to the overconvergent algebra. -/
private theorem exists_mul_add_eq_series_of_isRestricted {c : Option σ → ℝ}
    [∀ i, Fact (0 < c i)] {ρ : ℝ} (hρ : 1 < ρ) (hρc : ∀ i, ρ ≤ c i)
    {g : W'} {s : ℕ} (hgc : IsRestricted c (g : MvPowerSeries (Option σ) K))
    (hg : PowerSeries.IsDistinguished (c none) s
      (Huber.restrictedOptionEquiv (c := c) (⟨g, hgc⟩ : IsRestricted.subring (R := K) c) :
        PowerSeries (IsRestricted.subring (R := K) (fun i : σ ↦ c (some i)))))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (c := c) (⟨g, hgc⟩ : IsRestricted.subring (R := K) c) :
        PowerSeries (IsRestricted.subring (R := K) (fun i : σ ↦ c (some i))))))
    (f : W') (hf : IsRestricted c (f : MvPowerSeries (Option σ) K)) :
    ∃ (q : W') (r : PowerSeries W),
      (∀ m, s ≤ m → PowerSeries.coeff m r = 0) ∧
        optionSeries q * optionSeries g + r = optionSeries f := by
  let gC : IsRestricted.subring (R := K) c := ⟨g, hgc⟩
  let fC : IsRestricted.subring (R := K) c := ⟨f, hf⟩
  let G := Huber.restrictedOptionEquiv (c := c) gC
  let F := Huber.restrictedOptionEquiv (c := c) fC
  obtain ⟨Q, R, hQ, hR, hQR⟩ := hg.exists_mul_add_eq hu (Fact.out : 0 < c none) G.2 F.2
  let qC := (Huber.restrictedOptionEquiv (c := c)).symm ⟨Q, hQ⟩
  let q : W' := ⟨qC, mem_washnitzerAlgebra.mpr
    ⟨ρ, hρ, isRestricted_of_le qC.2 (fun _ ↦ (zero_lt_one.trans hρ).le) hρc⟩⟩
  let φ : IsRestricted.subring (R := K) (fun i : σ ↦ c (some i)) →+* W :=
    (IsRestricted.subring (R := K) (fun i : σ ↦ c (some i))).subtype.codRestrict
      (washnitzerAlgebra σ K).toSubring
      (fun a ↦ mem_washnitzerAlgebra.mpr ⟨ρ, hρ,
        isRestricted_of_le a.2 (fun _ ↦ (zero_lt_one.trans hρ).le) (fun i ↦ hρc (some i))⟩)
  let Rw := PowerSeries.map φ R
  have hQmap : PowerSeries.map ((washnitzerAlgebra σ K).val :
      washnitzerAlgebra σ K →+* MvPowerSeries σ K) (optionSeries q) =
      PowerSeries.map (IsRestricted.subring (R := K) (fun i : σ ↦ c (some i))).subtype Q := by
    rw [washnitzerAlgebra.map_val_optionSeries]
    simp only [q, qC]
    rw [Huber.coe_restrictedOptionEquiv_symm (c := c)]
    exact (optionEquivLeft σ K).apply_symm_apply _
  have hRmap : PowerSeries.map ((washnitzerAlgebra σ K).val :
      washnitzerAlgebra σ K →+* MvPowerSeries σ K) Rw =
      PowerSeries.map (IsRestricted.subring (R := K) (fun i : σ ↦ c (some i))).subtype R := by
    ext m : 1
    simp [Rw, φ, Subalgebra.val_apply]
  refine ⟨q, Rw, fun m hm ↦ by simp [Rw, hR m hm], ?_⟩
  apply washnitzerAlgebra.map_val_injective
  rw [map_add, map_mul, hQmap, hRmap, washnitzerAlgebra.map_val_optionSeries,
    washnitzerAlgebra.map_val_optionSeries,
    ← Huber.map_subtype_restrictedOptionEquiv (c := c) gC, ← map_mul, ← map_add, hQR]
  exact Huber.map_subtype_restrictedOptionEquiv (c := c) fC

private theorem exists_mul_add_eq_series {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W') :
    ∃ (q : W') (r : PowerSeries W),
      (∀ m, s ≤ m → PowerSeries.coeff m r = 0) ∧
        optionSeries q * optionSeries g + r = optionSeries f := by
  obtain ⟨ρ₀, hρ₀, hf⟩ := mem_washnitzerAlgebra.mp f.2
  obtain ⟨ρ, hρpos, r, hρ, hρr, hr₀, hgr, G, hG, hd, huG⟩ :=
    exists_isDistinguished_isUnit_of_isDistinguished_one hg hu hρ₀
  -- Install the positive-radius instance used by the norm on the coefficients of `G`.
  let _ := hρpos
  let c : Option σ → ℝ := fun i ↦ i.elim r (fun _ ↦ ρ)
  have hr : 1 < r := hρ.trans_le hρr
  let _ : ∀ i, Fact (0 < c i) := fun i ↦ ⟨by
    cases i
    · exact zero_lt_one.trans hr
    · exact zero_lt_one.trans hρ⟩
  have hcr (i) : c i ≤ r := by cases i <;> simp [c, hρr]
  have hρc (i) : ρ ≤ c i := by cases i <;> simp [c, hρr]
  have hgc : IsRestricted c (g : MvPowerSeries (Option σ) K) :=
    isRestricted_of_le hgr (fun i ↦ (Fact.out : 0 < c i).le) hcr
  have hGC : G = (Huber.restrictedOptionEquiv (c := c)
      (⟨g, hgc⟩ : IsRestricted.subring (R := K) c)).val := by
    ext m : 1
    apply Subtype.ext
    rw [hG]
    -- The split polyradius restricts to the constant radius `ρ` on the coefficient variables.
    convert! (Huber.coeff_restrictedOptionEquiv (c := c)
      (⟨g, hgc⟩ : IsRestricted.subring (R := K) c) m).symm using 0
  -- The split polyradius has coefficient radius `ρ` and separated-variable radius `r`.
  apply exists_mul_add_eq_series_of_isRestricted (c := c) hρ hρc hgc
    (hGC ▸ hd) (hGC ▸ huG) f
  exact isRestricted_of_le hf (fun i ↦ (Fact.out : 0 < c i).le)
    (fun i ↦ (hcr i).trans hr₀)

/-- **Overconvergent Weierstrass division.** If `g` is distinguished of degree `s` at unit
radius with unit distinguished coefficient, then every overconvergent dividend `f` has an
overconvergent quotient `q` and a polynomial remainder `r` over the smaller overconvergent
algebra, of degree less than `s` in the separated variable, with `f = q * g + r`. -/
theorem exists_mul_add_eq_of_isDistinguished {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W') :
    ∃ (q : W') (r : Polynomial W), r.degree < (s : WithBot ℕ) ∧
      optionSeries q * optionSeries g + (r : PowerSeries W) = optionSeries f := by
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_series hg hu f
  refine ⟨q, r.trunc s, PowerSeries.degree_trunc_lt _ _, ?_⟩
  have htrunc : ((r.trunc s : Polynomial W) : PowerSeries W) = r := by
    ext m : 1
    simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hm
    · rfl
    · exact (hr m (Nat.le_of_not_gt hm)).symm
  rwa [htrunc]

omit [CompleteSpace K] in
/-- **Uniqueness in overconvergent Weierstrass division.** If `q * g + r = q' * g + r'`
with polynomial remainders `r, r'` of degree less than `s` in the separated variable, then
`q = q'` and `r = r'`. Neither completeness nor a unit distinguished coefficient is needed. -/
theorem eq_and_eq_of_mul_add_eq_mul_add_of_isDistinguished {g q q' : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    {r r' : Polynomial W} (hr : r.degree < (s : WithBot ℕ))
    (hr' : r'.degree < (s : WithBot ℕ))
    (h : optionSeries q * optionSeries g + (r : PowerSeries W) =
      optionSeries q' * optionSeries g + (r' : PowerSeries W)) : q = q' ∧ r = r' := by
  have hmap := congrArg (PowerSeries.map (toTate σ K : washnitzerAlgebra σ K →+*
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)))) h
  simp only [map_add, map_mul, washnitzerAlgebra.map_toTate_optionSeries] at hmap
  have hz (p : Polynomial W) (hp : p.degree < (s : WithBot ℕ)) (m : ℕ) (hm : s ≤ m) :
      PowerSeries.coeff m
        (PowerSeries.map (toTate σ K : washnitzerAlgebra σ K →+*
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))) (p : PowerSeries W)) = 0 := by
    simp [Polynomial.coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hm))]
  obtain ⟨hqq, hrr⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add zero_lt_one
    (fun _ ↦ norm_mul _ _) (Huber.restrictedOptionEquiv (toTate _ K q)).2
    (Huber.restrictedOptionEquiv (toTate _ K q')).2 (hz r hr) (hz r' hr') hmap
  refine ⟨washnitzerAlgebra.optionSeries_injective ?_, ?_⟩
  · apply PowerSeries.map_injective (toTate σ K : washnitzerAlgebra σ K →+*
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))) washnitzerAlgebra.toTate_injective
    simpa only [washnitzerAlgebra.map_toTate_optionSeries] using hqq
  · have he := PowerSeries.map_injective (toTate σ K : washnitzerAlgebra σ K →+*
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)))
      washnitzerAlgebra.toTate_injective hrr
    exact Polynomial.coe_injective _ he

/-- **Unique overconvergent Weierstrass division**, with the quotient and polynomial remainder
bundled as a unique pair. No characteristic or nontrivial-norm assumption is required. -/
theorem existsUnique_mul_add_eq_of_isDistinguished {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W') :
    ∃! p : W' × Polynomial W, p.2.degree < (s : WithBot ℕ) ∧
      optionSeries p.1 * optionSeries g + (p.2 : PowerSeries W) = optionSeries f := by
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
  refine ⟨(q, r), ⟨hr, hqr⟩, fun p ⟨hp, he⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_add_eq_mul_add_of_isDistinguished hg hp hr (he.trans hqr.symm)
  exact Prod.ext h1 h2

end TauCeti.Dagger
