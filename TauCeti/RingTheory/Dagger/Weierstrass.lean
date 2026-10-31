/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.Dagger.OptionSeries
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.Algebra.GroupWithZero.Irreducible
import TauCeti.RingTheory.PowerSeries.Trunc

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

For a distinguished monic polynomial `ω ∈ K⟨X⟩†[Y]`, evaluated at `Y` by
`washnitzerAlgebra.polynomialToOption`, uniqueness of division shows that divisibility by `ω` is
the same in `K⟨X⟩†[Y]` and in `K⟨X, Y⟩†`, and existence shows that every series is congruent to
a polynomial modulo `ω`. Hence irreducibility of `ω` descends from `K⟨X, Y⟩†` to `K⟨X⟩†[Y]`, and
`ω` is prime in one ring iff it is prime in the other.

Dividing one variable at a time by its minimal polynomial over `K`, a polynomial with constant
coefficients and hence distinguished at unit radius, shows that every quotient of `K⟨X⟩†` in
finitely many variables which is integral over `K` is spanned by the images of polynomials
(`TauCeti.Dagger.washnitzerAlgebra.surjective_mkₐ_comp_ofMvPolynomial`).

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(i).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2.

The fixed-radius division is `TauCeti.PowerSeries.IsMulDistinguished.exists_mul_add_eq`;
the radius selection is `TauCeti.Dagger.exists_isDistinguished_isUnit_of_isDistinguished_one`.
The polynomial comparison follows its Tate-algebra counterpart
`TauCeti.PowerSeries.IsDistinguished.polynomialToRestricted_dvd_iff`.
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

/-- Transport fixed-radius division to the overconvergent algebra: `g` is restricted at radius
`r`, and its iterated series `G`, with coefficients restricted at radius `ρ`, is distinguished at
radius `r` with unit distinguished coefficient. -/
private theorem exists_mul_add_eq_series_of_isRestricted {ρ r : ℝ} [Fact (0 < ρ)] (hρ : 1 < ρ)
    (hρr : ρ ≤ r) {g : W'} {s : ℕ}
    (hgr : IsRestricted (fun _ ↦ r) (g : MvPowerSeries (Option σ) K))
    {G : PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ))}
    (hG : ∀ m, (↑(PowerSeries.coeff m G) : MvPowerSeries σ K) =
      PowerSeries.coeff m (optionEquivLeft σ K (g : MvPowerSeries (Option σ) K)))
    (hd : PowerSeries.IsDistinguished r s G) (hu : IsUnit (PowerSeries.coeff s G))
    (f : W') (hf : IsRestricted (fun _ ↦ r) (f : MvPowerSeries (Option σ) K)) :
    ∃ (q : W') (R : PowerSeries W),
      (∀ m, s ≤ m → PowerSeries.coeff m R = 0) ∧
        optionSeries q * optionSeries g + R = optionSeries f := by
  -- The split polyradius: `r` in the separated variable and `ρ` in the others. Its coefficient
  -- polyradius `fun i ↦ c (some i)` reduces to `fun _ ↦ ρ` by unfolding `splitRadius`.
  let c : Option σ → ℝ := splitRadius r ρ
  let _ : ∀ i, Fact (0 < c i) := fun i ↦ ⟨splitRadius_pos Fact.out hρr i⟩
  let fC : IsRestricted.subring (R := K) c :=
    ⟨f, isRestricted_of_le hf (fun i ↦ (Fact.out : 0 < c i).le) (splitRadius_le hρr)⟩
  have hGmap : PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype G =
      optionEquivLeft σ K (g : MvPowerSeries (Option σ) K) := PowerSeries.ext hG
  -- Divide at the fixed radius `r` over the Banach ring of radius-`ρ` series.
  obtain ⟨Q, R, hQ, hR, hQR⟩ := (PowerSeries.isMulDistinguished_iff_isUnit.mpr
    ⟨hd, hu⟩).exists_mul_add_eq (zero_lt_one.trans (hρ.trans_le hρr))
    (isRestricted_of_map_subtype_eq_optionEquivLeft hρr hgr hGmap) (restrictedOptionEquiv fC).2
  -- Pull `Q` and `R` back to the overconvergent algebras and compare formal series.
  let φ : IsRestricted.subring (R := K) (fun _ : σ ↦ ρ) →+* W :=
    washnitzerAlgebra.ofRestricted hρ fun _ ↦ le_rfl
  refine ⟨washnitzerAlgebra.ofRestricted hρ (le_splitRadius hρr)
    ((restrictedOptionEquiv (c := c)).symm ⟨Q, hQ⟩), PowerSeries.map φ R,
    fun m hm ↦ by simp [hR m hm], washnitzerAlgebra.map_val_injective ?_⟩
  have hRw : PowerSeries.map ((washnitzerAlgebra σ K).val : W →+* MvPowerSeries σ K)
      (PowerSeries.map φ R) =
        PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype R :=
    PowerSeries.ext fun m ↦ by simp [φ]
  have h := congrArg (PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype) hQR
  -- `RingHom.map_add` and `RingHom.map_mul`: the generic `map_add` searches `AddHomClass` slowly.
  rw [RingHom.map_add, RingHom.map_mul, hGmap, map_subtype_restrictedOptionEquiv fC] at h
  simp only [RingHom.map_add, RingHom.map_mul, washnitzerAlgebra.map_val_optionSeries, hRw,
    washnitzerAlgebra.coe_ofRestricted, coe_restrictedOptionEquiv_symm, AlgEquiv.apply_symm_apply]
  linear_combination h

private theorem exists_mul_add_eq_series {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W') :
    ∃ (q : W') (r : PowerSeries W),
      (∀ m, s ≤ m → PowerSeries.coeff m r = 0) ∧
        optionSeries q * optionSeries g + r = optionSeries f := by
  obtain ⟨ρ₀, hρ₀, hf⟩ := mem_washnitzerAlgebra.mp f.2
  obtain ⟨ρ, hρpos, r, hρ, hρr, hr₀, hgr, G, hG, hd, huG⟩ :=
    exists_isDistinguished_isUnit_of_isDistinguished_one hg hu hρ₀
  exact exists_mul_add_eq_series_of_isRestricted hρ hρr hgr hG hd huG f
    (isRestricted_of_le hf (fun _ ↦ (zero_lt_one.trans (hρ.trans_le hρr)).le) fun _ ↦ hr₀)

/-- **Overconvergent Weierstrass division.** If `g` is distinguished of degree `s` at unit
radius with unit distinguished coefficient, then every overconvergent dividend `f` has an
overconvergent quotient `q` and a polynomial remainder `r` over the smaller overconvergent
algebra, of degree less than `s` in the separated variable, with `f = q * g + r`. -/
theorem exists_mul_add_eq_of_isDistinguished {g : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W') :
    ∃ (q : W') (r : Polynomial W), r.degree < (s : WithBot ℕ) ∧
      optionSeries q * optionSeries g + (r : PowerSeries W) = optionSeries f := by
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_series hg hu f
  refine ⟨q, r.trunc s, PowerSeries.degree_trunc_lt _ _, ?_⟩
  rwa [PowerSeries.coe_trunc_eq_self_of_coeff_eq_zero hr]

omit [CompleteSpace K] in
/-- **Uniqueness in overconvergent Weierstrass division.** If `q * g + r = q' * g + r'`
with polynomial remainders `r, r'` of degree less than `s` in the separated variable, then
`q = q'` and `r = r'`. Neither completeness nor a unit distinguished coefficient is needed. -/
theorem eq_and_eq_of_mul_add_eq_mul_add_of_isDistinguished {g q q' : W'} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
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
    (fun _ ↦ norm_mul _ _) (restrictedOptionEquiv (toTate _ K q)).2
    (restrictedOptionEquiv (toTate _ K q')).2 (hz r hr) (hz r' hr') hmap
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
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W') :
    ∃! p : W' × Polynomial W, p.2.degree < (s : WithBot ℕ) ∧
      optionSeries p.1 * optionSeries g + (p.2 : PowerSeries W) = optionSeries f := by
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
  refine ⟨(q, r), ⟨hr, hqr⟩, fun p ⟨hp, he⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_add_eq_mul_add_of_isDistinguished hg hp hr (he.trans hqr.symm)
  exact Prod.ext h1 h2

namespace washnitzerAlgebra

section Polynomial

variable {s : ℕ} {ω : Polynomial (washnitzerAlgebra σ K)}

omit [CompleteSpace K] in
/-- Divisibility of polynomials by a distinguished monic polynomial `ω` is unchanged on passing
to `K⟨X, Y⟩†`. This holds without assuming `K` complete. -/
theorem polynomialToOption_dvd_iff
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) (p : Polynomial W) :
    polynomialToOption ω ∣ polynomialToOption p ↔ ω ∣ p := by
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ map_dvd _ h⟩
  have hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate) := by
    rwa [restrictedOptionEquiv_toTate_polynomialToOption]
  have hdeg : (p %ₘ ω).degree < (s : WithBot ℕ) := by
    simpa [Polynomial.degree_eq_natDegree hm.ne_zero, hm.natDegree_eq] using
      Polynomial.degree_modByMonic_lt p hm.monic
  -- Compare `p = a * ω` in `W'` with the polynomial division `p = (p /ₘ ω) * ω + p %ₘ ω`.
  have heq : optionSeries a * optionSeries (polynomialToOption ω) + ((0 : Polynomial W) :
      PowerSeries W) = optionSeries (polynomialToOption (p /ₘ ω)) *
        optionSeries (polynomialToOption ω) + ((p %ₘ ω : Polynomial W) : PowerSeries W) := by
    simpa [ha, mul_comm, add_comm] using congrArg (fun x ↦ optionSeries (polynomialToOption x))
      (Polynomial.modByMonic_add_div p ω).symm
  have hzero := (eq_and_eq_of_mul_add_eq_mul_add_of_isDistinguished hg
    (by simp [Polynomial.degree_zero]) hdeg heq).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm.monic).mp hzero.symm

omit [CompleteSpace K] in
/-- A distinguished monic polynomial which is irreducible in `K⟨X, Y⟩†` is irreducible in
`K⟨X⟩†[Y]`. -/
theorem irreducible_of_irreducible_polynomialToOption
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) (h : Irreducible (polynomialToOption ω)) : Irreducible ω :=
  h.of_map_of_dvd hm.ne_zero fun p ↦ (polynomialToOption_dvd_iff hω hm p).mp

/-- Every overconvergent series is congruent modulo a distinguished monic polynomial `ω` to a
polynomial in `Y` of degree less than that of `ω`, with coefficients in `K⟨X⟩†`. -/
theorem exists_mul_add_polynomialToOption_eq
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) (f : W') :
    ∃ (q : W') (r : Polynomial W), r.degree < (s : WithBot ℕ) ∧
      q * polynomialToOption ω + polynomialToOption r = f := by
  have hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate) := by
    rwa [restrictedOptionEquiv_toTate_polynomialToOption]
  have hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K (polynomialToOption ω)) : PowerSeries Tate)) := by
    simp [restrictedOptionEquiv_toTate_polynomialToOption, Polynomial.coeff_coe,
      ← hm.natDegree_eq, hm.monic.coeff_natDegree]
  obtain ⟨q, r, hr, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
  exact ⟨q, r, hr, optionSeries_injective (by simpa using hqr)⟩

/-- A distinguished monic polynomial is prime in `K⟨X⟩†[Y]` iff it is prime in `K⟨X, Y⟩†`. -/
theorem prime_polynomialToOption_iff
    (hω : PowerSeries.IsDistinguished 1 s (ω.map (toTate σ K).toRingHom : PowerSeries Tate))
    (hm : ω.IsMonicOfDegree s) : Prime (polynomialToOption ω) ↔ Prime ω := by
  have hdvd := polynomialToOption_dvd_iff hω hm
  refine ⟨fun h ↦ ⟨fun h0 ↦ h.ne_zero (by simp [h0]), fun hu ↦ h.not_isUnit (hu.map _),
    fun a b hab ↦ ?_⟩, fun h ↦ ⟨fun h0 ↦ h.ne_zero (polynomialToOption_injective (by simp [h0])),
    fun hu ↦ h.not_isUnit ?_, fun a b hab ↦ ?_⟩⟩
  · simpa only [← hdvd] using
      h.dvd_or_dvd (by simpa only [map_mul] using map_dvd polynomialToOption hab)
  · -- A unit `polynomialToOption ω` divides `polynomialToOption 1`, so `ω` divides `1`.
    exact isUnit_of_dvd_one ((hdvd 1).mp (by simpa using hu.dvd))
  · -- Reduce `a` and `b` to polynomial remainders modulo `ω`.
    obtain ⟨qa, ra, -, rfl⟩ := exists_mul_add_polynomialToOption_eq hω hm a
    obtain ⟨qb, rb, -, rfl⟩ := exists_mul_add_polynomialToOption_eq hω hm b
    have hr : ω ∣ ra * rb := by
      rw [← hdvd, map_mul]
      have hexp : (qa * polynomialToOption ω + polynomialToOption ra) *
          (qb * polynomialToOption ω + polynomialToOption rb) = polynomialToOption ω *
            (qa * qb * polynomialToOption ω + qa * polynomialToOption rb +
              qb * polynomialToOption ra) + polynomialToOption ra * polynomialToOption rb := by
        ring
      rw [hexp] at hab
      exact (dvd_add_right (dvd_mul_right _ _)).mp hab
    rcases h.dvd_or_dvd hr with ha | hb
    · exact Or.inl ((dvd_add_right (dvd_mul_left _ qa)).mpr ((hdvd ra).mpr ha))
    · exact Or.inr ((dvd_add_right (dvd_mul_left _ qb)).mpr ((hdvd rb).mpr hb))

end Polynomial

section IntegralQuotient

/-- The statement of `surjective_mkₐ_comp_ofMvPolynomial` for the variables `σ`. -/
private abbrev PolynomialsSurject (σ : Type*) : Prop :=
  ∀ (I : Ideal (washnitzerAlgebra σ K)) [Algebra.IsIntegral K (washnitzerAlgebra σ K ⧸ I)],
    Function.Surjective ((Ideal.Quotient.mkₐ K I).comp (ofMvPolynomial σ K))

omit [CompleteSpace K] in
private theorem polynomialsSurject_of_equiv {σ τ : Type*} (e : σ ≃ τ)
    (h : PolynomialsSurject (K := K) σ) : PolynomialsSurject (K := K) τ := by
  intro I _
  let φ := renameEquiv (R := K) e
  let J := I.comap φ.toAlgHom
  have : Algebra.IsIntegral K (washnitzerAlgebra σ K ⧸ J) :=
    Algebra.IsIntegral.of_injective (Ideal.quotientMapₐ I φ.toAlgHom le_rfl)
      Ideal.quotientMap_injective
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, hp⟩ := h J (Ideal.Quotient.mk J (φ.symm f))
  refine ⟨MvPolynomial.rename e p, ?_⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, J,
    Ideal.mem_comap] at hp
  refine Ideal.Quotient.eq.mpr ?_
  simpa [φ] using hp

omit [CompleteSpace K] in
private theorem polynomialsSurject_of_isEmpty {σ : Type*} [IsEmpty σ] :
    PolynomialsSurject (K := K) σ := by
  intro I _ x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, rfl⟩ := algebraMap_surjective (R := K) f
  exact ⟨algebraMap K _ r, by simp⟩

omit [CompleteSpace K] in
/-- A nonzero polynomial with coefficients in `K`, viewed in the separated variable `Y`, is
distinguished at the unit radius, with a unit coefficient in its distinguished degree. -/
private theorem exists_isDistinguished_polynomialToOption_map {Q : Polynomial K}
    (hQ : Q ≠ 0) : ∃ s : ℕ,
      PowerSeries.IsDistinguished 1 s (restrictedOptionEquiv
        (toTate _ K (polynomialToOption (Q.map (algebraMap K W)))) : PowerSeries Tate) ∧
      IsUnit (PowerSeries.coeff s (restrictedOptionEquiv
        (toTate _ K (polynomialToOption (Q.map (algebraMap K W)))) :
          PowerSeries Tate)) := by
  obtain ⟨s, hs⟩ := PowerSeries.exists_isDistinguished zero_lt_one
    (PowerSeries.isRestricted_polynomial Q) (by simpa [Polynomial.coe_eq_zero_iff] using hQ)
  have hmap : (restrictedOptionEquiv (toTate _ K (polynomialToOption
      (Q.map (algebraMap K W)))) : PowerSeries Tate) =
      PowerSeries.map (algebraMap K Tate) (Q : PowerSeries K) := by
    rw [restrictedOptionEquiv_toTate_polynomialToOption, Polynomial.map_map,
      ← Polynomial.polynomial_map_coe]
    congr 2
    exact (toTate σ K).comp_algebraMap
  rw [hmap]
  refine ⟨s, hs.map _ (norm_algebraMap_isRestrictedSubring (c := fun _ : σ ↦ (1 : ℝ))), ?_⟩
  rw [PowerSeries.coeff_map]
  exact (isUnit_iff_ne_zero.mpr hs.coeff_ne_zero).map _

/-- The inductive step: Weierstrass division by the minimal polynomial of `Y = X none`. -/
private theorem polynomialsSurject_option (ih : PolynomialsSurject (K := K) σ) :
    PolynomialsSurject (K := K) (Option σ) := by
  intro I _
  -- The minimal polynomial `Q` of `Y` modulo `I`, evaluated at `Y`, lies in `I`.
  set Q := minpoly K (Ideal.Quotient.mk I (X (Option σ) K none))
  have hQ0 : Q ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  set ω : Polynomial W := Q.map (algebraMap K W)
  have hωI : polynomialToOption ω ∈ I := by
    have h : polynomialToOption ω = Polynomial.aeval (X (Option σ) K none) Q := by
      have h' : polynomialToOption.comp (Polynomial.mapRingHom (algebraMap K W)) =
          (Polynomial.aeval (X (Option σ) K none) : Polynomial K →ₐ[K] W').toRingHom :=
        Polynomial.ringHom_ext (fun a ↦ by simp) (by simp)
      exact RingHom.congr_fun h' Q
    rw [← Ideal.Quotient.eq_zero_iff_mem, h, ← Ideal.Quotient.mkₐ_eq_mk K,
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, minpoly.aeval]
  obtain ⟨s, hg, hu⟩ := exists_isDistinguished_polynomialToOption_map (σ := σ) hQ0
  -- The coefficients of a remainder have polynomial representatives modulo `I ∩ W`.
  let J : Ideal W := I.comap (optionC (σ := σ) (R := K))
  have : Algebra.IsIntegral K (W ⧸ J) :=
    Algebra.IsIntegral.of_injective (Ideal.quotientMapₐ I optionC le_rfl)
      Ideal.quotientMap_injective
  let S := ((Ideal.Quotient.mkₐ K I).comp (ofMvPolynomial (Option σ) K)).range
  have hC (a : W) : Ideal.Quotient.mk I (optionC a) ∈ S := by
    obtain ⟨p, hp⟩ := ih J (Ideal.Quotient.mk J a)
    refine ⟨MvPolynomial.rename some p, ?_⟩
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, J,
      Ideal.mem_comap] at hp
    refine Ideal.Quotient.eq.mpr ?_
    rwa [map_sub, optionC_ofMvPolynomial] at hp
  have hY : Ideal.Quotient.mk I (X (Option σ) K none) ∈ S := ⟨MvPolynomial.X none, by simp⟩
  let ψ : Polynomial W →+* W' ⧸ I :=
    (Ideal.Quotient.mk I).comp polynomialToOption
  have hr (r : Polynomial W) : ψ r ∈ S := by
    induction r using Polynomial.induction_on' with
    | add p q hp hq => rw [ψ.map_add]; exact S.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ψ.map_mul, ψ.map_pow]
      simp only [ψ, RingHom.comp_apply, polynomialToOption_C, polynomialToOption_X]
      exact S.mul_mem (hC a) (S.pow_mem hY n)
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, r, -, hqr⟩ := exists_mul_add_eq_of_isDistinguished hg hu f
  have hf : f = q * polynomialToOption ω + polynomialToOption r :=
    optionSeries_injective (by
      rw [map_add, map_mul, optionSeries_polynomialToOption r]
      exact hqr.symm)
  have hfr : Ideal.Quotient.mk I f = ψ r := by
    rw [hf, (Ideal.Quotient.mk I).map_add, (Ideal.Quotient.mk I).map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr hωI, mul_zero, zero_add]
    rfl
  exact hfr ▸ (AlgHom.mem_range _).mp (hr r)

/-- **Polynomials surject onto integral quotients.** If a quotient of the Monsky–Washnitzer
algebra in finitely many variables is integral over `K`, for instance finite-dimensional, then
every class has a polynomial representative. -/
theorem surjective_mkₐ_comp_ofMvPolynomial {σ : Type*} [Finite σ]
    (I : Ideal (washnitzerAlgebra σ K)) [Algebra.IsIntegral K (washnitzerAlgebra σ K ⧸ I)] :
    Function.Surjective ((Ideal.Quotient.mkₐ K I).comp (ofMvPolynomial σ K)) :=
  Finite.induction_empty_option (P := PolynomialsSurject (K := K))
    polynomialsSurject_of_equiv polynomialsSurject_of_isEmpty polynomialsSurject_option σ I

end IntegralQuotient

end washnitzerAlgebra

end TauCeti.Dagger
