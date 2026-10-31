/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.Dagger.OptionSeries
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Multivariable overconvergent Weierstrass preparation

Over a complete ultrametric normed field `K`, an overconvergent series in `Option σ`
which is distinguished in `Y = X none` of degree `s`, with unit distinguished coefficient,
has a unique factorization as an overconvergent unit times a monic polynomial of degree `s`
over the overconvergent algebra in `σ`. The polynomial has unit Gauss norm.

The factorization is stated through the injective inclusions into the Tate algebras and
`MvPowerSeries.restrictedOptionEquiv`. Thus both factors belong to the overconvergent algebras,
not merely to their completions. Existence uses unequal radii: the radii in the coefficient
variables can be smaller than the radius in `Y`, as is necessary for `Y + X²`.
Uniqueness is detected at unit radius and needs no completeness hypothesis.
`washnitzerAlgebra.exists_isUnit_isMonicOfDegree_mul_polynomialToOption_eq` restates existence
in the overconvergent algebra itself, evaluating the monic polynomial at `Y` by
`washnitzerAlgebra.polynomialToOption`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(ii).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1.

The construction uses `exists_isDistinguished_isUnit_of_isDistinguished_one` for radius
selection and `PowerSeries.IsDistinguished.exists_isUnit_isMonicOfDegree_mul_eq` for
preparation over the resulting complete coefficient ring.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*}

local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))
local notation "W" => washnitzerAlgebra (Option σ) K
local notation "W₀" => washnitzerAlgebra σ K

section NormedCommRing

variable [NormedCommRing K] [IsUltrametricDist K] [NormMulClass K]

/-- Two overconvergent unit-times-monic factorizations of a distinguished series agree.
The equation is tested in the iterated Tate algebra, whose inclusions are injective. -/
theorem eq_and_eq_of_isUnit_isMonicOfDegree_mul_eq {g e e' : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    {ω ω' : Polynomial W₀} (he : IsUnit e) (he' : IsUnit e')
    (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : (restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
      (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
        restrictedOptionEquiv (toTate _ K g))
    (h' : (restrictedOptionEquiv (toTate _ K e') : PowerSeries Tate) *
      (ω'.map (toTate σ K).toRingHom : PowerSeries Tate) =
        restrictedOptionEquiv (toTate _ K g)) : e = e' ∧ ω = ω' := by
  have hm : (ω.map (toTate σ K).toRingHom).IsMonicOfDegree s :=
    ⟨(Polynomial.natDegree_map_eq_of_injective toTate_injective ω).trans hω.natDegree_eq,
      hω.monic.map _⟩
  have hm' : (ω'.map (toTate σ K).toRingHom).IsMonicOfDegree s :=
    ⟨(Polynomial.natDegree_map_eq_of_injective toTate_injective ω').trans hω'.natDegree_eq,
      hω'.monic.map _⟩
  obtain ⟨heq, hωeq⟩ := hg.eq_and_eq_of_mul_eq_mul one_pos
    ((he.map (toTate _ K)).map restrictedOptionEquiv.toRingHom)
    ((he'.map (toTate _ K)).map restrictedOptionEquiv.toRingHom) hm hm' h h'
  exact ⟨toTate_injective (restrictedOptionEquiv.injective heq),
    Polynomial.map_injective _ toTate_injective hωeq⟩

/-- The monic polynomial in an overconvergent Weierstrass preparation is a Weierstrass
polynomial: its unit-radius Gauss norm is `1`. -/
theorem gaussNorm_eq_one_of_isUnit_isMonicOfDegree_mul_eq {g e : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    {ω : Polynomial W₀} (he : IsUnit e) (hm : ω.IsMonicOfDegree s)
    (heq : (restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
      (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
        restrictedOptionEquiv (toTate _ K g)) :
    (ω.map (toTate σ K).toRingHom : PowerSeries Tate).gaussNorm norm 1 = 1 := by
  have hcoeff : ((PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate) : Tate) :
        MvPowerSeries σ K) ≠ 0 := fun h ↦ hg.coeff_ne_zero (Subtype.ext h)
  obtain ⟨d, hd⟩ := (ne_zero_iff_exists_coeff_ne_zero _).mp hcoeff
  have : Nontrivial K := nontrivial_of_ne _ _ hd
  have : NormOneClass K := NormMulClass.toNormOneClass
  have hd := PowerSeries.IsDistinguished.of_isUnit_mul (heq ▸ hg) one_pos
    ((he.map (toTate _ K)).map restrictedOptionEquiv.toRingHom)
  rw [← hd.norm_coeff_mul_pow_eq]
  simp [Polynomial.coeff_coe, ← hm.natDegree_eq, hm.monic.coeff_natDegree]

end NormedCommRing

section Field

variable [NormedField K] [IsUltrametricDist K]

/-- Transport a preparation at unequal radii to the overconvergent algebras. -/
private theorem lift_preparation {g : W} {s : ℕ} {ρ r : ℝ} [Fact (0 < ρ)]
    (hρ : 1 < ρ) (hρr : ρ ≤ r)
    (e : PowerSeries.IsRestricted.subring
      (R := IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)) r)
    (ω : Polynomial (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)))
    (he : IsUnit e) (hm : ω.IsMonicOfDegree s)
    (heq : PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype
        (e : PowerSeries _) *
      PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype
        (ω : PowerSeries _) = optionEquivLeft σ K (g : MvPowerSeries (Option σ) K)) :
    ∃ (e : W) (ω : Polynomial W₀), IsUnit e ∧ ω.IsMonicOfDegree s ∧
      (restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
        (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
          restrictedOptionEquiv (toTate _ K g) := by
  let c : Option σ → ℝ := splitRadius r ρ
  let : ∀ i, Fact (0 < c i) := fun i ↦ ⟨splitRadius_pos Fact.out hρr i⟩
  let Inner := IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)
  let Flat := IsRestricted.subring (R := K) c
  -- Flatten at the unequal polyradii, then restrict to the common radius `ρ > 1`.
  let a : Flat →+* W := ofRestricted hρ (le_splitRadius hρr)
  let b : Inner →+* W₀ := ofRestricted hρ fun _ ↦ le_rfl
  let E := a ((restrictedOptionEquiv (c := c)).symm e)
  let Ω := ω.map b
  refine ⟨E, Ω, ?_, ?_, ?_⟩
  · exact (he.map (restrictedOptionEquiv (c := c)).symm.toRingHom).map a
  · exact ⟨(hm.monic.natDegree_map b).trans hm.natDegree_eq, hm.monic.map b⟩
  -- Compare in formal series, where coefficient inclusions do not involve norms.
  apply PowerSeries.map_injective (Tate).subtype Subtype.val_injective
  have hE : PowerSeries.map (Tate).subtype
      (restrictedOptionEquiv (toTate _ K E) : PowerSeries Tate) =
      PowerSeries.map Inner.subtype (e : PowerSeries Inner) := by
    rw [map_subtype_restrictedOptionEquiv (c := fun _ : Option σ ↦ 1), coe_toTate]
    simp [E, a, coe_restrictedOptionEquiv_symm, Flat, Inner, c]
  have hΩ : PowerSeries.map (Tate).subtype
      (Ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
      PowerSeries.map Inner.subtype (ω : PowerSeries Inner) := by
    ext m : 1
    simp [Ω, b, Inner]
  rw [map_mul, hE, hΩ,
    map_subtype_restrictedOptionEquiv (c := fun _ : Option σ ↦ 1), coe_toTate]
  exact heq

/-- An overconvergent series distinguished of degree `s` at unit radius in the separated
variable, with unit coefficient in degree `s`, is an overconvergent unit times a monic
polynomial of degree `s` over the smaller overconvergent algebra. No characteristic,
finiteness of the variable type, or nontriviality of the norm is required. -/
theorem exists_isUnit_isMonicOfDegree_mul_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) :
    ∃ (e : W) (ω : Polynomial W₀), IsUnit e ∧ ω.IsMonicOfDegree s ∧
      (restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
        (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
          restrictedOptionEquiv (toTate _ K g) := by
  obtain ⟨ρ, hρpos, r, hρ, hρr, -, hgr, G, hG, hd, hunit⟩ :=
    exists_isDistinguished_isUnit_of_isDistinguished_one hg hu (ρ₀ := 2) one_lt_two
  let : Fact (0 < ρ) := hρpos
  have hgG : PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype G =
      optionEquivLeft σ K (g : MvPowerSeries (Option σ) K) := by
    ext m : 1
    simpa using hG m
  obtain ⟨e, ω, he, hm, heq⟩ := hd.exists_isUnit_isMonicOfDegree_mul_eq hunit
    (zero_lt_one.trans (hρ.trans_le hρr))
    (isRestricted_of_map_subtype_eq_optionEquivLeft hρr hgr hgG)
  apply lift_preparation hρ hρr e ω he hm
  simpa only [map_mul, hgG] using congrArg
    (PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype) heq

/-- Overconvergent Weierstrass preparation stated in `K⟨X, Y⟩†` itself: a series distinguished
of degree `s` at unit radius in the separated variable, with unit coefficient in degree `s`, is
an overconvergent unit times the evaluation at `Y` of a monic polynomial of degree `s` over the
smaller overconvergent algebra. -/
theorem exists_isUnit_isMonicOfDegree_mul_polynomialToOption_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) :
    ∃ (e : W) (ω : Polynomial W₀), IsUnit e ∧ ω.IsMonicOfDegree s ∧
      e * polynomialToOption ω = g := by
  obtain ⟨e, ω, he, hm, heq⟩ := exists_isUnit_isMonicOfDegree_mul_eq hg hu
  refine ⟨e, ω, he, hm, toTate_injective (restrictedOptionEquiv.injective ?_)⟩
  apply Subtype.ext
  rw [map_mul, map_mul, Subring.coe_mul, restrictedOptionEquiv_toTate_polynomialToOption, heq]

/-- Unique multivariable Weierstrass preparation in the Monsky–Washnitzer algebra.
The series is distinguished of degree `s` at unit radius in the separated variable,
with unit coefficient in degree `s`.
Both the unit and every coefficient of the monic polynomial are overconvergent. -/
theorem existsUnique_isUnit_isMonicOfDegree_mul_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) :
    ∃! p : W × Polynomial W₀, IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧
      (restrictedOptionEquiv (toTate _ K p.1) : PowerSeries Tate) *
        (p.2.map (toTate σ K).toRingHom : PowerSeries Tate) =
          restrictedOptionEquiv (toTate _ K g) := by
  obtain ⟨e, ω, he, hm, heq⟩ := exists_isUnit_isMonicOfDegree_mul_eq hg hu
  refine ⟨(e, ω), ⟨he, hm, heq⟩, fun p ⟨he', hm', heq'⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_isUnit_isMonicOfDegree_mul_eq hg he' he hm' hm heq' heq
  exact Prod.ext h1 h2

end Field

end TauCeti.Dagger.washnitzerAlgebra
