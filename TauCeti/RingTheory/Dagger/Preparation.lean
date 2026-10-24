/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Multivariable overconvergent Weierstrass preparation

Over a complete ultrametric normed field `K`, an overconvergent series in `Option σ`
which is distinguished in `Y = X none` of degree `s`, with unit distinguished coefficient,
has a unique factorization as an overconvergent unit times a monic polynomial of degree `s`
over the overconvergent algebra in `σ`. The polynomial has unit Gauss norm.

The factorization is stated through the injective inclusions into the Tate algebras and
`Huber.restrictedOptionEquiv`. Thus both factors belong to the overconvergent algebras,
not merely to their completions. Existence uses unequal radii: the radii in the coefficient
variables can be smaller than the radius in `Y`, as is necessary for `Y + X²`.
Uniqueness is detected at unit radius and needs no completeness hypothesis.

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
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    {ω ω' : Polynomial W₀} (he : IsUnit e) (he' : IsUnit e')
    (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : (Huber.restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
      (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
        Huber.restrictedOptionEquiv (toTate _ K g))
    (h' : (Huber.restrictedOptionEquiv (toTate _ K e') : PowerSeries Tate) *
      (ω'.map (toTate σ K).toRingHom : PowerSeries Tate) =
        Huber.restrictedOptionEquiv (toTate _ K g)) : e = e' ∧ ω = ω' := by
  have hm : (ω.map (toTate σ K).toRingHom).IsMonicOfDegree s :=
    ⟨(Polynomial.natDegree_map_eq_of_injective toTate_injective ω).trans hω.natDegree_eq,
      hω.monic.map _⟩
  have hm' : (ω'.map (toTate σ K).toRingHom).IsMonicOfDegree s :=
    ⟨(Polynomial.natDegree_map_eq_of_injective toTate_injective ω').trans hω'.natDegree_eq,
      hω'.monic.map _⟩
  obtain ⟨heq, hωeq⟩ := hg.eq_and_eq_of_mul_eq_mul one_pos
    ((he.map (toTate _ K)).map Huber.restrictedOptionEquiv.toRingHom)
    ((he'.map (toTate _ K)).map Huber.restrictedOptionEquiv.toRingHom) hm hm' h h'
  exact ⟨toTate_injective (Huber.restrictedOptionEquiv.injective heq),
    Polynomial.map_injective _ toTate_injective hωeq⟩

/-- The monic polynomial in an overconvergent Weierstrass preparation is a Weierstrass
polynomial: its unit-radius Gauss norm is `1`. -/
theorem gaussNorm_eq_one_of_isUnit_isMonicOfDegree_mul_eq [NormOneClass K] {g e : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    {ω : Polynomial W₀} (he : IsUnit e) (hm : ω.IsMonicOfDegree s)
    (heq : (Huber.restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
      (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
        Huber.restrictedOptionEquiv (toTate _ K g)) :
    (ω.map (toTate σ K).toRingHom : PowerSeries Tate).gaussNorm norm 1 = 1 := by
  have hd := PowerSeries.IsDistinguished.of_isUnit_mul (heq ▸ hg) one_pos
    ((he.map (toTate _ K)).map Huber.restrictedOptionEquiv.toRingHom)
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
      (Huber.restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
        (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
          Huber.restrictedOptionEquiv (toTate _ K g) := by
  let c : Option σ → ℝ := fun | none => r | some _ => ρ
  have hr : 1 < r := hρ.trans_le hρr
  let : ∀ i, Fact (0 < c i) := fun
    | none => ⟨zero_lt_one.trans hr⟩
    | some _ => ⟨zero_lt_one.trans hρ⟩
  let Inner := IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)
  let Flat := IsRestricted.subring (R := K) c
  -- Flatten at the unequal polyradii, then restrict to the common radius `ρ > 1`.
  let a : Flat →+* W := (Flat.subtype).codRestrict
    (washnitzerAlgebra (Option σ) K).toSubring fun f ↦ mem_washnitzerAlgebra.mpr
      ⟨ρ, hρ, MvPowerSeries.isRestricted_of_le f.2 (fun _ ↦ (zero_lt_one.trans hρ).le)
        (by intro i; cases i <;> simp [c, hρr])⟩
  let b : Inner →+* W₀ := (Inner.subtype).codRestrict
    (washnitzerAlgebra σ K).toSubring fun f ↦ mem_washnitzerAlgebra.mpr ⟨ρ, hρ, f.2⟩
  let E := a ((Huber.restrictedOptionEquiv (c := c)).symm e)
  let Ω := ω.map b
  refine ⟨E, Ω, ?_, ?_, ?_⟩
  · exact (he.map (Huber.restrictedOptionEquiv (c := c)).symm.toRingHom).map a
  · exact ⟨(hm.monic.natDegree_map b).trans hm.natDegree_eq, hm.monic.map b⟩
  -- Compare in formal series, where coefficient inclusions do not involve norms.
  apply PowerSeries.map_injective (Tate).subtype Subtype.val_injective
  have hE : PowerSeries.map (Tate).subtype
      (Huber.restrictedOptionEquiv (toTate _ K E) : PowerSeries Tate) =
      PowerSeries.map Inner.subtype (e : PowerSeries Inner) := by
    rw [Huber.map_subtype_restrictedOptionEquiv (c := fun _ : Option σ ↦ 1), coe_toTate]
    simp [E, a, Huber.coe_restrictedOptionEquiv_symm, Inner, c]
  have hΩ : PowerSeries.map (Tate).subtype
      (Ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
      PowerSeries.map Inner.subtype (ω : PowerSeries Inner) := by
    ext m : 1
    simp [Ω, b]
  rw [map_mul, hE, hΩ,
    Huber.map_subtype_restrictedOptionEquiv (c := fun _ : Option σ ↦ 1), coe_toTate]
  exact heq

/-- An overconvergent series distinguished in the separated variable is an overconvergent
unit times a monic polynomial of the distinguished degree over the smaller overconvergent
algebra. No characteristic, finiteness of the variable type, or nontriviality of the norm
is required. -/
theorem exists_isUnit_isMonicOfDegree_mul_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) :
    ∃ (e : W) (ω : Polynomial W₀), IsUnit e ∧ ω.IsMonicOfDegree s ∧
      (Huber.restrictedOptionEquiv (toTate _ K e) : PowerSeries Tate) *
        (ω.map (toTate σ K).toRingHom : PowerSeries Tate) =
          Huber.restrictedOptionEquiv (toTate _ K g) := by
  obtain ⟨ρ, hρpos, r, hρ, hρr, -, hgr, G, hG, hd, hunit⟩ :=
    exists_isDistinguished_isUnit_of_isDistinguished_one hg hu (ρ₀ := 2) one_lt_two
  let : Fact (0 < ρ) := hρpos
  have hr : 1 < r := hρ.trans_le hρr
  let c : Option σ → ℝ := fun | none => r | some _ => ρ
  let : ∀ i, Fact (0 < c i) := fun
    | none => ⟨zero_lt_one.trans hr⟩
    | some _ => ⟨zero_lt_one.trans hρ⟩
  let gflat : IsRestricted.subring (R := K) c := ⟨g, MvPowerSeries.isRestricted_of_le hgr
    (fun i ↦ (Fact.out (p := 0 < c i)).le) (by
      intro i
      cases i <;> simp [c, hρr])⟩
  have hGflat : (Huber.restrictedOptionEquiv (c := c) gflat :
      PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ))) = G := by
    ext m : 1
    apply Subtype.ext
    simpa [gflat] using (hG m).symm
  obtain ⟨e, ω, he, hm, heq⟩ := hd.exists_isUnit_isMonicOfDegree_mul_eq hunit
    (zero_lt_one.trans hr) (hGflat ▸ (Huber.restrictedOptionEquiv (c := c) gflat).2)
  apply lift_preparation hρ hρr e ω he hm
  have hgG : PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype G =
      optionEquivLeft σ K (g : MvPowerSeries (Option σ) K) := by
    ext m : 1
    simpa using hG m
  simpa only [map_mul, hgG] using congrArg
    (PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype) heq

/-- Unique multivariable Weierstrass preparation in the Monsky–Washnitzer algebra.
Both the unit and every coefficient of the monic polynomial are overconvergent. -/
theorem existsUnique_isUnit_isMonicOfDegree_mul_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) :
    ∃! p : W × Polynomial W₀, IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧
      (Huber.restrictedOptionEquiv (toTate _ K p.1) : PowerSeries Tate) *
        (p.2.map (toTate σ K).toRingHom : PowerSeries Tate) =
          Huber.restrictedOptionEquiv (toTate _ K g) := by
  obtain ⟨e, ω, he, hm, heq⟩ := exists_isUnit_isMonicOfDegree_mul_eq hg hu
  refine ⟨(e, ω), ⟨he, hm, heq⟩, fun p ⟨he', hm', heq'⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_isUnit_isMonicOfDegree_mul_eq hg he' he hm' hm heq' heq
  exact Prod.ext h1 h2

end Field

end TauCeti.Dagger.washnitzerAlgebra
