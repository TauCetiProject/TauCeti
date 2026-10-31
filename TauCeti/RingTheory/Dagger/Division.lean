/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.DivMod

/-!
# Multivariable overconvergent Weierstrass division

Over a complete ultrametric normed field `K`, let `g` be an overconvergent series in the
variables `Option σ` which, as a series in `Y = X none` over the Tate algebra in `σ`, is
distinguished of degree `s` at unit radius with unit coefficient in degree `s`. Then every
overconvergent series `f` is uniquely

```text
f = g * q + r,    q overconvergent,    r a polynomial in Y of degree < s,
```

where the coefficients of `r` are overconvergent series in `σ`. Thus the quotient lies in the
Monsky–Washnitzer algebra `K⟨X, Y⟩†` and the remainder in `K⟨X⟩†[Y]`, not merely in their
completions.

As for preparation, the decomposition is stated through the injective inclusions into the Tate
algebras and `Huber.restrictedOptionEquiv`. Existence divides at unequal radii, chosen by
`exists_isDistinguished_isUnit_of_isDistinguished_one` so that both `f` and `g` are restricted
there: the radii in the coefficient variables can be smaller than the radius in `Y`, as is
necessary for `Y + X²`. The division itself is the fixed-radius division
`PowerSeries.IsMulDistinguished.weierstrassDiv` over the resulting complete ring of series
restricted in `σ`. Uniqueness is detected at unit radius and needs no completeness hypothesis
and no unit condition on the distinguished coefficient.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.eq_and_eq_of_mul_add_eq_mul_add`: uniqueness of the quotient
  and the remainder.
* `TauCeti.Dagger.washnitzerAlgebra.exists_mul_add_eq`: existence of overconvergent Weierstrass
  division.
* `TauCeti.Dagger.washnitzerAlgebra.existsUnique_mul_add_eq`: the unique-existence form.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(i).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2.
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

omit [NormMulClass K] in
/-- A polynomial over `W₀` of degree less than `s`, viewed as a series over the Tate algebra,
vanishes in every degree at least `s`. -/
private theorem coeff_map_toTate_eq_zero {r : Polynomial W₀} {s : ℕ} (hr : r.degree < s)
    {m : ℕ} (hm : s ≤ m) :
    PowerSeries.coeff m (r.map (toTate σ K).toRingHom : PowerSeries Tate) = 0 := by
  rw [Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_degree_lt
    ((Polynomial.degree_map_le).trans_lt (hr.trans_le (by exact_mod_cast hm)))

/-- **Uniqueness in overconvergent Weierstrass division.** For `g` distinguished of degree `s`
at unit radius in the separated variable, two decompositions `f = g * q + r` with `q`
overconvergent and `r` a polynomial of degree less than `s` over the overconvergent algebra in
`σ` agree. The equations are tested in the iterated Tate algebra, whose inclusions are
injective. -/
theorem eq_and_eq_of_mul_add_eq_mul_add {g f q q' : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    {r r' : Polynomial W₀} (hr : r.degree < s) (hr' : r'.degree < s)
    (h : (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate) *
        (Huber.restrictedOptionEquiv (toTate _ K q) : PowerSeries Tate) +
      (r.map (toTate σ K).toRingHom : PowerSeries Tate) =
        Huber.restrictedOptionEquiv (toTate _ K f))
    (h' : (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate) *
        (Huber.restrictedOptionEquiv (toTate _ K q') : PowerSeries Tate) +
      (r'.map (toTate σ K).toRingHom : PowerSeries Tate) =
        Huber.restrictedOptionEquiv (toTate _ K f)) : q = q' ∧ r = r' := by
  rw [mul_comm] at h h'
  obtain ⟨hq, hrr⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add one_pos (fun x ↦ norm_mul _ _)
    (Huber.restrictedOptionEquiv (toTate _ K q)).2 (Huber.restrictedOptionEquiv (toTate _ K q')).2
    (fun _ ↦ coeff_map_toTate_eq_zero hr) (fun _ ↦ coeff_map_toTate_eq_zero hr') (h.trans h'.symm)
  exact ⟨toTate_injective (Huber.restrictedOptionEquiv.injective (Subtype.ext hq)),
    Polynomial.map_injective _ toTate_injective (Polynomial.coe_inj.mp hrr)⟩

end NormedCommRing

section Field

variable [NormedField K] [IsUltrametricDist K]

/-- Transport a division at unequal radii to the overconvergent algebras. -/
private theorem lift_division {g f : W} {s : ℕ} {ρ r : ℝ} [Fact (0 < ρ)]
    (hρ : 1 < ρ) (hρr : ρ ≤ r)
    (q : PowerSeries.IsRestricted.subring
      (R := IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)) r)
    (rem : Polynomial (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ))) (hrem : rem.degree < s)
    (heq : optionEquivLeft σ K (g : MvPowerSeries (Option σ) K) *
        PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype
          (q : PowerSeries _) +
      PowerSeries.map (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)).subtype
        (rem : PowerSeries _) = optionEquivLeft σ K (f : MvPowerSeries (Option σ) K)) :
    ∃ (q : W) (r : Polynomial W₀), r.degree < s ∧
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate) *
          (Huber.restrictedOptionEquiv (toTate _ K q) : PowerSeries Tate) +
        (r.map (toTate σ K).toRingHom : PowerSeries Tate) =
          Huber.restrictedOptionEquiv (toTate _ K f) := by
  let c : Option σ → ℝ := fun | none => r | some _ => ρ
  have hr : 1 < r := hρ.trans_le hρr
  let : ∀ i, Fact (0 < c i) := fun
    | none => ⟨zero_lt_one.trans hr⟩
    | some _ => ⟨zero_lt_one.trans hρ⟩
  let Inner := IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)
  let Flat := IsRestricted.subring (R := K) c
  -- Flatten at the unequal polyradii, then restrict to the common radius `ρ > 1`.
  let a : Flat →+* W := (Flat.subtype).codRestrict
    (washnitzerAlgebra (Option σ) K).toSubring fun h ↦ mem_washnitzerAlgebra.mpr
      ⟨ρ, hρ, MvPowerSeries.isRestricted_of_le h.2 (fun _ ↦ (zero_lt_one.trans hρ).le)
        (by intro i; cases i <;> simp [c, hρr])⟩
  let b : Inner →+* W₀ := (Inner.subtype).codRestrict
    (washnitzerAlgebra σ K).toSubring fun h ↦ mem_washnitzerAlgebra.mpr ⟨ρ, hρ, h.2⟩
  refine ⟨a ((Huber.restrictedOptionEquiv (c := c)).symm q), rem.map b,
    (Polynomial.degree_map_le).trans_lt hrem, ?_⟩
  -- Compare in formal series, where coefficient inclusions do not involve norms.
  apply PowerSeries.map_injective (Tate).subtype Subtype.val_injective
  have hmap (h : W) : PowerSeries.map (Tate).subtype
      (Huber.restrictedOptionEquiv (toTate _ K h) : PowerSeries Tate) =
        optionEquivLeft σ K (h : MvPowerSeries (Option σ) K) := by
    rw [Huber.map_subtype_restrictedOptionEquiv (c := fun _ : Option σ ↦ 1), coe_toTate]
  have hQ : optionEquivLeft σ K
      ((a ((Huber.restrictedOptionEquiv (c := c)).symm q) : W) : MvPowerSeries (Option σ) K) =
      PowerSeries.map Inner.subtype (q : PowerSeries Inner) := by
    simp [a, Huber.coe_restrictedOptionEquiv_symm, Inner, c]
  have hR : PowerSeries.map (Tate).subtype
      ((rem.map b).map (toTate σ K).toRingHom : PowerSeries Tate) =
      PowerSeries.map Inner.subtype (rem : PowerSeries Inner) := by
    ext m : 1
    simp [b]
  rw [map_add, map_mul, hmap, hmap, hmap, hR, hQ]
  exact heq

/-- **Overconvergent Weierstrass division.** Over a complete ultrametric normed field, let `g` be
an overconvergent series in the variables `Option σ` which is distinguished of degree `s` at unit
radius in the separated variable `Y = X none`, with unit coefficient in degree `s`. Then every
overconvergent `f` is `g * q + r` with `q` overconvergent and `r` a polynomial in `Y` of degree
less than `s` whose coefficients are overconvergent in `σ`. No characteristic, finiteness of the
variable type, or nontriviality of the norm is required. -/
theorem exists_mul_add_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W) :
    ∃ (q : W) (r : Polynomial W₀), r.degree < s ∧
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate) *
          (Huber.restrictedOptionEquiv (toTate _ K q) : PowerSeries Tate) +
        (r.map (toTate σ K).toRingHom : PowerSeries Tate) =
          Huber.restrictedOptionEquiv (toTate _ K f) := by
  -- Choose the radii inside the convergence radius of `f`, so that `f` is restricted there too.
  obtain ⟨ρf, hρf, hfρ⟩ := mem_washnitzerAlgebra.mp f.2
  obtain ⟨ρ, hρpos, r, hρ, hρr, hrf, hgr, G, hG, hd, hunit⟩ :=
    exists_isDistinguished_isUnit_of_isDistinguished_one hg hu hρf
  let : Fact (0 < ρ) := hρpos
  have hr0 : 0 < r := zero_lt_one.trans (hρ.trans_le hρr)
  let c : Option σ → ℝ := fun | none => r | some _ => ρ
  let : ∀ i, Fact (0 < c i) := fun
    | none => ⟨hr0⟩
    | some _ => ⟨zero_lt_one.trans hρ⟩
  have hc0 (i : Option σ) : 0 ≤ c i := (Fact.out (p := 0 < c i)).le
  have hc (i : Option σ) : c i ≤ r := by cases i <;> simp [c, hρr]
  let Inner := IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)
  -- Shrink the common radius `r` to the polyradius `c`, and divide there.
  let gflat : IsRestricted.subring (R := K) c := ⟨g, MvPowerSeries.isRestricted_of_le hgr hc0 hc⟩
  let fflat : IsRestricted.subring (R := K) c := ⟨f, MvPowerSeries.isRestricted_of_le
    (MvPowerSeries.isRestricted_of_le hfρ (fun _ ↦ hr0.le) fun _ ↦ hrf) hc0 hc⟩
  have hGflat : (Huber.restrictedOptionEquiv (c := c) gflat : PowerSeries Inner) = G := by
    ext m : 1
    apply Subtype.ext
    simpa [gflat] using (hG m).symm
  have hdiv : PowerSeries.IsMulDistinguished r s
      (Huber.restrictedOptionEquiv (c := c) gflat : PowerSeries Inner) :=
    hGflat ▸ PowerSeries.isMulDistinguished_iff_isUnit.mpr ⟨hd, hunit⟩
  set F := Huber.restrictedOptionEquiv (c := c) fflat
  apply lift_division hρ hρr (hdiv.weierstrassDiv hr0 F) (hdiv.weierstrassMod hr0 F)
    (hdiv.degree_weierstrassMod_lt hr0 F)
  have hqr := congrArg Subtype.val (hdiv.mul_weierstrassDiv_add_weierstrassMod hr0 F)
  simp only [AddMemClass.coe_add, MulMemClass.coe_mul,
    PowerSeries.coe_polynomialToRestricted] at hqr
  rw [← Huber.map_subtype_restrictedOptionEquiv (c := c) gflat,
    ← Huber.map_subtype_restrictedOptionEquiv (c := c) fflat, ← map_mul, ← map_add, hqr]

/-- **Unique overconvergent Weierstrass division** (Grosse-Klönne, §1.3(i)). Over a complete
ultrametric normed field, for `g` an overconvergent series distinguished of degree `s` at unit
radius in the separated variable, with unit coefficient in degree `s`, every overconvergent `f`
is in exactly one way `g * q + r` with `q` overconvergent and `r` a polynomial in the separated
variable of degree less than `s` over the overconvergent algebra in the remaining variables. -/
theorem existsUnique_mul_add_eq [CompleteSpace K] {g : W} {s : ℕ}
    (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate))) (f : W) :
    ∃! p : W × Polynomial W₀, p.2.degree < s ∧
      (Huber.restrictedOptionEquiv (toTate _ K g) : PowerSeries Tate) *
          (Huber.restrictedOptionEquiv (toTate _ K p.1) : PowerSeries Tate) +
        (p.2.map (toTate σ K).toRingHom : PowerSeries Tate) =
          Huber.restrictedOptionEquiv (toTate _ K f) := by
  obtain ⟨q, r, hr, h⟩ := exists_mul_add_eq hg hu f
  refine ⟨(q, r), ⟨hr, h⟩, fun p ⟨hr', h'⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_add_eq_mul_add hg hr' hr h' h
  exact Prod.ext h1 h2

end Field

end TauCeti.Dagger.washnitzerAlgebra
