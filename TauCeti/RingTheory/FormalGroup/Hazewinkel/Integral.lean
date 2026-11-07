/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.FunctionalEquation
public import TauCeti.RingTheory.MvPolynomial.Expand

/-!
# Hazewinkel's integral polynomial law

The rational law with logarithm `∑ mₙ X^(pⁿ)` descends to a commutative formal group
law over `ℤ[v₁, v₂, …]`. Its specialization defines `hazewinkelIntegralFormalGroup p v`
for a family `v` in any commutative ring, including rings with torsion. Over a
`ℚ`-algebra this recovers `hazewinkelFormalGroup p v`, and hence its logarithm
and Hazewinkel recursion.

Integrality follows from the functional equation with coefficient endomorphism
`vᵢ ↦ vᵢ^p`: expansion of an integer polynomial lifts Frobenius modulo `p`.
In particular one may extend the integral law to `ℤ_(p)[v₁, v₂, …]`; no
classification of p-typical laws over rings with torsion is asserted here.

## References

* M. Hazewinkel, *Constructing formal groups. I. The local one dimensional case*,
  J. Pure Appl. Algebra 9 (1977), 131–149.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2.
-/

public section

noncomputable section

namespace TauCeti

namespace Hazewinkel

variable (p : ℕ) [hp : Fact p.Prime]

/-- Every coefficient of the rational universal Hazewinkel law is an integer polynomial
in its generators. -/
theorem coeff_formalGroup_mem_range (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d
      (hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ)).toPowerSeries ∈
        (MvPolynomial.map (Int.castRingHom ℚ) :
          MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ).range := by
  apply coeff_hazewinkelFormalGroup_mem (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ)
    (MvPolynomial.expand p).toRingHom
  · rintro a ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := MvPolynomial.natCast_dvd_expand_sub_pow p f
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) g, ⟨g, rfl⟩, ?_⟩
    simpa only [map_sub, MvPolynomial.map_expand, map_pow, map_mul, map_natCast,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hg
  · intro j
    exact MvPolynomial.expand_X p j
  · intro j
    exact ⟨MvPolynomial.X j, MvPolynomial.map_X _ _⟩

/-- Coefficientwise descent of the rational universal law. -/
private def integralSeries : MvPowerSeries (Fin 2) (MvPolynomial ℕ+ ℤ) :=
  fun d ↦ (coeff_formalGroup_mem_range p d).choose

private theorem map_integralSeries :
    (integralSeries p).map (MvPolynomial.map (Int.castRingHom ℚ)) =
      (hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ)).toPowerSeries := by
  ext1 d
  exact (coeff_formalGroup_mem_range p d).choose_spec

/-- Hazewinkel's commutative formal group law over the integer polynomial ring
on the generators `v₁, v₂, …`. -/
def integralFormalGroup : FormalGroup (MvPolynomial ℕ+ ℤ) :=
  FormalGroup.ofMap (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    (integralSeries p) (hazewinkelFormalGroup p MvPolynomial.X) (map_integralSeries p)

/-- Extending the integral polynomial law to rational coefficients recovers the law
defined by Hazewinkel's logarithm. -/
@[simp]
theorem map_integralFormalGroup :
    (integralFormalGroup p).map (MvPolynomial.map (Int.castRingHom ℚ)) =
      hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ) := by
  apply FormalGroup.map_ofMap

instance : (integralFormalGroup p).IsComm := by
  have : ((integralFormalGroup p).map (MvPolynomial.map (Int.castRingHom ℚ))).IsComm := by
    rw [map_integralFormalGroup]
    infer_instance
  exact FormalGroup.isComm_of_map
    (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)

end Hazewinkel

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

/-- The integral Hazewinkel formal group law specialized at a family of generators in
an arbitrary commutative ring. -/
def hazewinkelIntegralFormalGroup (v : ℕ+ → R) : FormalGroup R :=
  (Hazewinkel.integralFormalGroup p).map (MvPolynomial.eval₂Hom (Int.castRingHom R) v)

/-- Specialization of the integral polynomial law is coefficient evaluation. -/
theorem hazewinkelIntegralFormalGroup_def (v : ℕ+ → R) :
    hazewinkelIntegralFormalGroup p v =
      (Hazewinkel.integralFormalGroup p).map (MvPolynomial.eval₂Hom (Int.castRingHom R) v) :=
  (rfl)

instance (v : ℕ+ → R) : (hazewinkelIntegralFormalGroup p v).IsComm := by
  rw [hazewinkelIntegralFormalGroup_def]
  infer_instance

/-- Specialization of the integral Hazewinkel law commutes with arbitrary coefficient maps,
including maps to rings with torsion. -/
@[simp]
theorem map_hazewinkelIntegralFormalGroup (v : ℕ+ → R) (f : R →+* S) :
    (hazewinkelIntegralFormalGroup p v).map f = hazewinkelIntegralFormalGroup p (f ∘ v) := by
  rw [hazewinkelIntegralFormalGroup_def, hazewinkelIntegralFormalGroup_def, FormalGroup.map_comp]
  congr 1
  ext j
  · simp
  · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Function.comp_apply]

/-- Specializing at the polynomial generators returns the integral polynomial law. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_X :
    hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℤ) =
      Hazewinkel.integralFormalGroup p := by
  rw [hazewinkelIntegralFormalGroup_def]
  have h : MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial ℕ+ ℤ)) MvPolynomial.X =
      RingHom.id (MvPolynomial ℕ+ ℤ) := by ext <;> simp
  rw [h, FormalGroup.map_id]

/-- Over a rational algebra, integral specialization agrees with the formal group law
defined using Hazewinkel's logarithm. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_eq [Algebra ℚ R] (v : ℕ+ → R) :
    hazewinkelIntegralFormalGroup p v = hazewinkelFormalGroup p v := by
  have h : (MvPolynomial.eval₂Hom (algebraMap ℚ R) v).comp
      (MvPolynomial.map (Int.castRingHom ℚ)) = MvPolynomial.eval₂Hom (Int.castRingHom R) v := by
    ext <;> simp
  rw [hazewinkelIntegralFormalGroup_def, ← h, ← FormalGroup.map_comp,
    Hazewinkel.map_integralFormalGroup, map_hazewinkelFormalGroup]
  congr 1
  funext j
  exact MvPolynomial.eval₂_X _ _ _

end TauCeti
