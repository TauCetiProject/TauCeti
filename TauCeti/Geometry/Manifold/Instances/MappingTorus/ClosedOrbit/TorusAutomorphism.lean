/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.CatMap
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit.Lefschetz

/-!
# The orbit zeta function of the suspension of a toral automorphism

Let `p > 0` and let `A ∈ GL(ι, ℤ)` act on the torus `Tⁿ = ι → AddCircle p` by the diffeomorphism
`φ(x) = A • x` (`Diffeomorph.constSmul`), with mapping torus `Y_φ`. Suppose that no iterate of
`φ` is degenerate, `det (1 - Aⁿ) ≠ 0` for every `n ≥ 1`, as for a hyperbolic matrix. Then each
`φⁿ` has finitely many fixed points
(`AddCircle.finite_ptsOfPeriod_generalLinearGroup_smul_iff`), which is what the fixed-point form of
the orbit zeta function of the closed orbits of the suspension flow on `Y_φ` needs. That orbit zeta
function is taken over a choice of one point on each periodic orbit of `φ`, which always exists
(`Function.exists_forall_mem_periodicPts_existsUnique_iterate_eq`), labelled by the signs
`sgn det (1 - d(φᵏ))` of the return maps, and specialized along the integral time period
`N : H₁(Y_φ; ℤ) → ℤ`.

Over a field `k` of characteristic zero this univariate orbit zeta function is the Lefschetz zeta
function `exp (∑_{n ≥ 1} L(φⁿ) tⁿ / n)` of `φ`
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_lefschetzZeta`).
Indeed, by `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff`
this is the Lefschetz fixed-point formula for every iterate of `φ`, and for a toral automorphism
both sides of that formula are `det (1 - Aⁿ)` (`AddCircle.`
`finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber`).

On the two-torus, for an area-preserving `A`, `det A = 1`, the univariate orbit zeta function is
therefore the homology determinant formula `det (1 - t A) / (1 - t)²`
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_charpolyRev_mul`).
For Arnold's cat map `A = !![2, 1; 1, 1]`, every iterate of which is nondegenerate, it is
`(1 - 3 t + t²) / (1 - t)² = 1 - t - 2 t² - 3 t³ - ⋯`
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_constSmul_catMapUnit`).

## Main results

* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_lefschetzZeta`:
  for a toral automorphism without degenerate iterates, the univariate orbit zeta function of its
  suspension is its Lefschetz zeta function.
* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_charpolyRev_mul`:
  on the two-torus, for `det A = 1`, it is `det (1 - t A) / (1 - t)²`.
* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_constSmul_catMapUnit`: for the cat map it is
  `1 - t - 2 t² - 3 t³ - ⋯`.

## References

* E.-N. Ionel and T. H. Parker, *The Gromov invariants of Ruan–Tian and Taubes*, Math. Res. Lett.
  4 (1997), 521–532, Lemma 3.1 and Theorem 5.1.
* A. Katok and B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 1.8.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff PowerSeries

namespace TauCeti.SmoothMappingTorus

open AddCircle NovikovSeries

variable {p : ℝ} [Fact (0 < p)] {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*}
  {x : κ → ι → AddCircle p} {d : κ → ℕ}

/-- **The univariate orbit zeta function of the suspension of a toral automorphism.** Let
`A ∈ GL(ι, ℤ)` act on the torus `ι → AddCircle p` by the diffeomorphism `φ(x) = A • x`, with
`det (1 - Aⁿ) ≠ 0` for every `n ≥ 1`, and let `x i` be points of least periods `d i`, one on each
periodic orbit of `φ`. Over a field `k` of characteristic zero, the pushforward along the integral
time period of the orbit zeta function of the closed orbits of the suspension of `φ` is the image at
`t = e^1` of the Lefschetz zeta function `exp (∑_{n ≥ 1} L(φⁿ) tⁿ / n)` of `φ`. -/
theorem mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_lefschetzZeta (k : Type) [Field k]
    [Algebra ℚ k] {A : GL ι ℤ} (hA : ∀ n, 0 < n → (1 - (A : Matrix ι ι ℤ) ^ n).det ≠ 0)
    (hxd : ∀ i, IsPeriodicPt (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A)
      (d i) (x i)) (hd : ∀ i, 0 < d i)
    (hmin : ∀ i, minimalPeriod (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A)
      (x i) = d i)
    (hrep : ∀ y ∈ periodicPts (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A),
      ∃! i, ∃ j, (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A)^[j] (x i) = y) :
    mapRingHom (RingHom.id k)
        (intTimePeriodHom (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A))
        (exists_period_rescale_intTimePeriodHom _)
        (orbitZeta k (timePeriodHom _) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp)
        ((⟨fun y ↦ A • y, continuous_const_smul A⟩ :
          C(ι → AddCircle p, ι → AddCircle p)).lefschetzZeta k) := by
  -- Every iterate has finitely many fixed points.
  have hfin (n : ℕ) (hn : 0 < n) :
      (ptsOfPeriod (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A :
        (ι → AddCircle p) ≃ₘ⟮_, _⟯ (ι → AddCircle p)) n).Finite := by
    rw [Diffeomorph.coe_constSmul]
    exact (finite_ptsOfPeriod_generalLinearGroup_smul_iff p A n).2 (hA n hn)
  have := algebraRat.charZero k
  have hφ : (⟨Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A,
      (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A).continuous⟩ :
        C(ι → AddCircle p, ι → AddCircle p)) = ⟨fun y ↦ A • y, continuous_const_smul A⟩ :=
    ContinuousMap.ext fun y ↦ Diffeomorph.constSmul_apply A y
  rw [← hφ]
  refine (mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff hfin hxd hd hmin hrep k).2
    fun n _ ↦ ?_
  -- The Lefschetz fixed-point formula for `φⁿ`, stated for every continuous map equal to
  -- `x ↦ A • x`, since the diffeomorphism occurs in the dependent type of the fixed points.
  have key (f : (ι → AddCircle p) → ι → AddCircle p) (hf : Continuous f)
      (hfA : f = fun y ↦ A • y) :
      ((∑ᶠ y : {y // f^[n] y = y}, (SignType.sign (LinearMap.det (LinearMap.id -
        fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f^[n] y)) : ℤ) : ℤ) : k) =
        (⟨f^[n], hf.iterate n⟩ : C(ι → AddCircle p, ι → AddCircle p)).lefschetzNumber k := by
    subst hfA
    exact
      finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber
        p k A n
  exact key _ (Diffeomorph.continuous _) (Diffeomorph.coe_constSmul A)

/-- **The univariate orbit zeta function of the suspension of an area-preserving linear map of the
two-torus.** Let `A ∈ SL(2, ℤ)` act on the torus `Fin 2 → AddCircle p` by the diffeomorphism
`φ(x) = A • x`, with `det (1 - Aⁿ) ≠ 0` for every `n ≥ 1`, and let `x i` be points of least
periods `d i`, one on each periodic orbit of `φ`. The pushforward along the integral time period of
the orbit zeta function of the closed orbits of the suspension of `φ` is the image at `t = e^1` of
`det (1 - t A) / (1 - t)²`. -/
theorem mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_charpolyRev_mul
    {x : κ → Fin 2 → AddCircle p} {A : GL (Fin 2) ℤ}
    (hA : ∀ n, 0 < n → (1 - (A : Matrix (Fin 2) (Fin 2) ℤ) ^ n).det ≠ 0)
    (hdet : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1)
    (hxd : ∀ i, IsPeriodicPt
      (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ A) (d i) (x i))
    (hd : ∀ i, 0 < d i)
    (hmin : ∀ i, minimalPeriod
      (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ A) (x i) = d i)
    (hrep : ∀ y ∈ periodicPts
        (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ A),
      ∃! i, ∃ j,
        (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ A)^[j] (x i) = y) :
    mapRingHom (RingHom.id ℚ)
        (intTimePeriodHom (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ A))
        (exists_period_rescale_intTimePeriodHom _)
        (orbitZeta ℚ (timePeriodHom _) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
              (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ A)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp)
        ((((A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)).charpolyRev : ℚ⟦X⟧) *
          PowerSeries.mk 1 ^ 2) := by
  rw [mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_lefschetzZeta ℚ hA hxd hd hmin hrep,
    lefschetzZeta_generalLinearGroup_smul_eq_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative,
    subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul p hdet]

/-- **The univariate orbit zeta function of the suspension of the cat map.** Let `φ(x) = P • x` be
Arnold's cat map of the torus `Fin 2 → AddCircle p`, `P = !![2, 1; 1, 1]`, and let `x i` be points
of least periods `d i`, one on each periodic orbit of `φ`. The pushforward along the integral time
period of the orbit zeta function of the closed orbits of the suspension of `φ` is the image at
`t = e^1` of `(1 - 3 t + t²) / (1 - t)² = 1 - t - 2 t² - 3 t³ - ⋯`. -/
theorem mapRingHom_orbitZeta_constSmul_catMapUnit {x : κ → Fin 2 → AddCircle p}
    (hxd : ∀ i, IsPeriodicPt
      (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ catMapUnit) (d i) (x i))
    (hd : ∀ i, 0 < d i)
    (hmin : ∀ i, minimalPeriod
      (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ catMapUnit) (x i) = d i)
    (hrep : ∀ y ∈ periodicPts
        (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ catMapUnit),
      ∃! i, ∃ j, (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞
        catMapUnit)^[j] (x i) = y) :
    mapRingHom (RingHom.id ℚ)
        (intTimePeriodHom
          (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ catMapUnit))
        (exists_period_rescale_intTimePeriodHom _)
        (orbitZeta ℚ (timePeriodHom _) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
              (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞
                catMapUnit)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp) (PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℚ)) := by
  have hA (n : ℕ) (hn : 0 < n) :
      (1 - ((catMapUnit : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ^ n).det ≠ 0 := by
    rw [coe_catMapUnit]
    exact (det_one_sub_catMap_pow_neg hn.ne').ne
  rw [mapRingHom_orbitZeta_constSmul_eq_ofPowerSeries_lefschetzZeta ℚ hA hxd hd hmin hrep,
    lefschetzZeta_generalLinearGroup_smul_eq_subst_exp_finsum_sign_det_id_sub_fixedPointDerivative,
    subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapUnit_smul]

end TauCeti.SmoothMappingTorus
