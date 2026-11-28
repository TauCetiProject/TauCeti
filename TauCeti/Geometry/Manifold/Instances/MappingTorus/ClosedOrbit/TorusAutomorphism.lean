/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.CatMap
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit.Lefschetz

/-!
# The orbit zeta function of the mapping torus of a linear torus automorphism

Let `p > 0`, let `A ∈ GL(ι, ℤ)` act on the torus `Tⁿ = ι → AddCircle p`, let `φ` be a
diffeomorphism of `Tⁿ` with `φ(x) = A • x`, such as `Diffeomorph.constSmul _ _ A`
(`Diffeomorph.coe_constSmul`), and let `Y_φ` be its mapping torus. When no positive power of `A`
has eigenvalue `1`, that is `det (1 - Aⁿ) ≠ 0` for every `n ≥ 1`, each iterate `φⁿ` has finitely
many fixed points (`AddCircle.finite_ptsOfPeriod_generalLinearGroup_smul_iff`), so the periodic
orbits of `φ` define the orbit zeta function of the suspension flow of `Y_φ`
(`TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum_single_sign_det_div`). This file identifies its
univariate specialization along the integral time period `N : H₁(Y_φ; ℤ) → ℤ` with the Lefschetz
zeta function of `φ`
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul`):

`N_* ζ_orb = exp (∑_{n ≥ 1} L(φⁿ) tⁿ / n) = exp (∑_{n ≥ 1} det (1 - Aⁿ) tⁿ / n)`,

evaluated at `t = e^1`. The orbit zeta function and the Lefschetz zeta function agree exactly when
the Lefschetz fixed-point formula holds for every iterate
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff`), and for
`φ(x) = A • x` both sides of that formula are `det (1 - Aⁿ)` (`AddCircle.`
`finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber`).

On the two-torus with `det A = 1`, an area-preserving linear map, the Lefschetz zeta function is
the homology determinant formula `det (1 - t A) / (1 - t)²`, so this is also the specialized orbit
zeta function (`TauCeti.SmoothMappingTorus.`
`mapRingHom_orbitZeta_eq_ofPowerSeries_charpolyRev_mul_of_coe_eq_smul`). For Arnold's cat map
`A = !![2, 1; 1, 1]`, every iterate of which is nondegenerate, it is
`(1 - 3 t + t²) / (1 - t)² = 1 - t - 2 t² - 3 t³ - ⋯`, with vacuum coefficient `1`
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_of_coe_eq_catMapUnit_smul`).

The statements are about any choice of points `x i`, one on each periodic orbit of `φ`, of least
periods `d i`; such a choice exists
(`Function.exists_forall_mem_periodicPts_existsUnique_iterate_eq`).

## Main results

* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul`:
  the univariate orbit zeta function of the mapping torus of `x ↦ A • x` is its Lefschetz zeta
  function.
* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_subst_exp_of_coe_eq_smul`: it
  is `exp (∑_{n ≥ 1} det (1 - Aⁿ) tⁿ / n)`.
* `TauCeti.SmoothMappingTorus.`
  `mapRingHom_orbitZeta_eq_ofPowerSeries_charpolyRev_mul_of_coe_eq_smul`: on the two-torus with
  `det A = 1` it is `det (1 - t A) / (1 - t)²`.
* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_of_coe_eq_catMapUnit_smul`: for
  the cat map it is `1 - t - 2 t² - 3 t³ - ⋯`.

## References

* S. Smale, *Differentiable dynamical systems*, Bull. Amer. Math. Soc. 73 (1967), 747–817.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158, Lemma 3.1.
* A. Katok and B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 1.8.
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff PowerSeries

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

variable {p : ℝ} [Fact (0 < p)] {ι : Type} [Fintype ι] [DecidableEq ι] {A : GL ι ℤ}
  {φ : (ι → AddCircle p) ≃ₘ⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ),
    ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)⟯ (ι → AddCircle p)}
  {κ : Type*} {x : κ → ι → AddCircle p} {d : κ → ℕ}

/-- A diffeomorphism `φ(x) = A • x` of the torus is, as a continuous map, the map induced by the
integer matrix `A`. -/
private theorem continuousMap_eq_smulVecHom (hφ : ⇑φ = fun y ↦ A • y) :
    (⟨φ, φ.continuous⟩ : C(ι → AddCircle p, ι → AddCircle p)) =
      (A : Matrix ι ι ℤ).smulVecHom (AddCircle p) :=
  ContinuousMap.ext fun y ↦ (congrFun hφ y).trans
    (AddCircle.generalLinearGroup_smul_eq_smulVecHom p A y)

variable (hφ : ⇑φ = fun y ↦ A • y) (hA : ∀ n, 0 < n → (1 - (A : Matrix ι ι ℤ) ^ n).det ≠ 0)
  (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)
  (hmin : ∀ i, minimalPeriod φ (x i) = d i)
  (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (k : Type) [Field k] [Algebra ℚ k]

open AddCircle in
include hφ hA hxd hd hmin hrep in
/-- **The orbit zeta function of the mapping torus of a linear torus automorphism is its
Lefschetz zeta function.** Let `A ∈ GL(ι, ℤ)` act on the torus `ι → AddCircle p` by the
diffeomorphism `φ(x) = A • x`, with `det (1 - Aⁿ) ≠ 0` for every `n ≥ 1`, let `x i` be points of
least periods `d i`, one on each periodic orbit of `φ`, and let `k` be a field of characteristic
zero. The pushforward of the orbit zeta function of the mapping torus of `φ` along the integral
time period is the image at `t = e^1` of the Lefschetz zeta function
`exp (∑_{n ≥ 1} L(φⁿ) tⁿ / n)` of `φ`. -/
theorem mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul :
    mapRingHom (RingHom.id k) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta k (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (⇑φ)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp)
        ((⟨φ, φ.continuous⟩ : C(ι → AddCircle p, ι → AddCircle p)).lefschetzZeta k) := by
  have := algebraRat.charZero k
  refine (mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff
    (fun n hn ↦ hφ ▸ (finite_ptsOfPeriod_generalLinearGroup_smul_iff p A n).2 (hA n hn)) hxd hd
    hmin hrep k).2 fun n _ ↦ ?_
  -- Both sides of the Lefschetz formula for `φⁿ` only see the map `⇑φ = fun y ↦ A • y`.
  suffices key : ∀ (f : (ι → AddCircle p) → ι → AddCircle p) (hf : Continuous f),
      f = (fun y ↦ A • y) →
      ((∑ᶠ y : {y : ι → AddCircle p // f^[n] y = y}, (SignType.sign (LinearMap.det
        (LinearMap.id - fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f^[n] y)) :
          ℤ) : ℤ) : k) =
        (⟨f^[n], hf.iterate n⟩ : C(ι → AddCircle p, ι → AddCircle p)).lefschetzNumber k from
    key φ φ.continuous hφ
  rintro f hf rfl
  exact
    finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber
      p k A n

include hφ hA hxd hd hmin hrep in
/-- **The orbit zeta function of the mapping torus of a linear torus automorphism.** Under the
hypotheses of
`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul`,
the pushforward of the orbit zeta function of the mapping torus of `φ(x) = A • x` along the integral
time period is the image at `t = e^1` of `exp (∑_{n ≥ 1} det (1 - Aⁿ) tⁿ / n)`. -/
theorem mapRingHom_orbitZeta_eq_ofPowerSeries_subst_exp_of_coe_eq_smul :
    mapRingHom (RingHom.id k) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta k (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (⇑φ)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp) ((PowerSeries.exp k).subst
        (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • ((1 - (A : Matrix ι ι ℤ) ^ n).det : k))) := by
  rw [mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul hφ hA hxd hd hmin hrep k,
    continuousMap_eq_smulVecHom hφ, Matrix.lefschetzZeta_smulVecHom _ k (Fact.out : 0 < p).ne']

/-- **The orbit zeta function of the mapping torus of an area-preserving linear map of the
two-torus.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul`
on the two-torus `Fin 2 → AddCircle p`, if moreover `det A = 1`, the pushforward of the orbit zeta
function of the mapping torus of `φ(x) = A • x` along the integral time period is the image at
`t = e^1` of the homology determinant formula `det (1 - t A) / (1 - t)²`. -/
theorem mapRingHom_orbitZeta_eq_ofPowerSeries_charpolyRev_mul_of_coe_eq_smul {A : GL (Fin 2) ℤ}
    {φ : (Fin 2 → AddCircle p) ≃ₘ⟮ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ),
      ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)⟯ (Fin 2 → AddCircle p)}
    (hφ : ⇑φ = fun y ↦ A • y) (hA : ∀ n, 0 < n → (1 - (A : Matrix (Fin 2) (Fin 2) ℤ) ^ n).det ≠ 0)
    {x : κ → Fin 2 → AddCircle p} (hxd : ∀ i, IsPeriodicPt φ (d i) (x i))
    (hd : ∀ i, 0 < d i) (hmin : ∀ i, minimalPeriod φ (x i) = d i)
    (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
    (hdet : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1) :
    mapRingHom (RingHom.id k) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta k (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑φ)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp)
        ((((A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom k)).charpolyRev : PowerSeries k) *
          PowerSeries.mk 1 ^ 2) := by
  rw [mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul hφ hA hxd hd hmin hrep k,
    continuousMap_eq_smulVecHom hφ,
    Matrix.lefschetzZeta_smulVecHom_fin_two_of_det_eq_one hdet k (Fact.out : 0 < p).ne']

/-- **The orbit zeta function of the mapping torus of Arnold's cat map.** Let `φ` be the cat map
`x ↦ P • x` of the torus `Fin 2 → AddCircle p`, `P = !![2, 1; 1, 1]`, and let `x i` be points of
least periods `d i`, one on each periodic orbit of `φ`. The pushforward of the orbit zeta function
of the mapping torus of `φ` along the integral time period is the image at `t = e^1` of
`(1 - 3 t + t²) / (1 - t)² = 1 - t - 2 t² - 3 t³ - ⋯`. -/
theorem mapRingHom_orbitZeta_eq_ofPowerSeries_of_coe_eq_catMapUnit_smul
    {φ : (Fin 2 → AddCircle p) ≃ₘ⟮ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ),
      ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)⟯ (Fin 2 → AddCircle p)}
    (hφ : ⇑φ = fun y ↦ catMapUnit • y) {x : κ → Fin 2 → AddCircle p}
    (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)
    (hmin : ∀ i, minimalPeriod φ (x i) = d i)
    (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y) :
    mapRingHom (RingHom.id ℚ) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta ℚ (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑φ)^[d i * n]
              ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp) (PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℚ)) := by
  have hA (n : ℕ) (hn : 0 < n) : (1 - (catMapUnit : Matrix (Fin 2) (Fin 2) ℤ) ^ n).det ≠ 0 := by
    rw [coe_catMapUnit]
    exact (det_one_sub_catMap_pow_neg hn.ne').ne
  rw [mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_of_coe_eq_smul hφ hA hxd hd hmin hrep ℚ,
    continuousMap_eq_smulVecHom hφ, coe_catMapUnit, lefschetzZeta_smulVecHom_catMap]

end TauCeti.SmoothMappingTorus
