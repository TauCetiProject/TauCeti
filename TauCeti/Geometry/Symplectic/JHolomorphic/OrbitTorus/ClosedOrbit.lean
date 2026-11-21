/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit.Zeta
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Zeta
public import TauCeti.Geometry.Symplectic.Manifold.FixedPoint
import TauCeti.Dynamics.PeriodicPts.PeriodicPair
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# The orbit-torus series of the closed orbits of a mapping torus

Let `φ` be a diffeomorphism of a compact manifold `M`, modelled on a finite-dimensional real space,
and let `Y_φ` be its mapping torus. A point `x` of period `d > 0` gives the closed orbit
`[t] ↦ [t, x]` of the suspension flow, traversed once when `d` is the least period of `x`, with
class `[γ_x] ∈ H₁(Y_φ; ℤ)` (`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass`) and time
period `N [γ_x] = d` (`TauCeti.SmoothMappingTorus.timePeriodHom_closedOrbitHomologyClass`). The
positivity of this period is what allows the local multiplicity series `f(t)` of the orbit torus
`S¹ × γ_x` to be substituted at `t = e^[γ_x]` in the Novikov completion `Nov(ℤ, H₁(Y_φ; ℤ), N)`
(`TauCeti.NovikovSeries.ofPowerSeries`).

If `φ` is nondegenerate up to every period, it has only finitely many points with a positive
period at most any bound. Hence for any family of distinct points `x i` of positive periods `d i`
the time periods `N [γ_(x i)] = d i` tend to infinity along the cofinite filter
(`TauCeti.SmoothMappingTorus.tendsto_timePeriodHom_closedOrbitHomologyClass`, in
`TauCeti.Geometry.Manifold.DeRham.MappingTorus`), which is the
finiteness hypothesis of the product formulas for orbit-torus series
(`TauCeti.hasProd_ofPowerSeries_torusWeightSeries`). For such a family, for instance one point of
least period on each periodic orbit, the product of the substituted orbit-torus series therefore
converges in `Nov(ℤ, H₁(Y_φ; ℤ), N)` to the integral Euler product, and over a `ℚ`-algebra it is
the orbit zeta function
(`TauCeti.SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod`).

The labels of the orbit tori are read off, as in
`TauCeti.ofPowerSeries_torusWeightSeries_eq_zpow_unitsOneSubSingle`, from `2 × 2` matrices `P i`
of determinant one. In the first two statements below these are arbitrary inputs. When `M` is a
surface and `φ` preserves a nondegenerate two-form `σ`, as an area-preserving map does, they can
be taken to be the linearized return maps of the orbits: the fixed-point derivative
`D i = d(φ^[d i])_(x i)` (`TauCeti.fixedPointDerivative`) is an endomorphism of the
two-dimensional tangent space `T_(x i) M` of determinant one
(`TauCeti.SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one`), and the return map of the
`n`-fold cover is `D i ^ n = d(φ^[d i * n])_(x i)`
(`TauCeti.fixedPointDerivative_iterate_mul`). With these labels the product of the orbit-torus
series is the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - d(φ^[d i * n])_(x i)) e^(n [γ_(x i)]) / n)`, whose signs are the
local Lefschetz indices of the periodic points `x i` of `φ^[d i * n]`
(`SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative`).
Identifying these labels with the determinant signs of the twisted normal operators of the orbit
tori is not done here.

## Main results

* `TauCeti.SmoothMappingTorus.hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass`:
  the product of the orbit-torus series of the closed orbits, labelled by matrices `P i`,
  converges to the integral Euler product in `Nov(ℤ, H₁(Y_φ; ℤ), N)`.
* `TauCeti.SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod`: that
  product is the orbit zeta function.
* `TauCeti.SmoothMappingTorus.hasProd_ofPowerSeries_torusWeightSeries_fixedPointDerivative`,
  `SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative`:
  the same statements for an area-preserving map of a surface, with the orbit tori labelled by the
  linearized return maps of the orbits.
* `SmoothMappingTorus.mapRingHom_tprod_fixedPointDerivative_eq_exp_tsum_single_sign_det_div`: when
  the `x i` are one point on each periodic orbit, the product of the orbit-torus series is
  `exp (∑_{n > 0} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])`, a sum over the
  fixed points of the iterates of `φ`.
* For a map nondegenerate only up to period `T` and finitely many periodic points, the product of
  their orbit-torus series agrees with the orbit zeta function at every class of period at most
  `T`:
`orbitZeta_closedOrbitHomologyClass_sub_mapRingHom_tprod_fixedPointDerivative_mem_periodFiltration`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861--888.
-/

public section

open Filter Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hφ : ∀ N, IsNondegenerateUpToPeriod I φ N) {ι : Type*} {x : ι → M} (hx : Injective x)
  {d : ι → ℕ} (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {P : ι → Matrix (Fin 2) (Fin 2) R} (hdet : ∀ i, (P i).det = 1)

include hφ hx hd hdet in
/-- **The orbit-torus series of the closed orbits converge to an integral Euler product.** Let `φ`
be a diffeomorphism of a compact manifold, nondegenerate up to every period, and let `x i` be
distinct points of positive periods `d i`. Let `P i` be arbitrary nondegenerate `2 × 2` matrices
of determinant one, used as labels; their relation to the return maps of the orbits is not part of
this statement. The product over `i` of the labelled local series of the orbit tori, substituted
at `t = e^[γ_(x i)]`, converges in `Nov(ℤ, H₁(Y_φ; ℤ), N)` to the Euler product
`∏ᵢ (1 - σ' i e^[γ_(x i)]) ^ (-(ε i σ' i))`, with `ε i = sgn det (1 - P i)` and `σ' i = -1` if
`det (1 + P i) < 0`, `σ' i = 1` otherwise. -/
theorem hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass
    (hP : ∀ i, (1 - P i).det ≠ 0) :
    HasProd (fun i ↦ ofPowerSeries (closedOrbitHomologyClass (hxd i))
        (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
        (torusWeightSeries (decide (0 < (1 - P i).det)) (if (1 + P i).det < 0 then 1 else 0)))
      (eulerProduct (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
        (fun i ↦ if (1 + P i).det < 0 then -1 else 1)
        (fun i ↦ -(SignType.sign (1 - P i).det * if (1 + P i).det < 0 then -1 else 1))) :=
  TauCeti.hasProd_ofPowerSeries_torusWeightSeries _
    (tendsto_timePeriodHom_closedOrbitHomologyClass hφ hx hxd hd) hdet hP

include hφ hx hd hdet in
/-- **The orbit-torus series of the closed orbits give the orbit zeta function.** Under the
hypotheses of
`TauCeti.SmoothMappingTorus.hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass`,
with every nonzero power of each of the arbitrary label matrices `P i` nondegenerate, the product
of the substituted orbit-torus series is, over any `ℚ`-algebra `K`, the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - P i ^ n) e^(n [γ_(x i)]) / n)` in `Nov(K, H₁(Y_φ; ℤ), N)`. -/
theorem orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod
    (hP : ∀ i, ∀ k ≠ 0, (1 - P i ^ k).det ≠ 0) (K : Type*) [CommRing K] [Algebra ℚ K] :
    orbitZeta K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (1 - P i ^ n).det) =
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id _) ⟨1, one_pos, by simp⟩
        (∏' i, ofPowerSeries (closedOrbitHomologyClass (hxd i))
          (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
          (torusWeightSeries (decide (0 < (1 - P i).det))
            (if (1 + P i).det < 0 then 1 else 0))) :=
  TauCeti.orbitZeta_eq_mapRingHom_tprod_ofPowerSeries_torusWeightSeries _
    (tendsto_timePeriodHom_closedOrbitHomologyClass hφ hx hxd hd) hdet hP K

/-! ### Labels from the linearized return maps

For a diffeomorphism `φ` of a surface preserving a nondegenerate two-form `σ`, the labels can be
read off from the linearized return maps of the orbits themselves: the return map of the orbit
through `x i` is the fixed-point derivative `D i = d(φ^[d i])_(x i)`, an endomorphism of the
two-dimensional tangent space `T_(x i) M` of determinant one, and that of the `n`-fold cover is
`D i ^ n = d(φ^[d i * n])_(x i)`. -/

variable {σ : SmoothTwoForm I M}

omit [T2Space M] [CompactSpace M] in
/-- The return map `D = d(φ^[k])_y` of a periodic point `y` of a surface map preserving a
nondegenerate two-form, read as a matrix `P` in a basis of `E`: `P` has determinant one, and the
determinants of `1 + P`, `1 - P` and `1 - P ^ n` are those of `1 + D`, `1 - D` and
`1 - D ^ n = 1 - d(φ^[k * n])_y`. -/
private theorem exists_matrix_fixedPointDerivative (hE : Module.finrank ℝ E = 2)
    (hσ : σ.IsNondegenerate) (hφσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) {k : ℕ} {y : M}
    (hy : IsPeriodicPt φ k y) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det = 1 ∧
      (1 + P).det = LinearMap.det (LinearMap.id + fixedPointDerivative I (⇑φ)^[k] ⟨y, hy.eq⟩) ∧
      (1 - P).det = LinearMap.det (LinearMap.id - fixedPointDerivative I (⇑φ)^[k] ⟨y, hy.eq⟩) ∧
      ∀ n, (1 - P ^ n).det = LinearMap.det (LinearMap.id -
        fixedPointDerivative I (⇑φ)^[k * n] ⟨y, (hy.mul_const n).eq⟩) := by
  -- Read the return map `D` as a matrix in a basis of `T_y M = E`. The determinant identities are
  -- proved for endomorphisms of `E` and close the goals, stated on `T_y M`, by `exact`: the two
  -- spaces are the same.
  let D : Module.End ℝ E := fixedPointDerivative I (⇑φ)^[k] ⟨y, hy.eq⟩
  let P := Algebra.endAlgEquivMatrix ℝ E hE D
  have hadd : (1 + P).det = LinearMap.det (LinearMap.id + D) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_add, _root_.map_one]
  have hsub : (1 - P).det = LinearMap.det (LinearMap.id - D) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_sub, _root_.map_one]
  have hpow (n : ℕ) : (1 - P ^ n).det = LinearMap.det (LinearMap.id - D ^ n) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_sub, _root_.map_one,
      map_pow]
  refine ⟨P, ?_, hadd, hsub, fun n ↦ ?_⟩
  · rw [Algebra.det_endAlgEquivMatrix]
    exact SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one hσ φ.contMDiff hφσ hy
  -- The return map of the `n`-fold cover is the `n`-th power of the return map.
  rw [fixedPointDerivative_iterate_mul hy ((φ.contMDiff.iterate k).mdifferentiableAt (by simp)) n]
  exact hpow n

include hφ hx hd in
/-- **The orbit-torus series labelled by the return maps converge to an integral Euler product.**
Let `φ` be a diffeomorphism of a compact surface preserving a nondegenerate two-form `σ`,
nondegenerate up to every period, and let `x i` be distinct points of positive periods `d i`, with
linearized return maps `D i = d(φ^[d i])_(x i)`. The product over `i` of the local series of the
orbit tori labelled by `D i`, substituted at `t = e^[γ_(x i)]`, converges in
`Nov(ℤ, H₁(Y_φ; ℤ), N)` to the Euler product `∏ᵢ (1 - σ' i e^[γ_(x i)]) ^ (-(ε i σ' i))`, with
`ε i = sgn det (1 - D i)` and `σ' i = -1` if `det (1 + D i) < 0`, `σ' i = 1` otherwise. -/
theorem hasProd_ofPowerSeries_torusWeightSeries_fixedPointDerivative
    (hE : Module.finrank ℝ E = 2) (hσ : σ.IsNondegenerate)
    (hφσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) :
    HasProd (fun i ↦ ofPowerSeries (closedOrbitHomologyClass (hxd i))
        (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
        (torusWeightSeries
          (decide (0 < LinearMap.det
            (LinearMap.id - fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩)))
          (if LinearMap.det
              (LinearMap.id + fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩) < 0
            then 1 else 0)))
      (eulerProduct (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
        (fun i ↦ if LinearMap.det
            (LinearMap.id + fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩) < 0
          then -1 else 1)
        (fun i ↦ -(SignType.sign (LinearMap.det
            (LinearMap.id - fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩)) *
          if LinearMap.det
              (LinearMap.id + fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩) < 0
            then -1 else 1))) := by
  choose P hdet hPadd hPsub _ using
    fun i ↦ exists_matrix_fixedPointDerivative hE hσ hφσ (hxd i)
  have hP (i : ι) : (1 - P i).det ≠ 0 := by
    rw [hPsub i]
    exact (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x i, (hxd i).eq⟩
      ((φ.contMDiff.iterate (d i)).mdifferentiableAt (by simp))).1
      ((hφ (d i)).isNondegenerateFixedPt (hd i) le_rfl (hxd i))
  have key := hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass hφ hx hxd hd hdet hP
  simp only [hPadd, hPsub] at key
  -- `key` is stated on `E`, the goal on the tangent space at the subtype point `⟨x i, _⟩`; the
  -- two are the same space.
  exact key

include hφ hx hd in
/-- **The orbit-torus series labelled by the return maps give the orbit zeta function.** Under the
hypotheses of
`TauCeti.SmoothMappingTorus.hasProd_ofPowerSeries_torusWeightSeries_fixedPointDerivative`, the
product of the orbit-torus series labelled by the linearized return maps `D i = d(φ^[d i])_(x i)`
is, over any `ℚ`-algebra `K`, the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - d(φ^[d i * n])_(x i)) e^(n [γ_(x i)]) / n)` in
`Nov(K, H₁(Y_φ; ℤ), N)`. The sign `sgn det (1 - d(φ^[d i * n])_(x i))` is the local Lefschetz
index of `x i` as a fixed point of `φ^[d i * n]`. -/
theorem orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative
    (hE : Module.finrank ℝ E = 2) (hσ : σ.IsNondegenerate)
    (hφσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) (K : Type*) [CommRing K] [Algebra ℚ K] :
    orbitZeta K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩))) =
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id _) ⟨1, one_pos, by simp⟩
        (∏' i, ofPowerSeries (closedOrbitHomologyClass (hxd i))
          (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
          (torusWeightSeries
            (decide (0 < LinearMap.det
              (LinearMap.id - fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩)))
            (if LinearMap.det
                (LinearMap.id + fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩) < 0
              then 1 else 0))) := by
  choose P hdet hPadd hPsub hPpow using
    fun i ↦ exists_matrix_fixedPointDerivative hE hσ hφσ (hxd i)
  have hP (i : ι) (k : ℕ) (hk : k ≠ 0) : (1 - P i ^ k).det ≠ 0 := by
    rw [hPpow]
    exact (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x i, ((hxd i).mul_const k).eq⟩
      ((φ.contMDiff.iterate _).mdifferentiableAt (by simp))).1
      ((hφ (d i * k)).isNondegenerateFixedPt (Nat.mul_pos (hd i) (Nat.pos_of_ne_zero hk)) le_rfl
        ((hxd i).mul_const k))
  have key := orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod hφ hx hxd hd hdet hP K
  simp only [hPadd, hPsub, hPpow] at key
  -- As above, `key` and the goal differ only in how the tangent space is written.
  exact key

include hφ hd in
/-- **The orbit-torus series labelled by the return maps as a sum over fixed points.** Let `φ` be
a diffeomorphism of a compact surface preserving a nondegenerate two-form `σ`, nondegenerate up to
every period, and let `x i` be points of least periods `d i > 0` such that every periodic point of
`φ` lies on the orbit of exactly one `x i`. Then over any `ℚ`-algebra `K` the product of the
orbit-torus series labelled by the return maps `D i = d(φ^[d i])_(x i)`, substituted at
`t = e^[γ_(x i)]`, is
`exp (∑_{n > 0} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])` in
`Nov(K, H₁(Y_φ; ℤ), N)`: the exponential of the signed fixed points of the iterates of `φ`,
weighted by one over the period. -/
theorem mapRingHom_tprod_fixedPointDerivative_eq_exp_tsum_single_sign_det_div
    (hmin : ∀ i, minimalPeriod φ (x i) = d i)
    (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y) (hE : Module.finrank ℝ E = 2)
    (hσ : σ.IsNondegenerate) (hφσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) (K : Type*)
    [CommRing K] [Algebra ℚ K] :
    mapRingHom (Int.castRingHom K) (AddMonoidHom.id _) ⟨1, one_pos, by simp⟩
        (∏' i, ofPowerSeries (closedOrbitHomologyClass (hxd i))
          (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
          (torusWeightSeries
            (decide (0 < LinearMap.det
              (LinearMap.id - fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩)))
            (if LinearMap.det
                (LinearMap.id + fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩) < 0
              then 1 else 0))) =
      NormedSpace.exp (∑' q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2},
        (single (closedOrbitHomologyClass q.property.2) (algebraMap ℚ K
          ((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[q.val.1] ⟨q.val.2, q.property.2.eq⟩)) : ℤ) / q.val.1)) :
          NovikovSeries K _ (timePeriodHom φ))) := by
  have hx : Injective x :=
    injective_of_existsUnique_iterate (fun i ↦ mk_mem_periodicPts (hd i) (hxd i)) hrep
  rw [← orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative hφ hx hxd hd
    hE hσ hφσ K, orbitZeta_eq_exp_tsum_single_sign_det_div hφ hxd hd hmin hrep K]

include hd in
/-- **Below a period cutoff, the orbit-torus series labelled by the return maps give the orbit
zeta function.** Let `φ` be a diffeomorphism of a compact surface preserving a nondegenerate
two-form `σ`, nondegenerate only up to period `T`, and let `x i`, for `i` in a finite type, be
points of positive periods `d i`, with linearized return maps `D i = d(φ^[d i])_(x i)`. Then over
any `ℚ`-algebra `K` the product of the orbit-torus series labelled by `D i` agrees, below the period
`T + 1`, with the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - d(φ^[d i * n])_(x i)) e^(n [γ_(x i)]) / n)` in
`Nov(K, H₁(Y_φ; ℤ), N)`: their coefficients at every class of period at most `T` coincide.
Periodic points of period greater than `T` may be degenerate. -/
theorem
  orbitZeta_closedOrbitHomologyClass_sub_mapRingHom_tprod_fixedPointDerivative_mem_periodFiltration
    [Finite ι] {T : ℕ} (hφT : IsNondegenerateUpToPeriod I φ T) (hE : Module.finrank ℝ E = 2)
    (hσ : σ.IsNondegenerate) (hφσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) (K : Type*)
    [CommRing K] [Algebra ℚ K] :
    orbitZeta K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩))) -
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id _) ⟨1, one_pos, by simp⟩
        (∏' i, ofPowerSeries (closedOrbitHomologyClass (hxd i))
          (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
          (torusWeightSeries
            (decide (0 < LinearMap.det
              (LinearMap.id - fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩)))
            (if LinearMap.det
                (LinearMap.id + fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩) < 0
              then 1 else 0))) ∈ periodFiltration K (timePeriodHom φ) ((T : ℝ) + 1) := by
  choose P hdet hPadd hPsub hPpow using
    fun i ↦ exists_matrix_fixedPointDerivative hE hσ hφσ (hxd i)
  -- An iterate of period below `T + 1` has period at most `T`, so it is nondegenerate.
  have hP (i : ι) (n : ℕ) (hn : n ≠ 0)
      (hnT : n * timePeriodHom φ (closedOrbitHomologyClass (hxd i)) < (T : ℝ) + 1) :
      (1 - P i ^ n).det ≠ 0 := by
    rw [timePeriodHom_closedOrbitHomologyClass] at hnT
    have hle : d i * n ≤ T := by
      have : ((d i * n : ℕ) : ℝ) < T + 1 := by push_cast; linarith
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
    rw [hPpow]
    exact (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x i, ((hxd i).mul_const n).eq⟩
      ((φ.contMDiff.iterate _).mdifferentiableAt (by simp))).1
      (hφT.isNondegenerateFixedPt (Nat.mul_pos (hd i) (Nat.pos_of_ne_zero hn)) hle
        ((hxd i).mul_const n))
  have hfin : Tendsto (fun i ↦ timePeriodHom φ (closedOrbitHomologyClass (hxd i))) cofinite
      atTop := by
    rw [cofinite_eq_bot]
    exact tendsto_bot
  have key := orbitZeta_sub_mapRingHom_tprod_ofPowerSeries_torusWeightSeries_mem_periodFiltration
    (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i)) hfin hdet hP K
  simp only [hPadd, hPsub, hPpow] at key
  -- As above, `key` and the goal differ only in how the tangent space is written.
  exact key

end TauCeti.SmoothMappingTorus
