/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Zeta
public import TauCeti.Geometry.Symplectic.Manifold.FixedPoint
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
  -- Read each return map `D i` as a matrix `P i` in a basis of `T_(x i) M = E`.
  let D (i : ι) : Module.End ℝ E := fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩
  let P (i : ι) := Algebra.endAlgEquivMatrix ℝ E hE (D i)
  have hPdet (i : ι) : (P i).det = LinearMap.det (D i) := Algebra.det_endAlgEquivMatrix ..
  have hPadd (i : ι) : (1 + P i).det = LinearMap.det (LinearMap.id + D i) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_add, _root_.map_one]
  have hPsub (i : ι) : (1 - P i).det = LinearMap.det (LinearMap.id - D i) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_sub, _root_.map_one]
  have hdet (i : ι) : (P i).det = 1 := (hPdet i).trans
    (SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one hσ φ.contMDiff hφσ (hxd i))
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
  -- Read each return map `D i` as a matrix `P i` in a basis of `T_(x i) M = E`.
  let D (i : ι) : Module.End ℝ E := fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩
  let P (i : ι) := Algebra.endAlgEquivMatrix ℝ E hE (D i)
  have hPdet (i : ι) : (P i).det = LinearMap.det (D i) := Algebra.det_endAlgEquivMatrix ..
  have hPadd (i : ι) : (1 + P i).det = LinearMap.det (LinearMap.id + D i) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_add, _root_.map_one]
  have hPsub (i : ι) : (1 - P i).det = LinearMap.det (LinearMap.id - D i) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_sub, _root_.map_one]
  have hPpow (i : ι) (n : ℕ) : (1 - P i ^ n).det = LinearMap.det (LinearMap.id - D i ^ n) := by
    rw [← Module.End.one_eq_id, ← Algebra.det_endAlgEquivMatrix ℝ E hE, map_sub, _root_.map_one,
      map_pow]
  have hdiff (i : ι) (n : ℕ) : MDifferentiableAt I I (⇑φ)^[d i * n] (x i) :=
    (φ.contMDiff.iterate _).mdifferentiableAt (by simp)
  -- The return map of the `n`-fold cover is the `n`-th power of the return map.
  have hit (i : ι) (n : ℕ) :
      fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩ =
        fixedPointDerivative I (⇑φ)^[d i] ⟨x i, (hxd i).eq⟩ ^ n :=
    fixedPointDerivative_iterate_mul (hxd i) (by simpa using hdiff i 1) n
  have hdet (i : ι) : (P i).det = 1 := (hPdet i).trans
    (SmoothTwoForm.det_fixedPointDerivative_iterate_eq_one hσ φ.contMDiff hφσ (hxd i))
  have hP (i : ι) (k : ℕ) (hk : k ≠ 0) : (1 - P i ^ k).det ≠ 0 := by
    have h := (isNondegenerateFixedPt_iff_det_id_sub_ne_zero
      ⟨x i, ((hxd i).mul_const k).eq⟩ (hdiff i k)).1
      ((hφ (d i * k)).isNondegenerateFixedPt (Nat.mul_pos (hd i) (Nat.pos_of_ne_zero hk)) le_rfl
        ((hxd i).mul_const k))
    rw [hit] at h
    rw [hPpow]
    exact h
  have key := orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod hφ hx hxd hd hdet hP K
  simp only [hPadd, hPsub, hPpow] at key
  simp only [hit]
  -- As above, `key` and the goal differ only in how the tangent space is written.
  exact key

end TauCeti.SmoothMappingTorus
