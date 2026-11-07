/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic
public import TauCeti.RingTheory.NovikovSeries.PowerSeries
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# The product of the orbit-torus weights is the orbit zeta function

Let `φ` be an area-preserving diffeomorphism of a closed surface and `Y_φ` its mapping torus. Each
primitive periodic orbit `γ` of `φ` gives an embedded square-zero torus `S¹ × γ` in the symplectic
four-manifold `S¹ × Y_φ`, and a class `[γ] ∈ H₁(Y_φ; ℤ)` of positive period `N [γ] = ∫_γ dt`. In
Taubes's weighted count, the torus enters with the local multiplicity series
`f_(σ, i) = TauCeti.torusWeightSeries σ i`, a power series in one variable `t` recording its
multiplicities. Substituting `t = e^[γ]`, by the series map
`TauCeti.NovikovSeries.ofPowerSeries [γ] _ : ℤ⟦X⟧ → Nov(ℤ, H, N)`, places the multiplicity-`m`
weight at the class `m [γ]` of the `m`-fold cover; the product of these substituted series over
all orbits converges in the Novikov completion.

This file identifies that product with the orbit zeta function of `φ`. The label `(σ, i)` of
the torus is read off from the linearized return map `P` of `γ`, a `2 × 2` matrix of determinant
one: `σ` is the sign of `det (1 - P)`, and `i = 1` or `0` according as `det (1 + P)` is negative
or not. When `P` is nondegenerate, `det (1 - P) ≠ 0`, the substituted local series is the factor
`(1 - σ' e^[γ]) ^ (-(ε σ'))` of the Euler product of
`TauCeti.NovikovSeries.orbitZeta_eq_eulerProduct`, where `ε = sgn det (1 - P)` and
`σ' = -1` if `det (1 + P) < 0` and `σ' = 1` otherwise
(`TauCeti.ofPowerSeries_torusWeightSeries_eq_zpow_unitsOneSubSingle`). Explicitly:

* a positive hyperbolic orbit has label `(-, 0)`, local series `1 - t` and factor `1 - e^[γ]`;
* a negative hyperbolic orbit has label `(+, 1)`, local series `1 + t` and factor `1 + e^[γ]`;
* an elliptic orbit has label `(+, 0)`, local series `1 / (1 - t)` and factor
  `(1 - e^[γ])⁻¹`.

When every iterate of `P` is nondegenerate, the signs `sgn det (1 - P ^ n)` form a geometric
sequence (`Matrix.sign_det_one_sub_pow_succ_of_det_eq_one`), so the product formula for orbit zeta
functions applies. Consequently, for a family of orbits with only finitely many classes below each
period cutoff, the product of the substituted torus series is the integral Euler product
(`TauCeti.hasProd_ofPowerSeries_torusWeightSeries`), and its image over any `ℚ`-algebra is the orbit
zeta function `exp (∑_γ ∑_{n ≥ 1} sgn det (1 - P_γ ^ n) e^(n [γ]) / n)`
(`TauCeti.orbitZeta_eq_mapRingHom_tprod_ofPowerSeries_torusWeightSeries`). This is the global,
homology-indexed form of the local identity
`TauCeti.X_mul_derivative_torusWeightSeries_of_det_eq_one`.

The tori of distinct orbits are disjoint, so every multiplicity assignment on them is a compatible
configuration, and the generating series `∑_A Gr(A) e^A` of their weighted configuration counts
(`TauCeti.configurationCountSeries`) is the product of their substituted local series
(`TauCeti.hasProd_ofPowerSeries_configurationCountSeries`). It is therefore the integral Euler
product (`TauCeti.configurationCountSeries_eq_eulerProduct`), and over any `ℚ`-algebra the orbit
zeta function (`TauCeti.orbitZeta_eq_mapRingHom_configurationCountSeries`).

That the labels of the actual orbit tori are given by the signs of `det (1 ∓ P)` is a separate
determinant comparison for their twisted normal operators; the statements here concern the labels
those signs prescribe.

## Main results

* `TauCeti.ofPowerSeries_torusWeightSeries_eq_zpow_unitsOneSubSingle`: the substituted local
  series of an orbit torus is its Euler factor.
* `TauCeti.hasProd_ofPowerSeries_torusWeightSeries`: the product of the substituted local series
  converges to the integral Euler product.
* `TauCeti.orbitZeta_eq_mapRingHom_tprod_ofPowerSeries_torusWeightSeries`: that product is the
  orbit zeta function.
* `TauCeti.configurationCountSeries_eq_eulerProduct`,
  `TauCeti.orbitZeta_eq_mapRingHom_configurationCountSeries`: the generating series of the weighted
  configuration counts of pairwise compatible orbit tori is the Euler product and the orbit zeta
  function.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861--888.
-/

public section

open Filter Matrix

namespace TauCeti

open NovikovSeries

section Factor

variable {H : Type*} [AddCommMonoid H] {N : H →+ ℝ} {g : H} (hg : 0 < N g)

/-- The series `f_(-, 0) = 1 - t` of a positive hyperbolic orbit torus, at `t = e^g`, is the
factor `1 - e^g`. -/
theorem ofPowerSeries_torusWeightSeries_false_zero :
    ofPowerSeries g hg (torusWeightSeries false 0) =
      ((unitsOneSubSingle hg (1 : ℤ) : nonnegSubring ℤ N) : NovikovSeries ℤ H N) := by
  simp [torusWeightSeries_false_zero]

/-- The series `f_(+, 1) = 1 + t` of a negative hyperbolic orbit torus, at `t = e^g`, is the
factor `1 + e^g`. -/
theorem ofPowerSeries_torusWeightSeries_true_one :
    ofPowerSeries g hg (torusWeightSeries true 1) =
      ((unitsOneSubSingle hg (-1 : ℤ) : nonnegSubring ℤ N) : NovikovSeries ℤ H N) := by
  simp [torusWeightSeries_true_one, NovikovSeries.single_neg, sub_eq_add_neg]

/-- The series `f_(+, 0) = 1 / (1 - t)` of an elliptic orbit torus, at `t = e^g`, is the
inverse `(1 - e^g)⁻¹`. -/
theorem ofPowerSeries_torusWeightSeries_true_zero :
    ofPowerSeries g hg (torusWeightSeries true 0) =
      ((↑(unitsOneSubSingle hg (1 : ℤ))⁻¹ : nonnegSubring ℤ N) : NovikovSeries ℤ H N) := by
  have h := congrArg (ofPowerSeries g hg) torusWeightSeries_true_zero_mul
  rw [_root_.map_mul, _root_.map_one, map_sub, _root_.map_one, ofPowerSeries_X,
    ← coe_unitsOneSubSingle hg (1 : ℤ)] at h
  exact Units.eq_inv_of_mul_eq_one_right
    (u := Units.map (nonnegSubring ℤ N).subtype.toMonoidHom (unitsOneSubSingle hg (1 : ℤ))) h

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {P : Matrix (Fin 2) (Fin 2) R}

/-- **Orbit-torus weights are Euler factors.** Let `P` be a nondegenerate `2 × 2` matrix of
determinant one, `det (1 - P) ≠ 0`. Read off the label `σ = (0 < det (1 - P))` and `i = 1` if
`det (1 + P) < 0`, `i = 0` otherwise. Then the local series `f_(σ, i)` at `t = e^g` is the Euler
factor `(1 - σ' e^g) ^ (-(ε σ'))`, where `ε = sgn det (1 - P)` and `σ' = -1` if `det (1 + P) < 0`,
`σ' = 1` otherwise. -/
theorem ofPowerSeries_torusWeightSeries_eq_zpow_unitsOneSubSingle (hdet : P.det = 1)
    (hP : (1 - P).det ≠ 0) :
    ofPowerSeries g hg
        (torusWeightSeries (decide (0 < (1 - P).det)) (if (1 + P).det < 0 then 1 else 0)) =
      ((↑(unitsOneSubSingle hg (if (1 + P).det < 0 then -1 else 1 : ℤ) ^
          (-(SignType.sign (1 - P).det * if (1 + P).det < 0 then -1 else 1 : ℤ))) :
        nonnegSubring ℤ N) : NovikovSeries ℤ H N) := by
  rw [det_one_sub_eq_two_sub_trace_of_det_eq_one hdet] at hP ⊢
  rw [det_one_add_eq_two_add_trace_of_det_eq_one hdet]
  rcases lt_or_ge 2 P.trace with htr | htr
  · rw [decide_eq_false (by linarith), ite_eq_right (by linarith), ite_eq_right (by linarith),
      sign_neg (by linarith), ofPowerSeries_torusWeightSeries_false_zero hg]
    norm_num
  rcases lt_or_ge P.trace (-2) with htr' | htr'
  · rw [decide_eq_true (by linarith), ite_eq_left (by linarith), ite_eq_left (by linarith),
      sign_pos (by linarith), ofPowerSeries_torusWeightSeries_true_one hg]
    norm_num
  have hpos : 0 < 2 - P.trace := lt_of_le_of_ne (by linarith) hP.symm
  rw [decide_eq_true hpos, ite_eq_right (by linarith), ite_eq_right (by linarith), sign_pos hpos,
    ofPowerSeries_torusWeightSeries_true_zero hg]
  norm_num

end Factor

section Product

variable {ι H : Type*} [AddCommMonoid H] {N : H →+ ℝ} {γ : ι → H} (hpos : ∀ i, 0 < N (γ i))
  (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) {R : Type*} [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R] {P : ι → Matrix (Fin 2) (Fin 2) R} (hdet : ∀ i, (P i).det = 1)

include hfin hdet in
/-- **The product of the orbit-torus weights is an integral Euler product.** For a family of
orbits of classes `γ i` of positive period, finitely many below each cutoff, whose return maps
`P i` are nondegenerate of determinant one, the product over the orbits of the
labelled local series at `t = e^(γ i)` converges to the Euler product
`∏ᵢ (1 - σ' i e^(γ i)) ^ (-(ε i σ' i))`, with `ε i = sgn det (1 - P i)` and `σ' i = -1` if
`det (1 + P i) < 0`, `σ' i = 1` otherwise. -/
theorem hasProd_ofPowerSeries_torusWeightSeries (hP : ∀ i, (1 - P i).det ≠ 0) :
    HasProd (fun i => ofPowerSeries (γ i) (hpos i)
        (torusWeightSeries (decide (0 < (1 - P i).det)) (if (1 + P i).det < 0 then 1 else 0)))
      (eulerProduct γ hpos (fun i => if (1 + P i).det < 0 then -1 else 1)
        (fun i => -(SignType.sign (1 - P i).det * if (1 + P i).det < 0 then -1 else 1))) :=
  (hasProd_eulerProduct hfin _ _).congr_fun fun i =>
    ofPowerSeries_torusWeightSeries_eq_zpow_unitsOneSubSingle (hpos i) (hdet i) (hP i)

include hfin hdet in
/-- **The product of the orbit-torus weights is the orbit zeta function.** For a family of
orbits of classes `γ i` of positive period, finitely many below each cutoff, whose return maps
`P i` have determinant one and nondegenerate nonzero powers, the product over the orbits of the
labelled local series at `t = e^(γ i)` is, over any `ℚ`-algebra `K`, the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - P i ^ n) e^(n • γ i) / n)`. -/
theorem orbitZeta_eq_mapRingHom_tprod_ofPowerSeries_torusWeightSeries
    (hP : ∀ i, ∀ k ≠ 0, (1 - P i ^ k).det ≠ 0) (K : Type*) [CommRing K] [Algebra ℚ K] :
    orbitZeta K N γ (fun i n => SignType.sign (1 - P i ^ n).det) =
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id H) ⟨1, one_pos, by simp⟩
        (∏' i, ofPowerSeries (γ i) (hpos i) (torusWeightSeries (decide (0 < (1 - P i).det))
          (if (1 + P i).det < 0 then 1 else 0))) := by
  let σ (i : ι) : ℤˣ := if (1 + P i).det < 0 then -1 else 1
  have hσ (i : ι) : ((σ i : ℤˣ) : ℤ) = if (1 + P i).det < 0 then -1 else 1 := by
    simp only [σ]
    split_ifs <;> rfl
  have hε (i : ι) (k : ℕ) : (SignType.sign (1 - P i ^ (k + 1)).det : ℤ) =
      SignType.sign (1 - P i ^ 1).det * ↑(σ i ^ k) := by
    rw [pow_one, Units.val_pow_eq_pow_val, hσ]
    exact sign_det_one_sub_pow_succ_of_det_eq_one (hdet i) (hP i) k
  rw [orbitZeta_eq_mapRingHom_eulerProduct hpos hfin _ σ hε,
    (hasProd_ofPowerSeries_torusWeightSeries hpos hfin hdet fun i => by
      simpa using hP i 1 one_ne_zero).tprod_eq]
  simp only [hσ, pow_one]

include hdet in
/-- **The configuration count of the orbit tori is an integral Euler product.** Let the orbit
tori, of classes `γ i` of positive period with finitely many below each cutoff, be pairwise
compatible, as the tori `S¹ × γ` of distinct orbits are disjoint, and let each carry the four-twist
weights of the label read off from its nondegenerate return map `P i` of determinant one. Then the
generating series `∑_A Gr(A) e^A` of the weighted configuration counts is the Euler product
`∏ᵢ (1 - σ' i e^(γ i)) ^ (-(ε i σ' i))` of `TauCeti.hasProd_ofPowerSeries_torusWeightSeries`. -/
theorem configurationCountSeries_eq_eulerProduct {r : ι → ι → Prop} (hr : Pairwise r)
    {w : ι → ℕ → ℤ} (hw : ∀ i, w i = torusWeight (decide (0 < (1 - P i).det))
      (if (1 + P i).det < 0 then 1 else 0))
    (hfin : ∀ C : ℝ, {i ∈ Set.univ | N (γ i) ≤ C}.Finite) (hP : ∀ i, (1 - P i).det ≠ 0) :
    configurationCountSeries r γ w (fun i _ => hpos i) hfin =
      eulerProduct γ hpos (fun i => if (1 + P i).det < 0 then -1 else 1)
        (fun i => -(SignType.sign (1 - P i).det * if (1 + P i).det < 0 then -1 else 1)) :=
  (hasProd_ofPowerSeries_configurationCountSeries (Set.pairwise_univ.2 hr) _ hfin
    (f := fun i => torusWeightSeries (decide (0 < (1 - P i).det))
      (if (1 + P i).det < 0 then 1 else 0))
    (fun i _ k => by rw [hw, torusWeight_def])
    fun i _ => constantCoeff_torusWeightSeries _ _).unique ((Equiv.Set.univ ι).hasProd_iff.2
      (hasProd_ofPowerSeries_torusWeightSeries hpos
        ((northcott_iff_tendsto _).1 ⟨fun C => by simpa using hfin C⟩) hdet hP))

include hdet in
/-- **The configuration count of the orbit tori is the orbit zeta function.** Let the orbit
tori, of classes `γ i` of positive period with finitely many below each cutoff, be pairwise
compatible, and let each carry the four-twist weights of the label read off from its return map
`P i` of determinant one with nondegenerate nonzero powers. Then over any `ℚ`-algebra `K` the
generating series `∑_A Gr(A) e^A` of the weighted configuration counts is the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - P i ^ n) e^(n • γ i) / n)`. -/
theorem orbitZeta_eq_mapRingHom_configurationCountSeries {r : ι → ι → Prop} (hr : Pairwise r)
    {w : ι → ℕ → ℤ} (hw : ∀ i, w i = torusWeight (decide (0 < (1 - P i).det))
      (if (1 + P i).det < 0 then 1 else 0))
    (hfin : ∀ C : ℝ, {i ∈ Set.univ | N (γ i) ≤ C}.Finite)
    (hP : ∀ i, ∀ k ≠ 0, (1 - P i ^ k).det ≠ 0) (K : Type*) [CommRing K] [Algebra ℚ K] :
    orbitZeta K N γ (fun i n => SignType.sign (1 - P i ^ n).det) =
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id H) ⟨1, one_pos, by simp⟩
        (configurationCountSeries r γ w (fun i _ => hpos i) hfin) := by
  have hP₁ (i : ι) : (1 - P i).det ≠ 0 := by simpa using hP i 1 one_ne_zero
  have hN : Tendsto (fun i => N (γ i)) cofinite atTop :=
    (northcott_iff_tendsto _).1 ⟨fun C => by simpa using hfin C⟩
  rw [orbitZeta_eq_mapRingHom_tprod_ofPowerSeries_torusWeightSeries hpos hN hdet hP K,
    (hasProd_ofPowerSeries_torusWeightSeries hpos hN hdet hP₁).tprod_eq,
    configurationCountSeries_eq_eulerProduct hpos hdet hr hw hfin hP₁]

end Product

end TauCeti
