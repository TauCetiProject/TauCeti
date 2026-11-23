/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.Compact
import TauCeti.Algebra.Ring.Invertible
import TauCeti.Analysis.CStarAlgebra.Projection.Unitization

/-!
# Perturbation and paths of projections in C⋆-algebras

Perturbation and homotopy theory for star projections in complex C⋆-algebras:

* `IsStarProjection.nearbyUnitary`, `.coe_nearbyUnitary`, `.nearbyUnitary_mul_mul_star`,
  `.norm_nearbyUnitary_sub_one_le`, `.joined_one_nearbyUnitary`: Kato's overlap-polar unitary for
  nearby projections (`‖p - q‖ < 1`), built via `Units.polarUnitary` and connected to `1` via
  `Unitary.joined`.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`,
  `.exists_unitization_unitary_conj_of_norm_sub_lt_one`,
  `.exists_path_isStarProjection_of_norm_sub_lt_one`: nearby projections (`‖p - q‖ < 1`) are
  unitarily conjugate in the identity path component and joined by a continuous path of projections.
* `Path.exists_unitary_conj_of_isStarProjection`,
  `Path.exists_unitization_unitary_conj_of_isStarProjection`: endpoints of a norm-continuous path of
  star projections are unitarily conjugate in the identity path component.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6
  (Propositions 4.6.5 and 4.6.6).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer-Verlag, Berlin, 1995, Section I.4.6
  (unitary equivalence of nearby projections via the polar factor of `q p + (1 - q)(1 - p)`).
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal Real unitInterval Ring

section NearbyProjections

private theorem overlap_mul_star_aux {A : Type*} [Ring A] {a b : A} (ha : a * a = a)
    (hb : b * b = b) :
    (b * a + (1 - b) * (1 - a)) * (a * b + (1 - a) * (1 - b)) = 1 - (a - b) * (a - b) := by
  calc (b * a + (1 - b) * (1 - a)) * (a * b + (1 - a) * (1 - b))
      = b * (a * a) * b + b * (a - a * a) * (1 - b) + (1 - b) * (a - a * a) * b +
          (1 - b) * (1 - a - a + a * a) * (1 - b) := by noncomm_ring
    _ = b * a * b + (1 - b - b + b * b - a + b * a + a * b - b * a * b) := by
          rw [ha]; noncomm_ring
    _ = 1 - (a * a - a * b - b * a + b * b) := by rw [ha, hb]; noncomm_ring
    _ = 1 - (a - b) * (a - b) := by noncomm_ring

private theorem overlap_intertwine {A : Type*} [Ring A] {p q : A} (hp : p * p = p)
    (hq : q * q = q) :
    (q * p + (1 - q) * (1 - p)) * p = q * (q * p + (1 - q) * (1 - p)) := by
  calc (q * p + (1 - q) * (1 - p)) * p = q * p := by simp [add_mul, mul_assoc, hp, sub_mul]
    _ = q * (q * p + (1 - q) * (1 - p)) := by simp [mul_add, ← mul_assoc, hq, mul_sub]

private theorem overlap_mul_star_self {A : Type*} [Ring A] [StarRing A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (q * p + (1 - q) * (1 - p)) * star (q * p + (1 - q) * (1 - p)) = 1 - (p - q) * (p - q) := by
  simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
    hq.isSelfAdjoint.star_eq]
  exact overlap_mul_star_aux hp.isIdempotentElem.eq hq.isIdempotentElem.eq

private theorem overlap_star_mul_self {A : Type*} [Ring A] [StarRing A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (q * p + (1 - q) * (1 - p)) * (q * p + (1 - q) * (1 - p)) = 1 - (p - q) * (p - q) := by
  simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
    hq.isSelfAdjoint.star_eq]
  rw [overlap_mul_star_aux hq.isIdempotentElem.eq hp.isIdempotentElem.eq]
  congr 1; noncomm_ring

private theorem isUnit_overlap {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    IsUnit (q * p + (1 - q) * (1 - p)) := by
  let z : A := q * p + (1 - q) * (1 - p)
  have hzzs : z * star z = 1 - (p - q) * (p - q) := overlap_mul_star_self hp hq
  have hzsz : star z * z = 1 - (p - q) * (p - q) := overlap_star_mul_self hp hq
  have hnormal : Commute z (star z) := hzzs.trans hzsz.symm
  have hd_sa : (p - q) * (p - q) = star (p - q) * (p - q) := by
    rw [star_sub, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  have hd_norm : ‖(p - q) * (p - q)‖ = ‖p - q‖ * ‖p - q‖ := by
    rw [hd_sa, CStarRing.norm_star_mul_self]
  have h1d : IsUnit (1 - (p - q) * (p - q)) := isUnit_one_sub_of_norm_lt_one (by
    rw [hd_norm]; nlinarith [norm_nonneg (p - q)])
  exact (hnormal.isUnit_mul_iff.mp (hzzs ▸ h1d)).1

private theorem norm_nearbyUnitary_sub_one_le_aux {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1)
    {u : unitary A}
    (hu_eq : (u : A) = (CFC.sqrt (1 - (p - q) * (p - q)))⁻¹ʳ * (q * p + (1 - q) * (1 - p))) :
    ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  obtain _ | _ := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim ((u : A) - 1) 0]
  let z : A := q * p + (1 - q) * (1 - p)
  let d : A := (p - q) * (p - q)
  let s : A := CFC.sqrt (1 - d)
  have hzzs : z * star z = 1 - d := overlap_mul_star_self hp hq
  have hzsz : star z * z = 1 - d := overlap_star_mul_self hp hq
  have hnormal : Commute z (star z) := hzzs.trans hzsz.symm
  have hcomm_1d_sz : Commute (1 - d) (star z) := by
    rw [← hzzs]
    exact (hnormal.symm.mul_right (Commute.refl (star z))).symm
  have hs_unit : IsUnit s := by
    have h := (isUnit_overlap hp hq hpq).unit.isStrictlyPositive_sqrt_mul_star.isUnit
    rwa [(isUnit_overlap hp hq hpq).unit_spec, hzzs] at h
  have h1d_nonneg : 0 ≤ 1 - d := hzzs ▸ mul_star_self_nonneg z
  have hss : s * s = 1 - d := CFC.sqrt_mul_sqrt_self (1 - d) h1d_nonneg
  have hz_add_sz : z + star z = (2 : ℝ) • (s * s) := by
    rw [hss]
    simp only [z, d, star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, two_smul]
    noncomm_ring [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  have hu_add_star : (u : A) + star (u : A) = (2 : ℝ) • s := by
    have hcomm_s_sz : Commute s (star z) := hcomm_1d_sz.cfcₙ_nnreal NNReal.sqrt
    have hsu : star (u : A) = s⁻¹ʳ * star z := by
      rw [hu_eq, star_mul, ← Ring.inverse_star, (CFC.sqrt_nonneg (1 - d)).isSelfAdjoint.star_eq,
        hcomm_s_sz.ringInverse_left.eq]
    rw [hsu, hu_eq, ← mul_add, hz_add_sz, mul_smul_comm, ← mul_assoc,
      Ring.inverse_mul_cancel _ hs_unit, one_mul]
  have hdiff_sq : star ((u : A) - 1) * ((u : A) - 1) = (2 : ℝ) • (1 - s) := by
    calc star ((u : A) - 1) * ((u : A) - 1)
        = star (u : A) * (u : A) - ((u : A) + star (u : A)) + 1 := by
          rw [star_sub, star_one]; noncomm_ring
      _ = (2 : ℝ) • (1 - s) := by
          rw [Unitary.star_mul_self_of_mem u.property, hu_add_star, smul_sub, two_smul, two_smul]
          abel
  have hd_sa : d = star (p - q) * (p - q) := by
    rw [star_sub, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  have hd_norm : ‖d‖ = ‖p - q‖ * ‖p - q‖ := by rw [hd_sa, CStarRing.norm_star_mul_self]
  have h1d_le : 1 - d ≤ 1 := sub_le_self 1 (hd_sa ▸ star_mul_self_nonneg (p - q))
  have h1d_norm_le : ‖1 - d‖ ≤ 1 := by
    simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_le_of_nonneg h1d_le h1d_nonneg
  have h1s_norm : ‖1 - s‖ ≤ ‖d‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (sub_le_comm.mp (CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one h1d_nonneg h1d_norm_le))
      (sub_nonneg.mpr (CFC.sqrt_one (A := A) ▸ CFC.sqrt_le_sqrt (1 - d) 1 h1d_le))
  refine le_of_sq_le_sq ?_ (by positivity)
  have hlhs : ‖(u : A) - 1‖ ^ 2 = 2 * ‖1 - s‖ := by
    rw [sq, ← CStarRing.norm_star_mul_self, hdiff_sq, norm_smul, Real.norm_ofNat]
  rw [hlhs, mul_pow, Real.sq_sqrt (by positivity), sq, ← hd_norm]
  nlinarith

/-- Kato's overlap-polar unitary `u = (√(1 - (p - q)²))⁻¹ (q p + (1 - q)(1 - p))` for nearby
star projections `p` and `q` (`‖p - q‖ < 1`), formed by applying `Units.polarUnitary` to the
intertwining unit `z = q * p + (1 - q) * (1 - p)`. -/
noncomputable def IsStarProjection.nearbyUnitary {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) : unitary A :=
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  (isUnit_overlap hp hq hpq).unit.polarUnitary

private theorem coe_nearbyUnitary_spectral {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ s : A, s * s = 1 - (p - q) * (p - q) ∧ (∃ r : A, s = star r * r) ∧
      ((hp.nearbyUnitary hq hpq : unitary A) : A) = s⁻¹ʳ * (q * p + (1 - q) * (1 - p)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  refine ⟨CFC.sqrt (1 - (p - q) * (p - q)),
    CFC.sqrt_mul_sqrt_self _ (overlap_mul_star_self hp hq ▸ mul_star_self_nonneg _),
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (CFC.sqrt_nonneg _), ?_⟩
  rw [IsStarProjection.nearbyUnitary]
  dsimp only
  rw [Units.coe_polarUnitary, (isUnit_overlap hp hq hpq).unit_spec, overlap_mul_star_self hp hq]

/-- Explicit polar formula for Kato's unitary `IsStarProjection.nearbyUnitary`. -/
theorem IsStarProjection.coe_nearbyUnitary {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ((hp.nearbyUnitary hq hpq : unitary A) : A) =
      (CFC.sqrt (1 - (p - q) * (p - q)))⁻¹ʳ * (q * p + (1 - q) * (1 - p)) := by
  obtain ⟨s, hs_sq, ⟨r, hr⟩, hu⟩ := coe_nearbyUnitary_spectral hp hq hpq
  have hsqrt : CFC.sqrt (1 - (p - q) * (p - q)) = s :=
    CFC.sqrt_unique hs_sq (hr ▸ star_mul_self_nonneg r)
  rw [hu, hsqrt]

/-- Kato's overlap-polar unitary conjugates `p` to `q`. -/
theorem IsStarProjection.nearbyUnitary_mul_mul_star {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ((hp.nearbyUnitary hq hpq : unitary A) : A) * p *
        star ((hp.nearbyUnitary hq hpq : unitary A) : A) = q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let z : A := q * p + (1 - q) * (1 - p)
  have hzp : z * p = q * z := overlap_intertwine hp.isIdempotentElem.eq hq.isIdempotentElem.eq
  have hpzs : p * star z = star z * q := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using
      congrArg star hzp
  have hcomm_1d_q : Commute (1 - (p - q) * (p - q)) q := by
    rw [← overlap_mul_star_self hp hq, Commute, SemiconjBy, mul_assoc, ← hpzs, ← mul_assoc, hzp,
      mul_assoc]
  have hcomm_s_q : Commute (CFC.sqrt (1 - (p - q) * (p - q))) q :=
    hcomm_1d_q.cfcₙ_nnreal NNReal.sqrt
  have hup : ((hp.nearbyUnitary hq hpq : unitary A) : A) * p =
      q * ((hp.nearbyUnitary hq hpq : unitary A) : A) := by
    rw [hp.coe_nearbyUnitary hq hpq, mul_assoc, hzp, ← mul_assoc, hcomm_s_q.ringInverse_left.eq,
      mul_assoc]
  rw [hup, mul_assoc, Unitary.mul_star_self_of_mem (hp.nearbyUnitary hq hpq).property, mul_one]

/-- Kato's overlap-polar unitary satisfies `‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.norm_nearbyUnitary_sub_one_le {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ‖((hp.nearbyUnitary hq hpq : unitary A) : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact norm_nearbyUnitary_sub_one_le_aux hp hq hpq (hp.coe_nearbyUnitary hq hpq)

/-- Kato's overlap-polar unitary lies in the identity path component of `unitary A`, by
Mathlib's `Unitary.joined` criterion (`‖u - 1‖ < 2`). -/
theorem IsStarProjection.joined_one_nearbyUnitary {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    Joined (1 : unitary A) (hp.nearbyUnitary hq hpq) := by
  refine Unitary.joined 1 (hp.nearbyUnitary hq hpq) ?_
  have hsqrt2 : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact ((hp.norm_nearbyUnitary_sub_one_le hq hpq).trans
    ((mul_le_mul_of_nonneg_left hpq.le (by positivity)).trans_eq (mul_one _))).trans_lt hsqrt2

/-- **Nearby projections in a unital C⋆-algebra are unitarily conjugate.** If `p` and `q` are star
projections with `‖p - q‖ < 1`, Kato's overlap-polar unitary `IsStarProjection.nearbyUnitary`
(built via `Units.polarUnitary` and connected to `1` via `Unitary.joined`) conjugates `p` to `q`
with `‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one {A : Type*} [CStarAlgebra A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A) u :=
  ⟨hp.nearbyUnitary hq hpq, hp.nearbyUnitary_mul_mul_star hq hpq,
    hp.norm_nearbyUnitary_sub_one_le hq hpq, hp.joined_one_nearbyUnitary hq hpq⟩

/-- **Nearby projections in a non-unital C⋆-algebra are unitarily conjugate in the unitization.**
Specializes `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one` (and
`IsStarProjection.nearbyUnitary`) to the images `(p : A⁺¹)` and `(q : A⁺¹)` in `A⁺¹`: when
`‖p - q‖ < 1`, there is a unitary `u` in the identity path component of `unitary A⁺¹` such that
`u * p * star u = q` and `‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      ‖(u : A⁺¹) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A⁺¹) u := by
  have hpq' : ‖(p : A⁺¹) - (q : A⁺¹)‖ < 1 := by rwa [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hconj, hnorm, hjoin⟩ :=
    IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one hp.inr hq.inr hpq'
  exact ⟨u, hconj, by simpa only [← Unitization.inr_sub, Unitization.norm_inr] using hnorm, hjoin⟩

/-- Two star projections at distance strictly less than `1` in a (possibly non-unital) C⋆-algebra
are joined by a norm-continuous path of star projections in `A`. -/
theorem IsStarProjection.exists_path_isStarProjection_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) :
    ∃ γ : Path p q, ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨u, hconj, -, ⟨δ⟩⟩ := hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq hpq
  refine ⟨⟨⟨fun t => ((δ t : A⁺¹) * (p : A⁺¹) * star (δ t : A⁺¹)).snd, ?_⟩,
    by simp [δ.source], by simp [δ.target, hconj]⟩, fun t => (hp.unitization_conj_snd (δ t)).1⟩
  have hδ : Continuous (fun t : I => ((δ t : unitary A⁺¹) : A⁺¹)) :=
    continuous_subtypeVal.comp δ.continuous
  exact (Unitization.continuous_snd (𝕜 := ℂ) (A := A)).comp
    ((hδ.mul continuous_const).mul hδ.star)

end NearbyProjections

section ProjectionPath

/-- **Endpoints of a continuous path of projections are unitarily conjugate** in a unital
C⋆-algebra, by a unitary in the identity path component of `unitary A`. -/
theorem Path.exists_unitary_conj_of_isStarProjection {A : Type*} [CStarAlgebra A]
    {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧ Joined (1 : unitary A) u := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous γ.continuous)
      1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  let N : ℕ := n + 1
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.succ_pos n)
  let grid : Fin (N + 1) → I := fun k =>
    ⟨(k : ℝ) / N, by positivity,
      (div_le_one hNposR).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt))⟩
  have hgrid0 : grid ⟨0, Nat.succ_pos N⟩ = 0 := Subtype.ext (by simp [grid])
  have hgridN : grid ⟨N, Nat.lt_succ_self N⟩ = 1 :=
    Subtype.ext (by simp [grid])
  have hdist (k : ℕ) (hk : k + 1 ≤ N) :
      dist (grid ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩)
        (grid ⟨k + 1, Nat.lt_succ_of_le hk⟩) = (1 : ℝ) / N := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hsub : (grid ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩ : ℝ) -
        (grid ⟨k + 1, Nat.lt_succ_of_le hk⟩ : ℝ) = -((1 : ℝ) / N) := by
      simp only [grid, Nat.cast_add, Nat.cast_one]
      ring
    rw [hsub, abs_neg, abs_of_pos (one_div_pos.mpr hNposR)]
  have hstep : ∀ k : ℕ, (hk : k ≤ N) →
      ∃ u : unitary A, (u : A) * γ 0 * star (u : A) = γ (grid ⟨k, Nat.lt_succ_of_le hk⟩) ∧
        Joined (1 : unitary A) u := fun k => by
    induction k with
    | zero => exact fun _ => ⟨1, by rw [hgrid0]; simp, Joined.refl 1⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu_conj, hu_join⟩ := ih (Nat.le_of_succ_le hk)
      let t₁ : I := grid ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩
      let t₂ : I := grid ⟨k + 1, Nat.lt_succ_of_le hk⟩
      have hnorm : ‖γ t₁ - γ t₂‖ < 1 := by
        rw [← dist_eq_norm]
        refine hδ ?_
        rw [hdist k hk]
        simpa [N] using hn
      obtain ⟨v, hv_conj, -, hv_join⟩ :=
        IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one (hγ t₁) (hγ t₂) hnorm
      refine ⟨v * u, ?_, by simpa only [one_mul] using hv_join.mul hu_join⟩
      calc ((v * u : unitary A) : A) * γ 0 * star ((v * u : unitary A) : A)
          = (v : A) * ((u : A) * γ 0 * star (u : A)) * star (v : A) := by
            simp only [Submonoid.coe_mul, star_mul]; noncomm_ring
        _ = γ t₂ := by rw [hu_conj, hv_conj]
  obtain ⟨u, hu_conj, hu_join⟩ := hstep N le_rfl
  exact ⟨u, by simpa only [γ.source, γ.target, hgridN] using hu_conj, hu_join⟩

/-- **Endpoints of a continuous path of projections are unitarily conjugate in the unitization**
for any (possibly non-unital) C⋆-algebra, by a unitary in the identity path component of
`unitary A⁺¹`. -/
theorem Path.exists_unitization_unitary_conj_of_isStarProjection {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      Joined (1 : unitary A⁺¹) u :=
  (γ.map (Unitization.continuous_inr (𝕜 := ℂ) (A := A))).exists_unitary_conj_of_isStarProjection
    fun t => (hγ t).inr

end ProjectionPath
