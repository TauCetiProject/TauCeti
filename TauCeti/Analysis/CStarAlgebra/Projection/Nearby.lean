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
import Mathlib.Topology.Connected.Clopen
import TauCeti.Algebra.Ring.Invertible
import TauCeti.Algebra.Star.Projection.Pair
import TauCeti.Algebra.Star.Projection.Unitization

/-!
# Perturbation and paths of projections in C⋆-algebras

Perturbation and homotopy theory for star projections in complex C⋆-algebras:

* `IsStarProjection.nearbyUnitary`, `.coe_nearbyUnitary`, `.nearbyUnitary_mul_mul_star`,
  `.norm_nearbyUnitary_sub_one_le`, `.joined_one_nearbyUnitary`: Kato's overlap-polar unitary for
  nearby projections (`‖p - q‖ < 1`), lying in the identity path component and conjugating `p` to
  `q`.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`,
  `.exists_unitization_unitary_conj_of_norm_sub_lt_one`,
  `.exists_path_isStarProjection_of_norm_sub_lt_one`: nearby projections (`‖p - q‖ < 1`) are
  unitarily conjugate in the identity path component and joined by a continuous path of projections.
* `Continuous.exists_joined_one_mul_mul_star_eq`, `Path.exists_unitary_conj_of_isStarProjection`,
  `Path.exists_unitization_unitary_conj_of_isStarProjection`: values of a continuous family (and
  endpoints of a norm-continuous path) of star projections are unitarily conjugate in the identity
  path component.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6
  (Propositions 4.6.5 and 4.6.6).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer-Verlag, Berlin, 1995, Section I.4.6
  (unitary equivalence of nearby projections via the polar factor of `q p + (1 - q)(1 - p)`).
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal Real unitInterval Ring

section NearbyProjections

private theorem isUnit_overlap {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    IsUnit (TauCeti.intertwiner p q) := by
  let z : A := TauCeti.intertwiner p q
  have hzzs : z * star z = 1 - (p - q) ^ 2 := hp.intertwiner_mul_star_intertwiner hq
  have hzsz : star z * z = 1 - (p - q) ^ 2 := hp.star_intertwiner_mul_intertwiner hq
  have hnormal : Commute z (star z) := hzzs.trans hzsz.symm
  have hd_sa : (p - q) ^ 2 = star (p - q) * (p - q) := by
    rw [pow_two, star_sub, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  have hd_norm : ‖(p - q) ^ 2‖ = ‖p - q‖ * ‖p - q‖ := by
    rw [hd_sa, CStarRing.norm_star_mul_self]
  have h1d : IsUnit (1 - (p - q) ^ 2) := isUnit_one_sub_of_norm_lt_one (by
    rw [hd_norm]; nlinarith [norm_nonneg (p - q)])
  exact (hnormal.isUnit_mul_iff.mp (hzzs ▸ h1d)).1

private theorem nearbyUnitary_add_star {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1)
    {u : unitary A}
    (hu_eq : (u : A) = (CFC.sqrt (1 - (p - q) * (p - q)))⁻¹ʳ * (q * p + (1 - q) * (1 - p))) :
    (u : A) + star (u : A) = (2 : ℝ) • CFC.sqrt (1 - (p - q) * (p - q)) := by
  let z : A := TauCeti.intertwiner p q
  let d : A := (p - q) ^ 2
  let s : A := CFC.sqrt (1 - d)
  have hu_eq' : (u : A) = s⁻¹ʳ * z := by
    simpa only [s, d, z, pow_two, TauCeti.intertwiner_def] using hu_eq
  have hzzs : z * star z = 1 - d := hp.intertwiner_mul_star_intertwiner hq
  have hzsz : star z * z = 1 - d := hp.star_intertwiner_mul_intertwiner hq
  have hnormal : Commute z (star z) := hzzs.trans hzsz.symm
  have hcomm_1d_sz : Commute (1 - d) (star z) := by
    rw [← hzzs]
    exact (hnormal.symm.mul_right (Commute.refl (star z))).symm
  have hs_unit : IsUnit s := by
    have h := (isUnit_overlap hp hq hpq).unit.isStrictlyPositive_sqrt_mul_star.isUnit
    rwa [(isUnit_overlap hp hq hpq).unit_spec, hzzs] at h
  have h1d_nonneg : 0 ≤ 1 - d := hzzs ▸ mul_star_self_nonneg z
  have hss : s * s = 1 - d := CFC.sqrt_mul_sqrt_self (1 - d) h1d_nonneg
  -- For projections `p, q`, `z + z⋆ = 2 (1 - (p - q)²) = 2 s²`.
  have hz_add_sz : z + star z = (2 : ℝ) • (s * s) := by
    rw [hss, hp.intertwiner_add_star_intertwiner hq, two_mul, two_smul]
  -- Since `s` commutes with `z⋆`, `u⋆ = s⁻¹ z⋆`, giving `u + u⋆ = s⁻¹ (z + z⋆) = 2 s`.
  have hcomm_s_sz : Commute s (star z) := hcomm_1d_sz.cfcₙ_nnreal NNReal.sqrt
  have hsu : star (u : A) = s⁻¹ʳ * star z := by
    rw [hu_eq', star_mul, ← Ring.inverse_star, (CFC.sqrt_nonneg (1 - d)).isSelfAdjoint.star_eq,
      hcomm_s_sz.ringInverse_left.eq]
  rw [show (CFC.sqrt (1 - (p - q) * (p - q))) = s by simp only [s, d, pow_two]]
  rw [hsu, hu_eq', ← mul_add, hz_add_sz, mul_smul_comm, ← mul_assoc,
    Ring.inverse_mul_cancel _ hs_unit, one_mul]

private theorem norm_nearbyUnitary_sub_one_le_aux {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1)
    {u : unitary A}
    (hu_eq : (u : A) = (CFC.sqrt (1 - (p - q) * (p - q)))⁻¹ʳ * (q * p + (1 - q) * (1 - p))) :
    ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  obtain _ | _ := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim ((u : A) - 1) 0]
  let z : A := TauCeti.intertwiner p q
  let d : A := (p - q) ^ 2
  let s : A := CFC.sqrt (1 - d)
  have h1d_nonneg : 0 ≤ 1 - d :=
    hp.intertwiner_mul_star_intertwiner hq ▸ mul_star_self_nonneg z
  -- Step 1: Express `(u - 1)⋆ (u - 1) = 2 (1 - s)` using `u + u⋆ = 2 s`.
  have hu_add_star : (u : A) + star (u : A) = (2 : ℝ) • s := by
    simpa only [s, d, pow_two] using nearbyUnitary_add_star hp hq hpq hu_eq
  have hdiff_sq : star ((u : A) - 1) * ((u : A) - 1) = (2 : ℝ) • (1 - s) := by
    calc star ((u : A) - 1) * ((u : A) - 1)
        = star (u : A) * (u : A) - ((u : A) + star (u : A)) + 1 := by
          rw [star_sub, star_one]; noncomm_ring
      _ = (2 : ℝ) • (1 - s) := by
          rw [Unitary.star_mul_self_of_mem u.property, hu_add_star, smul_sub, two_smul, two_smul]
          abel
  -- Step 2: Bound `0 ≤ 1 - s ≤ d` (since `1 - d ≤ s = √(1 - d) ≤ 1`), hence `‖1 - s‖ ≤ ‖p - q‖²`.
  have hd_sa : d = star (p - q) * (p - q) := by
    dsimp only [d]
    rw [pow_two, star_sub, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  have hd_norm : ‖d‖ = ‖p - q‖ * ‖p - q‖ := by rw [hd_sa, CStarRing.norm_star_mul_self]
  have h1d_le : 1 - d ≤ 1 := sub_le_self 1 (hd_sa ▸ star_mul_self_nonneg (p - q))
  have h1d_norm_le : ‖1 - d‖ ≤ 1 := by
    simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_le_of_nonneg h1d_le h1d_nonneg
  have h1s_norm : ‖1 - s‖ ≤ ‖d‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (sub_le_comm.mp (CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one h1d_nonneg h1d_norm_le))
      (sub_nonneg.mpr (CFC.sqrt_one (A := A) ▸ CFC.sqrt_le_sqrt (1 - d) 1 h1d_le))
  -- Step 3: Conclude `‖u - 1‖² = 2 ‖1 - s‖ ≤ 2 ‖p - q‖²`.
  refine le_of_sq_le_sq ?_ (by positivity)
  have hlhs : ‖(u : A) - 1‖ ^ 2 = 2 * ‖1 - s‖ := by
    rw [sq, ← CStarRing.norm_star_mul_self, hdiff_sq, norm_smul, Real.norm_ofNat]
  rw [hlhs, mul_pow, Real.sq_sqrt (by positivity), sq, ← hd_norm]
  nlinarith

/-- Kato's overlap-polar unitary `u = (√(1 - (p - q)²))⁻¹ (q p + (1 - q)(1 - p))` for nearby
star projections `p` and `q` (`‖p - q‖ < 1`). -/
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
  have hzzs : TauCeti.intertwiner p q * star (TauCeti.intertwiner p q) =
      1 - (p - q) * (p - q) := by
    rw [hp.intertwiner_mul_star_intertwiner hq, pow_two]
  refine ⟨CFC.sqrt (1 - (p - q) * (p - q)),
    CFC.sqrt_mul_sqrt_self _ (hzzs ▸ mul_star_self_nonneg _),
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (CFC.sqrt_nonneg _), ?_⟩
  rw [IsStarProjection.nearbyUnitary]
  dsimp only
  rw [Units.coe_polarUnitary, (isUnit_overlap hp hq hpq).unit_spec, hzzs, TauCeti.intertwiner_def]

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
  have hzp : TauCeti.intertwiner p q * p = q * TauCeti.intertwiner p q :=
    hp.isIdempotentElem.intertwiner_mul hq.isIdempotentElem
  have hcomm_1d_q : Commute (1 - (p - q) ^ 2) q :=
    (Commute.one_left q).sub_left
      (hp.isIdempotentElem.commute_sub_sq_right hq.isIdempotentElem).symm
  have hcomm_s_q : Commute (CFC.sqrt (1 - (p - q) ^ 2)) q :=
    hcomm_1d_q.cfcₙ_nnreal NNReal.sqrt
  have hup : ((hp.nearbyUnitary hq hpq : unitary A) : A) * p =
      q * ((hp.nearbyUnitary hq hpq : unitary A) : A) := by
    rw [hp.coe_nearbyUnitary hq hpq, ← pow_two, ← TauCeti.intertwiner_def, mul_assoc, hzp,
      ← mul_assoc, hcomm_s_q.ringInverse_left.eq, mul_assoc]
  rw [hup, mul_assoc, Unitary.mul_star_self_of_mem (hp.nearbyUnitary hq hpq).property, mul_one]

/-- Kato's overlap-polar unitary satisfies `‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.norm_nearbyUnitary_sub_one_le {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ‖((hp.nearbyUnitary hq hpq : unitary A) : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact norm_nearbyUnitary_sub_one_le_aux hp hq hpq (hp.coe_nearbyUnitary hq hpq)

/-- Kato's overlap-polar unitary lies in the identity path component of `unitary A`. -/
theorem IsStarProjection.joined_one_nearbyUnitary {A : Type*} [CStarAlgebra A] {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    Joined (1 : unitary A) (hp.nearbyUnitary hq hpq) := by
  -- Follows from Mathlib's `Unitary.joined` criterion (`‖u - 1‖ < 2`).
  refine Unitary.joined 1 (hp.nearbyUnitary hq hpq) ?_
  have hsqrt2 : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact ((hp.norm_nearbyUnitary_sub_one_le hq hpq).trans
    ((mul_le_mul_of_nonneg_left hpq.le (by positivity)).trans_eq (mul_one _))).trans_lt hsqrt2

/-- **Nearby projections in a unital C⋆-algebra are unitarily conjugate.** If `p` and `q` are star
projections with `‖p - q‖ < 1`, Kato's overlap-polar unitary `IsStarProjection.nearbyUnitary` lies
in the identity path component of `unitary A`, conjugates `p` to `q`, and satisfies
`‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
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
    by simp [δ.source], by simp [δ.target, hconj]⟩,
    fun t => hp.isStarProjection_unitization_conj_snd (δ t)⟩
  have hδ : Continuous (fun t : I => ((δ t : unitary A⁺¹) : A⁺¹)) :=
    continuous_subtypeVal.comp δ.continuous
  exact (Unitization.continuous_snd (𝕜 := ℂ) (A := A)).comp
    ((hδ.mul continuous_const).mul hδ.star)

end NearbyProjections

section ProjectionPath

/-! The statement below writes `Star.star`: in a declaration named `Continuous.foo`, plain `star`
resolves to `Continuous.star`. -/

/-- **Homotopic projections are unitarily equivalent.** For a continuous family `f` of star
projections of a unital C⋆-algebra over a preconnected space, any two values `f x` and `f y` are
conjugate by a unitary in the path component of `1`. For a path of projections this compares its
endpoints. -/
theorem Continuous.exists_joined_one_mul_mul_star_eq {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {A : Type*} [CStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y := by
  refine PreconnectedSpace.induction₂'
    (fun x y ↦ ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y)
    (fun x ↦ ?_) ⟨fun a b c ⟨u, hu, hab⟩ ⟨v, hv, hbc⟩ ↦ ⟨v * u, ?_, ?_⟩⟩ x y
  · filter_upwards [hf.continuousAt.eventually (Metric.ball_mem_nhds (f x) one_pos)] with y hy
    rw [dist_eq_norm] at hy
    obtain ⟨u₁, hu₁_conj, -, hu₁_join⟩ :=
      (hfp x).exists_unitary_conj_of_norm_sub_lt_one (hfp y) (by rwa [norm_sub_rev])
    obtain ⟨u₂, hu₂_conj, -, hu₂_join⟩ :=
      (hfp y).exists_unitary_conj_of_norm_sub_lt_one (hfp x) hy
    exact ⟨⟨u₁, hu₁_join, hu₁_conj⟩, ⟨u₂, hu₂_join, hu₂_conj⟩⟩
  · simpa using hv.mul hu
  · rw [Submonoid.coe_mul, star_mul, ← hbc, ← hab]
    simp only [mul_assoc]

/-- **Endpoints of a continuous path of projections are unitarily conjugate** in a unital
C⋆-algebra, by a unitary in the identity path component of `unitary A`. -/
theorem Path.exists_unitary_conj_of_isStarProjection {A : Type*} [CStarAlgebra A]
    {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧ Joined (1 : unitary A) u := by
  obtain ⟨u, hjoin, hconj⟩ := γ.continuous.exists_joined_one_mul_mul_star_eq hγ 0 1
  exact ⟨u, by simpa only [γ.source, γ.target] using hconj, hjoin⟩

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
