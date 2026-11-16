/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Typical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral

/-!
# `p`-typical formal group laws and Cartier's `p`-typicalization

A commutative formal group law `F` over a commutative ring `R` is **`p`-typical** when its
tautological curve `γ₀(T) = T` is a `p`-typical curve: Cartier's Frobenius operator `f_q` kills
`γ₀` for every prime `q ≠ p`. Over a `ℚ`-algebra and for `p` prime, this says precisely that the
logarithm of `F` has no terms outside the degrees `pⁿ`. Hence, over a `ℚ`-algebra, the `p`-typical
laws are exactly Hazewinkel's laws `F_v`, and Hazewinkel's integral law is `p`-typical over every
commutative ring.

**Cartier's theorem.** When every prime `q ≠ p` is invertible in `R`, every commutative formal
group law `F` over `R` is strictly isomorphic to a `p`-typical one. Cartier's `p`-typical projector
`ε` sends the tautological curve to a curve `ψ = ε γ₀` with linear coefficient `1`, a strict
formal coordinate. Writing `F` in the coordinate `ψ⁻¹` gives the formal group law
`ψ⁻¹ • F` (`FormalGroup.pTypicalization`), and `ψ⁻¹` is a strict isomorphism from `F` to it. The
law `ψ⁻¹ • F` is `p`-typical because `ψ` carries its tautological curve to the `p`-typical
curve `ε γ₀` of `F`. A `p`-typical law is its own `p`-typicalization.

## Main definitions

* `FormalGroup.IsPTypical F p`: the formal group law `F` is `p`-typical.
* `FormalGroup.pTypicalCoordinate F hR`: the strict coordinate `ε γ₀`.
* `FormalGroup.pTypicalization F hR`: Cartier's `p`-typicalization of `F`.
* `FormalGroup.pTypicalizationIso F hR`: the strict isomorphism from `F` to its
  `p`-typicalization.

## Main results

* `FormalGroup.isPTypical_iff_coeff_log`: over a `ℚ`-algebra and for `p` prime, `F` is
  `p`-typical exactly when its logarithm is supported in the degrees `pⁿ`.
* `FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup`: over a `ℚ`-algebra, the
  `p`-typical laws are Hazewinkel's laws.
* `TauCeti.isPTypical_hazewinkelIntegralFormalGroup`: Hazewinkel's integral law is `p`-typical
  over every commutative ring.
* `FormalGroup.isPTypical_pTypicalization`, `FormalGroup.instIsStrictPTypicalizationIso`:
  **Cartier's theorem**, every commutative formal group law over a ring in which every prime
  `q ≠ p` is invertible is strictly isomorphic to a `p`-typical one.
* `FormalGroup.pTypicalization_eq_self_iff`: a law is its own `p`-typicalization exactly when it
  is `p`-typical.
* `FormalGroup.map_pTypicalization`: `p`-typicalization commutes with base change.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §15–16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws -/

section IsPTypical

/-- A commutative formal group law is **`p`-typical** when its tautological curve `γ₀(T) = T` is
`p`-typical, that is, Cartier's Frobenius operator `f_q` kills `γ₀` for every prime `q ≠ p`. -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve ∈ F.pTypicalCurves p

variable {F : FormalGroup R} [F.IsComm] {p : ℕ}

/-- `F` is `p`-typical exactly when its tautological curve is a `p`-typical curve. -/
theorem isPTypical_def : F.IsPTypical p ↔ F.tautologicalCurve ∈ F.pTypicalCurves p :=
  Iff.rfl

/-- `F` is `p`-typical exactly when `f_q γ₀ = 0` for every prime `q ≠ p`. -/
theorem isPTypical_iff : F.IsPTypical p ↔
    ∀ q (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 :=
  F.mem_pTypicalCurves p

/-- Being `p`-typical is a property of the formal group law, not of its commutativity proof. -/
theorem isPTypical_congr {G : FormalGroup R} [G.IsComm] (h : F = G) :
    F.IsPTypical p ↔ G.IsPTypical p := by
  subst h
  rfl

/-- Base change preserves `p`-typical formal group laws. -/
theorem IsPTypical.map (hF : F.IsPTypical p) (φ : R →+* S) : (F.map φ).IsPTypical p := by
  rw [IsPTypical, ← map_tautologicalCurve]
  exact map_mem_pTypicalCurves φ hF

/-- Along an injective coefficient map, a formal group law is `p`-typical exactly when its base
change is. -/
theorem isPTypical_map_iff {φ : R →+* S} (hφ : Function.Injective φ) :
    (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [IsPTypical, IsPTypical, ← map_tautologicalCurve, map_mem_pTypicalCurves_iff hφ]

end IsPTypical

/-- The target of an isomorphism `e : F ≅ G` is `p`-typical exactly when the inverse `e⁻¹(T)`,
viewed as a curve on `F`, is `p`-typical. -/
theorem _root_.TauCeti.FormalGroupIso.isPTypical_iff {F G : FormalGroup R} [F.IsComm] [G.IsComm]
    (e : TauCeti.FormalGroupIso F G) {p : ℕ} :
    G.IsPTypical p ↔ e.invHom.mapCurve G.tautologicalCurve ∈ F.pTypicalCurves p := by
  rw [IsPTypical, ← e.symm.curveEquiv_mem_pTypicalCurves_iff,
    TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupIso.symm_toHom]

/-! ### `p`-typical laws over `ℚ`-algebras -/

section RatAlgebra

variable [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]

/-- Over a `ℚ`-algebra, `f_q` kills the tautological curve exactly when the logarithm has no terms
in degrees divisible by `q`. -/
private theorem frobeniusCurve_tautologicalCurve_eq_zero_iff {q : ℕ} (hq : q ≠ 0) :
    F.frobeniusCurve q hq F.tautologicalCurve = 0 ↔ ∀ k, PowerSeries.coeff (q * k) F.log = 0 := by
  have hunit : IsUnit (q : R) := by
    simpa using (Ne.isUnit (Nat.cast_ne_zero.mpr hq : (q : ℚ) ≠ 0)).map (algebraMap ℚ R)
  rw [← F.logIso.curveEquiv.map_eq_zero_iff, Curve.ext_iff, PowerSeries.ext_iff]
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom, Curve.toPowerSeries_zero,
    map_zero, TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_subst_frobeniusCurve_log, toPowerSeries_tautologicalCurve, PowerSeries.X_subst,
    hunit.mul_right_eq_zero]

/-- **`p`-typical laws over a `ℚ`-algebra**: for `p` prime, a commutative formal group law over a
`ℚ`-algebra is `p`-typical exactly when its logarithm has no terms outside the degrees `pⁿ`. -/
theorem isPTypical_iff_coeff_log {p : ℕ} [hp : Fact p.Prime] :
    F.IsPTypical p ↔ ∀ k, (∀ n, p ^ n ≠ k) → PowerSeries.coeff k F.log = 0 := by
  simp only [isPTypical_iff, frobeniusCurve_tautologicalCurve_eq_zero_iff]
  refine ⟨fun h k hk ↦ ?_, fun h q hq hqp m ↦ h _ fun n hn ↦ hqp ?_⟩
  · rcases eq_or_ne k 0 with rfl | hk0
    · exact (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans F.constantCoeff_log
    obtain ⟨q, hq, hqk, hqp⟩ : ∃ q, q.Prime ∧ q ∣ k ∧ q ≠ p := by
      by_contra! hne
      exact hk _ (Nat.eq_prime_pow_of_unique_prime_dvd hk0 fun hd hdk ↦ hne _ hd hdk).symm
    obtain ⟨m, rfl⟩ := hqk
    exact h q hq hqp m
  · exact (Nat.prime_dvd_prime_iff_eq hq hp.out).mp
      (hq.dvd_of_dvd_pow (hn ▸ dvd_mul_right q m : q ∣ p ^ n))

/-- **Classification of `p`-typical laws over a `ℚ`-algebra**: for `p` prime, the `p`-typical
commutative formal group laws over a `ℚ`-algebra are exactly Hazewinkel's laws `F_v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup {p : ℕ} [hp : Fact p.Prime] :
    F.IsPTypical p ↔ ∃ v, F = TauCeti.hazewinkelFormalGroup p v := by
  refine ⟨fun h ↦ (TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.out.one_lt
    ((isPTypical_iff_coeff_log F).mp h)).exists, ?_⟩
  rintro ⟨v, rfl⟩
  exact (isPTypical_iff_coeff_log _).mpr fun k hk ↦ by
    rw [TauCeti.log_hazewinkelFormalGroup, TauCeti.coeff_hazewinkelLog_eq_zero v hk]

end RatAlgebra

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- Over a `ℚ`-algebra, Hazewinkel's formal group law is `p`-typical. -/
theorem isPTypical_hazewinkelFormalGroup {K : Type*} [CommRing K] [Algebra ℚ K]
    (v : ℕ+ → K) : (hazewinkelFormalGroup p v).IsPTypical p :=
  (FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup _).mpr ⟨v, rfl⟩

/-- **Hazewinkel's integral formal group law is `p`-typical** over every commutative ring,
including rings with torsion. -/
theorem isPTypical_hazewinkelIntegralFormalGroup (v : ℕ+ → R) :
    (hazewinkelIntegralFormalGroup p v).IsPTypical p := by
  have h : (universalHazewinkelIntegralFormalGroup p).IsPTypical p :=
    (FormalGroup.isPTypical_map_iff
      (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)).mp
      ((FormalGroup.isPTypical_congr (map_intCast_universalHazewinkelIntegralFormalGroup p)).mpr
        (isPTypical_hazewinkelFormalGroup p _))
  exact (FormalGroup.isPTypical_congr (hazewinkelIntegralFormalGroup_def p v)).mpr (h.map _)

end TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Cartier's `p`-typicalization -/

section Typicalization

open TauCeti

variable (F : FormalGroup R) [F.IsComm] {p : ℕ}
  (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- The strict formal coordinate `ψ = ε γ₀` obtained by applying Cartier's `p`-typical projector
to the tautological curve of `F`. -/
noncomputable def pTypicalCoordinate : FormalCoordinate R where
  toPowerSeries := (F.pTypicalProjectorCurve hR F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries := Curve.constantCoeff_toPowerSeries _
  isUnit_coeff_one := by simp

@[simp]
theorem toPowerSeries_pTypicalCoordinate :
    (F.pTypicalCoordinate hR).toPowerSeries =
      (F.pTypicalProjectorCurve hR F.tautologicalCurve).toPowerSeries :=
  (rfl)

/-- The coordinate `ε γ₀` is strict. -/
@[simp]
theorem linearCoeff_pTypicalCoordinate :
    FormalCoordinate.linearCoeff (F.pTypicalCoordinate hR) = 1 :=
  Units.ext (by simp [FormalCoordinate.val_linearCoeff])

/-- **Cartier's `p`-typicalization** of a commutative formal group law `F` over a ring in which
every prime `q ≠ p` is invertible: the law `ψ⁻¹ • F` obtained by writing `F` in the coordinate
`ψ⁻¹`, where `ψ = ε γ₀` is the `p`-typical projection of the tautological curve. -/
@[expose] noncomputable def pTypicalization : FormalGroup R :=
  (F.pTypicalCoordinate hR)⁻¹ • F

/-- The `p`-typicalization of `F` is `F` written in the coordinate `ψ⁻¹`, where `ψ = ε γ₀`. -/
theorem pTypicalization_def : F.pTypicalization hR = (F.pTypicalCoordinate hR)⁻¹ • F :=
  (rfl)

instance : (F.pTypicalization hR).IsComm :=
  instIsCommSMul _ _

/-- The strict isomorphism `ψ⁻¹` from `F` to its `p`-typicalization. -/
noncomputable def pTypicalizationIso : FormalGroupIso F (F.pTypicalization hR) :=
  smulIso _ F

/-- The `p`-typicalization isomorphism is the coordinate-change isomorphism for `ψ⁻¹`. -/
theorem pTypicalizationIso_def :
    F.pTypicalizationIso hR = smulIso (F.pTypicalCoordinate hR)⁻¹ F :=
  (rfl)

@[simp]
theorem pTypicalizationIso_toHom_toPowerSeries :
    (F.pTypicalizationIso hR).toHom.toPowerSeries = (F.pTypicalCoordinate hR)⁻¹.toPowerSeries :=
  smulIso_toHom_toPowerSeries _ F

/-- The inverse of the `p`-typicalization isomorphism is the `p`-typical curve `ε γ₀`. -/
@[simp]
theorem pTypicalizationIso_invHom_toPowerSeries :
    (F.pTypicalizationIso hR).invHom.toPowerSeries =
      (F.pTypicalProjectorCurve hR F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalizationIso_def, smulIso_invHom_toPowerSeries, inv_inv,
    toPowerSeries_pTypicalCoordinate]

/-- The isomorphism from `F` to its `p`-typicalization is strict. -/
instance instIsStrictPTypicalizationIso : (F.pTypicalizationIso hR).IsStrict :=
  (isStrict_smulIso_iff _ F).mpr (by simp)

/-- **Cartier's theorem**: the `p`-typicalization of `F` is `p`-typical. Together with
`FormalGroup.instIsStrictPTypicalizationIso`, every commutative formal group law over a ring in
which every prime `q ≠ p` is invertible is strictly isomorphic to a `p`-typical one. -/
theorem isPTypical_pTypicalization : (F.pTypicalization hR).IsPTypical p := by
  rw [(F.pTypicalizationIso hR).isPTypical_iff]
  convert F.pTypicalProjectorCurve_mem_pTypicalCurves hR F.tautologicalCurve using 1
  ext : 1
  simp

/-- A commutative formal group law is its own `p`-typicalization exactly when it is
`p`-typical. -/
theorem pTypicalization_eq_self_iff : F.pTypicalization hR = F ↔ F.IsPTypical p := by
  refine ⟨fun h ↦ (isPTypical_congr h).mp (F.isPTypical_pTypicalization hR), fun h ↦ ?_⟩
  have hψ : F.pTypicalCoordinate hR = 1 := FormalCoordinate.ext <| by
    rw [toPowerSeries_pTypicalCoordinate, F.pTypicalProjectorCurve_eq_self hR h,
      toPowerSeries_tautologicalCurve, FormalCoordinate.toPowerSeries_one]
  rw [pTypicalization_def, hψ, inv_one, one_smul]

/-- **`p`-typicalization commutes with base change.** -/
theorem map_pTypicalization (φ : R →+* S) :
    (F.pTypicalization hR).map φ =
      (F.map φ).pTypicalization (fun q hq hqp ↦ by simpa using (hR q hq hqp).map φ) := by
  rw [pTypicalization_def, pTypicalization_def, map_smul, map_inv]
  congr 2
  ext : 1
  rw [FormalCoordinate.toPowerSeries_map, toPowerSeries_pTypicalCoordinate,
    toPowerSeries_pTypicalCoordinate, ← Curve.toPowerSeries_map, map_pTypicalProjectorCurve,
    map_tautologicalCurve]

end Typicalization

end FormalGroup
