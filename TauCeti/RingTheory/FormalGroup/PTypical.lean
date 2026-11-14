/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.PTypical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
import Mathlib.Data.Nat.Log

/-!
# `p`-typical formal group laws and Cartier's `p`-typicalization

A one-dimensional formal group law `F` over a commutative ring `R` is **`p`-typical**
(`FormalGroup.IsPTypical`) if it is commutative and its tautological curve `γ(T) = T` is
`p`-typical in Cartier's sense, meaning that Cartier's Frobenius operator `f_q` annihilates
`F.tautologicalCurve` for every prime `q ≠ p`. This definition requires neither characteristic zero
nor torsion-freeness of `R`:

* Over any commutative ring `R`, `p`-typicality is preserved by base change and reflected along
  injective ring homomorphisms; the additive formal group law `𝔾ₐ` and Hazewinkel's universal and
  specialized integral formal group laws (`TauCeti.universalHazewinkelIntegralFormalGroup`,
  `TauCeti.hazewinkelIntegralFormalGroup`) are `p`-typical over every commutative ring.
* Over a `ℚ`-algebra and for `p` prime, `F` is `p`-typical if and only if `F` is commutative and
  its formal logarithm has nonzero coefficients only in degrees `p ^ m`, and hence if and only if
  `F` equals `TauCeti.hazewinkelFormalGroup p v` for a (unique) parameter family `v : ℕ+ → R`.

When every prime `q ≠ p` is invertible in `R` (for example when `R` is a `ℤ_{(p)}`-algebra),
applying Cartier's prime-to-`p` projector `Π_p` (`FormalGroup.pTypicalProjectorCurve`) to the
tautological curve `T` produces a `p`-typical curve `Π_p(T) = T + ⋯` on `F` with unit linear
coefficient `1`. Its compositional inverse defines **Cartier's canonical `p`-typical coordinate**
`FormalGroup.pTypicalCoordinate F p hunit`, a strict formal coordinate transporting `F` via the
strict isomorphism `FormalGroup.pTypicalizeIso` to its **canonical `p`-typicalization**
`FormalGroup.pTypicalize F p hunit`. The `p`-typicalization operation is idempotent, fixes
precisely the `p`-typical formal group laws, commutes with base change, and over a `ℚ`-algebra
retains the `X ^ (p ^ m)`-terms of `log_F(X)` while deleting all other terms.

## Main definitions

* `FormalGroup.IsPTypical`: `p`-typicality of a formal group law `F`.
* `FormalGroup.pTypicalCoordinate`: Cartier's canonical strict coordinate `(Π_p(T))⁻¹` when every
  prime `q ≠ p` is invertible in `R`.
* `FormalGroup.pTypicalize`: the strictly isomorphic `p`-typical formal group law
  `F.pTypicalCoordinate p hunit • F`.
* `FormalGroup.pTypicalizeIso`: the canonical strict isomorphism `F ≅ F.pTypicalize p hunit`.

## Main results

* `FormalGroup.isPTypical_iff_coeff_log_eq_zero` and
  `FormalGroup.IsPTypical.existsUnique_eq_hazewinkelFormalGroup`: rational logarithm and Hazewinkel
  classification of `p`-typical formal group laws for `p` prime.
* `FormalGroup.isPTypical_universalHazewinkelIntegralFormalGroup` and
  `FormalGroup.isPTypical_hazewinkelIntegralFormalGroup`: Hazewinkel's integral formal group laws
  are `p`-typical over every commutative ring.
* `FormalGroup.isPTypical_pTypicalize`, `FormalGroup.pTypicalize_eq_self_iff`, and
  `FormalGroup.pTypicalize_pTypicalize`: `F.pTypicalize p hunit` is `p`-typical, fixes `p`-typical
  laws, and is idempotent.
* `FormalGroup.eq_pTypicalCoordinate_iff`: uniqueness characterization of Cartier's canonical
  `p`-typical coordinate via `F.pTypicalProjectorCurve`.
* `FormalGroup.map_pTypicalCoordinate` and `FormalGroup.map_pTypicalize`: base-change naturality.
* `FormalGroup.coeff_log_pTypicalize_of_prime` and
  `FormalGroup.existsUnique_pTypicalize_eq_hazewinkelFormalGroup`: rational logarithm coefficients
  and Hazewinkel parameters of `F.pTypicalize p hunit`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter III,
  §16.3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.21–A2.1.23.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws -/

/-- A formal group law `F` over `R` is **`p`-typical** if it is commutative and its tautological
curve `γ(T) = T` is `p`-typical, i.e., Cartier's Frobenius operator `f_q` annihilates
`F.tautologicalCurve` for every prime `q ≠ p`. -/
structure IsPTypical (F : FormalGroup R) (p : ℕ) : Prop extends F.IsComm where
  /-- The tautological curve `T` on `F` is annihilated by `f_q` for all primes `q ≠ p`. -/
  isPTypical_tautologicalCurve : F.tautologicalCurve.IsPTypical p

theorem isPTypical_iff_tautologicalCurve (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔ F.tautologicalCurve.IsPTypical p :=
  ⟨fun h ↦ h.isPTypical_tautologicalCurve, fun h ↦ ⟨‹_›, h⟩⟩

theorem isPTypical_iff (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ q : ℕ, (hq : q.Prime) → q ≠ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 :=
  (F.isPTypical_iff_tautologicalCurve p).trans Curve.isPTypical_iff

/-- For a prime `p`, a commutative formal group law `F` over any commutative ring is `p`-typical if
and only if `f_n(T) = 0` for every nonzero `n` that is not a power of `p`. -/
theorem isPTypical_iff_forall_frobeniusCurve_eq_zero {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hp : p.Prime) :
    F.IsPTypical p ↔
      ∀ n : ℕ, (hn : n ≠ 0) → (∀ k : ℕ, p ^ k ≠ n) →
        F.frobeniusCurve n hn F.tautologicalCurve = 0 :=
  (F.isPTypical_iff_tautologicalCurve p).trans
    (Curve.isPTypical_iff_forall_frobeniusCurve_eq_zero hp)

/-- For a prime `p`, every `p`-power monomial curve `T ^ (p ^ k) = V_{p ^ k}(T)` on a `p`-typical
formal group law is `p`-typical. -/
theorem IsPTypical.verschiebungCurve_pow_tautologicalCurve {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hp : p.Prime) (hF : F.IsPTypical p) (k : ℕ) :
    (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) F.tautologicalCurve).IsPTypical p :=
  (Curve.isPTypical_verschiebungCurve_pow_iff hp k).mpr hF.isPTypical_tautologicalCurve

/-- Base change preserves `p`-typicality of formal group laws. -/
theorem IsPTypical.map {F : FormalGroup R} {p : ℕ} (hF : F.IsPTypical p)
    (φ : R →+* S) : (F.map φ).IsPTypical p := by
  let _ := hF.toIsComm
  rw [isPTypical_iff_tautologicalCurve, ← F.map_tautologicalCurve φ]
  exact Curve.IsPTypical.map hF.isPTypical_tautologicalCurve φ

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typicality of
formal group laws. -/
@[simp]
theorem isPTypical_map_iff {F : FormalGroup R} {p : ℕ} {φ : R →+* S}
    (hφ : Function.Injective φ) :
    (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map φ⟩
  let _ := h.toIsComm
  let _ : F.IsComm := isComm_of_map hφ
  rw [isPTypical_iff_tautologicalCurve]
  have ht := h.isPTypical_tautologicalCurve
  rwa [← F.map_tautologicalCurve φ, Curve.isPTypical_map_iff hφ] at ht

/-- The additive formal group law is `p`-typical over every commutative ring and for every `p`. -/
@[simp]
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ (R := R)).IsPTypical p := by
  rw [isPTypical_iff]
  intro q hq _
  ext k
  simp only [toPowerSeries_frobeniusCurve_𝔾ₐ, Curve.toPowerSeries_zero,
    toPowerSeries_tautologicalCurve, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
    Nat.add_zero, PowerSeries.coeff_X, map_zero, smul_eq_mul]
  have hne : q * k ≠ 1 := by
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · exact ne_of_gt (lt_of_lt_of_le hq.one_lt (Nat.le_mul_of_pos_right q (Nat.pos_of_ne_zero hk0)))
  rw [ite_eq_right hne, mul_zero]

/-- Transporting a commutative formal group law `F` along a formal coordinate `φ` produces a
`p`-typical formal group law `φ • F` if and only if the inverse coordinate series `φ⁻¹(T)` is a
`p`-typical curve on `F`. -/
theorem isPTypical_smul_iff (φ : TauCeti.FormalCoordinate R) (F : FormalGroup R) [F.IsComm]
    (p : ℕ) :
    (φ • F).IsPTypical p ↔
      (⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve).IsPTypical p := by
  let δ : F.Curve := ⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩
  have hδ : (smulIso φ F).curveEquiv δ = (φ • F).tautologicalCurve := by
    ext1
    rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
      smulIso_toHom_toPowerSeries, toPowerSeries_tautologicalCurve]
    simpa only [PowerSeries.X_subst] using φ.subst_subst_inv PowerSeries.HasSubst.X'
  rw [isPTypical_iff_tautologicalCurve, ← hδ, (smulIso φ F).curveEquiv_isPTypical_iff]

/-! ### Rational logarithm characterization and Hazewinkel's formal group laws -/

/-- Over a `ℚ`-algebra, for `p` prime, a commutative formal group law `F` is `p`-typical if and only
if its formal logarithm `F.log` vanishes outside the degrees `p ^ m`. -/
theorem isPTypical_iff_coeff_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ k : ℕ, (∀ m : ℕ, p ^ m ≠ k) → PowerSeries.coeff k F.log = 0 := by
  simpa only [isPTypical_iff_tautologicalCurve, toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst] using
    (Curve.isPTypical_iff_coeff_subst_log_eq_zero (F := F) (γ := F.tautologicalCurve) hp)

/-- Over a `ℚ`-algebra, for `p` prime, Hazewinkel's formal group law is `p`-typical. -/
@[simp]
theorem isPTypical_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime) (v : ℕ+ → R) :
    (TauCeti.hazewinkelFormalGroup p v).IsPTypical p :=
  (isPTypical_iff_coeff_log_eq_zero hp).mpr fun k hk ↦ by
    rw [TauCeti.log_hazewinkelFormalGroup, TauCeti.coeff_hazewinkelLog_eq_zero v hk]

/-- Over a `ℚ`-algebra, for `p` prime, every `p`-typical formal group law is Hazewinkel's formal
group law for a unique parameter family `v : ℕ+ → R`. -/
theorem IsPTypical.existsUnique_eq_hazewinkelFormalGroup [Algebra ℚ R] {F : FormalGroup R}
    {p : ℕ} (hp : p.Prime) (hF : F.IsPTypical p) :
    ∃! v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v := by
  let _ := hF.toIsComm
  exact TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt
    ((isPTypical_iff_coeff_log_eq_zero hp).mp hF)

/-- Over a `ℚ`-algebra, for `p` prime, a formal group law is `p`-typical if and only if it is of
the form `TauCeti.hazewinkelFormalGroup p v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup [Algebra ℚ R] {F : FormalGroup R}
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∃ v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  ⟨fun h ↦ (h.existsUnique_eq_hazewinkelFormalGroup hp).exists,
    fun ⟨v, hv⟩ ↦ hv ▸ isPTypical_hazewinkelFormalGroup hp v⟩

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem isPTypical_universalHazewinkelIntegralFormalGroup (p : ℕ) [hp : Fact p.Prime] :
    (TauCeti.universalHazewinkelIntegralFormalGroup p).IsPTypical p := by
  rw [← isPTypical_map_iff (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective),
    TauCeti.map_intCast_universalHazewinkelIntegralFormalGroup]
  exact isPTypical_hazewinkelFormalGroup hp.out _

/-- Hazewinkel's integral formal group law specialized at any family `v : ℕ+ → R` over an arbitrary
commutative ring `R` (including rings of characteristic `p` or with torsion) is `p`-typical. -/
@[simp]
theorem isPTypical_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime] (v : ℕ+ → R) :
    (TauCeti.hazewinkelIntegralFormalGroup p v).IsPTypical p := by
  rw [TauCeti.hazewinkelIntegralFormalGroup_def]
  exact (isPTypical_universalHazewinkelIntegralFormalGroup p).map _

/-! ### Cartier's canonical `p`-typicalization -/

section PTypicalize

variable (F : FormalGroup R) [F.IsComm] (p : ℕ)

/-- **Cartier's canonical `p`-typical coordinate** on a commutative formal group law `F` when every
prime `q ≠ p` is invertible in `R`: the compositional inverse of the projected tautological curve
`Π_p(T) = T + ⋯`, giving a strict formal coordinate `φ` that transports `F` to its canonical
`p`-typicalization `φ • F`. -/
noncomputable def pTypicalCoordinate (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate R :=
  (⟨(F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries,
    (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries, by
      rw [F.coeff_one_pTypicalProjectorCurve p hunit, toPowerSeries_tautologicalCurve,
        PowerSeries.coeff_one_X]
      exact isUnit_one⟩ : TauCeti.FormalCoordinate R)⁻¹

theorem toPowerSeries_inv_pTypicalCoordinate
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalCoordinate, inv_inv]

@[simp]
theorem linearCoeff_pTypicalCoordinate
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit) = 1 :=
  inv_eq_one.mp <| Units.ext <| by
    rw [← map_inv, TauCeti.FormalCoordinate.val_linearCoeff,
      toPowerSeries_inv_pTypicalCoordinate, F.coeff_one_pTypicalProjectorCurve p hunit,
      toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X, Units.val_one]

@[simp]
theorem coeff_one_pTypicalCoordinate
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff 1 (F.pTypicalCoordinate p hunit).toPowerSeries = 1 := by
  rw [← TauCeti.FormalCoordinate.val_linearCoeff, F.linearCoeff_pTypicalCoordinate p hunit,
    Units.val_one]

/-- Cartier's canonical `p`-typical coordinate is the identity coordinate `X` if and only if `F` is
already `p`-typical. -/
@[simp]
theorem pTypicalCoordinate_eq_one_iff
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = 1 ↔ F.IsPTypical p := by
  rw [← inv_eq_one, TauCeti.FormalCoordinate.ext_iff, toPowerSeries_inv_pTypicalCoordinate,
    TauCeti.FormalCoordinate.toPowerSeries_one, ← toPowerSeries_tautologicalCurve F,
    ← Curve.ext_iff, F.pTypicalProjectorCurve_eq_self_iff p hunit,
    isPTypical_iff_tautologicalCurve]

/-- **Cartier's canonical `p`-typicalization** of a commutative formal group law `F` over a ring in
which every prime `q ≠ p` is invertible, obtained by transporting `F` along
`FormalGroup.pTypicalCoordinate F p hunit`. -/
noncomputable def pTypicalize (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    FormalGroup R :=
  F.pTypicalCoordinate p hunit • F

theorem pTypicalize_def (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = F.pTypicalCoordinate p hunit • F :=
  (rfl)

instance (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).IsComm := by
  rw [pTypicalize_def]
  infer_instance

/-- The canonical strict isomorphism `F ≅ F.pTypicalize p hunit` induced by
`FormalGroup.pTypicalCoordinate F p hunit`. -/
noncomputable def pTypicalizeIso (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalGroupIso F (F.pTypicalize p hunit) :=
  smulIso (F.pTypicalCoordinate p hunit) F

@[simp]
theorem pTypicalizeIso_toHom_toPowerSeries
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).toHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit).toPowerSeries :=
  smulIso_toHom_toPowerSeries _ F

@[simp]
theorem pTypicalizeIso_invHom_toPowerSeries
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).invHom.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalizeIso, smulIso_invHom_toPowerSeries, toPowerSeries_inv_pTypicalCoordinate]

instance (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).IsStrict :=
  (isStrict_smulIso_iff (F.pTypicalCoordinate p hunit) F).mpr
    (F.linearCoeff_pTypicalCoordinate p hunit)

/-- Cartier's `p`-typicalization of any commutative formal group law is `p`-typical. -/
@[simp]
theorem isPTypical_pTypicalize (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).IsPTypical p := by
  rw [pTypicalize_def, isPTypical_smul_iff]
  have hcurve :
      (⟨(F.pTypicalCoordinate p hunit)⁻¹.toPowerSeries,
        (F.pTypicalCoordinate p hunit)⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve) =
        F.pTypicalProjectorCurve p hunit F.tautologicalCurve :=
    Curve.ext (F.toPowerSeries_inv_pTypicalCoordinate p hunit)
  rw [hcurve]
  exact F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve

/-- Every `p`-typical formal group law is fixed by Cartier's `p`-typicalization. -/
theorem pTypicalize_eq_self (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (hF : F.IsPTypical p) :
    F.pTypicalize p hunit = F := by
  rw [pTypicalize_def, (F.pTypicalCoordinate_eq_one_iff p hunit).mpr hF, one_smul]

/-- Cartier's `p`-typicalization fixes `F` if and only if `F` is `p`-typical. -/
@[simp]
theorem pTypicalize_eq_self_iff (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = F ↔ F.IsPTypical p :=
  ⟨fun h ↦ h ▸ F.isPTypical_pTypicalize p hunit, F.pTypicalize_eq_self p hunit⟩

@[simp]
theorem pTypicalCoordinate_pTypicalize (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).pTypicalCoordinate p hunit = 1 :=
  ((F.pTypicalize p hunit).pTypicalCoordinate_eq_one_iff p hunit).mpr
    (F.isPTypical_pTypicalize p hunit)

/-- Cartier's `p`-typicalization is idempotent. -/
@[simp]
theorem pTypicalize_pTypicalize (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).pTypicalize p hunit = F.pTypicalize p hunit :=
  (F.pTypicalize p hunit).pTypicalize_eq_self p hunit (F.isPTypical_pTypicalize p hunit)

/-- **Uniqueness characterization of Cartier's canonical `p`-typical coordinate**: a formal
coordinate `φ` equals `F.pTypicalCoordinate p hunit` if and only if `φ • F` is `p`-typical and the
difference between `F.tautologicalCurve` and `φ⁻¹(T)` lies in the kernel of Cartier's prime-to-`p`
projector. -/
theorem eq_pTypicalCoordinate_iff (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (φ : TauCeti.FormalCoordinate R) :
    φ = F.pTypicalCoordinate p hunit ↔
      (φ • F).IsPTypical p ∧
        F.pTypicalProjectorCurve p hunit
          (F.tautologicalCurve - ⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩) = 0 := by
  rw [isPTypical_smul_iff]
  set δ : F.Curve := ⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩
  have heq : φ = F.pTypicalCoordinate p hunit ↔
      δ = F.pTypicalProjectorCurve p hunit F.tautologicalCurve := by
    rw [← inv_inj, TauCeti.FormalCoordinate.ext_iff, toPowerSeries_inv_pTypicalCoordinate,
      Curve.ext_iff]
  rw [heq]
  constructor
  · intro h
    rw [h]
    refine ⟨F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve, ?_⟩
    rw [map_sub, pTypicalProjectorCurve_pTypicalProjectorCurve, sub_self]
  · rintro ⟨h₁, h₂⟩
    rw [map_sub, F.pTypicalProjectorCurve_eq_self p hunit h₁, sub_eq_zero] at h₂
    exact h₂.symm

/-- Base change commutes with Cartier's canonical `p`-typical coordinate. -/
theorem map_pTypicalCoordinate (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (f : R →+* S) :
    TauCeti.FormalCoordinate.map f (F.pTypicalCoordinate p hR) =
      (F.map f).pTypicalCoordinate p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map f) := by
  apply inv_inj.mp
  ext1
  rw [← map_inv, TauCeti.FormalCoordinate.toPowerSeries_map, toPowerSeries_inv_pTypicalCoordinate,
    toPowerSeries_inv_pTypicalCoordinate, ← Curve.toPowerSeries_map,
    F.map_pTypicalProjectorCurve p hR f, F.map_tautologicalCurve f]

/-- Base change commutes with Cartier's canonical `p`-typicalization. -/
theorem map_pTypicalize (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (f : R →+* S) :
    (F.pTypicalize p hR).map f =
      (F.map f).pTypicalize p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map f) := by
  rw [pTypicalize_def, pTypicalize_def, map_smul, F.map_pTypicalCoordinate p hR f]

/-- Over a `ℚ`-algebra, the formal logarithm of `F.pTypicalize p hunit` is `log_F((Π_p T)(X))`. -/
theorem log_pTypicalize [Algebra ℚ R] (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).log =
      PowerSeries.subst
        (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries F.log := by
  rw [pTypicalize_def, F.log_smul, F.linearCoeff_pTypicalCoordinate, Units.val_one, one_smul,
    F.toPowerSeries_inv_pTypicalCoordinate]

/-- Over a `ℚ`-algebra, `p`-typicalization leaves unchanged every formal-logarithm coefficient whose
degree has no prime divisor distinct from `p`. -/
theorem coeff_log_pTypicalize_of_forall_not_dvd [Algebra ℚ R]
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) :
    PowerSeries.coeff k (F.pTypicalize p hunit).log = PowerSeries.coeff k F.log := by
  rw [F.log_pTypicalize p hunit,
    F.coeff_subst_pTypicalProjectorCurve_log_of_forall_not_dvd p hunit hk F.tautologicalCurve,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, `p`-typicalization zeroes every formal-logarithm coefficient whose degree is
divisible by a prime `q ≠ p`. -/
theorem coeff_log_pTypicalize_eq_zero_of_prime_dvd [Algebra ℚ R]
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hqk : q ∣ k) :
    PowerSeries.coeff k (F.pTypicalize p hunit).log = 0 := by
  rw [F.log_pTypicalize p hunit,
    F.coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd p hunit hq hqp hqk
      F.tautologicalCurve]

/-- Over a `ℚ`-algebra, for `p` prime, the formal logarithm of `F.pTypicalize p hunit` retains the
coefficients of `F.log` in degrees `p ^ m` and zeroes all others. -/
theorem coeff_log_pTypicalize_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalize p hunit).log =
      if p ^ Nat.log p k = k then PowerSeries.coeff k F.log else 0 := by
  rw [F.log_pTypicalize p hunit,
    F.coeff_subst_pTypicalProjectorCurve_log_of_prime hp hunit k F.tautologicalCurve,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

@[simp]
theorem coeff_pow_log_pTypicalize [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (m : ℕ) :
    PowerSeries.coeff (p ^ m) (F.pTypicalize p hunit).log = PowerSeries.coeff (p ^ m) F.log := by
  rw [F.coeff_log_pTypicalize_of_prime hp hunit (p ^ m), Nat.log_pow hp.one_lt, ite_eq_left rfl]

@[simp]
theorem coeff_log_pTypicalize_eq_zero [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k) :
    PowerSeries.coeff k (F.pTypicalize p hunit).log = 0 := by
  rw [F.coeff_log_pTypicalize_of_prime hp hunit k, ite_eq_right (hk (Nat.log p k))]

/-- Over a `ℚ`-algebra, for `p` prime, Cartier's `p`-typicalization `F.pTypicalize p hunit` is
Hazewinkel's formal group law for a unique parameter family `v : ℕ+ → R`. -/
theorem existsUnique_pTypicalize_eq_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃! v : ℕ+ → R, F.pTypicalize p hunit = TauCeti.hazewinkelFormalGroup p v :=
  (F.isPTypical_pTypicalize p hunit).existsUnique_eq_hazewinkelFormalGroup hp

end PTypicalize

@[simp]
theorem pTypicalCoordinate_𝔾ₐ (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (𝔾ₐ (R := R)).pTypicalCoordinate p hunit = 1 :=
  ((𝔾ₐ (R := R)).pTypicalCoordinate_eq_one_iff p hunit).mpr (isPTypical_𝔾ₐ p)

@[simp]
theorem pTypicalize_𝔾ₐ (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (𝔾ₐ (R := R)).pTypicalize p hunit = 𝔾ₐ :=
  (𝔾ₐ (R := R)).pTypicalize_eq_self p hunit (isPTypical_𝔾ₐ p)

end FormalGroup
