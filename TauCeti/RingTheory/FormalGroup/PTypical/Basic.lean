/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Curve.PTypical

/-!
# `p`-typical formal group laws and Cartier–Quillen `p`-typicalization

A commutative one-dimensional formal group law `F(X, Y)` over a commutative ring `R` is
**`p`-typical** (`FormalGroup.IsPTypical`) if its tautological curve `γ(T) = T`
(`FormalGroup.tautologicalCurve`) is `p`-typical, that is,

  `f_q T = 0` on `F` for every prime `q ≠ p`.

Transporting `F` along a formal coordinate `φ` produces a `p`-typical formal group law `φ • F` if
and only if the inverse coordinate `φ⁻¹` is a `p`-typical curve on `F`
(`FormalGroup.isPTypical_smul_iff`). Over a `ℚ`-algebra and for a prime `p`, `F` is `p`-typical if
and only if its formal logarithm `log_F(X)` has nonzero coefficients only in degrees `p^n`.

When every prime `q ≠ p` is invertible in `R`, applying Cartier's `p`-typical curve projector
`FormalGroup.pTypicalProjectorCurve` to the tautological curve `T` produces a strict formal
coordinate `η_F = FormalGroup.pTypicalCoordinate F p hunit`. Changing coordinates by `η_F⁻¹`
defines the **Cartier–Quillen `p`-typicalization**

  `F.pTypicalize p hunit = η_F⁻¹ • F`,

which is canonically strictly isomorphic to `F` via `FormalGroup.pTypicalIso`, is `p`-typical over
any commutative ring in which primes `q ≠ p` are units, equals `F` if and only if `F` is already
`p`-typical, and commutes with base change. Over a `ℚ`-algebra (for `p` prime), the formal
logarithm of `F.pTypicalize p hunit` is obtained from `log_F(X)` by keeping the `X^(p^n)` terms
and deleting all other degrees.

## Main definitions

* `TauCeti.FormalCoordinate.toCurve`: a formal coordinate viewed as a curve on `F`.
* `FormalGroup.IsPTypical`: the predicate that `F.tautologicalCurve` is `p`-typical.
* `FormalGroup.pTypicalCoordinate`: the strict coordinate obtained by projecting
  `F.tautologicalCurve` onto `p`-typical curves.
* `FormalGroup.pTypicalize`: the `p`-typicalized formal group law `η_F⁻¹ • F`.
* `FormalGroup.pTypicalIso`: the canonical strict isomorphism `F ≅ F.pTypicalize p hunit`.

## Main results

* `FormalGroup.isPTypical_𝔾ₐ`: the additive formal group law is `p`-typical over any commutative
  ring.
* `FormalGroup.isPTypical_smul_iff` and `FormalGroup.isPTypical_inv_smul_iff`: coordinate-change
  characterization of `p`-typical formal group laws.
* `FormalGroup.isPTypical_iff_coeff_log_eq_zero`: rational logarithm characterization of
  `p`-typical formal group laws.
* `FormalGroup.isPTypical_pTypicalize`, `FormalGroup.pTypicalize_eq_self_iff`, and
  `FormalGroup.pTypicalize_pTypicalize`: `p`-typicality, fixed-point characterization, and
  idempotence of `FormalGroup.pTypicalize`.
* `FormalGroup.map_pTypicalCoordinate` and `FormalGroup.map_pTypicalize`: compatibility with base
  change.
* `FormalGroup.log_pTypicalize`, `FormalGroup.coeff_log_pTypicalize_pow`, and
  `FormalGroup.coeff_log_pTypicalize_eq_zero`: logarithm of `FormalGroup.pTypicalize` over a
  `ℚ`-algebra.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.2–16.4.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.21–A2.1.24.
-/

public section

namespace TauCeti.FormalCoordinate

variable {R S : Type*} [CommRing R] [CommRing S]

/-- View a formal coordinate `φ(T) = u T + ⋯` as a curve on a formal group law `F`. -/
def toCurve (φ : FormalCoordinate R) (F : FormalGroup R) : F.Curve where
  toPowerSeries := φ.toPowerSeries
  constantCoeff_toPowerSeries := φ.constantCoeff_toPowerSeries

/-- Viewing a formal coordinate as a curve preserves its underlying power series. -/
@[simp]
theorem toPowerSeries_toCurve (φ : FormalCoordinate R) (F : FormalGroup R) :
    (φ.toCurve F).toPowerSeries = φ.toPowerSeries :=
  (rfl)

/-- The identity coordinate `X` viewed as a curve on `F` is the tautological curve of `F`. -/
@[simp]
theorem one_toCurve (F : FormalGroup R) :
    (1 : FormalCoordinate R).toCurve F = F.tautologicalCurve :=
  FormalGroup.Curve.ext (by simp)

/-- Two formal coordinates are equal if they give the same curve on `F`. -/
theorem toCurve_injective (F : FormalGroup R) :
    Function.Injective (fun φ : FormalCoordinate R ↦ φ.toCurve F) :=
  fun _ _ h ↦ FormalCoordinate.ext (congrArg FormalGroup.Curve.toPowerSeries h)

/-- Viewing a formal coordinate as a curve commutes with base change. -/
@[simp]
theorem map_toCurve (f : R →+* S) (φ : FormalCoordinate R) (F : FormalGroup R) :
    (φ.map f).toCurve (F.map f) = FormalGroup.Curve.map f (φ.toCurve F) :=
  FormalGroup.Curve.ext (by simp [toPowerSeries_map])

end TauCeti.FormalCoordinate

namespace FormalGroup

open TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws -/

/-- A commutative formal group law `F` over `R` is **`p`-typical** if its tautological curve
`γ(T) = T` is `p`-typical (`f_q T = 0` for all primes `q ≠ p`). -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve.IsPTypical p

/-- Defining equivalence for `FormalGroup.IsPTypical`. -/
theorem isPTypical_iff_tautologicalCurve (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔ F.tautologicalCurve.IsPTypical p :=
  (Iff.rfl)

/-- Equal commutative formal group laws have the same `p`-typicality. -/
theorem isPTypical_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) (p : ℕ) :
    F.IsPTypical p ↔ G.IsPTypical p := by
  subst h
  rfl

/-- The tautological curve of a `p`-typical formal group law is `p`-typical. -/
theorem IsPTypical.tautologicalCurve {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) : F.tautologicalCurve.IsPTypical p :=
  hF

/-- A commutative formal group law is `p`-typical if and only if `f_n T = 0` for every nonzero `n`
not of the form `p^k`. -/
theorem isPTypical_iff_forall_ne_pow (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ ⦃n : ℕ⦄ (hn : n ≠ 0), (∀ k, n ≠ p ^ k) →
        F.frobeniusCurve n hn F.tautologicalCurve = 0 :=
  F.tautologicalCurve.isPTypical_iff_forall_ne_pow p

/-- For a prime `p`, a commutative formal group law is `p`-typical if and only if `f_n T = 0` for
every `n > 1` coprime to `p`. -/
theorem isPTypical_iff_forall_coprime (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔
      ∀ ⦃n : ℕ⦄ (hn : 1 < n), p.Coprime n →
        F.frobeniusCurve n (by omega) F.tautologicalCurve = 0 :=
  F.tautologicalCurve.isPTypical_iff_forall_coprime hp

/-- The additive formal group law `𝔾ₐ` is `p`-typical over any commutative ring. -/
@[simp]
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ : FormalGroup R).IsPTypical p := by
  rw [isPTypical_iff_tautologicalCurve, Curve.isPTypical_def]
  intro q hq _
  ext k
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, Curve.toPowerSeries_zero, map_zero, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero, toPowerSeries_tautologicalCurve, PowerSeries.coeff_X]
  have hne : q * k ≠ 1 := by
    have hq1 := hq.one_lt
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
      nlinarith
  rw [ite_eq_right hne, smul_zero]

/-- Base change along a ring homomorphism preserves `p`-typical formal group laws. -/
theorem IsPTypical.map (φ : R →+* S) {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) : (F.map φ).IsPTypical p := by
  simpa only [isPTypical_iff_tautologicalCurve, ← map_tautologicalCurve] using
    hF.tautologicalCurve.map φ

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typical formal
group laws. -/
theorem isPTypical_map_iff {φ : R →+* S} (hφ : Function.Injective φ)
    (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [isPTypical_iff_tautologicalCurve, ← map_tautologicalCurve,
    Curve.isPTypical_map_iff hφ, ← isPTypical_iff_tautologicalCurve]

/-- Changing the coordinate of `F` by `φ` yields a `p`-typical formal group law `φ • F` if and
only if the inverse coordinate `φ⁻¹` is a `p`-typical curve on `F`. -/
theorem isPTypical_smul_iff (φ : FormalCoordinate R) (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    (φ • F).IsPTypical p ↔ (φ⁻¹.toCurve F).IsPTypical p := by
  have hcurve : (smulIso φ F).invHom.mapCurve (φ • F).tautologicalCurve = φ⁻¹.toCurve F :=
    Curve.ext (by simp)
  rw [isPTypical_iff_tautologicalCurve,
    ← (smulIso φ F).isPTypical_mapCurve_invHom_iff (φ • F).tautologicalCurve p, hcurve]

/-- Changing the coordinate of `F` by `φ⁻¹` yields a `p`-typical formal group law `φ⁻¹ • F` if
and only if `φ` is a `p`-typical curve on `F`. -/
theorem isPTypical_inv_smul_iff (φ : FormalCoordinate R) (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    (φ⁻¹ • F).IsPTypical p ↔ (φ.toCurve F).IsPTypical p := by
  simpa only [inv_inv] using isPTypical_smul_iff φ⁻¹ F p

/-- Over a `ℚ`-algebra, the formal logarithm of a `p`-typical formal group law vanishes outside
degrees `p^n`. -/
theorem IsPTypical.coeff_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k F.log = 0 := by
  simpa only [toPowerSeries_tautologicalCurve, PowerSeries.X_subst] using
    hF.tautologicalCurve.coeff_subst_log_eq_zero hk

/-- Over a `ℚ`-algebra and for a prime `p`, a commutative formal group law `F` is `p`-typical if
and only if `log_F(X)` has zero coefficients outside degrees `p^n`. -/
theorem isPTypical_iff_coeff_log_eq_zero [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ k, (∀ n, p ^ n ≠ k) → PowerSeries.coeff k F.log = 0 := by
  simpa only [isPTypical_iff_tautologicalCurve, toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst] using
    F.tautologicalCurve.isPTypical_iff_coeff_subst_log_eq_zero hp

/-! ### Cartier–Quillen `p`-typicalization -/

section PTypicalize

variable (F : FormalGroup R) [F.IsComm]

/-- The strict formal coordinate obtained by applying Cartier's `p`-typical curve projector to the
tautological curve of `F`. -/
noncomputable def pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : FormalCoordinate R where
  toPowerSeries := (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries :=
    (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries
  isUnit_coeff_one := by
    rw [coeff_one_pTypicalProjectorCurve, toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X]
    exact isUnit_one

/-- The underlying power series of `FormalGroup.pTypicalCoordinate`. -/
@[simp]
theorem toPowerSeries_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit).toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries :=
  (rfl)

/-- Viewed as a curve on `F`, `F.pTypicalCoordinate p hunit` is Cartier's `p`-typical projection of
the tautological curve. -/
@[simp]
theorem toCurve_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit).toCurve F =
      F.pTypicalProjectorCurve p hunit F.tautologicalCurve :=
  Curve.ext rfl

/-- `FormalGroup.pTypicalCoordinate` has linear coefficient `1`. -/
theorem coeff_one_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff 1 (F.pTypicalCoordinate p hunit).toPowerSeries = 1 := by
  rw [toPowerSeries_pTypicalCoordinate, coeff_one_pTypicalProjectorCurve,
    toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X]

/-- `FormalGroup.pTypicalCoordinate` is a strict formal coordinate (`linearCoeff = 1`). -/
@[simp]
theorem linearCoeff_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit) = 1 :=
  Units.ext (by simp)

/-- Viewed as a curve on `F`, `F.pTypicalCoordinate p hunit` is `p`-typical. -/
theorem isPTypical_toCurve_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    ((F.pTypicalCoordinate p hunit).toCurve F).IsPTypical p := by
  rw [toCurve_pTypicalCoordinate]
  exact F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve

/-- The `p`-typicalizing coordinate of `F` is the identity coordinate `X` if and only if `F` is
already `p`-typical. -/
@[simp]
theorem pTypicalCoordinate_eq_one_iff (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = 1 ↔ F.IsPTypical p := by
  rw [← (FormalCoordinate.toCurve_injective F).eq_iff, toCurve_pTypicalCoordinate,
    FormalCoordinate.one_toCurve, pTypicalProjectorCurve_eq_self_iff,
    ← isPTypical_iff_tautologicalCurve]

/-- **Cartier–Quillen `p`-typicalization** of a commutative formal group law `F` over a ring in
which all primes `q ≠ p` are units: the formal group law obtained by changing coordinates along the
inverse of `FormalGroup.pTypicalCoordinate`. -/
noncomputable def pTypicalize (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : FormalGroup R :=
  (F.pTypicalCoordinate p hunit)⁻¹ • F

/-- `FormalGroup.pTypicalize` is defined by transporting `F` along
`(F.pTypicalCoordinate p hunit)⁻¹`. -/
theorem pTypicalize_def (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = (F.pTypicalCoordinate p hunit)⁻¹ • F :=
  (rfl)

instance (p : ℕ) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).IsComm :=
  instIsCommSMul _ _

/-- The canonical strict isomorphism `F ≅ F.pTypicalize p hunit` induced by
`(F.pTypicalCoordinate p hunit)⁻¹`. -/
noncomputable def pTypicalIso (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    FormalGroupIso F (F.pTypicalize p hunit) :=
  smulIso (F.pTypicalCoordinate p hunit)⁻¹ F

instance (p : ℕ) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).IsStrict :=
  (isStrict_smulIso_iff _ F).mpr <| by
    rw [map_inv, linearCoeff_pTypicalCoordinate, inv_one]

/-- The forward power series of `FormalGroup.pTypicalIso` is `(F.pTypicalCoordinate p hunit)⁻¹`. -/
@[simp]
theorem pTypicalIso_toHom_toPowerSeries (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).toHom.toPowerSeries =
      ((F.pTypicalCoordinate p hunit)⁻¹).toPowerSeries :=
  smulIso_toHom_toPowerSeries _ F

/-- The inverse power series of `FormalGroup.pTypicalIso` is `F.pTypicalCoordinate p hunit`. -/
@[simp]
theorem pTypicalIso_invHom_toPowerSeries (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).invHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit).toPowerSeries := by
  simp [pTypicalIso]

/-- The `p`-typicalization of every commutative formal group law is `p`-typical. -/
theorem isPTypical_pTypicalize (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).IsPTypical p := by
  rw [isPTypical_congr (F.pTypicalize_def p hunit), isPTypical_inv_smul_iff]
  exact F.isPTypical_toCurve_pTypicalCoordinate p hunit

/-- A `p`-typical formal group law is fixed by `FormalGroup.pTypicalize`. -/
theorem pTypicalize_eq_self {p : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalize p hunit = F := by
  rw [pTypicalize_def, (F.pTypicalCoordinate_eq_one_iff p hunit).mpr hF, inv_one, one_smul]

/-- `F.pTypicalize p hunit` equals `F` if and only if `F` is `p`-typical. -/
@[simp]
theorem pTypicalize_eq_self_iff (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = F ↔ F.IsPTypical p :=
  ⟨fun h ↦ (isPTypical_congr h p).mp (F.isPTypical_pTypicalize p hunit),
   F.pTypicalize_eq_self hunit⟩

/-- The `p`-typicalizing coordinate of `F.pTypicalize p hunit` is the identity coordinate `X`. -/
@[simp]
theorem pTypicalCoordinate_pTypicalize (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).pTypicalCoordinate p hunit = 1 :=
  ((F.pTypicalize p hunit).pTypicalCoordinate_eq_one_iff p hunit).mpr
    (F.isPTypical_pTypicalize p hunit)

/-- `FormalGroup.pTypicalize` is idempotent. -/
@[simp]
theorem pTypicalize_pTypicalize (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).pTypicalize p hunit = F.pTypicalize p hunit :=
  ((F.pTypicalize p hunit).pTypicalize_eq_self_iff p hunit).mpr
    (F.isPTypical_pTypicalize p hunit)

/-- Base change commutes with `FormalGroup.pTypicalCoordinate`. -/
theorem map_pTypicalCoordinate (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    FormalCoordinate.map φ (F.pTypicalCoordinate p hR) =
      (F.map φ).pTypicalCoordinate p (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) := by
  apply FormalCoordinate.toCurve_injective (F.map φ)
  dsimp only
  rw [FormalCoordinate.map_toCurve, toCurve_pTypicalCoordinate, toCurve_pTypicalCoordinate,
    F.map_pTypicalProjectorCurve φ p hR, map_tautologicalCurve]

/-- Base change commutes with `FormalGroup.pTypicalize`. -/
theorem map_pTypicalize (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hR).map φ =
      (F.map φ).pTypicalize p (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) := by
  rw [pTypicalize_def, pTypicalize_def, map_smul, map_inv, F.map_pTypicalCoordinate φ p hR]

/-- Over a `ℚ`-algebra, the formal logarithm of `F.pTypicalize p hunit` is obtained by
substituting `F.pTypicalCoordinate p hunit` into `F.log`. -/
theorem log_pTypicalize [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).log =
      PowerSeries.subst (F.pTypicalCoordinate p hunit).toPowerSeries F.log := by
  rw [pTypicalize_def, log_smul, map_inv, linearCoeff_pTypicalCoordinate, inv_one,
    Units.val_one, one_smul, inv_inv]

/-- Over a `ℚ`-algebra, the formal logarithm of `F.pTypicalize p hunit` vanishes outside degrees
`p^n`. -/
theorem coeff_log_pTypicalize_eq_zero [Algebra ℚ R] {p k : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k (F.pTypicalize p hunit).log = 0 :=
  (F.isPTypical_pTypicalize p hunit).coeff_log_eq_zero hk

/-- Over a `ℚ`-algebra and for a prime `p`, `F.pTypicalize p hunit` has the same degree-`p^n`
logarithm coefficients as `F`. -/
@[simp]
theorem coeff_log_pTypicalize_pow [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    PowerSeries.coeff (p ^ n) (F.pTypicalize p hunit).log =
      PowerSeries.coeff (p ^ n) F.log := by
  rw [log_pTypicalize, toPowerSeries_pTypicalCoordinate,
    F.coeff_subst_pTypicalProjectorCurve_log_pow hp hunit,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

end PTypicalize

end FormalGroup
