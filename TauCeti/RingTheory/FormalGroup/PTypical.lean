/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.PTypical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
import TauCeti.RingTheory.FormalGroup.CoordinateChange.Graded

/-!
# `p`-typical formal group laws and canonical `p`-typicalization

A commutative one-dimensional formal group law `F` over a commutative ring `R` is **`p`-typical**
(`FormalGroup.IsPTypical F p`) if its tautological curve `γ_0(T) = T` is a `p`-typical curve in the
sense of Cartier (`FormalGroup.Curve.IsPTypical`), i.e., `f_q γ_0 = 0` for every prime `q ≠ p`.

Over a `ℚ`-algebra `K` with `p` prime, `F` is `p`-typical if and only if its formal logarithm
`log_F(X)` has zero coefficients in all degrees outside `{p^m | m : ℕ}`, and hence if and only if
`F = TauCeti.hazewinkelFormalGroup p v` for a unique family `v : ℕ+ → K`. Hazewinkel's integral
formal group law `TauCeti.hazewinkelIntegralFormalGroup p v` is `p`-typical over **every**
commutative ring `R`, including rings with `p`-torsion. Moreover, `p`-typicality is preserved by
arbitrary base change and by rescaling `FormalGroup.rescale F s` at any element `s : R` (zero
divisor or not).

When every prime `q ≠ p` is invertible in `R` (for instance over `ℚ`-algebras, local rings of
residue characteristic `p`, or `ℤ_{(p)}`-algebras), applying Cartier's `p`-typicalization projector
`FormalGroup.pTypicalProjectorCurve F p hunit` to the tautological curve produces a `p`-typical
curve `ψ_F(T) = T + ⋯` with linear coefficient `1`. Its compositional inverse defines a canonical
strict formal coordinate `FormalGroup.pTypicalCoordinate F p hunit`, and transporting `F` along this
coordinate gives Quillen's **canonical `p`-typicalization**

  `FormalGroup.pTypicalize F p hunit := F.pTypicalCoordinate p hunit • F`,

together with the canonical strict isomorphism
`FormalGroup.pTypicalizeIso F p hunit : F ≅ F.pTypicalize p hunit`. Over arbitrary commutative rings
with primes `q ≠ p` invertible, `pTypicalize`:

* produces a `p`-typical formal group law;
* fixes `F` (with `pTypicalCoordinate = 1`) if and only if `F` is already `p`-typical, and in
  particular is idempotent and fixes `𝔾ₐ` and `hazewinkelIntegralFormalGroup p v`;
* commutes with base change and with rescaling `F.rescale s` for every `s : R`, and therefore
  preserves the grading of any graded formal group law (`FormalGroup.coeff_pTypicalize_mem`);
* over a `ℚ`-algebra with `p` prime, deletes precisely the non-`p`-power terms of `log_F(X)` while
  preserving `coeff (p^m) log_F` for all `m : ℕ`.

## Main definitions

* `FormalGroup.IsPTypical`: predicate that a commutative formal group law is `p`-typical.
* `FormalGroup.pTypicalCoordinate`: the canonical strict coordinate transporting `F` to its
  `p`-typicalization when primes `q ≠ p` are invertible in `R`.
* `FormalGroup.pTypicalize`: Quillen's canonical `p`-typicalization `pTypicalCoordinate • F`.
* `FormalGroup.pTypicalizeIso`: the canonical strict isomorphism `F ≅ F.pTypicalize p hunit`.

## Main results

* `FormalGroup.IsPTypical.rescale`: rescaling by any `s : R` preserves `p`-typicality.
* `FormalGroup.isPTypical_iff_forall_coeff_log_eq_zero` and
  `FormalGroup.IsPTypical.existsUnique_eq_hazewinkelFormalGroup`: rational logarithm and Hazewinkel
  classification of `p`-typical formal group laws over `ℚ`-algebras.
* `TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup` and
  `TauCeti.isPTypical_hazewinkelIntegralFormalGroup`: Hazewinkel's integral formal group laws are
  `p`-typical over arbitrary commutative rings.
* `FormalGroup.isPTypical_pTypicalize`, `FormalGroup.pTypicalize_eq_self_iff`, and
  `FormalGroup.pTypicalize_pTypicalize`: `p`-typicality, fixed-point characterization, and
  idempotency of `pTypicalize`.
* `FormalGroup.pTypicalize_rescale` and `FormalGroup.coeff_pTypicalize_mem`: compatibility of
  `pTypicalize` with rescaling and `ℕ`-gradings.
* `FormalGroup.coeff_log_pTypicalize`: rational logarithm coefficients of `pTypicalize`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter III,
  §16.3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.20–A2.1.21.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws -/

/-- A commutative formal group law `F` over `R` is **`p`-typical** if its tautological curve
`γ_0(T) = T` is `p`-typical, i.e., `f_q γ_0 = 0` for every prime `q ≠ p`. -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve.IsPTypical p

/-- Unfold `FormalGroup.IsPTypical` in terms of `FormalGroup.Curve.IsPTypical`. -/
theorem isPTypical_def (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔ F.tautologicalCurve.IsPTypical p :=
  (Iff.rfl)

/-- Unfold `FormalGroup.IsPTypical` in terms of Cartier's Frobenius operators `f_q`. -/
theorem isPTypical_iff (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ q : ℕ, ∀ hq : q.Prime, q ≠ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 := by
  rw [isPTypical_def, Curve.isPTypical_def]

/-- Equality of commutative formal group laws gives equivalence of `IsPTypical`. -/
theorem isPTypical_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) {p : ℕ} :
    F.IsPTypical p ↔ G.IsPTypical p := by
  subst h
  rfl

/-- When `p` is prime, `F` is `p`-typical if and only if `f_n` kills the tautological curve for
every `n > 1` coprime to `p`. -/
theorem isPTypical_iff_frobeniusCurve_eq_zero_of_coprime (F : FormalGroup R) [F.IsComm] {p : ℕ}
    (hp : p.Prime) :
    F.IsPTypical p ↔
      ∀ n : ℕ, 1 < n → n.Coprime p → ∀ hn : n ≠ 0,
        F.frobeniusCurve n hn F.tautologicalCurve = 0 :=
  F.tautologicalCurve.isPTypical_iff_frobeniusCurve_eq_zero_of_coprime hp

/-- `F` is `p`-typical if and only if `f_n` kills the tautological curve at every nonzero index `n`
that is not a power of `p`. -/
theorem isPTypical_iff_frobeniusCurve_eq_zero_of_forall_pow_ne (F : FormalGroup R) [F.IsComm]
    (p : ℕ) :
    F.IsPTypical p ↔
      ∀ n : ℕ, ∀ hn : n ≠ 0, (∀ m : ℕ, p ^ m ≠ n) →
        F.frobeniusCurve n hn F.tautologicalCurve = 0 :=
  F.tautologicalCurve.isPTypical_iff_frobeniusCurve_eq_zero_of_forall_pow_ne p

/-- The additive formal group law `𝔾ₐ` is `p`-typical for every `p`. -/
@[simp]
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ (R := R)).IsPTypical p := by
  rw [isPTypical_iff]
  intro q hq _
  apply Curve.ext
  ext k
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_tautologicalCurve, Curve.toPowerSeries_zero,
    PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, PowerSeries.coeff_X, map_zero]
  have hne : q * k ≠ 1 := by
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · have hgt : 1 < q * k := lt_of_lt_of_le hq.one_lt (Nat.le_mul_of_pos_right q (by omega))
      omega
  rw [ite_eq_right hne, smul_zero]

/-- Base change preserves `p`-typicality of commutative formal group laws. -/
theorem IsPTypical.map {F : FormalGroup R} [F.IsComm] {p : ℕ} (h : F.IsPTypical p) (φ : R →+* S) :
    (F.map φ).IsPTypical p := by
  simpa only [isPTypical_def, ← F.map_tautologicalCurve φ] using Curve.IsPTypical.map h φ

/-- Base change along an injective ring homomorphism reflects and preserves `p`-typicality. -/
@[simp]
theorem isPTypical_map_iff {F : FormalGroup R} [F.IsComm] {φ : R →+* S} (hφ : Function.Injective φ)
    {p : ℕ} : (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [isPTypical_def, isPTypical_def, ← F.map_tautologicalCurve φ, Curve.isPTypical_map_iff hφ]

/-! ### Coordinate changes, homomorphisms, and rescaling -/

/-- Every homomorphism out of a `p`-typical formal group law defines a `p`-typical curve on the
target. -/
theorem _root_.TauCeti.FormalGroupHom.isPTypical_mapCurve_tautologicalCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) {p : ℕ}
    (hF : F.IsPTypical p) : (f.mapCurve F.tautologicalCurve).IsPTypical p :=
  f.isPTypical_mapCurve hF

/-- An isomorphism `e : F ≅ G` identifies `p`-typicality of `F` with `p`-typicality of `e` viewed as
a curve on `G`. -/
theorem _root_.TauCeti.FormalGroupIso.isPTypical_iff_isPTypical_mapCurve_tautologicalCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) {p : ℕ} :
    F.IsPTypical p ↔ (e.toHom.mapCurve F.tautologicalCurve).IsPTypical p := by
  rw [isPTypical_def, ← e.isPTypical_curveEquiv_iff, e.curveEquiv_apply]

/-- Transporting `F` along a formal coordinate `φ` gives a `p`-typical formal group law if and only
if the inverse coordinate `φ⁻¹`, viewed as a curve on `F`, is `p`-typical. -/
theorem isPTypical_smul_iff (F : FormalGroup R) [F.IsComm] (φ : TauCeti.FormalCoordinate R)
    (p : ℕ) :
    (φ • F).IsPTypical p ↔
      (⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve).IsPTypical p := by
  rw [isPTypical_def, ← (smulIso φ F).isPTypical_mapCurve_invHom_iff,
    show (smulIso φ F).invHom.mapCurve (φ • F).tautologicalCurve =
      ⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩ from Curve.ext (by simp)]

/-- Transporting `F` along `ψ⁻¹` gives a `p`-typical formal group law if and only if `ψ`, viewed as
a curve on `F`, is `p`-typical. -/
theorem isPTypical_inv_smul_iff (F : FormalGroup R) [F.IsComm] (ψ : TauCeti.FormalCoordinate R)
    (p : ℕ) :
    (ψ⁻¹ • F).IsPTypical p ↔
      (⟨ψ.toPowerSeries, ψ.constantCoeff_toPowerSeries⟩ : F.Curve).IsPTypical p := by
  rw [isPTypical_smul_iff, inv_inv]

private theorem isPTypical_rescale_of_isLeftRegular {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) {s : R} (hs : IsLeftRegular s) : (F.rescale s).IsPTypical p := by
  rw [isPTypical_iff]
  intro q hq hqp
  have hinj : Function.Injective (F.rescaleHom s).mapCurve := fun γ₁ γ₂ h ↦ by
    ext k
    have hk := congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries) h
    simp only [Function.comp_apply, toPowerSeries_mapCurve_rescaleHom, PowerSeries.coeff_smul,
      smul_eq_mul] at hk
    exact hs hk
  apply hinj
  have h0 : F.frobeniusCurve q hq.ne_zero (F.rescaleCurve s F.tautologicalCurve) = 0 :=
    ((Curve.isPTypical_def _ p).mp (Curve.IsPTypical.rescaleCurve hF s)) q hq hqp
  rw [(F.rescaleHom s).mapCurve_frobeniusCurve, mapCurve_rescaleHom_tautologicalCurve,
    map_zero, h0]

private theorem map_evalRingHom_rescale_X (L : FormalGroup R) (s : R) :
    ((L.map Polynomial.C).rescale Polynomial.X).map (Polynomial.evalRingHom s) =
      L.rescale s := by
  rw [map_rescale, map_comp]
  simp only [Polynomial.evalRingHom, Polynomial.eval₂RingHom_comp_C, map_id,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- Rescaling a `p`-typical formal group law by any element `s : R` (zero divisor or not) preserves
`p`-typicality. -/
theorem IsPTypical.rescale {F : FormalGroup R} [F.IsComm] {p : ℕ} (hF : F.IsPTypical p) (s : R) :
    (F.rescale s).IsPTypical p := by
  have hgen : ((F.map Polynomial.C).rescale Polynomial.X).IsPTypical p :=
    isPTypical_rescale_of_isLeftRegular (hF.map Polynomial.C) Polynomial.isRegular_X.left
  exact (isPTypical_congr (map_evalRingHom_rescale_X F s)).mp (hgen.map (Polynomial.evalRingHom s))

/-- Changing coordinates by a homothety `X ↦ u X` preserves and reflects `p`-typicality. -/
@[simp]
theorem isPTypical_homothety_smul_iff (F : FormalGroup R) [F.IsComm] (u : Rˣ) (p : ℕ) :
    (TauCeti.FormalCoordinate.homothety u • F).IsPTypical p ↔ F.IsPTypical p := by
  refine ⟨fun h ↦ ?_, fun h ↦ (isPTypical_congr (homothety_smul F u).symm).mp (h.rescale _)⟩
  have h' : (TauCeti.FormalCoordinate.homothety u⁻¹ •
      (TauCeti.FormalCoordinate.homothety u • F)).IsPTypical p :=
    (isPTypical_congr (homothety_smul _ u⁻¹).symm).mp (h.rescale _)
  have heq : TauCeti.FormalCoordinate.homothety u⁻¹ •
      (TauCeti.FormalCoordinate.homothety u • F) = F := by
    rw [map_inv, inv_smul_smul]
  exact (isPTypical_congr heq).mp h'

/-! ### Rational logarithm characterization and Hazewinkel's `p`-typical laws -/

/-- Over a `ℚ`-algebra, the formal logarithm of a `p`-typical formal group law vanishes outside the
degrees `p^m`. -/
theorem IsPTypical.coeff_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k) :
    PowerSeries.coeff k F.log = 0 := by
  simpa only [toPowerSeries_tautologicalCurve, PowerSeries.X_subst] using
    Curve.IsPTypical.coeff_subst_log_eq_zero hF hk

/-- Over a `ℚ`-algebra, when `p` is prime, a commutative formal group law `F` is `p`-typical if and
only if `log_F(X)` has zero coefficients outside the degrees `p^m`. -/
theorem isPTypical_iff_forall_coeff_log_eq_zero [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ k : ℕ, (∀ m : ℕ, p ^ m ≠ k) → PowerSeries.coeff k F.log = 0 := by
  simpa only [isPTypical_def, toPowerSeries_tautologicalCurve, PowerSeries.X_subst] using
    Curve.isPTypical_iff_forall_coeff_subst_log_eq_zero hp F.tautologicalCurve

/-- Over a `ℚ`-algebra, when `p` is prime, Hazewinkel's formal group law `hazewinkelFormalGroup p v`
is `p`-typical. -/
@[simp]
theorem _root_.TauCeti.isPTypical_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (v : ℕ+ → R) : (TauCeti.hazewinkelFormalGroup p v).IsPTypical p := by
  rw [isPTypical_iff_forall_coeff_log_eq_zero _ hp]
  intro k hk
  rw [TauCeti.log_hazewinkelFormalGroup, TauCeti.coeff_hazewinkelLog_eq_zero v hk]

/-- Over a `ℚ`-algebra, when `p` is prime, every `p`-typical formal group law is
`TauCeti.hazewinkelFormalGroup p v` for a unique family `v`. -/
theorem IsPTypical.existsUnique_eq_hazewinkelFormalGroup [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {p : ℕ} (hp : p.Prime) (hF : F.IsPTypical p) :
    ∃! v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt fun _ hk ↦ hF.coeff_log_eq_zero hk

/-- Over a `ℚ`-algebra, when `p` is prime, a commutative formal group law is `p`-typical if and only
if it is of the form `TauCeti.hazewinkelFormalGroup p v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∃ v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  ⟨fun hF ↦ (hF.existsUnique_eq_hazewinkelFormalGroup hp).exists,
    fun ⟨v, hv⟩ ↦ (isPTypical_congr hv).mpr (TauCeti.isPTypical_hazewinkelFormalGroup hp v)⟩

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem _root_.TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup (p : ℕ)
    [hp : Fact p.Prime] :
    (TauCeti.universalHazewinkelIntegralFormalGroup p).IsPTypical p := by
  rw [← isPTypical_map_iff (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective),
    isPTypical_congr (TauCeti.map_intCast_universalHazewinkelIntegralFormalGroup p)]
  exact TauCeti.isPTypical_hazewinkelFormalGroup hp.out MvPolynomial.X

/-- Hazewinkel's integral formal group law `hazewinkelIntegralFormalGroup p v` is `p`-typical over
every commutative ring `R`, including rings with torsion. -/
@[simp]
theorem _root_.TauCeti.isPTypical_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) : (TauCeti.hazewinkelIntegralFormalGroup p v).IsPTypical p :=
  (isPTypical_congr (TauCeti.hazewinkelIntegralFormalGroup_def p v)).mpr
    ((TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup p).map _)

/-! ### Canonical strict `p`-typicalization -/

section PTypicalize

variable (F : FormalGroup R) [F.IsComm]

/-- Applying Cartier's `p`-typicalization projector to the tautological curve gives a strict formal
coordinate, whose compositional inverse `FormalGroup.pTypicalCoordinate` transports `F` to its
canonical `p`-typicalization. -/
private noncomputable def invPTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R where
  toPowerSeries := (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries :=
    (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries
  isUnit_coeff_one := by
    rw [F.coeff_one_pTypicalProjectorCurve, toPowerSeries_tautologicalCurve,
      PowerSeries.coeff_one_X]
    exact isUnit_one

/-- The canonical strict formal coordinate transporting a commutative formal group law `F` to its
`p`-typicalization `FormalGroup.pTypicalize F p hunit`, when every prime `q ≠ p` is invertible in
`R`. Its compositional inverse is Cartier's `p`-typicalization of the tautological curve. -/
noncomputable def pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R :=
  (F.invPTypicalCoordinate p hunit)⁻¹

/-- The inverse of `FormalGroup.pTypicalCoordinate` has underlying series equal to Cartier's
`p`-typicalization of the tautological curve. -/
theorem toPowerSeries_inv_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalCoordinate, inv_inv]
  rfl

/-- Equality of commutative formal group laws gives equality of `pTypicalCoordinate`. -/
theorem pTypicalCoordinate_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = G.pTypicalCoordinate p hunit := by
  subst h
  rfl

/-- `FormalGroup.pTypicalCoordinate` is a strict coordinate (`linearCoeff = 1`). -/
@[simp]
theorem linearCoeff_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit) = 1 := by
  have hinv : TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit)⁻¹ = 1 := by
    ext
    rw [TauCeti.FormalCoordinate.val_linearCoeff, toPowerSeries_inv_pTypicalCoordinate,
      F.coeff_one_pTypicalProjectorCurve, toPowerSeries_tautologicalCurve,
      PowerSeries.coeff_one_X, Units.val_one]
  rw [map_inv] at hinv
  exact inv_injective (hinv.trans inv_one.symm)

/-- The linear coefficient of `FormalGroup.pTypicalCoordinate` is `1`. -/
@[simp]
theorem coeff_one_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff 1 (F.pTypicalCoordinate p hunit).toPowerSeries = 1 := by
  rw [← TauCeti.FormalCoordinate.val_linearCoeff, F.linearCoeff_pTypicalCoordinate, Units.val_one]

/-- **Quillen's canonical `p`-typicalization** of a commutative formal group law `F` over a ring `R`
in which every prime `q ≠ p` is invertible, obtained by transporting `F` along
`FormalGroup.pTypicalCoordinate F p hunit`. -/
noncomputable def pTypicalize (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : FormalGroup R :=
  F.pTypicalCoordinate p hunit • F

/-- Unfold `FormalGroup.pTypicalize` as the coordinate transport by `pTypicalCoordinate`. -/
theorem pTypicalize_def (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = F.pTypicalCoordinate p hunit • F := (rfl)

/-- Equality of commutative formal group laws gives equality of `pTypicalize`. -/
theorem pTypicalize_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = G.pTypicalize p hunit := by
  subst h
  rfl

instance (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).IsComm :=
  inferInstanceAs (F.pTypicalCoordinate p hunit • F).IsComm

/-- The canonical strict isomorphism `F ≅ F.pTypicalize p hunit`. -/
noncomputable def pTypicalizeIso (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalGroupIso F (F.pTypicalize p hunit) :=
  smulIso (F.pTypicalCoordinate p hunit) F

/-- The forward power series of `FormalGroup.pTypicalizeIso` is `FormalGroup.pTypicalCoordinate`. -/
@[simp]
theorem pTypicalizeIso_toHom_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).toHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit).toPowerSeries :=
  smulIso_toHom_toPowerSeries _ _

/-- The inverse power series of `FormalGroup.pTypicalizeIso` is Cartier's `p`-typicalization of the
tautological curve. -/
@[simp]
theorem pTypicalizeIso_invHom_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).invHom.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalizeIso, smulIso_invHom_toPowerSeries, toPowerSeries_inv_pTypicalCoordinate]

instance (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).IsStrict :=
  (isStrict_smulIso_iff (F.pTypicalCoordinate p hunit) F).mpr
    (F.linearCoeff_pTypicalCoordinate p hunit)

/-- Pushing the tautological curve of `F.pTypicalize p hunit` along `(F.pTypicalizeIso p hunit)⁻¹`
recovers Cartier's `p`-typicalization of `F.tautologicalCurve`. -/
theorem mapCurve_invHom_pTypicalizeIso_tautologicalCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalizeIso p hunit).invHom.mapCurve (F.pTypicalize p hunit).tautologicalCurve =
      F.pTypicalProjectorCurve p hunit F.tautologicalCurve :=
  Curve.ext (by simp)

/-- Precomposing any homomorphism `f : F → G` with `(F.pTypicalizeIso p hunit)⁻¹` projects the
corresponding curve on `G` by Cartier's `p`-typicalization projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_comp_invHom_pTypicalizeIso_tautologicalCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (f.comp (F.pTypicalizeIso p hunit).invHom).mapCurve
        (F.pTypicalize p hunit).tautologicalCurve =
      G.pTypicalProjectorCurve p hunit (f.mapCurve F.tautologicalCurve) := by
  rw [TauCeti.FormalGroupHom.comp_mapCurve, F.mapCurve_invHom_pTypicalizeIso_tautologicalCurve,
    f.mapCurve_pTypicalProjectorCurve]

/-- The canonical `p`-typicalization `F.pTypicalize p hunit` is `p`-typical. -/
@[simp]
theorem isPTypical_pTypicalize (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).IsPTypical p := by
  rw [(F.pTypicalizeIso p hunit).symm.isPTypical_iff_isPTypical_mapCurve_tautologicalCurve,
    TauCeti.FormalGroupIso.symm_toHom, F.mapCurve_invHom_pTypicalizeIso_tautologicalCurve]
  exact F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve

/-- The canonical `p`-typicalizing coordinate is the identity coordinate `1` if and only if `F` is
already `p`-typical. -/
@[simp]
theorem pTypicalCoordinate_eq_one_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = 1 ↔ F.IsPTypical p := by
  rw [← inv_eq_one, TauCeti.FormalCoordinate.ext_iff, toPowerSeries_inv_pTypicalCoordinate,
    TauCeti.FormalCoordinate.toPowerSeries_one, ← toPowerSeries_tautologicalCurve F,
    ← Curve.ext_iff, F.pTypicalProjectorCurve_eq_self_iff p hunit F.tautologicalCurve,
    isPTypical_def]

/-- `FormalGroup.pTypicalize` fixes `F` if and only if `F` is already `p`-typical. -/
@[simp]
theorem pTypicalize_eq_self_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalize p hunit = F ↔ F.IsPTypical p := by
  refine ⟨fun h ↦ (isPTypical_congr h).mp (F.isPTypical_pTypicalize p hunit), fun h ↦ ?_⟩
  rw [pTypicalize_def, (F.pTypicalCoordinate_eq_one_iff p hunit).mpr h, one_smul]

/-- The `p`-typicalizing coordinate of an already `p`-typicalization is `1`. -/
@[simp]
theorem pTypicalCoordinate_pTypicalize (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).pTypicalCoordinate p hunit = 1 :=
  ((F.pTypicalize p hunit).pTypicalCoordinate_eq_one_iff p hunit).mpr
    (F.isPTypical_pTypicalize p hunit)

/-- `FormalGroup.pTypicalize` is idempotent. -/
@[simp]
theorem pTypicalize_pTypicalize (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).pTypicalize p hunit = F.pTypicalize p hunit :=
  ((F.pTypicalize p hunit).pTypicalize_eq_self_iff p hunit).mpr (F.isPTypical_pTypicalize p hunit)

/-- The canonical `p`-typicalizing coordinate of `𝔾ₐ` is `1`. -/
@[simp]
theorem pTypicalCoordinate_𝔾ₐ (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (𝔾ₐ (R := R)).pTypicalCoordinate p hunit = 1 :=
  ((𝔾ₐ (R := R)).pTypicalCoordinate_eq_one_iff p hunit).mpr (isPTypical_𝔾ₐ p)

/-- Canonical `p`-typicalization fixes `𝔾ₐ`. -/
@[simp]
theorem pTypicalize_𝔾ₐ (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (𝔾ₐ (R := R)).pTypicalize p hunit = 𝔾ₐ :=
  ((𝔾ₐ (R := R)).pTypicalize_eq_self_iff p hunit).mpr (isPTypical_𝔾ₐ p)

/-- The canonical `p`-typicalizing coordinate of `TauCeti.hazewinkelIntegralFormalGroup` is `1`. -/
@[simp]
theorem _root_.TauCeti.pTypicalCoordinate_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (TauCeti.hazewinkelIntegralFormalGroup p v).pTypicalCoordinate p hunit = 1 :=
  ((TauCeti.hazewinkelIntegralFormalGroup p v).pTypicalCoordinate_eq_one_iff p hunit).mpr
    (TauCeti.isPTypical_hazewinkelIntegralFormalGroup p v)

/-- Canonical `p`-typicalization fixes `TauCeti.hazewinkelIntegralFormalGroup`. -/
@[simp]
theorem _root_.TauCeti.pTypicalize_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (TauCeti.hazewinkelIntegralFormalGroup p v).pTypicalize p hunit =
      TauCeti.hazewinkelIntegralFormalGroup p v :=
  ((TauCeti.hazewinkelIntegralFormalGroup p v).pTypicalize_eq_self_iff p hunit).mpr
    (TauCeti.isPTypical_hazewinkelIntegralFormalGroup p v)

/-- Base change commutes with `FormalGroup.pTypicalCoordinate`. -/
theorem map_pTypicalCoordinate (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.map φ (F.pTypicalCoordinate p hR) =
      (F.map φ).pTypicalCoordinate p (fun q hq hqp ↦ by simpa using (hR q hq hqp).map φ) := by
  apply inv_injective
  rw [← map_inv]
  apply TauCeti.FormalCoordinate.ext
  rw [TauCeti.FormalCoordinate.toPowerSeries_map, toPowerSeries_inv_pTypicalCoordinate,
    toPowerSeries_inv_pTypicalCoordinate, ← Curve.toPowerSeries_map,
    F.map_pTypicalProjectorCurve φ p hR, F.map_tautologicalCurve]

/-- Base change commutes with `FormalGroup.pTypicalize`. -/
theorem map_pTypicalize (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hR).map φ =
      (F.map φ).pTypicalize p (fun q hq hqp ↦ by simpa using (hR q hq hqp).map φ) := by
  rw [pTypicalize_def, pTypicalize_def, map_smul, F.map_pTypicalCoordinate φ p hR]

private theorem toPowerSeries_inv_pTypicalCoordinate_rescale_of_isLeftRegular (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {s : R} (hs : IsLeftRegular s) :
    ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      ((F.pTypicalizeIso p hunit).invHom.rescale s).toPowerSeries := by
  have hreg : IsSMulRegular (PowerSeries R) s := .pi fun _ ↦ hs.isSMulRegular
  refine hreg ?_
  have hLHS : s • ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      PowerSeries.rescale s
        (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries :=
    calc s • ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries
        = ((F.rescaleHom s).mapCurve
            ((F.rescale s).pTypicalProjectorCurve p hunit
              (F.rescale s).tautologicalCurve)).toPowerSeries := by
          rw [toPowerSeries_mapCurve_rescaleHom, toPowerSeries_inv_pTypicalCoordinate]
      _ = (F.pTypicalProjectorCurve p hunit
            ((F.rescaleHom s).mapCurve (F.rescale s).tautologicalCurve)).toPowerSeries := by
          rw [(F.rescaleHom s).mapCurve_pTypicalProjectorCurve]
      _ = (F.rescaleCurve s
            (F.pTypicalProjectorCurve p hunit F.tautologicalCurve)).toPowerSeries := by
          rw [mapCurve_rescaleHom_tautologicalCurve, F.pTypicalProjectorCurve_rescaleCurve]
      _ = PowerSeries.rescale s
            (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries :=
          F.toPowerSeries_rescaleCurve s _
  have hRHS : s • ((F.pTypicalizeIso p hunit).invHom.rescale s).toPowerSeries =
      PowerSeries.rescale s
        (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
    simpa only [pTypicalizeIso_invHom_toPowerSeries] using
      (F.pTypicalizeIso p hunit).invHom.smul_rescale s
  exact hLHS.trans hRHS.symm

private theorem toPowerSeries_pTypicalCoordinate_rescale_of_isLeftRegular (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {s : R} (hs : IsLeftRegular s) :
    ((F.rescale s).pTypicalCoordinate p hunit).toPowerSeries =
      ((F.pTypicalizeIso p hunit).toHom.rescale s).toPowerSeries := by
  set φ_s : TauCeti.FormalCoordinate R :=
    { toPowerSeries := ((F.pTypicalizeIso p hunit).toHom.rescale s).toPowerSeries
      constantCoeff_toPowerSeries := ((F.pTypicalizeIso p hunit).toHom.rescale s).zero_constantCoeff
      isUnit_coeff_one := by
        rw [TauCeti.FormalGroupHom.coeff_rescale, Nat.sub_self, pow_zero, one_mul,
          pTypicalizeIso_toHom_toPowerSeries, coeff_one_pTypicalCoordinate]
        exact isUnit_one }
  set ψ_s : TauCeti.FormalCoordinate R :=
    { toPowerSeries := ((F.pTypicalizeIso p hunit).invHom.rescale s).toPowerSeries
      constantCoeff_toPowerSeries :=
        ((F.pTypicalizeIso p hunit).invHom.rescale s).zero_constantCoeff
      isUnit_coeff_one := by
        rw [TauCeti.FormalGroupHom.coeff_rescale, Nat.sub_self, pow_zero, one_mul,
          pTypicalizeIso_invHom_toPowerSeries, coeff_one_pTypicalProjectorCurve,
          toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X]
        exact isUnit_one }
  have hmul : φ_s * ψ_s = 1 := by
    apply TauCeti.FormalCoordinate.ext
    have hcomp := congrArg TauCeti.FormalGroupHom.toPowerSeries
      (TauCeti.FormalGroupHom.rescale_comp (F.pTypicalizeIso p hunit).toHom
        (F.pTypicalizeIso p hunit).invHom s).symm
    rw [TauCeti.FormalGroupIso.toHom_comp_invHom, TauCeti.FormalGroupHom.rescale_id,
      TauCeti.FormalGroupHom.id_toPowerSeries, TauCeti.FormalGroupHom.comp_toPowerSeries] at hcomp
    exact hcomp.trans TauCeti.FormalCoordinate.toPowerSeries_one.symm
  have hinv_eq : ((F.rescale s).pTypicalCoordinate p hunit)⁻¹ = ψ_s :=
    TauCeti.FormalCoordinate.ext
      (F.toPowerSeries_inv_pTypicalCoordinate_rescale_of_isLeftRegular p hunit hs)
  exact congrArg TauCeti.FormalCoordinate.toPowerSeries
    (inv_injective (hinv_eq.trans (inv_eq_of_mul_eq_one_right hmul).symm))

private theorem isUnit_polynomial_natCast_of_isUnit {B : Type*} [CommRing B] {p : ℕ}
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : B)) :
    ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : Polynomial B) :=
  fun q hq hqp ↦ by simpa only [map_natCast] using (hunit q hq hqp).map Polynomial.C

/-- Rescaling `F` by any `s : R` rescales the canonical `p`-typicalizing isomorphism by `s`. -/
theorem toPowerSeries_pTypicalCoordinate_rescale (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) :
    ((F.rescale s).pTypicalCoordinate p hunit).toPowerSeries =
      ((F.pTypicalizeIso p hunit).toHom.rescale s).toPowerSeries := by
  let hPoly := isUnit_polynomial_natCast_of_isUnit hunit
  have hgen := toPowerSeries_pTypicalCoordinate_rescale_of_isLeftRegular (F.map Polynomial.C) p
    hPoly Polynomial.isRegular_X.left
  have heval := congrArg (PowerSeries.map (Polynomial.evalRingHom s)) hgen
  have hLHS : PowerSeries.map (Polynomial.evalRingHom s)
      (((F.map Polynomial.C).rescale Polynomial.X).pTypicalCoordinate p hPoly).toPowerSeries =
      ((F.rescale s).pTypicalCoordinate p hunit).toPowerSeries := by
    rw [← TauCeti.FormalCoordinate.toPowerSeries_map,
      map_pTypicalCoordinate ((F.map Polynomial.C).rescale Polynomial.X)
        (Polynomial.evalRingHom s) p hPoly]
    exact congrArg TauCeti.FormalCoordinate.toPowerSeries
      (pTypicalCoordinate_congr (map_evalRingHom_rescale_X F s) p hunit)
  have hRHS : PowerSeries.map (Polynomial.evalRingHom s)
      (((F.map Polynomial.C).pTypicalizeIso p hPoly).toHom.rescale Polynomial.X).toPowerSeries =
      ((F.pTypicalizeIso p hunit).toHom.rescale s).toPowerSeries := by
    ext n
    rw [PowerSeries.coeff_map, TauCeti.FormalGroupHom.coeff_rescale,
      TauCeti.FormalGroupHom.coeff_rescale, pTypicalizeIso_toHom_toPowerSeries,
      pTypicalizeIso_toHom_toPowerSeries, ← F.map_pTypicalCoordinate Polynomial.C p hunit,
      TauCeti.FormalCoordinate.toPowerSeries_map, map_mul, map_pow, PowerSeries.coeff_map,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C]
  exact hLHS.symm.trans (heval.trans hRHS)

/-- Degree-`n` coefficients of `FormalGroup.pTypicalCoordinate` scale by `s ^ (n - 1)` under
`FormalGroup.rescale F s`. -/
@[simp]
theorem coeff_pTypicalCoordinate_rescale (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) (n : ℕ) :
    PowerSeries.coeff n ((F.rescale s).pTypicalCoordinate p hunit).toPowerSeries =
      s ^ (n - 1) * PowerSeries.coeff n (F.pTypicalCoordinate p hunit).toPowerSeries := by
  rw [F.toPowerSeries_pTypicalCoordinate_rescale p hunit s, TauCeti.FormalGroupHom.coeff_rescale,
    pTypicalizeIso_toHom_toPowerSeries]

/-- Canonical `p`-typicalization commutes with rescaling by any element `s : R` (unit or not). -/
theorem pTypicalize_rescale (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) :
    (F.rescale s).pTypicalize p hunit = (F.pTypicalize p hunit).rescale s := by
  rw [pTypicalize_def]
  exact ((F.pTypicalizeIso p hunit).toHom.rescale s).smul_eq
    (F.toPowerSeries_pTypicalCoordinate_rescale p hunit s).symm

section Graded

open TauCeti.GradedAlgebra

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- If `F` is a graded commutative formal group law of weight `w`, then the `n`-th coefficient of
`FormalGroup.pTypicalCoordinate F p hunit` is homogeneous of degree `w * (n - 1)`. -/
theorem coeff_pTypicalCoordinate_mem (F : FormalGroup A) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : A)) {w : ℕ}
    (hF : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈ 𝒜 (w * (d.degree - 1)))
    (n : ℕ) :
    PowerSeries.coeff n (F.pTypicalCoordinate p hunit).toPowerSeries ∈ 𝒜 (w * (n - 1)) := by
  let hPoly := isUnit_polynomial_natCast_of_isUnit hunit
  have hEq : F.map (toPolynomial 𝒜) = (F.map Polynomial.C).rescale (Polynomial.X ^ w) :=
    (map_toPolynomial_eq_rescale_iff F w).mpr hF
  have hcoord : TauCeti.FormalCoordinate.map (toPolynomial 𝒜) (F.pTypicalCoordinate p hunit) =
      ((F.map Polynomial.C).rescale (Polynomial.X ^ w)).pTypicalCoordinate p hPoly := by
    rw [F.map_pTypicalCoordinate (toPolynomial 𝒜) p hunit]
    exact pTypicalCoordinate_congr hEq p hPoly
  have hn := congrArg (fun φ : TauCeti.FormalCoordinate (Polynomial A) ↦
    PowerSeries.coeff n φ.toPowerSeries) hcoord
  rw [TauCeti.FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map,
    coeff_pTypicalCoordinate_rescale, ← F.map_pTypicalCoordinate Polynomial.C p hunit,
    TauCeti.FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map, ← pow_mul, mul_comm,
    Polynomial.C_mul_X_pow_eq_monomial] at hn
  exact toPolynomial_eq_monomial_iff.mp hn

/-- Canonical `p`-typicalization preserves the grading of a graded commutative formal group law. -/
theorem coeff_pTypicalize_mem (F : FormalGroup A) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : A)) {w : ℕ}
    (hF : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈ 𝒜 (w * (d.degree - 1)))
    (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (F.pTypicalize p hunit).toPowerSeries ∈ 𝒜 (w * (d.degree - 1)) :=
  F.coeff_smul_mem w (F.pTypicalCoordinate p hunit)
    ((TauCeti.FormalCoordinate.mem_gradedSubgroup 𝒜 w _).mpr
      (F.coeff_pTypicalCoordinate_mem p hunit hF))
    hF d

end Graded

/-! ### Rational logarithm of the canonical `p`-typicalization -/

/-- Over a `ℚ`-algebra, the logarithm of `F.pTypicalize p hunit` is obtained by substituting
Cartier's `p`-typicalization of the tautological curve into `log_F`. -/
theorem log_pTypicalize_eq_subst [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalize p hunit).log =
      PowerSeries.subst (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
        F.log := by
  rw [pTypicalize_def, log_smul, F.linearCoeff_pTypicalCoordinate, Units.val_one, one_smul,
    toPowerSeries_inv_pTypicalCoordinate]

open Classical in
/-- Over a `ℚ`-algebra, when `p` is prime, the logarithm of `F.pTypicalize p hunit` retains the
coefficients of `log_F` in degrees `p^m` and zeroes out all other degrees. -/
theorem coeff_log_pTypicalize [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalize p hunit).log =
      if ∀ m : ℕ, p ^ m ≠ k then 0 else PowerSeries.coeff k F.log := by
  rw [F.log_pTypicalize_eq_subst p hunit,
    F.coeff_subst_pTypicalProjectorCurve_log hp hunit k F.tautologicalCurve,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, when `p` is prime, `pTypicalize` preserves the `p^m`-th logarithm
coefficients of `F`. -/
@[simp]
theorem coeff_pow_log_pTypicalize [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (m : ℕ) :
    PowerSeries.coeff (p ^ m) (F.pTypicalize p hunit).log = PowerSeries.coeff (p ^ m) F.log := by
  classical
  rw [F.coeff_log_pTypicalize hp hunit (p ^ m),
    ite_eq_right (not_forall.mpr ⟨m, not_not.mpr rfl⟩)]

/-- Over a `ℚ`-algebra, when `p` is prime, `F.pTypicalize p hunit` equals
`TauCeti.hazewinkelFormalGroup p v` for a unique family `v`. -/
theorem existsUnique_pTypicalize_eq_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃! v : ℕ+ → R, F.pTypicalize p hunit = TauCeti.hazewinkelFormalGroup p v :=
  (F.isPTypical_pTypicalize p hunit).existsUnique_eq_hazewinkelFormalGroup hp

end PTypicalize

end FormalGroup
