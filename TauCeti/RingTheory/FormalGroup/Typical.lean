/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Typical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral

/-!
# `p`-typical formal group laws and canonical `p`-typicalization

Let `F(X, Y)` be a one-dimensional commutative formal group law over a commutative ring `R`, and
fix a natural number `p` (in applications a prime). Following Cartier (1967) and Quillen (1969), `F`
is **`p`-typical** (`FormalGroup.IsPTypical`) if its tautological curve `T` is `p`-typical, i.e.,
Cartier's Frobenius operator `f_q` kills `T` for every prime `q ≠ p`. Transporting `F` along a
formal coordinate `c` yields a `p`-typical formal group law precisely when the inverse coordinate
`c⁻¹` defines a `p`-typical curve on `F` (`FormalGroup.isPTypical_smul_iff`).

Over any commutative ring (including rings with `p`-torsion and prime characteristic), the additive
formal group law `𝔾ₐ` and Hazewinkel's integral formal group law
`TauCeti.hazewinkelIntegralFormalGroup p v` are `p`-typical. Over a `ℚ`-algebra and for `p` prime,
`F` is `p`-typical if and only if its logarithm has no terms outside the degrees `p^n`, so the
`p`-typical formal group laws are precisely the laws `TauCeti.hazewinkelFormalGroup p v`, each for a
unique generator family `v` (`FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup` and
`FormalGroup.IsPTypical.existsUnique_eq_hazewinkelFormalGroup`).

When every prime `q ≠ p` is invertible in `R`, applying Cartier's curve projector
`FormalGroup.pTypicalProjectorCurve` to `F.tautologicalCurve` produces a `p`-typical curve with
linear coefficient `1`. Its compositional inverse `FormalGroup.pTypicalCoordinate` is Cartier and
Quillen's canonical strict coordinate transporting `F` via the strict isomorphism
`FormalGroup.pTypicalIso` to the `p`-typical formal group law `FormalGroup.pTypicalFormalGroup`.
Canonical `p`-typicalization fixes `p`-typical formal group laws, is idempotent, and commutes with
base change; over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup` is obtained from `F.log`
by deleting all degrees divisible by a prime `q ≠ p` and keeping the `p^n`-th coefficients unchanged
(`FormalGroup.coeff_log_pTypicalFormalGroup` and `FormalGroup.coeff_pow_log_pTypicalFormalGroup`).

## Main definitions

* `FormalGroup.IsPTypical`: predicate that a commutative formal group law has `p`-typical
  tautological curve.
* `FormalGroup.pTypicalCoordinate`: Cartier–Quillen's canonical strict formal coordinate whose
  inverse is the `p`-typical projection of `F.tautologicalCurve`.
* `FormalGroup.pTypicalFormalGroup`: canonical `p`-typicalization `F.pTypicalCoordinate p hunit • F`
  when every prime `q ≠ p` is invertible in `R`.
* `FormalGroup.pTypicalIso`: canonical strict isomorphism `F ≅ F.pTypicalFormalGroup`.

## Main results

* `FormalGroup.isPTypical_smul_iff`: `(c • F).IsPTypical p` holds if and only if `c⁻¹` is a
  `p`-typical curve on `F`.
* `FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup` and
  `TauCeti.isPTypical_hazewinkelIntegralFormalGroup`: rational classification by Hazewinkel's laws
  and unconditional `p`-typicality of Hazewinkel's integral law over any commutative ring.
* `FormalGroup.isPTypical_pTypicalFormalGroup`, `FormalGroup.pTypicalFormalGroup_eq_self_iff`, and
  `FormalGroup.pTypicalFormalGroup_pTypicalFormalGroup`: `p`-typicality, fixed-point
  characterization, and idempotence of canonical `p`-typicalization.
* `FormalGroup.coeff_log_pTypicalFormalGroup` and `FormalGroup.coeff_pow_log_pTypicalFormalGroup`:
  Quillen's logarithm formula for `F.pTypicalFormalGroup`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.20–A2.1.26.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws and Hazewinkel comparison -/

section IsPTypicalLaw

/-- A commutative formal group law `F` is **`p`-typical** if its tautological curve `T` is
`p`-typical, i.e. `f_q T = 0` for every prime `q ≠ p`. -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve.IsPTypical p

/-- Unfold `FormalGroup.IsPTypical`. -/
theorem isPTypical_def (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔ F.tautologicalCurve.IsPTypical p :=
  ⟨id, id⟩

/-- Equal commutative formal group laws have equivalent `p`-typicality predicates. -/
theorem isPTypical_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) (p : ℕ) :
    F.IsPTypical p ↔ G.IsPTypical p := by
  subst h
  rfl

/-- The tautological curve of a `p`-typical formal group law is `p`-typical. -/
theorem IsPTypical.tautologicalCurve {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) : F.tautologicalCurve.IsPTypical p :=
  hF

/-- Base change along a ring homomorphism preserves `p`-typicality of formal group laws. -/
theorem IsPTypical.map {F : FormalGroup R} [F.IsComm] {p : ℕ} (hF : F.IsPTypical p)
    (φ : R →+* S) : (F.map φ).IsPTypical p := by
  rw [isPTypical_def, ← F.map_tautologicalCurve φ]
  exact Curve.IsPTypical.map hF φ

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typicality of
formal group laws. -/
theorem isPTypical_map_iff {F : FormalGroup R} [F.IsComm] {φ : R →+* S}
    (hφ : Function.Injective φ) (p : ℕ) :
    (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [isPTypical_def, isPTypical_def, ← F.map_tautologicalCurve φ, Curve.isPTypical_map_iff hφ]

/-- Transporting `F` along a formal coordinate `c` produces a `p`-typical formal group law if and
only if the inverse coordinate `c⁻¹` is a `p`-typical curve on `F`. -/
theorem isPTypical_smul_iff (F : FormalGroup R) [F.IsComm] (c : TauCeti.FormalCoordinate R)
    (p : ℕ) :
    (c • F).IsPTypical p ↔
      (⟨c⁻¹.toPowerSeries, c⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve).IsPTypical p := by
  have htaut : (smulIso c F).curveEquiv ⟨c⁻¹.toPowerSeries, c⁻¹.constantCoeff_toPowerSeries⟩ =
      (c • F).tautologicalCurve := by
    ext1
    rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
      smulIso_toHom_toPowerSeries, ← TauCeti.FormalCoordinate.toPowerSeries_mul, mul_inv_cancel,
      TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]
  rw [isPTypical_def, ← htaut, Curve.isPTypical_curveEquiv_iff]

/-- The additive formal group law `𝔾ₐ` is `p`-typical over every commutative ring and for every
`p : ℕ`. -/
@[simp]
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ (R := R)).IsPTypical p := by
  refine Curve.isPTypical_𝔾ₐ_of_coeff_eq_zero p fun q hq _ k _ hqk ↦ ?_
  rw [toPowerSeries_tautologicalCurve, PowerSeries.coeff_X]
  exact ite_eq_right fun hk1 : k = 1 ↦ hq.not_dvd_one (hk1 ▸ hqk)

/-- Over a `ℚ`-algebra, a commutative formal group law `F` is `p`-typical if and only if `F.log`
has zero coefficient in every nonzero degree divisible by a prime `q ≠ p`. -/
theorem isPTypical_iff_coeff_log_eq_zero [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ q : ℕ, q.Prime → q ≠ p → ∀ k : ℕ, k ≠ 0 → q ∣ k → PowerSeries.coeff k F.log = 0 := by
  rw [isPTypical_def, Curve.isPTypical_iff_coeff_subst_log_eq_zero,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra and for `p` prime, a commutative formal group law `F` is `p`-typical if and
only if its logarithm has no terms outside the degrees `p^n`. -/
theorem isPTypical_iff_coeff_log_eq_zero_of_prime [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ k : ℕ, (∀ n : ℕ, p ^ n ≠ k) → PowerSeries.coeff k F.log = 0 := by
  rw [isPTypical_def, Curve.isPTypical_iff_coeff_subst_log_eq_zero_of_prime hp,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, Hazewinkel's formal group law `TauCeti.hazewinkelFormalGroup p v` is
`p`-typical for every prime `p` and generator family `v`. -/
@[simp]
theorem _root_.TauCeti.isPTypical_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (v : ℕ+ → R) : (TauCeti.hazewinkelFormalGroup p v).IsPTypical p := by
  rw [isPTypical_iff_coeff_log_eq_zero_of_prime _ hp, TauCeti.log_hazewinkelFormalGroup]
  exact fun _ hk ↦ TauCeti.coeff_hazewinkelLog_eq_zero v hk

/-- **Classification of `p`-typical formal group laws over `ℚ`-algebras**: for `p` prime, a
commutative formal group law over a `ℚ`-algebra is `p`-typical if and only if it is Hazewinkel's
formal group law of some generator family `v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∃ v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  ⟨fun hF ↦ (TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt
      ((isPTypical_iff_coeff_log_eq_zero_of_prime F hp).mp hF)).exists,
    fun ⟨v, hv⟩ ↦ (isPTypical_congr hv p).mpr (TauCeti.isPTypical_hazewinkelFormalGroup hp v)⟩

/-- Every `p`-typical formal group law over a `ℚ`-algebra (with `p` prime) arises from a unique
family of Hazewinkel generators. -/
theorem IsPTypical.existsUnique_eq_hazewinkelFormalGroup [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {p : ℕ} (hp : p.Prime) (hF : F.IsPTypical p) :
    ∃! v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt
    ((isPTypical_iff_coeff_log_eq_zero_of_prime F hp).mp hF)

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem _root_.TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup (p : ℕ)
    [hp : Fact p.Prime] :
    (TauCeti.universalHazewinkelIntegralFormalGroup p).IsPTypical p := by
  rw [← isPTypical_map_iff (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective) p]
  exact (isPTypical_congr (TauCeti.map_intCast_universalHazewinkelIntegralFormalGroup p) p).mpr
    (TauCeti.isPTypical_hazewinkelFormalGroup hp.out MvPolynomial.X)

/-- Hazewinkel's integral formal group law `TauCeti.hazewinkelIntegralFormalGroup p v` is
`p`-typical over any commutative ring `R` (including rings with torsion and prime
characteristic). -/
@[simp]
theorem _root_.TauCeti.isPTypical_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) : (TauCeti.hazewinkelIntegralFormalGroup p v).IsPTypical p :=
  (isPTypical_congr (TauCeti.hazewinkelIntegralFormalGroup_def p v) p).mpr
    ((TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup p).map _)

end IsPTypicalLaw

/-! ### Cartier–Quillen canonical strict `p`-typicalization -/

section CanonicalTypicalization

variable (F : FormalGroup R) [F.IsComm]

/-- The strict formal coordinate whose power series is the Cartier `p`-typicalization of the
tautological curve `T`. -/
private noncomputable def pTypicalCurveCoord (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R where
  toPowerSeries := (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries :=
    (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries
  isUnit_coeff_one := by
    rw [F.coeff_one_pTypicalProjectorCurve p hunit, toPowerSeries_tautologicalCurve,
      PowerSeries.coeff_one_X]
    exact isUnit_one

/-- **Cartier–Quillen's canonical `p`-typicalization coordinate**: the strict formal coordinate
whose inverse is the `p`-typical projection of `F.tautologicalCurve`, transporting `F` to a
`p`-typical formal group law. -/
noncomputable def pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R :=
  (pTypicalCurveCoord F p hunit)⁻¹

/-- The inverse of `F.pTypicalCoordinate` has underlying series equal to the `p`-typical projection
of the tautological curve `T`. -/
theorem inv_pTypicalCoordinate_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalCoordinate, inv_inv]
  rfl

/-- `F.pTypicalCoordinate` is a strict formal coordinate: its linear coefficient is `1`. -/
@[simp]
theorem linearCoeff_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit) = 1 := by
  rw [pTypicalCoordinate, map_inv, inv_eq_one]
  ext
  simp [pTypicalCurveCoord]

/-- The linear power-series coefficient of `F.pTypicalCoordinate` is `1`. -/
@[simp]
theorem coeff_one_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff 1 (F.pTypicalCoordinate p hunit).toPowerSeries = 1 := by
  rw [← TauCeti.FormalCoordinate.val_linearCoeff, linearCoeff_pTypicalCoordinate, Units.val_one]

/-- Base change commutes with `F.pTypicalCoordinate`. -/
theorem map_pTypicalCoordinate (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.map φ (F.pTypicalCoordinate p hR) =
      (F.map φ).pTypicalCoordinate p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ) := by
  rw [pTypicalCoordinate, pTypicalCoordinate, map_inv]
  congr 1
  ext1
  simp only [TauCeti.FormalCoordinate.toPowerSeries_map, pTypicalCurveCoord]
  rw [← Curve.toPowerSeries_map, F.map_pTypicalProjectorCurve φ p hR, F.map_tautologicalCurve]

/-- **Cartier–Quillen's canonical `p`-typicalization** of a commutative formal group law `F` over a
ring in which every prime `q ≠ p` is invertible, obtained by transporting `F` along
`F.pTypicalCoordinate`. -/
noncomputable def pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : FormalGroup R :=
  F.pTypicalCoordinate p hunit • F

/-- Unfold `FormalGroup.pTypicalFormalGroup` as coordinate transport along
`F.pTypicalCoordinate`. -/
theorem pTypicalFormalGroup_def (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalFormalGroup p hunit = F.pTypicalCoordinate p hunit • F :=
  (rfl)

/-- Canonical `p`-typicalization preserves commutativity of formal group laws. -/
instance (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).IsComm := by
  rw [pTypicalFormalGroup_def]
  infer_instance

/-- **Cartier–Quillen's canonical strict isomorphism** from `F` to its `p`-typicalization
`F.pTypicalFormalGroup`. -/
noncomputable def pTypicalIso (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalGroupIso F (F.pTypicalFormalGroup p hunit) :=
  smulIso (F.pTypicalCoordinate p hunit) F

/-- `F.pTypicalIso` is a strict isomorphism of formal group laws. -/
instance (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).IsStrict :=
  (isStrict_smulIso_iff (F.pTypicalCoordinate p hunit) F).mpr
    (F.linearCoeff_pTypicalCoordinate p hunit)

/-- The forward homomorphism of `F.pTypicalIso` has power series `F.pTypicalCoordinate`. -/
@[simp]
theorem pTypicalIso_toHom_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).toHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit).toPowerSeries :=
  smulIso_toHom_toPowerSeries _ _

/-- The inverse homomorphism of `F.pTypicalIso` has power series given by the `p`-typical
projection of `F.tautologicalCurve`. -/
@[simp]
theorem pTypicalIso_invHom_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).invHom.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalIso, smulIso_invHom_toPowerSeries, inv_pTypicalCoordinate_toPowerSeries]

/-- `F.pTypicalIso` carries the `p`-typical projection of `F.tautologicalCurve` to the tautological
curve of `F.pTypicalFormalGroup`. -/
theorem pTypicalIso_curveEquiv_pTypicalProjectorCurve_tautologicalCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).curveEquiv (F.pTypicalProjectorCurve p hunit F.tautologicalCurve) =
      (F.pTypicalFormalGroup p hunit).tautologicalCurve := by
  ext1
  rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    pTypicalIso_toHom_toPowerSeries, ← inv_pTypicalCoordinate_toPowerSeries,
    ← TauCeti.FormalCoordinate.toPowerSeries_mul, mul_inv_cancel,
    TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]

/-- Pushing the `p`-typical projection of `F.tautologicalCurve` forward along `F.pTypicalIso.toHom`
yields the tautological curve of `F.pTypicalFormalGroup`. -/
@[simp]
theorem pTypicalIso_toHom_mapCurve_pTypicalProjectorCurve_tautologicalCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).toHom.mapCurve (F.pTypicalProjectorCurve p hunit F.tautologicalCurve) =
      (F.pTypicalFormalGroup p hunit).tautologicalCurve := by
  rw [← TauCeti.FormalGroupIso.curveEquiv_apply,
    pTypicalIso_curveEquiv_pTypicalProjectorCurve_tautologicalCurve]

/-- The canonical `p`-typicalization `F.pTypicalFormalGroup` is a `p`-typical formal group law. -/
@[simp]
theorem isPTypical_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).IsPTypical p := by
  rw [(isPTypical_congr (F.pTypicalFormalGroup_def p hunit) p), isPTypical_smul_iff]
  simpa only [inv_pTypicalCoordinate_toPowerSeries] using
    F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve

/-- When `F` is already `p`-typical, its canonical `p`-typicalization coordinate is the identity
coordinate `1`. -/
theorem pTypicalCoordinate_eq_one_of_isPTypical (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalCoordinate p hunit = 1 := by
  apply inv_injective
  ext1
  rw [inv_one, inv_pTypicalCoordinate_toPowerSeries, F.pTypicalProjectorCurve_eq_self p hunit hF,
    toPowerSeries_tautologicalCurve, TauCeti.FormalCoordinate.toPowerSeries_one]

/-- `F.pTypicalCoordinate` is the identity coordinate if and only if `F` is `p`-typical. -/
@[simp]
theorem pTypicalCoordinate_eq_one_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = 1 ↔ F.IsPTypical p := by
  refine ⟨fun h ↦ ?_, F.pTypicalCoordinate_eq_one_of_isPTypical p hunit⟩
  have h1 : F.pTypicalFormalGroup p hunit = F := by
    rw [pTypicalFormalGroup_def, h, one_smul]
  exact (isPTypical_congr h1 p).mp (F.isPTypical_pTypicalFormalGroup p hunit)

/-- When `F` is already `p`-typical, its canonical `p`-typicalization is `F` itself. -/
theorem pTypicalFormalGroup_eq_self_of_isPTypical (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalFormalGroup p hunit = F := by
  rw [pTypicalFormalGroup_def, F.pTypicalCoordinate_eq_one_of_isPTypical p hunit hF, one_smul]

/-- A commutative formal group law is fixed by canonical `p`-typicalization if and only if it is
`p`-typical. -/
@[simp]
theorem pTypicalFormalGroup_eq_self_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalFormalGroup p hunit = F ↔ F.IsPTypical p :=
  ⟨fun h ↦ (isPTypical_congr h p).mp (F.isPTypical_pTypicalFormalGroup p hunit),
    F.pTypicalFormalGroup_eq_self_of_isPTypical p hunit⟩

/-- Canonical `p`-typicalization of formal group laws is idempotent. -/
@[simp]
theorem pTypicalFormalGroup_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).pTypicalFormalGroup p hunit =
      F.pTypicalFormalGroup p hunit :=
  (F.pTypicalFormalGroup p hunit).pTypicalFormalGroup_eq_self_of_isPTypical p hunit
    (F.isPTypical_pTypicalFormalGroup p hunit)

/-- Base change commutes with canonical `p`-typicalization of formal group laws. -/
theorem map_pTypicalFormalGroup (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hR).map φ =
      (F.map φ).pTypicalFormalGroup p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ) := by
  rw [pTypicalFormalGroup_def, pTypicalFormalGroup_def, map_smul, F.map_pTypicalCoordinate φ p hR]

/-- Over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup` is the logarithm of `F` evaluated
at the `p`-typical projection of the tautological curve. -/
theorem log_pTypicalFormalGroup [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).log =
      PowerSeries.subst (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
        F.log := by
  rw [pTypicalFormalGroup_def, log_smul, linearCoeff_pTypicalCoordinate, Units.val_one, one_smul,
    inv_pTypicalCoordinate_toPowerSeries]

open scoped Classical in
/-- **Quillen's logarithm formula**: over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup`
is obtained from `F.log` by deleting every degree divisible by a prime `q ≠ p` and leaving all other
coefficients unchanged. -/
theorem coeff_log_pTypicalFormalGroup [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalFormalGroup p hunit).log =
      if ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k then 0 else PowerSeries.coeff k F.log := by
  rw [F.log_pTypicalFormalGroup p hunit, F.coeff_subst_pTypicalProjectorCurve_log p hunit k,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra and for `p` prime, the logarithm of `F.pTypicalFormalGroup` keeps precisely
the `p^n`-th degree terms of `F.log`. -/
theorem coeff_log_pTypicalFormalGroup_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalFormalGroup p hunit).log =
      if p ^ Nat.log p k = k then PowerSeries.coeff k F.log else 0 := by
  rw [F.log_pTypicalFormalGroup p hunit,
    F.coeff_subst_pTypicalProjectorCurve_log_of_prime hp hunit k,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra and for `p` prime, `F.pTypicalFormalGroup` has the same `p^n`-th logarithm
coefficients as `F`. -/
@[simp]
theorem coeff_pow_log_pTypicalFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    PowerSeries.coeff (p ^ n) (F.pTypicalFormalGroup p hunit).log =
      PowerSeries.coeff (p ^ n) F.log := by
  rw [F.log_pTypicalFormalGroup p hunit, F.coeff_pow_subst_pTypicalProjectorCurve_log hp hunit n,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

end CanonicalTypicalization

end FormalGroup
