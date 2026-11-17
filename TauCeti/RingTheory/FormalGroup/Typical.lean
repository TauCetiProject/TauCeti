/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Typical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral

/-!
# `p`-typical formal group laws and Cartier's canonical coordinate

A commutative formal group law `F(X, Y)` over a commutative ring `R` is **`p`-typical**
(`FormalGroup.IsPTypical`) if its tautological curve `γ(T) = T` is a `p`-typical curve on `F`,
meaning that Cartier's Frobenius operator `f_q` annihilates `T` for every prime `q ≠ p`. For a
formal coordinate `φ`, the transported formal group law `φ⁻¹ • F` is `p`-typical if and only if
`φ`, viewed as a curve on `F` (`TauCeti.FormalCoordinate.toCurve`), is `p`-typical.

Over a `ℚ`-algebra with `p` prime, a commutative formal group law is `p`-typical if and only if
its logarithm `F.log` vanishes outside the degrees `p^n`, and therefore if and only if it is equal
to `TauCeti.hazewinkelFormalGroup p v` for a unique sequence of Hazewinkel parameters `v`. By
injective base change from `ℤ[v₁, v₂, …]` to `ℚ[v₁, v₂, …]` followed by specialization, Hazewinkel's
integral formal group laws `TauCeti.universalHazewinkelIntegralFormalGroup p` and
`TauCeti.hazewinkelIntegralFormalGroup p v` are `p`-typical over every commutative ring `R`,
including rings of characteristic `p` and rings with torsion.

When every prime `q ≠ p` is invertible in `R` (for example over `ℤ_(p)`-algebras, `ℚ`-algebras, or
rings of prime characteristic `p`), applying Cartier's `p`-typicalization projector
`FormalGroup.pTypicalProjectorCurve` to `F.tautologicalCurve` produces a strict formal coordinate
`FormalGroup.pTypicalCoordinate F p hunit`. Transporting `F` along its inverse yields the canonical
`p`-typical formal group law `FormalGroup.pTypicalFormalGroup F p hunit` together with the canonical
strict isomorphism `FormalGroup.pTypicalIso F p hunit : F ≅ F.pTypicalFormalGroup p hunit`. When `F`
is already `p`-typical this coordinate is `1` and `F.pTypicalFormalGroup p hunit = F`. Over a
`ℚ`-algebra with `p` prime, the logarithm of `F.pTypicalFormalGroup p hunit` is obtained from
`F.log` by retaining precisely the terms of degree `p^n`.

## Main definitions

* `FormalGroup.IsPTypical`: the predicate that a commutative formal group law `F` has `p`-typical
  tautological curve.
* `FormalGroup.pTypicalCoordinate`: Cartier's strict formal coordinate `(ε_p T)(X)`.
* `FormalGroup.pTypicalFormalGroup`: the canonical `p`-typical formal group law
  `(F.pTypicalCoordinate p hunit)⁻¹ • F`.
* `FormalGroup.pTypicalIso`: the canonical strict isomorphism from `F` to
  `F.pTypicalFormalGroup p hunit`.

## Main results

* `FormalGroup.isPTypical_inv_smul_iff` and `FormalGroup.isPTypical_smul_iff`: `φ⁻¹ • F` is
  `p`-typical if and only if `φ` is a `p`-typical curve on `F`.
* `FormalGroup.isPTypical_iff_forall_coeff_log_eq_zero` and
  `FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup`: over a `ℚ`-algebra with `p` prime,
  `p`-typical commutative formal group laws are those whose logarithm is supported in degrees `p^n`,
  and are classified by Hazewinkel's formal group laws.
* `TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup` and
  `TauCeti.isPTypical_hazewinkelIntegralFormalGroup`: Hazewinkel's integral polynomial law and
  all of its specializations are `p`-typical over arbitrary commutative rings.
* `FormalGroup.isPTypical_pTypicalFormalGroup`, `FormalGroup.pTypicalFormalGroup_eq_self_iff`, and
  `FormalGroup.coeff_log_pTypicalFormalGroup`: Cartier's canonical coordinate change produces a
  `p`-typical formal group law, fixes `p`-typical laws, and over `ℚ`-algebras extracts the `p`-power
  part of the formal logarithm.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.3–16.4.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.21–A2.1.23.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws -/

/-- A commutative formal group law `F` is **`p`-typical** if its tautological curve `T` is a
`p`-typical curve on `F`, i.e., `f_q T = 0` for every prime `q ≠ p`. -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve.IsPTypical p

/-- Unfolding characterization of `p`-typical formal group laws in terms of `tautologicalCurve`. -/
theorem isPTypical_def (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔ F.tautologicalCurve.IsPTypical p :=
  Iff.rfl

/-- A commutative formal group law `F` is `p`-typical if and only if `f_q T = 0` for every prime
`q ≠ p`. -/
theorem isPTypical_iff_forall_prime_ne (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 :=
  Curve.isPTypical_def

/-- Equal commutative formal group laws have the same `p`-typicality predicate, regardless of how
their `IsComm` instances are synthesized. -/
theorem isPTypical_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) {p : ℕ} :
    F.IsPTypical p ↔ G.IsPTypical p := by
  subst h
  rfl

/-- On a `p`-typical formal group law, `f_n T = 0` for every nonzero `n` not of the form `p^k`. -/
theorem IsPTypical.frobeniusCurve_tautologicalCurve_eq_zero {F : FormalGroup R} [F.IsComm]
    {p n : ℕ} (hF : F.IsPTypical p) (hn : n ≠ 0) (hnp : ∀ k, p ^ k ≠ n) :
    F.frobeniusCurve n hn F.tautologicalCurve = 0 :=
  Curve.IsPTypical.frobeniusCurve_eq_zero hF hn hnp

/-- A commutative formal group law is `p`-typical if and only if `f_n T = 0` for every nonzero `n`
that is not a power of `p`. -/
theorem isPTypical_iff_forall_frobeniusCurve_tautologicalCurve_eq_zero (F : FormalGroup R)
    [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ ⦃n : ℕ⦄ (hn : n ≠ 0), (∀ k, p ^ k ≠ n) →
        F.frobeniusCurve n hn F.tautologicalCurve = 0 :=
  Curve.isPTypical_iff_forall_frobeniusCurve_eq_zero

/-- The additive formal group law `𝔾ₐ` is `p`-typical for every `p`. -/
@[simp]
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ : FormalGroup R).IsPTypical p := by
  rw [isPTypical_iff_forall_prime_ne]
  intro q hq _
  ext k
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_tautologicalCurve, Curve.toPowerSeries_zero,
    map_zero, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, PowerSeries.coeff_X,
    ite_eq_right (fun h ↦ hq.ne_one (Nat.eq_one_of_mul_eq_one_right h)), smul_zero]

/-- Base change preserves `p`-typicality of formal group laws. -/
theorem IsPTypical.map {F : FormalGroup R} [F.IsComm] (φ : R →+* S) {p : ℕ}
    (hF : F.IsPTypical p) :
    (F.map φ).IsPTypical p := by
  rw [IsPTypical, ← F.map_tautologicalCurve φ]
  exact Curve.IsPTypical.map φ hF

/-- Along an injective ring homomorphism, base change reflects and preserves `p`-typicality of
formal group laws. -/
theorem isPTypical_map_iff_of_injective {F : FormalGroup R} [F.IsComm] {φ : R →+* S}
    (hφ : Function.Injective φ) {p : ℕ} :
    (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [IsPTypical, IsPTypical, ← F.map_tautologicalCurve φ,
    Curve.isPTypical_map_iff_of_injective hφ]

/-- Transporting `F` along `φ` produces a `p`-typical formal group law if and only if `φ⁻¹` is a
`p`-typical curve on `F`. -/
theorem isPTypical_smul_iff (φ : TauCeti.FormalCoordinate R) (F : FormalGroup R) [F.IsComm]
    (p : ℕ) :
    (φ • F).IsPTypical p ↔ (φ⁻¹.toCurve F).IsPTypical p := by
  rw [IsPTypical, ← (smulIso φ F).isPTypical_invHom_mapCurve_iff,
    smulIso_invHom_mapCurve_tautologicalCurve]

/-- Transporting `F` along `φ⁻¹` produces a `p`-typical formal group law if and only if `φ` is a
`p`-typical curve on `F`. -/
theorem isPTypical_inv_smul_iff (φ : TauCeti.FormalCoordinate R) (F : FormalGroup R) [F.IsComm]
    (p : ℕ) :
    (φ⁻¹ • F).IsPTypical p ↔ (φ.toCurve F).IsPTypical p := by
  rw [isPTypical_smul_iff, inv_inv]

/-! ### Logarithmic characterization and Hazewinkel's formal group laws -/

/-- Over a `ℚ`-algebra, the logarithm of a `p`-typical formal group law vanishes outside degrees of
the form `p^n`. -/
theorem IsPTypical.coeff_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k F.log = 0 := by
  simpa [PowerSeries.X_subst] using Curve.IsPTypical.coeff_subst_log_eq_zero hF hk

/-- Over a `ℚ`-algebra, for `p` prime, a commutative formal group law is `p`-typical if and only if
its logarithm has no nonzero terms outside the degrees `p^n`. -/
theorem isPTypical_iff_forall_coeff_log_eq_zero [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ k, (∀ n, p ^ n ≠ k) → PowerSeries.coeff k F.log = 0 := by
  simpa [IsPTypical, PowerSeries.X_subst] using
    Curve.isPTypical_iff_forall_coeff_subst_log_eq_zero (γ := F.tautologicalCurve) hp

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Over a `ℚ`-algebra, for `p` prime, Hazewinkel's formal group law is `p`-typical. -/
@[simp]
theorem isPTypical_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime) (v : ℕ+ → R) :
    (hazewinkelFormalGroup p v).IsPTypical p := by
  rw [FormalGroup.isPTypical_iff_forall_coeff_log_eq_zero _ hp]
  intro k hk
  rw [log_hazewinkelFormalGroup, coeff_hazewinkelLog_eq_zero v hk]

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem isPTypical_universalHazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime] :
    (universalHazewinkelIntegralFormalGroup p).IsPTypical p := by
  rw [← FormalGroup.isPTypical_map_iff_of_injective
      (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective),
    FormalGroup.isPTypical_congr (map_intCast_universalHazewinkelIntegralFormalGroup p)]
  exact isPTypical_hazewinkelFormalGroup Fact.out MvPolynomial.X

/-- Every specialization of Hazewinkel's integral formal group law over an arbitrary commutative
ring is `p`-typical. -/
@[simp]
theorem isPTypical_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime] (v : ℕ+ → R) :
    (hazewinkelIntegralFormalGroup p v).IsPTypical p := by
  rw [FormalGroup.isPTypical_congr (hazewinkelIntegralFormalGroup_def p v)]
  exact (isPTypical_universalHazewinkelIntegralFormalGroup p).map _

end TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Over a `ℚ`-algebra, for `p` prime, every `p`-typical commutative formal group law is
Hazewinkel's formal group law for a unique family of generators `v`. -/
theorem IsPTypical.existsUnique_eq_hazewinkelFormalGroup [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {p : ℕ} (hp : p.Prime) (hF : F.IsPTypical p) :
    ∃! v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt fun _ hk ↦ hF.coeff_log_eq_zero hk

/-- Over a `ℚ`-algebra, for `p` prime, a commutative formal group law is `p`-typical if and only if
it is of the form `TauCeti.hazewinkelFormalGroup p v` for some `v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∃ v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  ⟨fun hF ↦ (hF.existsUnique_eq_hazewinkelFormalGroup hp).exists,
    fun ⟨v, hv⟩ ↦ hv ▸ TauCeti.isPTypical_hazewinkelFormalGroup hp v⟩

/-! ### Cartier's canonical `p`-typicalization of a commutative formal group law -/

section CanonicalCoordinate

variable (F : FormalGroup R) [F.IsComm]

/-- **Cartier's `p`-typical coordinate** `(ε_p T)(X)` on a commutative formal group law `F` over a
ring in which every prime `q ≠ p` is invertible. It is a strict formal coordinate whose inverse
transports `F` to `F.pTypicalFormalGroup p hunit`. -/
noncomputable def pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R where
  toPowerSeries := (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries :=
    (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries
  isUnit_coeff_one := by simp

/-- The power series of Cartier's `p`-typical coordinate is the `p`-typical projection of `T`. -/
@[simp]
theorem toPowerSeries_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit).toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries :=
  (rfl)

/-- Viewing `F.pTypicalCoordinate p hunit` as a curve on `F` recovers the `p`-typical projection of
`F.tautologicalCurve`. -/
@[simp]
theorem toCurve_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit).toCurve F =
      F.pTypicalProjectorCurve p hunit F.tautologicalCurve :=
  Curve.ext (by simp)

/-- Cartier's `p`-typical coordinate has linear coefficient `1`. -/
theorem coeff_one_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff 1 (F.pTypicalCoordinate p hunit).toPowerSeries = 1 := by
  simp

/-- Cartier's `p`-typical coordinate has unit linear coefficient `1`. -/
@[simp]
theorem linearCoeff_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit) = 1 :=
  Units.ext (by simp)

/-- Viewed as a curve on `F`, Cartier's `p`-typical coordinate is `p`-typical. -/
theorem isPTypical_toCurve_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    ((F.pTypicalCoordinate p hunit).toCurve F).IsPTypical p := by
  rw [toCurve_pTypicalCoordinate]
  exact F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve

/-- On a `p`-typical formal group law, Cartier's `p`-typical coordinate is the identity coordinate
`1`. -/
theorem pTypicalCoordinate_eq_one (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalCoordinate p hunit = 1 := by
  ext1
  rw [toPowerSeries_pTypicalCoordinate, F.pTypicalProjectorCurve_eq_self p hunit hF,
    toPowerSeries_tautologicalCurve, TauCeti.FormalCoordinate.toPowerSeries_one]

/-- Cartier's `p`-typical coordinate is `1` if and only if `F` is `p`-typical. -/
@[simp]
theorem pTypicalCoordinate_eq_one_iff (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = 1 ↔ F.IsPTypical p := by
  rw [← TauCeti.FormalCoordinate.toCurve_inj F, toCurve_pTypicalCoordinate,
    TauCeti.FormalCoordinate.toCurve_one, pTypicalProjectorCurve_eq_self_iff, isPTypical_def]

/-- Base change commutes with Cartier's `p`-typical coordinate. -/
theorem map_pTypicalCoordinate (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.map φ (F.pTypicalCoordinate p hR) =
      (F.map φ).pTypicalCoordinate p (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) := by
  ext1
  rw [TauCeti.FormalCoordinate.toPowerSeries_map, toPowerSeries_pTypicalCoordinate,
    ← Curve.toPowerSeries_map, F.map_pTypicalProjectorCurve, F.map_tautologicalCurve,
    toPowerSeries_pTypicalCoordinate]

/-- **The canonical `p`-typicalization** of a commutative formal group law `F` over a ring in which
every prime `q ≠ p` is invertible, obtained by transporting `F` along
`(F.pTypicalCoordinate p hunit)⁻¹`. Over a `ℚ`-algebra with `p` prime, its logarithm retains
precisely the `p`-power terms of `F.log`. -/
noncomputable def pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : FormalGroup R :=
  (F.pTypicalCoordinate p hunit)⁻¹ • F

/-- Unfolding formula for `F.pTypicalFormalGroup p hunit` as a coordinate change of `F`. -/
theorem pTypicalFormalGroup_def (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalFormalGroup p hunit = (F.pTypicalCoordinate p hunit)⁻¹ • F :=
  (rfl)

instance (p : ℕ) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).IsComm :=
  instIsCommSMul _ _

/-- **The canonical strict isomorphism** `F ≅ F.pTypicalFormalGroup p hunit` induced by Cartier's
`p`-typicalization projector. -/
noncomputable def pTypicalIso (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalGroupIso F (F.pTypicalFormalGroup p hunit) :=
  smulIso (F.pTypicalCoordinate p hunit)⁻¹ F

instance (p : ℕ) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).IsStrict := by
  dsimp only [pTypicalIso, pTypicalFormalGroup]
  rw [isStrict_smulIso_iff, map_inv, linearCoeff_pTypicalCoordinate, inv_one]

/-- The forward series of `F.pTypicalIso p hunit` is `(F.pTypicalCoordinate p hunit)⁻¹`. -/
@[simp]
theorem pTypicalIso_toHom_toPowerSeries (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).toHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit)⁻¹.toPowerSeries :=
  smulIso_toHom_toPowerSeries _ _

/-- The inverse series of `F.pTypicalIso p hunit` is `F.pTypicalCoordinate p hunit`. -/
@[simp]
theorem pTypicalIso_invHom_toPowerSeries (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).invHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit).toPowerSeries := by
  rw [pTypicalIso, smulIso_invHom_toPowerSeries, inv_inv]

/-- The canonical `p`-typicalization `F.pTypicalFormalGroup p hunit` is `p`-typical. -/
@[simp]
theorem isPTypical_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).IsPTypical p := by
  rw [isPTypical_congr (F.pTypicalFormalGroup_def p hunit), isPTypical_inv_smul_iff]
  exact F.isPTypical_toCurve_pTypicalCoordinate p hunit

/-- If `F` is already `p`-typical, its canonical `p`-typicalization is `F` itself. -/
theorem pTypicalFormalGroup_eq_self (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalFormalGroup p hunit = F := by
  rw [pTypicalFormalGroup_def, F.pTypicalCoordinate_eq_one p hunit hF, inv_one, one_smul]

/-- The canonical `p`-typicalization fixes `F` if and only if `F` is `p`-typical. -/
@[simp]
theorem pTypicalFormalGroup_eq_self_iff (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalFormalGroup p hunit = F ↔ F.IsPTypical p :=
  ⟨fun h ↦ (isPTypical_congr h).mp (F.isPTypical_pTypicalFormalGroup p hunit),
    F.pTypicalFormalGroup_eq_self p hunit⟩

/-- Cartier's `p`-typical coordinate on an already `p`-typicalized formal group law is `1`. -/
@[simp]
theorem pTypicalCoordinate_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).pTypicalCoordinate p hunit = 1 :=
  (F.pTypicalFormalGroup p hunit).pTypicalCoordinate_eq_one p hunit
    (F.isPTypical_pTypicalFormalGroup p hunit)

/-- Canonical `p`-typicalization of formal group laws is idempotent. -/
@[simp]
theorem pTypicalFormalGroup_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).pTypicalFormalGroup p hunit =
      F.pTypicalFormalGroup p hunit :=
  (F.pTypicalFormalGroup p hunit).pTypicalFormalGroup_eq_self p hunit
    (F.isPTypical_pTypicalFormalGroup p hunit)

/-- Base change commutes with canonical `p`-typicalization of formal group laws. -/
theorem map_pTypicalFormalGroup (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hR).map φ =
      (F.map φ).pTypicalFormalGroup p (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) := by
  rw [pTypicalFormalGroup_def, map_smul, map_inv, F.map_pTypicalCoordinate, pTypicalFormalGroup_def]

/-- Over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup p hunit` is obtained by
substituting `F.pTypicalCoordinate p hunit` into `F.log`. -/
theorem log_pTypicalFormalGroup [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).log =
      PowerSeries.subst (F.pTypicalCoordinate p hunit).toPowerSeries F.log := by
  rw [pTypicalFormalGroup_def, log_smul, map_inv, linearCoeff_pTypicalCoordinate, inv_one,
    Units.val_one, one_smul, inv_inv]

/-- Over a `ℚ`-algebra, for `p` prime, the logarithm of `F.pTypicalFormalGroup p hunit` retains
precisely the `p`-power coefficients of `F.log` and zeroes all other degrees. -/
theorem coeff_log_pTypicalFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalFormalGroup p hunit).log =
      if p ^ Nat.log p k = k then PowerSeries.coeff k F.log else 0 := by
  rw [F.log_pTypicalFormalGroup, toPowerSeries_pTypicalCoordinate,
    F.coeff_subst_pTypicalProjectorCurve_log hp hunit k F.tautologicalCurve,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, for `p` prime, `F.pTypicalFormalGroup p hunit` has the same degree-`p^n`
logarithm coefficients as `F`. -/
@[simp]
theorem coeff_log_pTypicalFormalGroup_pow [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    PowerSeries.coeff (p ^ n) (F.pTypicalFormalGroup p hunit).log =
      PowerSeries.coeff (p ^ n) F.log := by
  rw [F.coeff_log_pTypicalFormalGroup hp hunit (p ^ n), ite_eq_left (by rw [Nat.log_pow hp.one_lt])]

/-- Over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup p hunit` vanishes outside degrees of
the form `p^n`. -/
theorem coeff_log_pTypicalFormalGroup_eq_zero [Algebra ℚ R] {p k : ℕ} (hk : ∀ n, p ^ n ≠ k)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff k (F.pTypicalFormalGroup p hunit).log = 0 :=
  (F.isPTypical_pTypicalFormalGroup p hunit).coeff_log_eq_zero hk

/-- Over a `ℚ`-algebra, for `p` prime, the canonical `p`-typicalization of `F` is Hazewinkel's
formal group law for a unique family of generators `v`. -/
theorem existsUnique_pTypicalFormalGroup_eq_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ}
    (hp : p.Prime) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃! v : ℕ+ → R, F.pTypicalFormalGroup p hunit = TauCeti.hazewinkelFormalGroup p v :=
  (F.isPTypical_pTypicalFormalGroup p hunit).existsUnique_eq_hazewinkelFormalGroup hp

end CanonicalCoordinate

end FormalGroup
