/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Graded
public import TauCeti.RingTheory.FormalGroup.Curve.Typical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral

/-!
# `p`-typical formal group laws and Cartier's canonical typicalization

A commutative formal group law `F` over `R` is **`p`-typical** (`FormalGroup.IsTypical`) if its
tautological curve `T` is `p`-typical (`f_q T = 0` for every prime `q ∤ p`). Over a `ℚ`-algebra,
`F` is `p`-typical iff `log_F(X)` is supported in degrees whose prime factors divide `p` (powers
`p^r` for prime `p`, matching `TauCeti.hazewinkelFormalGroup p v`). Over any commutative ring,
`TauCeti.hazewinkelIntegralFormalGroup p v` and `𝔾ₐ` are `p`-typical.

When every prime `q ∤ p` is invertible in `R`, applying `FormalGroup.typicalProjectorCurve` to `T`
gives Cartier's canonical strict coordinate `c_F = FormalGroup.typicalCoordinate F p hunit`.
Transporting `F` along `c_F⁻¹` gives **Cartier's canonical `p`-typicalization**
`F.typicalize p hunit = c_F⁻¹ • F` and strict isomorphism `F.typicalizeIso p hunit`. It lands in
`p`-typical laws, fixes precisely the `p`-typical laws, is idempotent, deletes non-`p`-typical
degrees from `log_F` over `ℚ`-algebras, commutes with base change and homotheties (while
`typicalCoordinate` conjugates under homotheties), and preserves `ℕ`-gradings.

## Main definitions and results

* `FormalGroup.IsTypical`, `FormalGroup.isTypical_iff_coeff_log_eq_zero`,
  `FormalGroup.isTypical_iff_coeff_log_eq_zero_of_prime`,
  `FormalGroup.IsTypical.existsUnique_eq_hazewinkelFormalGroup`: `p`-typical laws and rational
  classification.
* `TauCeti.isTypical_hazewinkelIntegralFormalGroup`: Hazewinkel's integral law is `p`-typical.
* `FormalGroup.typicalCoordinate`, `FormalGroup.typicalize`, `FormalGroup.typicalizeIso`,
  `FormalGroup.isTypical_typicalize`, `FormalGroup.typicalize_eq_self_iff`,
  `FormalGroup.typicalize_typicalize`, `FormalGroup.coeff_log_typicalize`: Cartier's canonical
  typicalization and its logarithm action.
* `FormalGroup.isTypical_homothety_smul_iff`, `FormalGroup.typicalCoordinate_homothety_smul`,
  `FormalGroup.typicalize_homothety_smul`, `FormalGroup.typicalCoordinate_mem_gradedSubgroup`,
  `FormalGroup.coeff_typicalize_mem`: homothety equivariance and grading preservation.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), A2.1.19–A2.1.25.
-/

public section

namespace FormalGroup

open TauCeti (FormalCoordinate FormalGroupHom FormalGroupIso)

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical formal group laws -/

section IsTypical

variable (F : FormalGroup R) [F.IsComm]

/-- A commutative formal group law `F` is **`p`-typical** if its tautological curve `T` is
`p`-typical on `F`, i.e., `f_q(T) = 0` for every prime `q` not dividing `p`. -/
def IsTypical (p : ℕ) : Prop := F.tautologicalCurve.IsTypical p

/-- Unfold `FormalGroup.IsTypical` in terms of the tautological curve. -/
theorem isTypical_def (p : ℕ) : F.IsTypical p ↔ F.tautologicalCurve.IsTypical p := Iff.rfl

/-- Unfold `FormalGroup.IsTypical` in terms of Cartier's Frobenius operators on `T`. -/
theorem isTypical_iff (p : ℕ) : F.IsTypical p ↔
    ∀ (q : ℕ) (hq : q.Prime), ¬ q ∣ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 :=
  F.tautologicalCurve.isTypical_def p

/-- When `p` is prime, `F` is `p`-typical iff `f_q(T) = 0` for every prime `q ≠ p`. -/
theorem isTypical_iff_of_prime {p : ℕ} (hp : p.Prime) : F.IsTypical p ↔
    ∀ (q : ℕ) (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 :=
  Curve.isTypical_iff_of_prime hp

/-- Every commutative formal group law is `0`-typical, since every prime divides `0`. -/
@[simp]
theorem isTypical_zero_right : F.IsTypical 0 := Curve.isTypical_zero_right F.tautologicalCurve

/-- The additive formal group law `𝔾ₐ` is `p`-typical for every `p` over any commutative ring. -/
@[simp]
theorem isTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ (R := R)).IsTypical p :=
  Curve.isTypical_𝔾ₐ_of_coeff_eq_zero fun k ⟨_, hqk, _⟩ ↦ by
    rcases eq_or_ne k 1 with rfl | hk <;>
      simp_all [toPowerSeries_tautologicalCurve, PowerSeries.coeff_X]

/-- Base change along an injective ring homomorphism reflects and preserves `p`-typicality. -/
theorem isTypical_map_iff_of_injective {p : ℕ} {φ : R →+* S} (hφ : Function.Injective φ) :
    (F.map φ).IsTypical p ↔ F.IsTypical p := by
  rw [isTypical_def, isTypical_def, ← F.map_tautologicalCurve φ,
    Curve.isTypical_map_iff_of_injective hφ]

/-- Over a `ℚ`-algebra, `F` is `p`-typical iff `log_F(X)` has zero coefficient in every degree
divisible by a prime not dividing `p`. -/
theorem isTypical_iff_coeff_log_eq_zero [Algebra ℚ R] (p : ℕ) : F.IsTypical p ↔
    ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) → PowerSeries.coeff k F.log = 0 := by
  rw [isTypical_def, Curve.isTypical_iff_coeff_subst_log_eq_zero, toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, for a prime `p`, `F` is `p`-typical iff `log_F(X)` is supported in the
prime-power degrees `p^r`. -/
theorem isTypical_iff_coeff_log_eq_zero_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime) :
    F.IsTypical p ↔ ∀ k : ℕ, (∀ r : ℕ, p ^ r ≠ k) → PowerSeries.coeff k F.log = 0 := by
  rw [isTypical_def, Curve.isTypical_iff_coeff_subst_log_eq_zero_of_prime hp,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

variable {F}

/-- Congruence for `FormalGroup.IsTypical` across equalities of commutative formal group laws. -/
theorem isTypical_congr {G : FormalGroup R} [G.IsComm] (h : F = G) {p : ℕ} :
    F.IsTypical p ↔ G.IsTypical p := h ▸ Iff.rfl

/-- The tautological curve of a `p`-typical formal group law is `p`-typical. -/
theorem IsTypical.tautologicalCurve {p : ℕ} (hF : F.IsTypical p) :
    F.tautologicalCurve.IsTypical p := hF

/-- On a `p`-typical formal group law with `p ≠ 0`, every curve `V_{p^r} T` is `p`-typical. -/
theorem IsTypical.verschiebungCurve_tautologicalCurve_pow {p : ℕ} (hF : F.IsTypical p)
    (hp : p ≠ 0) (r : ℕ) :
    (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) F.tautologicalCurve).IsTypical p :=
  hF.tautologicalCurve.verschiebungCurve_pow hp r

/-- Base change preserves `p`-typicality of formal group laws. -/
theorem IsTypical.map {p : ℕ} (hF : F.IsTypical p) (φ : R →+* S) : (F.map φ).IsTypical p := by
  rw [isTypical_def, ← F.map_tautologicalCurve φ]
  exact Curve.IsTypical.map hF φ

/-- Over a `ℚ`-algebra, for a prime `p`, every `p`-typical commutative formal group law is
`hazewinkelFormalGroup p v` for a unique parameter family `v : ℕ+ → R`. -/
theorem IsTypical.existsUnique_eq_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ}
    (hF : F.IsTypical p) (hp : p.Prime) :
    ∃! v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt
    ((F.isTypical_iff_coeff_log_eq_zero_of_prime hp).mp hF)

end IsTypical

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Over a `ℚ`-algebra, Hazewinkel's formal group law is `p`-typical for every `p : ℕ`. -/
@[simp]
theorem isTypical_hazewinkelFormalGroup [Algebra ℚ R] (p : ℕ) (v : ℕ+ → R) :
    (hazewinkelFormalGroup p v).IsTypical p := by
  rw [FormalGroup.isTypical_iff_coeff_log_eq_zero, log_hazewinkelFormalGroup]
  rintro k ⟨q, hqk, hqp⟩
  refine coeff_hazewinkelLog_eq_zero v fun r hr ↦ hqp ?_
  exact (Nat.prime_of_mem_primeFactors hqk).dvd_of_dvd_pow (hr ▸ Nat.dvd_of_mem_primeFactors hqk)

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem isTypical_universalHazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime] :
    (universalHazewinkelIntegralFormalGroup p).IsTypical p := by
  rw [← FormalGroup.isTypical_map_iff_of_injective _
      (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective),
    FormalGroup.isTypical_congr (map_intCast_universalHazewinkelIntegralFormalGroup p)]
  exact isTypical_hazewinkelFormalGroup p MvPolynomial.X

/-- Hazewinkel's integral formal group law `hazewinkelIntegralFormalGroup p v` is `p`-typical over
every commutative ring, including rings with torsion. -/
@[simp]
theorem isTypical_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime] (v : ℕ+ → R) :
    (hazewinkelIntegralFormalGroup p v).IsTypical p := by
  rw [FormalGroup.isTypical_congr (hazewinkelIntegralFormalGroup_def p v)]
  exact (isTypical_universalHazewinkelIntegralFormalGroup p).map _

end TauCeti

namespace FormalGroup

open TauCeti (FormalCoordinate FormalGroupHom FormalGroupIso)

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Cartier's canonical strict coordinate and `p`-typicalization -/

section Typicalize

variable (F : FormalGroup R) [F.IsComm]

section FixedPrime

variable (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))

/-- **Cartier's canonical strict coordinate** `c_F(X)` attached to `F` when every prime `q ∤ p` is
a unit in `R`: the typical projection of `T`. -/
noncomputable def typicalCoordinate : FormalCoordinate R where
  toPowerSeries := (F.typicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries :=
    (F.typicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries
  isUnit_coeff_one := by
    rw [F.coeff_one_typicalProjectorCurve, toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X]
    exact isUnit_one

/-- The underlying series of `F.typicalCoordinate p hunit` is the typical projection of `T`. -/
theorem toPowerSeries_typicalCoordinate : (F.typicalCoordinate p hunit).toPowerSeries =
    (F.typicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := (rfl)

/-- Cartier's canonical typical coordinate is strict: its linear coefficient is `1`. -/
@[simp]
theorem coeff_one_typicalCoordinate :
    PowerSeries.coeff 1 (F.typicalCoordinate p hunit).toPowerSeries = 1 := by
  rw [toPowerSeries_typicalCoordinate, F.coeff_one_typicalProjectorCurve,
    toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X]

/-- Cartier's canonical typical coordinate has unit linear coefficient `1`. -/
@[simp]
theorem linearCoeff_typicalCoordinate :
    FormalCoordinate.linearCoeff (F.typicalCoordinate p hunit) = 1 :=
  Units.ext (by rw [FormalCoordinate.val_linearCoeff, Units.val_one, F.coeff_one_typicalCoordinate])

/-- Cartier's canonical typical coordinate lies in the subgroup of strict coordinates. -/
theorem typicalCoordinate_mem_ker_linearCoeff :
    F.typicalCoordinate p hunit ∈ (FormalCoordinate.linearCoeff (R := R)).ker :=
  MonoidHom.mem_ker.mpr (F.linearCoeff_typicalCoordinate p hunit)

/-- The inverse of Cartier's canonical typical coordinate is a strict coordinate. -/
theorem inv_typicalCoordinate_mem_ker_linearCoeff :
    (F.typicalCoordinate p hunit)⁻¹ ∈ (FormalCoordinate.linearCoeff (R := R)).ker :=
  Subgroup.inv_mem _ (F.typicalCoordinate_mem_ker_linearCoeff p hunit)

/-- Cartier's canonical typical coordinate equals `1` if and only if `F` is `p`-typical. -/
@[simp]
theorem typicalCoordinate_eq_one_iff : F.typicalCoordinate p hunit = 1 ↔ F.IsTypical p := by
  rw [FormalCoordinate.ext_iff, toPowerSeries_typicalCoordinate, FormalCoordinate.toPowerSeries_one,
    ← F.toPowerSeries_tautologicalCurve, ← Curve.ext_iff, F.typicalProjectorCurve_eq_self_iff,
    isTypical_def]

/-- **Cartier's canonical `p`-typicalization** of `F` when every prime `q ∤ p` is a unit in `R`,
given by `(F.typicalCoordinate p hunit)⁻¹ • F`. -/
noncomputable def typicalize : FormalGroup R := (F.typicalCoordinate p hunit)⁻¹ • F

/-- Unfold `FormalGroup.typicalize` as `(F.typicalCoordinate p hunit)⁻¹ • F`. -/
theorem typicalize_def : F.typicalize p hunit = (F.typicalCoordinate p hunit)⁻¹ • F := (rfl)

instance : (F.typicalize p hunit).IsComm :=
  inferInstanceAs (((F.typicalCoordinate p hunit)⁻¹ • F).IsComm)

/-- **Cartier's canonical strict isomorphism** `F ≅ F.typicalize p hunit`, with forward series
`(F.typicalCoordinate p hunit)⁻¹` and inverse series `F.typicalCoordinate p hunit`. -/
noncomputable def typicalizeIso : FormalGroupIso F (F.typicalize p hunit) :=
  smulIso (F.typicalCoordinate p hunit)⁻¹ F

instance : (F.typicalizeIso p hunit).IsStrict :=
  (isStrict_smulIso_iff _ _).mpr <| by rw [map_inv, F.linearCoeff_typicalCoordinate, inv_one]

/-- The forward series of `F.typicalizeIso p hunit` is `(F.typicalCoordinate p hunit)⁻¹`. -/
@[simp]
theorem typicalizeIso_toHom_toPowerSeries :
    (F.typicalizeIso p hunit).toHom.toPowerSeries =
      (F.typicalCoordinate p hunit)⁻¹.toPowerSeries := smulIso_toHom_toPowerSeries _ _

/-- The inverse series of `F.typicalizeIso p hunit` is `F.typicalCoordinate p hunit`. -/
@[simp]
theorem typicalizeIso_invHom_toPowerSeries :
    (F.typicalizeIso p hunit).invHom.toPowerSeries = (F.typicalCoordinate p hunit).toPowerSeries :=
  by rw [typicalizeIso, smulIso_invHom_toPowerSeries, inv_inv]

/-- Under the inverse of `F.typicalizeIso p hunit`, the tautological curve of `F.typicalize p hunit`
maps to Cartier's typical projection of the tautological curve of `F`. -/
theorem typicalizeIso_invHom_mapCurve_tautologicalCurve :
    (F.typicalizeIso p hunit).invHom.mapCurve (F.typicalize p hunit).tautologicalCurve =
      F.typicalProjectorCurve p hunit F.tautologicalCurve :=
  Curve.ext <| by
    rw [FormalGroupHom.toPowerSeries_mapCurve, toPowerSeries_tautologicalCurve, PowerSeries.X_subst,
      typicalizeIso_invHom_toPowerSeries, toPowerSeries_typicalCoordinate]

/-- **Cartier's typicalization theorem**: `F.typicalize p hunit` is `p`-typical. -/
@[simp]
theorem isTypical_typicalize : (F.typicalize p hunit).IsTypical p := by
  rw [isTypical_def, ← (F.typicalizeIso p hunit).symm.isTypical_toHom_mapCurve_iff,
    FormalGroupIso.symm_toHom, F.typicalizeIso_invHom_mapCurve_tautologicalCurve]
  exact F.isTypical_typicalProjectorCurve p hunit F.tautologicalCurve

/-- Every `p`-typical formal group law is fixed by `typicalize`. -/
theorem typicalize_eq_self (hF : F.IsTypical p) : F.typicalize p hunit = F := by
  rw [typicalize_def, (F.typicalCoordinate_eq_one_iff p hunit).mpr hF, inv_one, one_smul]

/-- A formal group law is fixed by `typicalize` if and only if it is `p`-typical. -/
@[simp]
theorem typicalize_eq_self_iff : F.typicalize p hunit = F ↔ F.IsTypical p :=
  ⟨fun h ↦ (isTypical_congr h).mp (F.isTypical_typicalize p hunit), F.typicalize_eq_self p hunit⟩

/-- The canonical typical coordinate of `F.typicalize p hunit` is the identity coordinate. -/
@[simp]
theorem typicalCoordinate_typicalize : (F.typicalize p hunit).typicalCoordinate p hunit = 1 :=
  ((F.typicalize p hunit).typicalCoordinate_eq_one_iff p hunit).mpr
    (F.isTypical_typicalize p hunit)

/-- Cartier's `p`-typicalization is idempotent. -/
@[simp]
theorem typicalize_typicalize : (F.typicalize p hunit).typicalize p hunit = F.typicalize p hunit :=
  (F.typicalize p hunit).typicalize_eq_self p hunit (F.isTypical_typicalize p hunit)

end FixedPrime

/-- Cartier's canonical typical coordinate commutes with base change of the coefficient ring. -/
theorem map_typicalCoordinate (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) :
    FormalCoordinate.map φ (F.typicalCoordinate p hR) = (F.map φ).typicalCoordinate p
      (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ) :=
  FormalCoordinate.ext <| by
    rw [FormalCoordinate.toPowerSeries_map, toPowerSeries_typicalCoordinate,
      toPowerSeries_typicalCoordinate, ← Curve.toPowerSeries_map,
      F.map_typicalProjectorCurve φ p hR, F.map_tautologicalCurve]

section Congr

variable {F}

/-- Congruence for `FormalGroup.typicalCoordinate` across equalities of commutative laws. -/
theorem typicalCoordinate_congr {G : FormalGroup R} [G.IsComm] (h : F = G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) :
    F.typicalCoordinate p hunit = G.typicalCoordinate p hunit := h ▸ rfl

/-- Congruence for `FormalGroup.typicalize` across equalities of commutative laws. -/
theorem typicalize_congr {G : FormalGroup R} [G.IsComm] (h : F = G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) :
    F.typicalize p hunit = G.typicalize p hunit := h ▸ rfl

end Congr

/-- Cartier's `p`-typicalization commutes with base change of the coefficient ring. -/
theorem map_typicalize (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) :
    (F.typicalize p hR).map φ = (F.map φ).typicalize p
      (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ) := by
  rw [typicalize_def, typicalize_def, map_smul, map_inv, F.map_typicalCoordinate φ p hR]

end Typicalize

/-! ### Logarithm of the `p`-typicalization over `ℚ`-algebras -/

section Logarithm

variable [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]

section FixedPrime

variable (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))

/-- Over a `ℚ`-algebra, the logarithm of `F.typicalize p hunit` is `log_F(c_F(X))`. -/
theorem log_typicalize : (F.typicalize p hunit).log =
    PowerSeries.subst (F.typicalCoordinate p hunit).toPowerSeries F.log := by
  rw [typicalize_def, F.log_smul, inv_inv, map_inv, F.linearCoeff_typicalCoordinate, inv_one,
    Units.val_one, one_smul]

/-- Over a `ℚ`-algebra, `typicalize` retains degree-`k` logarithm coefficients whose prime factors
all divide `p` and zeroes out all other degrees. -/
theorem coeff_log_typicalize (k : ℕ) : PowerSeries.coeff k (F.typicalize p hunit).log =
    if ∀ q ∈ k.primeFactors, q ∣ p then PowerSeries.coeff k F.log else 0 := by
  rw [F.log_typicalize, toPowerSeries_typicalCoordinate, F.coeff_subst_typicalProjectorCurve_log,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, `F.typicalize p hunit` preserves degree-`p^r` logarithm coefficients. -/
@[simp]
theorem coeff_log_typicalize_pow (r : ℕ) :
    PowerSeries.coeff (p ^ r) (F.typicalize p hunit).log = PowerSeries.coeff (p ^ r) F.log := by
  rw [F.log_typicalize, toPowerSeries_typicalCoordinate,
    F.coeff_subst_typicalProjectorCurve_log_pow, toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, `F.typicalize p hunit` has zero logarithm coefficient in every degree
divisible by a prime not dividing `p`. -/
theorem coeff_log_typicalize_eq_zero {k : ℕ} (hk : ∃ q ∈ k.primeFactors, ¬ q ∣ p) :
    PowerSeries.coeff k (F.typicalize p hunit).log = 0 := by
  obtain ⟨q, hqk, hqp⟩ := hk
  rw [F.coeff_log_typicalize p hunit k, ite_eq_right (fun h ↦ hqp (h q hqk))]

end FixedPrime

/-- Over a `ℚ`-algebra, for a prime `p`, `typicalize` retains degrees `p^r` of `log_F` and zeroes
all other degrees. -/
theorem coeff_log_typicalize_of_prime {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.typicalize p hunit).log =
      if p ^ Nat.log p k = k then PowerSeries.coeff k F.log else 0 := by
  rw [F.log_typicalize, toPowerSeries_typicalCoordinate,
    F.coeff_subst_typicalProjectorCurve_log_of_prime hp, toPowerSeries_tautologicalCurve,
    PowerSeries.X_subst]

end Logarithm

/-! ### Homothety equivariance and preservation of grading -/

section Graded

private theorem mapCurve_homothety_tautologicalCurve (F : FormalGroup R) (u : Rˣ) :
    (smulIso (FormalCoordinate.homothety u) F).toHom.mapCurve
        (F.homothetyCurve (↑u⁻¹ : R) F.tautologicalCurve) =
      (FormalCoordinate.homothety u • F).tautologicalCurve :=
  Curve.ext <| by
    rw [FormalGroupHom.toPowerSeries_mapCurve, smulIso_toHom_toPowerSeries,
      FormalCoordinate.toPowerSeries_homothety,
      PowerSeries.subst_smul (F.homothetyCurve (↑u⁻¹ : R) F.tautologicalCurve).hasSubst,
      PowerSeries.subst_X (F.homothetyCurve (↑u⁻¹ : R) F.tautologicalCurve).hasSubst,
      toPowerSeries_homothetyCurve, toPowerSeries_tautologicalCurve,
      toPowerSeries_tautologicalCurve, PowerSeries.rescale_X, PowerSeries.smul_eq_C_mul,
      ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

/-- Transporting a formal group law along a homothety preserves and reflects `p`-typicality. -/
@[simp]
theorem isTypical_homothety_smul_iff (F : FormalGroup R) [F.IsComm] (p : ℕ) (u : Rˣ) :
    (FormalCoordinate.homothety u • F).IsTypical p ↔ F.IsTypical p := by
  have key (G : FormalGroup R) [G.IsComm] (v : Rˣ) (hG : G.IsTypical p) :
      (FormalCoordinate.homothety v • G).IsTypical p := by
    rw [isTypical_def, ← mapCurve_homothety_tautologicalCurve G v]
    exact (smulIso (FormalCoordinate.homothety v) G).toHom.isTypical_mapCurve
      (hG.tautologicalCurve.homothetyCurve _)
  refine ⟨fun h ↦ ?_, key F u⟩
  have hsmul : FormalCoordinate.homothety u⁻¹ • FormalCoordinate.homothety u • F = F := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  exact (isTypical_congr hsmul).mp (key (FormalCoordinate.homothety u • F) u⁻¹ h)

/-- Transporting `F` along `X ↦ u X` conjugates its canonical typical coordinate:
`c_{u • F}(X) = u c_F(u⁻¹ X)`. -/
theorem typicalCoordinate_homothety_smul (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (u : Rˣ) :
    (FormalCoordinate.homothety u • F).typicalCoordinate p hunit =
      FormalCoordinate.homothety u * F.typicalCoordinate p hunit *
        (FormalCoordinate.homothety u)⁻¹ := by
  let f := (smulIso (FormalCoordinate.homothety u) F).toHom
  let δ := F.homothetyCurve (↑u⁻¹ : R) (F.typicalProjectorCurve p hunit F.tautologicalCurve)
  have hproj :=
    f.mapCurve_typicalProjectorCurve p hunit (F.homothetyCurve (↑u⁻¹ : R) F.tautologicalCurve)
  rw [mapCurve_homothety_tautologicalCurve, F.typicalProjectorCurve_homothetyCurve] at hproj
  refine FormalCoordinate.ext <| PowerSeries.ext fun k ↦ ?_
  rw [toPowerSeries_typicalCoordinate, ← hproj, FormalGroupHom.toPowerSeries_mapCurve,
    smulIso_toHom_toPowerSeries, FormalCoordinate.toPowerSeries_homothety,
    PowerSeries.subst_smul δ.hasSubst, PowerSeries.subst_X δ.hasSubst, toPowerSeries_homothetyCurve,
    ← toPowerSeries_typicalCoordinate]
  have hconj := FormalCoordinate.coeff_homothety_inv_mul_mul_homothety u⁻¹
    (F.typicalCoordinate p hunit) k
  rw [inv_inv, map_inv] at hconj
  rw [hconj, PowerSeries.coeff_smul, PowerSeries.coeff_rescale, smul_eq_mul, mul_assoc]

/-- Transporting a formal group law along a homothety commutes with `typicalize`. -/
theorem typicalize_homothety_smul (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (u : Rˣ) :
    (FormalCoordinate.homothety u • F).typicalize p hunit =
      FormalCoordinate.homothety u • F.typicalize p hunit := by
  rw [typicalize_def, typicalize_def, typicalCoordinate_homothety_smul, mul_inv_rev, mul_inv_rev,
    inv_inv, mul_smul, mul_smul, inv_smul_smul]

section GradedRing

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] (F : FormalGroup A) [F.IsComm] (w p : ℕ)
  (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : A))
  (hF : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈ 𝒜 (w * (d.degree - 1)))
include hF

/-- For a graded commutative formal group law over `A`, `F.typicalCoordinate p hunit` lies in
`TauCeti.FormalCoordinate.gradedSubgroup 𝒜 w`. -/
theorem typicalCoordinate_mem_gradedSubgroup :
    F.typicalCoordinate p hunit ∈ FormalCoordinate.gradedSubgroup 𝒜 w := by
  rw [FormalCoordinate.mem_gradedSubgroup, ← FormalCoordinate.map_toLaurent_eq_conjugate_iff,
    F.map_typicalCoordinate _ p hunit,
    typicalCoordinate_congr ((F.map_toLaurent_eq_homothety_smul_iff w).mpr hF) p _,
    typicalCoordinate_homothety_smul, ← F.map_typicalCoordinate LaurentPolynomial.C p hunit,
    ← map_inv, inv_inv]

/-- **Cartier's `p`-typicalization preserves grading**: if `F` has its coefficient of `Xⁱ Yʲ` in
degree `w * (i + j - 1)`, then so does `F.typicalize p hunit`. -/
theorem coeff_typicalize_mem (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (F.typicalize p hunit).toPowerSeries ∈ 𝒜 (w * (d.degree - 1)) :=
  F.coeff_smul_mem w (F.typicalCoordinate p hunit)⁻¹
    ((FormalCoordinate.gradedSubgroup 𝒜 w).inv_mem
      (F.typicalCoordinate_mem_gradedSubgroup w p hunit hF)) hF d

end GradedRing

end Graded

end FormalGroup
