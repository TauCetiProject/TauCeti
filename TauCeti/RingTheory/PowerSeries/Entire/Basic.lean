/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm
public import TauCeti.RingTheory.PowerSeries.Restricted
import TauCeti.RingTheory.PowerSeries.Dvd

/-!
# Entire power series

A power series `f = ∑ aₙ Xⁿ` over a normed ring is *entire* when it is restricted at every real
radius, that is, `‖aₙ‖ rⁿ → 0` for every `r`. Over a complete ultrametric ring the sum
`∑ aₙ bⁿ` of such a series then converges at every `b`, not only on a closed disc of some fixed
radius. Entire series are the natural home of Fredholm determinants of compact operators and of
their factorisations by polynomials.

Restrictedness at a radius `r` implies restrictedness at every radius `s` with `|s| ≤ |r|`, so
it suffices to test positive radii (`PowerSeries.isEntire_iff_forall_pos`), or the radii along
any sequence tending to infinity (`PowerSeries.isEntire_iff_of_tendsto`). Over any normed ring,
the entire series form the subring `PowerSeries.IsEntire.subring`. Entire series are stable
under Hasse derivatives, rescaling `f(X) ↦ f(aX)` and coefficientwise application of bounded ring
homomorphisms.

Over a normed ring with `‖a‖ < 1`, the series `∑ a^(n²) Xⁿ` is entire
(`PowerSeries.isEntire_mk_pow_sq`), while for `a ≠ 0` and a multiplicative norm the series
`∑ aⁿ Xⁿ` is not, failing to be restricted at the radius `‖a‖⁻¹`
(`PowerSeries.not_isEntire_mk_pow`), although it is restricted at every radius `r` with
`|r| < ‖a‖⁻¹`. These are the standard examples separating entire series from series
restricted at a fixed radius.

## Main definitions

* `PowerSeries.IsEntire`: `f` is restricted at every real radius.
* `PowerSeries.IsEntire.subring`: the subring of entire series, with coefficient algebra structure
  `PowerSeries.IsEntire.instAlgebraSubring`.
* `PowerSeries.IsEntire.polynomialHom`: the inclusion of polynomials into that subring.
* `PowerSeries.IsEntire.mapHom`: the ring homomorphism on entire series induced by a bounded ring
  homomorphism.

## Main results

* `PowerSeries.isEntire_iff`: the defining condition, for use outside this file.
* `PowerSeries.isEntire_iff_forall_pos` and `PowerSeries.isEntire_iff_of_tendsto`: entireness
  can be tested at positive radii, or along radii tending to infinity.
* `PowerSeries.IsEntire.add`, `PowerSeries.IsEntire.mul`, `PowerSeries.isEntire_coe` and their
  companions: entire series form a subring containing the polynomials.
* `PowerSeries.IsEntire.hasseDeriv`, `PowerSeries.IsEntire.derivative`,
  `PowerSeries.IsEntire.rescale` and `PowerSeries.IsEntire.map`: entireness is preserved by Hasse
  derivatives, rescaling and bounded coefficient maps.
* `PowerSeries.IsEntire.summable_norm_coeff_mul_pow`: `∑ ‖aₙ‖ tⁿ` converges for every real `t`.
* `PowerSeries.IsEntire.mk_coeff_succ`: dropping the constant term and dividing by `X` keeps a
  series entire.
* `PowerSeries.IsEntire.mapHom_polynomialHom`, `PowerSeries.IsEntire.mapHom_id`, and
  `PowerSeries.IsEntire.mapHom_comp`: compatibility of `IsEntire.mapHom` with polynomial
  inclusion, identity, and composition.
* `PowerSeries.IsEntire.eq_C_of_mul_eq_one` and `PowerSeries.IsEntire.isUnit_iff`: over an
  ultrametric normed field, the units of the ring of entire series are the nonzero constants,
  since the Gauss norm is multiplicative and a nonconstant entire series has unbounded Gauss norms.
* `PowerSeries.IsEntire.exists_normalised_factorisation` and
  `PowerSeries.IsEntire.map_factorisation`: coprime entire factorisations rescale to the
  normalised case `Q₁(0) = 1` and transport along bounded ring homomorphisms.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

section NormedRing

variable {R : Type*} [NormedRing R] {f g : R⟦X⟧}

/-- A power series `∑ aₙ Xⁿ` is *entire* when it is restricted at every real radius `r`, that is,
`‖aₙ‖ rⁿ → 0`. -/
def IsEntire (f : R⟦X⟧) : Prop :=
  ∀ r : ℝ, f.IsRestricted r

/-- A series is entire exactly when it is restricted at every real radius. -/
theorem isEntire_iff : f.IsEntire ↔ ∀ r : ℝ, f.IsRestricted r :=
  Iff.rfl

/-- An entire series is restricted at every radius. -/
theorem IsEntire.isRestricted (hf : f.IsEntire) (r : ℝ) : f.IsRestricted r :=
  hf r

/-- Entireness only needs to be checked at positive radii. -/
theorem isEntire_iff_forall_pos : f.IsEntire ↔ ∀ r : ℝ, 0 < r → f.IsRestricted r := by
  refine ⟨fun hf r _ ↦ hf r, fun hf r ↦ ?_⟩
  refine TauCeti.PowerSeries.isRestricted_of_abs_le (hf (|r| + 1) (by positivity)) ?_
  rw [abs_of_pos (by positivity : 0 < |r| + 1)]
  exact le_add_of_nonneg_right zero_le_one

/-- Entireness only needs to be checked along a family of radii tending to infinity, for
instance at the radii `n : ℕ`. -/
theorem isEntire_iff_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {ρ : ι → ℝ}
    (hρ : Tendsto ρ l atTop) : f.IsEntire ↔ ∀ i, f.IsRestricted (ρ i) := by
  refine ⟨fun hf i ↦ hf (ρ i), fun hf r ↦ ?_⟩
  obtain ⟨i, hi⟩ := (hρ.eventually_ge_atTop |r|).exists
  exact TauCeti.PowerSeries.isRestricted_of_abs_le (hf i) (hi.trans (le_abs_self _))

/-- The zero series is entire. -/
@[simp]
theorem isEntire_zero : (0 : R⟦X⟧).IsEntire :=
  fun r ↦ isRestricted_zero r

/-- The constant series `1` is entire. -/
@[simp]
theorem isEntire_one : (1 : R⟦X⟧).IsEntire :=
  fun r ↦ isRestricted_one r

/-- Constant series are entire. -/
@[simp]
theorem isEntire_C (a : R) : (C a).IsEntire :=
  fun r ↦ isRestricted_C r a

/-- Monomials are entire. -/
@[simp]
theorem isEntire_monomial (n : ℕ) (a : R) : (monomial n a).IsEntire :=
  fun r ↦ isRestricted_monomial r n a

/-- The variable `X` is entire. -/
@[simp]
theorem isEntire_X : (X : R⟦X⟧).IsEntire :=
  fun _ ↦ MvPowerSeries.isRestricted_X _ ()

/-- Every polynomial is entire. -/
@[simp]
theorem isEntire_coe (p : Polynomial R) : (p : R⟦X⟧).IsEntire :=
  fun _ ↦ TauCeti.PowerSeries.isRestricted_polynomial p

/-- A sum of entire series is entire. -/
theorem IsEntire.add (hf : f.IsEntire) (hg : g.IsEntire) : (f + g).IsEntire :=
  fun r ↦ (hf r).add (hg r)

/-- The negative of an entire series is entire. -/
theorem IsEntire.neg (hf : f.IsEntire) : (-f).IsEntire :=
  fun r ↦ (hf r).neg

/-- A difference of entire series is entire. -/
theorem IsEntire.sub (hf : f.IsEntire) (hg : g.IsEntire) : (f - g).IsEntire :=
  fun r ↦ (hf r).sub (hg r)

/-- A scalar multiple `a • f` of an entire series is entire. -/
theorem IsEntire.smul (a : R) (hf : f.IsEntire) : (a • f).IsEntire :=
  fun r ↦ (hf r).smul a

/-- A finite sum of entire series is entire. -/
theorem IsEntire.sum {ι : Type*} {s : Finset ι} {f : ι → R⟦X⟧} (hf : ∀ i ∈ s, (f i).IsEntire) :
    (∑ i ∈ s, f i).IsEntire :=
  fun r ↦ MvPowerSeries.IsRestricted.sum fun i hi ↦ hf i hi r

/-- A bounded ring homomorphism `φ`, `‖φ x‖ ≤ C ‖x‖`, maps entire series to entire series
coefficientwise. -/
theorem IsEntire.map {S : Type*} [NormedRing S] (hf : f.IsEntire) (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) : (map φ f).IsEntire :=
  -- `PowerSeries.map φ` is `MvPowerSeries.map φ` in the single variable `Unit`, and
  -- `MvPowerSeries.map φ f` is definitionally `fun t ↦ φ (coeff t f)`, the series that
  -- `isRestricted_map` shows to be restricted.
  fun r ↦ MvPowerSeries.isRestricted_map _ φ hφ (hf r)

/-- Over a normed ring, if `‖a‖ < 1` then `∑ a^(n²) Xⁿ` is entire: at the radius `r`, its
weighted coefficient norms are bounded by `(‖a‖ⁿ r)ⁿ`. -/
theorem isEntire_mk_pow_sq {a : R} (ha : ‖a‖ < 1) : (mk fun n ↦ a ^ (n ^ 2)).IsEntire := by
  intro r
  rw [← isRestricted_abs_iff, isRestricted_iff']
  have hsmall : ∀ᶠ n in atTop, ‖a‖ ^ n * |r| ≤ 1 / 2 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg a) ha).mul_const |r|
    rw [zero_mul] at h
    exact h.eventually (Iic_mem_nhds (by norm_num))
  refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  calc ‖coeff n (mk fun n ↦ a ^ (n ^ 2))‖ * |r| ^ n ≤ ‖a‖ ^ (n ^ 2) * |r| ^ n := by
        rw [coeff_mk]
        gcongr
        exact norm_pow_le' a (by positivity)
    _ = (‖a‖ ^ n * |r|) ^ n := by rw [mul_pow, ← pow_mul, sq]
    _ ≤ (1 / 2) ^ n := by gcongr

/-- Over a ring with multiplicative norm, if `a ≠ 0` then `∑ aⁿ Xⁿ` is not entire: its weighted
coefficient norms at the radius `‖a‖⁻¹` are all `1`. -/
theorem not_isEntire_mk_pow [NormMulClass R] {a : R} (ha : a ≠ 0) :
    ¬(mk fun n ↦ a ^ n).IsEntire :=
  fun hf ↦ TauCeti.PowerSeries.not_isRestricted_mk_pow ha (hf ‖a‖⁻¹)

/-- A product of entire series is entire. -/
theorem IsEntire.mul (hf : f.IsEntire) (hg : g.IsEntire) : (f * g).IsEntire :=
  fun r ↦ (hf (|r| + 1)).mul_of_abs_lt (hg (|r| + 1)) (lt_abs.mpr (.inl (lt_add_one _)))

/-- A power of an entire series is entire. -/
theorem IsEntire.pow (hf : f.IsEntire) (n : ℕ) : (f ^ n).IsEntire := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

/-- Hasse derivatives of entire series are entire. The polynomial growth of the binomial
coefficient is absorbed by testing the original series at a larger radius. -/
theorem IsEntire.hasseDeriv (hf : f.IsEntire) (k : ℕ) :
    (PowerSeries.hasseDeriv k f).IsEntire :=
  fun r ↦ (hf (|r| + 1)).hasseDeriv_of_abs_lt (lt_abs.mpr (.inl (lt_add_one _))) k

/-- For an entire series `f = ∑ aₙ Xⁿ`, the series `∑ ‖aₙ‖ tⁿ` converges for every real `t`. -/
theorem IsEntire.summable_norm_coeff_mul_pow (hf : f.IsEntire) (t : ℝ) :
    Summable fun n ↦ ‖coeff n f‖ * t ^ n :=
  (hf.isRestricted (|t| + 1)).summable_norm_coeff_mul_pow
    (by rw [abs_of_pos (by positivity : 0 < |t| + 1)]; exact lt_add_one _)

/-- The series `∑ aₙ₊₁ Xⁿ` obtained from an entire series by dropping the constant term and
dividing by `X` is entire. -/
theorem IsEntire.mk_coeff_succ (hf : f.IsEntire) : (mk fun n ↦ coeff (n + 1) f).IsEntire := by
  refine isEntire_iff_forall_pos.mpr fun r hr ↦ (isRestricted_iff' r _).mpr ?_
  have h := ((tendsto_add_atTop_iff_nat 1).mpr
    ((isRestricted_iff' r f).mp (hf.isRestricted r))).mul_const r⁻¹
  rw [zero_mul] at h
  refine h.congr fun n ↦ ?_
  rw [coeff_mk, pow_succ]
  field_simp

variable (R) in
/-- The entire power series form a subring. -/
protected noncomputable def IsEntire.subring : Subring R⟦X⟧ where
  carrier := {f | f.IsEntire}
  zero_mem' := isEntire_zero
  one_mem' := isEntire_one
  add_mem' := fun hf hg ↦ hf.add hg
  mul_mem' := fun hf hg ↦ hf.mul hg
  neg_mem' := fun hf ↦ hf.neg

/-- Membership in the subring of entire series is entireness. -/
@[simp]
theorem IsEntire.mem_subring : f ∈ IsEntire.subring R ↔ f.IsEntire :=
  Iff.rfl

/-- The inclusion of polynomials into entire series. -/
noncomputable def IsEntire.polynomialHom : Polynomial R →+* IsEntire.subring R :=
  Polynomial.coeToPowerSeries.ringHom.codRestrict _ fun p ↦
    IsEntire.mem_subring.mpr (isEntire_coe p)

/-- Polynomial inclusion has the usual underlying formal power series. -/
@[simp]
theorem IsEntire.coe_polynomialHom (p : Polynomial R) :
    (IsEntire.polynomialHom p : R⟦X⟧) = p :=
  RingHom.codRestrict_apply _ _ _ p

/-- A bounded ring homomorphism `φ`, `‖φ x‖ ≤ C ‖x‖`, induces a ring homomorphism on subrings of
entire series. -/
noncomputable def IsEntire.mapHom {S : Type*} [NormedRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) : IsEntire.subring R →+* IsEntire.subring S :=
  ((PowerSeries.map φ).comp (IsEntire.subring R).subtype).codRestrict _ fun f ↦
    IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp f.property).map φ hφ)

/-- Applying `IsEntire.mapHom` acts on underlying power series by `PowerSeries.map`. -/
@[simp]
theorem IsEntire.coe_mapHom {S : Type*} [NormedRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (f : IsEntire.subring R) :
    (IsEntire.mapHom φ hφ f : S⟦X⟧) = PowerSeries.map φ (f : R⟦X⟧) :=
  RingHom.codRestrict_apply _ _ _ f

/-- Mapping an entire polynomial under `IsEntire.mapHom` is the polynomial inclusion of its
coefficientwise image. -/
@[simp]
theorem IsEntire.mapHom_polynomialHom {S : Type*} [NormedRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (p : Polynomial R) :
    IsEntire.mapHom φ hφ (IsEntire.polynomialHom p) = IsEntire.polynomialHom (p.map φ) :=
  Subtype.ext (PowerSeries.ext fun n ↦ by simp)

/-- The identity ring homomorphism induces the identity on entire power series. -/
@[simp]
theorem IsEntire.mapHom_id {C : ℝ} (hφ : ∀ x : R, ‖RingHom.id R x‖ ≤ C * ‖x‖) :
    IsEntire.mapHom (RingHom.id R) hφ = RingHom.id (IsEntire.subring R) :=
  RingHom.ext fun f ↦ Subtype.ext <| by
    rw [IsEntire.coe_mapHom, RingHom.id_apply, PowerSeries.map_id, id_eq]

/-- `IsEntire.mapHom` respects composition of bounded ring homomorphisms. -/
theorem IsEntire.mapHom_comp {S T : Type*} [NormedRing S] [NormedRing T]
    (ψ : S →+* T) {C₂ : ℝ} (hψ : ∀ x, ‖ψ x‖ ≤ C₂ * ‖x‖)
    (φ : R →+* S) {C₁ : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖)
    {C₃ : ℝ} (hcomp : ∀ x, ‖(ψ.comp φ) x‖ ≤ C₃ * ‖x‖) :
    IsEntire.mapHom (ψ.comp φ) hcomp =
      (IsEntire.mapHom ψ hψ).comp (IsEntire.mapHom φ hφ) :=
  RingHom.ext fun f ↦ Subtype.ext <| by
    rw [IsEntire.coe_mapHom, RingHom.comp_apply, IsEntire.coe_mapHom, IsEntire.coe_mapHom,
      PowerSeries.map_comp, RingHom.comp_apply]

/-- An algebra structure on the coefficients induces one on entire power series through constant
series. Scalars act as on the ambient formal series, and the coefficient ring need not be
commutative. -/
noncomputable instance IsEntire.instAlgebraSubring {S : Type*} [CommSemiring S] [Algebra S R] :
    Algebra S (IsEntire.subring R) :=
  (IsEntire.subring R).algebraOfMem fun s ↦ by
    rw [PowerSeries.algebraMap_apply]
    exact IsEntire.mem_subring.mpr (isEntire_C _)

/-- A scalar maps to the constant entire series of its image in the coefficient ring. -/
@[simp]
theorem IsEntire.coe_algebraMap_subring {S : Type*} [CommSemiring S] [Algebra S R] (s : S) :
    (algebraMap S (IsEntire.subring R) s : R⟦X⟧) = C (algebraMap S R s) :=
  (Subring.coe_algebraMap_algebraOfMem _ s).trans PowerSeries.algebraMap_apply

/-- Scalars act on entire series as on their underlying formal power series. -/
@[simp]
theorem IsEntire.coe_smul_subring {S : Type*} [CommSemiring S] [Algebra S R] (s : S)
    (h : IsEntire.subring R) :
    ((s • h : IsEntire.subring R) : R⟦X⟧) = s • (h : R⟦X⟧) :=
  Subring.coe_smul_algebraOfMem _ s h

/-- Scalar towers on the coefficients induce scalar towers on entire power series. -/
instance {S T : Type*} [CommSemiring S] [CommSemiring T] [Algebra S R] [Algebra T R]
    [SMul S T] [IsScalarTower S T R] :
    IsScalarTower S T (IsEntire.subring R) :=
  Subring.isScalarTower_algebraOfMem
    (fun s ↦ by rw [PowerSeries.algebraMap_apply]; exact IsEntire.mem_subring.mpr (isEntire_C _))
    (fun t ↦ by rw [PowerSeries.algebraMap_apply]; exact IsEntire.mem_subring.mpr (isEntire_C _))

/-- Over an ultrametric ring, every entire series is restricted at each radius `r`, so the
subring of entire series lies in the restricted subring at `r`. -/
theorem IsEntire.subring_le_isRestrictedSubring [IsUltrametricDist R] (r : ℝ) :
    IsEntire.subring R ≤ IsRestricted.subring r :=
  fun _ hf ↦ hf.isRestricted r

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] {f : R⟦X⟧}

/-- If `f(X)` is entire, so is `f(aX)` for every `a`. -/
theorem IsEntire.rescale (hf : f.IsEntire) (a : R) : (rescale a f).IsEntire :=
  fun _ ↦ (hf _).rescale

/-- The derivative of an entire series is entire. -/
theorem IsEntire.derivative (hf : f.IsEntire) : (d⁄dX f).IsEntire := by
  rw [← hasseDeriv_one_apply]
  exact hf.hasseDeriv 1

end NormedCommRing

section Units

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {f g : K⟦X⟧}

open TauCeti.PowerSeries

/-- **Entire units are constant.** Over an ultrametric normed field, if the product of two entire
series is `1`, then each of them is a constant. -/
theorem IsEntire.eq_C_of_mul_eq_one (hf : f.IsEntire) (hg : g.IsEntire) (h : f * g = 1) :
    f = C (constantCoeff f) := by
  ext n
  rcases n with _ | m
  · simp
  simp only [coeff_C, m.succ_ne_zero, ↓reduceIte]
  by_contra ha
  have hg0 : constantCoeff g ≠ 0 := by
    intro hg0
    simpa [hg0] using congrArg constantCoeff h
  -- At every radius `r > 0`, `‖aₘ₊₁‖ rᵐ⁺¹ ‖g(0)‖ ≤ ‖f‖_r ‖g‖_r = ‖f g‖_r = 1`.
  have key (r : ℝ) (hr : 0 < r) : ‖coeff (m + 1) f‖ * r ^ (m + 1) * ‖constantCoeff g‖ ≤ 1 := by
    have h1 := congrArg NNReal.toReal (map_one (gaussValuation (R := K) hr))
    rw [coe_gaussValuation, OneMemClass.coe_one, NNReal.coe_one, ← h,
      gaussNorm_mul_of_isRestricted hr (hf.isRestricted r) (hg.isRestricted r)] at h1
    rw [← h1]
    refine mul_le_mul (_root_.PowerSeries.le_gaussNorm _ _ _
      (hasGaussNorm_of_isRestricted (hf.isRestricted r)) _) ?_ (norm_nonneg _)
      (_root_.PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg)
    simpa using _root_.PowerSeries.le_gaussNorm _ _ _
      (hasGaussNorm_of_isRestricted (hg.isRestricted r)) 0
  -- A large radius violates this bound.
  set c := ‖coeff (m + 1) f‖ * ‖constantCoeff g‖ with hc_def
  have hc : 0 < c := by positivity
  set r := max 1 (2 / c)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hle : 2 ≤ c * r ^ (m + 1) := calc
    2 = c * (2 / c) := by field_simp
    _ ≤ c * r := by gcongr; exact le_max_right _ _
    _ ≤ c * r ^ (m + 1) := by gcongr; exact le_self_pow₀ hr1 m.succ_ne_zero
  have := key r (by positivity)
  rw [hc_def] at hle
  linarith

/-- **The units of the ring of entire series** over an ultrametric normed field are the nonzero
constants. -/
theorem IsEntire.isUnit_iff {F : IsEntire.subring K} :
    IsUnit F ↔ ∃ c : K, c ≠ 0 ∧ (F : PowerSeries K) = C c := by
  refine ⟨fun hF ↦ ?_, fun ⟨c, hc, hFc⟩ ↦ ?_⟩
  · obtain ⟨G, hG⟩ := hF.exists_right_inv
    have hFG : (F : PowerSeries K) * G = 1 := congrArg Subtype.val hG
    refine ⟨constantCoeff (F : PowerSeries K), fun h0 ↦ ?_,
      IsEntire.eq_C_of_mul_eq_one (IsEntire.mem_subring.mp F.property)
          (IsEntire.mem_subring.mp G.property) hFG⟩
    simpa [h0] using congrArg constantCoeff hFG
  · refine IsUnit.of_mul_eq_one
      (⟨C c⁻¹, IsEntire.mem_subring.mpr (isEntire_C c⁻¹)⟩ : IsEntire.subring K) (Subtype.ext ?_)
    rw [Subring.coe_mul, hFc, OneMemClass.coe_one, ← map_mul, mul_inv_cancel₀ hc, map_one]

end Units

section Factorisation

/-- Bridges `IsCoprime` for `IsEntire.polynomialHom Q` and the raw subtype element `⟨Q, _⟩`. -/
private theorem IsEntire.isCoprime_polynomialHom_iff {R : Type*} [NormedCommRing R]
    (Q : Polynomial R) (S : IsEntire.subring R) :
    IsCoprime (IsEntire.polynomialHom Q) S ↔
      IsCoprime (⟨Q, IsEntire.mem_subring.mpr (isEntire_coe Q)⟩ : IsEntire.subring R) S := by
  have hQ : IsEntire.polynomialHom Q = ⟨Q, IsEntire.mem_subring.mpr (isEntire_coe Q)⟩ :=
    Subtype.ext (IsEntire.coe_polynomialHom Q)
  rw [hQ]

/-- Rescales a general coprime factorisation `u_series = Q * S` (with `u_series(0) = 1`) to the
normalised case `Q₁(0) = 1` via `b = Ring.inverse (Q.coeff 0)` and `S₁ = C (Q.coeff 0) * S`. -/
theorem IsEntire.exists_normalised_factorisation {R : Type*} [NormedCommRing R]
    {u_series : R⟦X⟧} (hu0 : constantCoeff u_series = 1)
    {Q : Polynomial R} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u_series = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ (b : R) (Q₁ : Polynomial R) (S₁ : R⟦X⟧) (hS₁ : S₁.IsEntire),
      b = Ring.inverse (Q.coeff 0) ∧ IsUnit b ∧ Q₁ = Polynomial.C b * Q ∧
      S₁ = C (Q.coeff 0) * S ∧ Q₁.coeff 0 = 1 ∧ IsUnit Q₁.leadingCoeff ∧
      Q₁.natDegree = Q.natDegree ∧ u_series = (Q₁ : R⟦X⟧) * S₁ ∧
      IsCoprime (⟨Q₁, IsEntire.mem_subring.mpr (isEntire_coe Q₁)⟩ : IsEntire.subring R)
        ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩ := by
  have ha : IsUnit (Q.coeff 0) := isUnit_coeff_zero_of_eq_coe_mul hu0 hQS
  set a : R := Q.coeff 0
  set b : R := Ring.inverse a
  have hba : b * a = 1 := Ring.inverse_mul_cancel a ha
  have hb : IsUnit b := IsUnit.of_mul_eq_one a hba
  set Q₁ : Polynomial R := Polynomial.C b * Q
  set S₁ : R⟦X⟧ := C a * S
  have hS₁ : S₁.IsEntire := (isEntire_C a).mul hS
  have hQ₁0 : Q₁.coeff 0 = 1 := by simp [Q₁, hba, a]
  have hQ₁deg : Q₁.natDegree = Q.natDegree := Polynomial.natDegree_C_mul_of_isUnit hb Q
  have hQ₁lc : IsUnit Q₁.leadingCoeff := by
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit hb]
    exact hb.mul hQ
  have hQS₁ : u_series = (Q₁ : R⟦X⟧) * S₁ := by
    rw [hQS]
    simp only [Q₁, S₁, Polynomial.coe_mul, Polynomial.coe_C]
    calc (Q : R⟦X⟧) * S = C (b * a) * ((Q : R⟦X⟧) * S) := by rw [hba, map_one, one_mul]
      _ = C b * (Q : R⟦X⟧) * (C a * S) := by rw [map_mul]; ring
  let S₀ : IsEntire.subring R := ⟨S, IsEntire.mem_subring.mpr hS⟩
  let S₁sub : IsEntire.subring R := ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩
  have hS₁sub : S₁sub = IsEntire.polynomialHom (Polynomial.C a) * S₀ :=
    Subtype.ext (by simp [S₁sub, S₁, S₀])
  have hb' : IsUnit (IsEntire.polynomialHom (Polynomial.C b)) :=
    hb.map (IsEntire.polynomialHom.comp Polynomial.C)
  have ha' : IsUnit (IsEntire.polynomialHom (Polynomial.C a)) :=
    ha.map (IsEntire.polynomialHom.comp Polynomial.C)
  have hcop₁ : IsCoprime (IsEntire.polynomialHom Q₁) S₁sub := by
    rw [hS₁sub]
    simpa only [Q₁, map_mul] using (isCoprime_mul_units_left hb' ha' _ _).2
      ((IsEntire.isCoprime_polynomialHom_iff Q S₀).mpr hcop)
  exact ⟨b, Q₁, S₁, hS₁, rfl, hb, rfl, rfl, hQ₁0, hQ₁lc, hQ₁deg, hQS₁,
    (IsEntire.isCoprime_polynomialHom_iff Q₁ S₁sub).mp hcop₁⟩

/-- Transports a coprime polynomial factorisation `H = Q * S'` in entire power series along a
bounded ring homomorphism `f : R →+* S` into a nontrivial normed commutative ring `S`. -/
theorem IsEntire.map_factorisation {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    [Nontrivial S] {H : R⟦X⟧} {Q : Polynomial R} {S' : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire) (hQS' : H = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) {C : ℝ} (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (Q.map f).natDegree = Q.natDegree ∧
      IsUnit (Q.map f).leadingCoeff ∧
      (PowerSeries.map f S').IsEntire ∧
      PowerSeries.map f H = ((Q.map f : Polynomial S) : S⟦X⟧) * PowerSeries.map f S' ∧
      IsCoprime (⟨Q.map f, IsEntire.mem_subring.mpr (isEntire_coe (Q.map f))⟩ :
        IsEntire.subring S) ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr (hS'.map f hf)⟩ := by
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff f hQ
  have hQlc : IsUnit (Q.map f).leadingCoeff := by
    rw [Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff f hQ]
    exact hQ.map f
  have hFS : (PowerSeries.map f S').IsEntire := hS'.map f hf
  have hHS : PowerSeries.map f H = ((Q.map f : Polynomial S) : S⟦X⟧) * PowerSeries.map f S' := by
    rw [hQS', map_mul, Polynomial.polynomial_map_coe]
  let S₀ : IsEntire.subring R := ⟨S', IsEntire.mem_subring.mpr hS'⟩
  let S₁ : IsEntire.subring S := ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr hFS⟩
  have hS₁ : IsEntire.mapHom f hf S₀ = S₁ := Subtype.ext (IsEntire.coe_mapHom f hf S₀)
  have hcopS : IsCoprime (IsEntire.polynomialHom (Q.map f)) S₁ := by
    rw [← hS₁, ← IsEntire.mapHom_polynomialHom f hf Q]
    exact ((IsEntire.isCoprime_polynomialHom_iff Q S₀).mpr hcop).map (IsEntire.mapHom f hf)
  exact ⟨hQdeg, hQlc, hFS, hHS, (IsEntire.isCoprime_polynomialHom_iff (Q.map f) S₁).mp hcopS⟩

end Factorisation

end PowerSeries
