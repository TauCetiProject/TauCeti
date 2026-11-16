/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Cartier's `p`-typical projector on curves

Let `F` be a commutative formal group law over a commutative ring `R` and let `p` be a natural
number. A curve `γ` on `F` is **`p`-typical** when Cartier's Frobenius operator `f_q` kills it
for every prime `q ≠ p`. These curves form the subgroup `FormalGroup.pTypicalCurves F p`.

When every prime `q ≠ p` is invertible in `R` (for instance over a `ℤ_(p)`-algebra), each
elementary Cartier projector `ε_q = 1 - V_q [q]⁻¹ f_q` is defined, and Cartier's `p`-typical
projector is their infinite composite `ε = ∏_{q ≠ p} ε_q`. The product converges coefficientwise:
`ε_q` leaves coefficients below degree `q` unchanged, so the degree-`k` coefficient of `ε γ` is
that of the finite composite over the primes `q ≤ k`. The projector `ε` is an idempotent additive
endomorphism of the group of curves whose image is exactly the group of `p`-typical curves. It is
natural for base change and for homomorphisms of formal group laws, and it does not change the
linear coefficient of a curve. Over a `ℚ`-algebra it deletes from the logarithm of a curve every
degree with a prime factor other than `p`.

## Main definitions

* `FormalGroup.pTypicalCurves F p`: the subgroup of `p`-typical curves on `F`.
* `FormalGroup.pTypicalProjectorCurve F hR`: Cartier's `p`-typical projector, for
  `hR : ∀ q, q.Prime → q ≠ p → IsUnit (q : R)`.

## Main results

* `FormalGroup.pTypicalProjectorCurve_mem_pTypicalCurves`: the projector lands in the
  `p`-typical curves.
* `FormalGroup.pTypicalProjectorCurve_eq_self_iff`: its fixed curves are the `p`-typical curves.
* `FormalGroup.range_pTypicalProjectorCurve`, `FormalGroup.isIdempotentElem_pTypicalProjectorCurve`:
  it is an idempotent with image the `p`-typical curves.
* `FormalGroup.pTypicalProjectorCurve_cartierProjectorCurve`,
  `FormalGroup.pTypicalProjectorCurve_verschiebungCurve`: it absorbs each elementary projector
  `ε_q` and kills the image of each Verschiebung `V_q`, for primes `q ≠ p`.
* `FormalGroup.coeff_one_pTypicalProjectorCurve`: it preserves linear coefficients.
* `FormalGroup.map_pTypicalProjectorCurve`,
  `TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve`: naturality.
* `FormalGroup.coeff_subst_pTypicalProjectorCurve_log`: over a `ℚ`-algebra, the logarithm of
  `ε γ` keeps exactly the degrees without prime factors other than `p`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical curves -/

section Curves

variable (F : FormalGroup R) [F.IsComm] (p : ℕ)

/-- The **`p`-typical curves** on a commutative formal group law `F`: the curves killed by
Cartier's Frobenius operator `f_q` for every prime `q ≠ p`. -/
def pTypicalCurves : AddSubgroup F.Curve where
  carrier := {γ | ∀ q (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0}
  add_mem' hγ hδ q hq hqp := by rw [map_add, hγ q hq hqp, hδ q hq hqp, _root_.add_zero]
  zero_mem' _ _ _ := map_zero _
  neg_mem' hγ q hq hqp := by rw [map_neg, hγ q hq hqp, neg_zero]

/-- A curve is `p`-typical when `f_q` kills it for every prime `q ≠ p`. -/
@[simp]
theorem mem_pTypicalCurves {γ : F.Curve} :
    γ ∈ F.pTypicalCurves p ↔ ∀ q (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  Iff.rfl

variable {F p}

/-- Base change preserves `p`-typical curves. -/
theorem map_mem_pTypicalCurves (φ : R →+* S) {γ : F.Curve} (hγ : γ ∈ F.pTypicalCurves p) :
    Curve.map φ γ ∈ (F.map φ).pTypicalCurves p := fun q hq hqp ↦ by
  rw [← map_frobeniusCurve, hγ q hq hqp, map_zero]

/-- Along an injective coefficient map, a curve is `p`-typical exactly when its base change is. -/
theorem map_mem_pTypicalCurves_iff {φ : R →+* S} (hφ : Function.Injective φ) {γ : F.Curve} :
    Curve.map φ γ ∈ (F.map φ).pTypicalCurves p ↔ γ ∈ F.pTypicalCurves p := by
  refine ⟨fun hγ q hq hqp ↦ Curve.map_injective hφ ?_, map_mem_pTypicalCurves φ⟩
  rw [map_frobeniusCurve, hγ q hq hqp, map_zero]

end Curves

/-- Homomorphisms of formal group laws carry `p`-typical curves to `p`-typical curves. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_mem_pTypicalCurves {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) {p : ℕ} {γ : F.Curve}
    (hγ : γ ∈ F.pTypicalCurves p) : f.mapCurve γ ∈ G.pTypicalCurves p := fun q hq hqp ↦ by
  rw [← f.mapCurve_frobeniusCurve, hγ q hq hqp, map_zero]

/-- An isomorphism of formal group laws identifies their `p`-typical curves. -/
theorem _root_.TauCeti.FormalGroupIso.curveEquiv_mem_pTypicalCurves_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) {p : ℕ} {γ : F.Curve} :
    e.curveEquiv γ ∈ G.pTypicalCurves p ↔ γ ∈ F.pTypicalCurves p := by
  rw [TauCeti.FormalGroupIso.curveEquiv_apply]
  refine ⟨fun hγ ↦ ?_, e.toHom.mapCurve_mem_pTypicalCurves⟩
  have h := e.invHom.mapCurve_mem_pTypicalCurves hγ
  rwa [← TauCeti.FormalGroupIso.curveEquiv_apply, ← TauCeti.FormalGroupIso.curveEquiv_symm_apply,
    AddEquiv.symm_apply_apply] at h

/-! ### Cartier's `p`-typical projector -/

section Projector

variable (F : FormalGroup R) [F.IsComm] {p : ℕ}
  (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- The composite of the elementary Cartier projectors at the primes `q ≤ N` different
from `p`. -/
private noncomputable def truncProjector : ℕ → F.Curve →+ F.Curve
  | 0 => AddMonoidHom.id F.Curve
  | N + 1 =>
    if h : (N + 1).Prime ∧ N + 1 ≠ p then
      (F.cartierProjectorCurve (N + 1) N.succ_ne_zero (hR _ h.1 h.2)).comp (truncProjector N)
    else truncProjector N

/-- The finite composites agree with each other through degree `M` from stage `M` on. -/
private theorem coeff_truncProjector_of_le {k M N : ℕ} (hk : k ≤ M) (hMN : M ≤ N)
    (γ : F.Curve) :
    PowerSeries.coeff k (truncProjector F hR N γ).toPowerSeries =
      PowerSeries.coeff k (truncProjector F hR M γ).toPowerSeries := by
  induction N, hMN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih =>
    rw [← ih, truncProjector]
    split_ifs
    · exact F.coeff_cartierProjectorCurve_of_lt _ _ _ (by omega) _
    · rfl

/-- A `p`-typical curve is fixed by every finite composite. -/
private theorem truncProjector_eq_self {γ : F.Curve} (hγ : γ ∈ F.pTypicalCurves p) (N : ℕ) :
    truncProjector F hR N γ = γ := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [truncProjector]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, ih]
      exact F.cartierProjectorCurve_eq_self _ _ _ (hγ _ h.1 h.2)
    · exact ih

/-- Every finite composite commutes with each elementary projector `ε_q`. -/
private theorem truncProjector_cartierProjectorCurve {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (N : ℕ) (γ : F.Curve) :
    truncProjector F hR N (F.cartierProjectorCurve q hq.ne_zero (hR q hq hqp) γ) =
      F.cartierProjectorCurve q hq.ne_zero (hR q hq hqp) (truncProjector F hR N γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [truncProjector]
    split_ifs
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih, cartierProjectorCurve_comm]
    · exact ih

/-- From stage `q` on, the finite composites are fixed by `ε_q`. -/
private theorem cartierProjectorCurve_truncProjector {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    {N : ℕ} (hqN : q ≤ N) (γ : F.Curve) :
    F.cartierProjectorCurve q hq.ne_zero (hR q hq hqp) (truncProjector F hR N γ) =
      truncProjector F hR N γ := by
  induction N, hqN using Nat.le_induction with
  | base =>
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne_zero
    rw [truncProjector, dite_eq_left ⟨hq, hqp⟩, AddMonoidHom.comp_apply,
      cartierProjectorCurve_cartierProjectorCurve]
  | succ N _ ih =>
    rw [truncProjector]
    split_ifs
    · rw [AddMonoidHom.comp_apply, cartierProjectorCurve_comm, ih]
    · exact ih

private theorem map_truncProjector (φ : R →+* S)
    (hS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) (N : ℕ) (γ : F.Curve) :
    Curve.map φ (truncProjector F hR N γ) = truncProjector (F.map φ) hS N (Curve.map φ γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [truncProjector, truncProjector]
    split_ifs
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, map_cartierProjectorCurve, ih]
    · exact ih

private theorem mapCurve_truncProjector {G : FormalGroup R} [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (N : ℕ) (γ : F.Curve) :
    f.mapCurve (truncProjector F hR N γ) = truncProjector G hR N (f.mapCurve γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [truncProjector, truncProjector]
    split_ifs
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

/-- **Cartier's `p`-typical projector** `∏_{q ≠ p} ε_q` on the curves of a commutative formal
group law over a ring in which every prime `q ≠ p` is invertible. The infinite composite of the
elementary Cartier projectors `ε_q` converges coefficientwise: its degree-`k` coefficient is that
of the composite over the primes `q ≤ k`. -/
noncomputable def pTypicalProjectorCurve : F.Curve →+ F.Curve where
  toFun γ :=
    ⟨PowerSeries.mk fun k ↦ PowerSeries.coeff k (truncProjector F hR k γ).toPowerSeries, by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
        Curve.coeff_zero_toPowerSeries]⟩
  map_zero' := Curve.ext <| PowerSeries.ext fun k ↦ by simp
  map_add' γ δ := Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [PowerSeries.coeff_mk, map_add]
    refine Curve.coeff_add_congr (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;>
      simp only [PowerSeries.coeff_mk] <;> exact coeff_truncProjector_of_le F hR le_rfl hi _

private theorem toPowerSeries_pTypicalProjectorCurve (γ : F.Curve) :
    (F.pTypicalProjectorCurve hR γ).toPowerSeries =
      PowerSeries.mk fun k ↦ PowerSeries.coeff k (truncProjector F hR k γ).toPowerSeries :=
  (rfl)

/-- The degree-`k` coefficient of `ε γ` is that of every finite composite of elementary
projectors over all primes up to some `N ≥ k`. -/
private theorem coeff_pTypicalProjectorCurve {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve hR γ).toPowerSeries =
      PowerSeries.coeff k (truncProjector F hR N γ).toPowerSeries := by
  rw [toPowerSeries_pTypicalProjectorCurve, PowerSeries.coeff_mk,
    coeff_truncProjector_of_le F hR le_rfl hk]

/-- `ε γ` agrees with the finite composite through degree `N` modulo `X ^ (N + 1)`. -/
private theorem X_pow_dvd_pTypicalProjectorCurve_sub (N : ℕ) (γ : F.Curve) :
    PowerSeries.X ^ (N + 1) ∣ (F.pTypicalProjectorCurve hR γ).toPowerSeries -
      (truncProjector F hR N γ).toPowerSeries :=
  PowerSeries.X_pow_dvd_iff.mpr fun k hk ↦ by
    rw [map_sub, coeff_pTypicalProjectorCurve F hR (Nat.lt_succ_iff.mp hk), sub_self]

/-- Through degree `k`, substituting `ε γ` into a series agrees with substituting the finite
composite over the primes `q ≤ k`. -/
private theorem coeff_subst_pTypicalProjectorCurve (k : ℕ) (γ : F.Curve) (g : PowerSeries R) :
    PowerSeries.coeff k (PowerSeries.subst (F.pTypicalProjectorCurve hR γ).toPowerSeries g) =
      PowerSeries.coeff k (PowerSeries.subst (truncProjector F hR k γ).toPowerSeries g) := by
  have h := PowerSeries.X_pow_dvd_iff.mp (PowerSeries.X_pow_dvd_subst_sub_subst
    (F.pTypicalProjectorCurve hR γ).constantCoeff_toPowerSeries
    (X_pow_dvd_pTypicalProjectorCurve_sub F hR k γ) g) k (Nat.lt_succ_self k)
  rwa [map_sub, sub_eq_zero] at h

/-- Cartier's `p`-typical projector does not change the linear coefficient of a curve. -/
@[simp]
theorem coeff_one_pTypicalProjectorCurve (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalProjectorCurve hR γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries := by
  rw [coeff_pTypicalProjectorCurve F hR le_rfl, truncProjector,
    dite_eq_right fun h ↦ Nat.not_prime_one h.1, truncProjector, AddMonoidHom.id_apply]

/-- Cartier's `p`-typical projector fixes every `p`-typical curve. -/
theorem pTypicalProjectorCurve_eq_self {γ : F.Curve} (hγ : γ ∈ F.pTypicalCurves p) :
    F.pTypicalProjectorCurve hR γ = γ :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [coeff_pTypicalProjectorCurve F hR le_rfl, truncProjector_eq_self F hR hγ]

/-- **Base change commutes with Cartier's `p`-typical projector.** -/
theorem map_pTypicalProjectorCurve (φ : R →+* S) (γ : F.Curve) :
    Curve.map φ (F.pTypicalProjectorCurve hR γ) =
      (F.map φ).pTypicalProjectorCurve (fun q hq hqp ↦ by simpa using (hR q hq hqp).map φ)
        (Curve.map φ γ) :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [Curve.toPowerSeries_map, PowerSeries.coeff_map, coeff_pTypicalProjectorCurve F hR le_rfl,
      coeff_pTypicalProjectorCurve _ _ le_rfl, ← map_truncProjector F hR φ,
      Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- **Homomorphisms of formal group laws commute with Cartier's `p`-typical projector.** -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve {G : FormalGroup R}
    [G.IsComm] (f : TauCeti.FormalGroupHom F G) (γ : F.Curve) :
    f.mapCurve (F.pTypicalProjectorCurve hR γ) = G.pTypicalProjectorCurve hR (f.mapCurve γ) :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, coeff_subst_pTypicalProjectorCurve,
      coeff_pTypicalProjectorCurve G hR le_rfl, ← mapCurve_truncProjector F hR f,
      TauCeti.FormalGroupHom.toPowerSeries_mapCurve]

/-- Over a `ℚ`-algebra, the finite composite over the primes `q ≤ N`, `q ≠ p`, deletes from the
logarithm exactly the nonzero degrees divisible by one of these primes. -/
private theorem coeff_subst_truncProjector_log [Algebra ℚ R] (N : ℕ) {k : ℕ} (hk : k ≠ 0)
    (γ : F.Curve) :
    PowerSeries.coeff k (PowerSeries.subst (truncProjector F hR N γ).toPowerSeries F.log) =
      if ∃ q ∈ k.primeFactors, q ≤ N ∧ q ≠ p then 0
      else PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  induction N with
  | zero =>
    rw [ite_eq_right fun ⟨q, hq, hq0, _⟩ ↦ (Nat.prime_of_mem_primeFactors hq).ne_zero (by omega),
      truncProjector, AddMonoidHom.id_apply]
  | succ N ih =>
    have hC : (∃ q ∈ k.primeFactors, q ≤ N + 1 ∧ q ≠ p) ↔
        (∃ q ∈ k.primeFactors, q ≤ N ∧ q ≠ p) ∨ ((N + 1).Prime ∧ N + 1 ≠ p ∧ N + 1 ∣ k) := by
      simp only [Nat.mem_primeFactors, Nat.le_succ_iff]
      grind
    rw [truncProjector]
    by_cases h : (N + 1).Prime ∧ N + 1 ≠ p
    · rw [dite_eq_left h, AddMonoidHom.comp_apply, coeff_subst_cartierProjectorCurve_log, ih]
      by_cases hd : N + 1 ∣ k
      · rw [ite_eq_left hd, ite_eq_left (hC.mpr (Or.inr ⟨h.1, h.2, hd⟩))]
      · rw [ite_eq_right hd]
        exact if_congr (hC.trans (or_iff_left fun h' ↦ hd h'.2.2)).symm rfl rfl
    · rw [dite_eq_right h, ih]
      exact if_congr (hC.trans (or_iff_left fun h' ↦ h ⟨h'.1, h'.2.1⟩)).symm rfl rfl

/-- Over a `ℚ`-algebra, Cartier's `p`-typical projector deletes from the logarithm of a curve
exactly the degrees with a prime factor other than `p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log [Algebra ℚ R] (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve hR γ).toPowerSeries F.log) =
      if k.primeFactors ⊆ {p} then
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · have h0 (δ : F.Curve) : PowerSeries.coeff 0 (PowerSeries.subst δ.toPowerSeries F.log) = 0 :=
      (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans
        (PowerSeries.constantCoeff_subst_eq_zero δ.constantCoeff_toPowerSeries _
          F.constantCoeff_log)
    rw [ite_eq_left (by simp), h0, h0]
  rw [coeff_subst_pTypicalProjectorCurve, coeff_subst_truncProjector_log F hR k hk γ, ← ite_not]
  refine if_congr ?_ rfl rfl
  rw [Finset.subset_singleton_iff']
  push Not
  exact forall₂_congr fun q hq ↦ ⟨fun h ↦ h (Nat.le_of_mem_primeFactors hq), fun h _ ↦ h⟩

private theorem frobeniusCurve_pTypicalProjectorCurve_of_ratAlgebra [Algebra ℚ R] {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.pTypicalProjectorCurve hR γ) = 0 := by
  apply F.logIso.curveEquiv.injective
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Curve.coeff_zero_toPowerSeries, Curve.coeff_zero_toPowerSeries]
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom, map_zero,
    Curve.toPowerSeries_zero, TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_subst_frobeniusCurve_log, coeff_subst_pTypicalProjectorCurve_log]
  rw [ite_eq_right fun h ↦ hqp (Finset.subset_singleton_iff'.mp h q
    (Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_right q k, mul_ne_zero hq.ne_zero hk⟩)), mul_zero]

/-- **Cartier's `p`-typical projector lands in the `p`-typical curves**: `f_q (ε γ) = 0` for
every prime `q ≠ p`. -/
theorem pTypicalProjectorCurve_mem_pTypicalCurves (γ : F.Curve) :
    F.pTypicalProjectorCurve hR γ ∈ F.pTypicalCurves p := fun q hq hqp ↦
  Curve.eq_of_forall_ratAlgebra F γ {n | n.Prime ∧ n ≠ p} (fun n hn ↦ hR n hn.1 hn.2)
    (fun G _ hB δ ↦ G.frobeniusCurve q hq.ne_zero
      (G.pTypicalProjectorCurve (fun n hn hnp ↦ hB n ⟨hn, hnp⟩) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ _ δ ↦ frobeniusCurve_pTypicalProjectorCurve_of_ratAlgebra G _ hq hqp δ)
    (fun G _ _ _ φ δ ↦ by rw [map_frobeniusCurve, map_pTypicalProjectorCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- The fixed curves of Cartier's `p`-typical projector are exactly the `p`-typical curves. -/
@[simp]
theorem pTypicalProjectorCurve_eq_self_iff (γ : F.Curve) :
    F.pTypicalProjectorCurve hR γ = γ ↔ γ ∈ F.pTypicalCurves p :=
  ⟨fun h ↦ h ▸ F.pTypicalProjectorCurve_mem_pTypicalCurves hR γ,
    F.pTypicalProjectorCurve_eq_self hR⟩

/-- Cartier's `p`-typical projector is idempotent. -/
@[simp]
theorem pTypicalProjectorCurve_pTypicalProjectorCurve (γ : F.Curve) :
    F.pTypicalProjectorCurve hR (F.pTypicalProjectorCurve hR γ) =
      F.pTypicalProjectorCurve hR γ :=
  F.pTypicalProjectorCurve_eq_self hR (F.pTypicalProjectorCurve_mem_pTypicalCurves hR γ)

/-- Cartier's `p`-typical projector is an idempotent in the endomorphism ring of curves. -/
@[simp]
theorem isIdempotentElem_pTypicalProjectorCurve :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.pTypicalProjectorCurve hR) :=
  AddMonoidHom.ext (F.pTypicalProjectorCurve_pTypicalProjectorCurve hR)

/-- The image of Cartier's `p`-typical projector is the group of `p`-typical curves. -/
@[simp]
theorem range_pTypicalProjectorCurve :
    (F.pTypicalProjectorCurve hR).range = F.pTypicalCurves p := by
  ext γ
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.pTypicalProjectorCurve_mem_pTypicalCurves hR δ,
    fun hγ ↦ ⟨γ, F.pTypicalProjectorCurve_eq_self hR hγ⟩⟩

/-- Cartier's `p`-typical projector absorbs each elementary projector `ε_q`, `q ≠ p` prime. -/
@[simp]
theorem pTypicalProjectorCurve_cartierProjectorCurve {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hunit : IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve hR (F.cartierProjectorCurve q hq.ne_zero hunit γ) =
      F.pTypicalProjectorCurve hR γ :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [coeff_pTypicalProjectorCurve F hR (le_add_right le_rfl : k ≤ k + q),
      coeff_pTypicalProjectorCurve F hR (le_add_right le_rfl : k ≤ k + q),
      truncProjector_cartierProjectorCurve F hR hq hqp,
      cartierProjectorCurve_truncProjector F hR hq hqp (le_add_left le_rfl)]

/-- Cartier's `p`-typical projector kills the image of the Verschiebung `V_q` for every prime
`q ≠ p`. -/
@[simp]
theorem pTypicalProjectorCurve_verschiebungCurve {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) : F.pTypicalProjectorCurve hR (F.verschiebungCurve q hq.ne_zero γ) = 0 := by
  rw [← F.pTypicalProjectorCurve_cartierProjectorCurve hR hq hqp (hR q hq hqp),
    cartierProjectorCurve_verschiebungCurve, map_zero]

end Projector

end FormalGroup
