/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Polynomial.GCD
import TauCeti.Analysis.Polynomial.RealRoots.Ordered
import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
import TauCeti.Analysis.Polynomial.Subresultant
import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.RingTheory.Polynomial.Subresultant.GCD
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.Maps.DomRestrict

/-!
# Open-projection hypersurface modification (Łojasiewicz's Lemma 7)

Given a real-analytic function `f` at a point `p = (x₀, t₀)` of a cylinder `E × ℝ` whose vertical
slice `t ↦ f (x₀, t)` does not vanish identically near `t₀`, its local zero set `{f = 0}` need not
project openly to `E`: two complex-conjugate branches of `{f = 0}` can collide along a
lower-dimensional real locus whose image is not open in `E` (for instance `f ((u, v), t) =
t ^ 2 + u ^ 2` near `((0, 0), 0)`). Łojasiewicz's **open-projection hypersurface lemma** (Lemma 7)
repairs this by adjoining an auxiliary real-analytic factor `g` near `p` whose vertical slice at
`x₀` also does not vanish identically near `t₀`, such that the enlarged zero set `{q ∈ W | f q *
g q = 0}` satisfies *property (P)*: its restricted first-coordinate projection
`{q ∈ W | f q * g q = 0}.domRestrict Prod.fst` is an open map.

The proof proceeds by induction on `dim E`. By Weierstrass preparation, locally `f = P · u` for a
unit `u` and a monic polynomial `P x` in `t` of degree `d`. If `d = 0`, `{f = 0}` is locally empty
and `g = 1` suffices. When `0 < d`, let `k < d` be the least index whose principal subresultant
coefficient `δ k x = psc (P x) (P x)' d (d - 1) k` does not vanish identically near `x₀`. Off the
locus `{δ k = 0}`, the gcd of `P x` with its derivative has constant degree `k`, so `P x` has a
locally constant number of complex roots and its ordered real roots vary continuously; local
continuous root sections show `{P = 0 ∧ δ k ≠ 0}` has open projection. Along `{δ k = 0}`, a linear
change of base coordinates `(y, s)` makes `δ k` regular in `s`, Weierstrass preparation extracts a
monic factor `R y` of `δ k`, Weierstrass division divides `P` by `R y` in `s` with remainder
`Q (y, t)`, and the resultant `H (y, t) = psc (R y) (Q (y, t)) p p 0` vanishes wherever `P` and
`δ k` simultaneously vanish while satisfying `H (0, t) = t ^ (d * p)` near `0`. Applying the
induction hypothesis to `H` produces a factor `K (y, t)` such that `g = H · K` absorbs the singular
locus `{P = 0 ∧ δ k = 0}` into a cylinder over a set with open projection.

## Main declarations

* `AnalyticAt.exists_analyticOnNhd_isOpenMap_domRestrict_fst_mul_eq_zero`: Lemma 7 on `E × ℝ` for a
  finite-dimensional real normed space `E`, producing an open connected neighborhood `W ⊆ V` of `p`
  and `g` analytic on `W` with `¬(fun t ↦ g (p.1, t)) =ᶠ[𝓝 p.2] 0` such that
  `{q ∈ W | f q * g q = 0}.domRestrict Prod.fst` is an open map.
* `AnalyticAt.exists_analyticOnNhd_isOpenMap_domRestrict_tail_mul_eq_zero`: Lemma 7 in cylinder
  coordinates on `Fin (n + 1) → ℝ` with base projection `Fin.tail`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 7.
-/

public section

open Filter Function Polynomial Set Topology
open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff monicOfCoeff_coeff coeff_monicOfCoeff
  coeff_monicOfCoeff_self natDegree_monicOfCoeff eval_monicOfCoeff continuous_coeff_monicOfCoeff)

namespace TauCeti

section Helpers

/-- Each coefficient of `monicOfCoeff (fun i ↦ c i x)` is analytic wherever the lower coefficients
`c i` are analytic. -/
private theorem analyticAt_coeff_monicOfCoeff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {c : Fin d → E → ℝ} {x₀ : E} (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (j : ℕ) :
    AnalyticAt ℝ (fun x ↦ (monicOfCoeff fun i ↦ c i x).coeff j) x₀ := by
  rcases lt_trichotomy j d with hj | rfl | hj
  · exact (hc ⟨j, hj⟩).congr
      (Eventually.of_forall fun x ↦ (coeff_monicOfCoeff (fun i ↦ c i x) ⟨j, hj⟩).symm)
  · exact analyticAt_const.congr (Eventually.of_forall fun _ ↦ (coeff_monicOfCoeff_self _).symm)
  · exact (analyticAt_const (v := (0 : ℝ))).congr (Eventually.of_forall fun _ ↦
      (coeff_eq_zero_of_natDegree_lt ((natDegree_monicOfCoeff _).trans_lt hj)).symm)

/-- The principal subresultant coefficient of `monicOfCoeff c` and its derivative at formal bounds
`d` and `d - 1` is analytic wherever the lower coefficients `c i` are analytic. -/
private theorem analyticAt_psc_monicOfCoeff_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d : ℕ} {c : Fin d → E → ℝ} {x₀ : E} (hc : ∀ i, AnalyticAt ℝ (c i) x₀)
    (j : ℕ) :
    AnalyticAt ℝ (fun x ↦ psc (monicOfCoeff fun i ↦ c i x)
      (monicOfCoeff fun i ↦ c i x).derivative d (d - 1) j) x₀ := by
  refine analyticAt_psc (fun i _ ↦ analyticAt_coeff_monicOfCoeff hc i) (fun i _ ↦ ?_) j
  simp_rw [coeff_derivative]
  exact (analyticAt_coeff_monicOfCoeff hc (i + 1)).mul analyticAt_const

/-- Over an open locus where the principal subresultant coefficients of `monicOfCoeff a` and its
derivative vanish below `k` and the `k`-th one is nonzero, the real zero set has open
`Prod.fst` projection via continuous ordered root sections. -/
private theorem isOpenMap_domRestrict_fst_monicOfCoeff_psc_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ} {U : Set E} (hU : IsOpen U)
    {a : Fin d → E → ℝ} (ha : ∀ i, AnalyticOnNhd ℝ (a i) U)
    (hδlt : ∀ x ∈ U, ∀ j < k,
      psc (monicOfCoeff fun i ↦ a i x) (monicOfCoeff fun i ↦ a i x).derivative d (d - 1) j = 0) :
    IsOpenMap ({p : E × ℝ | p.1 ∈ U ∧ (monicOfCoeff fun i ↦ a i p.1).eval p.2 = 0 ∧
      psc (monicOfCoeff fun i ↦ a i p.1)
        (monicOfCoeff fun i ↦ a i p.1).derivative d (d - 1) k ≠ 0}.domRestrict Prod.fst) := by
  classical
  let P : E → ℝ[X] := fun x ↦ monicOfCoeff fun i ↦ a i x
  let δ : ℕ → E → ℝ := fun j x ↦ psc (P x) (P x).derivative d (d - 1) j
  have hδk_an : AnalyticOnNhd ℝ (δ k) U :=
    fun x hx ↦ analyticAt_psc_monicOfCoeff_derivative (fun i ↦ ha i x hx) k
  have hU'_open : IsOpen {x ∈ U | δ k x ≠ 0} :=
    isOpen_iff_mem_nhds.2 fun x ⟨hxU, hxδ⟩ ↦
      inter_mem (hU.mem_nhds hxU) ((hδk_an x hxU).continuousAt.eventually_ne hxδ)
  have hgcd {x : E} (hx : x ∈ {x ∈ U | δ k x ≠ 0}) :
      (EuclideanDomain.gcd (P x) (P x).derivative).natDegree = k := by
    refine (natDegree_gcd_eq_iff_psc (P x) (P x).derivative k).2 ?_
    rw [natDegree_monicOfCoeff, Polynomial.natDegree_derivative, natDegree_monicOfCoeff]
    exact ⟨hx.2, hδlt x hx.1⟩
  refine isOpenMap_domRestrict_of_local_sections ?_
  rintro ⟨x₀, t₀⟩ ⟨hx₀U, ht₀, hx₀δ⟩
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hU'_open x₀ ⟨hx₀U, hx₀δ⟩
  let B := Metric.ball x₀ r
  have : Nonempty B := ⟨⟨x₀, Metric.mem_ball_self hr⟩⟩
  have : PreconnectedSpace B := Subtype.preconnectedSpace (convex_ball x₀ r).isPreconnected
  have hdeg (b : B) : (P b.1).degree = d := by
    rw [degree_eq_natDegree (monic_monicOfCoeff _).ne_zero, natDegree_monicOfCoeff]
  have hcoeff (i : ℕ) (_ : i ≤ d) : Continuous fun b : B ↦ (P b.1).coeff i :=
    ((continuous_coeff_monicOfCoeff i).comp_continuousOn
      (continuousOn_pi.2 fun l ↦ (ha l).continuousOn.mono (hB.trans fun _ hx ↦ hx.1))).domRestrict
  have hcard (b₀ : B) :
      ∀ᶠ b in 𝓝 b₀, ((P b.1).aroots ℂ).toFinset.card ≤ ((P b₀.1).aroots ℂ).toFinset.card :=
    (eventually_card_aroots_toFinset_eq_of_natDegree_gcd_derivative (K := ℂ) (.of_forall hdeg)
      (.of_forall fun b ↦ by rw [hgcd (hB b.2), hgcd (hB b₀.2)])).mono fun _ h ↦ h.le
  obtain ⟨_, roots, hrc, -, hroot, -⟩ :=
    exists_continuous_ordered_roots_of_preconnectedSpace hcoeff hdeg hcard
  obtain ⟨i, hi⟩ := (hroot ⟨x₀, Metric.mem_ball_self hr⟩ t₀).1 ht₀
  let ρ : E → ℝ := fun x ↦ if hx : x ∈ B then roots ⟨x, hx⟩ i else t₀
  have hρ : ContinuousOn ρ B := continuousOn_iff_continuous_domRestrict.2 <| by
    convert hrc i with b
    simp [ρ, b.2]
  refine ⟨fun x ↦ (x, ρ x), continuousAt_id.prodMk (hρ.continuousAt (Metric.ball_mem_nhds x₀ hr)),
    Prod.ext rfl (by simp [ρ, hi]), ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with x hx
  have hρx : ρ x = roots ⟨x, hx⟩ i := by
    dsimp only [ρ]; split_ifs with hx'; exacts [rfl, (hx' hx).elim]
  refine ⟨⟨(hB hx).1, ?_, (hB hx).2⟩, rfl⟩
  rw [hρx]
  exact (hroot ⟨x, hx⟩ _).2 ⟨i, rfl⟩

/-- For `0 < d` and coefficient functions `a : Fin d → E → ℝ` analytic at `x₀`, there exists a
least index `k < d` whose principal subresultant coefficient `δ k` does not vanish identically near
`x₀`, together with an open neighborhood of `x₀` on which all `a i` are analytic and all `δ j` with
`j < k` vanish. -/
private theorem exists_lt_psc_monicOfCoeff_derivative_not_eventuallyEq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ} (hd : 0 < d) {a : Fin d → E → ℝ} {x₀ : E}
    (ha : ∀ i, AnalyticAt ℝ (a i) x₀) :
    ∃ (k : ℕ) (U : Set E), k < d ∧ IsOpen U ∧ x₀ ∈ U ∧ (∀ i, AnalyticOnNhd ℝ (a i) U) ∧
      ¬(fun x ↦ psc (monicOfCoeff fun i ↦ a i x)
        (monicOfCoeff fun i ↦ a i x).derivative d (d - 1) k) =ᶠ[𝓝 x₀] 0 ∧
      ∀ x ∈ U, ∀ j < k,
        psc (monicOfCoeff fun i ↦ a i x)
          (monicOfCoeff fun i ↦ a i x).derivative d (d - 1) j = 0 := by
  classical
  let P : E → ℝ[X] := fun x ↦ monicOfCoeff fun i ↦ a i x
  let δ : ℕ → E → ℝ := fun j x ↦ psc (P x) (P x).derivative d (d - 1) j
  have hex : ∃ j, j < d ∧ ¬δ j =ᶠ[𝓝 x₀] 0 := by
    let g₀ := (EuclideanDomain.gcd (P x₀) (P x₀).derivative).natDegree
    have hder0 : (P x₀).derivative ≠ 0 := by
      rw [Ne, derivative_eq_zero, natDegree_monicOfCoeff]
      exact hd.ne'
    have hg₀_lt : g₀ < d := by
      have hle := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (P x₀) (P x₀).derivative) hder0
      rw [Polynomial.natDegree_derivative, natDegree_monicOfCoeff] at hle
      omega
    have hg₀_ne : δ g₀ x₀ ≠ 0 :=
      psc_natDegree_gcd_ne_zero (monic_monicOfCoeff _).ne_zero (natDegree_monicOfCoeff _)
        (by rw [Polynomial.natDegree_derivative, natDegree_monicOfCoeff])
    exact ⟨g₀, hg₀_lt, fun h ↦ hg₀_ne h.self_of_nhds⟩
  let k := Nat.find hex
  obtain ⟨hk_lt, hk_ne⟩ := Nat.find_spec hex
  have hlt' : ∀ j : Fin k, ∀ᶠ x in 𝓝 x₀, δ j x = 0 := fun j ↦
    not_not.1 fun h ↦ Nat.find_min hex j.isLt ⟨j.isLt.trans hk_lt, h⟩
  have hlt : ∀ᶠ x in 𝓝 x₀, ∀ j < k, δ j x = 0 :=
    (eventually_all.2 hlt').mono fun _ hx j hj ↦ hx ⟨j, hj⟩
  have ha_nhd : ∀ᶠ x in 𝓝 x₀, ∀ i, AnalyticAt ℝ (a i) x :=
    eventually_all.2 fun i ↦ (ha i).eventually_analyticAt
  refine ⟨k, interior {x | (∀ i, AnalyticAt ℝ (a i) x) ∧ ∀ j < k, δ j x = 0}, hk_lt,
    isOpen_interior, mem_interior_iff_mem_nhds.2 (ha_nhd.and hlt),
    fun i x hx ↦ (interior_subset hx).1 i, hk_ne, fun x hx ↦ (interior_subset hx).2⟩

/-- If `monicOfCoeff c` (of degree `p`) and `Q` (`Q.natDegree ≤ p`) share a root `s`, their
fixed-bound resultant `psc (monicOfCoeff c) Q p p 0` vanishes. -/
private theorem psc_monicOfCoeff_zero_eq_zero_of_common_root {p : ℕ} {c : Fin p → ℝ} {Q : ℝ[X]}
    (hQ : Q.natDegree ≤ p) {s : ℝ} (hR : (monicOfCoeff c).eval s = 0) (hQs : Q.eval s = 0) :
    psc (monicOfCoeff c) Q p p 0 = 0 := by
  have hdvd : X - C s ∣ EuclideanDomain.gcd (monicOfCoeff c) Q :=
    EuclideanDomain.dvd_gcd (dvd_iff_isRoot.2 hR) (dvd_iff_isRoot.2 hQs)
  have hgcd0 : EuclideanDomain.gcd (monicOfCoeff c) Q ≠ 0 :=
    fun h ↦ (monic_monicOfCoeff c).ne_zero (EuclideanDomain.gcd_eq_zero_iff.1 h).1
  have hpos : 0 < (EuclideanDomain.gcd (monicOfCoeff c) Q).natDegree := by
    have h1 := natDegree_le_of_dvd hdvd hgcd0
    rw [natDegree_X_sub_C] at h1
    omega
  exact psc_eq_zero_of_lt_natDegree_gcd (natDegree_monicOfCoeff c).le hQ hpos

/-- For `δ : (Fin (m + 1) → ℝ) → ℝ` analytic at `0`, vanishing at `0`, and not identically zero
near `0`, a linear coordinate change `L : ((Fin m → ℝ) × ℝ) ≃L[ℝ] Fin (m + 1) → ℝ` makes `δ ∘ L`
locally equivalent in its zero set to a Weierstrass polynomial `monicOfCoeff b` of positive degree
in the second factor. -/
private theorem exists_weierstrass_divisor_of_not_eventuallyEq_zero {m : ℕ}
    {δ : (Fin (m + 1) → ℝ) → ℝ} (hδ : AnalyticAt ℝ δ 0) (hδ_not0 : ¬δ =ᶠ[𝓝 0] 0) (hδ0 : δ 0 = 0) :
    ∃ (L : ((Fin m → ℝ) × ℝ) ≃L[ℝ] Fin (m + 1) → ℝ) (p : ℕ) (b : Fin p → (Fin m → ℝ) → ℝ),
      0 < p ∧ (∀ i, AnalyticAt ℝ (b i) 0) ∧ (∀ i, b i 0 = 0) ∧
      ∀ᶠ ys in 𝓝 ((0 : Fin m → ℝ), (0 : ℝ)),
        δ (L ys) = 0 ↔ (monicOfCoeff fun i ↦ b i ys.1).eval ys.2 = 0 := by
  let e₀ : ((Fin m → ℝ) × ℝ) ≃L[ℝ] Fin (m + 1) → ℝ :=
    (ContinuousLinearEquiv.prodComm ℝ (Fin m → ℝ) ℝ).trans (Fin.consEquivL ℝ fun _ ↦ ℝ)
  have hδe : AnalyticAt ℝ (δ ∘ e₀) (0, 0) :=
    hδ.comp_of_eq (e₀.analyticAt (0, 0)) (map_zero e₀)
  have hδe0 : ¬(δ ∘ e₀) =ᶠ[𝓝 (0, 0)] 0 := fun h ↦ hδ_not0 <| by
    have h0 : e₀.symm 0 = (0, 0) := map_zero e₀.symm
    have ht : Tendsto e₀.symm (𝓝 0) (𝓝 (0, 0)) := h0 ▸ e₀.symm.continuousAt.tendsto
    exact (ht.eventually h).mono fun x hx ↦ by simpa [Function.comp_def] using hx
  obtain ⟨L₀, q, hLq, hord⟩ := hδe.exists_continuousLinearEquiv_analyticOrderAt_ne_top hδe0
  obtain rfl : q = (0, 0) := L₀.injective (hLq.trans (map_zero L₀).symm)
  let L := L₀.trans e₀
  have hLδ : AnalyticAt ℝ (fun ys ↦ δ (L ys)) (0, 0) :=
    hδ.comp_of_eq (L.analyticAt (0, 0)) (map_zero L)
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℕ∞) = analyticOrderAt (fun s ↦ δ (L (0, s))) 0 :=
    ENat.ne_top_iff_exists.1 (by simpa [L, Function.comp_def] using hord)
  have hp_pos : 0 < p := Nat.pos_of_ne_zero fun hp0 ↦ by
    have hne : δ (L (0, 0)) ≠ 0 :=
      hLδ.curry_right.analyticOrderAt_eq_zero.1 (by simpa [hp0] using hp.symm)
    have hL0 : L (0, 0) = 0 := map_zero L
    exact hne (hL0.symm ▸ hδ0)
  obtain ⟨b, u, hb, hb0, hu, hu0, hfac⟩ := hLδ.exists_weierstrassPreparation_real hp.symm
  refine ⟨L, p, b, hp_pos, hb, hb0, ?_⟩
  filter_upwards [hfac, hu.continuousAt.eventually_ne hu0] with ys hys hus
  rw [hys, sub_zero, mul_eq_zero, or_iff_left hus]

/-- Dividing `(monicOfCoeff (a ∘ L (y, s))).eval t` by `monicOfCoeff (b y)` in `s` near
`((0, 0), 0)` produces an analytic quotient and a polynomial remainder `Q (y, t)` of degree `< p`
with analytic coefficients. -/
private theorem exists_weierstrassDivision_remainder {m d p : ℕ}
    {L : ((Fin m → ℝ) × ℝ) ≃L[ℝ] Fin (m + 1) → ℝ}
    {a : Fin d → (Fin (m + 1) → ℝ) → ℝ} (ha : ∀ i, AnalyticAt ℝ (a i) 0)
    {b : Fin p → (Fin m → ℝ) → ℝ} (hb : ∀ i, AnalyticAt ℝ (b i) 0) (hb0 : ∀ i, b i 0 = 0) :
    ∃ (q : (((Fin m → ℝ) × ℝ) × ℝ) → ℝ) (r : Fin p → (Fin m → ℝ) × ℝ → ℝ),
      (∀ i, AnalyticAt ℝ (r i) (0, 0)) ∧
      ∀ᶠ yts : ((Fin m → ℝ) × ℝ) × ℝ in 𝓝 ((0, 0), 0),
        (monicOfCoeff fun i ↦ a i (L (yts.1.1, yts.2))).eval yts.1.2 =
          (monicOfCoeff fun i ↦ b i yts.1.1).eval yts.2 * q yts +
            (∑ i : Fin p, monomial (i : ℕ) (r i yts.1)).eval yts.2 := by
  let e₀ : ((Fin m → ℝ) × ℝ) ≃L[ℝ] Fin (m + 1) → ℝ :=
    (ContinuousLinearEquiv.prodComm ℝ (Fin m → ℝ) ℝ).trans (Fin.consEquivL ℝ fun _ ↦ ℝ)
  let c : Fin p → (Fin (m + 1) → ℝ) → ℝ := fun i w ↦ b i (e₀.symm w).1
  have hc (i : Fin p) : AnalyticAt ℝ (c i) 0 :=
    (hb i).comp_of_eq
      (((ContinuousLinearMap.fst ℝ _ _).comp e₀.symm.toContinuousLinearMap).analyticAt 0)
      (by simp)
  let g_div : (Fin (m + 1) → ℝ) × ℝ → ℝ :=
    fun ws ↦ (monicOfCoeff fun i ↦ a i (L ((e₀.symm ws.1).1, ws.2))).eval (e₀.symm ws.1).2
  have hg_div : AnalyticAt ℝ g_div (0, 0) := by
    let ψ : (Fin (m + 1) → ℝ) × ℝ →L[ℝ] (Fin (m + 1) → ℝ) × ℝ :=
      (L.toContinuousLinearMap.comp
        (((ContinuousLinearMap.fst ℝ _ _).comp e₀.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.fst ℝ _ _) |>.prod (ContinuousLinearMap.snd ℝ _ _))).prod
        (((ContinuousLinearMap.snd ℝ _ _).comp e₀.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.fst ℝ _ _))
    exact (TauCeti.Polynomial.analyticAt_eval_of_analyticAt_coeff
      (fun i _ ↦ analyticAt_coeff_monicOfCoeff ha i)
      (.of_forall fun _ ↦ (natDegree_monicOfCoeff _).le) 0).comp_of_eq
      (ψ.analyticAt (0, 0)) (map_zero ψ)
  obtain ⟨q_div, r_div, -, hr_div, hdiv₀⟩ :=
    hg_div.exists_weierstrassDivision_monicOfCoeff_real hc fun i ↦ by simp [c, hb0 i]
  let E₀ : (((Fin m → ℝ) × ℝ) × ℝ) → (Fin (m + 1) → ℝ) × ℝ := fun yts ↦ (e₀ yts.1, yts.2)
  have hE₀ : Tendsto E₀ (𝓝 ((0, 0), 0)) (𝓝 (0, 0)) := by
    have hE₀0 : E₀ ((0, 0), 0) = (0, 0) := Prod.ext (map_zero e₀) rfl
    exact hE₀0 ▸ ((e₀.continuous.comp continuous_fst).prodMk continuous_snd).continuousAt.tendsto
  refine ⟨fun yts ↦ q_div (E₀ yts), fun i yt ↦ r_div i (e₀ yt),
    fun i ↦ (hr_div i).comp_of_eq (e₀.analyticAt (0, 0)) (map_zero e₀), ?_⟩
  filter_upwards [hE₀.eventually hdiv₀] with ⟨⟨y, t⟩, s⟩ h
  simpa [g_div, E₀, c, eval_finsetSum] using h

/-- Resultant elimination along the singular locus `{δ = 0}`: dividing `(P (L (y, s))).eval t` by
the Weierstrass polynomial `R y` of `δ ∘ L` in `s` and taking the resultant `H (y, t)` with the
remainder eliminates `s` on a neighborhood of `((0, 0), 0)` while keeping `t ↦ H (0, t)` non-zero
near `0`. -/
private theorem exists_resultant_eliminator {m d : ℕ}
    {a : Fin d → (Fin (m + 1) → ℝ) → ℝ} (ha : ∀ i, AnalyticAt ℝ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    {δ : (Fin (m + 1) → ℝ) → ℝ} (hδ : AnalyticAt ℝ δ 0) (hδ_not0 : ¬δ =ᶠ[𝓝 0] 0) (hδ0 : δ 0 = 0) :
    ∃ (L : ((Fin m → ℝ) × ℝ) ≃L[ℝ] Fin (m + 1) → ℝ) (H : (Fin m → ℝ) × ℝ → ℝ)
      (N : Set (((Fin m → ℝ) × ℝ) × ℝ)),
      AnalyticAt ℝ H (0, 0) ∧ ¬(fun t ↦ H (0, t)) =ᶠ[𝓝 0] 0 ∧ N ∈ 𝓝 ((0, 0), 0) ∧
      ∀ y t s, ((y, t), s) ∈ N →
        (monicOfCoeff fun i ↦ a i (L (y, s))).eval t = 0 → δ (L (y, s)) = 0 → H (y, t) = 0 := by
  obtain ⟨L, p, b, hp_pos, hb, hb0, hδ_iff⟩ :=
    exists_weierstrass_divisor_of_not_eventuallyEq_zero hδ hδ_not0 hδ0
  obtain ⟨q', r', hr', hdiv⟩ := exists_weierstrassDivision_remainder (L := L) ha hb hb0
  let R : (Fin m → ℝ) → ℝ[X] := fun y ↦ monicOfCoeff fun i ↦ b i y
  let Q : (Fin m → ℝ) × ℝ → ℝ[X] := fun yt ↦ ∑ i : Fin p, monomial (i : ℕ) (r' i yt)
  have hQ_deg (yt : (Fin m → ℝ) × ℝ) : (Q yt).natDegree ≤ p :=
    natDegree_sum_le_of_forall_le _ _ fun i _ ↦ (natDegree_monomial_le (r' i yt)).trans i.isLt.le
  let H : (Fin m → ℝ) × ℝ → ℝ := fun yt ↦ psc (R yt.1) (Q yt) p p 0
  have hH_an : AnalyticAt ℝ H (0, 0) := by
    refine analyticAt_psc
      (fun j _ ↦ (analyticAt_coeff_monicOfCoeff hb j).comp_of_eq analyticAt_fst rfl)
      (fun j _ ↦ ?_) 0
    simp_rw [Q, finsetSum_coeff, coeff_monomial, Finsupp.single_apply]
    exact Finset.univ.analyticAt_fun_sum fun i _ ↦ by
      split_ifs <;> first | exact hr' i | exact analyticAt_const
  have hH_slice : ¬(fun t ↦ H (0, t)) =ᶠ[𝓝 0] 0 := fun h0 ↦ by
    have hR0 : R 0 = X ^ p := by
      convert monicOfCoeff_coeff (R := ℝ) (monic_X_pow p) (natDegree_X_pow p) with i
      simp [hb0 i, coeff_X_pow, i.isLt.ne]
    have ht0 : Tendsto (fun t : ℝ ↦ (((0 : Fin m → ℝ), t), (0 : ℝ))) (𝓝 0) (𝓝 ((0, 0), 0)) :=
      ((continuous_const.prodMk continuous_id).prodMk continuous_const).tendsto 0
    have hH_eq : (fun t ↦ H (0, t)) =ᶠ[𝓝 0] fun t ↦ (t - 0) ^ (d * p) := by
      filter_upwards [ht0.eventually hdiv] with t ht
      have hL0 : L (0, 0) = 0 := map_zero L
      have hQ0 : (Q (0, t)).coeff 0 = t ^ d := by
        rw [coeff_zero_eq_eval_zero]
        have ht' := ht
        rw [hL0, eval_monicOfCoeff, eval_monicOfCoeff] at ht'
        simpa [ha0, hb0, zero_pow hp_pos.ne'] using ht'.symm
      have hHp : H (0, t) = psc (R 0) (Q (0, t)) p p 0 := rfl
      rw [hHp, hR0, psc_zero, resultant_X_pow_left _ _ _ (hQ_deg _), hQ0, sub_zero, ← pow_mul]
    have htop := (analyticOrderAt_congr hH_eq.symm).trans (analyticOrderAt_eq_top.2 h0)
    exact ENat.natCast_ne_top (d * p) (analyticOrderAt_centeredMonomial.symm.trans htop)
  have hδ_pull : ∀ᶠ yts : ((Fin m → ℝ) × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      δ (L (yts.1.1, yts.2)) = 0 ↔ (R yts.1.1).eval yts.2 = 0 :=
    (((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto ((0, 0), 0)).eventually
      hδ_iff
  refine ⟨L, H, _, hH_an, hH_slice, inter_mem hdiv hδ_pull, fun y t s ⟨h1, h2⟩ hP0 hδL0 ↦ ?_⟩
  have hRs : (R y).eval s = 0 := h2.1 hδL0
  have hQs : (Q (y, t)).eval s = 0 := by
    have h1' : (monicOfCoeff fun i ↦ a i (L (y, s))).eval t =
        (R y).eval s * q' ((y, t), s) + (Q (y, t)).eval s := h1
    rw [hP0, hRs, zero_mul, zero_add] at h1'
    exact h1'.symm
  exact psc_monicOfCoeff_zero_eq_zero_of_common_root (hQ_deg (y, t)) hRs hQs

/-- Combining an open-projection subset `s₁` with a base-pulled-back open-projection zero set
`{g = 0}` yields open `Prod.fst` projection for `{q ∈ W | f q * g q = 0}`. -/
private theorem isOpenMap_domRestrict_fst_mul_of_cover {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {W s₁ : Set (X × ℝ)} (hW : IsOpen W)
    (hs₁ : IsOpenMap (s₁.domRestrict Prod.fst)) {Z_m : Set (Y × ℝ)}
    (hZ_m : IsOpenMap (Z_m.domRestrict Prod.fst)) {π : X → Y} (hπ : Continuous π)
    {f g : X × ℝ → ℝ} (hg_iff : ∀ q ∈ W, g q = 0 ↔ (π q.1, q.2) ∈ Z_m)
    (hs₁_sub : ∀ q ∈ s₁, q ∈ W → f q = 0)
    (hcover : ∀ q ∈ W, f q = 0 → q ∈ s₁ ∨ g q = 0) :
    IsOpenMap ({q ∈ W | f q * g q = 0}.domRestrict Prod.fst) := by
  have hZg : IsOpenMap ({q ∈ W | g q = 0}.domRestrict Prod.fst) := by
    have hset : {q ∈ W | g q = 0} = Prod.map π id ⁻¹' Z_m ∩ W := by
      ext q
      exact ⟨fun ⟨hqW, hg0⟩ ↦ ⟨(hg_iff q hqW).1 hg0, hqW⟩,
        fun ⟨hZ, hqW⟩ ↦ ⟨hqW, (hg_iff q hqW).2 hZ⟩⟩
    rw [hset]
    exact (hZ_m.domRestrict_fst_preimage_prodMap_id hπ).domRestrict_inter hW
  have hunion : {q ∈ W | f q * g q = 0} = (s₁ ∩ W) ∪ {q ∈ W | g q = 0} := by
    ext q
    refine ⟨fun ⟨hqW, hfg⟩ ↦ ?_, fun h ↦ ?_⟩
    · rcases mul_eq_zero.1 hfg with hf0 | hg0
      · exact (hcover q hqW hf0).imp (fun hs ↦ ⟨hs, hqW⟩) fun hg0 ↦ ⟨hqW, hg0⟩
      · exact Or.inr ⟨hqW, hg0⟩
    · rcases h with ⟨hs, hqW⟩ | ⟨hqW, hg0⟩
      · exact ⟨hqW, mul_eq_zero_of_left (hs₁_sub q hs hqW) _⟩
      · exact ⟨hqW, mul_eq_zero_of_right _ hg0⟩
  rw [hunion]
  exact (hs₁.domRestrict_inter hW).domRestrict_union hZg

/-- Inductive step at `(0, 0) : (Fin (m + 1) → ℝ) × ℝ` when `f` has positive vertical order `d` and
`δ k 0 = 0`. -/
private theorem exists_isOpenMap_domRestrict_fst_origin_succ_of_psc_zero {m d k : ℕ}
    (ih : ∀ {H : (Fin m → ℝ) × ℝ → ℝ} {V : Set ((Fin m → ℝ) × ℝ)},
      AnalyticAt ℝ H (0, 0) → ¬(fun t ↦ H (0, t)) =ᶠ[𝓝 0] 0 → V ∈ 𝓝 (0, 0) →
      ∃ (K : (Fin m → ℝ) × ℝ → ℝ) (W : Set ((Fin m → ℝ) × ℝ)),
        IsOpen W ∧ (0, 0) ∈ W ∧ W ⊆ V ∧ AnalyticOnNhd ℝ K W ∧ ¬(fun t ↦ K (0, t)) =ᶠ[𝓝 0] 0 ∧
        IsOpenMap ({q ∈ W | H q * K q = 0}.domRestrict Prod.fst))
    {f : (Fin (m + 1) → ℝ) × ℝ → ℝ} {V W₀ : Set ((Fin (m + 1) → ℝ) × ℝ)}
    {U_a : Set (Fin (m + 1) → ℝ)} {a : Fin d → (Fin (m + 1) → ℝ) → ℝ}
    (ha : ∀ i, AnalyticAt ℝ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hU_a : IsOpen U_a) (ha_on : ∀ i, AnalyticOnNhd ℝ (a i) U_a)
    (hδlt : ∀ x ∈ U_a, ∀ j < k,
      psc (monicOfCoeff fun i ↦ a i x) (monicOfCoeff fun i ↦ a i x).derivative d (d - 1) j = 0)
    (hk_ne : ¬(fun x ↦ psc (monicOfCoeff fun i ↦ a i x)
      (monicOfCoeff fun i ↦ a i x).derivative d (d - 1) k) =ᶠ[𝓝 0] 0)
    (hk0 : psc (monicOfCoeff fun i ↦ a i 0)
      (monicOfCoeff fun i ↦ a i 0).derivative d (d - 1) k = 0)
    (hW₀_open : IsOpen W₀) (h0W₀ : (0, 0) ∈ W₀) (hW₀V : W₀ ⊆ V)
    (hW₀_iff : ∀ q ∈ W₀, q.1 ∈ U_a ∧ (f q = 0 ↔ (monicOfCoeff fun i ↦ a i q.1).eval q.2 = 0)) :
    ∃ (g : (Fin (m + 1) → ℝ) × ℝ → ℝ) (W : Set ((Fin (m + 1) → ℝ) × ℝ)),
      IsOpen W ∧ (0, 0) ∈ W ∧ W ⊆ V ∧ AnalyticOnNhd ℝ g W ∧ ¬(fun t ↦ g (0, t)) =ᶠ[𝓝 0] 0 ∧
      IsOpenMap ({q ∈ W | f q * g q = 0}.domRestrict Prod.fst) := by
  let P : (Fin (m + 1) → ℝ) → ℝ[X] := fun x ↦ monicOfCoeff fun i ↦ a i x
  obtain ⟨L, H, N, hH_an, hH_slice, hN, hH_elim⟩ :=
    exists_resultant_eliminator ha ha0 (analyticAt_psc_monicOfCoeff_derivative ha k) hk_ne hk0
  obtain ⟨r_H, hr_H, hH_ball⟩ := hH_an.exists_ball_analyticOnNhd
  have hΦW₀ : {yts : ((Fin m → ℝ) × ℝ) × ℝ | (L (yts.1.1, yts.2), yts.1.2) ∈ W₀} ∈
      𝓝 ((0, 0), 0) :=
    (hW₀_open.preimage <|
      (L.continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
        (continuous_snd.comp continuous_fst)).mem_nhds
      (by have hL0 : L (0, 0) = 0 := map_zero L; simpa [hL0] using h0W₀)
  obtain ⟨U_yt, hU_yt, U_s0, hU_s0, hprod⟩ := mem_nhds_prod_iff.1 (inter_mem hN hΦW₀)
  obtain ⟨K, W_m, hWm_open, h0Wm, hWm_sub, hK_an, hK_slice, hZ_m⟩ :=
    ih hH_an hH_slice (inter_mem hU_yt (Metric.ball_mem_nhds (0, 0) hr_H))
  let π := (ContinuousLinearMap.fst ℝ _ _).comp L.symm.toContinuousLinearMap
  let σ_s := (ContinuousLinearMap.snd ℝ _ _).comp L.symm.toContinuousLinearMap
  have hL (x) : L (π x, σ_s x) = x := L.apply_symm_apply x
  let W := Prod.map π id ⁻¹' W_m ∩ (σ_s ⁻¹' interior U_s0) ×ˢ univ
  have hW_open : IsOpen W := (hWm_open.preimage (π.continuous.prodMap continuous_id)).inter
    ((isOpen_interior.preimage σ_s.continuous).prod isOpen_univ)
  have h0W : (0, 0) ∈ W := ⟨by simpa [π] using h0Wm,
    mem_interior_iff_mem_nhds.2 (by simpa [σ_s] using hU_s0), trivial⟩
  have hW_sub {q} (hq : q ∈ W) : ((π q.1, q.2), σ_s q.1) ∈ N ∧ q ∈ W₀ := by
    have hmem := hprod (mk_mem_prod (hWm_sub hq.1).1 (interior_subset hq.2.1))
    exact ⟨hmem.1, by simpa [hL q.1] using hmem.2⟩
  let g : (Fin (m + 1) → ℝ) × ℝ → ℝ := fun q ↦ H (π q.1, q.2) * K (π q.1, q.2)
  have hg_an : AnalyticOnNhd ℝ g W := fun q hq ↦
    ((hH_ball _ (hWm_sub hq.1).2).mul (hK_an _ hq.1)).comp
      (((π.comp (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)).analyticAt q)
  have hg_slice : ¬(fun t ↦ g (0, t)) =ᶠ[𝓝 0] 0 := fun h0 ↦ by
    have h0' : (fun t ↦ H (0, t) * K (0, t)) =ᶠ[𝓝 0] 0 :=
      h0.mono fun t ht ↦ by simpa only [g, π, map_zero] using ht
    have htop : analyticOrderAt (fun t ↦ H (0, t) * K (0, t)) 0 = ⊤ :=
      analyticOrderAt_eq_top.2 h0'
    rw [analyticOrderAt_fun_mul hH_an.curry_right (hK_an (0, 0) h0Wm).curry_right,
      ENat.add_eq_top, analyticOrderAt_eq_top, analyticOrderAt_eq_top] at htop
    exact htop.elim hH_slice hK_slice
  refine ⟨g, W, hW_open, h0W, fun q hq ↦ hW₀V (hW_sub hq).2, hg_an, hg_slice,
    isOpenMap_domRestrict_fst_mul_of_cover hW_open
      (isOpenMap_domRestrict_fst_monicOfCoeff_psc_ne_zero hU_a ha_on hδlt) hZ_m π.continuous
      (fun _ hq ↦ ⟨fun hg0 ↦ ⟨hq.1, hg0⟩, fun ⟨_, hg0⟩ ↦ hg0⟩)
      (fun q hq hqW ↦ (hW₀_iff q (hW_sub hqW).2).2.2 hq.2.1) fun q hqW hf0 ↦ ?_⟩
  obtain ⟨hqN, hqW₀⟩ := hW_sub hqW
  have hPq : (P q.1).eval q.2 = 0 := (hW₀_iff q hqW₀).2.1 hf0
  by_cases hδq : psc (P q.1) (P q.1).derivative d (d - 1) k = 0
  · have hH0 := hH_elim (π q.1) q.2 (σ_s q.1) hqN
      (by simpa [P, hL q.1] using hPq) (by simpa [P, hL q.1] using hδq)
    exact Or.inr (by simp [g, hH0])
  · exact Or.inl ⟨(hW₀_iff q hqW₀).1, hPq, hδq⟩

/-- Non-singular step at `(0, 0) : (Fin (m + 1) → ℝ) × ℝ` when `f` has positive vertical order `d`
and `δ k 0 ≠ 0`: no auxiliary factor (`g = 1`) is needed. -/
private theorem exists_isOpenMap_domRestrict_fst_origin_succ_of_psc_ne_zero {m d k : ℕ}
    {f : (Fin (m + 1) → ℝ) × ℝ → ℝ} {V W₀ : Set ((Fin (m + 1) → ℝ) × ℝ)}
    {U_a : Set (Fin (m + 1) → ℝ)} {a : Fin d → (Fin (m + 1) → ℝ) → ℝ}
    (hU_a : IsOpen U_a) (h0U_a : 0 ∈ U_a) (ha_on : ∀ i, AnalyticOnNhd ℝ (a i) U_a)
    (hδlt : ∀ x ∈ U_a, ∀ j < k,
      psc (monicOfCoeff fun i ↦ a i x) (monicOfCoeff fun i ↦ a i x).derivative d (d - 1) j = 0)
    (hk0 : psc (monicOfCoeff fun i ↦ a i 0)
      (monicOfCoeff fun i ↦ a i 0).derivative d (d - 1) k ≠ 0)
    (hW₀_open : IsOpen W₀) (h0W₀ : (0, 0) ∈ W₀) (hW₀V : W₀ ⊆ V)
    (hW₀_iff : ∀ q ∈ W₀, q.1 ∈ U_a ∧ (f q = 0 ↔ (monicOfCoeff fun i ↦ a i q.1).eval q.2 = 0)) :
    ∃ (g : (Fin (m + 1) → ℝ) × ℝ → ℝ) (W : Set ((Fin (m + 1) → ℝ) × ℝ)),
      IsOpen W ∧ (0, 0) ∈ W ∧ W ⊆ V ∧ AnalyticOnNhd ℝ g W ∧ ¬(fun t ↦ g (0, t)) =ᶠ[𝓝 0] 0 ∧
      IsOpenMap ({q ∈ W | f q * g q = 0}.domRestrict Prod.fst) := by
  let P : (Fin (m + 1) → ℝ) → ℝ[X] := fun x ↦ monicOfCoeff fun i ↦ a i x
  let δ : (Fin (m + 1) → ℝ) → ℝ := fun x ↦ psc (P x) (P x).derivative d (d - 1) k
  have hδ_open : IsOpen {x ∈ U_a | δ x ≠ 0} :=
    isOpen_iff_mem_nhds.2 fun x ⟨hxU, hxδ⟩ ↦ inter_mem (hU_a.mem_nhds hxU)
      ((analyticAt_psc_monicOfCoeff_derivative (fun i ↦ ha_on i x hxU)
        k).continuousAt.eventually_ne hxδ)
  let W := W₀ ∩ {x ∈ U_a | δ x ≠ 0} ×ˢ univ
  have hW_open : IsOpen W := hW₀_open.inter (hδ_open.prod isOpen_univ)
  refine ⟨fun _ ↦ 1, W, hW_open, ⟨h0W₀, ⟨h0U_a, hk0⟩, trivial⟩,
    inter_subset_left.trans hW₀V, fun _ _ ↦ analyticAt_const,
    fun h ↦ one_ne_zero h.self_of_nhds, ?_⟩
  have hset : {q ∈ W | f q * 1 = 0} =
      {q | q.1 ∈ U_a ∧ (P q.1).eval q.2 = 0 ∧ δ q.1 ≠ 0} ∩ W := by
    ext q
    exact ⟨fun ⟨hqW, hfq⟩ ↦ ⟨⟨hqW.2.1.1, (hW₀_iff q hqW.1).2.1 (by simpa using hfq),
      hqW.2.1.2⟩, hqW⟩,
      fun ⟨⟨_, hPq, _⟩, hqW⟩ ↦ ⟨hqW, by simpa using (hW₀_iff q hqW.1).2.2 hPq⟩⟩
  rw [hset]
  exact (isOpenMap_domRestrict_fst_monicOfCoeff_psc_ne_zero hU_a ha_on
    hδlt).domRestrict_inter hW_open

/-- Origin form of Lemma 7 on `(Fin m → ℝ) × ℝ`, proved by induction on `m`. -/
private theorem exists_analyticOnNhd_isOpenMap_domRestrict_fst_origin :
    ∀ {m : ℕ} {f : (Fin m → ℝ) × ℝ → ℝ} {V : Set ((Fin m → ℝ) × ℝ)},
      AnalyticAt ℝ f (0, 0) → ¬(fun t ↦ f (0, t)) =ᶠ[𝓝 0] 0 → V ∈ 𝓝 (0, 0) →
      ∃ (g : (Fin m → ℝ) × ℝ → ℝ) (W : Set ((Fin m → ℝ) × ℝ)),
        IsOpen W ∧ (0, 0) ∈ W ∧ W ⊆ V ∧ AnalyticOnNhd ℝ g W ∧ ¬(fun t ↦ g (0, t)) =ᶠ[𝓝 0] 0 ∧
        IsOpenMap ({q ∈ W | f q * g q = 0}.domRestrict Prod.fst)
  | 0, _, V, _, _, hV => by
    refine ⟨fun _ ↦ 1, interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV,
      interior_subset, fun _ _ ↦ analyticAt_const, fun h ↦ one_ne_zero h.self_of_nhds,
      fun U _ ↦ ?_⟩
    rcases (_ '' U).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
    · exact h ▸ isOpen_empty
    · convert isOpen_univ
      exact eq_univ_of_forall fun y ↦ Subsingleton.elim y y₀ ▸ hy₀
  | m + 1, f, V, hf, hf₀, hV => by
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1
      (fun h ↦ hf₀ (analyticOrderAt_eq_top.1 h) : analyticOrderAt (fun t ↦ f (0, t)) 0 ≠ ⊤)
    rcases d.eq_zero_or_pos with rfl | hd_pos
    · have hf00 : f (0, 0) ≠ 0 :=
        hf.curry_right.analyticOrderAt_eq_zero.1 (by simpa using hd.symm)
      let W := interior (V ∩ {q | f q ≠ 0})
      refine ⟨fun _ ↦ 1, W, isOpen_interior,
        mem_interior_iff_mem_nhds.2 (inter_mem hV (hf.continuousAt.eventually_ne hf00)),
        interior_subset.trans inter_subset_left, fun _ _ ↦ analyticAt_const,
        fun h ↦ one_ne_zero h.self_of_nhds, ?_⟩
      have : IsEmpty {q : (Fin (m + 1) → ℝ) × ℝ // q ∈ {q ∈ W | f q * 1 = 0}} :=
        ⟨fun ⟨q, hqW, hq0⟩ ↦ (interior_subset hqW).2 (by simpa using hq0)⟩
      exact IsOpenMap.of_isEmpty _
    · obtain ⟨a, u_f, ha, ha0, hu_f, hu_f0, hf_eq⟩ := hf.exists_weierstrassPreparation_real hd.symm
      obtain ⟨k, U_a, -, hU_a, h0U_a, ha_on, hk_ne, hδlt⟩ :=
        exists_lt_psc_monicOfCoeff_derivative_not_eventuallyEq_zero hd_pos ha
      let P : (Fin (m + 1) → ℝ) → ℝ[X] := fun x ↦ monicOfCoeff fun i ↦ a i x
      let W₀ := interior (V ∩ {q | f q = (P q.1).eval q.2 * u_f q ∧ u_f q ≠ 0}) ∩ U_a ×ˢ univ
      have hW₀_open : IsOpen W₀ := isOpen_interior.inter (hU_a.prod isOpen_univ)
      have h0W₀ : (0, 0) ∈ W₀ := ⟨mem_interior_iff_mem_nhds.2
        (inter_mem hV ((hf_eq.mono fun q hq ↦ by simpa using hq).and
          (hu_f.continuousAt.eventually_ne hu_f0))), h0U_a, trivial⟩
      have hW₀V : W₀ ⊆ V := inter_subset_left.trans (interior_subset.trans inter_subset_left)
      have hW₀_iff (q) (hq : q ∈ W₀) : q.1 ∈ U_a ∧ (f q = 0 ↔ (P q.1).eval q.2 = 0) :=
        ⟨hq.2.1, by
          rw [(interior_subset hq.1).2.1, mul_eq_zero, or_iff_left (interior_subset hq.1).2.2]⟩
      by_cases hk0 : psc (P 0) (P 0).derivative d (d - 1) k = 0
      · exact exists_isOpenMap_domRestrict_fst_origin_succ_of_psc_zero
          exists_analyticOnNhd_isOpenMap_domRestrict_fst_origin ha ha0 hU_a ha_on hδlt hk_ne hk0
          hW₀_open h0W₀ hW₀V hW₀_iff
      · exact exists_isOpenMap_domRestrict_fst_origin_succ_of_psc_ne_zero hU_a h0U_a ha_on
          hδlt hk0 hW₀_open h0W₀ hW₀V hW₀_iff

end Helpers

end TauCeti

namespace AnalyticAt

/-- **Łojasiewicz's open-projection hypersurface lemma (Lemma 7, `Prod.fst` form).** Let `E` be a
finite-dimensional real normed space, let `f : E × ℝ → ℝ` be real analytic at `p` with vertical
slice `t ↦ f (p.1, t)` not identically zero near `p.2`, and let `V ∈ 𝓝 p`. Then there exist an open
connected neighborhood `W ⊆ V` of `p` and a function `g : E × ℝ → ℝ` analytic on `W` whose vertical
slice `t ↦ g (p.1, t)` is not identically zero near `p.2`, such that the zero set
`{q ∈ W | f q * g q = 0}` has open restricted projection `Prod.fst` to `E`. -/
theorem exists_analyticOnNhd_isOpenMap_domRestrict_fst_mul_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E × ℝ → ℝ} {p : E × ℝ}
    (hf : AnalyticAt ℝ f p) (hf₀ : ¬(fun t ↦ f (p.1, t)) =ᶠ[𝓝 p.2] 0) {V : Set (E × ℝ)}
    (hV : V ∈ 𝓝 p) :
    ∃ (g : E × ℝ → ℝ) (W : Set (E × ℝ)),
      IsOpen W ∧ IsConnected W ∧ p ∈ W ∧ W ⊆ V ∧ AnalyticOnNhd ℝ g W ∧
      ¬(fun t ↦ g (p.1, t)) =ᶠ[𝓝 p.2] 0 ∧
      IsOpenMap ({q ∈ W | f q * g q = 0}.domRestrict Prod.fst) := by
  let φ : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (LinearEquiv.ofFinrankEq _ E (Module.finrank_fin_fun ℝ)).toContinuousLinearEquiv
  let e₁ : (Fin (Module.finrank ℝ E) → ℝ) ≃ₜ E := φ.toHomeomorph.trans (Homeomorph.addRight p.1)
  let e₂ : ℝ ≃ₜ ℝ := Homeomorph.addRight p.2
  let e := e₁.prodCongr e₂
  have he₁0 : e₁ 0 = p.1 := by simp [e₁]
  have he₂0 : e₂ 0 = p.2 := zero_add p.2
  have he0 : e (0, 0) = p := Prod.ext he₁0 he₂0
  have he_an (q) : AnalyticAt ℝ e q :=
    (((φ.analyticAt q.1).comp analyticAt_fst).add analyticAt_const).prod
      (analyticAt_snd.add analyticAt_const)
  have he_symm_an (q) : AnalyticAt ℝ e.symm q :=
    ((φ.symm.analyticAt _).comp (analyticAt_fst.add analyticAt_const)).prod
      (analyticAt_snd.add analyticAt_const)
  have hf_e : AnalyticAt ℝ (f ∘ e) (0, 0) := hf.comp_of_eq (he_an (0, 0)) he0
  have hf₀_e : ¬(fun t ↦ (f ∘ e) (0, t)) =ᶠ[𝓝 0] 0 := fun h ↦ hf₀ <| by
    have h0 : e₂.symm p.2 = 0 := by rw [← he₂0, e₂.symm_apply_apply]
    have ht : Tendsto e₂.symm (𝓝 p.2) (𝓝 0) := h0 ▸ e₂.symm.continuous.continuousAt.tendsto
    exact (ht.eventually h).mono fun t ht' ↦ by simpa [e, he₁0] using ht'
  have hV_e : e ⁻¹' V ∈ 𝓝 (0, 0) :=
    e.continuous.continuousAt.preimage_mem_nhds (he0.symm ▸ hV)
  obtain ⟨g₀, W₀, hW₀_open, h0W₀, hW₀V, hg₀_an, hg₀_slice, hZ₀⟩ :=
    TauCeti.exists_analyticOnNhd_isOpenMap_domRestrict_fst_origin hf_e hf₀_e hV_e
  let W₁ := e.symm ⁻¹' W₀
  have hW₁_open : IsOpen W₁ := hW₀_open.preimage e.symm.continuous
  have hpW₁ : p ∈ W₁ := by simpa [W₁, ← he0] using h0W₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW₁_open p hpW₁
  let W := Metric.ball p r
  let g := g₀ ∘ e.symm
  have hg_slice : ¬(fun t ↦ g (p.1, t)) =ᶠ[𝓝 p.2] 0 := fun h ↦ hg₀_slice <| by
    have ht : Tendsto e₂ (𝓝 0) (𝓝 p.2) := he₂0 ▸ e₂.continuous.continuousAt.tendsto
    exact (ht.eventually h).mono fun t ht' ↦ by simpa [g, e, ← he₁0] using ht'
  refine ⟨g, W, Metric.isOpen_ball, ⟨⟨p, Metric.mem_ball_self hr⟩,
    (convex_ball p r).isPreconnected⟩, Metric.mem_ball_self hr,
    hball.trans fun q hq ↦ by simpa [W₁] using hW₀V hq,
    fun q hq ↦ (hg₀_an _ (hball hq)).comp (he_symm_an q), hg_slice, ?_⟩
  have hset : {q ∈ W | f q * g q = 0} =
      e.symm ⁻¹' {q ∈ W₀ | (f ∘ e) q * g₀ q = 0} ∩ W := by
    ext q
    exact ⟨fun ⟨hqW, hfg⟩ ↦ ⟨⟨hball hqW, by simpa [g, Function.comp_def, e.apply_symm_apply]
      using hfg⟩, hqW⟩, fun ⟨⟨_, hfg⟩, hqW⟩ ↦ ⟨hqW, by
      simpa [g, Function.comp_def, e.apply_symm_apply] using hfg⟩⟩
  rw [hset]
  exact (hZ₀.domRestrict_fst_preimage_prodCongr e₁.symm e₂.symm).domRestrict_inter
    Metric.isOpen_ball

/-- **Łojasiewicz's open-projection hypersurface lemma (Lemma 7, `Fin.tail` cylinder form).** Let
`f : (Fin (n + 1) → ℝ) → ℝ` be real analytic at `v` with vertical slice
`t ↦ f (Fin.cons t (Fin.tail v))` not identically zero near `v 0`, and let `V ∈ 𝓝 v`. Then there
exist an open connected neighborhood `W ⊆ V` of `v` and a function `g` analytic on `W` whose
vertical slice `t ↦ g (Fin.cons t (Fin.tail v))` is not identically zero near `v 0`, such that the
zero set `{w ∈ W | f w * g w = 0}` has open restricted projection `Fin.tail` to `Fin n → ℝ`. -/
theorem exists_analyticOnNhd_isOpenMap_domRestrict_tail_mul_eq_zero {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} {v : Fin (n + 1) → ℝ} (hf : AnalyticAt ℝ f v)
    (hf₀ : ¬(fun t ↦ f (Fin.cons t (Fin.tail v))) =ᶠ[𝓝 (v 0)] 0) {V : Set (Fin (n + 1) → ℝ)}
    (hV : V ∈ 𝓝 v) :
    ∃ (g : (Fin (n + 1) → ℝ) → ℝ) (W : Set (Fin (n + 1) → ℝ)),
      IsOpen W ∧ IsConnected W ∧ v ∈ W ∧ W ⊆ V ∧ AnalyticOnNhd ℝ g W ∧
      ¬(fun t ↦ g (Fin.cons t (Fin.tail v))) =ᶠ[𝓝 (v 0)] 0 ∧
      IsOpenMap ({w ∈ W | f w * g w = 0}.domRestrict Fin.tail) := by
  let e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin n → ℝ) × ℝ :=
    (Fin.consEquivL ℝ fun _ ↦ ℝ).symm.trans (ContinuousLinearEquiv.prodComm ℝ ℝ (Fin n → ℝ))
  have he (w : Fin (n + 1) → ℝ) : e w = (Fin.tail w, w 0) := rfl
  have he_symm (p : (Fin n → ℝ) × ℝ) : e.symm p = Fin.cons p.2 p.1 := by
    ext i
    simp [e, Fin.consEquivL_apply]
  have hf_e : AnalyticAt ℝ (f ∘ e.symm) (e v) :=
    hf.comp_of_eq (e.symm.analyticAt (e v)) (e.symm_apply_apply v)
  have hf₀_e : ¬(fun t ↦ (f ∘ e.symm) ((e v).1, t)) =ᶠ[𝓝 (e v).2] 0 := by
    simpa [Function.comp_def, he, he_symm] using hf₀
  have hV_e : e.symm ⁻¹' V ∈ 𝓝 (e v) := by
    have hV' : V ∈ 𝓝 (e.symm (e v)) := by rwa [e.symm_apply_apply]
    exact e.symm.continuous.continuousAt.preimage_mem_nhds hV'
  obtain ⟨g₀, W₀, hW₀_open, hW₀_conn, hvW₀, hW₀V, hg₀_an, hg₀_slice, hZ₀⟩ :=
    hf_e.exists_analyticOnNhd_isOpenMap_domRestrict_fst_mul_eq_zero hf₀_e hV_e
  let W := e ⁻¹' W₀
  let g := g₀ ∘ e
  have hW_img : W = e.symm '' W₀ := (ContinuousLinearEquiv.image_eq_preimage_symm e.symm W₀).symm
  refine ⟨g, W, hW₀_open.preimage e.continuous,
    hW_img ▸ hW₀_conn.image _ e.symm.continuous.continuousOn, hvW₀,
    fun w hw ↦ by simpa only [mem_preimage, e.symm_apply_apply] using hW₀V hw,
    fun w hw ↦ (hg₀_an _ hw).comp (e.analyticAt w), ?_, ?_⟩
  · intro h
    apply hg₀_slice
    filter_upwards [h] with t ht
    simpa [g, he, Fin.tail_cons, Fin.cons_zero] using ht
  · have hset : {w ∈ W | f w * g w = 0} =
        {w : Fin (n + 1) → ℝ | (Fin.tail w, w 0) ∈ {q ∈ W₀ | (f ∘ e.symm) q * g₀ q = 0}} := by
      ext w
      exact ⟨fun ⟨hw, hfg⟩ ↦ ⟨hw, by simpa [g, Function.comp_def, ← he w, e.symm_apply_apply]
        using hfg⟩, fun ⟨hw, hfg⟩ ↦ ⟨hw, by
        simpa [g, Function.comp_def, ← he w, e.symm_apply_apply] using hfg⟩⟩
    rw [hset]
    exact TauCeti.isOpenMap_domRestrict_tail_preimage_iff.2 hZ₀

end AnalyticAt

end
