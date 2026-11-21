/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import TauCeti.Order.Filter.Germ.MvPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Rings of analytic function germs

`TauCeti.analyticGerms 𝕜 a` is the subring of function germs at `a` represented by functions
analytic at `a`. Equality is ordinary equality of germs, so restriction to smaller neighborhoods
requires no additional identifications. Analytic maps induce ring homomorphisms by pullback.
These rings allow operations on local analytic functions to be compared independently of the
representatives and neighborhoods used to construct them. Locally inverse analytic maps give
ring equivalences (`TauCeti.analyticGerms.equivOfInverse`), without choosing representatives.
The subring construction follows `TauCeti.meromorphicGerms`, using ordinary neighborhoods and
`AnalyticAt` in place of punctured neighborhoods and `MeromorphicAt`. The local-inverse
construction is analogous to `OpenPartialHomeomorph.meromorphicGermsEquiv`.

Over any normed space over a nontrivially normed field, `TauCeti.analyticGerms 𝕜 a` is an integral
domain (`IsDomain (analyticGerms 𝕜 a)`): restricting power series to lines reduces zero-divisor
cancellation to the one-dimensional isolated-zeros principle. On finite coordinate spaces `σ → 𝕜`,
coordinate polynomials act on analytic germs as polynomial functions
(`TauCeti.analyticGerms.mvPolynomialAlgebra`), mirroring `Filter.Germ.mvPolynomialAlgebra` so that
algebraicity of an analytic germ over `MvPolynomial σ 𝕜` characterizes local polynomial relations
(`TauCeti.analyticGerms.isAlgebraic_ofAnalyticAt_iff`).
-/

public section

open Filter Topology

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The ring of scalar analytic germs at `a`, inside the ring of all function germs. -/
def analyticGerms (a : E) : Subring (Germ (𝓝 a) 𝕜) where
  carrier := {φ | ∃ f : E → 𝕜, AnalyticAt 𝕜 f a ∧ (f : Germ (𝓝 a) 𝕜) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

variable {𝕜} {a : E} {b : F}

/-- Membership in the analytic germ ring means having an analytic representative. -/
theorem mem_analyticGerms_iff {φ : Germ (𝓝 a) 𝕜} :
    φ ∈ analyticGerms 𝕜 a ↔ ∃ f : E → 𝕜, AnalyticAt 𝕜 f a ∧ (f : Germ (𝓝 a) 𝕜) = φ :=
  Iff.rfl

/-- A function has an analytic germ exactly when it is analytic at the base point. -/
@[simp]
theorem coe_mem_analyticGerms {f : E → 𝕜} :
    (f : Germ (𝓝 a) 𝕜) ∈ analyticGerms 𝕜 a ↔ AnalyticAt 𝕜 f a :=
  ⟨fun ⟨_, hg, hgf⟩ ↦ hg.congr (Germ.coe_eq.1 hgf), fun hf ↦ ⟨f, hf, rfl⟩⟩

namespace analyticGerms

/-- The germ of a function analytic at the base point. -/
def ofAnalyticAt (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a) : analyticGerms 𝕜 a :=
  ⟨f, coe_mem_analyticGerms.2 hf⟩

@[simp]
theorem coe_ofAnalyticAt (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a) :
    ((ofAnalyticAt f hf : analyticGerms 𝕜 a) : Germ (𝓝 a) 𝕜) = f := (rfl)

/-- The zero function represents the zero analytic germ. -/
@[simp]
theorem ofAnalyticAt_zero :
    ofAnalyticAt (0 : E → 𝕜) (a := a) analyticAt_const = 0 := (rfl)

/-- The constant one function represents the unit analytic germ. -/
@[simp]
theorem ofAnalyticAt_one :
    ofAnalyticAt (1 : E → 𝕜) (a := a) analyticAt_const = 1 := (rfl)

/-- Taking analytic germs preserves addition. -/
@[simp]
theorem ofAnalyticAt_add (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f a)
    (hg : AnalyticAt 𝕜 g a) :
    ofAnalyticAt (f + g) (hf.add hg) = ofAnalyticAt f hf + ofAnalyticAt g hg := (rfl)

/-- Taking analytic germs preserves multiplication. -/
@[simp]
theorem ofAnalyticAt_mul (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f a)
    (hg : AnalyticAt 𝕜 g a) :
    ofAnalyticAt (f * g) (hf.mul hg) = ofAnalyticAt f hf * ofAnalyticAt g hg := (rfl)

/-- Taking analytic germs preserves negation. -/
@[simp]
theorem ofAnalyticAt_neg (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a) :
    ofAnalyticAt (-f) hf.neg = -ofAnalyticAt f hf := (rfl)

/-- Taking analytic germs preserves subtraction. -/
@[simp]
theorem ofAnalyticAt_sub (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f a)
    (hg : AnalyticAt 𝕜 g a) :
    ofAnalyticAt (f - g) (hf.sub hg) = ofAnalyticAt f hf - ofAnalyticAt g hg := (rfl)

/-- Two analytic representatives define the same germ exactly when they agree near the base
point. -/
@[simp]
theorem ofAnalyticAt_eq_ofAnalyticAt_iff {f g : E → 𝕜}
    {hf : AnalyticAt 𝕜 f a} {hg : AnalyticAt 𝕜 g a} :
    ofAnalyticAt f hf = ofAnalyticAt g hg ↔ f =ᶠ[𝓝 a] g := by
  rw [Subtype.ext_iff, coe_ofAnalyticAt, coe_ofAnalyticAt, Germ.coe_eq]

/-- An analytic representative defines the zero germ exactly when it vanishes near the base
point. -/
@[simp]
theorem ofAnalyticAt_eq_zero_iff {f : E → 𝕜} {hf : AnalyticAt 𝕜 f a} :
    ofAnalyticAt f hf = 0 ↔ f =ᶠ[𝓝 a] 0 := by
  rw [Subtype.ext_iff, coe_ofAnalyticAt, Subring.coe_zero, ← Germ.coe_zero, Germ.coe_eq]

/-- Eventually equal analytic functions represent the same analytic germ. -/
theorem ofAnalyticAt_congr {f g : E → 𝕜} {hf : AnalyticAt 𝕜 f a}
    {hg : AnalyticAt 𝕜 g a} (h : f =ᶠ[𝓝 a] g) :
    ofAnalyticAt f hf = ofAnalyticAt g hg :=
  ofAnalyticAt_eq_ofAnalyticAt_iff.2 h

/-- Pullback of scalar analytic germs along a map analytic at the base point. -/
def pullback (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b) :
    analyticGerms 𝕜 b →+* analyticGerms 𝕜 a where
  toFun φ := ⟨(φ : Germ (𝓝 b) 𝕜).compTendsto g (hga ▸ hg.continuousAt.tendsto), by
    obtain ⟨f, hf, hφ⟩ := φ.property
    rw [← hφ, Germ.coe_compTendsto, coe_mem_analyticGerms]
    exact hf.comp_of_eq hg hga⟩
  map_zero' := Subtype.ext <| Germ.const_compTendsto 0 (hga ▸ hg.continuousAt.tendsto)
  map_one' := Subtype.ext <| Germ.const_compTendsto 1 (hga ▸ hg.continuousAt.tendsto)
  map_add' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := φ.property
    obtain ⟨g, hg, hψ⟩ := ψ.property
    apply Subtype.ext
    simp only [Subring.coe_add, ← hφ, ← hψ, ← Germ.coe_add, Germ.coe_compTendsto]
    rfl
  map_mul' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := φ.property
    obtain ⟨g, hg, hψ⟩ := ψ.property
    apply Subtype.ext
    simp only [Subring.coe_mul, ← hφ, ← hψ, ← Germ.coe_mul, Germ.coe_compTendsto]
    rfl

@[simp]
theorem coe_pullback (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (φ : analyticGerms 𝕜 b) :
    ((pullback g hg hga φ : analyticGerms 𝕜 a) : Germ (𝓝 a) 𝕜) =
      (φ : Germ (𝓝 b) 𝕜).compTendsto g (hga ▸ hg.continuousAt.tendsto) := (rfl)

/-- Pullback sends the germ of `f` to the germ of its composition. -/
@[simp]
theorem pullback_ofAnalyticAt (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (f : F → 𝕜) (hf : AnalyticAt 𝕜 f b) :
    pullback g hg hga (ofAnalyticAt f hf) = ofAnalyticAt (f ∘ g) (hf.comp_of_eq hg hga) :=
  Subtype.ext (by rw [coe_pullback, coe_ofAnalyticAt, coe_ofAnalyticAt,
    Germ.coe_compTendsto])

/-- Every analytic germ is the germ of an analytic function. -/
theorem exists_ofAnalyticAt (φ : analyticGerms 𝕜 a) :
    ∃ (f : E → 𝕜) (hf : AnalyticAt 𝕜 f a), ofAnalyticAt f hf = φ := by
  obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.property
  exact ⟨f, hf, Subtype.ext (by rw [coe_ofAnalyticAt, hφ])⟩

/-- Pullback along the identity fixes each analytic germ. -/
@[simp]
theorem pullback_id (φ : analyticGerms 𝕜 a) (h : id a = a) :
    pullback (b := a) id analyticAt_id h φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt]
  rfl

/-- Pullback depends only on the germ of the analytic map. -/
theorem pullback_congr {g g' : E → F} (hg : AnalyticAt 𝕜 g a) (hg' : AnalyticAt 𝕜 g' a)
    (hga : g a = b) (hg'a : g' a = b) (h : g =ᶠ[𝓝 a] g') :
    pullback g hg hga = pullback g' hg' hg'a := by
  apply RingHom.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt]
  exact ofAnalyticAt_congr (h.fun_comp f)

/-- Pullbacks compose in the opposite order to analytic maps. -/
@[simp]
theorem pullback_pullback {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {c : G} (g : E → F) (hg : AnalyticAt 𝕜 g a) (hga : g a = b)
    (h : F → G) (hh : AnalyticAt 𝕜 h b) (hhb : h b = c) (φ : analyticGerms 𝕜 c) :
    pullback g hg hga (pullback h hh hhb φ) =
      pullback (h ∘ g) (hh.comp_of_eq hg hga) (by rw [Function.comp_apply, hga, hhb]) φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt, pullback_ofAnalyticAt]
  rfl

/-- Locally inverse analytic maps identify the scalar analytic germ rings at corresponding
points, contravariantly. Only inverse identities near the two base points are required. -/
def equivOfInverse (g : E → F) (h : F → E)
    (hg : AnalyticAt 𝕜 g a) (hh : AnalyticAt 𝕜 h b) (hga : g a = b)
    (hleft : h ∘ g =ᶠ[𝓝 a] id) (hright : g ∘ h =ᶠ[𝓝 b] id) :
    analyticGerms 𝕜 b ≃+* analyticGerms 𝕜 a where
  toFun := pullback g hg hga
  invFun := pullback h hh (hga ▸ hleft.self_of_nhds)
  map_mul' := map_mul (pullback g hg hga)
  map_add' := map_add (pullback g hg hga)
  left_inv φ := by
    obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
    rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt]
    exact ofAnalyticAt_congr (hright.fun_comp f)
  right_inv φ := by
    obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
    rw [pullback_ofAnalyticAt, pullback_ofAnalyticAt]
    exact ofAnalyticAt_congr (hleft.fun_comp f)

/-- Transport by locally inverse analytic maps is analytic pullback. -/
@[simp]
theorem equivOfInverse_apply (g : E → F) (h : F → E)
    (hg : AnalyticAt 𝕜 g a) (hh : AnalyticAt 𝕜 h b) (hga : g a = b)
    (hleft : h ∘ g =ᶠ[𝓝 a] id) (hright : g ∘ h =ᶠ[𝓝 b] id)
    (φ : analyticGerms 𝕜 b) :
    equivOfInverse g h hg hh hga hleft hright φ = pullback g hg hga φ := (rfl)

/-- Inverse transport is pullback by the local inverse. -/
@[simp]
theorem equivOfInverse_symm_apply (g : E → F) (h : F → E)
    (hg : AnalyticAt 𝕜 g a) (hh : AnalyticAt 𝕜 h b) (hga : g a = b)
    (hleft : h ∘ g =ᶠ[𝓝 a] id) (hright : g ∘ h =ᶠ[𝓝 b] id)
    (φ : analyticGerms 𝕜 a) :
    (equivOfInverse g h hg hh hga hleft hright).symm φ =
      pullback h hh (hga ▸ hleft.self_of_nhds) φ := (rfl)

/-- The ring of scalar analytic germs is nontrivial because `0 ≠ 1` in the base field. -/
instance : Nontrivial (analyticGerms 𝕜 a) :=
  ⟨⟨ofAnalyticAt 0 analyticAt_const, ofAnalyticAt 1 analyticAt_const, fun h ↦
    zero_ne_one (ofAnalyticAt_eq_ofAnalyticAt_iff.1 h).self_of_nhds⟩⟩

/-- The ring of scalar analytic germs has no zero divisors: restricting power series to a line
through `a` along which both series have nonzero terms reduces to the one-dimensional
isolated-zeros principle. -/
instance : NoZeroDivisors (analyticGerms 𝕜 a) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} hmul := by
    classical
    obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
    obtain ⟨g, hg, rfl⟩ := exists_ofAnalyticAt ψ
    rw [← ofAnalyticAt_mul, ofAnalyticAt_eq_zero_iff] at hmul
    rw [ofAnalyticAt_eq_zero_iff, ofAnalyticAt_eq_zero_iff]
    by_contra h
    push Not at h
    obtain ⟨hf0, hg0⟩ := h
    obtain ⟨p, rp, hp⟩ := hf
    obtain ⟨q, rq, hq⟩ := hg
    -- Step 1: Extract directions `u, v` where some terms of `p` and `q` do not vanish.
    have hex_term {hfun : E → 𝕜} {s : FormalMultilinearSeries 𝕜 E 𝕜} {rs : ENNReal}
        (hs : HasFPowerSeriesOnBall hfun s a rs) (h0 : ¬ hfun =ᶠ[𝓝 a] 0) :
        ∃ (m : ℕ) (u : E), s m (fun _ ↦ u) ≠ 0 := by
      by_contra hs0
      push Not at hs0
      refine h0 (eventually_of_mem (Metric.eball_mem_nhds a hs.r_pos) fun y hy ↦ ?_)
      have hmem : y - a ∈ Metric.eball 0 rs := by
        simpa [Metric.mem_eball, eDist_eq_eNorm_sub] using hy
      have hsum := hs.hasSum hmem
      simp only [add_sub_cancel, hs0] at hsum
      exact hsum.unique hasSum_zero
    obtain ⟨m, u, hu⟩ := hex_term hp hf0
    obtain ⟨n, v, hv⟩ := hex_term hq hg0
    -- Step 2: Expand `c ↦ L (u + c • v, …, u + c • v)` as a polynomial in `c` to choose a common
    -- direction `w = u + c • v` where both `p m` and `q n` are nonzero.
    have hex_poly {k : ℕ} (L : ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ E) 𝕜) :
        ∃ P : Polynomial 𝕜, (∀ c : 𝕜, P.eval c = L (fun _ ↦ u + c • v)) ∧
          P.coeff k = L (fun _ ↦ v) := by
      refine ⟨∑ s : Finset (Fin k),
        Polynomial.C (L (s.piecewise (fun _ ↦ u) (fun _ ↦ v))) * Polynomial.X ^ sᶜ.card,
        fun c ↦ ?_, ?_⟩
      · have hsum_arg : (fun _ : Fin k ↦ u + c • v) = (fun _ ↦ u) + (fun _ ↦ c • v) := rfl
        rw [hsum_arg, L.map_add_univ, ← Polynomial.coe_evalRingHom, map_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        have hpiece : s.piecewise (fun _ ↦ u) (fun _ ↦ c • v) =
            fun i ↦ (if i ∈ s then (1 : 𝕜) else c) • s.piecewise (fun _ ↦ u) (fun _ ↦ v) i := by
          ext i; by_cases hi : i ∈ s <;> simp [hi]
        rw [hpiece, L.map_smul_univ, Polynomial.coe_evalRingHom, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
        congr 1
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
        congr 2
        ext i
        simp
      · rw [← Polynomial.lcoeff_apply, map_sum, Finset.sum_eq_single ∅]
        · simp
        · intro s _ hs
          rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow, ite_eq_right]
          intro heq
          have hlt : sᶜ.card < k := by
            have := Finset.card_lt_card (s := sᶜ) (t := Finset.univ)
              (by rw [Finset.ssubset_univ_iff]; simpa using hs)
            simpa using this
          exact absurd heq hlt.ne'
        · intro hmem; exact absurd (Finset.mem_univ ∅) hmem
    obtain ⟨P, hP_eval, -⟩ := hex_poly (p m)
    obtain ⟨Q, hQ_eval, hQ_coeff⟩ := hex_poly (q n)
    have hP0 : P ≠ 0 := fun h0 ↦ hu (by simpa [h0] using (hP_eval 0).symm)
    have hQ0 : Q ≠ 0 := fun h0 ↦ hv (by simpa [h0] using hQ_coeff.symm)
    have : Infinite 𝕜 := NontriviallyNormedField.infinite 𝕜
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (P * Q).roots.toFinset
    have hPQc : P.eval c * Q.eval c ≠ 0 := by
      rw [← Polynomial.eval_mul]
      intro h0
      exact hc (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (mul_ne_zero hP0 hQ0)).mpr h0))
    set w : E := u + c • v
    have hpw : p m (fun _ ↦ w) ≠ 0 := (hP_eval c) ▸ left_ne_zero_of_mul hPQc
    have hqw : q n (fun _ ↦ w) ≠ 0 := (hQ_eval c) ▸ right_ne_zero_of_mul hPQc
    -- Step 3: Restrict to `t ↦ a + t • w` and apply the 1D isolated-zeros dichotomy.
    let L : 𝕜 →L[𝕜] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) w
    have shift_line {hfun : E → 𝕜} {s : FormalMultilinearSeries 𝕜 E 𝕜} {rs : ENNReal}
        (hs : HasFPowerSeriesOnBall hfun s a rs) :
        HasFPowerSeriesAt (fun t : 𝕜 ↦ hfun (a + t • w)) (s.compContinuousLinearMap L) 0 := by
      have hshift : HasFPowerSeriesAt (fun y : E ↦ hfun (a + y)) s (L 0) := by
        rw [map_zero]
        exact ⟨rs, ⟨hs.r_le, hs.r_pos, fun hy ↦ by simpa only [zero_add] using hs.hasSum hy⟩⟩
      exact hshift.compContinuousLinearMap
    have hfp := shift_line hp
    have hgq := shift_line hq
    have hmul_line : (fun t : 𝕜 ↦ f (a + t • w)) * (fun t : 𝕜 ↦ g (a + t • w)) =ᶠ[𝓝 0] 0 := by
      have htend : Tendsto (fun t : 𝕜 ↦ a + t • w) (𝓝 0) (𝓝 a) := by
        simpa using (by fun_prop : Continuous fun t : 𝕜 ↦ a + t • w).tendsto 0
      filter_upwards [htend.eventually hmul] with t ht
      exact ht
    rcases hfp.analyticAt.eventually_eq_zero_or_eventually_ne_zero with hfl | hfl
    · have h0 := (hfp.congr hfl).apply_eq_zero m 1
      simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def, L,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at h0
      exact hpw h0
    · rcases hgq.analyticAt.eventually_eq_zero_or_eventually_ne_zero with hgl | hgl
      · have h0 := (hgq.congr hgl).apply_eq_zero n 1
        simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def, L,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at h0
        exact hqw h0
      · have hne : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), f (a + t • w) * g (a + t • w) ≠ 0 :=
          (hfl.and hgl).mono fun t ⟨h1, h2⟩ ↦ mul_ne_zero h1 h2
        have hzero : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), f (a + t • w) * g (a + t • w) = 0 :=
          nhdsWithin_le_nhds hmul_line
        obtain ⟨t, ht1, ht2⟩ := (hne.and hzero).exists
        exact ht1 ht2

/-- The ring of scalar analytic germs is an integral domain. -/
instance : IsDomain (analyticGerms 𝕜 a) :=
  NoZeroDivisors.to_isDomain _

section MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- Coordinate polynomials act on analytic germs at `a : σ → 𝕜` as polynomial functions:
`p` acts as the analytic germ of `y ↦ MvPolynomial.eval y p`. -/
@[instance_reducible]
noncomputable def mvPolynomialAlgebra (a : σ → 𝕜) :
    Algebra (MvPolynomial σ 𝕜) (analyticGerms 𝕜 a) :=
  RingHom.toAlgebra
    { toFun p := ofAnalyticAt (fun y ↦ MvPolynomial.eval y p)
        (AnalyticAt.aeval_mvPolynomial (f := id)
          (fun i ↦ (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i).analyticAt a) p)
      map_one' := Subtype.ext (Germ.coe_eq.2 (.of_forall fun _ ↦ map_one _))
      map_mul' _ _ := Subtype.ext (Germ.coe_eq.2 (.of_forall fun _ ↦ map_mul _ _ _))
      map_zero' := Subtype.ext (Germ.coe_eq.2 (.of_forall fun _ ↦ map_zero _))
      map_add' _ _ := Subtype.ext (Germ.coe_eq.2 (.of_forall fun _ ↦ map_add _ _ _)) }

attribute [local instance] mvPolynomialAlgebra Filter.Germ.mvPolynomialAlgebra

/-- A coordinate polynomial acts on analytic germs as the germ of its polynomial function. -/
theorem coe_mvPolynomialAlgebra_algebraMap (a : σ → 𝕜) (p : MvPolynomial σ 𝕜) :
    ((algebraMap (MvPolynomial σ 𝕜) (analyticGerms 𝕜 a) p : analyticGerms 𝕜 a) : Germ (𝓝 a) 𝕜) =
      ((fun y ↦ MvPolynomial.eval y p : (σ → 𝕜) → 𝕜) : Germ (𝓝 a) 𝕜) := by
  rw [RingHom.algebraMap_toAlgebra]
  rfl

/-- Evaluating `P : (MvPolynomial σ 𝕜)[X]` at an analytic germ and coercing to `Germ (𝓝 a) 𝕜`
agrees with evaluating `P` at the coerced germ. -/
theorem coe_aeval {a : σ → 𝕜} (φ : analyticGerms 𝕜 a) (P : Polynomial (MvPolynomial σ 𝕜)) :
    ((Polynomial.aeval φ P : analyticGerms 𝕜 a) : Germ (𝓝 a) 𝕜) =
      Polynomial.aeval (φ : Germ (𝓝 a) 𝕜) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Subring.coe_subtype, Polynomial.hom_eval₂]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, Subring.coe_subtype, coe_mvPolynomialAlgebra_algebraMap,
    Filter.Germ.mvPolynomialAlgebra_algebraMap_apply]

/-- An analytic germ is algebraic over `MvPolynomial σ 𝕜` in `analyticGerms 𝕜 a` if and only if
its underlying germ in `Germ (𝓝 a) 𝕜` is algebraic over `MvPolynomial σ 𝕜`. -/
theorem isAlgebraic_iff_coe {a : σ → 𝕜} (φ : analyticGerms 𝕜 a) :
    IsAlgebraic (MvPolynomial σ 𝕜) φ ↔ IsAlgebraic (MvPolynomial σ 𝕜) (φ : Germ (𝓝 a) 𝕜) := by
  simp only [IsAlgebraic, ← Subtype.coe_inj, coe_aeval, Subring.coe_zero]

/-- The analytic germ of `f` is algebraic over the coordinate polynomials exactly when `f`
satisfies a nonzero polynomial relation `P (y, f y) = 0` near `a`. -/
theorem isAlgebraic_ofAnalyticAt_iff {a : σ → 𝕜} {f : (σ → 𝕜) → 𝕜} {hf : AnalyticAt 𝕜 f a} :
    IsAlgebraic (MvPolynomial σ 𝕜) (ofAnalyticAt f hf) ↔
      ∃ P : Polynomial (MvPolynomial σ 𝕜), P ≠ 0 ∧
        ∀ᶠ y in 𝓝 a, (P.map (MvPolynomial.eval y)).eval (f y) = 0 := by
  rw [isAlgebraic_iff_coe, coe_ofAnalyticAt, Filter.Germ.isAlgebraic_coe_iff]

end MvPolynomial

end analyticGerms

end TauCeti
