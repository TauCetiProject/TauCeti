/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Germ
public import TauCeti.Analysis.Complex.RealDeriv
public import TauCeti.Topology.ContinuousMap.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Perfect

/-!
# Restrictions to a set of functions holomorphic near it

For `s : Set ℂ`, a germ in `holomorphicGerms s` is represented by a function holomorphic on some
open neighbourhood of `s`, the neighbourhood depending on the germ. Its values on `s` form a
continuous function on `s`, and the value map `holomorphicGerms.toContinuousMap s` is a complex
algebra homomorphism `holomorphicGerms s →ₐ[ℂ] C(s, ℂ)`. Its range
`holomorphicRestrictions s`, written `O(s)`, is the algebra of restrictions to `s` of functions
holomorphic near `s`. For compact `s` this is the space in which Runge approximation is stated:
the restrictions of functions holomorphic on a larger open set `Ω` are then asked to be dense in
`O(s)` for its sup-norm topology. Being in `O(s)` is stronger than being continuous on `s` and
holomorphic on its interior.

The value map forgets the germ away from `s`. It is injective exactly when `s` has no isolated
point (`holomorphicGerms.toContinuousMap_injective_iff`), so for instance on every connected set
with two points, such as a closed disc, while on `{c}` the germs of `z ↦ z - c` and of `0` have
the same value. For finite `s`, Lagrange interpolation (`polynomialFunctions.eq_top_of_finite`)
shows `O(s) = C(s, ℂ)`.

The algebra `O(s)` is neither open nor closed in general. As soon as `s` has interior, the
small multiples `ε • conj z` of the conjugate coordinate tend to `0` without ever lying in
`O(s)`, so `O(s)` is not open (`not_isOpen_holomorphicRestrictions`). For the closed unit
disc a uniform limit of polynomials outside `O(s)` shows that it is not closed either; this
example is in `TauCeti.Analysis.Complex.Germ.HolomorphicRestrictions.NotClosed`.

## Main definitions

* `TauCeti.holomorphicGerms.toContinuousMap s`: the value map on germs near `s`.
* `TauCeti.holomorphicRestrictions s`: its range `O(s)`, a subalgebra of `C(s, ℂ)`.

## Main results

* `TauCeti.mem_holomorphicRestrictions_iff_exists_open`: a continuous function on `s` lies in
  `O(s)` exactly when it agrees on `s` with a function holomorphic on an open set containing `s`.
* `TauCeti.comp_inclusion_mem_holomorphicRestrictions`: restriction to a smaller set preserves
  `O(·)`, and `TauCeti.HolomorphicFunctions.comp_inclusion_mem_holomorphicRestrictions`: the
  restriction to `s` of a holomorphic function on an open `U ⊇ s` lies in `O(s)`.
* `TauCeti.holomorphicRestrictions_coe_opens`: on an open set `U`, `O(U)` is
  `holomorphicFunctions U`, so restricting an element of `O(s)` to an open `U ⊆ s` gives a
  holomorphic function (`TauCeti.comp_inclusion_mem_holomorphicFunctions`).
* `TauCeti.holomorphicGerms.toContinuousMap_injective_iff`: injectivity of the value map.
* `TauCeti.holomorphicRestrictions_eq_top_of_finite`: `O(s) = C(s, ℂ)` for finite `s`.
* `TauCeti.not_isOpen_holomorphicRestrictions`: `O(s)` is not open when `s` has interior.

## References

* A. Rainer, *Advanced Complex Analysis*, §11 (the algebra of functions holomorphic near a
  compact set, in which Runge's theorem is formulated).
-/

public noncomputable section

open Filter Set Topology TopologicalSpace ComplexConjugate

namespace TauCeti

namespace holomorphicGerms

variable {s t : Set ℂ}

/-- The value map: a germ near `s` is sent to the continuous function `x ↦ g(x)` on `s`. -/
def toContinuousMap (s : Set ℂ) : holomorphicGerms s →ₐ[ℂ] C(s, ℂ) where
  toFun g := ⟨fun x ↦ eval (x : ℂ) x.property g, by
    obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    simp only [eval_ofFun]
    exact hf.continuousOn.domRestrict⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  commutes' _ := by ext; simp

@[simp]
theorem toContinuousMap_apply (g : holomorphicGerms s) (x : s) :
    toContinuousMap s g x = eval (x : ℂ) x.property g := (rfl)

theorem toContinuousMap_ofFun (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s) (x : s) :
    toContinuousMap s (ofFun f hf) x = f x := by
  simp

/-- Restricting a germ to a smaller set restricts its values. -/
@[simp]
theorem toContinuousMap_restrict (h : t ⊆ s) (g : holomorphicGerms s) :
    toContinuousMap t (restrict h g) = (toContinuousMap s g).comp (ContinuousMap.inclusion h) := by
  ext
  simp

/-- The values on `s` of the germ of a holomorphic function on an open `U ⊇ s` are the
restriction of that function. -/
@[simp]
theorem toContinuousMap_toGerm {U : Opens ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U) :
    toContinuousMap s (HolomorphicFunctions.toGerm hs f) =
      (f : C(U, ℂ)).comp (ContinuousMap.inclusion hs) := by
  ext x
  simp only [toContinuousMap_apply, HolomorphicFunctions.eval_toGerm, ContinuousMap.comp_apply]
  exact congrArg f.val (Subtype.ext (ContinuousMap.inclusion_apply_coe hs x).symm)

/-- The value map is injective when every point of `s` is an accumulation point of `s`. -/
theorem toContinuousMap_injective (hs : Preperfect s) : Function.Injective (toContinuousMap s) := by
  refine (injective_iff_map_eq_zero _).mpr fun g hg ↦ ?_
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  have h0 : ∀ y ∈ s, f y = 0 := fun y hy ↦ by
    simpa using DFunLike.congr_fun hg ⟨y, hy⟩
  rw [ofFun_eq_zero_iff hf]
  exact eventually_nhdsSet_iff_forall.mpr fun x hx ↦
    (hf x hx).frequently_zero_iff_eventually_zero.mp
      ((accPt_iff_frequently_nhdsNE.mp (hs x hx)).mono h0)

/-- At an isolated point `x` of `s`, the function equal to `z - x` near `x` and to `0` elsewhere
is holomorphic near `s`, vanishes on `s`, and has nonzero germ. -/
private theorem exists_ne_zero_of_not_accPt {x : ℂ} (hx : x ∈ s) (hacc : ¬AccPt x (𝓟 s)) :
    ∃ (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s), (∀ y ∈ s, f y = 0) ∧ ofFun f hf ≠ 0 := by
  rw [accPt_iff_nhds] at hacc
  push Not at hacc
  obtain ⟨U, hU, hUs⟩ := hacc
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  -- Points of `s` other than `x` stay at distance at least `r` from `x`.
  have hfar : ∀ y ∈ s, y ≠ x → r ≤ dist y x := fun y hy hyx ↦
    not_lt.mp fun h ↦ hyx (hUs y ⟨hrU h, hy⟩)
  set f : ℂ → ℂ := (Metric.ball x (r / 2)).indicator fun z ↦ z - x with hf_def
  have hnear : f =ᶠ[𝓝 x] fun z ↦ z - x := by
    filter_upwards [Metric.ball_mem_nhds x (half_pos hr)] with z hz
    exact indicator_of_mem hz _
  have hf : AnalyticOnNhd ℂ f s := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      exact (analyticAt_id.sub analyticAt_const).congr hnear.symm
    · refine analyticAt_const.congr (f := fun _ ↦ (0 : ℂ)) ?_
      filter_upwards [Metric.ball_mem_nhds y (half_pos hr)] with z hz
      refine (indicator_of_notMem (fun hzx ↦ ?_) _).symm
      have := hfar y hy hyx
      have := dist_triangle y z x
      rw [Metric.mem_ball] at hz hzx
      rw [dist_comm] at hz
      linarith
  refine ⟨f, hf, fun y hy ↦ ?_, fun h0 ↦ ?_⟩
  · by_cases hyx : y = x
    · simp [hf_def, hyx]
    · refine indicator_of_notMem (fun hyb ↦ ?_) _
      have := hfar y hy hyx
      rw [Metric.mem_ball] at hyb
      linarith
  · rw [ofFun_eq_zero_iff hf] at h0
    -- Near `x` the function would be both `z - x` and `0`, forcing every nearby point to be `x`.
    have hx0 : ∀ᶠ z in 𝓝 x, z = x := by
      filter_upwards [hnear, h0.filter_mono (nhds_le_nhdsSet hx)] with z hz hz0
      rw [hz0] at hz
      exact (sub_eq_zero.mp hz.symm)
    obtain ⟨z, hzx, hz⟩ := ((hx0.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {x}ᶜ ∈ 𝓝[≠] x)).exists
    exact hz hzx

/-- The value map is injective exactly when `s` has no isolated point. -/
theorem toContinuousMap_injective_iff : Function.Injective (toContinuousMap s) ↔ Preperfect s := by
  refine ⟨fun hinj x hx ↦ ?_, toContinuousMap_injective⟩
  by_contra hacc
  obtain ⟨f, hf, h0, hne⟩ := exists_ne_zero_of_not_accPt hx hacc
  refine hne (hinj ?_)
  ext y
  simpa using h0 y y.property

/-- On a preconnected set with at least two points, such as a closed disc of positive radius, a
germ is determined by its values. -/
theorem toContinuousMap_injective_of_isPreconnected (hs : IsPreconnected s) (hnt : s.Nontrivial) :
    Function.Injective (toContinuousMap s) :=
  toContinuousMap_injective (hs.preperfect_of_nontrivial hnt)

/-- On a single point the value map is not injective. -/
theorem not_injective_toContinuousMap_singleton (c : ℂ) :
    ¬Function.Injective (toContinuousMap {c}) := by
  rw [toContinuousMap_injective_iff]
  intro h
  obtain ⟨y, ⟨-, hy⟩, hyc⟩ := accPt_iff_nhds.mp (h c rfl) univ univ_mem
  exact hyc hy

end holomorphicGerms

variable {s t : Set ℂ}

/-- The algebra `O(s)` of restrictions to `s` of functions holomorphic near `s`: the range of
the value map on `holomorphicGerms s`. -/
def holomorphicRestrictions (s : Set ℂ) : Subalgebra ℂ C(s, ℂ) :=
  (holomorphicGerms.toContinuousMap s).range

/-- The range of the value map on `holomorphicGerms s` is `O(s)`. -/
@[simp]
theorem holomorphicGerms.range_toContinuousMap (s : Set ℂ) :
    (holomorphicGerms.toContinuousMap s).range = holomorphicRestrictions s := (rfl)

/-- The values on `s` of a germ near `s` lie in `O(s)`. -/
@[simp]
theorem holomorphicGerms.toContinuousMap_mem_holomorphicRestrictions (g : holomorphicGerms s) :
    holomorphicGerms.toContinuousMap s g ∈ holomorphicRestrictions s := by
  rw [← holomorphicGerms.range_toContinuousMap]
  exact AlgHom.mem_range_self _ g

/-- A continuous function on `s` lies in `O(s)` exactly when it agrees on `s` with a function
analytic on a neighbourhood of `s`. -/
theorem mem_holomorphicRestrictions_iff {φ : C(s, ℂ)} :
    φ ∈ holomorphicRestrictions s ↔ ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f s ∧ ∀ x : s, f x = φ x := by
  rw [← holomorphicGerms.range_toContinuousMap]
  refine (AlgHom.mem_range _).trans ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
    exact ⟨f, hf, fun x ↦ (holomorphicGerms.toContinuousMap_ofFun f hf x).symm⟩
  · rintro ⟨f, hf, hfφ⟩
    exact ⟨holomorphicGerms.ofFun f hf,
      ContinuousMap.ext fun x ↦ (holomorphicGerms.toContinuousMap_ofFun f hf x).trans (hfφ x)⟩

/-- A continuous function on `s` lies in `O(s)` exactly when it agrees on `s` with a function
holomorphic on some open set containing `s`. -/
theorem mem_holomorphicRestrictions_iff_exists_open {φ : C(s, ℂ)} :
    φ ∈ holomorphicRestrictions s ↔ ∃ (U : Set ℂ) (f : ℂ → ℂ), IsOpen U ∧ s ⊆ U ∧
      DifferentiableOn ℂ f U ∧ ∀ x : s, f x = φ x := by
  rw [mem_holomorphicRestrictions_iff]
  constructor
  · rintro ⟨f, hf, hfφ⟩
    exact ⟨{z | AnalyticAt ℂ f z}, f, isOpen_analyticAt ℂ f, hf,
      fun z hz ↦ hz.differentiableAt.differentiableWithinAt, hfφ⟩
  · rintro ⟨U, f, hU, hsU, hf, hfφ⟩
    exact ⟨f, (hf.analyticOnNhd hU).mono hsU, hfφ⟩

/-- Restriction to a smaller set carries `O(s)` into `O(t)`. -/
theorem comp_inclusion_mem_holomorphicRestrictions {φ : C(s, ℂ)}
    (hφ : φ ∈ holomorphicRestrictions s) (h : t ⊆ s) :
    φ.comp (ContinuousMap.inclusion h) ∈ holomorphicRestrictions t := by
  rw [← holomorphicGerms.range_toContinuousMap] at hφ
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hφ
  rw [← holomorphicGerms.toContinuousMap_restrict h g]
  exact holomorphicGerms.toContinuousMap_mem_holomorphicRestrictions _

/-- The restriction to `s` of a holomorphic function on an open set `U ⊇ s` lies in `O(s)`. -/
theorem HolomorphicFunctions.comp_inclusion_mem_holomorphicRestrictions {U : Opens ℂ}
    (hs : s ⊆ U) (f : holomorphicFunctions U) :
    (f : C(U, ℂ)).comp (ContinuousMap.inclusion hs) ∈ holomorphicRestrictions s := by
  rw [← holomorphicGerms.toContinuousMap_toGerm hs f]
  exact holomorphicGerms.toContinuousMap_mem_holomorphicRestrictions _

/-- On an open set `U`, `O(U)` is the algebra of holomorphic functions on `U`. -/
@[simp]
theorem holomorphicRestrictions_coe_opens (U : Opens ℂ) :
    holomorphicRestrictions (U : Set ℂ) = holomorphicFunctions U := by
  ext φ
  rw [mem_holomorphicRestrictions_iff, mem_holomorphicFunctions_iff]
  exact ⟨fun ⟨f, hf, hfφ⟩ ↦ ⟨f, hf.differentiableOn, hfφ⟩,
    fun ⟨f, hf, hfφ⟩ ↦ ⟨f, hf.analyticOnNhd U.isOpen, hfφ⟩⟩

/-- The restriction of an element of `O(s)` to an open subset `U ⊆ s` is holomorphic on `U`. -/
theorem comp_inclusion_mem_holomorphicFunctions {φ : C(s, ℂ)}
    (hφ : φ ∈ holomorphicRestrictions s) {U : Opens ℂ} (hU : (U : Set ℂ) ⊆ s) :
    φ.comp (ContinuousMap.inclusion hU) ∈ holomorphicFunctions U :=
  holomorphicRestrictions_coe_opens U ▸ comp_inclusion_mem_holomorphicRestrictions hφ hU

/-- Polynomial functions on `s` lie in `O(s)`. -/
theorem polynomialFunctions_le_holomorphicRestrictions (s : Set ℂ) :
    polynomialFunctions s ≤ holomorphicRestrictions s := by
  intro φ hφ
  rw [← SetLike.mem_coe, polynomialFunctions_coe] at hφ
  obtain ⟨p, rfl⟩ := hφ
  exact mem_holomorphicRestrictions_iff.mpr
    ⟨fun z ↦ p.eval z, fun z _ ↦ (Polynomial.differentiable p).analyticAt z, fun _ ↦ by simp⟩

/-- On a finite set `s`, including the empty set, `O(s) = C(s, ℂ)`. -/
theorem holomorphicRestrictions_eq_top_of_finite (hs : s.Finite) :
    holomorphicRestrictions s = ⊤ :=
  eq_top_mono (polynomialFunctions_le_holomorphicRestrictions s)
    (polynomialFunctions.eq_top_of_finite hs)

/-- The conjugate coordinate `z ↦ conj z` on a set with nonempty interior does not lie in
`O(s)`. -/
theorem star_restrict_id_notMem_holomorphicRestrictions (hs : (interior s).Nonempty) :
    star (ContinuousMap.restrict s (ContinuousMap.id ℂ)) ∉ holomorphicRestrictions s := by
  rw [mem_holomorphicRestrictions_iff_exists_open]
  rintro ⟨U, f, hU, hsU, hf, hfφ⟩
  obtain ⟨z, hz⟩ := hs
  have heq : (fun w ↦ conj w) =ᶠ[𝓝 z] f := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hz] with w hw
    simpa using (hfφ ⟨w, hw⟩).symm
  exact Complex.not_differentiableAt_conj z
    ((hf.differentiableAt (hU.mem_nhds (hsU (interior_subset hz)))).congr_of_eventuallyEq heq)

/-- On a set with nonempty interior, `O(s)` is not open in `C(s, ℂ)`. -/
theorem not_isOpen_holomorphicRestrictions (hs : (interior s).Nonempty) :
    ¬IsOpen (holomorphicRestrictions s : Set C(s, ℂ)) := by
  intro hopen
  have huniv := (absorbent_nhds_zero (𝕜 := ℂ)
    (hopen.mem_nhds (zero_mem (holomorphicRestrictions s)))).eq_univ_of_smulMemClass
  exact star_restrict_id_notMem_holomorphicRestrictions hs
    (SetLike.mem_coe.mp (eq_univ_iff_forall.mp huniv _))

end TauCeti
