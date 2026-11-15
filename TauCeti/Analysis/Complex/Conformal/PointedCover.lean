/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Rotation
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Pointed holomorphic universal covers by the unit disc

A *pointed cover* of a plane set `Ω` at `a ∈ Ω` is a holomorphic map `F` of the unit disc onto
`Ω` with `F 0 = a` that is a topological covering map `Complex.UnitDisc → Ω`. Since the disc is
simply connected, such an `F` is a universal cover of `Ω`. This file records the comparison
theory of these covers, which holds for every `Ω` admitting one; the existence of a pointed cover
of a hyperbolic plane domain is the uniformization theorem and is not proved here.

The cover is stored as a scalar function `ℂ → ℂ`, so that `deriv` and the other one-variable
tools apply to it directly; its values off the unit disc play no role, and every statement below
compares covers and lifts on the disc only.

## Main declarations

* `TauCeti.PointedCover Ω a`: a based holomorphic covering map of `Ω` by the unit disc.
* `TauCeti.PointedCover.deriv_ne_zero`: a pointed cover has nonvanishing derivative on the disc.
* `TauCeti.PointedCover.exists_lift`: a holomorphic map of a simply connected open set into `Ω`
  lifts through a pointed cover to a holomorphic map into the disc, with any prescribed lift of
  one value.
* `TauCeti.PointedCover.eqOn_of_comp_eqOn`: such lifts are unique.
* `TauCeti.PointedCover.existsUnique_rotation`: two pointed covers of `Ω` at `a` differ by a
  unique rotation of the source disc.
* `TauCeti.PointedCover.norm_deriv_toFun_zero_eq`: consequently all pointed covers of `Ω` at `a`
  have the same derivative norm at the origin, so this norm is an invariant of `(Ω, a)`.
* `TauCeti.PointedCover.ofBall`: the affine map `z ↦ c + r * z` is a pointed cover of the disc
  `ball c r` at `c`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The linear independence of 1, ζ(2), and L(2, χ₋₃)*,
  §5.1 (the normalization of the universal cover after Lemma 5.1.2).
* A. Hatcher, *Algebraic Topology*, Propositions 1.33 and 1.34 (lifting of maps through
  covering spaces).
-/

public section

namespace TauCeti

open _root_.Complex Metric Set Filter
open scoped Topology

/-- A *pointed cover* of `Ω ⊆ ℂ` at `a`: a holomorphic map `toFun` of the unit disc into `Ω`,
sending `0` to `a`, that is a covering map of `Complex.UnitDisc` onto the subtype `Ω`.

Only the values of `toFun` on the unit disc are meaningful; covers are compared on the disc. -/
structure PointedCover (Ω : Set ℂ) (a : ℂ) where
  /-- The scalar representative of the cover. -/
  toFun : ℂ → ℂ
  /-- The cover is holomorphic on the unit disc. -/
  differentiableOn : DifferentiableOn ℂ toFun (ball 0 1)
  /-- The cover maps the unit disc into `Ω`. -/
  mapsTo : MapsTo toFun (ball 0 1) Ω
  /-- The cover sends the origin to the base point. -/
  map_zero : toFun 0 = a
  /-- The cover is a covering map of `Complex.UnitDisc` over the subtype `Ω`. -/
  isCoveringMap : IsCoveringMap fun z : UnitDisc ↦
    (⟨toFun z, mapsTo (mem_ball_zero_iff.2 z.norm_lt_one)⟩ : Ω)
  /-- The cover maps the unit disc onto `Ω`. -/
  surjOn : SurjOn toFun (ball 0 1) Ω

namespace PointedCover

variable {Ω : Set ℂ} {a : ℂ} (F : PointedCover Ω a)

/-- A continuous map of `U` into the unit disc, as a bundled map into `Complex.UnitDisc`. -/
private def toUnitDisc {U : Set ℂ} {l : ℂ → ℂ} (hl : ContinuousOn l U)
    (hm : MapsTo l U (ball 0 1)) : C(U, UnitDisc) :=
  ⟨fun z ↦ UnitDisc.mk (l z) (mem_ball_zero_iff.1 (hm z.2)),
    UnitDisc.isEmbedding_coe.continuous_iff.2 (continuousOn_iff_continuous_domRestrict.1 hl)⟩

/-- A pointed cover has nonvanishing derivative at every point of the unit disc: a covering map
is locally injective, and a locally injective holomorphic map has nonzero derivative. -/
theorem deriv_ne_zero {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv F.toFun z ≠ 0 := by
  obtain ⟨V, hVo, hzV, hinj⟩ := F.isCoveringMap.isLocalHomeomorph.isLocallyInjective
    (UnitDisc.mk z (mem_ball_zero_iff.1 hz))
  obtain ⟨W, hWo, rfl⟩ := UnitDisc.isEmbedding_coe.isInducing.isOpen_iff.1 hVo
  refine (exists_injOn_nhds_iff_deriv_ne_zero
    (F.differentiableOn.analyticAt (isOpen_ball.mem_nhds hz))).1
      ⟨W ∩ ball 0 1, (hWo.inter isOpen_ball).mem_nhds ⟨hzV, hz⟩, ?_⟩
  intro x hx y hy hxy
  have := hinj (x₁ := UnitDisc.mk x (mem_ball_zero_iff.1 hx.2)) hx.1
    (x₂ := UnitDisc.mk y (mem_ball_zero_iff.1 hy.2)) hy.1 (Subtype.ext hxy)
  simpa using congrArg ((↑) : UnitDisc → ℂ) this

/-- **Uniqueness of lifts.** Two continuous maps of a preconnected set `U` into the unit disc
whose composites with a pointed cover agree on `U`, and which agree at one point of `U`, agree on
all of `U`. -/
theorem eqOn_of_comp_eqOn {U : Set ℂ} (hU : IsPreconnected U) {l₁ l₂ : ℂ → ℂ}
    (h₁ : ContinuousOn l₁ U) (h₂ : ContinuousOn l₂ U)
    (hm₁ : MapsTo l₁ U (ball 0 1)) (hm₂ : MapsTo l₂ U (ball 0 1))
    (he : EqOn (F.toFun ∘ l₁) (F.toFun ∘ l₂) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (h₀ : l₁ z₀ = l₂ z₀) : EqOn l₁ l₂ U := by
  have := isPreconnected_iff_preconnectedSpace.1 hU
  have := F.isCoveringMap.eq_of_comp_eq (toUnitDisc h₁ hm₁).continuous
    (toUnitDisc h₂ hm₂).continuous (funext fun z ↦ Subtype.ext (he z.2)) ⟨z₀, hz₀⟩
    (UnitDisc.coe_injective h₀)
  exact fun z hz ↦ congrArg (fun g : U → UnitDisc ↦ (g ⟨z, hz⟩ : ℂ)) this

/-- **Continuous lifting.** A continuous map `f` of a simply connected open set `U` into `Ω`
lifts through a pointed cover of `Ω` to a continuous map of `U` into the unit disc, taking a
prescribed value `w₀` over `f z₀` at `z₀`. -/
theorem exists_continuousOn_lift {U : Set ℂ} (hUo : IsOpen U) (hU : IsSimplyConnected U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hfU : MapsTo f U Ω) {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hw₀ : w₀ ∈ ball (0 : ℂ) 1) (hfz₀ : F.toFun w₀ = f z₀) :
    ∃ l : ℂ → ℂ, ContinuousOn l U ∧ MapsTo l U (ball 0 1) ∧ l z₀ = w₀ ∧
      EqOn (F.toFun ∘ l) f U := by
  classical
  have := hU.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  let fU : C(U, Ω) :=
    ⟨fun z ↦ ⟨f z, hfU z.2⟩, (continuousOn_iff_continuous_domRestrict.1 hf).subtype_mk _⟩
  obtain ⟨L, ⟨hL₀, hL⟩, -⟩ := F.isCoveringMap.existsUnique_continuousMap_lifts fU ⟨z₀, hz₀⟩
    (UnitDisc.mk w₀ (mem_ball_zero_iff.1 hw₀)) (Subtype.ext hfz₀)
  let l : ℂ → ℂ := fun z ↦ if hz : z ∈ U then (L ⟨z, hz⟩ : ℂ) else w₀
  have hlL : ∀ z (hz : z ∈ U), l z = L ⟨z, hz⟩ := fun z hz ↦ by simp [l, hz]
  refine ⟨l, ?_, fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert UnitDisc.continuous_coe.comp L.continuous using 1
    exact funext fun z ↦ hlL z z.2
  · rw [hlL z hz, mem_ball_zero_iff]
    exact (L _).norm_lt_one
  · rw [hlL z₀ hz₀, hL₀, UnitDisc.coe_mk]
  · rw [Function.comp_apply, hlL z hz]
    exact congrArg Subtype.val (congrFun hL ⟨z, hz⟩)

/-- **Holomorphy of lifts.** A continuous lift into the unit disc of a holomorphic map on an open
set, through a pointed cover, is holomorphic: near each point it is a holomorphic local inverse of
the cover composed with the map. -/
theorem differentiableOn_of_comp {U : Set ℂ} (hUo : IsOpen U) {f l : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hl : ContinuousOn l U) (hm : MapsTo l U (ball 0 1))
    (he : EqOn (F.toFun ∘ l) f U) : DifferentiableOn ℂ l U := by
  intro z hz
  have hw := hm hz
  have hs := (F.differentiableOn.analyticAt (isOpen_ball.mem_nhds hw)).hasStrictDerivAt
  have hd := F.deriv_ne_zero hw
  -- A holomorphic local inverse `g` of the cover near `l z`.
  obtain ⟨g, hg, hgF⟩ : ∃ g : ℂ → ℂ, DifferentiableAt ℂ g (F.toFun (l z)) ∧
      ∀ᶠ y in 𝓝 (l z), g (F.toFun y) = y :=
    ⟨_, (hs.to_localInverse hd).hasDerivAt.differentiableAt, hs.eventually_left_inverse hd⟩
  rw [← Function.comp_apply (f := F.toFun), he hz] at hg
  have hev : l =ᶠ[𝓝 z] g ∘ f := by
    filter_upwards [(hl.continuousAt (hUo.mem_nhds hz)).eventually hgF, hUo.mem_nhds hz]
      with y hy hyU
    rw [Function.comp_apply, ← he hyU]
    exact hy.symm
  exact ((hg.comp z (hf.differentiableAt (hUo.mem_nhds hz))).congr_of_eventuallyEq
    hev).differentiableWithinAt

/-- **Holomorphic lifting.** A holomorphic map `f` of a simply connected open set `U` into `Ω`
lifts through a pointed cover of `Ω` to a holomorphic map of `U` into the unit disc, taking a
prescribed value `w₀` over `f z₀` at `z₀`. For `U` the unit disc and `f 0 = a`, the choice
`z₀ = w₀ = 0` gives the based lift; it is unique by `PointedCover.eqOn_of_comp_eqOn`. -/
theorem exists_lift {U : Set ℂ} (hUo : IsOpen U) (hU : IsSimplyConnected U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hfU : MapsTo f U Ω) {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hw₀ : w₀ ∈ ball (0 : ℂ) 1) (hfz₀ : F.toFun w₀ = f z₀) :
    ∃ l : ℂ → ℂ, DifferentiableOn ℂ l U ∧ MapsTo l U (ball 0 1) ∧ l z₀ = w₀ ∧
      EqOn (F.toFun ∘ l) f U := by
  obtain ⟨l, hl, hm, hl₀, he⟩ :=
    F.exists_continuousOn_lift hUo hU hf.continuousOn hfU hz₀ hw₀ hfz₀
  exact ⟨l, F.differentiableOn_of_comp hUo hf hl hm he, hm, hl₀, he⟩

/-- Multiplication by a unimodular constant maps the unit disc to itself. -/
private theorem mapsTo_const_mul_ball {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    MapsTo (fun z ↦ ζ * z) (ball (0 : ℂ) 1) (ball 0 1) := fun z hz ↦ by
  simpa [norm_mul, hζ] using hz

/-- **Uniqueness of pointed covers.** Two pointed covers `F` and `G` of `Ω` at `a` differ by a
unique rotation of the source disc: there is exactly one `ζ` with `‖ζ‖ = 1` and
`G z = F (ζ * z)` on the unit disc. -/
theorem existsUnique_rotation (G : PointedCover Ω a) :
    ∃! ζ : ℂ, ‖ζ‖ = 1 ∧ EqOn G.toFun (fun z ↦ F.toFun (ζ * z)) (ball 0 1) := by
  have h₀ : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hB : IsSimplyConnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isSimplyConnected ⟨0, h₀⟩
  have hBp : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isPreconnected
  -- Lift `G` through `F` and `F` through `G`, both based at the origin.
  obtain ⟨l, hl, hlm, hl₀, hFl⟩ := F.exists_lift isOpen_ball hB G.differentiableOn G.mapsTo h₀
    h₀ (F.map_zero.trans G.map_zero.symm)
  obtain ⟨m, hm, hmm, hm₀, hGm⟩ := G.exists_lift isOpen_ball hB F.differentiableOn F.mapsTo h₀
    h₀ (G.map_zero.trans F.map_zero.symm)
  -- `m ∘ l` lifts `G` through itself and fixes the origin, so it is the identity.
  have hml : ∀ z ∈ ball (0 : ℂ) 1, m (l z) = z :=
    G.eqOn_of_comp_eqOn hBp (hm.continuousOn.comp hl.continuousOn hlm) continuousOn_id
      (hmm.comp hlm) (mapsTo_id _) (fun z hz ↦ (hGm (hlm hz)).trans (hFl hz)) h₀
      (by simp [hl₀, hm₀])
  -- Hence `l` is a disc automorphism fixing the origin, i.e. a rotation.
  obtain ⟨c, hc, hlc⟩ := exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero hl hm hlm hmm hml hl₀
  have hGc : EqOn G.toFun (fun z ↦ F.toFun (c * z)) (ball 0 1) := fun z hz ↦
    (hFl hz).symm.trans (congrArg F.toFun (hlc hz))
  refine ⟨c, ⟨hc, hGc⟩, ?_⟩
  -- Two rotations lifting `G` through `F` agree on the disc, hence have equal factors.
  rintro ζ ⟨hζ, hGζ⟩
  have hζc := F.eqOn_of_comp_eqOn hBp (by fun_prop) (by fun_prop) (mapsTo_const_mul_ball hζ)
    (mapsTo_const_mul_ball hc)
    (fun z hz ↦ (hGζ hz).symm.trans (hGc hz)) h₀ (by simp)
    (show (2⁻¹ : ℂ) ∈ ball (0 : ℂ) 1 by norm_num [mem_ball_zero_iff])
  simpa using hζc

/-- All pointed covers of `Ω` at `a` have the same derivative norm at the origin: they differ
by a rotation of the source disc. -/
theorem norm_deriv_toFun_zero_eq (G : PointedCover Ω a) :
    ‖deriv G.toFun 0‖ = ‖deriv F.toFun 0‖ := by
  obtain ⟨ζ, ⟨hζ, hG⟩, -⟩ := F.existsUnique_rotation G
  have hev : G.toFun =ᶠ[𝓝 0] fun z ↦ F.toFun (ζ * z) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hG
  rw [hev.deriv_eq, deriv_comp_mul_left]
  simp [hζ]

/-- The affine map `z ↦ c + r * z` sends the unit disc into `ball c r`. -/
private theorem add_mul_mem_ball (c : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ < 1) :
    c + r * z ∈ ball c r := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  exact mul_lt_of_lt_one_right hr hz

/-- The inverse affine map `w ↦ (w - c) / r` sends `ball c r` into the unit disc. -/
private theorem norm_sub_div_lt_one {c w : ℂ} {r : ℝ} (hr : 0 < r) (hw : w ∈ ball c r) :
    ‖(w - c) / r‖ < 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one hr, ← dist_eq_norm]
  exact hw

/-- The affine map `z ↦ c + r * z` is a pointed cover of the disc `ball c r` at its centre. -/
noncomputable def ofBall (c : ℂ) {r : ℝ} (hr : 0 < r) : PointedCover (ball c r) c where
  toFun z := c + r * z
  differentiableOn := by fun_prop
  mapsTo _ hz := add_mul_mem_ball c hr (mem_ball_zero_iff.1 hz)
  map_zero := by simp
  isCoveringMap := by
    let e : UnitDisc ≃ₜ ball c r :=
      { toFun z := ⟨c + r * z, add_mul_mem_ball c hr z.norm_lt_one⟩
        invFun w := UnitDisc.mk ((w - c) / r) (norm_sub_div_lt_one hr w.2)
        left_inv z := UnitDisc.coe_injective (by
          simp [Complex.ofReal_ne_zero.2 hr.ne'])
        right_inv w := Subtype.ext (by
          simp [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr.ne')])
        continuous_toFun := by fun_prop
        continuous_invFun := by
          refine UnitDisc.isEmbedding_coe.continuous_iff.2 ?_
          simp only [Function.comp_def, UnitDisc.coe_mk]
          fun_prop }
    have : T2Space UnitDisc := UnitDisc.isEmbedding_coe.t2Space
    have := e.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (s := univ) (fun x _ ↦ (subsingleton_singleton.preimage e.injective).finite)
      e.isLocalHomeomorph.isLocalHomeomorphOn
    exact isCoveringMap_iff_isCoveringMapOn_univ.2 this
  surjOn w hw := by
    refine ⟨(w - c) / r, mem_ball_zero_iff.2 (norm_sub_div_lt_one hr hw), ?_⟩
    simp [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr.ne')]

/-- The scalar representative of `PointedCover.ofBall c hr` is `z ↦ c + r * z`. -/
@[simp]
theorem ofBall_toFun (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (ofBall c hr).toFun = fun z ↦ c + r * z := (rfl)

end PointedCover

end TauCeti
