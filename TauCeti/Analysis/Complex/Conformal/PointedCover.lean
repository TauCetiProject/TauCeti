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
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Rotation
import TauCeti.Analysis.Complex.UnitDisc.Basic
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Topology.Covering.Homeomorph

/-!
# Pointed holomorphic universal covers by the unit disc

A *pointed cover* of a plane set `Ω` at `a ∈ Ω` is a holomorphic map `F` of the unit disc onto
`Ω` with `F 0 = a` that is a topological covering map `Complex.UnitDisc → Ω`. Since the disc is
simply connected, such an `F` is a universal cover of `Ω`. This file records the comparison
theory of these covers, which holds for every `Ω` admitting one; the existence of a pointed cover
of a hyperbolic plane domain is the uniformization theorem and is not proved here.

The cover is stored as a scalar function `ℂ → ℂ`, so that `deriv` and the other one-variable
tools apply to it directly. Off the unit disc it takes the base value `a`, so a pointed cover is
determined by its values on the disc (`PointedCover.ext`). Covers are compared on the unit disc,
and lifts through a cover on their source set `U`.

## Main declarations

* `TauCeti.PointedCover Ω a`: a based holomorphic covering map of `Ω` by the unit disc.
* `TauCeti.PointedCover.ext`: two pointed covers that agree on the unit disc are equal.
* `TauCeti.PointedCover.coverMap`: the cover as a covering map `Complex.UnitDisc → Ω`.
* `TauCeti.PointedCover.deriv_ne_zero`: a pointed cover has nonvanishing derivative on the disc.
* `TauCeti.PointedCover.exists_differentiableOn_lift`: a holomorphic map of a simply connected
  open set `U` into `Ω` lifts through a pointed cover to a holomorphic map of `U` into the disc,
  with any prescribed lift of one value; `PointedCover.exists_differentiableOn_lift_ball` is the
  based lift of a holomorphic disc map.
* `TauCeti.PointedCover.eqOn_of_comp_eqOn`: two continuous lifts of the same map on a
  preconnected set `U` that agree at one point agree on `U`.
* `TauCeti.PointedCover.rotate`: precomposing a pointed cover with a rotation of the disc gives a
  pointed cover.
* `TauCeti.PointedCover.existsUnique_eqOn_comp_const_mul`: two pointed covers of `Ω` at `a`
  differ by a unique rotation of the source disc.
* `TauCeti.PointedCover.norm_deriv_toFun_zero_eq`: consequently all pointed covers of `Ω` at `a`
  have the same derivative norm at the origin, so this norm is an invariant of `(Ω, a)`.
* `TauCeti.PointedCover.ofBall`: for `0 < r`, the affine map `z ↦ c + r * z` is a pointed cover
  of the disc `ball c r` at `c`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math.
  Soc. 38 (2025), 627–702, §5.1, p. 668 (the normalization of the universal cover after
  Lemma 5.1.2).
* A. Hatcher, *Algebraic Topology*, Propositions 1.33 and 1.34 (lifting of maps through
  covering spaces).
-/

public section

namespace TauCeti

open _root_.Complex Metric Set Filter
open scoped Topology

/-- A *pointed cover* of `Ω ⊆ ℂ` at `a`: a holomorphic map `toFun` of the unit disc into `Ω`,
sending `0` to `a`, that is a covering map of `Complex.UnitDisc` onto the subtype `Ω`.

Off the unit disc, `toFun` takes the base value `a`, so the cover is determined by its values on
the disc. -/
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
  /-- Off the unit disc, the cover takes the base value. -/
  toFun_of_notMem : ∀ z ∉ ball (0 : ℂ) 1, toFun z = a

namespace PointedCover

variable {Ω : Set ℂ} {a : ℂ} (F : PointedCover Ω a)

attribute [simp] map_zero

/-- Two pointed covers of `Ω` at `a` that agree on the unit disc are equal. -/
@[ext (iff := false)]
theorem ext {F G : PointedCover Ω a} (h : EqOn F.toFun G.toFun (ball 0 1)) : F = G := by
  have hfg : F.toFun = G.toFun := funext fun z ↦ by
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · exact h hz
    · rw [F.toFun_of_notMem z hz, G.toFun_of_notMem z hz]
  cases F
  cases G
  cases hfg
  rfl

/-- Two pointed covers of `Ω` at `a` are equal if and only if they agree on the unit disc. -/
theorem ext_iff {F G : PointedCover Ω a} : F = G ↔ EqOn F.toFun G.toFun (ball 0 1) :=
  ⟨fun h ↦ h ▸ eqOn_refl _ _, ext⟩

/-- The base point of a pointed cover lies in `Ω`. -/
theorem base_mem (F : PointedCover Ω a) : a ∈ Ω :=
  F.map_zero ▸ F.mapsTo (mem_ball_self one_pos)

/-- A pointed cover as a map from `Complex.UnitDisc` to the subtype `Ω`. -/
def coverMap (z : UnitDisc) : Ω :=
  ⟨F.toFun z, F.mapsTo (mem_ball_zero_iff.2 z.norm_lt_one)⟩

@[simp]
theorem coe_coverMap (z : UnitDisc) : (F.coverMap z : ℂ) = F.toFun z :=
  (rfl)

/-- The map `Complex.UnitDisc → Ω` of a pointed cover is a covering map. -/
theorem isCoveringMap_coverMap : IsCoveringMap F.coverMap :=
  F.isCoveringMap

/-- The map `Complex.UnitDisc → Ω` of a pointed cover is surjective. -/
theorem coverMap_surjective : Function.Surjective F.coverMap := fun w ↦ by
  obtain ⟨z, hz, hzw⟩ := F.surjOn w.property
  exact ⟨UnitDisc.mk z (mem_ball_zero_iff.1 hz), Subtype.ext hzw⟩

/-- A pointed cover has nonvanishing derivative at every point of the unit disc. -/
theorem deriv_ne_zero {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv F.toFun z ≠ 0 := by
  -- A covering map is locally injective, and a locally injective holomorphic map has nonzero
  -- derivative.
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
theorem eqOn_of_comp_eqOn {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsPreconnected U)
    {l₁ l₂ : X → ℂ} (h₁ : ContinuousOn l₁ U) (h₂ : ContinuousOn l₂ U)
    (hm₁ : MapsTo l₁ U (ball 0 1)) (hm₂ : MapsTo l₂ U (ball 0 1))
    (he : EqOn (F.toFun ∘ l₁) (F.toFun ∘ l₂) U) {z₀ : X} (hz₀ : z₀ ∈ U)
    (h₀ : l₁ z₀ = l₂ z₀) : EqOn l₁ l₂ U := by
  have := isPreconnected_iff_preconnectedSpace.1 hU
  have hc : ∀ {l : X → ℂ}, ContinuousOn l U → ∀ hm : MapsTo l U (ball 0 1),
      Continuous fun z : U ↦ UnitDisc.mk (l z) (mem_ball_zero_iff.1 (hm z.property)) := fun hl _ ↦
    UnitDisc.isEmbedding_coe.continuous_iff.2 (continuousOn_iff_continuous_domRestrict.1 hl)
  have := F.isCoveringMap.eq_of_comp_eq (hc h₁ hm₁) (hc h₂ hm₂)
    (funext fun z ↦ Subtype.ext (he z.property)) ⟨z₀, hz₀⟩ (UnitDisc.coe_injective h₀)
  exact fun z hz ↦ congrArg (fun g : U → UnitDisc ↦ (g ⟨z, hz⟩ : ℂ)) this

/-- **Continuous lifting.** A continuous map `f` of a simply connected open set `U` into `Ω`
lifts through a pointed cover of `Ω` to a continuous map of `U` into the unit disc, taking a
prescribed value `w₀` over `f z₀` at `z₀`. -/
theorem exists_continuousOn_lift {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hUo : IsOpen U) (hU : IsSimplyConnected U) {f : X → ℂ} (hf : ContinuousOn f U)
    (hfU : MapsTo f U Ω) {z₀ : X} {w₀ : ℂ} (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ ball (0 : ℂ) 1)
    (hfz₀ : F.toFun w₀ = f z₀) :
    ∃ l : X → ℂ, ContinuousOn l U ∧ MapsTo l U (ball 0 1) ∧ l z₀ = w₀ ∧
      EqOn (F.toFun ∘ l) f U := by
  classical
  have := hU.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  let fU : C(U, Ω) :=
    ⟨fun z ↦ ⟨f z, hfU z.property⟩, (continuousOn_iff_continuous_domRestrict.1 hf).subtype_mk _⟩
  obtain ⟨L, ⟨hL₀, hL⟩, -⟩ := F.isCoveringMap.existsUnique_continuousMap_lifts fU ⟨z₀, hz₀⟩
    (UnitDisc.mk w₀ (mem_ball_zero_iff.1 hw₀)) (Subtype.ext hfz₀)
  let l : X → ℂ := fun z ↦ if hz : z ∈ U then (L ⟨z, hz⟩ : ℂ) else w₀
  have hlL : ∀ z (hz : z ∈ U), l z = L ⟨z, hz⟩ := fun z hz ↦ by simp [l, hz]
  refine ⟨l, ?_, fun z hz ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert UnitDisc.continuous_coe.comp L.continuous using 1
    exact funext fun z ↦ hlL z z.property
  · rw [hlL z hz, mem_ball_zero_iff]
    exact (L _).norm_lt_one
  · rw [hlL z₀ hz₀, hL₀, UnitDisc.coe_mk]
  · rw [Function.comp_apply, hlL z hz]
    exact congrArg Subtype.val (congrFun hL ⟨z, hz⟩)

/-- **Holomorphy of lifts.** A continuous lift into the unit disc, through a pointed cover, of a
holomorphic map on a set `U` is holomorphic on `U`. -/
theorem differentiableOn_of_comp_eqOn {U : Set ℂ} {f l : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hl : ContinuousOn l U) (hm : MapsTo l U (ball 0 1))
    (he : EqOn (F.toFun ∘ l) f U) : DifferentiableOn ℂ l U := by
  intro z hz
  have hd := F.deriv_ne_zero (hm hz)
  have hF := (F.differentiableOn.differentiableAt
    (isOpen_ball.mem_nhds (hm hz))).hasDerivAt.hasFDerivAt.hasFDerivWithinAt (s := univ)
  refine (hF.of_comp_of_leftInverse (s := U) ?_ (hf z hz).hasFDerivWithinAt
    (eventuallyEq_nhdsWithin_of_eqOn he)
    (f'symm := .toSpanSingleton ℂ (deriv F.toFun (l z))⁻¹) (fun _ ↦ by simp [hd])
    hz).differentiableWithinAt
  simpa only [nhdsWithin_univ] using (hl z hz).tendsto

/-- **Holomorphic lifting.** A holomorphic map `f` of a simply connected open set `U` into `Ω`
lifts through a pointed cover of `Ω` to a holomorphic map of `U` into the unit disc, taking a
prescribed value `w₀` over `f z₀` at `z₀`. On a preconnected `U` this lift is unique on `U`, by
`PointedCover.eqOn_of_comp_eqOn`. -/
theorem exists_differentiableOn_lift {U : Set ℂ} (hUo : IsOpen U) (hU : IsSimplyConnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hfU : MapsTo f U Ω) {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hw₀ : w₀ ∈ ball (0 : ℂ) 1) (hfz₀ : F.toFun w₀ = f z₀) :
    ∃ l : ℂ → ℂ, DifferentiableOn ℂ l U ∧ MapsTo l U (ball 0 1) ∧ l z₀ = w₀ ∧
      EqOn (F.toFun ∘ l) f U := by
  obtain ⟨l, hl, hm, hl₀, he⟩ :=
    F.exists_continuousOn_lift hUo hU hf.continuousOn hfU hz₀ hw₀ hfz₀
  exact ⟨l, F.differentiableOn_of_comp_eqOn hf hl hm he, hm, hl₀, he⟩

/-- **Based holomorphic lifting.** A holomorphic map `f` of the unit disc into `Ω` with
`f 0 = a` lifts through a pointed cover of `Ω` at `a` to a holomorphic self-map of the unit disc
fixing `0`. This lift is unique on the unit disc, by `PointedCover.eqOn_of_comp_eqOn`. -/
theorem exists_differentiableOn_lift_ball {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hfΩ : MapsTo f (ball 0 1) Ω) (hf₀ : f 0 = a) :
    ∃ l : ℂ → ℂ, DifferentiableOn ℂ l (ball 0 1) ∧ MapsTo l (ball 0 1) (ball 0 1) ∧ l 0 = 0 ∧
      EqOn (F.toFun ∘ l) f (ball 0 1) :=
  have h₀ : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  F.exists_differentiableOn_lift isOpen_ball ((convex_ball 0 1).isSimplyConnected ⟨0, h₀⟩) hf
    hfΩ h₀ h₀ (F.map_zero.trans hf₀.symm)

/-- Precomposing a pointed cover with the rotation `z ↦ u * z` of the unit disc, for `u` on the
unit circle, gives a pointed cover. -/
def rotate (u : Circle) : PointedCover Ω a where
  toFun z := F.toFun (u * z)
  differentiableOn := F.differentiableOn.comp (by fun_prop)
    fun _ hz ↦ balanced_ball_zero.smul_mem (Circle.norm_coe u).le hz
  mapsTo := F.mapsTo.comp fun _ hz ↦ balanced_ball_zero.smul_mem (Circle.norm_coe u).le hz
  map_zero := by simp
  isCoveringMap := F.isCoveringMap.comp_homeomorph (Homeomorph.smul u)
  surjOn w hw := by
    obtain ⟨z, hz, rfl⟩ := F.surjOn hw
    refine ⟨u⁻¹ * z, balanced_ball_zero.smul_mem (Circle.norm_coe u⁻¹).le hz, ?_⟩
    simp
  -- Rotations preserve the complement of the disc.
  toFun_of_notMem z hz := F.toFun_of_notMem _ fun h ↦ hz <| by
    simpa using balanced_ball_zero.smul_mem (Circle.norm_coe u⁻¹).le h

@[simp]
theorem rotate_toFun (u : Circle) : (F.rotate u).toFun = fun z ↦ F.toFun (u * z) :=
  (rfl)

/-- **Uniqueness of pointed covers.** Two pointed covers `F` and `G` of `Ω` at `a` differ by a
unique rotation of the source disc: there is exactly one `ζ` with `‖ζ‖ = 1` and
`G z = F (ζ * z)` on the unit disc. -/
theorem existsUnique_eqOn_comp_const_mul (G : PointedCover Ω a) :
    ∃! ζ : ℂ, ‖ζ‖ = 1 ∧ EqOn G.toFun (fun z ↦ F.toFun (ζ * z)) (ball 0 1) := by
  have h₀ : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hBp : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isPreconnected
  -- Lift `G` through `F` and `F` through `G`, both based at the origin.
  obtain ⟨l, hl, hlm, hl₀, hFl⟩ :=
    F.exists_differentiableOn_lift_ball G.differentiableOn G.mapsTo G.map_zero
  obtain ⟨m, hm, hmm, hm₀, hGm⟩ :=
    G.exists_differentiableOn_lift_ball F.differentiableOn F.mapsTo F.map_zero
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
  have hζc := F.eqOn_of_comp_eqOn hBp (by fun_prop) (by fun_prop)
    (fun _ hz ↦ balanced_ball_zero.smul_mem hζ.le hz)
    (fun _ hz ↦ balanced_ball_zero.smul_mem hc.le hz)
    (fun z hz ↦ (hGζ hz).symm.trans (hGc hz)) h₀ (by simp)
  have hhalf : (2⁻¹ : ℂ) ∈ ball (0 : ℂ) 1 := by norm_num [mem_ball_zero_iff]
  simpa using hζc hhalf

/-- All pointed covers of `Ω` at `a` have the same derivative norm at the origin. -/
theorem norm_deriv_toFun_zero_eq (G : PointedCover Ω a) :
    ‖deriv G.toFun 0‖ = ‖deriv F.toFun 0‖ := by
  -- The two covers differ by a rotation of the source disc.
  obtain ⟨ζ, ⟨hζ, hG⟩, -⟩ := F.existsUnique_eqOn_comp_const_mul G
  have hev : G.toFun =ᶠ[𝓝 0] fun z ↦ F.toFun (ζ * z) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hG
  rw [hev.deriv_eq, deriv_comp_mul_left]
  simp [hζ]

/-- For `0 < r`, the affine map `z ↦ c + r * z` on the unit disc is a pointed cover of the disc
`ball c r` at its centre. -/
noncomputable def ofBall (c : ℂ) {r : ℝ} (hr : 0 < r) : PointedCover (ball c r) c :=
  -- Mathlib's affine homeomorphism of `ball 0 1` onto `ball c r` is `z ↦ c + r * z`.
  let f := OpenPartialHomeomorph.unitBallBall c r hr
  have hf : ∀ z, f z = c + r * z := fun z ↦ by simp [f, add_comm]
  have hs : f.source = ball 0 1 := OpenPartialHomeomorph.unitBallBall_source c r hr
  have ht : f.target = ball c r := OpenPartialHomeomorph.unitBallBall_target c r hr
  have hb : ∀ z ∈ ball (0 : ℂ) 1, c + (ball 0 1).indicator (fun z : ℂ ↦ (r : ℂ) * z) z = f z :=
    fun z hz ↦ by rw [indicator_of_mem hz, hf]
  have hd : DifferentiableOn ℂ (fun z : ℂ ↦ c + r * z) (ball 0 1) := by fun_prop
  { toFun z := c + (ball 0 1).indicator (fun z : ℂ ↦ (r : ℂ) * z) z
    differentiableOn := hd.congr fun z hz ↦ (hb z hz).trans (hf z)
    mapsTo z hz := by simpa only [hb z hz, ht] using f.map_source (hs ▸ hz)
    map_zero := by simp
    isCoveringMap := by
      convert (UnitDisc.homeomorphBall.trans <| (Homeomorph.setCongr hs.symm).trans <|
        f.toHomeomorphSourceTarget.trans <| Homeomorph.setCongr ht).isCoveringMap using 1
      funext z
      ext
      simp [hb z (mem_ball_zero_iff.2 z.norm_lt_one), Homeomorph.setCongr]
    surjOn w hw := by
      have hm : f.symm w ∈ ball (0 : ℂ) 1 := hs ▸ f.map_target (ht ▸ hw)
      exact ⟨f.symm w, hm, (hb _ hm).trans (f.right_inv (ht ▸ hw))⟩
    toFun_of_notMem _ hz := by simp [indicator_of_notMem hz] }

/-- On the unit disc, `PointedCover.ofBall c hr` is `z ↦ c + r * z`. -/
@[simp]
theorem ofBall_toFun (c : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (ofBall c hr).toFun z = c + r * z :=
  congrArg (c + ·) (indicator_of_mem hz _)

end PointedCover

end TauCeti
