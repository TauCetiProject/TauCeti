/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Topology.Homotopy.HurewiczFibration.Transport

/-!
# Fibre transport along a path by pulling back to the interval

Let `q : X → Y` be a Hurewicz fibration and let `K` deform `Y` onto a subset `S` in the weak
sense: `K` starts at the identity, ends inside `S` and keeps `S` inside `S`. Lifting `K` along `q`,
starting at the identity, deforms `X` onto `q⁻¹ S` in the same sense, so the inclusion
`q⁻¹ S → X` is a homotopy equivalence (`TauCeti.IsHurewiczFibration.preimageHomotopyEquiv`).

For a Hurewicz fibration `p : E → B` and a map `γ : I → B`, the pullback
`TauCeti.PathPullback p γ = {(t, e) | γ t = p e}` is a Hurewicz fibration over the interval. The
straight-line deformation of `I` onto a point `t₀` therefore shows that the inclusion of the fibre
`p⁻¹ b`, for `b = γ t₀`, into the pullback is a homotopy equivalence
(`TauCeti.IsHurewiczFibration.pathPullbackHomotopyEquiv`). Its homotopy inverse is the end of a
lift of the deformation, which need not fix the fibre.

For a path `γ` from `b₀` to `b₁`, composing the equivalences at the two end points gives the
**fibre transport** `p⁻¹ b₀ ≃ₕ p⁻¹ b₁` along `γ`
(`TauCeti.IsHurewiczFibration.transportHomotopyEquiv`): include the fibre over `t = 0` into the
pullback and deform it into the fibre over `t = 1`. Its homotopy inverse includes the fibre over
`t = 1` and deforms it back. It compares fibres along the supplied path, not by a path-independent
map, and empty fibres are allowed. No regular or transitive lifting function is used. When `p`
has a lifting function `Λ`, the forward map is homotopic to the lifting-function transport
`Λ.transport γ` (`TauCeti.LiftingFunction.transport_homotopic_transportHomotopyEquiv`), which is
therefore a homotopy equivalence too.

## Main definitions

* `TauCeti.IsHurewiczFibration.preimageHomotopyEquiv`: the inclusion of the preimage of a weak
  deformation retract under a Hurewicz fibration, as a homotopy equivalence.
* `TauCeti.PathPullback p γ`: the pullback of `p` along a map `γ : I → B`.
* `TauCeti.IsHurewiczFibration.pathPullbackHomotopyEquiv`: the inclusion of the fibre over a
  point of the interval into the pullback, as a homotopy equivalence.
* `TauCeti.IsHurewiczFibration.transportHomotopyEquiv`: the fibre transport along a path.

## Main results

* `TauCeti.LiftingFunction.transport_homotopic_transportHomotopyEquiv`: the transport of a lifting
  function is homotopic to the fibre transport through the pullback.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
* A. Hatcher, *Algebraic Topology*, Section 4.2.
-/

public section

open Set unitInterval ContinuousMap

universe u v w

namespace TauCeti

section Preimage

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {q : X → Y}
  {S : Set Y}

namespace IsHurewiczFibration

/-- A deformation `K` of the base of a Hurewicz fibration `q`, starting at the identity, lifts to a
deformation of the total space starting at the identity. -/
private theorem exists_lift_deformation (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) :
    ∃ G : C(I × X, X), (∀ x, G (0, x) = x) ∧ ∀ t x, q (G (t, x)) = K (t, q x) := by
  obtain ⟨G, hG, hG₀⟩ := hq.hasHomotopyLiftingProperty X (.id X)
    (K.comp ⟨fun z ↦ (z.1, q z.2),
      continuous_fst.prodMk (hq.continuous.comp continuous_snd)⟩) fun x ↦ h₀ (q x)
  exact ⟨G, hG₀, fun t x ↦ congrFun hG (t, x)⟩

/-- **Lifting a deformation.** The chosen lift, starting at the identity, of a deformation `K` of
the base of a Hurewicz fibration `q` starting at the identity: a deformation of the total space
lying over `K`. -/
noncomputable def liftDeformation (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) : C(I × X, X) :=
  (hq.exists_lift_deformation K h₀).choose

@[simp]
theorem liftDeformation_zero (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) (x : X) : hq.liftDeformation K h₀ (0, x) = x :=
  (hq.exists_lift_deformation K h₀).choose_spec.1 x

theorem apply_liftDeformation (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) (t : I) (x : X) :
    q (hq.liftDeformation K h₀ (t, x)) = K (t, q x) :=
  (hq.exists_lift_deformation K h₀).choose_spec.2 t x

/-- **The preimage of a weak deformation retract under a Hurewicz fibration.** Let `K` deform the
base of a Hurewicz fibration `q` onto `S` in the weak sense: it starts at the identity, ends inside
`S` and keeps `S` inside `S`. Then the inclusion of `q⁻¹ S` into the total space is a homotopy
equivalence, whose homotopy inverse is the end of the lift of `K` starting at the identity. -/
noncomputable def preimageHomotopyEquiv (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) (h₁ : ∀ y, K (1, y) ∈ S) (hS : ∀ t y, y ∈ S → K (t, y) ∈ S) :
    q ⁻¹' S ≃ₕ X :=
  (HomotopyEquiv.ofWeakDeformationRetraction (subset_univ (q ⁻¹' S))
    (fun z : I × (univ : Set X) ↦ hq.liftDeformation K h₀ (z.1, z.2)) (by fun_prop)
    (fun _ ↦ mem_univ _) (fun x ↦ hq.liftDeformation_zero K h₀ x)
    (fun x ↦ mem_preimage.2 (by rw [hq.apply_liftDeformation K h₀]; exact h₁ _))
    (fun t x hx ↦ mem_preimage.2 (by rw [hq.apply_liftDeformation K h₀]; exact hS t _ hx))).trans
    (Homeomorph.Set.univ X).toHomotopyEquiv

/-- The homotopy equivalence `TauCeti.IsHurewiczFibration.preimageHomotopyEquiv` is the
inclusion. -/
@[simp]
theorem preimageHomotopyEquiv_apply (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) (h₁ : ∀ y, K (1, y) ∈ S) (hS : ∀ t y, y ∈ S → K (t, y) ∈ S)
    (x : q ⁻¹' S) : hq.preimageHomotopyEquiv K h₀ h₁ hS x = x := by
  simp [preimageHomotopyEquiv]

/-- The homotopy inverse of `TauCeti.IsHurewiczFibration.preimageHomotopyEquiv` is the end of
the lift of the deformation. -/
@[simp]
theorem coe_preimageHomotopyEquiv_symm_apply (hq : IsHurewiczFibration.{u} q) (K : C(I × Y, Y))
    (h₀ : ∀ y, K (0, y) = y) (h₁ : ∀ y, K (1, y) ∈ S) (hS : ∀ t y, y ∈ S → K (t, y) ∈ S)
    (x : X) :
    ((hq.preimageHomotopyEquiv K h₀ h₁ hS).symm x : X) = hq.liftDeformation K h₀ (1, x) :=
  -- The homotopy inverse of `Homeomorph.Set.univ X` is the identity on underlying points.
  HomotopyEquiv.coe_ofWeakDeformationRetraction_symm_apply ..

end IsHurewiczFibration

end Preimage

/-! ### The pullback of a fibration along a path -/

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The pullback `{(t, e) | γ t = p e}` of `p : E → B` along a map `γ : I → B`. Its projection to
the interval is a Hurewicz fibration when `p` is one (`TauCeti.IsHurewiczFibration.pullback`), and
its fibre over `t` is the fibre of `p` over `γ t`. -/
abbrev PathPullback (p : E → B) (γ : C(I, B)) := {x : I × E // γ x.1 = p x.2}

namespace PathPullback

variable {p : E → B} {b : B}

/-- The inclusion of the fibre of `p` over `b` into the pullback along `γ`, as the fibre over a
point `t₀` of the interval with `γ t₀ = b`. -/
def fiberInclusion (γ : C(I, B)) (t₀ : I) (hb : γ t₀ = b) : C(p ⁻¹' {b}, PathPullback p γ) where
  toFun e := ⟨(t₀, e), hb.trans (e.2 : p e = b).symm⟩

@[simp]
theorem coe_fiberInclusion_apply (γ : C(I, B)) (t₀ : I) (hb : γ t₀ = b) (e : p ⁻¹' {b}) :
    (fiberInclusion γ t₀ hb e : I × E) = (t₀, (e : E)) :=
  (rfl)

/-- The fibre of the projection of the pullback along `γ` over `t₀` is homeomorphic to the fibre of
`p` over `b = γ t₀`. -/
def fiberHomeomorph (γ : C(I, B)) (t₀ : I) (hb : γ t₀ = b) :
    p ⁻¹' {b} ≃ₜ (fun x : PathPullback p γ ↦ x.1.1) ⁻¹' {t₀} where
  toFun e := ⟨fiberInclusion γ t₀ hb e, rfl⟩
  invFun x := ⟨x.1.1.2, by rw [mem_preimage, mem_singleton_iff, ← x.1.2, ← hb,
    mem_singleton_iff.1 (mem_preimage.1 x.2)]⟩
  left_inv _ := rfl
  right_inv x :=
    Subtype.ext (Subtype.ext (Prod.ext (mem_singleton_iff.1 (mem_preimage.1 x.2)).symm rfl))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end PathPullback

/-- The straight-line deformation `(s, t) ↦ (1 - s) t + s t₀` of the interval onto `t₀`. -/
private noncomputable def toPoint (t₀ : I) : C(I × I, I) where
  toFun z := Set.Icc.convexComb z.2 t₀ z.1
  continuous_toFun := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, Set.Icc.coe_convexComb]
    fun_prop

private theorem toPoint_zero (t₀ t : I) : toPoint t₀ (0, t) = t :=
  Set.Icc.convexComb_zero t t₀

private theorem toPoint_one (t₀ t : I) : toPoint t₀ (1, t) ∈ ({t₀} : Set I) :=
  Set.Icc.convexComb_one t t₀

private theorem toPoint_mem (t₀ s t : I) (ht : t ∈ ({t₀} : Set I)) :
    toPoint t₀ (s, t) ∈ ({t₀} : Set I) := by
  rw [mem_singleton_iff.1 ht]
  exact Set.Icc.convexComb_eq t₀ s

namespace IsHurewiczFibration

variable {p : E → B} {b b₀ b₁ : B}

/-- **The fibre of a Hurewicz fibration over a point of a path is a homotopy retract of the
pullback.** For a Hurewicz fibration `p` and a map `γ : I → B` with `γ t₀ = b`, the inclusion of
the fibre `p⁻¹ b` into the pullback of `p` along `γ`, over `t₀`, is a homotopy equivalence. Its
homotopy inverse is the end of a lift of the straight-line deformation of the interval onto
`t₀`. -/
noncomputable def pathPullbackHomotopyEquiv (hp : IsHurewiczFibration.{u} p) (γ : C(I, B))
    (t₀ : I) (hb : γ t₀ = b) : p ⁻¹' {b} ≃ₕ PathPullback p γ :=
  (PathPullback.fiberHomeomorph γ t₀ hb).toHomotopyEquiv.trans
    ((hp.pullback γ).preimageHomotopyEquiv (toPoint t₀) (toPoint_zero t₀) (toPoint_one t₀)
      (toPoint_mem t₀))

@[simp]
theorem pathPullbackHomotopyEquiv_apply (hp : IsHurewiczFibration.{u} p) (γ : C(I, B)) (t₀ : I)
    (hb : γ t₀ = b) (e : p ⁻¹' {b}) :
    hp.pathPullbackHomotopyEquiv γ t₀ hb e = PathPullback.fiberInclusion γ t₀ hb e :=
  -- The fibre homeomorphism sends `e` to its fibre inclusion, with the projection condition.
  (hp.pullback γ).preimageHomotopyEquiv_apply _ (toPoint_zero t₀) (toPoint_one t₀)
    (toPoint_mem t₀) _

/-- The homotopy inverse of the fibre inclusion into the pullback along `γ` deforms each point
along a lift of the straight-line deformation of the interval onto `t₀`, starting at that point;
this is the end point of the lift. -/
theorem exists_pathPullbackHomotopyEquiv_symm (hp : IsHurewiczFibration.{u} p) (γ : C(I, B))
    (t₀ : I) (hb : γ t₀ = b) :
    ∃ G : C(I × PathPullback p γ, PathPullback p γ), (∀ x, G (0, x) = x) ∧
      (∀ s x, (G (s, x)).1.1 = Set.Icc.convexComb x.1.1 t₀ s) ∧
      ∀ x, ((hp.pathPullbackHomotopyEquiv γ t₀ hb).symm x : E) = (G (1, x)).1.2 :=
  ⟨(hp.pullback γ).liftDeformation (toPoint t₀) (toPoint_zero t₀),
    (hp.pullback γ).liftDeformation_zero _ _, (hp.pullback γ).apply_liftDeformation _ _,
    -- The inverse of the fibre homeomorphism takes the `E`-coordinate.
    fun x ↦ congrArg (fun z ↦ z.1.2) ((hp.pullback γ).coe_preimageHomotopyEquiv_symm_apply _
      (toPoint_zero t₀) (toPoint_one t₀) (toPoint_mem t₀) x)⟩

/-- **Fibre transport along a path.** For a Hurewicz fibration `p` and a path `γ` from `b₀` to
`b₁`, the homotopy equivalence `p⁻¹ b₀ ≃ₕ p⁻¹ b₁` which includes the fibre over `b₀` into the
pullback of `p` along `γ`, over `t = 0`, and deforms the pullback into the fibre over `b₁`, over
`t = 1`. Its homotopy inverse includes the fibre over `b₁` and deforms the pullback into the fibre
over `b₀`. -/
noncomputable def transportHomotopyEquiv (hp : IsHurewiczFibration.{u} p) (γ : Path b₀ b₁) :
    p ⁻¹' {b₀} ≃ₕ p ⁻¹' {b₁} :=
  (hp.pathPullbackHomotopyEquiv γ 0 γ.source).trans
    (hp.pathPullbackHomotopyEquiv γ 1 γ.target).symm

theorem transportHomotopyEquiv_apply (hp : IsHurewiczFibration.{u} p) (γ : Path b₀ b₁)
    (e : p ⁻¹' {b₀}) :
    hp.transportHomotopyEquiv γ e = (hp.pathPullbackHomotopyEquiv γ 1 γ.target).symm
      (PathPullback.fiberInclusion γ 0 γ.source e) :=
  congrArg (hp.pathPullbackHomotopyEquiv γ 1 γ.target).symm
    (hp.pathPullbackHomotopyEquiv_apply γ 0 γ.source e)

theorem transportHomotopyEquiv_symm_apply (hp : IsHurewiczFibration.{u} p) (γ : Path b₀ b₁)
    (e : p ⁻¹' {b₁}) :
    (hp.transportHomotopyEquiv γ).symm e = (hp.pathPullbackHomotopyEquiv γ 0 γ.source).symm
      (PathPullback.fiberInclusion γ 1 γ.target e) :=
  congrArg (hp.pathPullbackHomotopyEquiv γ 0 γ.source).symm
    (hp.pathPullbackHomotopyEquiv_apply γ 1 γ.target e)

end IsHurewiczFibration

namespace LiftingFunction

variable {p : C(E, B)} {b₀ b₁ : B}

/-- **The transport of a lifting function is the fibre transport through the pullback.** For a
lifting function `Λ` of `p` and a path `γ`, the transport `Λ.transport γ`, which lifts `γ` from
each point of the fibre, is homotopic to the forward map of the fibre transport
`TauCeti.IsHurewiczFibration.transportHomotopyEquiv`. In particular `Λ.transport γ` is a homotopy
equivalence. -/
theorem transport_homotopic_transportHomotopyEquiv (Λ : LiftingFunction p) (γ : Path b₀ b₁) :
    (Λ.transport γ).Homotopic (Λ.isHurewiczFibration.{u}.transportHomotopyEquiv γ).toFun := by
  obtain ⟨G, hG₀, hG, hG₁⟩ :=
    Λ.isHurewiczFibration.{u}.exists_pathPullbackHomotopyEquiv_symm γ 1 γ.target
  -- Both maps are end points of lifts of `γ` from each point of the fibre over `b₀`: the lifts
  -- given by `Λ`, and the lifts traced in the pullback by the deformation onto `t = 1`.
  let f : C(p ⁻¹' {b₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  let Γ : C(p ⁻¹' {b₀} × I, B) := γ.toContinuousMap.comp ContinuousMap.snd
  have hΓ : ∀ y, Γ (y, 0) = p (f y) := fun y ↦ γ.source.trans (y.2 : p y.1 = b₀).symm
  let α' : C(p ⁻¹' {b₀} × I, E) :=
    ⟨fun z ↦ (G (z.2, PathPullback.fiberInclusion γ 0 γ.source z.1)).1.2, by fun_prop⟩
  have hα' : ∀ y t, p (α' (y, t)) = Γ (y, t) := fun y t ↦ by
    have h := (G (t, PathPullback.fiberInclusion γ 0 γ.source y)).2
    rw [hG] at h
    simpa [α', Γ] using h.symm
  obtain ⟨K, hK₀, hK₁, hK⟩ := Λ.isHurewiczFibration.{u}.exists_homotopy_endpoints Γ
    (Λ.liftFamily f Γ hΓ) α' (Λ.apply_liftFamily f Γ hΓ) hα' fun y ↦ by
      rw [Λ.liftFamily_zero]
      exact (congrArg (fun x ↦ x.1.2) (hG₀ (PathPullback.fiberInclusion γ 0 γ.source y))).symm
  refine ContinuousMap.homotopic_of_fiber _ _ K (fun y ↦ ?_) (fun y ↦ ?_)
    fun y s ↦ (hK y s).trans γ.target
  · rw [hK₀, Λ.liftFamily_apply, Λ.transport_apply_coe]
    exact congrArg (fun e ↦ e 1) (Λ.lift_congr rfl rfl _ _)
  · rw [hK₁, IsHurewiczFibration.transportHomotopyEquiv_apply, hG₁]
    rfl

end LiftingFunction

end TauCeti
