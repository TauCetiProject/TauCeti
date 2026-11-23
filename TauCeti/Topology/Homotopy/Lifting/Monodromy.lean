/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.Topology.Homotopy.Lifting.Basic
import TauCeti.Topology.Path.Map

/-!
# Monodromy on the path components of the fibres of a map that lifts homotopies of paths

Let `p : E → B` be a continuous map with the homotopy lifting property with respect to the
interval, for instance a Serre fibration
(`TauCeti.TopCat.hasHomotopyLiftingProperty_unitInterval_of_mem_serreFibrations`), a Hurewicz
fibration or a covering map. A path `γ` from `x` to `y` in `B` lifts, from any point `z` of the
fibre `p⁻¹(x)`, to a path of `E` ending in the fibre `p⁻¹(y)`. The end point depends on the chosen
lift, but its path component in `p⁻¹(y)` does not, nor does it change when `γ` moves in its
homotopy class or `z` in its path component
(`TauCeti.HasHomotopyLiftingProperty.joined_of_homotopic_of_lifts`). This defines the
**monodromy** of `p` on the path components of its fibres,

`TauCeti.HasHomotopyLiftingProperty.fiberMonodromy :
  Path.Homotopic.Quotient x y → π₀(p⁻¹(x)) → π₀(p⁻¹(y))`,

characterized by `TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_mk`: the monodromy of `[γ]`
sends the component of `z` to the component of the end of any lift of `γ` from `z`. It is
functorial on the fundamental groupoid of `B`
(`TauCeti.HasHomotopyLiftingProperty.fiberMonodromyFunctor`), so monodromy along a path class is a
bijection (`TauCeti.HasHomotopyLiftingProperty.fiberMonodromyEquiv`), and `π₁(B, b)` acts on the
path components of the fibre over `b`
(`TauCeti.HasHomotopyLiftingProperty.fiberMonodromyMulAction`).

For a fibration this action is the low end of the exact homotopy sequence
`π₁(E, e) → π₁(B, b) → π₀(F, e) → π₀(E, e)`, with `F = p⁻¹(b)`:

* monodromy along `γ` carries the component of `z` to that of `w` exactly when `γ` is the
  projection of a path class of `E` from `z` to `w`
  (`TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_eq_mk_iff`);
* so two points of fibres of `p` are joined in `E` exactly when monodromy along some path class
  of `B` carries the component of the first to that of the second
  (`TauCeti.HasHomotopyLiftingProperty.joined_iff_exists_fiberMonodromy_eq`), and the orbits of
  `π₁(B, b)` on `π₀(F)` are the fibres of the map `π₀(F) → π₀(E)`;
* a loop class of `B` at `b` fixes the component of `e` exactly when it comes from a loop of `E`
  at `e`: the stabiliser of that component is the image of `π₁(E, e)`
  (`TauCeti.HasHomotopyLiftingProperty.stabilizer_fiberMonodromy_eq_range`);
* hence the components of `F` that meet the path component of `e` in `E` are in bijection with
  `π₁(B, b) ⧸ p_*π₁(E, e)`
  (`TauCeti.HasHomotopyLiftingProperty.fiberMonodromyOrbitEquivQuotientRange`).

For a Serre fibration the boundary map `π₁(B, b) → π₀(F, e)` of the exact sequence is the orbit
map of the component of `e` (`TauCeti.TopCat.fibrationBoundary_eq_fiberMonodromy`, in
`TauCeti.Topology.Homotopy.SerreFibration.Exact`). For a covering map the fibres are discrete,
and the action is Mathlib's monodromy action `IsCoveringMap.fundamentalGroupMulAction` on the
points of the fibre.

## Main definitions

* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromy`: monodromy along a path class on the path
  components of the fibres.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromyFunctor`: monodromy as a functor on the
  fundamental groupoid.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromyEquiv`: monodromy along a path class as a
  bijection.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromyMulAction`: the action of `π₁(B, b)` on the
  path components of the fibre over `b`.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromyOrbitEquivQuotientRange`: the orbit of the
  component of `e` as the cosets of the image of `π₁(E, e)`.

## Main results

* `TauCeti.HasHomotopyLiftingProperty.joined_of_homotopic_of_lifts`: lifts of homotopic paths
  from joined points of a fibre end at joined points of a fibre.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_mk`: monodromy is computed by any lift.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_eq_mk_iff`: the lifting criterion.
* `TauCeti.HasHomotopyLiftingProperty.joined_iff_exists_fiberMonodromy_eq`,
  `TauCeti.HasHomotopyLiftingProperty.mem_orbit_fiberMonodromy_iff`: the orbits are the path
  components of `E`.
* `TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_eq_self_iff_mem_range`,
  `TauCeti.HasHomotopyLiftingProperty.stabilizer_fiberMonodromy_eq_range`: the stabiliser is the
  image of `π₁(E, e)`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2, Theorem 4.41 and the
  action of `π₁(B)` on the fibre that follows it.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
* The API follows Junyan Xu's monodromy of covering maps in Mathlib's
  `Mathlib/Topology/Homotopy/Lifting.lean` (`IsCoveringMap.monodromy`,
  `IsCoveringMap.fundamentalGroupMulAction`, `IsCoveringMap.monodromyFunctor`) and the stabiliser
  results of `TauCeti.Topology.Homotopy.Monodromy.Basic`
  (`IsCoveringMap.monodromy_eq_self_iff_mem_range`, `IsCoveringMap.fiberEquivQuotientRange`).
  No Mathlib proof is vendored.
-/

public noncomputable section

open CategoryTheory unitInterval

universe u v

namespace TauCeti.HasHomotopyLiftingProperty

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}

/-! ### Lifting paths up to the path components of the fibres -/

/-- A path of `E` that stays over `b` joins its ends inside the fibre over `b`. -/
private theorem joined_of_forall_eq {b : B} (c : C(I, E)) (hc : ∀ s, p (c s) = b)
    {y y' : p ⁻¹' {b}} (h₀ : c 0 = y) (h₁ : c 1 = y') : Joined y y' :=
  ⟨⟨⟨fun s ↦ ⟨c s, hc s⟩, by fun_prop⟩, Subtype.ext h₀, Subtype.ext h₁⟩⟩

/-- A path `δ` of `E` between two points of the fibre over `b`, whose projection is homotopic,
relative to its ends, to the constant path at `b`, joins them inside the fibre. -/
private theorem joined_of_homotopy_const (hp : HasHomotopyLiftingProperty p I) {b : B} (δ : C(I, E))
    (F : C(I × I, B)) (h₀ : ∀ t, F (0, t) = p (δ t)) (h₁ : ∀ t, F (1, t) = b)
    (hl : ∀ s, F (s, 0) = b) (hr : ∀ s, F (s, 1) = b) {y y' : p ⁻¹' {b}} (hy : δ 0 = y)
    (hy' : δ 1 = y') : Joined y y' := by
  -- Lift the homotopy from `δ`: its two sides and its end are paths in the fibre over `b`.
  obtain ⟨G, hG, hG₀⟩ := hp δ F h₀
  have hGF (x : I × I) : p (G x) = F x := congrFun hG x
  have hG₁ (t : I) : p (G (1, t)) = b := (hGF (1, t)).trans (h₁ t)
  exact ((joined_of_forall_eq ⟨fun s ↦ G (s, 0), by fun_prop⟩ (fun s ↦ (hGF _).trans (hl s))
      ((hG₀ 0).trans hy) (y' := ⟨_, hG₁ 0⟩) rfl).trans
    (joined_of_forall_eq ⟨fun t ↦ G (1, t), by fun_prop⟩ hG₁ rfl (y' := ⟨_, hG₁ 1⟩) rfl)).trans
    (joined_of_forall_eq ⟨fun s ↦ G (s, 1), by fun_prop⟩ (fun s ↦ (hGF _).trans (hr s))
      ((hG₀ 1).trans hy') rfl).symm

/-- Two lifts of the same path from the same point end at joined points of the fibre. -/
private theorem joined_of_lifts_of_eq (hp : HasHomotopyLiftingProperty p I) {x y : B} (γ : Path x y)
    {Γ Γ' : C(I, E)} (hΓ : p ∘ Γ = γ) (hΓ' : p ∘ Γ' = γ) (h₀ : Γ 0 = Γ' 0) {w w' : p ⁻¹' {y}}
    (hw : Γ 1 = w) (hw' : Γ' 1 = w') : Joined w w' := by
  -- The first lift reversed followed by the second lies over `γ⁻¹ γ`, which is null-homotopic.
  let δ : Path (Γ 1) (Γ' 1) :=
    (Path.mk Γ rfl rfl : Path (Γ 0) (Γ 1)).symm.trans (Path.mk Γ' h₀.symm rfl)
  let F := (Path.Homotopy.reflSymmTrans γ).symm
  have hδ : p ∘ δ = γ.symm.trans γ :=
    Path.comp_trans_eq_of_comp_eq (funext fun t ↦ congrFun hΓ (σ t)) hΓ'
  exact joined_of_homotopy_const hp δ F (fun t ↦ (F.apply_zero t).trans (congrFun hδ t).symm)
    (fun t ↦ F.apply_one t) (fun s ↦ F.source s) (fun s ↦ F.target s) (δ.source.trans hw)
    (δ.target.trans hw')

/-- Lifts of the same path from joined points of a fibre end at joined points of a fibre. -/
private theorem joined_of_lifts_of_joined (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path x y) {Γ Γ' : C(I, E)} (hΓ : p ∘ Γ = γ) (hΓ' : p ∘ Γ' = γ) {z z' : p ⁻¹' {x}}
    (hz : Γ 0 = z) (hz' : Γ' 0 = z') (h : Joined z z') {w w' : p ⁻¹' {y}} (hw : Γ 1 = w)
    (hw' : Γ' 1 = w') : Joined w w' := by
  -- Lift `γ` from every point `α s` of a path `α` from `z` to `z'`; the end points of these lifts
  -- move along a path in the fibre over `y`.
  obtain ⟨α⟩ := h
  obtain ⟨G, hG, hG₀⟩ := hp ⟨fun s ↦ (α s : E), by fun_prop⟩ ⟨fun x ↦ γ x.1, by fun_prop⟩
    fun s ↦ γ.source.trans (α s).property.symm
  have hGy (s : I) : p (G (1, s)) = y := (congrFun hG (1, s)).trans γ.target
  have hlift (s : I) : p ∘ (⟨fun t ↦ G (t, s), by fun_prop⟩ : C(I, E)) = γ :=
    funext fun t ↦ congrFun hG (t, s)
  refine ((joined_of_lifts_of_eq hp γ hΓ (hlift 0) ?_ hw (w' := ⟨_, hGy 0⟩) rfl).trans
    (joined_of_forall_eq ⟨fun s ↦ G (1, s), by fun_prop⟩ hGy rfl (y' := ⟨_, hGy 1⟩) rfl)).trans
    (joined_of_lifts_of_eq hp γ hΓ' (hlift 1) ?_ hw' rfl).symm
  · exact hz.trans ((congrArg Subtype.val α.source).symm.trans (hG₀ 0).symm)
  · exact hz'.trans ((congrArg Subtype.val α.target).symm.trans (hG₀ 1).symm)

/-- **Lifting homotopic paths up to path components.** Let `p` lift homotopies of paths, and let
`Γ₀`, `Γ₁` be lifts of homotopic paths `γ₀`, `γ₁` from `x` to `y`, starting at joined points `z₀`,
`z₁` of the fibre over `x`. Then they end at joined points of the fibre over `y`. -/
theorem joined_of_homotopic_of_lifts (hp : HasHomotopyLiftingProperty p I) {x y : B}
    {γ₀ γ₁ : Path x y} (hγ : γ₀.Homotopic γ₁) {Γ₀ Γ₁ : C(I, E)} (hΓ₀ : p ∘ Γ₀ = γ₀)
    (hΓ₁ : p ∘ Γ₁ = γ₁) {z₀ z₁ : p ⁻¹' {x}} (hz₀ : Γ₀ 0 = z₀) (hz₁ : Γ₁ 0 = z₁) (hz : Joined z₀ z₁)
    {w₀ w₁ : p ⁻¹' {y}} (hw₀ : Γ₀ 1 = w₀) (hw₁ : Γ₁ 1 = w₁) : Joined w₀ w₁ := by
  obtain ⟨H⟩ := hγ
  -- Lift the homotopy from `Γ₀`. Its end is a lift of `γ₁`, and its two sides are paths in the
  -- fibres over `x` and `y` from the ends of `Γ₀` to the ends of that lift.
  obtain ⟨G, hG, hG₀⟩ :=
    hp Γ₀ H.toContinuousMap fun t ↦ (H.apply_zero t).trans (congrFun hΓ₀ t).symm
  have hGH (s t : I) : p (G (s, t)) = H (s, t) := congrFun hG (s, t)
  have hx (s : I) : p (G (s, 0)) = x := (hGH s 0).trans (H.source s)
  have hy (s : I) : p (G (s, 1)) = y := (hGH s 1).trans (H.target s)
  have j₀ : Joined z₀ ⟨G (1, 0), hx 1⟩ :=
    joined_of_forall_eq ⟨fun s ↦ G (s, 0), by fun_prop⟩ hx ((hG₀ 0).trans hz₀) rfl
  have j₁ : Joined w₀ ⟨G (1, 1), hy 1⟩ :=
    joined_of_forall_eq ⟨fun s ↦ G (s, 1), by fun_prop⟩ hy ((hG₀ 1).trans hw₀) rfl
  have hlift : p ∘ (⟨fun t ↦ G (1, t), by fun_prop⟩ : C(I, E)) = γ₁ :=
    funext fun t ↦ (hGH 1 t).trans (H.apply_one t)
  exact j₁.trans (joined_of_lifts_of_joined hp γ₁ hlift hΓ₁ rfl hz₁ (j₀.symm.trans hz) rfl hw₁)

/-! ### Monodromy -/

/-- A chosen lift of `γ` from `z`. -/
private def lift (hp : HasHomotopyLiftingProperty p I) {x y : B} (γ : Path x y)
    (z : p ⁻¹' {x}) : C(I, E) :=
  (hp.exists_path_lift (γ.cast z.property rfl)).choose

private theorem lift_spec (hp : HasHomotopyLiftingProperty p I) {x y : B} (γ : Path x y)
    (z : p ⁻¹' {x}) : p ∘ lift hp γ z = γ ∧ lift hp γ z 0 = z :=
  ⟨(hp.exists_path_lift (γ.cast z.property rfl)).choose_spec.2,
    (hp.exists_path_lift (γ.cast z.property rfl)).choose_spec.1⟩

/-- The end point of the chosen lift of `γ` from `z`, in the fibre over the end of `γ`. -/
private def liftEnd (hp : HasHomotopyLiftingProperty p I) {x y : B} (γ : Path x y)
    (z : p ⁻¹' {x}) : p ⁻¹' {y} :=
  ⟨lift hp γ z 1, (congrFun (lift_spec hp γ z).1 1).trans γ.target⟩

/-- The path component of `liftEnd` depends only on the homotopy class of the path and on the
path component of the starting point. -/
private theorem joined_liftEnd (hp : HasHomotopyLiftingProperty p I) {x y : B} {γ₀ γ₁ : Path x y}
    (hγ : γ₀.Homotopic γ₁) {z₀ z₁ : p ⁻¹' {x}} (hz : Joined z₀ z₁) :
    Joined (liftEnd hp γ₀ z₀) (liftEnd hp γ₁ z₁) :=
  joined_of_homotopic_of_lifts hp hγ (lift_spec hp γ₀ z₀).1 (lift_spec hp γ₁ z₁).1
    (lift_spec hp γ₀ z₀).2 (lift_spec hp γ₁ z₁).2 hz rfl rfl

/-- **The monodromy of `p` on the path components of its fibres.** For a homotopy
class `γ` of paths from `x` to `y`, it sends the path component of a point `z` of the fibre over
`x` to the path component, in the fibre over `y`, of the end of a lift of a representative of
`γ` from `z` (`TauCeti.HasHomotopyLiftingProperty.fiberMonodromy_mk`). -/
def fiberMonodromy (hp : HasHomotopyLiftingProperty p I) {x y : B} (γ : Path.Homotopic.Quotient x y)
    (c : ZerothHomotopy (p ⁻¹' {x})) : ZerothHomotopy (p ⁻¹' {y}) :=
  Quotient.lift₂ (s₁ := Path.Homotopic.setoid x y) (s₂ := pathSetoid (p ⁻¹' {x}))
    (fun γ z ↦ ZerothHomotopy.mk (liftEnd hp γ z))
    (fun _ _ _ _ hγ hz ↦ ZerothHomotopy.sound (joined_liftEnd hp hγ hz).somePath) γ c

/-- **Monodromy is computed by any lift.** The monodromy along the class of a path `γ` sends the
path component of `z` to the path component of the end `w` of any lift of `γ` from `z`. -/
theorem fiberMonodromy_mk (hp : HasHomotopyLiftingProperty p I) {x y : B} (γ : Path x y)
    {Γ : C(I, E)} (hΓ : p ∘ Γ = γ) {z : p ⁻¹' {x}} (hz : Γ 0 = z) {w : p ⁻¹' {y}}
    (hw : Γ 1 = w) : fiberMonodromy hp (.mk γ) (.mk z) = .mk w :=
  ZerothHomotopy.sound (joined_of_homotopic_of_lifts hp (.refl γ) (lift_spec hp γ z).1 hΓ
    (lift_spec hp γ z).2 hz (.refl z) (rfl : _ = (liftEnd hp γ z : E)) hw).somePath

/-- Monodromy along the constant path is the identity. -/
@[simp]
theorem fiberMonodromy_refl (hp : HasHomotopyLiftingProperty p I) (x : B) :
    fiberMonodromy hp (.refl x) = id := by
  funext c
  induction c with | mk z =>
  exact fiberMonodromy_mk hp (Path.refl x) (Γ := .const I (z : E)) (funext fun _ ↦ z.property)
    rfl rfl

/-- Monodromy along a concatenation is the composite of the monodromies. -/
theorem fiberMonodromy_trans_apply (hp : HasHomotopyLiftingProperty p I) {x y z : B}
    (γ : Path.Homotopic.Quotient x y) (γ' : Path.Homotopic.Quotient y z)
    (c : ZerothHomotopy (p ⁻¹' {x})) :
    fiberMonodromy hp (γ.trans γ') c = fiberMonodromy hp γ' (fiberMonodromy hp γ c) := by
  induction γ with | mk γ =>
  induction γ' with | mk γ' =>
  induction c with | mk e =>
  obtain ⟨hΓ, he⟩ := lift_spec hp γ e
  set Γ := lift hp γ e
  have hΓy : p (Γ 1) = y := (congrFun hΓ 1).trans γ.target
  obtain ⟨hΓ', he'⟩ := lift_spec hp γ' ⟨Γ 1, hΓy⟩
  set Γ' := lift hp γ' ⟨Γ 1, hΓy⟩
  have hΓz : p (Γ' 1) = z := (congrFun hΓ' 1).trans γ'.target
  let Γ'' : Path (Γ 0) (Γ' 1) := (Path.mk Γ rfl rfl : Path (Γ 0) (Γ 1)).trans (Path.mk Γ' he' rfl)
  have hΓ'' : p ∘ Γ'' = γ.trans γ' := Path.comp_trans_eq_of_comp_eq hΓ hΓ'
  rw [← Path.Homotopic.Quotient.mk_trans, fiberMonodromy_mk hp _ hΓ'' (Γ''.source.trans he)
    (w := ⟨Γ' 1, hΓz⟩) Γ''.target, fiberMonodromy_mk hp γ hΓ he (w := ⟨Γ 1, hΓy⟩) rfl,
    fiberMonodromy_mk hp γ' hΓ' he' (w := ⟨Γ' 1, hΓz⟩) rfl]

/-- **Monodromy as a functor on the fundamental groupoid**: it sends a point of `B` to the set of
path components of the fibre over it, and a homotopy class of paths to the monodromy along it. -/
@[expose, simps]
def fiberMonodromyFunctor (hp : HasHomotopyLiftingProperty p I) :
    FundamentalGroupoid B ⥤ Type u where
  obj x := ZerothHomotopy (p ⁻¹' ({x.as} : Set B))
  map γ := ↾(fiberMonodromy hp γ)
  map_id x := by ext c : 3; exact congrFun (fiberMonodromy_refl hp x.as) c
  map_comp γ γ' := by ext c : 3; exact fiberMonodromy_trans_apply hp γ γ' c

/-- Monodromy along the reversed class undoes monodromy along `γ`. -/
@[simp]
theorem fiberMonodromy_symm_fiberMonodromy (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : ZerothHomotopy (p ⁻¹' {x})) :
    fiberMonodromy hp γ.symm (fiberMonodromy hp γ c) = c := by
  rw [← fiberMonodromy_trans_apply, Path.Homotopic.Quotient.trans_symm, fiberMonodromy_refl, id]

/-- Monodromy along `γ` undoes monodromy along the reversed class. -/
@[simp]
theorem fiberMonodromy_fiberMonodromy_symm (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : ZerothHomotopy (p ⁻¹' {y})) :
    fiberMonodromy hp γ (fiberMonodromy hp γ.symm c) = c := by
  rw [← fiberMonodromy_trans_apply, Path.Homotopic.Quotient.symm_trans, fiberMonodromy_refl, id]

/-- **Monodromy along a path class is a bijection** between the path components of the fibres over
its ends, with inverse the monodromy along the reversed class. -/
def fiberMonodromyEquiv (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path.Homotopic.Quotient x y) :
    ZerothHomotopy (p ⁻¹' {x}) ≃ ZerothHomotopy (p ⁻¹' {y}) where
  toFun := fiberMonodromy hp γ
  invFun := fiberMonodromy hp γ.symm
  left_inv := fiberMonodromy_symm_fiberMonodromy hp γ
  right_inv := fiberMonodromy_fiberMonodromy_symm hp γ

@[simp]
theorem fiberMonodromyEquiv_apply (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : ZerothHomotopy (p ⁻¹' {x})) :
    fiberMonodromyEquiv hp γ c = fiberMonodromy hp γ c :=
  (rfl)

@[simp]
theorem fiberMonodromyEquiv_symm_apply (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : ZerothHomotopy (p ⁻¹' {y})) :
    (fiberMonodromyEquiv hp γ).symm c = fiberMonodromy hp γ.symm c :=
  (rfl)

/-- **The action of `π₁(B, b)` on the path components of the fibre over `b`**, by monodromy. Since
`γ * γ'` is `γ'` followed by `γ` in `FundamentalGroup`, monodromy is a left action. -/
abbrev fiberMonodromyMulAction (hp : HasHomotopyLiftingProperty p I) (b : B) :
    MulAction (FundamentalGroup B b) (ZerothHomotopy (p ⁻¹' {b})) where
  smul γ c := fiberMonodromy hp γ.asHom c
  one_smul := congrFun (fiberMonodromy_refl hp b)
  mul_smul γ γ' c := fiberMonodromy_trans_apply hp γ'.asHom γ.asHom c

/-- A loop class acts on the path components of the fibre by the monodromy along it. -/
theorem smul_eq_fiberMonodromy (hp : HasHomotopyLiftingProperty p I) {b : B}
    (γ : FundamentalGroup B b) (c : ZerothHomotopy (p ⁻¹' {b})) :
    letI := fiberMonodromyMulAction hp b
    γ • c = fiberMonodromy hp γ.asHom c :=
  (rfl)

/-! ### The orbits and the stabilisers -/

/-- **The lifting criterion for monodromy.** Monodromy along `γ` carries the path component of `z`
to that of `w` exactly when `γ` is the projection of a homotopy class of paths of `E` from `z` to
`w`. -/
theorem fiberMonodromy_eq_mk_iff (hp : HasHomotopyLiftingProperty p I) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (z : p ⁻¹' {x}) (w : p ⁻¹' {y}) :
    fiberMonodromy hp γ (.mk z) = .mk w ↔
      ∃ δ : Path.Homotopic.Quotient (z : E) (w : E),
        (δ.map p).cast z.property.symm w.property.symm = γ := by
  constructor
  · induction γ with | mk γ =>
    intro hγ
    obtain ⟨hΓ, hz⟩ := lift_spec hp γ z
    set Γ := lift hp γ z
    have hΓy : p (Γ 1) = y := (congrFun hΓ 1).trans γ.target
    rw [fiberMonodromy_mk hp γ hΓ hz (w := ⟨Γ 1, hΓy⟩) rfl] at hγ
    -- Follow the lift of `γ` by a path to `w` in the fibre over `y`.
    obtain ⟨α⟩ := (Quotient.exact hγ : Joined (⟨Γ 1, hΓy⟩ : p ⁻¹' {y}) w)
    let δ : Path (z : E) w := (Path.mk Γ hz rfl).trans (α.map continuous_subtypeVal)
    have hδ : (δ.map p.continuous).cast z.property.symm w.property.symm = γ.trans (Path.refl y) :=
      Path.ext (Path.comp_trans_eq_of_comp_eq hΓ (funext fun t ↦ (α t).property))
    refine ⟨.mk δ, ?_⟩
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast, hδ,
      Path.Homotopic.Quotient.eq]
    exact Path.Homotopic.trans_refl γ
  · rintro ⟨δ, rfl⟩
    induction δ with | mk δ =>
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    exact fiberMonodromy_mk hp _ (Γ := δ.toContinuousMap) rfl δ.source δ.target

/-- **The orbits of monodromy are the path components of the total space.** A point `z` of the
fibre over `x` and a point `w` of the fibre over `y` are joined in `E` exactly when the
monodromy along some homotopy class of paths from `x` to `y` carries the path component of `z`
to that of `w`. -/
theorem joined_iff_exists_fiberMonodromy_eq (hp : HasHomotopyLiftingProperty p I) {x y : B}
    {z : p ⁻¹' {x}} {w : p ⁻¹' {y}} :
    Joined (z : E) (w : E) ↔
      ∃ γ : Path.Homotopic.Quotient x y, fiberMonodromy hp γ (.mk z) = .mk w := by
  constructor
  · rintro ⟨δ⟩
    exact ⟨_, (fiberMonodromy_eq_mk_iff hp _ z w).2 ⟨.mk δ, rfl⟩⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨δ, -⟩ := (fiberMonodromy_eq_mk_iff hp γ z w).1 hγ
    induction δ with | mk δ => exact ⟨δ⟩

/-- **The stabiliser of a path component of the fibre.** A loop class of the base at `b` fixes the
path component of a point `e` of the fibre over `b` exactly when it is the image of a loop class
of the total space at `e`. -/
theorem fiberMonodromy_eq_self_iff_mem_range (hp : HasHomotopyLiftingProperty p I) {b : B}
    (e : p ⁻¹' {b}) (γ : FundamentalGroup B b) :
    fiberMonodromy hp γ.asHom (.mk e) = .mk e ↔
      γ ∈ (FundamentalGroup.mapOfEq p e.property).range := by
  rw [fiberMonodromy_eq_mk_iff]
  constructor
  · rintro ⟨δ, hδ⟩
    exact ⟨.of δ, End.ext ((congrArg End.asHom (FundamentalGroup.mapOfEq_apply _ _ _)).trans hδ)⟩
  · rintro ⟨δ, rfl⟩
    exact ⟨δ.asHom, (congrArg End.asHom (FundamentalGroup.mapOfEq_apply _ _ _)).symm⟩

/-- The stabiliser of the path component of a point `e` of the fibre over `b`, for the monodromy
action of `π₁(B, b)`, is the image of `π₁(E, e)`. -/
theorem stabilizer_fiberMonodromy_eq_range (hp : HasHomotopyLiftingProperty p I) {b : B}
    (e : p ⁻¹' {b}) :
    letI := fiberMonodromyMulAction hp b
    MulAction.stabilizer (FundamentalGroup B b) (ZerothHomotopy.mk e) =
      (FundamentalGroup.mapOfEq p e.property).range := by
  ext γ
  exact fiberMonodromy_eq_self_iff_mem_range hp e γ

/-- The path component of a point `y` of the fibre over `b` lies in the orbit of the path
component of `e` under `π₁(B, b)` exactly when `e` and `y` are joined in `E`. -/
theorem mem_orbit_fiberMonodromy_iff (hp : HasHomotopyLiftingProperty p I) {b : B}
    (e y : p ⁻¹' {b}) :
    letI := fiberMonodromyMulAction hp b
    ZerothHomotopy.mk y ∈ MulAction.orbit (FundamentalGroup B b) (ZerothHomotopy.mk e) ↔
      Joined (e : E) (y : E) := by
  let := fiberMonodromyMulAction hp b
  rw [MulAction.mem_orbit_iff, joined_iff_exists_fiberMonodromy_eq hp]
  exact ⟨fun ⟨γ, h⟩ ↦ ⟨γ.asHom, h⟩, fun ⟨γ, h⟩ ↦ ⟨.of γ, h⟩⟩

/-- **Orbit and stabiliser of a path component of the fibre.** The path components of the fibre
over `b` reached from that of `e` by the monodromy action of `π₁(B, b)`, which are those meeting
the path component of `e` in `E`
(`TauCeti.HasHomotopyLiftingProperty.mem_orbit_fiberMonodromy_iff`), are in bijection with the
cosets of the image of `π₁(E, e)` in `π₁(B, b)`. -/
def fiberMonodromyOrbitEquivQuotientRange (hp : HasHomotopyLiftingProperty p I) {b : B}
    (e : p ⁻¹' {b}) :
    letI := fiberMonodromyMulAction hp b
    MulAction.orbit (FundamentalGroup B b) (ZerothHomotopy.mk e) ≃
      FundamentalGroup B b ⧸ (FundamentalGroup.mapOfEq p e.property).range :=
  letI := fiberMonodromyMulAction hp b
  (MulAction.orbitEquivQuotientStabilizer _ _).trans
    (Subgroup.quotientEquivOfEq (stabilizer_fiberMonodromy_eq_range hp e))

/-- The inverse of `TauCeti.HasHomotopyLiftingProperty.fiberMonodromyOrbitEquivQuotientRange` sends
the coset of a loop class `γ` to the monodromy of `γ` applied to the path component of `e`. -/
@[simp]
theorem coe_fiberMonodromyOrbitEquivQuotientRange_symm_apply
    (hp : HasHomotopyLiftingProperty p I) {b : B} (e : p ⁻¹' {b}) (γ : FundamentalGroup B b) :
    ((fiberMonodromyOrbitEquivQuotientRange hp e).symm γ : ZerothHomotopy (p ⁻¹' {b})) =
      fiberMonodromy hp γ.asHom (.mk e) :=
  (rfl)

end TauCeti.HasHomotopyLiftingProperty
