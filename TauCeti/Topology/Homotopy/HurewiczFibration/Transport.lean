/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction
public import TauCeti.Topology.Homotopy.OpenBoxLifting

/-!
# Transport in the fibers of a Hurewicz fibration

Let `p : E → B` be a Hurewicz fibration with a lifting function `Λ`.  Lifting a path `γ` from
`b₀` to `b₁` starting at each point of the fiber over `b₀` and taking the end point gives the
**transport** `Λ.transport γ : p⁻¹ b₀ → p⁻¹ b₁`, a continuous map between the fibers.  The
transport depends on the path only up to homotopy, and is compatible with the identity and with
concatenation, up to homotopy of maps between the fibers.  The homology of the fibers is
therefore a local coefficient system
(`TauCeti.AlgebraicTopology.Singular.Fibration.LocalSystem`).

## Main definitions

* `TauCeti.LiftingFunction.transport Λ γ`: the transport of the fibers along a path `γ`.

## Main results

* `TauCeti.LiftingFunction.exists_lift_trans`: the lift of a concatenation of paths, from each
  point of the fiber, ends at the iterated transport.
* `TauCeti.LiftingFunction.transport_homotopic`: homotopic paths have homotopic transports.
* `TauCeti.LiftingFunction.transport_refl_homotopic`,
  `TauCeti.LiftingFunction.transport_trans_homotopic`: transport along the constant path is
  homotopic to the identity, and transport along a concatenation is homotopic to the composite.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, and Proposition 4.61.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

namespace LiftingFunction

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
  (Λ : LiftingFunction p)

section Transport

variable {b₀ b₁ b₂ : B}

/-- **Transport** in the fibers of a Hurewicz fibration with lifting function `Λ`: the continuous
map from the fiber over `b₀` to the fiber over `b₁` sending a point to the end point of the lift of
the path `γ` starting at it. -/
def transport (γ : Path b₀ b₁) : C(p ⁻¹' {b₀}, p ⁻¹' {b₁}) :=
  ⟨fun x ↦ ⟨Λ.lift x.1 γ.toContinuousMap (γ.source.trans (x.2 : p x.1 = b₀).symm) 1,
      (Λ.apply_lift _ _ _ 1).trans γ.target⟩,
    Continuous.subtype_mk
      ((continuous_eval_const (1 : I)).comp
        (Λ.continuous_lift continuous_subtype_val continuous_const _)) _⟩

/-- The end point of the lift of `γ` from `x` is the image of `x` under the transport. -/
theorem transport_apply_coe (γ : Path b₀ b₁) (x : p ⁻¹' {b₀}) :
    (Λ.transport γ x).1 = Λ.lift x.1 γ.toContinuousMap (γ.source.trans (x.2 : p x.1 = b₀).symm) 1 :=
  (rfl)

/-- The end point of the lift of the family `γ ∘ snd`, constant in `Y`, from the points `f y` is
the transport of any point `x` with `f y = x`. -/
private theorem liftFamily_comp_snd_one {Y : Type*} [TopologicalSpace Y] (f : C(Y, E))
    (γ : Path b₀ b₁) (h : ∀ y, (γ.toContinuousMap.comp ContinuousMap.snd) (y, 0) = p (f y))
    (y : Y) (x : p ⁻¹' {b₀}) (hx : f y = x.1) :
    Λ.liftFamily f (γ.toContinuousMap.comp ContinuousMap.snd) h (y, 1) = (Λ.transport γ x).1 := by
  rw [Λ.liftFamily_apply, Λ.transport_apply_coe]
  exact congrArg (fun e ↦ e 1) (Λ.lift_congr hx rfl _ _)

/-- Transport along a constant path is homotopic to the identity of the fiber. -/
theorem transport_refl_homotopic (b : B) :
    (Λ.transport (Path.refl b)).Homotopic (ContinuousMap.id _) := by
  let f : C(p ⁻¹' {b}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  let Γ : C(p ⁻¹' {b} × I, B) := (Path.refl b).toContinuousMap.comp ContinuousMap.snd
  have h : ∀ y, Γ (y, 0) = p (f y) := fun y ↦ (y.2 : p y.1 = b).symm
  obtain ⟨K, hK₀, hK₁, hK⟩ := Λ.isHurewiczFibration.{u}.exists_homotopy_endpoints
    Γ (Λ.liftFamily f _ h) ⟨fun z ↦ z.1.1, by fun_prop⟩
    (Λ.apply_liftFamily f _ h) (fun y t ↦ (y.2 : p y.1 = b)) (fun y ↦ Λ.liftFamily_zero f _ h y)
  exact ContinuousMap.homotopic_of_fiber _ _ K
    (fun y ↦ (hK₀ y).trans (Λ.liftFamily_comp_snd_one f _ h y y rfl)) hK₁ hK

/-- Homotopic paths have homotopic transports. -/
theorem transport_homotopic {γ γ' : Path b₀ b₁} (h : γ.Homotopic γ') :
    (Λ.transport γ).Homotopic (Λ.transport γ') := by
  obtain ⟨F⟩ := h
  -- The family over `(y, s)` of the lifts of the paths `F s` from `y`.
  let f : C(p ⁻¹' {b₀} × I, E) := ⟨fun z ↦ z.1.1, by fun_prop⟩
  let G : C((p ⁻¹' {b₀} × I) × I, B) := ⟨fun z ↦ F (z.1.2, z.2), by fun_prop⟩
  have f_apply : ∀ z, f z = z.1.1 := fun _ ↦ (rfl) -- the definition of `f`
  have G_apply : ∀ z, G z = F (z.1.2, z.2) := fun _ ↦ (rfl) -- the definition of `G`
  have hG : ∀ z, G (z, 0) = p (f z) := fun z ↦ by
    rw [G_apply, f_apply, F.source]
    exact (z.1.2 : p z.1.1 = b₀).symm
  let L := Λ.liftFamily f G hG
  let K : C(p ⁻¹' {b₀} × I, E) := ⟨fun z ↦ L ((z.1, z.2), 1), by fun_prop⟩
  have K_apply : ∀ y s, K (y, s) = L ((y, s), 1) := fun _ _ ↦ (rfl) -- the definition of `K`
  -- The lift at `s = 0` and `s = 1` is the lift along `γ` and `γ'`.
  have hend : ∀ (δ : Path b₀ b₁) (s : I), (∀ t, F (s, t) = δ t) → ∀ y,
      L ((y, s), 1) = (Λ.transport δ y).1 := fun δ s hs y ↦ by
    rw [Λ.liftFamily_apply, Λ.transport_apply_coe]
    refine congrArg (fun e ↦ e 1) (Λ.lift_congr (f_apply _) ?_ _ _)
    exact ContinuousMap.ext fun t ↦ (G_apply _).trans (hs t)
  refine ContinuousMap.homotopic_of_fiber _ _ K (fun y ↦ ?_) (fun y ↦ ?_) fun y s ↦ ?_
  · exact (K_apply y 0).trans (hend γ 0 F.apply_zero y)
  · exact (K_apply y 1).trans (hend γ' 1 F.apply_one y)
  · rw [K_apply]
    exact (Λ.apply_liftFamily f G hG (y, s) 1).trans ((G_apply _).trans (F.target s))

/-- **Lifting a concatenation of paths.**  For paths `γ` and `δ`, there is a family of lifts of
`γ.trans δ`, starting at each point `y` of the fiber over `b₀`, that ends at the transport of `y`
along `γ` followed by the transport along `δ`. -/
theorem exists_lift_trans (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    ∃ C : C(p ⁻¹' {b₀} × I, E), (∀ y, C (y, 0) = y.1) ∧
      (∀ y, C (y, 1) = (Λ.transport δ (Λ.transport γ y)).1) ∧
      ∀ y t, p (C (y, t)) = (γ.trans δ) t := by
  let f : C(p ⁻¹' {b₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  -- The constant-in-`y` families of paths `γ`, `δ` and `γ.trans δ` over the fiber.
  let Γγ : C(p ⁻¹' {b₀} × I, B) := γ.toContinuousMap.comp ContinuousMap.snd
  let Γδ : C(p ⁻¹' {b₀} × I, B) := δ.toContinuousMap.comp ContinuousMap.snd
  let Γ : C(p ⁻¹' {b₀} × I, B) := (γ.trans δ).toContinuousMap.comp ContinuousMap.snd
  have Γγ_apply : ∀ z, Γγ z = γ z.2 := fun _ ↦ (rfl) -- the definition of `Γγ`
  have Γδ_apply : ∀ z, Γδ z = δ z.2 := fun _ ↦ (rfl) -- the definition of `Γδ`
  have Γ_apply : ∀ z, Γ z = (γ.trans δ) z.2 := fun _ ↦ (rfl) -- the definition of `Γ`
  have hγ : ∀ y, Γγ (y, 0) = p (f y) := fun y ↦ γ.source.trans (y.2 : p y.1 = b₀).symm
  -- The lift of `γ`, and then the lift of `δ` from its end point.
  let A := Λ.liftFamily f _ hγ
  let f' : C(p ⁻¹' {b₀}, E) := ⟨fun y ↦ A (y, 1), by fun_prop⟩
  have f'_apply : ∀ y, f' y = A (y, 1) := fun _ ↦ (rfl) -- the definition of `f'`
  have hδ : ∀ y, Γδ (y, 0) = p (f' y) := fun y ↦ by
    rw [f'_apply, Λ.apply_liftFamily]
    exact δ.source.trans γ.target.symm
  let D := Λ.liftFamily f' _ hδ
  -- The two lifts as paths, which are concatenated.
  let pa : ∀ y : p ⁻¹' {b₀}, Path (f y) (A (y, 1)) := fun y ↦
    { toContinuousMap := A.curry y
      source' := Λ.liftFamily_zero f _ hγ y
      target' := rfl }
  let pd : ∀ y : p ⁻¹' {b₀}, Path (A (y, 1)) (D (y, 1)) := fun y ↦
    { toContinuousMap := D.curry y
      source' := (Λ.liftFamily_zero f' _ hδ y).trans (f'_apply y)
      target' := rfl }
  have hpa : Continuous ↿pa := A.continuous -- the paths `pa y` are the curried map `A`
  have hpd : Continuous ↿pd := D.continuous -- the paths `pd y` are the curried map `D`
  let C₂ : C(p ⁻¹' {b₀} × I, E) :=
    ⟨fun z ↦ ((pa z.1).trans (pd z.1)) z.2,
      (Path.trans_continuous_family pa hpa pd hpd).comp continuous_id⟩
  have C₂_apply : ∀ z, C₂ z = ((pa z.1).trans (pd z.1)) z.2 :=
    fun _ ↦ (rfl) -- the definition of `C₂`
  have hC : ∀ y t, p (C₂ (y, t)) = Γ (y, t) := by
    intro y t
    rw [Γ_apply, Path.trans_apply, C₂_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [ht, ↓reduceDIte]
      exact (Λ.apply_liftFamily f _ hγ y _).trans (Γγ_apply _)
    · simp only [ht, ↓reduceDIte]
      exact (Λ.apply_liftFamily f' _ hδ y _).trans (Γδ_apply _)
  refine ⟨C₂, fun y ↦ ?_, fun y ↦ ?_, fun y t ↦ ?_⟩
  · rw [C₂_apply]
    exact Path.source _
  · -- At time `1` the concatenation is at the end of the second path, the lift of `δ` from the end
    -- point of the lift of `γ`.
    rw [C₂_apply, Path.target]
    exact Λ.liftFamily_comp_snd_one f' δ hδ y (Λ.transport γ y)
      (Λ.liftFamily_comp_snd_one f γ hγ y y rfl)
  · exact (hC y t).trans (Γ_apply _)

/-- Transport along a concatenation of paths is homotopic to the composite of the transports. -/
theorem transport_trans_homotopic (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    (Λ.transport (γ.trans δ)).Homotopic ((Λ.transport δ).comp (Λ.transport γ)) := by
  obtain ⟨C, hC₀, hC₁, hC⟩ := Λ.exists_lift_trans γ δ
  let f : C(p ⁻¹' {b₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  let Γ : C(p ⁻¹' {b₀} × I, B) := (γ.trans δ).toContinuousMap.comp ContinuousMap.snd
  have Γ_apply : ∀ z, Γ z = (γ.trans δ) z.2 := fun _ ↦ (rfl) -- the definition of `Γ`
  have hz : ∀ y, Γ (y, 0) = p (f y) := fun y ↦ (γ.trans δ).source.trans (y.2 : p y.1 = b₀).symm
  obtain ⟨K, hK₀, hK₁, hK⟩ := Λ.isHurewiczFibration.{u}.exists_homotopy_endpoints Γ
    (Λ.liftFamily f _ hz) C (Λ.apply_liftFamily f _ hz)
    (fun y t ↦ (hC y t).trans (Γ_apply (y, t)).symm)
    fun y ↦ (Λ.liftFamily_zero f _ hz y).trans (hC₀ y).symm
  exact ContinuousMap.homotopic_of_fiber _ _ K
    (fun y ↦ (hK₀ y).trans (Λ.liftFamily_comp_snd_one f _ hz y y rfl))
    (fun y ↦ (hK₁ y).trans (hC₁ y)) fun y s ↦ (hK y s).trans (γ.trans δ).target

end Transport

end LiftingFunction

end TauCeti
