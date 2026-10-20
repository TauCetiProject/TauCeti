/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction
public import TauCeti.Topology.Homotopy.OpenBoxLifting

/-!
# Transport in the fibres of a Hurewicz fibration

Let `p : E → B` be a Hurewicz fibration with a lifting function `Λ`.  Lifting a path `γ` from
`b₀` to `b₁` starting at each point of the fibre over `b₀` and taking the end point gives the
**transport** `Λ.transport γ : p⁻¹ b₀ → p⁻¹ b₁`, a continuous map between the fibres.  The
transport depends on the path only up to homotopy, and is compatible with the identity and with
concatenation, up to homotopy of maps between the fibres.  Hence it induces a functor from the
fundamental groupoid of `B` to the homotopy category of spaces, and the homology of the fibres
forms a local coefficient system (`TauCeti.LocalCoefficientSystem`, see
`TauCeti.AlgebraicTopology.Singular.Fibration.LocalSystem`).

The two homotopy statements both come from one lemma on the uniqueness of lifts of paths up to
homotopy in the fibre (`TauCeti.LiftingFunction.exists_homotopy_endpoints`): two lifts of the same
path with the same starting point have homotopic end points, through points of one fibre, and the
homotopy depends continuously on parameters.  Its proof lifts a square, constant on the base in one
direction, from the open box formed by the start and the two lifts
(`TauCeti.IsHurewiczFibration.exists_lift_openBox`).

## Main definitions

* `ContinuousMap.glueHalves s a a'`: glue two maps along the halves `s ≤ 1/2` and `1/2 ≤ s`.
* `TauCeti.LiftingFunction.transport Λ γ`: the transport of the fibres along a path `γ`.

## Main results

* `ContinuousMap.homotopic_of_fibre`: a homotopy over a fixed point of the base is a homotopy of
  maps into the fibre.
* `TauCeti.LiftingFunction.exists_homotopy_endpoints`: lifts of one path with one starting point
  have homotopic end points.
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

namespace ContinuousMap

/-- Glue two maps along the two halves `s ≤ 1/2` and `1/2 ≤ s` of the parameter `s`, assuming
that they agree where `s = 1/2`. -/
noncomputable def glueHalves {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X] (s : C(Z, I))
    (a a' : C(Z, X)) (h : ∀ z, (s z : ℝ) = 1 / 2 → a z = a' z) : C(Z, X) :=
  ⟨fun z ↦ if (s z : ℝ) ≤ 1 / 2 then a z else a' z,
    Continuous.if_le a.continuous a'.continuous (continuous_subtype_val.comp s.continuous)
      continuous_const h⟩

variable {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X] (s : C(Z, I))
  (a a' : C(Z, X)) (h : ∀ z, (s z : ℝ) = 1 / 2 → a z = a' z) {z : Z}

theorem glueHalves_of_le (hz : (s z : ℝ) ≤ 1 / 2) : glueHalves s a a' h z = a z :=
  by simp only [glueHalves, ContinuousMap.coe_mk, hz, ↓reduceIte]

theorem glueHalves_of_not_le (hz : ¬ (s z : ℝ) ≤ 1 / 2) : glueHalves s a a' h z = a' z :=
  by simp only [glueHalves, ContinuousMap.coe_mk, hz, ↓reduceIte]

/-- A homotopy of maps to the total space of a map `p`, staying over a fixed point `b`, gives a
homotopy of maps into the fibre over `b`. -/
theorem homotopic_of_fibre {E B Y : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Y] {p : C(E, B)} {b : B} (f g : C(Y, p ⁻¹' {b}))
    (K : C(Y × I, E)) (h₀ : ∀ y, K (y, 0) = f y) (h₁ : ∀ y, K (y, 1) = g y)
    (hK : ∀ y s, p (K (y, s)) = b) : f.Homotopic g :=
  ⟨{ toFun := fun z ↦ ⟨K (z.2, z.1), hK z.2 z.1⟩
     continuous_toFun := by fun_prop
     map_zero_left := fun y ↦ Subtype.ext (h₀ y)
     map_one_left := fun y ↦ Subtype.ext (h₁ y) }⟩

end ContinuousMap

namespace TauCeti

namespace LiftingFunction

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
  (Λ : LiftingFunction p)

/-- **Uniqueness of lifts up to homotopy in the fibre.**  Two families of paths `α` and `α'` in
`E`, parametrized by a space `Y`, with the same starting points, over the same family of paths `γ`
in `B`, have homotopic end points through a homotopy `K` taking values in the fibre over the end
point of `γ`. -/
theorem exists_homotopy_endpoints {Y : Type w} [TopologicalSpace Y]
    (hp : IsHurewiczFibration.{w} p) (γ : C(Y × I, B)) (α α' : C(Y × I, E))
    (hα : ∀ y t, p (α (y, t)) = γ (y, t))
    (hα' : ∀ y t, p (α' (y, t)) = γ (y, t)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    ∃ K : C(Y × I, E), (∀ y, K (y, 0) = α (y, 1)) ∧ (∀ y, K (y, 1) = α' (y, 1)) ∧
      ∀ y s, p (K (y, s)) = γ (y, 1) := by
  -- Reparametrizations of the paths by `t * (1 - 2 u)` and `t * (2 u - 1)`, clipped to `I`.
  let c₁ : C(Y × (I × I), I) := ⟨fun x ↦ projIcc 0 1 zero_le_one
    ((x.2.2 : ℝ) * (1 - 2 * x.2.1)), continuous_projIcc.comp (by fun_prop)⟩
  let c₂ : C(Y × (I × I), I) := ⟨fun x ↦ projIcc 0 1 zero_le_one
    ((x.2.2 : ℝ) * (2 * x.2.1 - 1)), continuous_projIcc.comp (by fun_prop)⟩
  have c₁_apply : ∀ x, c₁ x = projIcc 0 1 zero_le_one ((x.2.2 : ℝ) * (1 - 2 * x.2.1)) :=
    fun _ ↦ (rfl) -- the definition of the bundled map `c₁`
  have c₂_apply : ∀ x, c₂ x = projIcc 0 1 zero_le_one ((x.2.2 : ℝ) * (2 * x.2.1 - 1)) :=
    fun _ ↦ (rfl) -- the definition of the bundled map `c₂`
  have c₁_zero_right : ∀ y u, c₁ (y, (u, 0)) = 0 := fun y u ↦ by simp [c₁_apply]
  have c₂_zero_right : ∀ y u, c₂ (y, (u, 0)) = 0 := fun y u ↦ by simp [c₂_apply]
  have c₁_zero_left : ∀ y t, c₁ (y, (0, t)) = t := fun y t ↦ by simp [c₁_apply]
  have c₂_one_left : ∀ y t, c₂ (y, (1, t)) = t := fun y t ↦ by simp [c₂_apply]; norm_num
  let a₁ : C(Y × (I × I), E) := α.comp ⟨fun x ↦ (x.1, c₁ x), by fun_prop⟩
  let a₂ : C(Y × (I × I), E) := α'.comp ⟨fun x ↦ (x.1, c₂ x), by fun_prop⟩
  let u : C(Y × (I × I), I) := ⟨fun x ↦ x.2.1, by fun_prop⟩
  have a₁_apply : ∀ x, a₁ x = α (x.1, c₁ x) := fun _ ↦ (rfl) -- the definition of `a₁`
  have a₂_apply : ∀ x, a₂ x = α' (x.1, c₂ x) := fun _ ↦ (rfl) -- the definition of `a₂`
  have u_apply : ∀ x, u x = x.2.1 := fun _ ↦ (rfl) -- the definition of `u`
  -- At `u = 1/2` both reparametrizations are constant at the starting point.
  have hagree : ∀ x, (u x : ℝ) = 1 / 2 → a₁ x = a₂ x := fun x hx ↦ by
    have h1 : c₁ x = 0 := by rw [c₁_apply]; rw [u_apply] at hx; simp [hx]
    have h2 : c₂ x = 0 := by rw [c₂_apply]; rw [u_apply] at hx; simp [hx]
    rw [a₁_apply, a₂_apply, h1, h2]
    exact h₀ x.1
  -- The lift on the open box: `α` on the side `u = 0`, `α'` on the side `u = 1`, constant on the
  -- bottom.
  let g := ContinuousMap.glueHalves u a₁ a₂ hagree
  let H : C(Y × (I × I), B) := ⟨fun x ↦ γ (x.1, x.2.2), by fun_prop⟩
  have H_apply : ∀ x, H x = γ (x.1, x.2.2) := fun _ ↦ (rfl) -- the definition of `H`
  obtain ⟨G, hG, hGJ⟩ := hp.exists_lift_openBox g H (by
    rintro y ⟨u', t⟩ (h | h | h)
    · obtain rfl : t = 0 := h
      by_cases hu : (u' : ℝ) ≤ 1 / 2
      · rw [ContinuousMap.glueHalves_of_le u a₁ a₂ hagree (z := (y, (u', 0))) hu, a₁_apply,
          c₁_zero_right, hα, H_apply]
      · rw [ContinuousMap.glueHalves_of_not_le u a₁ a₂ hagree (z := (y, (u', 0))) hu, a₂_apply,
          c₂_zero_right, hα', H_apply]
    · obtain rfl : u' = 0 := h
      rw [ContinuousMap.glueHalves_of_le u a₁ a₂ hagree (z := (y, (0, t))) (by simp [u_apply]),
        a₁_apply, c₁_zero_left, hα, H_apply]
    · obtain rfl : u' = 1 := h
      rw [ContinuousMap.glueHalves_of_not_le u a₁ a₂ hagree (z := (y, (1, t)))
        (by simp [u_apply]; norm_num), a₂_apply, c₂_one_left, hα', H_apply])
  -- The homotopy is the lift on the top edge `t = 1`.
  let K : C(Y × I, E) := ⟨fun z ↦ G (z.1, (z.2, 1)), by fun_prop⟩
  have K_apply : ∀ y s, K (y, s) = G (y, (s, 1)) := fun _ _ ↦ (rfl) -- the definition of `K`
  refine ⟨K, fun y ↦ ?_, fun y ↦ ?_, fun y s ↦ ?_⟩
  · rw [K_apply, hGJ y (0, 1) (Or.inr (Or.inl rfl)),
      ContinuousMap.glueHalves_of_le u a₁ a₂ hagree (z := (y, (0, 1))) (by simp [u_apply]),
      a₁_apply, c₁_zero_left]
  · rw [K_apply, hGJ y (1, 1) (Or.inr (Or.inr rfl)),
      ContinuousMap.glueHalves_of_not_le u a₁ a₂ hagree (z := (y, (1, 1)))
        (by simp [u_apply]; norm_num), a₂_apply, c₂_one_left]
  · rw [K_apply, ← H_apply (y, (s, 1))]
    exact congr_fun hG (y, (s, 1))

section Transport

variable {b₀ b₁ b₂ : B}

/-- **Transport** in the fibres of a Hurewicz fibration with lifting function `Λ`: the continuous
map from the fibre over `b₀` to the fibre over `b₁` sending a point to the end point of the lift of
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

/-- The family of the constant-in-`Y` paths `γ`, as a map on `Y × I`. -/
private def constFamily {Y : Type*} [TopologicalSpace Y] (γ : Path b₀ b₁) : C(Y × I, B) :=
  ⟨fun z ↦ γ z.2, by fun_prop⟩

private theorem constFamily_apply {Y : Type*} [TopologicalSpace Y] (γ : Path b₀ b₁) (z : Y × I) :
    constFamily γ z = γ z.2 :=
  (rfl)

/-- The end point of the lift of the constant family `γ` from the points `f y` is the transport of
any point `x` with `f y = x`. -/
private theorem liftFamily_constFamily_one {Y : Type*} [TopologicalSpace Y] (f : C(Y, E))
    (γ : Path b₀ b₁) (h : ∀ y, constFamily γ (y, 0) = p (f y)) (y : Y) (x : p ⁻¹' {b₀})
    (hx : f y = x.1) : Λ.liftFamily f (constFamily γ) h (y, 1) = (Λ.transport γ x).1 := by
  rw [Λ.liftFamily_apply, Λ.transport_apply_coe]
  exact congrArg (fun e ↦ e 1) (Λ.lift_congr hx rfl _ _)

/-- Transport along a constant path is homotopic to the identity of the fibre. -/
theorem transport_refl_homotopic (b : B) :
    (Λ.transport (Path.refl b)).Homotopic (ContinuousMap.id _) := by
  let f : C(p ⁻¹' {b}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have h : ∀ y, (constFamily (Path.refl b) : C(p ⁻¹' {b} × I, B)) (y, 0) = p (f y) :=
    fun y ↦ (y.2 : p y.1 = b).symm
  obtain ⟨K, hK₀, hK₁, hK⟩ := exists_homotopy_endpoints Λ.isHurewiczFibration.{u}
    (constFamily (Path.refl b)) (Λ.liftFamily f _ h) ⟨fun z ↦ z.1.1, by fun_prop⟩
    (Λ.apply_liftFamily f _ h) (fun y t ↦ (y.2 : p y.1 = b)) (fun y ↦ Λ.liftFamily_zero f _ h y)
  exact ContinuousMap.homotopic_of_fibre _ _ K
    (fun y ↦ (hK₀ y).trans (Λ.liftFamily_constFamily_one f _ h y y rfl)) hK₁ hK

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
  refine ContinuousMap.homotopic_of_fibre _ _ K (fun y ↦ ?_) (fun y ↦ ?_) fun y s ↦ ?_
  · exact (K_apply y 0).trans (hend γ 0 F.apply_zero y)
  · exact (K_apply y 1).trans (hend γ' 1 F.apply_one y)
  · rw [K_apply]
    exact (Λ.apply_liftFamily f G hG (y, s) 1).trans ((G_apply _).trans (F.target s))

/-- Transport along a concatenation of paths is homotopic to the composite of the transports. -/
theorem transport_trans_homotopic (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    (Λ.transport (γ.trans δ)).Homotopic ((Λ.transport δ).comp (Λ.transport γ)) := by
  let f : C(p ⁻¹' {b₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have hγ : ∀ y, (constFamily γ : C(p ⁻¹' {b₀} × I, B)) (y, 0) = p (f y) :=
    fun y ↦ γ.source.trans (y.2 : p y.1 = b₀).symm
  -- The lift of `γ`, and then the lift of `δ` from its end point.
  let A := Λ.liftFamily f _ hγ
  let f' : C(p ⁻¹' {b₀}, E) := ⟨fun y ↦ A (y, 1), by fun_prop⟩
  have f'_apply : ∀ y, f' y = A (y, 1) := fun _ ↦ (rfl) -- the definition of `f'`
  have hδ : ∀ y, (constFamily δ : C(p ⁻¹' {b₀} × I, B)) (y, 0) = p (f' y) := fun y ↦ by
    rw [f'_apply, Λ.apply_liftFamily, constFamily_apply, constFamily_apply]
    exact δ.source.trans γ.target.symm
  let D := Λ.liftFamily f' _ hδ
  -- Doubled time for the first half, doubled time minus one for the second half.
  let d₁ : C(p ⁻¹' {b₀} × I, I) :=
    ⟨fun z ↦ projIcc 0 1 zero_le_one (2 * (z.2 : ℝ)), continuous_projIcc.comp (by fun_prop)⟩
  let d₂ : C(p ⁻¹' {b₀} × I, I) :=
    ⟨fun z ↦ projIcc 0 1 zero_le_one (2 * (z.2 : ℝ) - 1), continuous_projIcc.comp (by fun_prop)⟩
  have d₁_apply : ∀ z, d₁ z = projIcc 0 1 zero_le_one (2 * (z.2 : ℝ)) :=
    fun _ ↦ (rfl) -- the definition of `d₁`
  have d₂_apply : ∀ z, d₂ z = projIcc 0 1 zero_le_one (2 * (z.2 : ℝ) - 1) :=
    fun _ ↦ (rfl) -- the definition of `d₂`
  let a₁ : C(p ⁻¹' {b₀} × I, E) := A.comp ⟨fun z ↦ (z.1, d₁ z), by fun_prop⟩
  let a₂ : C(p ⁻¹' {b₀} × I, E) := D.comp ⟨fun z ↦ (z.1, d₂ z), by fun_prop⟩
  have a₁_apply : ∀ z, a₁ z = A (z.1, d₁ z) := fun _ ↦ (rfl) -- the definition of `a₁`
  have a₂_apply : ∀ z, a₂ z = D (z.1, d₂ z) := fun _ ↦ (rfl) -- the definition of `a₂`
  have hagree : ∀ z, ((ContinuousMap.snd : C(p ⁻¹' {b₀} × I, I)) z : ℝ) = 1 / 2 → a₁ z = a₂ z :=
    fun z hz ↦ by
    have hz' : (z.2 : ℝ) = 1 / 2 := hz
    have h1 : d₁ z = 1 := by rw [d₁_apply, hz']; norm_num
    have h2 : d₂ z = 0 := by rw [d₂_apply, hz']; norm_num
    rw [a₁_apply, a₂_apply, h1, h2, Λ.liftFamily_zero]
    exact f'_apply z.1
  let C₂ := ContinuousMap.glueHalves ContinuousMap.snd a₁ a₂ hagree
  have hC : ∀ y t, p (C₂ (y, t)) = constFamily (γ.trans δ) (y, t) := by
    intro y t
    rw [constFamily_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [ContinuousMap.glueHalves_of_le _ _ _ _ (z := (y, t)) ht, a₁_apply,
        Λ.apply_liftFamily, constFamily_apply]
      simp only [ht, ↓reduceDIte, d₁_apply]
      exact congrArg γ (projIcc_of_mem zero_le_one ⟨by have := t.2.1; positivity, by linarith⟩)
    · rw [ContinuousMap.glueHalves_of_not_le _ _ _ _ (z := (y, t)) ht, a₂_apply,
        Λ.apply_liftFamily, constFamily_apply]
      simp only [ht, ↓reduceDIte, d₂_apply]
      exact congrArg δ (projIcc_of_mem zero_le_one ⟨by linarith, by have := t.2.2; linarith⟩)
  have hz : ∀ y, (constFamily (γ.trans δ) : C(p ⁻¹' {b₀} × I, B)) (y, 0) = p (f y) :=
    fun y ↦ (γ.trans δ).source.trans (y.2 : p y.1 = b₀).symm
  have h0 : ∀ y, Λ.liftFamily f _ hz (y, 0) = C₂ (y, 0) := fun y ↦ by
    have hle : ((ContinuousMap.snd : C(p ⁻¹' {b₀} × I, I)) (y, 0) : ℝ) ≤ 1 / 2 := by simp
    rw [ContinuousMap.glueHalves_of_le _ _ _ _ hle, a₁_apply, Λ.liftFamily_zero]
    have : d₁ (y, 0) = 0 := by rw [d₁_apply]; simp
    rw [this, Λ.liftFamily_zero]
  obtain ⟨K, hK₀, hK₁, hK⟩ := exists_homotopy_endpoints Λ.isHurewiczFibration.{u}
    (constFamily (γ.trans δ)) (Λ.liftFamily f _ hz) C₂ (Λ.apply_liftFamily f _ hz) hC h0
  refine ContinuousMap.homotopic_of_fibre _ _ K
    (fun y ↦ (hK₀ y).trans (Λ.liftFamily_constFamily_one f _ hz y y rfl))
    (fun y ↦ (hK₁ y).trans ?_) fun y s ↦ (hK y s).trans (γ.trans δ).target
  -- At time `1` the glued map is the second half at its end, the lift of `δ` from `γ`'s end point.
  have hnot : ¬ (((ContinuousMap.snd : C(p ⁻¹' {b₀} × I, I)) (y, 1) : ℝ) ≤ 1 / 2) := by
    simp; norm_num
  have hd : d₂ (y, 1) = 1 := by rw [d₂_apply]; norm_num
  rw [ContinuousMap.glueHalves_of_not_le _ _ _ _ hnot, a₂_apply, hd]
  exact Λ.liftFamily_constFamily_one f' δ hδ y (Λ.transport γ y)
    (Λ.liftFamily_constFamily_one f γ hγ y y rfl)

end Transport

end LiftingFunction

end TauCeti
