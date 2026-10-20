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

* `TauCeti.LiftingFunction.transport Λ γ`: the transport of the fibres along a path `γ`.

## Main results

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
  let c₁ : C(Y × (I × I), I) := ⟨fun x ↦ projIcc 0 1 zero_le_one
    ((x.2.2 : ℝ) * (1 - 2 * x.2.1)), continuous_projIcc.comp (by fun_prop)⟩
  let c₂ : C(Y × (I × I), I) := ⟨fun x ↦ projIcc 0 1 zero_le_one
    ((x.2.2 : ℝ) * (2 * x.2.1 - 1)), continuous_projIcc.comp (by fun_prop)⟩
  let g : C(Y × (I × I), E) := ⟨fun x ↦ if (x.2.1 : ℝ) ≤ 1 / 2 then α (x.1, c₁ x) else
      α' (x.1, c₂ x), by
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) ?_
    intro x hx
    have h1 : c₁ x = 0 := by
      change projIcc 0 1 zero_le_one _ = 0
      rw [hx]; simp
    have h2 : c₂ x = 0 := by
      change projIcc 0 1 zero_le_one _ = 0
      rw [hx]; simp
    rw [h1, h2]; exact h₀ x.1⟩
  let H : C(Y × (I × I), B) := ⟨fun x ↦ γ (x.1, x.2.2), by fun_prop⟩
  obtain ⟨G, hG, hGJ⟩ := hp.exists_lift_openBox g H (by
    rintro y ⟨u, t⟩ (h | h | h)
    · obtain rfl : t = 0 := h
      have h1 : c₁ (y, (u, 0)) = 0 := by
        change projIcc 0 1 zero_le_one _ = 0
        simp
      have h2 : c₂ (y, (u, 0)) = 0 := by
        change projIcc 0 1 zero_le_one _ = 0
        simp
      change p (if (u : ℝ) ≤ 1 / 2 then α (y, c₁ (y, (u, 0))) else α' (y, c₂ (y, (u, 0)))) =
        γ (y, 0)
      split_ifs
      · rw [h1, hα]
      · rw [h2, hα']
    · obtain rfl : u = 0 := h
      have h1 : c₁ (y, (0, t)) = t := by
        change projIcc 0 1 zero_le_one _ = t
        simp
      change p (if ((0 : I) : ℝ) ≤ 1 / 2 then α (y, c₁ (y, (0, t))) else
        α' (y, c₂ (y, (0, t)))) = γ (y, t)
      split_ifs with hc
      · rw [h1, hα]
      · exact absurd (by simp) hc
    · obtain rfl : u = 1 := h
      have h2 : c₂ (y, (1, t)) = t := by
        change projIcc 0 1 zero_le_one _ = t
        norm_num
      change p (if ((1 : I) : ℝ) ≤ 1 / 2 then α (y, c₁ (y, (1, t))) else
        α' (y, c₂ (y, (1, t)))) = γ (y, t)
      split_ifs with hc
      · exact absurd hc (by norm_num)
      · rw [h2, hα'])
  refine ⟨⟨fun z ↦ G (z.1, (z.2, 1)), by fun_prop⟩, ?_, ?_, ?_⟩
  · intro y
    change G (y, (0, 1)) = _
    rw [hGJ y (0, 1) (Or.inr (Or.inl rfl))]
    change (if ((0 : I) : ℝ) ≤ 1 / 2 then α (y, c₁ (y, (0, 1))) else
        α' (y, c₂ (y, (0, 1)))) = _
    split_ifs with hc
    · congr 2
      change projIcc 0 1 zero_le_one _ = 1
      simp
    · exact absurd (by simp) hc
  · intro y
    change G (y, (1, 1)) = _
    rw [hGJ y (1, 1) (Or.inr (Or.inr rfl))]
    change (if ((1 : I) : ℝ) ≤ 1 / 2 then α (y, c₁ (y, (1, 1))) else
        α' (y, c₂ (y, (1, 1)))) = _
    split_ifs with hc
    · exact absurd hc (by norm_num)
    · congr 2
      change projIcc 0 1 zero_le_one _ = 1
      norm_num
  · intro y s
    exact congr_fun hG (y, (s, 1))

section Transport

variable {b₀ b₁ b₂ : B}

/-- A map into the fibre over `b` that is homotopic, through maps into that fibre, to another one:
a homotopy `K` of maps to the total space staying over `b` gives a homotopy of maps to the fibre. -/
theorem homotopic_of_fibre {Y : Type*} [TopologicalSpace Y] {b : B} (f g : C(Y, p ⁻¹' {b}))
    (K : C(Y × I, E)) (h₀ : ∀ y, K (y, 0) = f y) (h₁ : ∀ y, K (y, 1) = g y)
    (hK : ∀ y s, p (K (y, s)) = b) : f.Homotopic g :=
  ⟨{ toFun := fun z ↦ ⟨K (z.2, z.1), hK z.2 z.1⟩
     continuous_toFun := by fun_prop
     map_zero_left := fun y ↦ Subtype.ext (h₀ y)
     map_one_left := fun y ↦ Subtype.ext (h₁ y) }⟩

/-- The point of the fibre over `b₁` reached by lifting a path `γ` from `b₀` to `b₁` starting at a
point `x` of the fibre over `b₀`. -/
def transportFun (γ : Path b₀ b₁) (x : p ⁻¹' {b₀}) : p ⁻¹' {b₁} :=
  ⟨Λ.lift x.1 γ.toContinuousMap (γ.source.trans (x.2 : p x.1 = b₀).symm) 1,
    (Λ.apply_lift _ _ _ 1).trans γ.target⟩

/-- **Transport** in the fibres of a Hurewicz fibration with lifting function `Λ`: the continuous
map from the fibre over `b₀` to the fibre over `b₁` sending a point to the end point of the lift of
the path `γ` starting at it. -/
def transport (γ : Path b₀ b₁) : C(p ⁻¹' {b₀}, p ⁻¹' {b₁}) :=
  ⟨Λ.transportFun γ, Continuous.subtype_mk
    ((continuous_eval_const (1 : I)).comp
      (Λ.continuous_lift continuous_subtype_val continuous_const _)) _⟩

theorem transport_apply_coe (γ : Path b₀ b₁) (x : p ⁻¹' {b₀}) :
    (Λ.transport γ x).1 = Λ.lift x.1 γ.toContinuousMap (γ.source.trans (x.2 : p x.1 = b₀).symm) 1 :=
  (rfl)

/-- The lifts, starting at the points `f y`, of a family `γ` of paths in `B` with
`γ (y, 0) = p (f y)`, as a continuous map on `Y × I`. -/
def liftFamily {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) : C(Y × I, E) :=
  ⟨fun z ↦ Λ.lift (f z.1) (γ.curry z.1) (h z.1) z.2,
    continuous_eval.comp
      (((Λ.continuous_lift (f.continuous.comp continuous_fst)
        (γ.curry.continuous.comp continuous_fst) fun z ↦ h z.1)).prodMk continuous_snd)⟩

theorem liftFamily_apply {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) (y : Y) (t : I) :
    Λ.liftFamily f γ h (y, t) = Λ.lift (f y) (γ.curry y) (h y) t :=
  (rfl)

@[simp]
theorem liftFamily_zero {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) (y : Y) : Λ.liftFamily f γ h (y, 0) = f y :=
  Λ.lift_zero _ _ _

@[simp]
theorem apply_liftFamily {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) (y : Y) (t : I) : p (Λ.liftFamily f γ h (y, t)) = γ (y, t) :=
  Λ.apply_lift _ _ _ t

/-- The family of the constant-in-`Y` paths `γ`, as a map on `Y × I`. -/
private def constFamily {Y : Type*} [TopologicalSpace Y] (γ : Path b₀ b₁) : C(Y × I, B) :=
  ⟨fun z ↦ γ z.2, by fun_prop⟩

/-- Transport along a constant path is homotopic to the identity of the fibre. -/
theorem transport_refl_homotopic (b : B) :
    (Λ.transport (Path.refl b)).Homotopic (ContinuousMap.id _) := by
  let f : C(p ⁻¹' {b}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have h : ∀ y, (constFamily (Path.refl b) : C(p ⁻¹' {b} × I, B)) (y, 0) = p (f y) :=
    fun y ↦ (y.2 : p y.1 = b).symm
  obtain ⟨K, hK₀, hK₁, hK⟩ := exists_homotopy_endpoints Λ.isHurewiczFibration.{u}
    (constFamily (Path.refl b)) (Λ.liftFamily f _ h) ⟨fun z ↦ z.1.1, by fun_prop⟩
    (Λ.apply_liftFamily f _ h) (fun y t ↦ (y.2 : p y.1 = b)) (fun y ↦ Λ.liftFamily_zero f _ h y)
  exact homotopic_of_fibre _ _ K hK₀ hK₁ hK

/-- Homotopic paths have homotopic transports. -/
theorem transport_homotopic {γ γ' : Path b₀ b₁} (h : γ.Homotopic γ') :
    (Λ.transport γ).Homotopic (Λ.transport γ') := by
  obtain ⟨F⟩ := h
  let f : C(p ⁻¹' {b₀} × I, E) := ⟨fun z ↦ z.1.1, by fun_prop⟩
  let G : C((p ⁻¹' {b₀} × I) × I, B) := ⟨fun z ↦ F (z.1.2, z.2), by fun_prop⟩
  have hG : ∀ z, G (z, 0) = p (f z) := fun z ↦ by
    change F (z.2, 0) = p z.1.1
    rw [F.source, (z.1.2 : p z.1.1 = b₀)]
  let L := Λ.liftFamily f G hG
  refine homotopic_of_fibre _ _ ⟨fun z ↦ L ((z.1, z.2), 1), by fun_prop⟩ (fun y ↦ ?_)
    (fun y ↦ ?_) fun y s ↦ ?_
  · refine congrArg (fun e ↦ e 1) (Λ.lift_congr _ ?_ _ _)
    ext t
    exact F.apply_zero t
  · refine congrArg (fun e ↦ e 1) (Λ.lift_congr _ ?_ _ _)
    ext t
    exact F.apply_one t
  · exact (Λ.apply_liftFamily f G hG (y, s) 1).trans (F.target s)

/-- Transport along a concatenation of paths is homotopic to the composite of the transports. -/
theorem transport_trans_homotopic (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    (Λ.transport (γ.trans δ)).Homotopic ((Λ.transport δ).comp (Λ.transport γ)) := by
  let f : C(p ⁻¹' {b₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have hγ : ∀ y, (constFamily γ : C(p ⁻¹' {b₀} × I, B)) (y, 0) = p (f y) :=
    fun y ↦ γ.source.trans (y.2 : p y.1 = b₀).symm
  -- the lift of `γ` followed by the lift of `δ` from the end point
  let A := Λ.liftFamily f _ hγ
  let f' : C(p ⁻¹' {b₀}, E) := ⟨fun y ↦ A (y, 1), by fun_prop⟩
  have hδ : ∀ y, (constFamily δ : C(p ⁻¹' {b₀} × I, B)) (y, 0) = p (f' y) := fun y ↦ by
    change δ 0 = p (A (y, 1))
    rw [Λ.apply_liftFamily, constFamily]
    exact δ.source.trans γ.target.symm
  let D := Λ.liftFamily f' _ hδ
  let C₂ : C(p ⁻¹' {b₀} × I, E) := ⟨fun z ↦ if (z.2 : ℝ) ≤ 1 / 2 then
      A (z.1, projIcc 0 1 zero_le_one (2 * z.2)) else
      D (z.1, projIcc 0 1 zero_le_one (2 * z.2 - 1)), by
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) ?_
    intro z hz
    have h1 : projIcc 0 1 zero_le_one (2 * (z.2 : ℝ)) = 1 := by
      rw [hz]; norm_num
    have h2 : projIcc 0 1 zero_le_one (2 * (z.2 : ℝ) - 1) = 0 := by
      rw [hz]; norm_num
    rw [h1, h2]
    exact (Λ.liftFamily_zero f' _ hδ z.1).symm⟩
  have hC : ∀ y t, p (C₂ (y, t)) = constFamily (γ.trans δ) (y, t) := by
    intro y t
    change p (if (t : ℝ) ≤ 1 / 2 then _ else _) = (γ.trans δ) t
    rw [Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [ht, ↓reduceIte, ↓reduceDIte]
      rw [Λ.apply_liftFamily]
      exact congrArg γ (projIcc_of_mem zero_le_one ⟨by have := t.2.1; positivity, by linarith⟩)
    · simp only [ht, ↓reduceIte, ↓reduceDIte]
      rw [Λ.apply_liftFamily]
      exact congrArg δ (projIcc_of_mem zero_le_one ⟨by linarith, by have := t.2.2; linarith⟩)
  have hz : ∀ y, (constFamily (γ.trans δ) : C(p ⁻¹' {b₀} × I, B)) (y, 0) = p (f y) :=
    fun y ↦ (γ.trans δ).source.trans (y.2 : p y.1 = b₀).symm
  have h0 : ∀ y, Λ.liftFamily f _ hz (y, 0) = C₂ (y, 0) := fun y ↦ by
    rw [Λ.liftFamily_zero]
    change f y = if ((0 : I) : ℝ) ≤ 1 / 2 then A (y, projIcc 0 1 zero_le_one (2 * ((0 : I) : ℝ)))
      else _
    simp [A]
  obtain ⟨K, hK₀, hK₁, hK⟩ := exists_homotopy_endpoints Λ.isHurewiczFibration.{u}
    (constFamily (γ.trans δ)) (Λ.liftFamily f _ hz) C₂ (Λ.apply_liftFamily f _ hz) hC h0
  refine homotopic_of_fibre _ _ K hK₀ (fun y ↦ (hK₁ y).trans ?_) fun y s ↦
    (hK y s).trans (γ.trans δ).target
  change (if ((1 : I) : ℝ) ≤ 1 / 2 then _ else
    D (y, projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1))) = _
  have hn : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by norm_num
  have h1 : projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = 1 := by norm_num
  simp only [hn, ↓reduceIte, h1]
  rfl

end Transport

end LiftingFunction

end TauCeti
