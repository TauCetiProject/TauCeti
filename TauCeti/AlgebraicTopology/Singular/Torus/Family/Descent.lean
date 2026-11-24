/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Basic
public import TauCeti.Topology.Homotopy.Lifting.Basic

/-!
# Monodromy of a family of tori descended through a free action

Let `P : Y → (Λ →ₗ[ℤ] E)` be a continuous family of full lattices, with family of tori
`X = (Y × E)/Λ` and projection `p : X → Y`. Let a group `Γ` act on `Y` freely, properly
discontinuously and continuously, and on `X` by a continuous affine cocycle
`g • [y, v] = R g y v +ᵥ b g y` (`TauCeti.torusFamilyAffineMulAction`) whose linear parts carry
periods along `ρ : Representation ℤ Γ Λ`. The projection descends to the family
`X/Γ → Y/Γ`, and the orbit map `Y → Y/Γ` is a covering map. Since `Γ` acts freely on `Y`, two
points of the fibre of `X` over `y₀` with the same image in `X/Γ` are equal. Loops in the fibre of
`X/Γ` over the orbit `[y₀]` are therefore described here as the images of loops in the fibre of `X`
over `y₀`, and marked by the canonical marking `H₁(T_{y₀}; ℤ) ≃ Λ` of that fibre
(`TauCeti.torusFamilyMarking`).

This file computes the monodromy of the descended family on this marking, as a function of the
loop in the base `Y/Γ` (`TauCeti.torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy`).
Let `c₀` and `c₁` be loops in the fibre over `[y₀]`, the images of loops `γ₀` and `γ₁` in the
fibre of `X` over `y₀`, and let `H` be a free homotopy between them in `X/Γ`, whose base points
trace the loop `δ` in `Y/Γ`. The lift of `δ` from `y₀` through the covering map `Y → Y/Γ` ends at
`g • y₀` for a unique `g ∈ Γ`, the element of Mathlib's
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite` attached to `δ`. Then

`μ(γ₁) = ρ(g⁻¹) μ(γ₀)`,

where `μ` is the canonical marking. Lifting `H` through the covering map `X → X/Γ`
(`IsCoveringMap.exists_lift_freeHomotopy`) gives a free homotopy in `X` from `γ₀` to a loop over
`g • y₀`, which the action of `g⁻¹` moves to `γ₁`; so this is the monodromy of the affine action in
the total space, `TauCeti.torusFamilyMarking_singularHomologyMap_loopClass_of_homotopy`, read on
loops in the base `Y/Γ`.

Reversing the orientation of the loop inverts the monodromy
(`TauCeti.torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy_symm`): the lift of the
reversed loop `δ⁻¹` from `y₀` ends at `g⁻¹ • y₀`, so a free homotopy over `δ⁻¹` transforms the
marking by `ρ(g)`, the inverse of `ρ(g⁻¹)`.

Singular chains with integer coefficients are defined on spaces in the lowest universe, so `Y`
and `E` are types in `Type`.

## Main results

* `TauCeti.torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy`: the monodromy of the
  descended family along a loop `δ` in `Y/Γ` whose lift from `y₀` ends at `g • y₀` is `ρ(g⁻¹)`.
* `TauCeti.torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy_symm`: along the reversed
  loop the monodromy is `ρ(g)`, its inverse.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
* A. Hatcher, *Algebraic Topology*, Proposition 1.30 (homotopy lifting) and Proposition 1.34
  (uniqueness of lifts).
-/

public section

noncomputable section

open Function unitInterval TauCeti.HurewiczOne

namespace TauCeti

variable {Y E : Type} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y]
  [IsCancelSMul Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (ρ : Representation ℤ Γ Λ) (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2) (hbc : ∀ g, Continuous (b g))

include hR hbc

omit [ContinuousConstSMul Γ Y] in
/-- The monodromy in the total space, with the end loop moved back by the action. Let `H'` be a
free homotopy of loops in `X` from the loop `γ₀` over `y₀` to a loop over `g • y₀` whose image in
`X/Γ` is that of the loop `γ₁` over `y₀`. Then the marking of `γ₁` is `ρ g⁻¹` applied to the
marking of `γ₀`. -/
private theorem torusFamilyMarking_loopClass_of_homotopy_of_mk_eq {g : Γ} {y₀ : Y}
    {z₀ z₁ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀}}
    (γ₀ : Path z₀ z₀) (γ₁ : Path z₁ z₁)
    (H' : letI := periodAddAction P; C(I × I, AddAction.orbitRel.Quotient Λ (Y × E)))
    (hloop : ∀ s, H' (0, s) = H' (1, s)) (hbot : ∀ t, H' (t, 0) = γ₀ t)
    (htop : ∀ t, torusFamilyProjection P (H' (t, 1)) = g • y₀)
    (h₁ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ t, Quotient.mk (MulAction.orbitRel Γ _) (H' (t, 1)) =
        Quotient.mk _ (γ₁ t : AddAction.orbitRel.Quotient Λ (Y × E))) :
    torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology ℤ _ (loopClass ℤ γ₁)) =
      ρ g⁻¹ (torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology ℤ _ (loopClass ℤ γ₀))) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
  have covX := (isQuotientCoveringMap_quotientMk_torusFamilyAffineMulAction P hcont hinj R hone
    hmul ρ hP b hb hbmul hR hbc).isCoveringMap
  let γ₁' : Path (⟨H' (0, 1), htop 0⟩ : {z | torusFamilyProjection P z = g • y₀})
      ⟨H' (0, 1), htop 0⟩ :=
    { toFun t := ⟨H' (t, 1), htop t⟩
      continuous_toFun := (H'.continuous.comp (Continuous.prodMk_left 1)).subtype_mk htop
      source' := rfl
      target' := Subtype.ext (hloop 1).symm }
  -- The action of `g⁻¹` carries the fibre over `g • y₀` back to the fibre over `y₀`.
  have hmem : ∀ x : {z | torusFamilyProjection P z = g • y₀},
      torusFamilyAffineMap R P ρ hP b hb g⁻¹ x ∈ {z | torusFamilyProjection P z = y₀} :=
    fun x ↦ by rw [Set.mem_ofPred_eq, torusFamilyProjection_affineMap, x.property, inv_smul_smul]
  let φ : C({z | torusFamilyProjection P z = g • y₀}, {z | torusFamilyProjection P z = y₀}) :=
    ⟨fun x ↦ ⟨_, hmem x⟩, ((continuous_torusFamilyAffineMap R P ρ hP b hb hcont (hR g⁻¹)
      (hbc g⁻¹)).comp continuous_subtypeVal).subtype_mk hmem⟩
  have hφ : ∀ x, (φ x : AddAction.orbitRel.Quotient Λ (Y × E)) = g⁻¹ • (x : _) := fun x ↦
    (torusFamilyAffineMulAction_smul R hone hmul P ρ hP b hb hbmul g⁻¹ x).symm
  have key := torusFamilyMarking_singularHomologyMap_loopClass_of_homotopy P hcont hinj R ρ hP b
    hb γ₀ γ₁' H' hloop (fun t ↦ (hbot t).symm) (fun _ ↦ rfl) φ (fun _ ↦ rfl)
    ((hR g⁻¹).comp (Continuous.prodMk_right (g • y₀)))
  -- The transported loop `φ ∘ γ₁'` is `γ₁`: both lift `H (·, 1)` to the fibre over `y₀`, and
  -- they start at the same point since `Γ` acts freely on `Y`.
  have hφγ : ∀ t, Quotient.mk (MulAction.orbitRel Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
      (φ (γ₁' t) : AddAction.orbitRel.Quotient Λ (Y × E)) =
        Quotient.mk _ (γ₁ t : AddAction.orbitRel.Quotient Λ (Y × E)) := fun t ↦ by
    rw [hφ, MulAction.orbitRel.Quotient.quotient_smul_eq]
    exact h₁ t
  have hstart : (φ (γ₁' 0) : AddAction.orbitRel.Quotient Λ (Y × E)) = γ₁ 0 := by
    obtain ⟨h, hh⟩ := Quotient.exact (hφγ 0)
    beta_reduce at hh
    have h1 : h = 1 := IsCancelSMul.right_cancel h 1 y₀ <| by
      have e := congrArg (torusFamilyProjection P) hh
      have e' : torusFamilyProjection P (φ (γ₁' 0) : _) = y₀ := (φ (γ₁' 0)).property
      rw [torusFamilyAffineMulAction_smul, torusFamilyProjection_affineMap, (γ₁ 0).property,
        e'] at e
      rwa [one_smul]
    rw [← hh, h1, one_smul]
  have hγ₁ : ∀ t, (φ (γ₁' t) : AddAction.orbitRel.Quotient Λ (Y × E)) = γ₁ t := congr_fun <|
    covX.eq_of_comp_eq (g₁ := fun t ↦ (φ (γ₁' t) : AddAction.orbitRel.Quotient Λ (Y × E)))
      (continuous_subtypeVal.comp (φ.continuous.comp γ₁'.continuous))
      (continuous_subtypeVal.comp γ₁.continuous) (funext hφγ) 0 hstart
  rwa [ContinuousMap.singularHomologyMap_loopClass,
    loopClass_eq_of_apply_eq _ γ₁ fun t ↦ Subtype.ext (hγ₁ t)] at key

/-- **Monodromy of a descended family of tori.** Let `Γ` act freely, properly discontinuously and
continuously on `Y`, and on the family of tori `X = (Y × E)/Λ` by a continuous affine cocycle, so
that the projection descends to `X/Γ → Y/Γ`. Let `H` be a free homotopy in `X/Γ` between loops in
the fibre over the orbit `[y₀]`, the images of loops `γ₀` and `γ₁` in the fibre of `X` over `y₀`:
`H (·, 0)` and `H (·, 1)` are the images of `γ₀` and `γ₁`, and each `H (·, s)` is a loop. Let `δ`
be the loop in `Y/Γ` traced by the base points `H (0, s)`, and let `g ∈ Γ` be the element that
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite` attaches to `δ` for the covering map
`Y → Y/Γ` and the base point `y₀`: the lift of `δ` from `y₀` ends at `g • y₀`. Then the marking of
`γ₁` is `ρ g⁻¹` applied to the marking of `γ₀`. -/
theorem torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy {y₀ : Y}
    {z₀ z₁ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀}}
    (γ₀ : Path z₀ z₀) (γ₁ : Path z₁ z₁)
    (H : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      C(I × I, MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))))
    (hH : ∀ s, H (0, s) = H (1, s))
    (h₀ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ t, Quotient.mk _ (γ₀ t : AddAction.orbitRel.Quotient Λ (Y × E)) = H (t, 0))
    (h₁ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ t, Quotient.mk _ (γ₁ t : AddAction.orbitRel.Quotient Λ (Y × E)) = H (t, 1))
    (δ : Path (Quotient.mk (MulAction.orbitRel Γ Y) y₀) (Quotient.mk (MulAction.orbitRel Γ Y) y₀))
    (hδ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ s, δ s = MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineProjectionHom R hone hmul P ρ hP b hb hbmul) (H (0, s))) :
    torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology ℤ _ (loopClass ℤ γ₁)) =
      ρ ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ) (E := Y)
          |>.fundamentalGroupToMulOpposite ⟨y₀, rfl⟩ (.of (.mk δ))).unop⁻¹)
        (torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology ℤ _ (loopClass ℤ γ₀))) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
  have hqY := isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ) (E := Y)
  -- Lift `H` through the orbit map `X → X/Γ` to a free homotopy of loops starting at `γ₀`.
  obtain ⟨H', hH', hbot, hloop⟩ := (isQuotientCoveringMap_quotientMk_torusFamilyAffineMulAction P
    hcont hinj R hone hmul ρ hP b hb hbmul hR hbc).isCoveringMap.exists_lift_freeHomotopy H hH
    ⟨fun t ↦ (γ₀ t : AddAction.orbitRel.Quotient Λ (Y × E)), continuous_subtypeVal.comp
      γ₀.continuous⟩ h₀ (congrArg Subtype.val (γ₀.source.trans γ₀.target.symm))
  replace hH' : ∀ t s, Quotient.mk _ (H' (t, s)) = H (t, s) := fun t s ↦ congr_fun hH' (t, s)
  -- The base points `p (H' (0, s))` lift `δ` from `y₀`, and end at `g • y₀`.
  have hp : ∀ x : AddAction.orbitRel.Quotient Λ (Y × E),
      Quotient.mk (MulAction.orbitRel Γ Y) (torusFamilyProjection P x) =
        MulActionHom.orbitRelQuotientMap
          (torusFamilyAffineProjectionHom R hone hmul P ρ hP b hb hbmul) (Quotient.mk _ x) :=
    fun x ↦ by rw [MulActionHom.orbitRelQuotientMap_mk, coe_torusFamilyAffineProjectionHom]
  have hβ : ∀ s, Quotient.mk (MulAction.orbitRel Γ Y) (torusFamilyProjection P (H' (0, s))) =
      δ s := fun s ↦ by rw [hp, hH', hδ]
  have hβ₀ : torusFamilyProjection P (H' (0, 0)) = y₀ := by rw [hbot]; exact (γ₀ 0).property
  obtain ⟨g, hg⟩ : ∃ g : Γ, g • y₀ = torusFamilyProjection P (H' (0, 1)) :=
    Quotient.exact ((hβ 1).trans δ.target)
  have hδg : hqY.fundamentalGroupToMulOpposite ⟨y₀, rfl⟩ (.of (.mk δ)) = .op g :=
    hqY.fundamentalGroupToMulOpposite_apply_mk_eq
      (Γ := ⟨fun s ↦ torusFamilyProjection P (H' (0, s)),
        (continuous_torusFamilyProjection P).comp (H'.continuous.comp (Continuous.prodMk_right 0))⟩)
      (funext hβ) hβ₀ hg.symm
  -- The top edge of the lift lies over `g • y₀`, as its image in `Y/Γ` is the constant `[y₀]`.
  have hq : ∀ t, Quotient.mk (MulAction.orbitRel Γ Y) (torusFamilyProjection P (H' (t, 1))) =
      Quotient.mk _ y₀ := fun t ↦ by rw [hp, hH', ← h₁, ← hp, (γ₁ t).property]
  have htop : ∀ t, torusFamilyProjection P (H' (t, 1)) = g • y₀ := fun t ↦
    (hqY.isCoveringMap.const_of_comp (g := fun t ↦ torusFamilyProjection P (H' (t, 1)))
      ((continuous_torusFamilyProjection P).comp (H'.continuous.comp (Continuous.prodMk_left 1)))
      (fun t t' ↦ (hq t).trans (hq t').symm) t 0).trans hg.symm
  rw [hδg, MulOpposite.unop_op]
  exact torusFamilyMarking_loopClass_of_homotopy_of_mk_eq P hcont hinj R hone hmul ρ hP b hb hbmul
    hR hbc γ₀ γ₁ H' hloop hbot htop fun t ↦ (hH' t 1).trans (h₁ t).symm

/-- **Reversal of loop orientation inverts the monodromy of a descended family of tori.** In the
setting of `TauCeti.torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy`, let the base points
`H (0, s)` of the free homotopy trace the reversed loop `δ⁻¹` instead of `δ`. Let `g ∈ Γ` be the
element attached to `δ`, so that the lift of `δ` from `y₀` ends at `g • y₀` and the monodromy along
`δ` is `ρ g⁻¹`. Then the marking of `γ₁` is `ρ g` applied to the marking of `γ₀`: the monodromy
along `δ⁻¹` is the inverse of the monodromy along `δ`. -/
theorem torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy_symm {y₀ : Y}
    {z₀ z₁ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀}}
    (γ₀ : Path z₀ z₀) (γ₁ : Path z₁ z₁)
    (H : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      C(I × I, MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))))
    (hH : ∀ s, H (0, s) = H (1, s))
    (h₀ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ t, Quotient.mk _ (γ₀ t : AddAction.orbitRel.Quotient Λ (Y × E)) = H (t, 0))
    (h₁ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ t, Quotient.mk _ (γ₁ t : AddAction.orbitRel.Quotient Λ (Y × E)) = H (t, 1))
    (δ : Path (Quotient.mk (MulAction.orbitRel Γ Y) y₀) (Quotient.mk (MulAction.orbitRel Γ Y) y₀))
    (hδ : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbmul
      ∀ s, δ.symm s = MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineProjectionHom R hone hmul P ρ hP b hb hbmul) (H (0, s))) :
    torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology ℤ _ (loopClass ℤ γ₁)) =
      ρ (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ) (E := Y)
          |>.fundamentalGroupToMulOpposite ⟨y₀, rfl⟩ (.of (.mk δ))).unop
        (torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology ℤ _ (loopClass ℤ γ₀))) := by
  have hqY := isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ) (E := Y)
  -- The class of `δ⁻¹` is the inverse of the class of `δ` in the fundamental group.
  have hinv : (hqY.fundamentalGroupToMulOpposite ⟨y₀, rfl⟩ (.of (.mk δ.symm))).unop⁻¹ =
      (hqY.fundamentalGroupToMulOpposite ⟨y₀, rfl⟩ (.of (.mk δ))).unop := by
    rw [Path.Homotopic.Quotient.mk_symm, ← FundamentalGroup.inv_def, map_inv,
      MulOpposite.unop_inv, inv_inv]
  rw [torusFamilyMarking_loopClass_of_orbitRelQuotient_homotopy P hcont hinj R hone hmul ρ hP b hb
    hbmul hR hbc γ₀ γ₁ H hH h₀ h₁ δ.symm hδ, hinv]

end TauCeti
