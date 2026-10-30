/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LinearAction
public import TauCeti.Algebra.Module.ZLattice.Family.Translation

/-!
# Affine equivariant actions on families of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a period family, with total space the orbit space `(Y × E)/Λ` of the
period translation action (`TauCeti.periodAddAction`), and let a monoid `Γ` act on `Y`.
`TauCeti.torusFamilyLinearMulAction` lifts this action by a cocycle of fibrewise additive maps
`R g y : E →+ E`; it fixes the zero section over every fixed point of the base. This file adds a
translation part, so that `g` acts on fibres by the affine maps `x ↦ R g y x + b g y`.

The translation part is a section of the family itself, not a vector in `E`: `b g y` is a point
of `(Y × E)/Λ` lying over `g • y`. A torus-valued section need not lift to `E` continuously,
let alone holomorphically, so no global lift is required. The vector `R g y v` is added to the
point `b g y` by the fibrewise translation action of `E` on the family,
`v +ᵥ [y, w] = [y, v + w]` (`TauCeti.torusFamilyTranslationAddAction`).

* `TauCeti.torusFamilyAffineMap` is the map `[y, v] ↦ R g y v +ᵥ b g y` of the family, for each
  `g`. It is well defined because `R g y` carries periods at `y` to periods at `g • y`. When
  `b g y = [g • y, β]`, it sends `[y, v]` to `[g • y, R g y v + β]`
  (`TauCeti.torusFamilyAffineMap_mk_of_eq`).
* `TauCeti.torusFamilyAffineMulAction` is the resulting action of `Γ`, under the cocycle laws
  `b 1 y = [y, 0]` and `b (g * h) y = g · b h y`, where
  `g · b h y = R g (h • y) (b h y) + b g (h • y)` is the affine map of `g` applied to the point
  `b h y` of the fibre over `h • y`.

With the zero section as translation part, the affine maps are the linear action
(`TauCeti.torusFamilyAffineMap_zero_translation`). Unlike the linear action, the affine action can
be free over a fixed point of the base: an element `g` acting on the fibre over `y` by the
translation by `b g y` fixes a point of that fibre exactly when `b g y` is the zero of the fibre
(`TauCeti.torusFamilyAffineMap_mk_eq_self_iff_of_translation`). In general, a point of the fibre
over a fixed point is fixed exactly when its representative solves an affine equation modulo the
periods (`TauCeti.torusFamilyAffineMap_mk_eq_mk_iff`).

## Main definitions

* `TauCeti.torusFamilyAffineMap`: the affine map of the family defined by `g`.
* `TauCeti.torusFamilyAffineMulAction`: the affine action of `Γ` on the family.

## Main results

* `TauCeti.torusFamilyAffineMap_vadd`: the affine map of `g` is additive along fibres with linear
  part `R g`.
* `TauCeti.torusFamilyAffineMulAction_inv_smul_mk`: the inverse formula
  `g⁻¹ • [g • y, v] = [y, R g⁻¹ (g • y) (v - β)]`, for a representative `β` of `b g y`.
* `TauCeti.torusFamilyAffineMap_mk_eq_mk_iff`: when two points of the family are related by an
  affine map.
* `TauCeti.isCancelSMul_torusFamilyAffineMulAction`: the affine action is free when the action on
  the base is free.
* `TauCeti.continuousConstSMul_torusFamilyAffineMulAction`,
  `TauCeti.properlyDiscontinuousSMul_torusFamilyAffineMulAction`: continuity and proper
  discontinuity of the affine action.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
-/

public section

namespace TauCeti

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]

/-! ### The affine maps -/

section Monoid

variable {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- The affine map `[y, v] ↦ R g y v +ᵥ b g y` of the family of tori defined by `g`, with linear
part `R g` and translation part the section `b g`, whose value `b g y` lies over `g • y`. It is
well defined because `R g y` carries the periods at `y` to periods at `g • y`, which fix every
point over `g • y`. -/
def torusFamilyAffineMap (g : Γ) :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × E) → AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction P
  letI := torusFamilyTranslationAddAction P
  Quotient.lift (fun p ↦ R g p.1 p.2 +ᵥ b g p.1) fun p q hpq ↦ by
    obtain ⟨l, rfl⟩ := AddAction.mem_orbit_iff.1 (AddAction.orbitRel_apply.1 hpq)
    -- The period `P y l` is carried to the period `P (g • y) (ρ g l)` at the base of `b g y`.
    have h := torusFamilyTranslationAddAction_period_vadd P (ρ g l) (b g q.1)
    rw [hb, hP] at h
    simp only [periodAddAction_vadd, map_add]
    rw [add_vadd, h]

/-- The affine map of `g` sends the class of `(y, v)` to the translate of `b g y` by `R g y v`. -/
@[simp] theorem torusFamilyAffineMap_mk (g : Γ) (p : Y × E) :
    letI := periodAddAction P
    letI := torusFamilyTranslationAddAction P
    torusFamilyAffineMap R P ρ hP b hb g (Quotient.mk _ p) = R g p.1 p.2 +ᵥ b g p.1 := (rfl)

/-- **Compatibility with the period quotient.** If `β` represents `b g y`, the affine map of `g`
is induced on the class of `(y, v)` by the affine map `(y, v) ↦ (g • y, R g y v + β)`. -/
theorem torusFamilyAffineMap_mk_of_eq {g : Γ} {y : Y} {β : E}
    (hβ : b g y = Quotient.mk _ (g • y, β)) (v : E) :
    letI := periodAddAction P
    torusFamilyAffineMap R P ρ hP b hb g (Quotient.mk _ (y, v)) =
      Quotient.mk _ (g • y, R g y v + β) := by
  simp [hβ]

/-- The affine map of `g` carries the fibre over `y` to the fibre over `g • y`. -/
@[simp] theorem torusFamilyProjection_affineMap (g : Γ)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyProjection P (torusFamilyAffineMap R P ρ hP b hb g x) =
      g • torusFamilyProjection P x := by
  induction x using Quotient.inductionOn with
  | h p => simp [hb]

/-- The affine map of `g` has linear part `R g`: translating a point over `y` by `v` before
applying it is translating by `R g y v` after. -/
theorem torusFamilyAffineMap_vadd (g : Γ) (v : E)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyTranslationAddAction P
    torusFamilyAffineMap R P ρ hP b hb g (v +ᵥ x) =
      R g (torusFamilyProjection P x) v +ᵥ torusFamilyAffineMap R P ρ hP b hb g x := by
  let _ := torusFamilyTranslationAddAction P
  induction x using Quotient.inductionOn with
  | h p => simp [add_vadd]

/-- **Two points related by an affine map.** If `β` represents `b g y`, the affine map of `g`
sends the class of `(y, v)` to the class of `(y', v')` exactly when `g • y = y'` and
`R g y v + β - v'` is a period at `y'`. For `y' = y` this describes the fixed points of `g` in
the fibre over a fixed point `y` of the base. -/
theorem torusFamilyAffineMap_mk_eq_mk_iff {g : Γ} {y : Y} {β : E}
    (hβ : b g y = Quotient.mk _ (g • y, β)) (v : E) (y' : Y) (v' : E) :
    letI := periodAddAction P
    torusFamilyAffineMap R P ρ hP b hb g (Quotient.mk _ (y, v)) = Quotient.mk _ (y', v') ↔
      g • y = y' ∧ R g y v + β - v' ∈ LinearMap.range (P y') := by
  let _ := periodAddAction P
  rw [torusFamilyAffineMap_mk_of_eq R P ρ hP b hb hβ, Quotient.eq, AddAction.orbitRel_apply,
    mem_orbit_periodAddAction_iff]

/-- **Translations.** If `R g y` is the identity, so that `g` acts on the fibre over `y` as the
translation by `b g y`, then `g` fixes a point of that fibre exactly when `b g y` is the zero
`[y, 0]` of the fibre; this forces `g • y = y`. In particular, over a fixed point of the base, a
translation by a nonzero point fixes no point of the fibre, unlike the linear action, which fixes
the zero section (`TauCeti.torusFamilyLinearMulAction_stabilizer_mk_zero`). -/
theorem torusFamilyAffineMap_mk_eq_self_iff_of_translation {g : Γ} {y : Y}
    (hR : ∀ v, R g y v = v) (v : E) :
    letI := periodAddAction P
    torusFamilyAffineMap R P ρ hP b hb g (Quotient.mk _ (y, v)) = Quotient.mk _ (y, v) ↔
      b g y = Quotient.mk _ (y, 0) := by
  let _ := periodAddAction P
  let _ := torusFamilyTranslationAddAction P
  have hv : (Quotient.mk _ (y, v) : AddAction.orbitRel.Quotient Λ (Y × E)) =
      v +ᵥ (Quotient.mk _ (y, 0) : AddAction.orbitRel.Quotient Λ (Y × E)) := by
    simp
  simp only [torusFamilyAffineMap_mk]
  rw [hR, hv, vadd_left_cancel_iff]

/-- **The linear action is the affine action with zero translation part.** When `b g y` is the
class of `(g • y, 0)`, the affine map of `g` is the action of `g` by
`TauCeti.torusFamilyLinearMulAction`. -/
theorem torusFamilyAffineMap_zero_translation (g : Γ)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    torusFamilyAffineMap R P ρ hP (fun g y ↦ Quotient.mk _ (g • y, 0))
      (fun g y ↦ torusFamilyProjection_mk P (g • y, 0)) g x =
      g • x := by
  induction x using Quotient.inductionOn with
  | h p => simp

variable (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))

/-- **The affine action** of `Γ` on the family of tori, `g • [y, v] = R g y v +ᵥ b g y`.
Besides the cocycle laws of `R`, it requires the cocycle laws of the translation part:
`b 1 y` is the zero `[y, 0]` of the fibre over `y`, and `b (g * h) y` is the image of `b h y`
under the affine map of `g`, that is `R g (h • y) (b h y) + b g (h • y)`. -/
@[instance_reducible]
def torusFamilyAffineMulAction :
    letI := periodAddAction P
    MulAction Γ (AddAction.orbitRel.Quotient Λ (Y × E)) :=
  letI := periodAddAction P
  letI := torusFamilyTranslationAddAction P
  { smul := torusFamilyAffineMap R P ρ hP b hb
    one_smul x := by
      induction x using Quotient.inductionOn with
      | h p =>
        -- Unfold the action field to the affine map of `1`.
        change torusFamilyAffineMap R P ρ hP b hb 1 (Quotient.mk _ p) = Quotient.mk _ p
        simp [hone, hbone]
    mul_smul g h x := by
      induction x using Quotient.inductionOn with
      | h p =>
        -- Both sides translate `b (g * h) p.1 = g · b h p.1` by `R g (h • p.1) (R h p.1 p.2)`.
        change torusFamilyAffineMap R P ρ hP b hb (g * h) (Quotient.mk _ p) =
          torusFamilyAffineMap R P ρ hP b hb g (torusFamilyAffineMap R P ρ hP b hb h
            (Quotient.mk _ p))
        rw [torusFamilyAffineMap_mk, torusFamilyAffineMap_mk, torusFamilyAffineMap_vadd, hb,
          hmul, hbmul] }

/-- The affine action of `g` is the affine map of `g`. -/
@[simp] theorem torusFamilyAffineMulAction_smul (g : Γ)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    g • x = torusFamilyAffineMap R P ρ hP b hb g x := (rfl)

/-! ### Topology of the affine action -/

section Topology

variable [TopologicalSpace Y] [TopologicalSpace E]

/-- **Proper discontinuity of the affine action.** The affine action on the family of tori is
properly discontinuous whenever the base action is, since the projection of the family is
continuous and equivariant. -/
theorem properlyDiscontinuousSMul_torusFamilyAffineMulAction [ProperlyDiscontinuousSMul Γ Y] :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    ProperlyDiscontinuousSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) :=
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  (continuous_torusFamilyProjection P).properlyDiscontinuousSMul fun g x ↦ by simp

variable [ContinuousAdd E] (hcont : ∀ l, Continuous fun y ↦ P y l)

include hcont in
/-- The affine map of `g` is continuous when `(y, v) ↦ R g y v` and the translation section
`b g` are continuous. -/
theorem continuous_torusFamilyAffineMap {g : Γ} (hR : Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : Continuous (b g)) : Continuous (torusFamilyAffineMap R P ρ hP b hb g) := by
  let _ := periodAddAction P
  let _ := torusFamilyTranslationAddAction P
  have := continuousVAdd_torusFamilyTranslationAddAction P hcont
  exact Continuous.quotient_lift (hR.vadd (hbc.comp continuous_fst)) _

include hcont in
/-- The affine action acts by continuous maps when each `(y, v) ↦ R g y v` and each translation
section `b g` is continuous. No continuity of the base action is assumed: it follows, since
`b g y` lies over `g • y`. -/
theorem continuousConstSMul_torusFamilyAffineMulAction
    (hR : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2) (hbc : ∀ g, Continuous (b g)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  exact ⟨fun g ↦ continuous_torusFamilyAffineMap R P ρ hP b hb hcont (hR g) (hbc g)⟩

end Topology

end Monoid

section Group

variable {Γ : Type*} [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))

/-- **The inverse formula.** If `β` represents `b g y`, the inverse of the affine map of `g`
sends the class of `(g • y, v)` to the class of `(y, R g⁻¹ (g • y) (v - β))`. -/
theorem torusFamilyAffineMulAction_inv_smul_mk {g : Γ} {y : Y} {β : E}
    (hβ : b g y = Quotient.mk _ (g • y, β)) (v : E) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    g⁻¹ • (Quotient.mk _ (g • y, v) : AddAction.orbitRel.Quotient Λ (Y × E)) =
      Quotient.mk _ (y, R g⁻¹ (g • y) (v - β)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  refine (smul_left_cancel_iff g).1 ?_
  rw [smul_inv_smul, torusFamilyAffineMulAction_smul,
    torusFamilyAffineMap_mk_of_eq R P ρ hP b hb hβ, linearCocycle_apply_inv_apply R hone hmul,
    sub_add_cancel]

/-- An element fixing a point of the family of tori fixes its base point. -/
theorem torusFamilyAffineMulAction_stabilizer_le
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    MulAction.stabilizer Γ x ≤ MulAction.stabilizer Γ (torusFamilyProjection P x) := by
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← torusFamilyProjection_affineMap R P ρ hP b hb, ← torusFamilyAffineMulAction_smul R hone
    hmul P ρ hP b hb hbone hbmul, hg]

/-- The affine action on the family of tori is free when the action on the base is free. -/
theorem isCancelSMul_torusFamilyAffineMulAction [IsCancelSMul Γ Y] :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun g x hg ↦ ?_
  exact isCancelSMul_iff_eq_one_of_smul_eq.1 ‹_› g _
    (torusFamilyAffineMulAction_stabilizer_le R hone hmul P ρ hP b hb hbone hbmul x hg)

end Group

end TauCeti
