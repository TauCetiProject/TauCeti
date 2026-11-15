/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Trivialization.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies of principal-bundle trivializations

A homotopy of global trivializations consists of equivariant product coordinates at every time,
with both the coordinates and their inverses jointly continuous. Relative to a reference
trivialization, these are exactly homotopies of continuous group-valued gauges. Thus the gauge
parametrization descends to homotopy classes. The reference is essential: it supplies the origin
for the parametrization, rather than a preferred trivialization of an arbitrary principal bundle.

The correspondence also retains homotopies fixed over any subset of the base. No local
compactness of the base, connectedness of the group, or existence of a reference independent of
the supplied trivializations is assumed. These comparisons are used when changing hemisphere
trivializations in clutching constructions.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Chapter 4, §§2–3.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (homotopies of clutching data).
-/

public section

noncomputable section

open Bundle unitInterval

namespace TauCeti.PrincipalBundle.GlobalTrivialization

variable {B G : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, MulAction Gᵐᵒᵖ (P b)]

/-- A family of equivariant global trivializations with jointly continuous coordinates and
inverses, joining the two specified trivializations. -/
structure Homotopy (τ υ : GlobalTrivialization G P) where
  /-- The global trivialization at each time. -/
  toFun : I → GlobalTrivialization G P
  /-- The initial trivialization. -/
  map_zero : toFun 0 = τ
  /-- The final trivialization. -/
  map_one : toFun 1 = υ
  /-- Joint continuity of the forward coordinates. -/
  continuous_toFun : Continuous fun x : I × TotalSpace G P ↦
    (x.2.proj, (toFun x.1).equivAt x.2.proj x.2.2)
  /-- Joint continuity of the inverse coordinates. -/
  continuous_invFun : Continuous fun x : I × (B × G) ↦
    (⟨x.2.1, ((toFun x.1).equivAt x.2.1).symm x.2.2⟩ : TotalSpace G P)

namespace Homotopy

variable {τ υ : GlobalTrivialization G P}

/-- Homotopies are determined by their trivializations at each time. -/
@[ext]
theorem ext {H H' : Homotopy τ υ} (h : ∀ t, H.toFun t = H'.toFun t) : H = H' := by
  cases H
  cases H'
  congr
  exact funext h

variable [IsTopologicalGroup G] (ρ : GlobalTrivialization G P)

/-- Read a homotopy of trivializations as the homotopy of its transition gauges from `ρ`. -/
def toGaugeHomotopy (H : Homotopy τ υ) :
    ContinuousMap.Homotopy (ρ.transition τ) (ρ.transition υ) where
  toFun x := (H.toFun x.1).equivAt x.2 (ρ.sectionValue x.2)
  continuous_toFun := (H.continuous_toFun.comp
    (continuous_fst.prodMk (ρ.continuous_sectionValue.comp continuous_snd))).snd
  map_zero_left b := by simp [H.map_zero]
  map_one_left b := by simp [H.map_one]

omit [IsTopologicalGroup G] in
/-- The gauge homotopy evaluates the current coordinates on the reference section. -/
@[simp]
theorem toGaugeHomotopy_apply (H : Homotopy τ υ) (t : I) (b : B) :
    H.toGaugeHomotopy ρ (t, b) = (H.toFun t).equivAt b (ρ.sectionValue b) :=
  (rfl)

/-- Turn a homotopy of gauges into a homotopy through actual equivariant trivializations.
The inverse coordinates use the inverse gauge, continuously in both time and base. -/
def ofGaugeHomotopy
    (F : ContinuousMap.Homotopy (ρ.transition τ) (ρ.transition υ)) : Homotopy τ υ where
  toFun t := ρ.gauge ⟨fun b ↦ F (t, b),
    F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  map_zero := by
    convert ρ.gauge_transition τ using 1
    congr 1
    ext b
    exact F.apply_zero b
  map_one := by
    convert ρ.gauge_transition υ using 1
    congr 1
    ext b
    exact F.apply_one b
  continuous_toFun := by
    simp only [equivAt_gauge, ContinuousMap.coe_mk]
    exact (ρ.continuous_toFun.fst.comp continuous_snd).prodMk
      ((F.continuous.comp (continuous_fst.prodMk
        (ρ.continuous_toFun.fst.comp continuous_snd))).mul
          (ρ.continuous_toFun.snd.comp continuous_snd))
  continuous_invFun := by
    simp only [equivAt_gauge_symm_apply, ContinuousMap.coe_mk]
    exact ρ.continuous_invFun.comp (continuous_snd.fst.prodMk
      ((F.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).inv.mul
        continuous_snd.snd))

/-- The trivialization at time `t` is the gauge change specified by that time slice. -/
theorem ofGaugeHomotopy_toFun
    (F : ContinuousMap.Homotopy (ρ.transition τ) (ρ.transition υ)) (t : I) :
    (ofGaugeHomotopy ρ F).toFun t = ρ.gauge
      ⟨fun b ↦ F (t, b), F.continuous.comp (continuous_const.prodMk continuous_id)⟩ :=
  (rfl)

/-- The coordinates at time `t` multiply the reference coordinates on the left. -/
@[simp]
theorem equivAt_ofGaugeHomotopy
    (F : ContinuousMap.Homotopy (ρ.transition τ) (ρ.transition υ)) (t : I) (b : B) (p : P b) :
    ((ofGaugeHomotopy ρ F).toFun t).equivAt b p = F (t, b) * ρ.equivAt b p :=
  equivAt_gauge _ _ _ _

/-- Homotopies of trivializations correspond bijectively to homotopies of transition gauges. -/
def gaugeEquiv : Homotopy τ υ ≃
    ContinuousMap.Homotopy (ρ.transition τ) (ρ.transition υ) where
  toFun := toGaugeHomotopy ρ
  invFun := ofGaugeHomotopy ρ
  left_inv H := by
    ext t b p
    rw [equivAt_ofGaugeHomotopy, toGaugeHomotopy_apply, ← transition_apply,
      ← equivAt_gauge, gauge_transition]
  right_inv F := by
    ext ⟨t, b⟩
    simp only [toGaugeHomotopy_apply, equivAt_ofGaugeHomotopy, equivAt_sectionValue, mul_one]

/-- The homotopy correspondence reads transition gauges. -/
@[simp]
theorem gaugeEquiv_apply (H : Homotopy τ υ) : gaugeEquiv ρ H = H.toGaugeHomotopy ρ :=
  (rfl)

/-- The inverse correspondence changes the reference coordinates by the gauge homotopy. -/
@[simp]
theorem gaugeEquiv_symm_apply
    (F : ContinuousMap.Homotopy (ρ.transition τ) (ρ.transition υ)) :
    (gaugeEquiv ρ).symm F = ofGaugeHomotopy ρ F :=
  (rfl)

end Homotopy

variable [IsTopologicalGroup G]

/-- A homotopy of trivializations fixed over `S`: every fibre coordinate over `S` agrees with
the initial trivialization throughout the homotopy. -/
abbrev HomotopyRel (τ υ : GlobalTrivialization G P) (S : Set B) :=
  {H : Homotopy τ υ // ∀ t b, b ∈ S → ∀ p : P b,
    (H.toFun t).equivAt b p = τ.equivAt b p}

variable (ρ τ υ : GlobalTrivialization G P)

/-- Relative homotopies of trivializations correspond to relative homotopies of their gauges,
for any subset of the base, without a closedness assumption. -/
def homotopyRelEquiv (S : Set B) : HomotopyRel τ υ S ≃
    ContinuousMap.HomotopyRel (ρ.transition τ) (ρ.transition υ) S where
  toFun H :=
    { toHomotopy := H.1.toGaugeHomotopy ρ
      prop' t b hb := by
        exact (Homotopy.toGaugeHomotopy_apply ρ H.1 t b).trans
          ((H.2 t b hb (ρ.sectionValue b)).trans (transition_apply ρ τ b).symm) }
  invFun F := ⟨Homotopy.ofGaugeHomotopy ρ F.toHomotopy, fun t b hb p ↦ by
    rw [Homotopy.equivAt_ofGaugeHomotopy, ContinuousMap.HomotopyWith.coe_toHomotopy,
      F.eq_fst t hb, ← equivAt_gauge, gauge_transition]⟩
  left_inv H := Subtype.ext ((Homotopy.gaugeEquiv ρ).left_inv H.1)
  right_inv F := by
    apply ContinuousMap.HomotopyWith.ext
    intro x
    exact DFunLike.congr_fun ((Homotopy.gaugeEquiv ρ).right_inv F.toHomotopy) x

/-- Relative gauge homotopies read the current coordinates on the reference section. -/
@[simp]
theorem homotopyRelEquiv_apply (S : Set B) (H : HomotopyRel τ υ S) (t : I) (b : B) :
    homotopyRelEquiv ρ τ υ S H (t, b) = (H.1.toFun t).equivAt b (ρ.sectionValue b) :=
  (rfl)

/-- The inverse relative correspondence retains the underlying gauge homotopy. -/
@[simp]
theorem homotopyRelEquiv_symm_apply (S : Set B)
    (F : ContinuousMap.HomotopyRel (ρ.transition τ) (ρ.transition υ) S) :
    ((homotopyRelEquiv ρ τ υ S).symm F).1 = Homotopy.ofGaugeHomotopy ρ F.toHomotopy :=
  (rfl)

/-- Two global trivializations are homotopic through equivariant product coordinates with
jointly continuous inverses. -/
def Homotopic (τ υ : GlobalTrivialization G P) : Prop := Nonempty (Homotopy τ υ)

omit [IsTopologicalGroup G] in
/-- Homotopy of trivializations means existence of a jointly continuous family of coordinates
and inverses. -/
theorem homotopic_iff_nonempty : Homotopic τ υ ↔ Nonempty (Homotopy τ υ) :=
  Iff.rfl

/-- A reference trivialization detects homotopy by the homotopy of transition gauges. -/
theorem homotopic_iff : Homotopic τ υ ↔ (ρ.transition τ).Homotopic (ρ.transition υ) :=
  (Homotopy.gaugeEquiv ρ).nonempty_congr

/-- Gauge changes are homotopic exactly when their continuous gauges are homotopic. -/
@[simp]
theorem homotopic_gauge_iff (a c : C(B, G)) :
    Homotopic (ρ.gauge a) (ρ.gauge c) ↔ a.Homotopic c := by
  simpa only [transition_gauge] using homotopic_iff ρ (ρ.gauge a) (ρ.gauge c)

namespace Homotopic

/-- The constant family is a homotopy from any trivialization to itself. -/
@[refl]
theorem refl (τ : GlobalTrivialization G P) : Homotopic τ τ :=
  (homotopic_iff τ τ τ).2 (.refl _)

/-- Reverse a homotopy of trivializations. -/
@[symm]
theorem symm {τ υ : GlobalTrivialization G P} (h : Homotopic τ υ) : Homotopic υ τ :=
  (homotopic_iff τ υ τ).2 (((homotopic_iff τ τ υ).1 h).symm)

/-- Concatenate homotopies of trivializations. -/
@[trans]
theorem trans {τ υ ω : GlobalTrivialization G P} (h : Homotopic τ υ) (h' : Homotopic υ ω) :
    Homotopic τ ω :=
  (homotopic_iff τ τ ω).2
    (((homotopic_iff τ τ υ).1 h).trans ((homotopic_iff τ υ ω).1 h'))

/-- The setoid of global trivializations under homotopy. -/
def setoid : Setoid (GlobalTrivialization G P) where
  r := Homotopic
  iseqv := ⟨refl, symm, trans⟩

/-- The homotopy setoid relates exactly the homotopic trivializations. -/
@[simp]
theorem setoid_iff (τ υ : GlobalTrivialization G P) : setoid τ υ ↔ Homotopic τ υ :=
  Iff.rfl

end Homotopic

/-- A reference trivialization identifies homotopy classes of trivializations with homotopy
classes of continuous maps to the structure group. -/
def homotopyClassEquiv : Quotient (Homotopic.setoid (G := G) (P := P)) ≃
    Quotient ⟨ContinuousMap.Homotopic (X := B) (Y := G),
      ContinuousMap.Homotopic.equivalence⟩ :=
  Quotient.congr ρ.gaugeEquiv.symm (fun τ υ ↦ by
    simpa only [Homotopic.setoid_iff, GlobalTrivialization.gaugeEquiv_symm_apply]
      using homotopic_iff ρ τ υ)

/-- The class correspondence sends a trivialization to its transition gauge from the reference. -/
@[simp]
theorem homotopyClassEquiv_mk (τ : GlobalTrivialization G P) :
    ρ.homotopyClassEquiv (Quotient.mk _ τ) = Quotient.mk _ (ρ.transition τ) :=
  Quotient.congr_mk _ _ τ |>.trans (congrArg (Quotient.mk _)
    (GlobalTrivialization.gaugeEquiv_symm_apply ρ τ))

/-- The inverse class correspondence changes the reference by a representative gauge. -/
@[simp]
theorem homotopyClassEquiv_symm_mk (a : C(B, G)) :
    ρ.homotopyClassEquiv.symm (Quotient.mk _ a) = Quotient.mk _ (ρ.gauge a) := by
  apply ρ.homotopyClassEquiv.injective
  simp

end TauCeti.PrincipalBundle.GlobalTrivialization
