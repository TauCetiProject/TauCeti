/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Global trivializations of principal bundles

A global trivialization of a right principal bundle identifies it equivariantly with the product
bundle. Such trivializations correspond to continuous sections: a section supplies the origin in
each fibre, and the division map supplies the group coordinate. With a reference trivialization,
all others are uniquely obtained by left multiplication by a continuous group-valued map.
The multiplication is on the left even though the principal action is on the right.

The correspondence retains actual trivializations and sections, not their homotopy classes, and
requires neither a connected structure group nor separation assumptions on the base.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Chapter 4, §§2–3.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry I*, Chapter I, §5.
-/

public section

noncomputable section

open Bundle MulOpposite

namespace TauCeti.PrincipalBundle

variable {B G : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, MulAction Gᵐᵒᵖ (P b)]

/-- An equivariant global trivialization of a right principal bundle. Its fibre equivalences and
their inverses assemble to continuous maps of total spaces. -/
structure GlobalTrivialization (G : Type*) [Group G] [TopologicalSpace G]
    (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, MulAction Gᵐᵒᵖ (P b)] where
  /-- The group coordinate in each fibre. -/
  toEquiv : ∀ b, P b ≃ G
  /-- Continuity of the product coordinates. -/
  continuous_toFun : Continuous fun p : TotalSpace G P ↦ (p.proj, toEquiv p.proj p.2)
  /-- Joint continuity of the inverse coordinates. -/
  continuous_invFun : Continuous fun x : B × G ↦
    (⟨x.1, (toEquiv x.1).symm x.2⟩ : TotalSpace G P)
  /-- The coordinates intertwine the right action with right multiplication. -/
  map_smul : ∀ b (p : P b) (g : G), toEquiv b (op g • p) = toEquiv b p * g

namespace GlobalTrivialization

variable (τ υ : GlobalTrivialization G P)

/-- Global trivializations are determined by their group coordinates. -/
@[ext]
theorem ext (h : ∀ b p, τ.toEquiv b p = υ.toEquiv b p) : τ = υ := by
  have he : τ.toEquiv = υ.toEquiv := funext fun b ↦ Equiv.ext (h b)
  cases τ
  cases υ
  cases he
  rfl

/-- The equivariant homeomorphism from the total space to the product bundle. -/
def homeomorph : TotalSpace G P ≃ₜ B × G where
  toFun p := (p.proj, τ.toEquiv p.proj p.2)
  invFun x := ⟨x.1, (τ.toEquiv x.1).symm x.2⟩
  left_inv p := by simp
  right_inv x := by simp
  continuous_toFun := τ.continuous_toFun
  continuous_invFun := τ.continuous_invFun

/-- The homeomorphism records the base point and the group coordinate. -/
@[simp]
theorem homeomorph_apply (p : TotalSpace G P) :
    τ.homeomorph p = (p.proj, τ.toEquiv p.proj p.2) :=
  (rfl)

/-- The inverse homeomorphism uses the inverse fibre coordinate. -/
@[simp]
theorem homeomorph_symm_apply (x : B × G) :
    τ.homeomorph.symm x = ⟨x.1, (τ.toEquiv x.1).symm x.2⟩ :=
  (rfl)

/-- The section whose group coordinate is the identity. -/
def sectionValue (b : B) : P b := (τ.toEquiv b).symm 1

/-- The selected section has coordinate one. -/
@[simp]
theorem toEquiv_sectionValue (b : B) : τ.toEquiv b (τ.sectionValue b) = 1 :=
  (τ.toEquiv b).apply_symm_apply 1

/-- The section selected by a global trivialization is continuous. -/
theorem continuous_sectionValue :
    Continuous fun b ↦ (⟨b, τ.sectionValue b⟩ : TotalSpace G P) :=
  τ.continuous_invFun.comp (continuous_id.prodMk continuous_const)

/-- The inverse coordinates are obtained by the right action on the selected section. -/
theorem symm_apply_eq_smul (b : B) (g : G) :
    (τ.toEquiv b).symm g = op g • τ.sectionValue b := by
  apply (τ.toEquiv b).injective
  simp [τ.map_smul]

section Sections

variable [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [PrincipalBundle G P]
  [IsTopologicalGroup G]

/-- A continuous section trivializes a principal bundle using its division map. -/
def ofSection (σ : ∀ b, P b)
    (hσ : Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)) : GlobalTrivialization G P where
  toEquiv b :=
    { toFun := division G (σ b)
      invFun := fun g ↦ op g • σ b
      left_inv := smul_division (σ b)
      right_inv := fun g ↦ by simp }
  continuous_toFun := (FiberBundle.continuous_proj G P).prodMk
    ((hσ.comp (FiberBundle.continuous_proj G P)).division continuous_id)
  continuous_invFun := (hσ.comp continuous_fst).totalSpaceMk_smul continuous_snd
  map_smul := fun b p g ↦ division_smul_right (σ b) p g

/-- The coordinates supplied by a section are the division from that section. -/
@[simp]
theorem ofSection_toEquiv (σ : ∀ b, P b)
    (hσ : Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)) (b : B) (p : P b) :
    (ofSection σ hσ).toEquiv b p = division G (σ b) p :=
  (rfl)

/-- The trivialization constructed from a section selects that same section. -/
@[simp]
theorem sectionValue_ofSection (σ : ∀ b, P b)
    (hσ : Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)) (b : B) :
    (ofSection σ hσ).sectionValue b = σ b := by
  simp [sectionValue, ofSection]

omit [IsTopologicalGroup G] in
/-- The coordinate of a point is its division from the section of the trivialization. -/
theorem toEquiv_eq_division (b : B) (p : P b) :
    τ.toEquiv b p = division G (τ.sectionValue b) p := by
  symm
  apply division_eq_iff.2
  exact (τ.symm_apply_eq_smul b (τ.toEquiv b p)).symm.trans
    ((τ.toEquiv b).symm_apply_apply p)

/-- A trivialization is reconstructed from its selected section. -/
@[simp]
theorem ofSection_sectionValue : ofSection τ.sectionValue τ.continuous_sectionValue = τ := by
  ext b p
  exact (τ.toEquiv_eq_division b p).symm

/-- Global equivariant trivializations correspond to continuous sections, with no chosen origin. -/
def sectionEquiv : GlobalTrivialization G P ≃
    {σ : ∀ b, P b // Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)} where
  toFun τ := ⟨τ.sectionValue, τ.continuous_sectionValue⟩
  invFun σ := ofSection σ.1 σ.2
  left_inv τ := τ.ofSection_sectionValue
  right_inv σ := Subtype.ext (funext (sectionValue_ofSection σ.1 σ.2))

/-- The section correspondence selects the identity-coordinate section. -/
@[simp]
theorem sectionEquiv_apply : (sectionEquiv τ).1 = τ.sectionValue :=
  (rfl)

/-- The inverse section correspondence uses division coordinates. -/
@[simp]
theorem sectionEquiv_symm_apply
    (σ : {σ : ∀ b, P b // Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)}) :
    sectionEquiv.symm σ = ofSection σ.1 σ.2 :=
  (rfl)

end Sections

section Gauge

variable [IsTopologicalGroup G]

/-- Change the coordinates by left multiplication by a continuous gauge `a`. -/
def gauge (a : C(B, G)) : GlobalTrivialization G P where
  toEquiv b := (τ.toEquiv b).trans (Equiv.mulLeft (a b))
  continuous_toFun := τ.continuous_toFun.fst.prodMk
    ((a.continuous.comp τ.continuous_toFun.fst).mul τ.continuous_toFun.snd)
  continuous_invFun := τ.continuous_invFun.comp
    (continuous_fst.prodMk ((a.continuous.comp continuous_fst).inv.mul continuous_snd))
  map_smul b p g := by simp [τ.map_smul, mul_assoc]

/-- A gauge multiplies the group coordinate on the left. -/
@[simp]
theorem gauge_toEquiv (a : C(B, G)) (b : B) (p : P b) :
    (τ.gauge a).toEquiv b p = a b * τ.toEquiv b p :=
  (rfl)

/-- The inverse coordinate change multiplies by the inverse gauge on the left. -/
@[simp]
theorem gauge_toEquiv_symm (a : C(B, G)) (b : B) (g : G) :
    ((τ.gauge a).toEquiv b).symm g = (τ.toEquiv b).symm ((a b)⁻¹ * g) :=
  (rfl)

/-- Changing coordinates by `a` moves the selected section by the inverse right action. -/
@[simp]
theorem sectionValue_gauge (a : C(B, G)) (b : B) :
    (τ.gauge a).sectionValue b = op ((a b)⁻¹) • τ.sectionValue b := by
  rw [sectionValue, gauge_toEquiv_symm, mul_one, symm_apply_eq_smul]

/-- The identity gauge leaves the trivialization unchanged. -/
@[simp]
theorem gauge_one : τ.gauge 1 = τ := by
  ext b p
  simp

/-- Successive left gauge changes multiply in their order of application. -/
@[simp]
theorem gauge_gauge (a c : C(B, G)) : (τ.gauge a).gauge c = τ.gauge (c * a) := by
  ext b p
  simp [mul_assoc]

/-- The transition gauge from `τ` to `υ`, evaluated on the section of `τ`. -/
def transition : C(B, G) :=
  ⟨fun b ↦ υ.toEquiv b (τ.sectionValue b),
    continuous_snd.comp (υ.continuous_toFun.comp τ.continuous_sectionValue)⟩

omit [IsTopologicalGroup G] in
/-- Evaluate the target coordinate on the section of the reference. -/
@[simp]
theorem transition_apply (b : B) : τ.transition υ b = υ.toEquiv b (τ.sectionValue b) :=
  (rfl)

/-- A trivialization is recovered from a reference by its transition gauge. -/
@[simp]
theorem gauge_transition : τ.gauge (τ.transition υ) = υ := by
  ext b p
  rw [gauge_toEquiv, transition_apply, ← υ.map_smul,
    ← τ.symm_apply_eq_smul, Equiv.symm_apply_apply]

/-- The gauge changing a fixed reference to a trivialization is unique. -/
@[simp]
theorem transition_gauge (a : C(B, G)) : τ.transition (τ.gauge a) = a := by
  ext b
  simp

/-- Relative to a reference trivialization, continuous gauges parametrize all trivializations. -/
def gaugeEquiv : C(B, G) ≃ GlobalTrivialization G P where
  toFun := τ.gauge
  invFun := τ.transition
  left_inv := τ.transition_gauge
  right_inv υ := τ.gauge_transition υ

/-- Gauge parametrization acts by left coordinate change. -/
@[simp]
theorem gaugeEquiv_apply (a : C(B, G)) : τ.gaugeEquiv a = τ.gauge a :=
  (rfl)

/-- The inverse gauge parametrization is the transition from the reference. -/
@[simp]
theorem gaugeEquiv_symm_apply : τ.gaugeEquiv.symm υ = τ.transition υ :=
  (rfl)

/-- Changing reference from `τ` through `υ` composes the transition gauges on the left. -/
theorem transition_mul (ρ : GlobalTrivialization G P) :
    υ.transition ρ * τ.transition υ = τ.transition ρ := by
  apply τ.gaugeEquiv.injective
  simp only [gaugeEquiv_apply, ← gauge_gauge, gauge_transition]

omit [IsTopologicalGroup G] in
/-- The transition from a trivialization to itself is the identity gauge. -/
@[simp]
theorem transition_self : τ.transition τ = 1 := by
  ext b
  simp

/-- Reversing a transition inverts its gauge. -/
theorem transition_reverse : υ.transition τ = (τ.transition υ)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, transition_mul, transition_self]

/-- Continuous gauges act freely and transitively on global trivializations. -/
instance : MulAction C(B, G) (GlobalTrivialization G P) where
  smul a τ := τ.gauge a
  one_smul τ := τ.gauge_one
  mul_smul a c τ := (τ.gauge_gauge c a).symm

/-- The action is the left coordinate change. -/
@[simp]
theorem smul_toEquiv (a : C(B, G)) (b : B) (p : P b) :
    (a • τ).toEquiv b p = a b * τ.toEquiv b p :=
  (rfl)

/-- The action is free, including over the empty base. -/
theorem smul_eq_smul_iff (a c : C(B, G)) : a • τ = c • τ ↔ a = c :=
  τ.gaugeEquiv.injective.eq_iff

/-- A transition gauge carries its reference trivialization to its target. -/
@[simp]
theorem transition_smul : τ.transition υ • τ = υ :=
  τ.gauge_transition υ

/-- Any two trivializations differ by a continuous gauge. -/
instance : MulAction.IsPretransitive C(B, G) (GlobalTrivialization G P) :=
  ⟨fun τ υ ↦ ⟨τ.transition υ, τ.transition_smul υ⟩⟩

end Gauge

section Pullback

variable {B' : Type*} [TopologicalSpace B'] (f : C(B', B))

/-- Pull back global coordinates along a continuous map of bases. -/
def pullback : GlobalTrivialization G ((⇑f) *ᵖ P) where
  toEquiv b := τ.toEquiv (f b)
  continuous_toFun := (Pullback.continuous_proj G P f).prodMk
    (τ.continuous_toFun.snd.comp (Pullback.continuous_lift G P f))
  continuous_invFun := (inducing_pullbackTotalSpaceEmbedding G P f).continuous_iff.2
    (continuous_fst.prodMk (τ.continuous_invFun.comp
      ((f.continuous.comp continuous_fst).prodMk continuous_snd)))
  map_smul b p g := τ.map_smul (f b) p g

/-- Pullback reads the coordinate over the image base point. -/
@[simp]
theorem pullback_toEquiv (b : B') (p : ((⇑f) *ᵖ P) b) :
    (τ.pullback f).toEquiv b p = τ.toEquiv (f b) p :=
  (rfl)

/-- The selected section pulls back by composition on the base. -/
@[simp]
theorem sectionValue_pullback (b : B') : (τ.pullback f).sectionValue b = τ.sectionValue (f b) :=
  (rfl)

/-- Pullback preserves the reference transition map. -/
@[simp]
theorem transition_pullback :
    (τ.pullback f).transition (υ.pullback f) = (τ.transition υ).comp f := by
  ext b
  rfl

variable [IsTopologicalGroup G]

/-- Coordinate gauge changes commute with pullback. -/
@[simp]
theorem gauge_pullback (a : C(B, G)) :
    (τ.gauge a).pullback f = (τ.pullback f).gauge (a.comp f) := by
  ext b p
  rfl

end Pullback

/-- The canonical trivialization of the product principal bundle. -/
def trivial (B G : Type*) [TopologicalSpace B] [Group G] [TopologicalSpace G] :
    GlobalTrivialization G (Bundle.Trivial B G) where
  toEquiv _ := Equiv.refl G
  continuous_toFun := (Bundle.Trivial.homeomorphProd B G).continuous
  continuous_invFun := (Bundle.Trivial.homeomorphProd B G).symm.continuous
  map_smul _ _ _ := rfl

/-- The canonical product trivialization has the identity group coordinate. -/
@[simp]
theorem trivial_toEquiv (b : B) (g : G) : (trivial B G).toEquiv b g = g :=
  (rfl)

/-- The canonical product trivialization selects the constant identity section. -/
@[simp]
theorem sectionValue_trivial (b : B) : (trivial B G).sectionValue b = 1 :=
  (rfl)

end GlobalTrivialization

end TauCeti.PrincipalBundle
