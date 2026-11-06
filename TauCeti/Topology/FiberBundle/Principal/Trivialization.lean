/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.VectorBundle.Trivialization
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Global trivializations of principal bundles

A global trivialization of a right principal bundle identifies it equivariantly with the product
bundle. Such trivializations correspond to continuous sections: a section supplies the origin in
each fibre, and the division map supplies the group coordinate. With a reference trivialization,
all others are uniquely obtained by left multiplication by a continuous group-valued map.
The multiplication is on the left even though the principal action is on the right.

Global trivializations bundle native `Bundle.Trivialization` data with equivariance and a full
base set; fibre equivalences and the total-space homeomorphism are derived from that data.
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

/-- An equivariant native bundle trivialization whose base set is the whole base. -/
structure GlobalTrivialization (G : Type*) [Group G] [TopologicalSpace G]
    (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, MulAction Gᵐᵒᵖ (P b)]
    extends Trivialization G (π G P) where
  /-- The trivialization is defined over every base point. -/
  baseSet_eq_univ : toTrivialization.baseSet = Set.univ
  /-- The native trivialization intertwines the right action with right multiplication. -/
  isEquivariant : toTrivialization.IsEquivariant

namespace GlobalTrivialization

variable (τ υ : GlobalTrivialization G P)

attribute [instance] GlobalTrivialization.isEquivariant

/-- Every base point belongs to a global trivialization's base set. -/
theorem mem_baseSet (b : B) : b ∈ τ.toTrivialization.baseSet := by
  simp [τ.baseSet_eq_univ]

/-- The equivariant homeomorphism from the total space to the product bundle. -/
def homeomorph : TotalSpace G P ≃ₜ B × G :=
  (τ.toTrivialization.homeomorphTrivial τ.baseSet_eq_univ).trans
    (Bundle.Trivial.homeomorphProd B G)

private theorem homeomorph_symm_apply_eq (x : B × G) :
    τ.homeomorph.symm x = τ.toOpenPartialHomeomorph.symm x := by
  simp [homeomorph]

private theorem nonempty_fibres (τ : GlobalTrivialization G P) : ∀ b, Nonempty (P b) := by
  intro b
  obtain ⟨p, _, hp⟩ := τ.toTrivialization.proj_surjOn_baseSet (τ.mem_baseSet b)
  exact hp ▸ ⟨p.2⟩

/-- Restriction of the native trivialization to a fibre. -/
def equivAt (b : B) : P b ≃ G :=
  letI := τ.nonempty_fibres
  { toFun p := (τ.toTrivialization ⟨b, p⟩).2
    invFun := τ.toTrivialization.symm b
    left_inv p := τ.toTrivialization.symm_apply_apply_mk (τ.mem_baseSet b) p
    right_inv g := congrArg Prod.snd
      (τ.toTrivialization.apply_mk_symm (τ.mem_baseSet b) g) }

/-- The fibre coordinate is the second component of the native trivialization. -/
theorem equivAt_apply (b : B) (p : P b) :
    τ.equivAt b p = (τ.toTrivialization ⟨b, p⟩).2 :=
  (rfl)

/-- The homeomorphism records the base point and the group coordinate. -/
@[simp]
theorem homeomorph_apply (p : TotalSpace G P) :
    τ.homeomorph p = (p.proj, τ.equivAt p.proj p.2) :=
  congrArg (Bundle.Trivial.homeomorphProd B G)
    (τ.toTrivialization.homeomorphTrivial_apply τ.baseSet_eq_univ p)

/-- The inverse homeomorphism uses the inverse fibre coordinate. -/
@[simp]
theorem homeomorph_symm_apply (x : B × G) :
    τ.homeomorph.symm x = ⟨x.1, (τ.equivAt x.1).symm x.2⟩ := by
  rw [homeomorph_symm_apply_eq]
  let := τ.nonempty_fibres
  exact (τ.toTrivialization.mk_symm (τ.mem_baseSet x.1) x.2).symm

/-- Global trivializations are determined by their group coordinates. -/
@[ext]
theorem ext (h : ∀ b p, τ.equivAt b p = υ.equivAt b p) : τ = υ := by
  have hh : τ.homeomorph = υ.homeomorph := Homeomorph.ext fun p ↦ by
    simp only [homeomorph_apply, h]
  have he : τ.toTrivialization = υ.toTrivialization := by
    apply Trivialization.ext'
    · apply OpenPartialHomeomorph.ext
      · intro p
        apply Prod.ext
        · exact (τ.toTrivialization.coe_fst' (τ.mem_baseSet p.proj)).trans
            (υ.toTrivialization.coe_fst' (υ.mem_baseSet p.proj)).symm
        · exact h p.proj p.2
      · intro x
        simpa only [homeomorph_symm_apply_eq] using
          DFunLike.congr_fun (congrArg Homeomorph.symm hh) x
      · rw [τ.source_eq, υ.source_eq, τ.baseSet_eq_univ, υ.baseSet_eq_univ]
    · rw [τ.baseSet_eq_univ, υ.baseSet_eq_univ]
  cases τ
  cases υ
  cases he
  rfl

/-- Continuity of the global product coordinates. -/
theorem continuous_toFun :
    Continuous fun p : TotalSpace G P ↦ (p.proj, τ.equivAt p.proj p.2) := by
  simpa only [← homeomorph_apply] using τ.homeomorph.continuous

/-- Joint continuity of the inverse fibre coordinates. -/
theorem continuous_invFun :
    Continuous fun x : B × G ↦ (⟨x.1, (τ.equivAt x.1).symm x.2⟩ : TotalSpace G P) := by
  simpa only [← homeomorph_symm_apply] using τ.homeomorph.symm.continuous

/-- Global coordinates intertwine the right action with right multiplication. -/
@[simp]
theorem equivAt_op_smul (b : B) (p : P b) (g : G) :
    τ.equivAt b (op g • p) = τ.equivAt b p * g :=
  τ.toTrivialization.snd_apply_smul (τ.mem_baseSet b) p g

/-- Assemble global coordinates from equivariant fibre equivalences with jointly continuous
forward and inverse maps. -/
def ofEquiv (e : ∀ b, P b ≃ G)
    (hc : Continuous fun p : TotalSpace G P ↦ (p.proj, e p.proj p.2))
    (hi : Continuous fun x : B × G ↦ (⟨x.1, (e x.1).symm x.2⟩ : TotalSpace G P))
    (he : ∀ b (p : P b) (g : G), e b (op g • p) = e b p * g) :
    GlobalTrivialization G P where
  toFun p := (p.proj, e p.proj p.2)
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := by simp
  right_inv' x _ := by simp
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := hc.continuousOn
  continuousOn_invFun := hi.continuousOn
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := (Set.preimage_univ).symm
  target_eq := Set.univ_prod_univ.symm
  proj_toFun _ _ := rfl
  baseSet_eq_univ := rfl
  isEquivariant := ⟨fun b _ p g ↦ he b p g⟩

/-- The assembled global trivialization has the prescribed fibre coordinates. -/
@[simp]
theorem equivAt_ofEquiv (e : ∀ b, P b ≃ G)
    (hc : Continuous fun p : TotalSpace G P ↦ (p.proj, e p.proj p.2))
    (hi : Continuous fun x : B × G ↦ (⟨x.1, (e x.1).symm x.2⟩ : TotalSpace G P))
    (he : ∀ b (p : P b) (g : G), e b (op g • p) = e b p * g) (b : B) (p : P b) :
    (ofEquiv e hc hi he).equivAt b p = e b p :=
  (rfl)

/-- The section whose group coordinate is the identity. -/
def sectionValue (b : B) : P b := (τ.equivAt b).symm 1

/-- The selected section has coordinate one. -/
@[simp]
theorem equivAt_sectionValue (b : B) : τ.equivAt b (τ.sectionValue b) = 1 :=
  (τ.equivAt b).apply_symm_apply 1

/-- The section selected by a global trivialization is continuous. -/
theorem continuous_sectionValue :
    Continuous fun b ↦ (⟨b, τ.sectionValue b⟩ : TotalSpace G P) :=
  τ.continuous_invFun.comp (continuous_id.prodMk continuous_const)

/-- The inverse coordinates are obtained by the right action on the selected section. -/
theorem equivAt_symm_apply (b : B) (g : G) :
    (τ.equivAt b).symm g = op g • τ.sectionValue b := by
  have h : τ.homeomorph.symm (b, g) = op g • τ.homeomorph.symm (b, 1) := by
    rw [homeomorph_symm_apply_eq, homeomorph_symm_apply_eq]
    exact τ.toTrivialization.symm_apply_eq_smul (τ.mem_baseSet b) g
  rw [homeomorph_symm_apply, homeomorph_symm_apply] at h
  exact TotalSpace.mk_injective b h

section Sections

variable [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [PrincipalBundle G P]
  [IsTopologicalGroup G]

/-- A continuous section trivializes a principal bundle using its division map. -/
def ofSection (σ : ∀ b, P b)
    (hσ : Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)) : GlobalTrivialization G P where
  toTrivialization := trivializationOfSection σ isOpen_univ hσ.continuousOn
  baseSet_eq_univ := baseSet_trivializationOfSection σ isOpen_univ hσ.continuousOn
  isEquivariant := inferInstance

/-- The coordinates supplied by a section are the division from that section. -/
@[simp]
theorem equivAt_ofSection (σ : ∀ b, P b)
    (hσ : Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)) (b : B) (p : P b) :
    (ofSection σ hσ).equivAt b p = division G (σ b) p :=
  congrArg Prod.snd (trivializationOfSection_apply σ isOpen_univ hσ.continuousOn ⟨b, p⟩)

/-- The trivialization constructed from a section selects that same section. -/
@[simp]
theorem sectionValue_ofSection (σ : ∀ b, P b)
    (hσ : Continuous fun b ↦ (⟨b, σ b⟩ : TotalSpace G P)) (b : B) :
    (ofSection σ hσ).sectionValue b = σ b := by
  apply (ofSection σ hσ).equivAt b |>.injective
  simp

omit [IsTopologicalGroup G] in
/-- The coordinate of a point is its division from the section of the trivialization. -/
theorem equivAt_eq_division (b : B) (p : P b) :
    τ.equivAt b p = division G (τ.sectionValue b) p := by
  symm
  apply division_eq_iff.2
  exact (τ.equivAt_symm_apply b (τ.equivAt b p)).symm.trans
    ((τ.equivAt b).symm_apply_apply p)

/-- A trivialization is reconstructed from its selected section. -/
@[simp]
theorem ofSection_sectionValue : ofSection τ.sectionValue τ.continuous_sectionValue = τ := by
  ext b p
  simpa only [equivAt_ofSection] using (τ.equivAt_eq_division b p).symm

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
def gauge (a : C(B, G)) : GlobalTrivialization G P :=
  ofEquiv (fun b ↦ (τ.equivAt b).trans (Equiv.mulLeft (a b)))
    (τ.continuous_toFun.fst.prodMk
      ((a.continuous.comp τ.continuous_toFun.fst).mul τ.continuous_toFun.snd))
    (τ.continuous_invFun.comp
      (continuous_fst.prodMk ((a.continuous.comp continuous_fst).inv.mul continuous_snd)))
    (fun b p g ↦ by simp [mul_assoc])

/-- A gauge multiplies the group coordinate on the left. -/
@[simp]
theorem equivAt_gauge (a : C(B, G)) (b : B) (p : P b) :
    (τ.gauge a).equivAt b p = a b * τ.equivAt b p :=
  (rfl)

/-- The inverse coordinate change multiplies by the inverse gauge on the left. -/
@[simp]
theorem equivAt_gauge_symm_apply (a : C(B, G)) (b : B) (g : G) :
    ((τ.gauge a).equivAt b).symm g = (τ.equivAt b).symm ((a b)⁻¹ * g) := by
  apply ((τ.gauge a).equivAt b).injective
  simp

/-- Changing coordinates by `a` moves the selected section by the inverse right action. -/
@[simp]
theorem sectionValue_gauge (a : C(B, G)) (b : B) :
    (τ.gauge a).sectionValue b = op ((a b)⁻¹) • τ.sectionValue b := by
  rw [sectionValue, equivAt_gauge_symm_apply, mul_one, equivAt_symm_apply]

/-- The identity gauge leaves the trivialization unchanged. -/
@[simp]
theorem gauge_one : τ.gauge 1 = τ := by
  ext b p
  simp

/-- Applying `a` and then `c` is the single gauge change by `c * a`;
later gauges multiply on the left. -/
@[simp]
theorem gauge_gauge (a c : C(B, G)) : (τ.gauge a).gauge c = τ.gauge (c * a) := by
  ext b p
  simp [mul_assoc]

/-- The transition gauge from `τ` to `υ`, evaluated on the section of `τ`. -/
def transition : C(B, G) :=
  ⟨fun b ↦ υ.equivAt b (τ.sectionValue b),
    (υ.continuous_toFun.comp τ.continuous_sectionValue).snd⟩

omit [IsTopologicalGroup G] in
/-- Evaluate the target coordinate on the section of the reference. -/
@[simp]
theorem transition_apply (b : B) : τ.transition υ b = υ.equivAt b (τ.sectionValue b) :=
  (rfl)

omit [IsTopologicalGroup G] in
/-- The transition gauge is the native coordinate change evaluated at the identity. -/
theorem transition_eq_coordChange (b : B) :
    τ.transition υ b = τ.toTrivialization.coordChange υ.toTrivialization b 1 := by
  have h := τ.toTrivialization.mk_coordChange υ.toTrivialization
    (τ.mem_baseSet b) (υ.mem_baseSet b) 1
  rw [← homeomorph_symm_apply_eq, homeomorph_symm_apply] at h
  simpa only [transition_apply, equivAt_apply, sectionValue] using (congrArg Prod.snd h).symm

/-- A trivialization is recovered from a reference by its transition gauge. -/
@[simp]
theorem gauge_transition : τ.gauge (τ.transition υ) = υ := by
  ext b p
  rw [equivAt_gauge, transition_apply, ← υ.equivAt_op_smul,
    ← τ.equivAt_symm_apply, Equiv.symm_apply_apply]

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
@[simp]
theorem transition_mul_transition (ρ : GlobalTrivialization G P) :
    υ.transition ρ * τ.transition υ = τ.transition ρ := by
  ext b
  simp only [ContinuousMap.mul_apply, transition_eq_coordChange]
  exact (υ.toTrivialization.coordChange_eq_mul ρ.toTrivialization
    (υ.mem_baseSet b) (ρ.mem_baseSet b) _).symm.trans
    (τ.toTrivialization.coordChange_coordChange υ.toTrivialization ρ.toTrivialization
      (τ.mem_baseSet b) (υ.mem_baseSet b) 1)

omit [IsTopologicalGroup G] in
/-- The transition from a trivialization to itself is the identity gauge. -/
@[simp]
theorem transition_self : τ.transition τ = 1 := by
  ext b
  simp

/-- Reversing a transition inverts its gauge. -/
@[simp]
theorem inv_transition : (τ.transition υ)⁻¹ = υ.transition τ := by
  rw [inv_eq_iff_mul_eq_one, transition_mul_transition, transition_self]

/-- Continuous gauges act on global trivializations by left coordinate change. -/
instance : MulAction C(B, G) (GlobalTrivialization G P) where
  smul a τ := τ.gauge a
  one_smul τ := τ.gauge_one
  mul_smul a c τ := (τ.gauge_gauge c a).symm

/-- The action is given by the explicit gauge construction. -/
@[simp]
theorem smul_def (a : C(B, G)) : a • τ = τ.gauge a :=
  (rfl)

/-- The action is free, including over the empty base. -/
theorem smul_eq_smul_iff (a c : C(B, G)) : a • τ = c • τ ↔ a = c :=
  τ.gaugeEquiv.injective.eq_iff

/-- Any two trivializations differ by a continuous gauge. -/
instance : MulAction.IsPretransitive C(B, G) (GlobalTrivialization G P) :=
  ⟨fun τ υ ↦ ⟨τ.transition υ, by simp⟩⟩

end Gauge

section Pullback

variable {B' : Type*} [TopologicalSpace B'] (f : C(B', B))

/-- Pull back global coordinates along a continuous map of bases. -/
def pullback : GlobalTrivialization G ((⇑f) *ᵖ P) :=
  letI := τ.nonempty_fibres
  { toTrivialization := τ.toTrivialization.pullback f
    baseSet_eq_univ := by simp [τ.baseSet_eq_univ]
    isEquivariant := inferInstance }

/-- Pullback reads the coordinate over the image base point. -/
@[simp]
theorem equivAt_pullback (b : B') (p : ((⇑f) *ᵖ P) b) :
    (τ.pullback f).equivAt b p = τ.equivAt (f b) p := by
  let := τ.nonempty_fibres
  -- Explicit fibre arguments let rewriting cross the Pullback type alias.
  rw [(τ.pullback f).equivAt_apply b p, τ.equivAt_apply (f b) p]
  simp only [pullback, Trivialization.pullback_apply, Pullback.lift_mk f b p]

/-- The selected section pulls back by composition on the base. -/
@[simp]
theorem sectionValue_pullback (b : B') : (τ.pullback f).sectionValue b = τ.sectionValue (f b) := by
  apply ((τ.pullback f).equivAt b).injective
  simp [τ.equivAt_pullback f b (τ.sectionValue (f b))]

/-- Pullback preserves the reference transition map. -/
@[simp]
theorem transition_pullback :
    (τ.pullback f).transition (υ.pullback f) = (τ.transition υ).comp f := by
  let := τ.nonempty_fibres
  ext b
  simp only [ContinuousMap.comp_apply, transition_eq_coordChange]
  exact τ.toTrivialization.coordChange_pullback υ.toTrivialization f (τ.mem_baseSet (f b)) 1

variable [IsTopologicalGroup G]

/-- Coordinate gauge changes commute with pullback. -/
@[simp]
theorem pullback_gauge (a : C(B, G)) :
    (τ.gauge a).pullback f = (τ.pullback f).gauge (a.comp f) := by
  ext b p
  simp [τ.equivAt_gauge a (f b) p]

end Pullback

/-- The canonical trivialization of the product principal bundle. -/
def trivial (B G : Type*) [TopologicalSpace B] [Group G] [TopologicalSpace G] :
    GlobalTrivialization G (Bundle.Trivial B G) where
  toTrivialization := Bundle.Trivial.trivialization B G
  baseSet_eq_univ := rfl
  isEquivariant := ⟨fun _ _ p g ↦ by simp only [Trivial.trivialization_apply, op_smul_eq_mul]⟩

/-- The canonical product trivialization has the identity group coordinate. -/
@[simp]
theorem equivAt_trivial (b : B) (g : G) : (trivial B G).equivAt b g = g := by
  simp [equivAt_apply, trivial, Trivial.trivialization_apply]

/-- The canonical product trivialization selects the constant identity section. -/
@[simp]
theorem sectionValue_trivial (b : B) : (trivial B G).sectionValue b = 1 := by
  simpa only [equivAt_trivial] using (trivial B G).equivAt_sectionValue b

end GlobalTrivialization

end TauCeti.PrincipalBundle
