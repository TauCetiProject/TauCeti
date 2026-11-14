/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Topology.Algebra.Group.ZPow
public import TauCeti.Topology.FiberBundle.Associated.Principal
public import TauCeti.Topology.FiberBundle.Associated.Pullback

/-!
# Extensions and reductions of the structure group of a principal bundle

For a principal `G`-bundle `P` over `B` and a continuous homomorphism `ρ : G →* H` into a group `H`
with continuous multiplication, scoping `MulAction.compHom H ρ` inside `extendCore` defines the
**extension of structure group** `TauCeti.PrincipalBundle.Extend P ρ hρ` (`P ×_ρ H`) as a principal
`H`-bundle over `B` without polluting global typeclass search, together with its universal property,
reduction recovery, functoriality, pullback, associated-bundle, and `Dual` / `ZPow` identifications.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963, Ch. I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §§10.6 and 10.12.
* D. Husemoller, *Fibre Bundles*, 3rd ed., Springer, 1994, Ch. 6, §§2–3.
-/

public section

open Bundle Filter MulOpposite Set Topology

namespace TauCeti.PrincipalBundle

private theorem compHom_continuousSMul {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [ContinuousMul H] (ρ : G →* H) (hρ : Continuous ρ) :
    letI : MulAction G H := MulAction.compHom H ρ; ContinuousSMul G H :=
  letI : MulAction G H := MulAction.compHom H ρ; ⟨(hρ.comp continuous_fst).mul continuous_snd⟩
private theorem compHom_smulCommClass {G H : Type*} [Group G] [Group H] (ρ : G →* H) :
    letI : MulAction G H := MulAction.compHom H ρ; SMulCommClass G Hᵐᵒᵖ H :=
  letI : MulAction G H := MulAction.compHom H ρ; ⟨fun _ _ _ ↦ (mul_assoc _ _ _).symm⟩
private theorem compHom_isScalarTower {G H K : Type*} [Group G] [Group H] [Group K]
    (ρ : G →* H) (σ : H →* K) :
    letI : MulAction G H := MulAction.compHom H ρ; letI : MulAction H K := MulAction.compHom K σ
    letI : MulAction G K := MulAction.compHom K (σ.comp ρ); IsScalarTower G H K :=
  letI : MulAction G H := MulAction.compHom H ρ; letI : MulAction H K := MulAction.compHom K σ
  letI : MulAction G K := MulAction.compHom K (σ.comp ρ)
  ⟨fun g h k ↦ (congrArg (· * k) (map_mul σ (ρ g) h)).trans (mul_assoc _ _ _)⟩

section Extend
section
variable {G H B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] (P : B → Type*) [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The fibre bundle core of the extension of `P` along `ρ : G →* H`, scoping
`MulAction.compHom H ρ` inside an unexposed definition. -/
noncomputable def extendCore (ρ : G →* H) (hρ : Continuous ρ) [ContinuousMul H] :
    FiberBundleCore B B H :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  associatedBundleCore G P H
@[simp] theorem extendCore_indexAt (ρ : G →* H) (hρ : Continuous ρ) [ContinuousMul H] (b : B) :
    (extendCore P ρ hρ).indexAt b = b :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  associatedBundleCore_indexAt b
@[simp] theorem extendCore_localTriv_baseSet (ρ : G →* H) (hρ : Continuous ρ) [ContinuousMul H]
    (b : B) : ((extendCore P ρ hρ).localTriv b).baseSet = (trivializationAt G P b).baseSet :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  associatedBundleCore_localTriv_baseSet b
theorem extendContinuousCoe {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] (ρ : G →* H) (hρ : Continuous ρ) : Continuous ⇑ρ := hρ
/-- The **extension of structure group** `P ×_ρ H` of a principal `G`-bundle `P` along a continuous
group homomorphism `ρ : G →* H` into a group `H` with continuous multiplication. -/
abbrev Extend (ρ : G →* H) (hρ : Continuous ρ) [ContinuousMul H] : B → Type _ :=
  (extendCore P ρ (extendContinuousCoe ρ hρ)).Fiber
end

namespace Extend
variable {G H B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]
  [PrincipalBundle G P] [ContinuousMul H]

instance instNonempty (ρ : G →* H) (hρ : Continuous ⇑ρ) (b : B) :
    Nonempty ((extendCore P ρ hρ).Fiber b) := ⟨(1 : H)⟩
instance instMulActionOp (ρ : G →* H) (hρ : Continuous ⇑ρ) (b : B) :
    MulAction Hᵐᵒᵖ ((extendCore P ρ hρ).Fiber b) := inferInstanceAs (MulAction Hᵐᵒᵖ H)
instance instPrincipalBundle (ρ : G →* H) (hρ : Continuous ⇑ρ) :
    PrincipalBundle H (extendCore P ρ hρ).Fiber :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ; AssociatedBundle.instPrincipalBundle
theorem trivializationAt_eq_localTriv (ρ : G →* H) (hρ : Continuous ρ) (b : B) :
    trivializationAt H (Extend P ρ hρ) b =
      (extendCore P ρ (extendContinuousCoe ρ hρ)).localTriv b :=
  congrArg (extendCore P ρ (extendContinuousCoe ρ hρ)).localTriv
    (extendCore_indexAt P ρ (extendContinuousCoe ρ hρ) b)
@[simp] theorem baseSet_trivializationAt (ρ : G →* H) (hρ : Continuous ρ) (b : B) :
    (trivializationAt H (Extend P ρ hρ) b).baseSet = (trivializationAt G P b).baseSet := by
  rw [trivializationAt_eq_localTriv, extendCore_localTriv_baseSet]
theorem coordChange_trivializationAt (ρ : G →* H) (hρ : Continuous ρ) {b b' x : B}
    (hb : x ∈ (trivializationAt G P b).baseSet) (hb' : x ∈ (trivializationAt G P b').baseSet)
    (h : H) : (trivializationAt H (Extend P ρ hρ) b).coordChange
        (trivializationAt H (Extend P ρ hρ) b') x h =
      ρ ((trivializationAt G P b).coordChange (trivializationAt G P b') x 1) * h :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.coordChange_trivializationAt hb hb' h
/-- The class `[p, h]` in the extended principal bundle `Extend P ρ hρ`. -/
noncomputable def mk (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (h : H) :
    Extend P ρ hρ b :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.mk G p h
theorem mk_def (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (h : H) :
    mk ρ hρ p h = (ρ (trivializationAt G P b ⟨b, p⟩).2 * h : H) :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.mk_def p h
/-- The canonical `ρ`-equivariant bundle morphism `P → Extend P ρ hρ`, sending `p` to `[p, 1]`. -/
noncomputable def inl (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) : Extend P ρ hρ b :=
  mk ρ hρ p 1
theorem inl_def (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) :
    inl ρ hρ p = mk ρ hρ p 1 := (rfl)
theorem trivializationAt_mk (ρ : G →* H) (hρ : Continuous ρ) {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (p : P b) (h : H) :
    trivializationAt H (Extend P ρ hρ) b' ⟨b, mk ρ hρ p h⟩ =
      (b, ρ (trivializationAt G P b' ⟨b, p⟩).2 * h) :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.trivializationAt_mk hb p h
theorem trivializationAt_mk_snd (ρ : G →* H) (hρ : Continuous ρ) {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (p : P b) (h : H) :
    (trivializationAt H (Extend P ρ hρ) b' ⟨b, mk ρ hρ p h⟩).2 =
      ρ (trivializationAt G P b' ⟨b, p⟩).2 * h := by rw [trivializationAt_mk ρ hρ hb]
theorem trivializationAt_inl (ρ : G →* H) (hρ : Continuous ρ) {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (p : P b) :
    trivializationAt H (Extend P ρ hρ) b' ⟨b, inl ρ hρ p⟩ =
      (b, ρ (trivializationAt G P b' ⟨b, p⟩).2) := by
  rw [inl_def, trivializationAt_mk ρ hρ hb, mul_one]
@[simp] theorem mk_smul (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (g : G) (h : H) :
    mk ρ hρ (op g • p) h = mk ρ hρ p (ρ g * h) :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.mk_smul p g h
@[simp] theorem smul_mk (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (h h' : H) :
    op h' • mk ρ hρ p h = mk ρ hρ p (h * h') :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ; AssociatedBundle.smul_mk p h h'
@[simp] theorem smul_inl (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (h : H) :
    op h • inl ρ hρ p = mk ρ hρ p h := by rw [inl_def, smul_mk, one_mul]
@[simp] theorem inl_smul (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (g : G) :
    inl ρ hρ (op g • p) = op (ρ g) • inl ρ hρ p := by rw [inl_def, mk_smul, mul_one, ← smul_inl]
theorem mk_eq_mk_iff {ρ : G →* H} {hρ : Continuous ρ} {b : B} {p q : P b} {h₁ h₂ : H} :
    mk ρ hρ p h₁ = mk ρ hρ q h₂ ↔ h₁ = ρ (division G p q) * h₂ :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.mk_eq_mk_iff
theorem mk_bijective (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) :
    Function.Bijective (mk ρ hρ p : H → Extend P ρ hρ b) :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.mk_bijective p
theorem exists_mk {ρ : G →* H} {hρ : Continuous ρ} {b : B} (z : Extend P ρ hρ b) :
    ∃ (p : P b) (h : H), mk ρ hρ p h = z :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.exists_mk z
theorem division_mk (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p q : P b) (h₁ h₂ : H) :
    division H (mk ρ hρ p h₁) (mk ρ hρ q h₂) = h₁⁻¹ * (ρ (division G p q) * h₂) :=
  division_eq_iff.2 <| by rw [smul_mk, mul_inv_cancel_left, ← mk_smul, smul_division]
@[simp] theorem division_mk_same (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p : P b) (h₁ h₂ : H) :
    division H (mk ρ hρ p h₁) (mk ρ hρ p h₂) = h₁⁻¹ * h₂ := by
  rw [division_mk, division_self, map_one, one_mul]
@[simp] theorem division_inl (ρ : G →* H) (hρ : Continuous ρ) {b : B} (p q : P b) :
    division H (inl ρ hρ p) (inl ρ hρ q) = ρ (division G p q) := by
  rw [inl_def, inl_def, division_mk, inv_one, one_mul, mul_one]
end Extend
end Extend
end TauCeti.PrincipalBundle

section ExtendContinuity
open TauCeti TauCeti.PrincipalBundle
variable {G H B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [ContinuousMul H]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {ρ : G →* H} {f : X → B} {p : ∀ x, P (f x)} {h : X → H} {s : Set X} {x₀ : X}

theorem ContinuousWithinAt.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) s x₀)
    (hh : ContinuousWithinAt h s x₀) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x))) s x₀ :=
  letI : MulAction G H := MulAction.compHom H ρ
  haveI : ContinuousSMul G H := ⟨(hρ.comp continuous_fst).mul continuous_snd⟩
  hp.totalSpaceMk_associatedBundleMk hh
theorem ContinuousAt.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) x₀) (hh : ContinuousAt h x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x))) x₀ :=
  (continuousWithinAt_univ _ _).1 <|
    hp.continuousWithinAt.totalSpaceMk_extendMk hρ hh.continuousWithinAt
theorem ContinuousOn.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (p x)) s) (hh : ContinuousOn h s) :
    ContinuousOn (fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x))) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_extendMk hρ (hh x hx)
theorem Continuous.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : Continuous fun x ↦ TotalSpace.mk' G (f x) (p x)) (hh : Continuous h) :
    Continuous fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x)) :=
  continuous_iff_continuousAt.2 fun _ ↦ hp.continuousAt.totalSpaceMk_extendMk hρ hh.continuousAt
end ExtendContinuity

namespace TauCeti.PrincipalBundle.Extend

section
variable {G H B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] [ContinuousMul H]
  (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  (ρ : G →* H) (hρ : Continuous ρ)
theorem continuous_totalSpaceMk_mk :
    Continuous fun x : TotalSpace G P × H ↦
      (⟨x.1.proj, mk ρ hρ x.1.2 x.2⟩ : TotalSpace H (Extend P ρ hρ)) :=
  Continuous.totalSpaceMk_extendMk hρ (f := fun x : TotalSpace G P × H ↦ x.1.proj)
    continuous_fst continuous_snd
theorem continuous_inl :
    Continuous fun x : TotalSpace G P ↦ (⟨x.proj, inl ρ hρ x.2⟩ : TotalSpace H (Extend P ρ hρ)) :=
  Continuous.totalSpaceMk_extendMk hρ (f := TotalSpace.proj) continuous_id continuous_const
theorem isOpenQuotientMap_totalSpaceMk_mk :
    IsOpenQuotientMap fun x : TotalSpace G P × H ↦
      (⟨x.1.proj, mk ρ hρ x.1.2 x.2⟩ : TotalSpace H (Extend P ρ hρ)) :=
  letI : MulAction G H := MulAction.compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk G P H
end

variable {G H K B B' F : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

section Reduction
variable {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q] [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q] [ContinuousMul H]

/-- **Universal property of structure-group extension.** Any `ρ`-equivariant fibrewise map
`φ : ∀ b, P b → Q b` into a principal `H`-bundle `Q` extends to an `H`-equivariant fibrewise
equivalence `Extend P ρ hρ b ≃ Q b` sending `[p, h]` to `φ b p • h`. -/
noncomputable def equivOfEquivariant (ρ : G →* H) (hρ : Continuous ρ)
    (φ : ∀ b, P b → Q b) (_hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (b : B) : Extend P ρ hρ b ≃ Q b :=
  let p₀ : P b := (FiberBundle.homeomorphAt G P b).symm 1
  (Equiv.ofBijective (mk ρ hρ p₀) (mk_bijective ρ hρ p₀)).symm.trans
    { toFun h := op h • φ b p₀
      invFun q := division H (φ b p₀) q
      left_inv h := by dsimp only; rw [division_smul_right, division_self, one_mul]
      right_inv q := smul_division (φ b p₀) q }

section
variable (ρ : G →* H) (hρ : Continuous ρ) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
@[simp] theorem equivOfEquivariant_mk {b : B} (p : P b) (h : H) :
    equivOfEquivariant ρ hρ φ hφ b (mk ρ hρ p h) = op h • φ b p := by
  set p₀ : P b := (FiberBundle.homeomorphAt G P b).symm 1
  have hp : p = op (division G p₀ p) • p₀ := (smul_division p₀ p).symm
  dsimp only [equivOfEquivariant]
  rw [hp, mk_smul, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply]
  dsimp only [Equiv.coe_fn_mk]; rw [hφ, op_mul, mul_smul]
@[simp] theorem equivOfEquivariant_inl {b : B} (p : P b) :
    equivOfEquivariant ρ hρ φ hφ b (inl ρ hρ p) = φ b p := by
  rw [inl_def, equivOfEquivariant_mk, op_one, one_smul]
@[simp] theorem equivOfEquivariant_smul (b : B) (h' : H) (z : Extend P ρ hρ b) :
    equivOfEquivariant ρ hρ φ hφ b (op h' • z) = op h' • equivOfEquivariant ρ hρ φ hφ b z := by
  obtain ⟨p, h, rfl⟩ := exists_mk z
  rw [smul_mk, equivOfEquivariant_mk, equivOfEquivariant_mk, op_mul, mul_smul]
theorem equivOfEquivariant_symm_apply_smul {b : B} (p : P b) (q : Q b) :
    (equivOfEquivariant ρ hρ φ hφ b).symm q = mk ρ hρ p (division H (φ b p) q) :=
  (equivOfEquivariant ρ hρ φ hφ b).symm_apply_eq.2 <| by rw [equivOfEquivariant_mk, smul_division]
theorem equivOfEquivariant_unique (ψ : ∀ b, Extend P ρ hρ b → Q b)
    (hψ_smul : ∀ b (h : H) z, ψ b (op h • z) = op h • ψ b z)
    (hψ_inl : ∀ b (p : P b), ψ b (inl ρ hρ p) = φ b p) (b : B) (z : Extend P ρ hρ b) :
    ψ b z = equivOfEquivariant ρ hρ φ hφ b z := by
  obtain ⟨p, h, rfl⟩ := exists_mk z
  rw [← smul_inl, hψ_smul, hψ_inl, smul_inl, equivOfEquivariant_mk]
end
end Reduction

section ReductionHomeomorph
variable {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q] [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q] [IsTopologicalGroup H]

/-- **Extending a reduction recovers the original principal bundle.** If `(P, φ)` is a continuous
`ρ`-equivariant map into a principal `H`-bundle `Q` and `H` is a topological group, then
`[p, h] ↦ φ b p • h` is an `H`-equivariant homeomorphism `Extend P ρ hρ ≃ₜ Q` over `B`. -/
noncomputable def homeomorphOfEquivariant (ρ : G →* H) (hρ : Continuous ρ)
    (φ : ∀ b, P b → Q b) (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (hφc : Continuous fun x : TotalSpace G P ↦ TotalSpace.mk' H x.proj (φ x.proj x.2)) :
    TotalSpace H (Extend P ρ hρ) ≃ₜ TotalSpace H Q where
  toFun z := ⟨z.proj, equivOfEquivariant ρ hρ φ hφ z.proj z.2⟩
  invFun q := ⟨q.proj, (equivOfEquivariant ρ hρ φ hφ q.proj).symm q.2⟩
  left_inv z := by simp
  right_inv q := by simp
  continuous_toFun := by
    rw [(isOpenQuotientMap_totalSpaceMk_mk P ρ hρ).isQuotientMap.continuous_iff]
    refine (Continuous.totalSpaceMk_smul (G := H) (P := Q)
      (f := fun x : TotalSpace G P × H ↦ x.1.proj) (p := fun x ↦ φ x.1.proj x.1.2)
      (hφc.comp continuous_fst) continuous_snd).congr fun ⟨⟨b, p⟩, h⟩ ↦
        congrArg (TotalSpace.mk b) (equivOfEquivariant_mk ρ hρ φ hφ p h).symm
  continuous_invFun := by
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
    set b₀ := q₀.proj; set eP := trivializationAt G P b₀
    have hbP₀ : b₀ ∈ eP.baseSet := mem_baseSet_trivializationAt G P b₀
    have hσ_cont : ContinuousAt (fun b ↦ TotalSpace.mk' G b (eP.symm b 1)) b₀ :=
      (ContinuousAt.comp (x := b₀)
        (eP.toOpenPartialHomeomorph.continuousAt_symm ((eP.mem_target (x := (b₀, (1 : G)))).2 hbP₀))
        (continuousAt_id.prodMk continuousAt_const)).congr_of_eventuallyEq
        (mem_of_superset (eP.open_baseSet.mem_nhds hbP₀) fun _ hb ↦ eP.mk_symm hb 1)
    have hσq : ContinuousAt (fun q : TotalSpace H Q ↦ TotalSpace.mk' G q.proj (eP.symm q.proj 1))
        q₀ := hσ_cont.comp (FiberBundle.continuous_proj H Q).continuousAt
    refine (hσq.totalSpaceMk_extendMk hρ
      ((hφc.continuousAt.comp hσq).division (f := TotalSpace.proj) (q := fun q ↦ q.2)
        continuousAt_id)).congr_of_eventuallyEq
      (Eventually.of_forall fun ⟨b, y⟩ ↦
        congrArg (TotalSpace.mk b) (equivOfEquivariant_symm_apply_smul ρ hρ φ hφ (eP.symm b 1) y))

section
variable (ρ : G →* H) (hρ : Continuous ρ) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : Continuous fun x : TotalSpace G P ↦ TotalSpace.mk' H x.proj (φ x.proj x.2))
theorem homeomorphOfEquivariant_apply (z : TotalSpace H (Extend P ρ hρ)) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc z =
      ⟨z.proj, equivOfEquivariant ρ hρ φ hφ z.proj z.2⟩ := (rfl)
@[simp] theorem homeomorphOfEquivariant_proj (z : TotalSpace H (Extend P ρ hρ)) :
    (homeomorphOfEquivariant ρ hρ φ hφ hφc z).proj = z.proj := (rfl)
@[simp] theorem homeomorphOfEquivariant_mk {b : B} (p : P b) (h : H) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc ⟨b, mk ρ hρ p h⟩ = ⟨b, op h • φ b p⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_mk ρ hρ φ hφ p h)
@[simp] theorem homeomorphOfEquivariant_inl {b : B} (p : P b) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc ⟨b, inl ρ hρ p⟩ = ⟨b, φ b p⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_inl ρ hρ φ hφ p)
@[simp] theorem homeomorphOfEquivariant_smul (h' : H) (z : TotalSpace H (Extend P ρ hρ)) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc (op h' • z) =
      op h' • homeomorphOfEquivariant ρ hρ φ hφ hφc z :=
  congrArg (TotalSpace.mk z.proj) (equivOfEquivariant_smul ρ hρ φ hφ z.proj h' z.2)
end
end ReductionHomeomorph

section Congr
variable [ContinuousMul H] {ρ₁ ρ₂ : G →* H}
/-- Equal homomorphisms produce canonically equivalent extended fibres. -/
noncomputable def congrEquiv (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) (b : B) :
    Extend P ρ₁ hρ₁ b ≃ Extend P ρ₂ hρ₂ b := h ▸ Equiv.refl _
@[simp] theorem congrEquiv_mk (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) {b : B}
    (p : P b) (x : H) : congrEquiv h hρ₁ hρ₂ b (mk ρ₁ hρ₁ p x) = mk ρ₂ hρ₂ p x := by subst h; rfl
@[simp] theorem congrEquiv_symm (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) (b : B) :
    (congrEquiv (P := P) h hρ₁ hρ₂ b).symm = congrEquiv h.symm hρ₂ hρ₁ b := by subst h; rfl
@[simp] theorem congrEquiv_smul (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) (b : B)
    (x : H) (z : Extend P ρ₁ hρ₁ b) :
    congrEquiv h hρ₁ hρ₂ b (op x • z) = op x • congrEquiv h hρ₁ hρ₂ b z := by subst h; rfl
theorem trivializationAt_congrEquiv_snd (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
    (b' b : B) (z : Extend P ρ₁ hρ₁ b) :
    (trivializationAt H (Extend P ρ₁ hρ₁) b' ⟨b, z⟩).2 =
      (trivializationAt H (Extend P ρ₂ hρ₂) b' ⟨b, congrEquiv h hρ₁ hρ₂ b z⟩).2 := by subst h; rfl
/-- Equal homomorphisms produce canonically homeomorphic extended total spaces. -/
noncomputable def congrHomeomorph (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) :
    TotalSpace H (Extend P ρ₁ hρ₁) ≃ₜ TotalSpace H (Extend P ρ₂ hρ₂) := h ▸ Homeomorph.refl _
@[simp] theorem congrHomeomorph_apply (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
    (z : TotalSpace H (Extend P ρ₁ hρ₁)) :
    congrHomeomorph h hρ₁ hρ₂ z = ⟨z.proj, congrEquiv h hρ₁ hρ₂ z.proj z.2⟩ := by subst h; rfl
@[simp] theorem congrHomeomorph_symm (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) :
    (congrHomeomorph (P := P) h hρ₁ hρ₂).symm = congrHomeomorph h.symm hρ₂ hρ₁ := by subst h; rfl
end Congr

section Id
variable [ContinuousMul G]
/-- Extending `P` along `MonoidHom.id G` recovers the fibres of `P`, sending `[p, g]` to `p • g`. -/
noncomputable def idEquiv (b : B) : Extend P (MonoidHom.id G) continuous_id b ≃ P b :=
  equivOfEquivariant (MonoidHom.id G) continuous_id (fun _ p ↦ p) (fun _ _ _ ↦ rfl) b
@[simp] theorem idEquiv_mk {b : B} (p : P b) (g : G) :
    idEquiv b (mk (MonoidHom.id G) continuous_id p g) = op g • p :=
  equivOfEquivariant_mk (MonoidHom.id G) continuous_id (fun _ p ↦ p) (fun _ _ _ ↦ rfl) p g
@[simp] theorem idEquiv_inl {b : B} (p : P b) :
    idEquiv b (inl (MonoidHom.id G) continuous_id p) = p :=
  equivOfEquivariant_inl (MonoidHom.id G) continuous_id (fun _ p ↦ p) (fun _ _ _ ↦ rfl) p
@[simp] theorem idEquiv_symm_apply {b : B} (p : P b) :
    (idEquiv b).symm p = inl (MonoidHom.id G) continuous_id p :=
  (idEquiv b).symm_apply_eq.2 (idEquiv_inl p).symm
@[simp] theorem idEquiv_smul (b : B) (g : G) (z : Extend P (MonoidHom.id G) continuous_id b) :
    idEquiv b (op g • z) = op g • idEquiv b z :=
  equivOfEquivariant_smul (MonoidHom.id G) continuous_id (fun _ p ↦ p) (fun _ _ _ ↦ rfl) b g z
theorem trivializationAt_idEquiv_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (z : Extend P (MonoidHom.id G) continuous_id b) :
    (trivializationAt G (Extend P (MonoidHom.id G) continuous_id) b' ⟨b, z⟩).2 =
      (trivializationAt G P b' ⟨b, idEquiv b z⟩).2 := by
  obtain ⟨p, g, rfl⟩ := exists_mk z
  rw [idEquiv_mk, trivializationAt_mk_snd (MonoidHom.id G) continuous_id hb,
    (trivializationAt G P b').snd_apply_smul hb, MonoidHom.id_apply]
/-- **Extension along the identity homomorphism.** `Extend P (MonoidHom.id G) continuous_id` is
canonically homeomorphic to `P` over `B`. -/
noncomputable def idHomeomorph :
    TotalSpace G (Extend P (MonoidHom.id G) continuous_id) ≃ₜ TotalSpace G P where
  toFun z := ⟨z.proj, idEquiv z.proj z.2⟩
  invFun z := ⟨z.proj, (idEquiv z.proj).symm z.2⟩
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun z₀ ↦
      (FiberBundle.continuousAt_totalSpace G
        (fun z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id) ↦
          TotalSpace.mk' G z.proj (idEquiv z.proj z.2))).2
        ⟨(FiberBundle.continuous_proj G _).continuousAt, ?_⟩
    have hb₀ := mem_baseSet_trivializationAt G P z₀.proj
    have hbE₀ : z₀.proj ∈
        (trivializationAt G (Extend P (MonoidHom.id G) continuous_id) z₀.proj).baseSet :=
      (baseSet_trivializationAt (P := P) (MonoidHom.id G) continuous_id z₀.proj).symm ▸ hb₀
    refine (((trivializationAt G (Extend P (MonoidHom.id G) continuous_id) z₀.proj).continuousAt
      ((Trivialization.mem_source _).2 hbE₀)).snd).congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj G _).continuousAt.preimage_mem_nhds
      ((trivializationAt G P z₀.proj).open_baseSet.mem_nhds hb₀)] with z hz
    exact (trivializationAt_idEquiv_snd hz z.2).symm
  continuous_invFun := (continuous_inl P (MonoidHom.id G) continuous_id).congr fun ⟨b, p⟩ ↦
    congrArg (TotalSpace.mk b) (idEquiv_symm_apply (G := G) p).symm
theorem idHomeomorph_apply (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    idHomeomorph z = ⟨z.proj, idEquiv z.proj z.2⟩ := (rfl)
theorem idHomeomorph_symm_apply (z : TotalSpace G P) :
    (idHomeomorph (G := G) (P := P)).symm z = ⟨z.proj, inl (MonoidHom.id G) continuous_id z.2⟩ :=
  congrArg (TotalSpace.mk z.proj) (idEquiv_symm_apply (G := G) z.2)
@[simp] theorem idHomeomorph_proj (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    (idHomeomorph z).proj = z.proj := (rfl)
@[simp] theorem idHomeomorph_mk {b : B} (p : P b) (g : G) :
    idHomeomorph ⟨b, mk (MonoidHom.id G) continuous_id p g⟩ = ⟨b, op g • p⟩ :=
  congrArg (TotalSpace.mk b) (idEquiv_mk p g)
end Id

section Comp
variable [ContinuousMul H] [ContinuousMul K]
  (ρ : G →* H) (hρ : Continuous ρ) (σ : H →* K) (hσ : Continuous σ)
/-- Extending along `ρ : G →* H` and then along `σ : H →* K` is fibrewise equivalent to extending
along `σ.comp ρ`, sending `[[p, h], k]` to `[p, σ h * k]`. -/
noncomputable def compEquiv (b : B) :
    Extend (Extend P ρ hρ) σ hσ b ≃ Extend P (σ.comp ρ) (hσ.comp hρ) b :=
  letI : MulAction G H := .compHom H ρ; letI : MulAction H K := .compHom K σ
  letI : MulAction G K := .compHom K (σ.comp ρ); haveI := compHom_smulCommClass ρ
  haveI := compHom_continuousSMul ρ hρ; haveI := compHom_continuousSMul σ hσ
  haveI := compHom_continuousSMul (σ.comp ρ) (hσ.comp hρ)
  AssociatedBundle.assocEquiv (G := G) (P := P) (H := H) (F := K) b
@[simp] theorem compEquiv_mk {b : B} (p : P b) (h : H) (k : K) :
    compEquiv ρ hρ σ hσ b (mk σ hσ (mk ρ hρ p h) k) = mk (σ.comp ρ) (hσ.comp hρ) p (σ h * k) :=
  letI : MulAction G H := .compHom H ρ; letI : MulAction H K := .compHom K σ
  letI : MulAction G K := .compHom K (σ.comp ρ); haveI := compHom_smulCommClass ρ
  haveI := compHom_continuousSMul ρ hρ; haveI := compHom_continuousSMul σ hσ
  haveI := compHom_continuousSMul (σ.comp ρ) (hσ.comp hρ); haveI := compHom_isScalarTower ρ σ
  AssociatedBundle.assocEquiv_mk p h k
@[simp] theorem compEquiv_symm_mk {b : B} (p : P b) (k : K) :
    (compEquiv ρ hρ σ hσ b).symm (mk (σ.comp ρ) (hσ.comp hρ) p k) = mk σ hσ (inl ρ hρ p) k :=
  (compEquiv ρ hρ σ hσ b).symm_apply_eq.2 (by rw [inl_def, compEquiv_mk, map_one, one_mul])
@[simp] theorem compEquiv_smul (b : B) (k' : K) (z : Extend (Extend P ρ hρ) σ hσ b) :
    compEquiv ρ hρ σ hσ b (op k' • z) = op k' • compEquiv ρ hρ σ hσ b z := by
  obtain ⟨u, k, rfl⟩ := exists_mk z; obtain ⟨p, h, rfl⟩ := exists_mk u
  rw [smul_mk, compEquiv_mk, compEquiv_mk, smul_mk, mul_assoc]
theorem trivializationAt_compEquiv_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (z : Extend (Extend P ρ hρ) σ hσ b) :
    (trivializationAt K (Extend (Extend P ρ hρ) σ hσ) b' ⟨b, z⟩).2 =
      (trivializationAt K (Extend P (σ.comp ρ) (hσ.comp hρ)) b'
        ⟨b, compEquiv ρ hρ σ hσ b z⟩).2 := by
  obtain ⟨u, k, rfl⟩ := exists_mk z; obtain ⟨p, h, rfl⟩ := exists_mk u
  have hbH : b ∈ (trivializationAt H (Extend P ρ hρ) b').baseSet :=
    (baseSet_trivializationAt (P := P) ρ hρ b').symm ▸ hb
  rw [compEquiv_mk, trivializationAt_mk_snd σ hσ hbH, trivializationAt_mk_snd ρ hρ hb,
    trivializationAt_mk_snd (σ.comp ρ) (hσ.comp hρ) hb, MonoidHom.comp_apply, map_mul, mul_assoc]
/-- **Functoriality of structure-group extension under composition.** -/
noncomputable def compHomeomorph :
    TotalSpace K (Extend (Extend P ρ hρ) σ hσ) ≃ₜ
      TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ)) :=
  letI : MulAction G H := .compHom H ρ; letI : MulAction H K := .compHom K σ
  letI : MulAction G K := .compHom K (σ.comp ρ); haveI := compHom_smulCommClass ρ
  haveI := compHom_continuousSMul ρ hρ; haveI := compHom_continuousSMul σ hσ
  haveI := compHom_continuousSMul (σ.comp ρ) (hσ.comp hρ); haveI := compHom_isScalarTower ρ σ
  AssociatedBundle.assocHomeomorph (G := G) (P := P) (H := H) (F := K)
theorem compHomeomorph_apply (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    compHomeomorph ρ hρ σ hσ z = ⟨z.proj, compEquiv ρ hρ σ hσ z.proj z.2⟩ :=
  letI : MulAction G H := .compHom H ρ; letI : MulAction H K := .compHom K σ
  letI : MulAction G K := .compHom K (σ.comp ρ); haveI := compHom_smulCommClass ρ
  haveI := compHom_continuousSMul ρ hρ; haveI := compHom_continuousSMul σ hσ
  haveI := compHom_continuousSMul (σ.comp ρ) (hσ.comp hρ); haveI := compHom_isScalarTower ρ σ
  AssociatedBundle.assocHomeomorph_apply z
theorem compHomeomorph_symm_apply (z : TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (compHomeomorph (P := P) ρ hρ σ hσ).symm z =
      ⟨z.proj, (compEquiv ρ hρ σ hσ z.proj).symm z.2⟩ :=
  (compHomeomorph ρ hρ σ hσ).symm_apply_eq.2 <| by rw [compHomeomorph_apply, Equiv.apply_symm_apply]
@[simp] theorem compHomeomorph_proj (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    (compHomeomorph ρ hρ σ hσ z).proj = z.proj := by rw [compHomeomorph_apply]
@[simp] theorem compHomeomorph_mk {b : B} (p : P b) (h : H) (k : K) :
    compHomeomorph ρ hρ σ hσ ⟨b, mk σ hσ (mk ρ hρ p h) k⟩ =
      ⟨b, mk (σ.comp ρ) (hσ.comp hρ) p (σ h * k)⟩ := by rw [compHomeomorph_apply, compEquiv_mk]
end Comp

section Pullback
variable [∀ b, Nonempty (P b)] [ContinuousMul H]
  {M : Type*} [FunLike M B' B] [ContinuousMapClass M B' B] (f : M) (ρ : G →* H) (hρ : Continuous ρ)
/-- Fibrewise equivalence between extending `f *ᵖ P` along `ρ` and pulling back `Extend P ρ hρ`. -/
noncomputable def pullbackEquiv (x : B') :
    Extend ((f : B' → B) *ᵖ P) ρ hρ x ≃ ((f : B' → B) *ᵖ (Extend P ρ hρ)) x :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.pullbackEquiv (G := G) (P := P) (F := H) f x
@[simp] theorem pullbackEquiv_mk (x : B') (p : P (f x)) (h : H) :
    pullbackEquiv f ρ hρ x (mk (P := (f : B' → B) *ᵖ P) ρ hρ p h) = mk (P := P) ρ hρ p h :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.pullbackEquiv_mk f x p h
@[simp] theorem pullbackEquiv_symm_mk (x : B') (p : P (f x)) (h : H) :
    (pullbackEquiv f ρ hρ x).symm (mk (P := P) ρ hρ p h) = mk (P := (f : B' → B) *ᵖ P) ρ hρ p h :=
  (pullbackEquiv f ρ hρ x).symm_apply_eq.2 (pullbackEquiv_mk f ρ hρ x p h).symm
@[simp] theorem pullbackEquiv_smul (x : B') (h' : H) (z : Extend ((f : B' → B) *ᵖ P) ρ hρ x) :
    pullbackEquiv f ρ hρ x (op h' • z) = op h' • pullbackEquiv f ρ hρ x z := by
  obtain ⟨p, h, rfl⟩ := exists_mk z
  rw [smul_mk (P := (f : B' → B) *ᵖ P), pullbackEquiv_mk f ρ hρ x p (h * h'),
    pullbackEquiv_mk f ρ hρ x p h, ← smul_mk (P := P) ρ hρ p h h']; rfl
theorem trivializationAt_pullbackEquiv_snd {x₀ x : B'}
    (hx : f x ∈ (trivializationAt G P (f x₀)).baseSet) (z : Extend ((f : B' → B) *ᵖ P) ρ hρ x) :
    (trivializationAt H (Extend ((f : B' → B) *ᵖ P) ρ hρ) x₀ ⟨x, z⟩).2 =
      (trivializationAt H (Extend P ρ hρ) (f x₀) ⟨f x, pullbackEquiv f ρ hρ x z⟩).2 :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.trivializationAt_pullbackEquiv_snd f hx z
/-- **Extension of structure group commutes with pullback.** -/
noncomputable def pullbackHomeomorph :
    TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ) ≃ₜ
      TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ)) :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.pullbackHomeomorph (G := G) (P := P) (F := H) f
theorem pullbackHomeomorph_apply (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    pullbackHomeomorph f ρ hρ z = ⟨z.proj, pullbackEquiv f ρ hρ z.proj z.2⟩ :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  AssociatedBundle.pullbackHomeomorph_apply f z
theorem pullbackHomeomorph_symm_apply (z : TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (pullbackHomeomorph (P := P) f ρ hρ).symm z =
      ⟨z.proj, (pullbackEquiv f ρ hρ z.proj).symm z.2⟩ :=
  (pullbackHomeomorph f ρ hρ).symm_apply_eq.2 <| by
    rw [pullbackHomeomorph_apply, Equiv.apply_symm_apply]
@[simp] theorem pullbackHomeomorph_proj (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    (pullbackHomeomorph f ρ hρ z).proj = z.proj := by rw [pullbackHomeomorph_apply]
@[simp] theorem pullbackHomeomorph_mk (x : B') (p : P (f x)) (h : H) :
    pullbackHomeomorph f ρ hρ ⟨x, mk (P := (f : B' → B) *ᵖ P) ρ hρ p h⟩ =
      ⟨x, mk (P := P) ρ hρ p h⟩ := by rw [pullbackHomeomorph_apply, pullbackEquiv_mk]
end Pullback

section Associated
variable [ContinuousMul H] [TopologicalSpace F]
  [MulAction H F] [ContinuousSMul H F] [MulAction G F] [ContinuousSMul G F]
/-- Fibrewise equivalence `(Extend P ρ hρ) ×_H F ≃ P ×_G F` when `G` acts on `F` through `ρ`. -/
noncomputable def associatedEquiv (ρ : G →* H) (hρ : Continuous ρ)
    (_hF : ∀ (g : G) (v : F), g • v = ρ g • v) (b : B) :
    AssociatedBundle H (Extend P ρ hρ) F b ≃ AssociatedBundle G P F b :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ; AssociatedBundle.assocEquiv (G := G) (P := P) b
/-- **Associated bundle of an extended principal bundle.** `(P ×_ρ H) ×_H F` is canonically
homeomorphic over `B` to `P ×_G F` when `G` acts on `F` through `ρ`. -/
noncomputable def associatedHomeomorph (ρ : G →* H) (hρ : Continuous ρ)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) :
    TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F) ≃ₜ TotalSpace F (AssociatedBundle G P F) :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.assocHomeomorph (G := G) (P := P) (H := H) (F := F)
section
variable (ρ : G →* H) (hρ : Continuous ρ) (hF : ∀ (g : G) (v : F), g • v = ρ g • v)
@[simp] theorem associatedEquiv_mk {b : B} (p : P b) (h : H) (v : F) :
    associatedEquiv ρ hρ hF b (AssociatedBundle.mk H (mk ρ hρ p h) v) =
      AssociatedBundle.mk G p (h • v) :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.assocEquiv_mk p h v
@[simp] theorem associatedEquiv_symm_mk {b : B} (p : P b) (v : F) :
    (associatedEquiv ρ hρ hF b).symm (AssociatedBundle.mk G p v) =
      AssociatedBundle.mk H (inl ρ hρ p) v :=
  (associatedEquiv ρ hρ hF b).symm_apply_eq.2 (by rw [inl_def, associatedEquiv_mk, one_smul])
theorem trivializationAt_associatedEquiv_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (z : AssociatedBundle H (Extend P ρ hρ) F b) :
    (trivializationAt F (AssociatedBundle H (Extend P ρ hρ) F) b' ⟨b, z⟩).2 =
      (trivializationAt F (AssociatedBundle G P F) b' ⟨b, associatedEquiv ρ hρ hF b z⟩).2 :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.trivializationAt_assocEquiv_snd hb z
theorem associatedHomeomorph_apply (z : TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F)) :
    associatedHomeomorph ρ hρ hF z = ⟨z.proj, associatedEquiv ρ hρ hF z.proj z.2⟩ :=
  letI : MulAction G H := .compHom H ρ; haveI := compHom_continuousSMul ρ hρ
  haveI := compHom_smulCommClass ρ
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.assocHomeomorph_apply z
theorem associatedHomeomorph_symm_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    (associatedHomeomorph (P := P) ρ hρ hF).symm z =
      ⟨z.proj, (associatedEquiv ρ hρ hF z.proj).symm z.2⟩ :=
  (associatedHomeomorph ρ hρ hF).symm_apply_eq.2 <| by
    rw [associatedHomeomorph_apply, Equiv.apply_symm_apply]
@[simp] theorem associatedHomeomorph_mk {b : B} (p : P b) (h : H) (v : F) :
    associatedHomeomorph ρ hρ hF ⟨b, AssociatedBundle.mk H (mk ρ hρ p h) v⟩ =
      ⟨b, AssociatedBundle.mk G p (h • v)⟩ := by rw [associatedHomeomorph_apply, associatedEquiv_mk]
end
end Associated

section CommGroup
variable (A : Type*) {B : Type*} [TopologicalSpace B] [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] (Q : B → Type*) [TopologicalSpace (TotalSpace A Q)]
  [∀ b, TopologicalSpace (Q b)] [FiberBundle A Q] [∀ b, MulAction Aᵐᵒᵖ (Q b)] [PrincipalBundle A Q]
/-- The **dual principal bundle** `Q∨` of `Q` (extension along `invMonoidHom`). -/
abbrev Dual : B → Type _ := Extend Q (invMonoidHom : A →* A) continuous_inv
/-- The **`k`-th power principal bundle** `Q^⊗k` of `Q` (extension along `zpowGroupHom k`). -/
abbrev ZPow (k : ℤ) : B → Type _ := Extend Q (zpowGroupHom k : A →* A) (continuous_zpow k)
/-- Taking the dual bundle twice recovers `Q` up to canonical homeomorphism over `B`. -/
noncomputable def dualDualHomeomorph : TotalSpace A (Dual A (Dual A Q)) ≃ₜ TotalSpace A Q :=
  (compHomeomorph (G := A) (P := Q) (invMonoidHom : A →* A) continuous_inv
      (invMonoidHom : A →* A) continuous_inv).trans <|
    (congrHomeomorph (G := A) (P := Q) invMonoidHom_comp_invMonoidHom
      (continuous_inv.comp continuous_inv) continuous_id).trans idHomeomorph
/-- Extending by `k`-th and then `l`-th powers is homeomorphic to `(k * l)`-th powers. -/
noncomputable def zpowMulHomeomorph (k l : ℤ) :
    TotalSpace A (ZPow A (ZPow A Q k) l) ≃ₜ TotalSpace A (ZPow A Q (k * l)) :=
  (compHomeomorph (G := A) (P := Q) (zpowGroupHom k : A →* A) (continuous_zpow k)
      (zpowGroupHom l : A →* A) (continuous_zpow l)).trans <|
    congrHomeomorph (G := A) (P := Q) (by ext a; simp [zpow_mul])
      ((continuous_zpow l).comp (continuous_zpow k)) (continuous_zpow (k * l))
/-- `ZPow A Q (-1)` is canonically homeomorphic to `Dual A Q`. -/
noncomputable def zpowNegOneHomeomorph : TotalSpace A (ZPow A Q (-1)) ≃ₜ TotalSpace A (Dual A Q) :=
  congrHomeomorph (G := A) (P := Q) (by ext a; simp) (continuous_zpow (-1)) continuous_inv
/-- Extending `Q` along the diagonal and `mulMonoidHom` is homeomorphic to `ZPow A Q 2`. -/
noncomputable def diagMulZPowTwoHomeomorph :
    TotalSpace A
        (Extend (Extend Q (MonoidHom.prod (.id A) (.id A)) (continuous_id.prodMk continuous_id))
          (mulMonoidHom : A × A →* A) continuous_mul) ≃ₜ TotalSpace A (ZPow A Q 2) :=
  (compHomeomorph (G := A) (P := Q) (MonoidHom.prod (.id A) (.id A))
      (continuous_id.prodMk continuous_id) (mulMonoidHom : A × A →* A) continuous_mul).trans <|
    congrHomeomorph (G := A) (P := Q) (by ext a; simp [sq])
      (continuous_mul.comp (continuous_id.prodMk continuous_id)) (continuous_zpow 2)
end CommGroup

end TauCeti.PrincipalBundle.Extend
