/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Principal
public import TauCeti.Topology.FiberBundle.Associated.Pullback

/-!
# Extension of the structure group of a principal bundle

Given a principal `G`-bundle `P` over `B` and a continuous group homomorphism `ρ : G →* H` into a
group `H` with continuous multiplication, the **extension of structure group**
`TauCeti.PrincipalBundle.Extend P ρ hρ` (written `P ×_ρ H`) is the principal `H`-bundle obtained as
the quotient of `P × H` by `(p • g, h) ∼ (p, ρ g * h)`, with transition cocycle `ρ ∘ c` where `c`
is the transition cocycle of `P`. It is built from an unexposed core `extendCore` so that
`MulAction.compHom H ρ` stays out of global typeclass search.

We establish the canonical `ρ`-equivariant map `inl : P → Extend P ρ hρ`, the universal property
and comparison with any principal `H`-bundle receiving a `ρ`-equivariant map from `P`
(`equivOfEquivariant`, `equivOfEquivariant_unique`, `homeomorphOfEquivariant`), congruence along
equal homomorphisms (`congrHomeomorph`), functoriality under identity and composition
(`idHomeomorph`, `compHomeomorph`), compatibility with pullback (`pullbackHomeomorph`), and
identification of associated bundles `(P ×_ρ H) ×_H F ≃ₜ P ×_G F` (`associatedHomeomorph`).

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963, Ch. I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §§10.6 and 10.12.
* D. Husemoller, *Fibre Bundles*, 3rd ed., Springer, 1994, Ch. 6, §§2–3.
-/

public section

open Bundle Filter MulAction MulOpposite Set Topology

namespace TauCeti.PrincipalBundle

section Extend
section
variable {G H B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] (P : B → Type*) [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  (ρ : G →* H) (hρ : Continuous ρ) [ContinuousMul H]

/-- The fibre bundle core of the extension of `P` along `ρ : G →* H`, scoping
`MulAction.compHom H ρ` inside an unexposed definition. -/
noncomputable def extendCore : FiberBundleCore B B H :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  associatedBundleCore G P H

/-- The preferred chart index of `extendCore P ρ hρ` at `b` is `b`. -/
@[simp] theorem extendCore_indexAt (b : B) : (extendCore P ρ hρ).indexAt b = b :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  associatedBundleCore_indexAt b

/-- The base set of chart `b` of `extendCore P ρ hρ` is that of `trivializationAt G P b`. -/
@[simp] theorem extendCore_localTriv_baseSet (b : B) :
    ((extendCore P ρ hρ).localTriv b).baseSet = (trivializationAt G P b).baseSet :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  associatedBundleCore_localTriv_baseSet b

/-- The **extension of structure group** `P ×_ρ H` of a principal `G`-bundle `P` along a continuous
group homomorphism `ρ : G →* H` into a group `H` with continuous multiplication. -/
abbrev Extend : B → Type _ := (extendCore P ρ hρ).Fiber
end

namespace Extend
variable {G H B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]
  [PrincipalBundle G P] [ContinuousMul H]

/-- Every fibre of `(extendCore P ρ hρ).Fiber` is nonempty, containing the identity coordinate. -/
instance instNonempty (ρ : G →* H) (hρ : Continuous ⇑ρ) (b : B) :
    Nonempty ((extendCore P ρ hρ).Fiber b) := ⟨(1 : H)⟩

/-- Each fibre of `(extendCore P ρ hρ).Fiber` carries the right-multiplication action of `H`. -/
instance instMulActionOp (ρ : G →* H) (hρ : Continuous ⇑ρ) (b : B) :
    MulAction Hᵐᵒᵖ ((extendCore P ρ hρ).Fiber b) := inferInstanceAs (MulAction Hᵐᵒᵖ H)

/-- The extension `Extend P ρ hρ` of a principal `G`-bundle along `ρ : G →* H` is a principal
`H`-bundle. -/
instance instPrincipalBundle (ρ : G →* H) (hρ : Continuous ⇑ρ) :
    PrincipalBundle H (extendCore P ρ hρ).Fiber :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  AssociatedBundle.instPrincipalBundle

section
variable (ρ : G →* H) (hρ : Continuous ρ)

/-- Preferred trivializations of `Extend P ρ hρ` agree with the native charts of `extendCore`. -/
theorem trivializationAt_eq_localTriv (b : B) :
    trivializationAt H (Extend P ρ hρ) b = (extendCore P ρ hρ).localTriv b :=
  congrArg (extendCore P ρ hρ).localTriv (extendCore_indexAt P ρ hρ b)
/-- The base set of `trivializationAt H (Extend P ρ hρ) b` agrees with `trivializationAt G P b`. -/
@[simp] theorem baseSet_trivializationAt (b : B) :
    (trivializationAt H (Extend P ρ hρ) b).baseSet = (trivializationAt G P b).baseSet := by
  rw [trivializationAt_eq_localTriv, extendCore_localTriv_baseSet]
/-- On overlaps of preferred charts, the transition function of `Extend P ρ hρ` is `ρ` applied to
the transition function of `P`. -/
theorem coordChange_trivializationAt {b b' x : B}
    (hb : x ∈ (trivializationAt G P b).baseSet) (hb' : x ∈ (trivializationAt G P b').baseSet)
    (h : H) : (trivializationAt H (Extend P ρ hρ) b).coordChange
        (trivializationAt H (Extend P ρ hρ) b') x h =
      ρ ((trivializationAt G P b).coordChange (trivializationAt G P b') x 1) * h :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.coordChange_trivializationAt hb hb' h

/-- The class `[p, h]` in the extended principal bundle `Extend P ρ hρ`. -/
noncomputable def mk {b : B} (p : P b) (h : H) : Extend P ρ hρ b :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.mk G p h
/-- Explicit fibre coordinate of `Extend.mk ρ hρ p h` in the preferred chart at `b`. -/
theorem mk_def {b : B} (p : P b) (h : H) :
    mk ρ hρ p h = (ρ (trivializationAt G P b ⟨b, p⟩).2 * h : H) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.mk_def p h
/-- The canonical `ρ`-equivariant bundle morphism `P → Extend P ρ hρ`, sending `p` to `[p, 1]`. -/
noncomputable def inl {b : B} (p : P b) : Extend P ρ hρ b := mk ρ hρ p 1
/-- Unfolding `Extend.inl ρ hρ p` as `Extend.mk ρ hρ p 1`. -/
theorem inl_def {b : B} (p : P b) : inl ρ hρ p = mk ρ hρ p 1 := (rfl)
/-- Evaluating the preferred trivialization of `Extend P ρ hρ` on `[p, h]`. -/
theorem trivializationAt_mk {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (p : P b) (h : H) :
    trivializationAt H (Extend P ρ hρ) b' ⟨b, mk ρ hρ p h⟩ =
      (b, ρ (trivializationAt G P b' ⟨b, p⟩).2 * h) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.trivializationAt_mk hb p h
/-- The fibre coordinate of `[p, h]` in the preferred trivialization of `Extend P ρ hρ`. -/
theorem trivializationAt_mk_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (p : P b) (h : H) :
    (trivializationAt H (Extend P ρ hρ) b' ⟨b, mk ρ hρ p h⟩).2 =
      ρ (trivializationAt G P b' ⟨b, p⟩).2 * h := by rw [trivializationAt_mk ρ hρ hb]
/-- Evaluating the preferred trivialization of `Extend P ρ hρ` on `inl ρ hρ p = [p, 1]`. -/
theorem trivializationAt_inl {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet) (p : P b) :
    trivializationAt H (Extend P ρ hρ) b' ⟨b, inl ρ hρ p⟩ =
      (b, ρ (trivializationAt G P b' ⟨b, p⟩).2) := by
  rw [inl_def, trivializationAt_mk ρ hρ hb, mul_one]

/-- Quotient relation on `Extend P ρ hρ`: `[p • g, h] = [p, ρ g * h]`. -/
@[simp] theorem mk_smul {b : B} (p : P b) (g : G) (h : H) :
    mk ρ hρ (op g • p) h = mk ρ hρ p (ρ g * h) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.mk_smul p g h
/-- Right multiplication by `h'` on `Extend P ρ hρ`: `[p, h] • h' = [p, h * h']`. -/
@[simp] theorem smul_mk {b : B} (p : P b) (h h' : H) :
    op h' • mk ρ hρ p h = mk ρ hρ p (h * h') :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  AssociatedBundle.smul_mk p h h'
/-- Acting on `inl ρ hρ p = [p, 1]` on the right by `h` produces `[p, h]`. -/
@[simp] theorem smul_inl {b : B} (p : P b) (h : H) :
    op h • inl ρ hρ p = mk ρ hρ p h := by rw [inl_def, smul_mk, one_mul]
/-- The canonical map `inl ρ hρ : P → Extend P ρ hρ` is `ρ`-equivariant. -/
@[simp] theorem inl_smul {b : B} (p : P b) (g : G) :
    inl ρ hρ (op g • p) = op (ρ g) • inl ρ hρ p := by rw [inl_def, mk_smul, mul_one, ← smul_inl]

/-- Fixing `p : P b`, the map `h ↦ [p, h]` is a bijection `H → Extend P ρ hρ b`. -/
theorem mk_bijective {b : B} (p : P b) : Function.Bijective (mk ρ hρ p : H → Extend P ρ hρ b) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.mk_bijective p
/-- Principal `H`-division on `Extend P ρ hρ` in terms of `division G` on `P`. -/
theorem division_mk {b : B} (p q : P b) (h₁ h₂ : H) :
    division H (mk ρ hρ p h₁) (mk ρ hρ q h₂) = h₁⁻¹ * (ρ (division G p q) * h₂) :=
  division_eq_iff.2 <| by rw [smul_mk, mul_inv_cancel_left, ← mk_smul, smul_division]
/-- Principal `H`-division between two classes with the same `P`-representative. -/
@[simp] theorem division_mk_same {b : B} (p : P b) (h₁ h₂ : H) :
    division H (mk ρ hρ p h₁) (mk ρ hρ p h₂) = h₁⁻¹ * h₂ := by
  rw [division_mk, division_self, map_one, one_mul]
/-- Principal `H`-division between images of `inl` is `ρ` applied to `division G`. -/
@[simp] theorem division_inl {b : B} (p q : P b) :
    division H (inl ρ hρ p) (inl ρ hρ q) = ρ (division G p q) := by
  rw [inl_def, inl_def, division_mk, inv_one, one_mul, mul_one]
end

/-- Two representatives `[p, h₁]` and `[q, h₂]` define the same point of `Extend P ρ hρ` iff
`h₁ = ρ (division G p q) * h₂`. -/
theorem mk_eq_mk_iff {ρ : G →* H} {hρ : Continuous ρ} {b : B} {p q : P b} {h₁ h₂ : H} :
    mk ρ hρ p h₁ = mk ρ hρ q h₂ ↔ h₁ = ρ (division G p q) * h₂ :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.mk_eq_mk_iff
/-- Every element of a fibre `Extend P ρ hρ b` has a representative `[p, h]`. -/
theorem exists_mk {ρ : G →* H} {hρ : Continuous ρ} {b : B} (z : Extend P ρ hρ b) :
    ∃ (p : P b) (h : H), mk ρ hρ p h = z :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.exists_mk z
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

/-- Continuity within a set at a point of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContinuousWithinAt.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) s x₀)
    (hh : ContinuousWithinAt h s x₀) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x))) s x₀ :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  hp.totalSpaceMk_associatedBundleMk hh
/-- Continuity at a point of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContinuousAt.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) x₀) (hh : ContinuousAt h x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x))) x₀ :=
  (continuousWithinAt_univ _ _).1 <|
    hp.continuousWithinAt.totalSpaceMk_extendMk hρ hh.continuousWithinAt
/-- Continuity on a set of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContinuousOn.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (p x)) s) (hh : ContinuousOn h s) :
    ContinuousOn (fun x ↦ TotalSpace.mk' H (f x) (Extend.mk ρ hρ (p x) (h x))) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_extendMk hρ (hh x hx)
/-- Global continuity of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
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

/-- The quotient projection `TotalSpace G P × H → TotalSpace H (Extend P ρ hρ)` is continuous. -/
theorem continuous_totalSpaceMk_mk :
    Continuous fun x : TotalSpace G P × H ↦
      (⟨x.1.proj, mk ρ hρ x.1.snd x.2⟩ : TotalSpace H (Extend P ρ hρ)) :=
  Continuous.totalSpaceMk_extendMk hρ (f := fun x : TotalSpace G P × H ↦ x.1.proj)
    continuous_fst continuous_snd

/-- The canonical `ρ`-equivariant map `inl : TotalSpace G P → TotalSpace H (Extend P ρ hρ)` is
continuous. -/
theorem continuous_inl :
    Continuous fun x : TotalSpace G P ↦ (⟨x.proj, inl ρ hρ x.snd⟩ : TotalSpace H (Extend P ρ hρ)) :=
  Continuous.totalSpaceMk_extendMk hρ (f := TotalSpace.proj) continuous_id continuous_const

/-- The quotient projection `TotalSpace G P × H → TotalSpace H (Extend P ρ hρ)` is an open
quotient map. -/
theorem isOpenQuotientMap_totalSpaceMk_mk :
    IsOpenQuotientMap fun x : TotalSpace G P × H ↦
      (⟨x.1.proj, mk ρ hρ x.1.snd x.2⟩ : TotalSpace H (Extend P ρ hρ)) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
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
  set g : G := division G p₀ p
  have hp : p = op g • p₀ := (smul_division p₀ p).symm
  have heval (k : H) :
      equivOfEquivariant ρ hρ φ hφ b (mk ρ hρ p₀ k) = op k • φ b p₀ := by
    simp [equivOfEquivariant, p₀]
  calc equivOfEquivariant ρ hρ φ hφ b (mk ρ hρ p h)
      = equivOfEquivariant ρ hρ φ hφ b (mk ρ hρ p₀ (ρ g * h)) := by rw [hp, mk_smul]
    _ = op (ρ g * h) • φ b p₀ := heval _
    _ = op h • φ b p := by rw [op_mul, mul_smul, ← hφ, ← hp]
@[simp] theorem equivOfEquivariant_inl {b : B} (p : P b) :
    equivOfEquivariant ρ hρ φ hφ b (inl ρ hρ p) = φ b p := by
  rw [inl_def, equivOfEquivariant_mk, op_one, one_smul]
@[simp] theorem equivOfEquivariant_smul (b : B) (h' : H) (z : Extend P ρ hρ b) :
    equivOfEquivariant ρ hρ φ hφ b (op h' • z) = op h' • equivOfEquivariant ρ hρ φ hφ b z := by
  obtain ⟨p, h, rfl⟩ := exists_mk z
  rw [smul_mk, equivOfEquivariant_mk, equivOfEquivariant_mk, op_mul, mul_smul]
/-- Evaluating `(equivOfEquivariant ... b).symm` at `q : Q b` using any base representative `p`. -/
theorem equivOfEquivariant_symm_apply {b : B} (p : P b) (q : Q b) :
    (equivOfEquivariant ρ hρ φ hφ b).symm q = mk ρ hρ p (division H (φ b p) q) :=
  (equivOfEquivariant ρ hρ φ hφ b).symm_apply_eq.2 <| by rw [equivOfEquivariant_mk, smul_division]
@[simp] theorem equivOfEquivariant_symm_inl {b : B} (p : P b) :
    (equivOfEquivariant ρ hρ φ hφ b).symm (φ b p) = inl ρ hρ p :=
  (equivOfEquivariant ρ hρ φ hφ b).symm_apply_eq.2 (equivOfEquivariant_inl ρ hρ φ hφ p).symm
@[simp] theorem equivOfEquivariant_symm_smul (b : B) (h' : H) (q : Q b) :
    (equivOfEquivariant ρ hρ φ hφ b).symm (op h' • q) =
      op h' • (equivOfEquivariant ρ hρ φ hφ b).symm q :=
  (equivOfEquivariant ρ hρ φ hφ b).symm_apply_eq.2 <| by
    rw [equivOfEquivariant_smul, Equiv.apply_symm_apply]
/-- Uniqueness in the universal property: any `H`-equivariant fibrewise map `Extend P ρ hρ → Q`
extending `φ` along `inl` equals `equivOfEquivariant`. -/
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
  (ρ : G →* H) (hρ : Continuous ρ) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : Continuous fun x : TotalSpace G P ↦ TotalSpace.mk' H x.proj (φ x.proj x.snd))

/-- **Universal comparison homeomorphism.** If `φ : ∀ b, P b → Q b` is a continuous
`ρ`-equivariant map into a principal `H`-bundle `Q` and `H` is a topological group, then
`[p, h] ↦ φ b p • h` is an `H`-equivariant homeomorphism `Extend P ρ hρ ≃ₜ Q` over `B`. -/
noncomputable def homeomorphOfEquivariant : TotalSpace H (Extend P ρ hρ) ≃ₜ TotalSpace H Q where
  toFun z := ⟨z.proj, equivOfEquivariant ρ hρ φ hφ z.proj z.snd⟩
  invFun q := ⟨q.proj, (equivOfEquivariant ρ hρ φ hφ q.proj).symm q.snd⟩
  left_inv z := by simp
  right_inv q := by simp
  continuous_toFun := by
    rw [(isOpenQuotientMap_totalSpaceMk_mk P ρ hρ).isQuotientMap.continuous_iff]
    refine (Continuous.totalSpaceMk_smul (G := H) (P := Q)
      (f := fun x : TotalSpace G P × H ↦ x.1.proj) (p := fun x ↦ φ x.1.proj x.1.snd)
      (hφc.comp continuous_fst) continuous_snd).congr fun ⟨⟨b, p⟩, h⟩ ↦
        congrArg (TotalSpace.mk b) (equivOfEquivariant_mk ρ hρ φ hφ p h).symm
  continuous_invFun := by
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
    set b₀ := q₀.proj; set eP := trivializationAt G P b₀
    have hσq : ContinuousAt (fun q : TotalSpace H Q ↦ TotalSpace.mk' G q.proj (eP.symm q.proj 1))
        q₀ := (eP.continuousAt_totalSpaceMk_symm (mem_baseSet_trivializationAt G P b₀) 1).comp
      (FiberBundle.continuous_proj H Q).continuousAt
    refine (hσq.totalSpaceMk_extendMk hρ
      ((hφc.continuousAt.comp hσq).division (f := TotalSpace.proj) (q := fun q ↦ q.snd)
        continuousAt_id)).congr_of_eventuallyEq
      (Eventually.of_forall fun ⟨b, y⟩ ↦
        congrArg (TotalSpace.mk b) (equivOfEquivariant_symm_apply ρ hρ φ hφ (eP.symm b 1) y))

theorem homeomorphOfEquivariant_apply (z : TotalSpace H (Extend P ρ hρ)) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc z =
      ⟨z.proj, equivOfEquivariant ρ hρ φ hφ z.proj z.snd⟩ := (rfl)
theorem homeomorphOfEquivariant_symm_apply (q : TotalSpace H Q) :
    (homeomorphOfEquivariant ρ hρ φ hφ hφc).symm q =
      ⟨q.proj, (equivOfEquivariant ρ hρ φ hφ q.proj).symm q.snd⟩ := (rfl)
@[simp] theorem homeomorphOfEquivariant_proj (z : TotalSpace H (Extend P ρ hρ)) :
    (homeomorphOfEquivariant ρ hρ φ hφ hφc z).proj = z.proj := (rfl)
@[simp] theorem homeomorphOfEquivariant_symm_proj (q : TotalSpace H Q) :
    ((homeomorphOfEquivariant ρ hρ φ hφ hφc).symm q).proj = q.proj := (rfl)
@[simp] theorem homeomorphOfEquivariant_mk {b : B} (p : P b) (h : H) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc ⟨b, mk ρ hρ p h⟩ = ⟨b, op h • φ b p⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_mk ρ hρ φ hφ p h)
@[simp] theorem homeomorphOfEquivariant_inl {b : B} (p : P b) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc ⟨b, inl ρ hρ p⟩ = ⟨b, φ b p⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_inl ρ hρ φ hφ p)
@[simp] theorem homeomorphOfEquivariant_symm_inl {b : B} (p : P b) :
    (homeomorphOfEquivariant ρ hρ φ hφ hφc).symm ⟨b, φ b p⟩ = ⟨b, inl ρ hρ p⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_symm_inl ρ hρ φ hφ p)
@[simp] theorem homeomorphOfEquivariant_smul (h' : H) (z : TotalSpace H (Extend P ρ hρ)) :
    homeomorphOfEquivariant ρ hρ φ hφ hφc (op h' • z) =
      op h' • homeomorphOfEquivariant ρ hρ φ hφ hφc z :=
  congrArg (TotalSpace.mk z.proj) (equivOfEquivariant_smul ρ hρ φ hφ z.proj h' z.snd)
@[simp] theorem homeomorphOfEquivariant_symm_smul (h' : H) (q : TotalSpace H Q) :
    (homeomorphOfEquivariant ρ hρ φ hφ hφc).symm (op h' • q) =
      op h' • (homeomorphOfEquivariant ρ hρ φ hφ hφc).symm q :=
  congrArg (TotalSpace.mk q.proj) (equivOfEquivariant_symm_smul ρ hρ φ hφ q.proj h' q.snd)
end ReductionHomeomorph

section Congr
variable [ContinuousMul H] {ρ₁ ρ₂ : G →* H}
/-- Equal homomorphisms produce canonically equivalent extended fibres. -/
noncomputable def congrEquiv (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) (b : B) :
    Extend P ρ₁ hρ₁ b ≃ Extend P ρ₂ hρ₂ b := h ▸ Equiv.refl _
/-- Equal homomorphisms produce canonically homeomorphic extended total spaces. -/
noncomputable def congrHomeomorph (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) :
    TotalSpace H (Extend P ρ₁ hρ₁) ≃ₜ TotalSpace H (Extend P ρ₂ hρ₂) := h ▸ Homeomorph.refl _
@[simp] theorem congrEquiv_refl (ρ : G →* H) (hρ : Continuous ρ) (b : B) :
    congrEquiv (P := P) rfl hρ hρ b = Equiv.refl _ := by unfold congrEquiv; rfl
@[simp] theorem congrHomeomorph_refl (ρ : G →* H) (hρ : Continuous ρ) :
    congrHomeomorph (P := P) rfl hρ hρ = Homeomorph.refl _ := by unfold congrHomeomorph; rfl
section
variable (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
@[simp] theorem congrEquiv_mk {b : B} (p : P b) (x : H) :
    congrEquiv h hρ₁ hρ₂ b (mk ρ₁ hρ₁ p x) = mk ρ₂ hρ₂ p x := by subst h; rfl
@[simp] theorem congrEquiv_symm_mk {b : B} (p : P b) (x : H) :
    (congrEquiv h hρ₁ hρ₂ b).symm (mk ρ₂ hρ₂ p x) = mk ρ₁ hρ₁ p x := by subst h; rfl
@[simp] theorem congrEquiv_inl {b : B} (p : P b) :
    congrEquiv h hρ₁ hρ₂ b (inl ρ₁ hρ₁ p) = inl ρ₂ hρ₂ p := by subst h; rfl
@[simp] theorem congrEquiv_symm_inl {b : B} (p : P b) :
    (congrEquiv h hρ₁ hρ₂ b).symm (inl ρ₂ hρ₂ p) = inl ρ₁ hρ₁ p := by subst h; rfl
theorem congrEquiv_symm (b : B) :
    (congrEquiv (P := P) h hρ₁ hρ₂ b).symm = congrEquiv h.symm hρ₂ hρ₁ b := by subst h; rfl
@[simp] theorem congrEquiv_smul (b : B) (x : H) (z : Extend P ρ₁ hρ₁ b) :
    congrEquiv h hρ₁ hρ₂ b (op x • z) = op x • congrEquiv h hρ₁ hρ₂ b z := by subst h; rfl
@[simp] theorem congrEquiv_symm_smul (b : B) (x : H) (z : Extend P ρ₂ hρ₂ b) :
    (congrEquiv h hρ₁ hρ₂ b).symm (op x • z) = op x • (congrEquiv h hρ₁ hρ₂ b).symm z := by
  subst h; rfl
theorem trivializationAt_congrEquiv_snd (b' b : B) (z : Extend P ρ₁ hρ₁ b) :
    (trivializationAt H (Extend P ρ₁ hρ₁) b' ⟨b, z⟩).2 =
      (trivializationAt H (Extend P ρ₂ hρ₂) b' ⟨b, congrEquiv h hρ₁ hρ₂ b z⟩).2 := by subst h; rfl
theorem congrHomeomorph_apply (z : TotalSpace H (Extend P ρ₁ hρ₁)) :
    congrHomeomorph h hρ₁ hρ₂ z = ⟨z.proj, congrEquiv h hρ₁ hρ₂ z.proj z.snd⟩ := by subst h; rfl
theorem congrHomeomorph_symm_apply (z : TotalSpace H (Extend P ρ₂ hρ₂)) :
    (congrHomeomorph h hρ₁ hρ₂).symm z = ⟨z.proj, (congrEquiv h hρ₁ hρ₂ z.proj).symm z.snd⟩ := by
  subst h; rfl
theorem congrHomeomorph_symm :
    (congrHomeomorph (P := P) h hρ₁ hρ₂).symm = congrHomeomorph h.symm hρ₂ hρ₁ := by subst h; rfl
@[simp] theorem congrHomeomorph_proj (z : TotalSpace H (Extend P ρ₁ hρ₁)) :
    (congrHomeomorph h hρ₁ hρ₂ z).proj = z.proj := by subst h; rfl
@[simp] theorem congrHomeomorph_symm_proj (z : TotalSpace H (Extend P ρ₂ hρ₂)) :
    ((congrHomeomorph h hρ₁ hρ₂).symm z).proj = z.proj := by subst h; rfl
@[simp] theorem congrHomeomorph_mk {b : B} (p : P b) (x : H) :
    congrHomeomorph h hρ₁ hρ₂ ⟨b, mk ρ₁ hρ₁ p x⟩ = ⟨b, mk ρ₂ hρ₂ p x⟩ := by subst h; rfl
@[simp] theorem congrHomeomorph_symm_mk {b : B} (p : P b) (x : H) :
    (congrHomeomorph h hρ₁ hρ₂).symm ⟨b, mk ρ₂ hρ₂ p x⟩ = ⟨b, mk ρ₁ hρ₁ p x⟩ := by subst h; rfl
@[simp] theorem congrHomeomorph_inl {b : B} (p : P b) :
    congrHomeomorph h hρ₁ hρ₂ ⟨b, inl ρ₁ hρ₁ p⟩ = ⟨b, inl ρ₂ hρ₂ p⟩ := by subst h; rfl
@[simp] theorem congrHomeomorph_symm_inl {b : B} (p : P b) :
    (congrHomeomorph h hρ₁ hρ₂).symm ⟨b, inl ρ₂ hρ₂ p⟩ = ⟨b, inl ρ₁ hρ₁ p⟩ := by subst h; rfl
@[simp] theorem congrHomeomorph_smul (x : H) (z : TotalSpace H (Extend P ρ₁ hρ₁)) :
    congrHomeomorph h hρ₁ hρ₂ (op x • z) = op x • congrHomeomorph h hρ₁ hρ₂ z := by subst h; rfl
@[simp] theorem congrHomeomorph_symm_smul (x : H) (z : TotalSpace H (Extend P ρ₂ hρ₂)) :
    (congrHomeomorph h hρ₁ hρ₂).symm (op x • z) = op x • (congrHomeomorph h hρ₁ hρ₂).symm z := by
  subst h; rfl
end
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
theorem idEquiv_symm_smul (b : B) (g : G) (p : P b) :
    (idEquiv (G := G) b).symm (op g • p) = op g • (idEquiv (G := G) b).symm p := by
  rw [idEquiv_symm_apply, idEquiv_symm_apply, inl_smul, MonoidHom.id_apply]
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
  toFun z := ⟨z.proj, idEquiv z.proj z.snd⟩
  invFun z := ⟨z.proj, (idEquiv z.proj).symm z.snd⟩
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun z₀ ↦
      (FiberBundle.continuousAt_totalSpace G (fun z : TotalSpace G
        (Extend P (MonoidHom.id G) continuous_id) ↦ TotalSpace.mk' G z.proj
            (idEquiv z.proj z.snd))).2
        ⟨(FiberBundle.continuous_proj G _).continuousAt, ?_⟩
    have hb₀ := mem_baseSet_trivializationAt G P z₀.proj
    refine (((trivializationAt G (Extend P (MonoidHom.id G) continuous_id) z₀.proj).continuousAt
      ((Trivialization.mem_source _).2 ((baseSet_trivializationAt (P := P)
        (MonoidHom.id G) continuous_id z₀.proj).symm ▸ hb₀))).snd).congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj G _).continuousAt.preimage_mem_nhds
      ((trivializationAt G P z₀.proj).open_baseSet.mem_nhds hb₀)] with z hz
    exact (trivializationAt_idEquiv_snd hz z.snd).symm
  continuous_invFun := (continuous_inl P (MonoidHom.id G) continuous_id).congr fun ⟨b, p⟩ ↦
    congrArg (TotalSpace.mk b) (idEquiv_symm_apply (G := G) p).symm
theorem idHomeomorph_apply (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    idHomeomorph z = ⟨z.proj, idEquiv z.proj z.snd⟩ := (rfl)
theorem idHomeomorph_symm_apply (z : TotalSpace G P) :
    (idHomeomorph (G := G) (P := P)).symm z = ⟨z.proj, inl (MonoidHom.id G) continuous_id z.snd⟩ :=
  congrArg (TotalSpace.mk z.proj) (idEquiv_symm_apply (G := G) z.snd)
@[simp] theorem idHomeomorph_proj (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    (idHomeomorph z).proj = z.proj := (rfl)
@[simp] theorem idHomeomorph_symm_proj (z : TotalSpace G P) :
    ((idHomeomorph (G := G) (P := P)).symm z).proj = z.proj := (rfl)
@[simp] theorem idHomeomorph_mk {b : B} (p : P b) (g : G) :
    idHomeomorph ⟨b, mk (MonoidHom.id G) continuous_id p g⟩ = ⟨b, op g • p⟩ :=
  congrArg (TotalSpace.mk b) (idEquiv_mk p g)
@[simp] theorem idHomeomorph_inl {b : B} (p : P b) :
    idHomeomorph ⟨b, inl (MonoidHom.id G) continuous_id p⟩ = ⟨b, p⟩ :=
  congrArg (TotalSpace.mk b) (idEquiv_inl p)
@[simp] theorem idHomeomorph_smul (g : G)
    (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    idHomeomorph (op g • z) = op g • idHomeomorph z :=
  congrArg (TotalSpace.mk z.proj) (idEquiv_smul z.proj g z.snd)
@[simp] theorem idHomeomorph_symm_smul (g : G) (z : TotalSpace G P) :
    (idHomeomorph (G := G) (P := P)).symm (op g • z) =
      op g • (idHomeomorph (G := G) (P := P)).symm z :=
  congrArg (TotalSpace.mk z.proj) (idEquiv_symm_smul z.proj g z.snd)
end Id

section Comp
variable [ContinuousMul H] [ContinuousMul K]
  (ρ : G →* H) (hρ : Continuous ρ) (σ : H →* K) (hσ : Continuous σ)
/-- In an iterated extension, `[[p, h], k] = [[p, 1], σ h * k]`. -/
theorem mk_mk {b : B} (p : P b) (h : H) (k : K) :
    mk σ hσ (mk ρ hρ p h) k = mk σ hσ (inl ρ hρ p) (σ h * k) := by
  rw [← smul_inl ρ hρ p h, mk_smul]
/-- Extending along `ρ : G →* H` and then along `σ : H →* K` is fibrewise equivalent to extending
along `σ.comp ρ`, sending `[[p, h], k]` to `[p, σ h * k]`. -/
noncomputable def compEquiv (b : B) :
    Extend (Extend P ρ hρ) σ hσ b ≃ Extend P (σ.comp ρ) (hσ.comp hρ) b :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  letI := compHom K σ; haveI : ContinuousSMul H K := continuousSMul_compHom hσ
  letI := compHom K (σ.comp ρ); haveI : ContinuousSMul G K := continuousSMul_compHom (hσ.comp hρ)
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  AssociatedBundle.assocEquiv (G := G) (P := P) (H := H) (F := K) b
@[simp] theorem compEquiv_mk {b : B} (p : P b) (h : H) (k : K) :
    compEquiv ρ hρ σ hσ b (mk σ hσ (mk ρ hρ p h) k) = mk (σ.comp ρ) (hσ.comp hρ) p (σ h * k) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  letI := compHom K σ; haveI : ContinuousSMul H K := continuousSMul_compHom hσ
  letI := compHom K (σ.comp ρ); haveI : ContinuousSMul G K := continuousSMul_compHom (hσ.comp hρ)
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H K := SMul.comp.isScalarTower (⇑ρ)
  AssociatedBundle.assocEquiv_mk p h k
@[simp] theorem compEquiv_symm_mk {b : B} (p : P b) (k : K) :
    (compEquiv ρ hρ σ hσ b).symm (mk (σ.comp ρ) (hσ.comp hρ) p k) = mk σ hσ (inl ρ hρ p) k :=
  (compEquiv ρ hρ σ hσ b).symm_apply_eq.2 (by rw [inl_def, compEquiv_mk, map_one, one_mul])
@[simp] theorem compEquiv_inl {b : B} (p : P b) :
    compEquiv ρ hρ σ hσ b (inl σ hσ (inl ρ hρ p)) = inl (σ.comp ρ) (hσ.comp hρ) p := by
  rw [inl_def, inl_def, inl_def, compEquiv_mk, map_one, one_mul]
@[simp] theorem compEquiv_symm_inl {b : B} (p : P b) :
    (compEquiv ρ hρ σ hσ b).symm (inl (σ.comp ρ) (hσ.comp hρ) p) = inl σ hσ (inl ρ hρ p) :=
  (compEquiv ρ hρ σ hσ b).symm_apply_eq.2 (compEquiv_inl ρ hρ σ hσ p).symm
@[simp] theorem compEquiv_smul (b : B) (k' : K) (z : Extend (Extend P ρ hρ) σ hσ b) :
    compEquiv ρ hρ σ hσ b (op k' • z) = op k' • compEquiv ρ hρ σ hσ b z := by
  obtain ⟨u, k, rfl⟩ := exists_mk z; obtain ⟨p, h, rfl⟩ := exists_mk u
  rw [smul_mk, compEquiv_mk, compEquiv_mk, smul_mk, mul_assoc]
@[simp] theorem compEquiv_symm_smul (b : B) (k' : K) (z : Extend P (σ.comp ρ) (hσ.comp hρ) b) :
    (compEquiv ρ hρ σ hσ b).symm (op k' • z) = op k' • (compEquiv ρ hρ σ hσ b).symm z :=
  (compEquiv ρ hρ σ hσ b).symm_apply_eq.2 <| by rw [compEquiv_smul, Equiv.apply_symm_apply]
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
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  letI := compHom K σ; haveI : ContinuousSMul H K := continuousSMul_compHom hσ
  letI := compHom K (σ.comp ρ); haveI : ContinuousSMul G K := continuousSMul_compHom (hσ.comp hρ)
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H K := SMul.comp.isScalarTower (⇑ρ)
  AssociatedBundle.assocHomeomorph (G := G) (P := P) (H := H) (F := K)
theorem compHomeomorph_apply (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    compHomeomorph ρ hρ σ hσ z = ⟨z.proj, compEquiv ρ hρ σ hσ z.proj z.snd⟩ :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  letI := compHom K σ; haveI : ContinuousSMul H K := continuousSMul_compHom hσ
  letI := compHom K (σ.comp ρ); haveI : ContinuousSMul G K := continuousSMul_compHom (hσ.comp hρ)
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H K := SMul.comp.isScalarTower (⇑ρ)
  AssociatedBundle.assocHomeomorph_apply z
theorem compHomeomorph_symm_apply (z : TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (compHomeomorph (P := P) ρ hρ σ hσ).symm z =
      ⟨z.proj, (compEquiv ρ hρ σ hσ z.proj).symm z.snd⟩ :=
  (compHomeomorph ρ hρ σ hσ).symm_apply_eq.2 <| by rw [compHomeomorph_apply, Equiv.apply_symm_apply]
@[simp] theorem compHomeomorph_proj (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    (compHomeomorph ρ hρ σ hσ z).proj = z.proj := by rw [compHomeomorph_apply]
@[simp] theorem compHomeomorph_symm_proj (z : TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    ((compHomeomorph (P := P) ρ hρ σ hσ).symm z).proj = z.proj := by rw [compHomeomorph_symm_apply]
@[simp] theorem compHomeomorph_mk {b : B} (p : P b) (h : H) (k : K) :
    compHomeomorph ρ hρ σ hσ ⟨b, mk σ hσ (mk ρ hρ p h) k⟩ =
      ⟨b, mk (σ.comp ρ) (hσ.comp hρ) p (σ h * k)⟩ := by rw [compHomeomorph_apply, compEquiv_mk]
@[simp] theorem compHomeomorph_symm_mk {b : B} (p : P b) (k : K) :
    (compHomeomorph ρ hρ σ hσ).symm ⟨b, mk (σ.comp ρ) (hσ.comp hρ) p k⟩ =
      ⟨b, mk σ hσ (inl ρ hρ p) k⟩ := by rw [compHomeomorph_symm_apply, compEquiv_symm_mk]
@[simp] theorem compHomeomorph_inl {b : B} (p : P b) :
    compHomeomorph ρ hρ σ hσ ⟨b, inl σ hσ (inl ρ hρ p)⟩ =
      ⟨b, inl (σ.comp ρ) (hσ.comp hρ) p⟩ := by rw [compHomeomorph_apply, compEquiv_inl]
@[simp] theorem compHomeomorph_symm_inl {b : B} (p : P b) :
    (compHomeomorph ρ hρ σ hσ).symm ⟨b, inl (σ.comp ρ) (hσ.comp hρ) p⟩ =
      ⟨b, inl σ hσ (inl ρ hρ p)⟩ := by rw [compHomeomorph_symm_apply, compEquiv_symm_inl]
@[simp] theorem compHomeomorph_smul (k' : K) (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    compHomeomorph ρ hρ σ hσ (op k' • z) = op k' • compHomeomorph ρ hρ σ hσ z := by
  rw [compHomeomorph_apply, compHomeomorph_apply]
  exact congrArg (TotalSpace.mk z.proj) (compEquiv_smul ρ hρ σ hσ z.proj k' z.snd)
@[simp] theorem compHomeomorph_symm_smul (k' : K)
    (z : TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (compHomeomorph (P := P) ρ hρ σ hσ).symm (op k' • z) =
      op k' • (compHomeomorph (P := P) ρ hρ σ hσ).symm z := by
  rw [compHomeomorph_symm_apply, compHomeomorph_symm_apply]
  exact congrArg (TotalSpace.mk z.proj) (compEquiv_symm_smul ρ hρ σ hσ z.proj k' z.snd)
end Comp

section Pullback
variable [∀ b, Nonempty (P b)] [ContinuousMul H]
  {M : Type*} [FunLike M B' B] [ContinuousMapClass M B' B] (f : M) (ρ : G →* H) (hρ : Continuous ρ)
/-- Fibrewise equivalence between extending `f *ᵖ P` along `ρ` and pulling back `Extend P ρ hρ`. -/
noncomputable def pullbackEquiv (x : B') :
    Extend ((f : B' → B) *ᵖ P) ρ hρ x ≃ ((f : B' → B) *ᵖ (Extend P ρ hρ)) x :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.pullbackEquiv (G := G) (P := P) (F := H) f x
@[simp] theorem pullbackEquiv_mk (x : B') (p : P (f x)) (h : H) :
    pullbackEquiv f ρ hρ x (mk (P := (f : B' → B) *ᵖ P) ρ hρ p h) = mk (P := P) ρ hρ p h :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.pullbackEquiv_mk f x p h
@[simp] theorem pullbackEquiv_symm_mk (x : B') (p : P (f x)) (h : H) :
    (pullbackEquiv f ρ hρ x).symm (mk (P := P) ρ hρ p h) = mk (P := (f : B' → B) *ᵖ P) ρ hρ p h :=
  (pullbackEquiv f ρ hρ x).symm_apply_eq.2 (pullbackEquiv_mk f ρ hρ x p h).symm
@[simp] theorem pullbackEquiv_inl (x : B') (p : P (f x)) :
    pullbackEquiv f ρ hρ x (inl (P := (f : B' → B) *ᵖ P) ρ hρ p) = inl (P := P) ρ hρ p :=
  pullbackEquiv_mk f ρ hρ x p 1
@[simp] theorem pullbackEquiv_symm_inl (x : B') (p : P (f x)) :
    (pullbackEquiv f ρ hρ x).symm (inl (P := P) ρ hρ p) = inl (P := (f : B' → B) *ᵖ P) ρ hρ p :=
  pullbackEquiv_symm_mk f ρ hρ x p 1
@[simp] theorem pullbackEquiv_smul (x : B') (h' : H) (z : Extend ((f : B' → B) *ᵖ P) ρ hρ x) :
    pullbackEquiv f ρ hρ x (op h' • z) = op h' • pullbackEquiv f ρ hρ x z := by
  obtain ⟨p, h, rfl⟩ := exists_mk z
  rw [Pullback.smul_eq, smul_mk (P := (f : B' → B) *ᵖ P)]
  exact (pullbackEquiv_mk f ρ hρ x p (h * h')).trans <|
    (smul_mk (P := P) ρ hρ p h h').symm.trans <|
      congrArg (op h' • ·) (pullbackEquiv_mk f ρ hρ x p h).symm
@[simp] theorem pullbackEquiv_symm_smul (x : B') (h' : H)
    (z : ((f : B' → B) *ᵖ (Extend P ρ hρ)) x) :
    (pullbackEquiv f ρ hρ x).symm (op h' • z) = op h' • (pullbackEquiv f ρ hρ x).symm z :=
  (pullbackEquiv f ρ hρ x).symm_apply_eq.2 <| by rw [pullbackEquiv_smul, Equiv.apply_symm_apply]
theorem trivializationAt_pullbackEquiv_snd {x₀ x : B'}
    (hx : f x ∈ (trivializationAt G P (f x₀)).baseSet) (z : Extend ((f : B' → B) *ᵖ P) ρ hρ x) :
    (trivializationAt H (Extend ((f : B' → B) *ᵖ P) ρ hρ) x₀ ⟨x, z⟩).2 =
      (trivializationAt H (Extend P ρ hρ) (f x₀) ⟨f x, pullbackEquiv f ρ hρ x z⟩).2 :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.trivializationAt_pullbackEquiv_snd f hx z
/-- **Extension of structure group commutes with pullback.** -/
noncomputable def pullbackHomeomorph :
    TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ) ≃ₜ
      TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ)) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.pullbackHomeomorph (G := G) (P := P) (F := H) f
theorem pullbackHomeomorph_apply (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    pullbackHomeomorph f ρ hρ z = ⟨z.proj, pullbackEquiv f ρ hρ z.proj z.snd⟩ :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  AssociatedBundle.pullbackHomeomorph_apply f z
theorem pullbackHomeomorph_symm_apply (z : TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (pullbackHomeomorph (P := P) f ρ hρ).symm z =
      ⟨z.proj, (pullbackEquiv f ρ hρ z.proj).symm z.snd⟩ :=
  (pullbackHomeomorph f ρ hρ).symm_apply_eq.2 <| by
    rw [pullbackHomeomorph_apply, Equiv.apply_symm_apply]
@[simp] theorem pullbackHomeomorph_proj (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    (pullbackHomeomorph f ρ hρ z).proj = z.proj := by rw [pullbackHomeomorph_apply]
@[simp] theorem pullbackHomeomorph_symm_proj (z : TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    ((pullbackHomeomorph (P := P) f ρ hρ).symm z).proj = z.proj := by
  rw [pullbackHomeomorph_symm_apply]
@[simp] theorem pullbackHomeomorph_mk (x : B') (p : P (f x)) (h : H) :
    pullbackHomeomorph f ρ hρ ⟨x, mk (P := (f : B' → B) *ᵖ P) ρ hρ p h⟩ =
      ⟨x, mk (P := P) ρ hρ p h⟩ := by rw [pullbackHomeomorph_apply, pullbackEquiv_mk]
@[simp] theorem pullbackHomeomorph_symm_mk (x : B') (p : P (f x)) (h : H) :
    (pullbackHomeomorph f ρ hρ).symm ⟨x, mk (P := P) ρ hρ p h⟩ =
      ⟨x, mk (P := (f : B' → B) *ᵖ P) ρ hρ p h⟩ := by
  rw [pullbackHomeomorph_symm_apply, pullbackEquiv_symm_mk]
@[simp] theorem pullbackHomeomorph_inl (x : B') (p : P (f x)) :
    pullbackHomeomorph f ρ hρ ⟨x, inl (P := (f : B' → B) *ᵖ P) ρ hρ p⟩ =
      ⟨x, inl (P := P) ρ hρ p⟩ := by rw [pullbackHomeomorph_apply, pullbackEquiv_inl]
@[simp] theorem pullbackHomeomorph_symm_inl (x : B') (p : P (f x)) :
    (pullbackHomeomorph f ρ hρ).symm ⟨x, inl (P := P) ρ hρ p⟩ =
      ⟨x, inl (P := (f : B' → B) *ᵖ P) ρ hρ p⟩ := by
  rw [pullbackHomeomorph_symm_apply, pullbackEquiv_symm_inl]
@[simp] theorem pullbackHomeomorph_smul (h' : H)
    (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    pullbackHomeomorph f ρ hρ (op h' • z) = op h' • pullbackHomeomorph f ρ hρ z := by
  rw [pullbackHomeomorph_apply, pullbackHomeomorph_apply]
  exact congrArg (TotalSpace.mk z.proj) (pullbackEquiv_smul f ρ hρ z.proj h' z.snd)
@[simp] theorem pullbackHomeomorph_symm_smul (h' : H)
    (z : TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (pullbackHomeomorph (P := P) f ρ hρ).symm (op h' • z) =
      op h' • (pullbackHomeomorph (P := P) f ρ hρ).symm z := by
  rw [pullbackHomeomorph_symm_apply, pullbackHomeomorph_symm_apply]
  exact congrArg (TotalSpace.mk z.proj) (pullbackEquiv_symm_smul f ρ hρ z.proj h' z.snd)
end Pullback

section Associated
variable [ContinuousMul H] [TopologicalSpace F]
  [MulAction H F] [ContinuousSMul H F] [MulAction G F] [ContinuousSMul G F]
  (ρ : G →* H) (hρ : Continuous ρ)
/-- Fibrewise equivalence `(Extend P ρ hρ) ×_H F ≃ P ×_G F` when `G` acts on `F` through `ρ`. -/
noncomputable def associatedEquiv (_hF : ∀ (g : G) (v : F), g • v = ρ g • v) (b : B) :
    AssociatedBundle H (Extend P ρ hρ) F b ≃ AssociatedBundle G P F b :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  AssociatedBundle.assocEquiv (G := G) (P := P) b
section
variable (hF : ∀ (g : G) (v : F), g • v = ρ g • v)
/-- **Associated bundle of an extended principal bundle.** `(P ×_ρ H) ×_H F` is canonically
homeomorphic over `B` to `P ×_G F` when `G` acts on `F` through `ρ`. -/
noncomputable def associatedHomeomorph :
    TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F) ≃ₜ TotalSpace F (AssociatedBundle G P F) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.assocHomeomorph (G := G) (P := P) (H := H) (F := F)
@[simp] theorem associatedEquiv_mk {b : B} (p : P b) (h : H) (v : F) :
    associatedEquiv ρ hρ hF b (AssociatedBundle.mk H (mk ρ hρ p h) v) =
      AssociatedBundle.mk G p (h • v) :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.assocEquiv_mk p h v
@[simp] theorem associatedEquiv_symm_mk {b : B} (p : P b) (v : F) :
    (associatedEquiv ρ hρ hF b).symm (AssociatedBundle.mk G p v) =
      AssociatedBundle.mk H (inl ρ hρ p) v :=
  (associatedEquiv ρ hρ hF b).symm_apply_eq.2 (by rw [inl_def, associatedEquiv_mk, one_smul])
@[simp] theorem associatedEquiv_inl {b : B} (p : P b) (v : F) :
    associatedEquiv ρ hρ hF b (AssociatedBundle.mk H (inl ρ hρ p) v) =
      AssociatedBundle.mk G p v := by rw [inl_def, associatedEquiv_mk, one_smul]
theorem trivializationAt_associatedEquiv_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (z : AssociatedBundle H (Extend P ρ hρ) F b) :
    (trivializationAt F (AssociatedBundle H (Extend P ρ hρ) F) b' ⟨b, z⟩).2 =
      (trivializationAt F (AssociatedBundle G P F) b' ⟨b, associatedEquiv ρ hρ hF b z⟩).2 :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.trivializationAt_assocEquiv_snd hb z
theorem associatedHomeomorph_apply (z : TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F)) :
    associatedHomeomorph ρ hρ hF z = ⟨z.proj, associatedEquiv ρ hρ hF z.proj z.snd⟩ :=
  letI := compHom H ρ; haveI : ContinuousSMul G H := continuousSMul_compHom hρ
  haveI : SMulCommClass G Hᵐᵒᵖ H := SMul.comp.smulCommClass (⇑ρ)
  haveI : IsScalarTower G H F := ⟨fun g h₀ v₀ ↦ (mul_smul (ρ g) h₀ v₀).trans (hF g (h₀ • v₀)).symm⟩
  AssociatedBundle.assocHomeomorph_apply z
theorem associatedHomeomorph_symm_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    (associatedHomeomorph (P := P) ρ hρ hF).symm z =
      ⟨z.proj, (associatedEquiv ρ hρ hF z.proj).symm z.snd⟩ :=
  (associatedHomeomorph ρ hρ hF).symm_apply_eq.2 <| by
    rw [associatedHomeomorph_apply, Equiv.apply_symm_apply]
@[simp] theorem associatedHomeomorph_proj
    (z : TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F)) :
    (associatedHomeomorph ρ hρ hF z).proj = z.proj := by rw [associatedHomeomorph_apply]
@[simp] theorem associatedHomeomorph_symm_proj (z : TotalSpace F (AssociatedBundle G P F)) :
    ((associatedHomeomorph (P := P) ρ hρ hF).symm z).proj = z.proj := by
  rw [associatedHomeomorph_symm_apply]
@[simp] theorem associatedHomeomorph_mk {b : B} (p : P b) (h : H) (v : F) :
    associatedHomeomorph ρ hρ hF ⟨b, AssociatedBundle.mk H (mk ρ hρ p h) v⟩ =
      ⟨b, AssociatedBundle.mk G p (h • v)⟩ := by rw [associatedHomeomorph_apply, associatedEquiv_mk]
@[simp] theorem associatedHomeomorph_symm_mk {b : B} (p : P b) (v : F) :
    (associatedHomeomorph ρ hρ hF).symm ⟨b, AssociatedBundle.mk G p v⟩ =
      ⟨b, AssociatedBundle.mk H (inl ρ hρ p) v⟩ := by
  rw [associatedHomeomorph_symm_apply, associatedEquiv_symm_mk]
@[simp] theorem associatedHomeomorph_inl {b : B} (p : P b) (v : F) :
    associatedHomeomorph ρ hρ hF ⟨b, AssociatedBundle.mk H (inl ρ hρ p) v⟩ =
      ⟨b, AssociatedBundle.mk G p v⟩ := by rw [associatedHomeomorph_apply, associatedEquiv_inl]
end
end Associated

end TauCeti.PrincipalBundle.Extend
