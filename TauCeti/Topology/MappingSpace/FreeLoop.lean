/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.CompactOpen
public import TauCeti.Topology.ContinuousMap.Precomp
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.PathSpace.Moore.Comparison.Between

/-!
# Paths of free loops, closed unit-interval paths, and contractible free loops

The free loop space of a space `Q` is the space `C(S¹, Q)` of maps from the circle, with the
compact-open topology. Precomposition with the standard quotient `unitToCircle : I → S¹`,
`t ↦ exp(2πit)`, identifies `C(S¹, Q)` homeomorphically with the subspace `ClosedUnitPath Q` of
closed unit-interval paths `{p : C(I, Q) // p 0 = p 1}` (`circleMapHomeomorphClosedUnitPath`),
compatibly with evaluation at `1 ∈ S¹`, constant loops, and the based loop fibre
`BasedMap Circle Q 1 x ≃ₜ Path x x` (`basedMapCircleOneHomeomorphPath`).

Its subspace `𝓛₀Q` of **contractible** loops (`TauCeti.contractibleLoops`) consists of the loops
joined by a path in the free loop space to a constant loop, equivalently to the constant loop at
their own basepoint (`mem_contractibleLoops_iff_joined_const`). The constant loops embed in `𝓛₀Q`
(`TauCeti.isEmbedding_constContractibleLoop`) and retract onto `Q` via evaluation at `1`
(`TauCeti.constContractibleLoopRangeHomeomorph`). A path in the free loop space that starts at a
constant loop stays in `𝓛₀Q` (`TauCeti.constLoopPath_mem_contractibleLoops`), so the paths from a
constant loop to a constant loop, `TauCeti.ConstLoopPath`, are the same as such paths in `𝓛₀Q`
(`TauCeti.constLoopPathHomeomorph`), which in turn identify with `unitPathsBetween` between the
constant-loop subspaces (`contractibleConstLoopPathHomeomorphUnitPathsBetween`,
`basedContractibleConstLoopPathHomeomorphUnitPathsBetween`).

## Main declarations

* `TauCeti.unitToCircle`, `TauCeti.ClosedUnitPath`,
  `TauCeti.circleMapHomeomorphClosedUnitPath`: `C(Circle, Q) ≃ₜ {p : C(I, Q) // p 0 = p 1}`.
* `TauCeti.basedMapCircleOneHomeomorphPath`: `BasedMap Circle Q 1 x ≃ₜ Path x x`.
* `TauCeti.contractibleLoops`: the contractible free loops `𝓛₀Q`.
* `TauCeti.constContractibleLoop`: the constant loops as a continuous map `Q → 𝓛₀Q`, an
  embedding by `TauCeti.isEmbedding_constContractibleLoop`, with image homeomorphic to `Q` by
  `TauCeti.constContractibleLoopRangeHomeomorph`.
* `TauCeti.ConstLoopPath`, `TauCeti.ContractibleConstLoopPath`, `TauCeti.constLoopPathHomeomorph`,
  `TauCeti.contractibleConstLoopPathHomeomorphUnitPathsBetween`,
  `TauCeti.basedContractibleConstLoopPathHomeomorphUnitPathsBetween`.
-/

public section

noncomputable section

open scoped unitInterval

namespace TauCeti

variable (Q : Type*) [TopologicalSpace Q]

/-- The paths `I → C(S¹, Q)` in the free loop space from a constant loop to a constant loop,
with the compact-open topology. -/
abbrev ConstLoopPath : Type _ :=
  {p : C(I, C(Circle, Q)) // (∃ q, p 0 = ContinuousMap.const Circle q) ∧
    ∃ q, p 1 = ContinuousMap.const Circle q}

variable {Q}

variable (Q) in
/-- The **contractible free loops** `𝓛₀Q ⊆ C(S¹, Q)`: the loops joined by a path in the free loop
space to a constant loop. -/
def contractibleLoops : Set C(Circle, Q) :=
  {γ | ∃ q, Joined γ (ContinuousMap.const Circle q)}

/-- A free loop is contractible exactly when it is joined, by a path in the free loop space, to a
constant loop. -/
@[simp]
theorem mem_contractibleLoops_iff {γ : C(Circle, Q)} :
    γ ∈ contractibleLoops Q ↔ ∃ q, Joined γ (ContinuousMap.const Circle q) :=
  Iff.rfl

/-- A constant loop is contractible. -/
theorem const_mem_contractibleLoops (q : Q) : ContinuousMap.const Circle q ∈ contractibleLoops Q :=
  ⟨q, Joined.refl _⟩

/-- The constant loops, as a continuous map `Q → 𝓛₀Q`. -/
def constContractibleLoop : C(Q, contractibleLoops Q) :=
  ⟨fun q => ⟨ContinuousMap.const Circle q, const_mem_contractibleLoops q⟩,
    ContinuousMap.continuous_const'.subtype_mk _⟩

/-- The underlying free loop of `constContractibleLoop q` is the constant loop at `q`. -/
@[simp]
theorem coe_constContractibleLoop (q : Q) :
    (constContractibleLoop q : C(Circle, Q)) = ContinuousMap.const Circle q := by
  rw [constContractibleLoop]
  -- the underlying free loop of the subtype element built there is the constant loop
  rfl

/-- The constant loops form a topological embedding `Q → 𝓛₀Q`, the codomain restriction of the
embedding of constant maps. -/
theorem isEmbedding_constContractibleLoop :
    Topology.IsEmbedding (constContractibleLoop (Q := Q)) :=
  ContinuousMap.isEmbedding_const.codRestrict _ const_mem_contractibleLoops

/-- Every loop along a path of free loops that starts at a constant loop is contractible: a path
in `ConstLoopPath Q` is a path in `𝓛₀Q`. -/
theorem constLoopPath_mem_contractibleLoops (p : ConstLoopPath Q) (t : I) :
    p.1 t ∈ contractibleLoops Q := by
  obtain ⟨⟨q, hq⟩, -⟩ := p.2
  have h : Joined (0 : I) t := ⟨⟨⟨fun s => s * t, by fun_prop⟩, by simp, by simp⟩⟩
  have h' := h.map p.1.continuous
  rw [hq] at h'
  exact ⟨q, h'.symm⟩

variable (Q) in
/-- The paths in the free loop space from the constant loop at `x` to a constant loop. -/
abbrev BasedConstLoopPath (x : Q) : Type _ :=
  {p : ConstLoopPath Q // p.1 0 = ContinuousMap.const Circle x}

variable (Q) in
/-- The paths in the contractible free loops `𝓛₀Q` from a constant loop to a constant loop. -/
abbrev ContractibleConstLoopPath : Type _ :=
  {p : C(I, contractibleLoops Q) //
    (∃ q, p 0 = constContractibleLoop q) ∧ ∃ q, p 1 = constContractibleLoop q}

/-- A path of free loops from a constant loop to a constant loop is a path in the contractible free
loops `𝓛₀Q`. -/
def constLoopPathHomeomorph : ConstLoopPath Q ≃ₜ ContractibleConstLoopPath Q where
  toFun p := ⟨⟨fun t => ⟨p.1 t, constLoopPath_mem_contractibleLoops p t⟩,
      p.1.continuous.subtype_mk _⟩,
    ⟨p.2.1.choose, Subtype.ext p.2.1.choose_spec⟩, ⟨p.2.2.choose, Subtype.ext p.2.2.choose_spec⟩⟩
  invFun r := ⟨(ContinuousMap.mk Subtype.val continuous_subtype_val).comp r.1,
    ⟨r.2.1.choose, congrArg Subtype.val r.2.1.choose_spec⟩,
    ⟨r.2.2.choose, congrArg Subtype.val r.2.2.choose_spec⟩⟩
  -- both composites rebuild the same data, by the definitional eta rules for subtypes
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    refine ((ContinuousMap.isInducing_postcomp (ContinuousMap.mk Subtype.val
      continuous_subtype_val) Topology.IsInducing.subtypeVal).continuous_iff).2 ?_
    exact continuous_subtype_val
  continuous_invFun :=
    continuous_induced_rng.2 ((ContinuousMap.continuous_postcomp _).comp continuous_subtype_val)

/-- The path of contractible loops, read in the free loop space, is the original path. -/
@[simp]
theorem coe_constLoopPathHomeomorph (p : ConstLoopPath Q) (t : I) :
    ((constLoopPathHomeomorph p).1 t : C(Circle, Q)) = p.1 t := by
  rw [constLoopPathHomeomorph]
  -- the underlying free loop at `t` is `p.1 t`, by construction of `toFun`
  rfl

variable (Q) in
/-- The paths in the contractible free loops from the constant loop at `x` to a constant loop. -/
abbrev BasedContractibleConstLoopPath (x : Q) : Type _ :=
  {p : ContractibleConstLoopPath Q // p.1 0 = constContractibleLoop x}

/-- The inverse of `constLoopPathHomeomorph` reads a path in the contractible loops in the free
loop space. -/
@[simp]
theorem coe_constLoopPathHomeomorph_symm (r : ContractibleConstLoopPath Q) (t : I) :
    (constLoopPathHomeomorph.symm r).1 t = (r.1 t : C(Circle, Q)) := by
  have h := coe_constLoopPathHomeomorph (constLoopPathHomeomorph.symm r) t
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-! ### Closed unit-interval paths and circle maps -/

/-- The standard quotient `I → Circle`, `t ↦ exp(2πit)`, collapsing the endpoints `0` and `1` to
`1 ∈ Circle` and mapping `(0, 1)` bijectively onto `Circle \ {1}`. -/
def unitToCircle : C(I, Circle) where
  toFun t := Circle.exp (2 * Real.pi * t)
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem unitToCircle_apply (t : I) : unitToCircle t = Circle.exp (2 * Real.pi * t) :=
  (rfl)

@[simp]
theorem unitToCircle_zero : unitToCircle 0 = 1 := by
  simp [unitToCircle_apply]

@[simp]
theorem unitToCircle_one : unitToCircle 1 = 1 := by
  simp [unitToCircle_apply]

/-- `unitToCircle` is surjective: every `z : Circle` is `exp (angleDiff 1 z)` for
`angleDiff 1 z ∈ [0, 2π)`. -/
theorem unitToCircle_surjective : Function.Surjective unitToCircle := fun z ↦ by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⟨Circle.angleDiff 1 z / (2 * Real.pi),
    div_nonneg (Circle.angleDiff_nonneg 1 z) hp.le,
    (div_le_one hp).2 (Circle.angleDiff_lt_two_pi 1 z).le⟩, ?_⟩
  rw [unitToCircle_apply, mul_div_cancel₀ _ hp.ne']
  simpa using Circle.exp_angleDiff_mul (x := 1) (y := z)

/-- `unitToCircle` sends exactly the endpoints `0` and `1` to `1 ∈ Circle`. -/
@[simp]
theorem unitToCircle_eq_one_iff (t : I) : unitToCircle t = 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    rw [unitToCircle_apply, Circle.exp_eq_one] at h
    obtain ⟨n, hn⟩ := h
    have hp : (2 * Real.pi) ≠ 0 := by positivity
    have htn : (t : ℝ) = n := mul_left_cancel₀ hp (by linarith)
    have h0 : 0 ≤ n := by exact_mod_cast (htn ▸ t.2.1 : (0 : ℝ) ≤ n)
    have h1 : n ≤ 1 := by exact_mod_cast (htn ▸ t.2.2 : (n : ℝ) ≤ 1)
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa using htn))
    · exact Or.inr (Subtype.ext (by simpa using htn))
  · rintro (rfl | rfl) <;> simp

/-- Two points of `I` with the same image under `unitToCircle` are equal or opposite endpoints. -/
theorem eq_or_of_unitToCircle_eq {s t : I} (h : unitToCircle s = unitToCircle t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  rw [unitToCircle_apply, unitToCircle_apply, Circle.exp_eq_exp] at h
  obtain ⟨m, hm⟩ := h
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  have hst : (s : ℝ) = t + m := mul_left_cancel₀ hp (by linarith)
  have hm1 : (-1 : ℝ) ≤ m := by linarith [s.2.1, t.2.2]
  have hm2 : (m : ℝ) ≤ 1 := by linarith [s.2.2, t.2.1]
  have hm1' : -1 ≤ m := by exact_mod_cast hm1
  have hm2' : m ≤ 1 := by exact_mod_cast hm2
  have hcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · right; left
    push_cast at hst
    exact ⟨Subtype.ext (by simpa using (by linarith [s.2.1, t.2.2] : (s : ℝ) = 0)),
      Subtype.ext (by simpa using (by linarith [s.2.1, t.2.2] : (t : ℝ) = 1))⟩
  · left
    push_cast at hst
    exact Subtype.ext (by linarith)
  · right; right
    push_cast at hst
    exact ⟨Subtype.ext (by simpa using (by linarith [s.2.2, t.2.1] : (s : ℝ) = 1)),
      Subtype.ext (by simpa using (by linarith [s.2.2, t.2.1] : (t : ℝ) = 0))⟩

variable (Q) in
/-- Closed paths on the unit interval `I`, with the subspace compact-open topology. -/
abbrev ClosedUnitPath : Type _ :=
  {p : C(I, Q) // p 0 = p 1}

private theorem factorsThrough_unitToCircle_iff (g : C(I, Q)) :
    Function.FactorsThrough g unitToCircle ↔ g 0 = g 1 where
  mp h := h (unitToCircle_zero.trans unitToCircle_one.symm)
  mpr hg _ _ hst := by
    rcases eq_or_of_unitToCircle_eq hst with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hg
    · exact hg.symm

/-- **Circle maps are closed unit-interval paths.** Precomposition with `unitToCircle` is a
homeomorphism `C(Circle, Q) ≃ₜ ClosedUnitPath Q`. -/
def circleMapHomeomorphClosedUnitPath : C(Circle, Q) ≃ₜ ClosedUnitPath Q :=
  (ContinuousMap.homeomorphFactorsThrough unitToCircle unitToCircle_surjective).trans
    { toFun g := ⟨g.1, (factorsThrough_unitToCircle_iff g.1).1 g.2⟩
      invFun p := ⟨p.1, (factorsThrough_unitToCircle_iff p.1).2 p.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }

@[simp]
theorem coe_circleMapHomeomorphClosedUnitPath (γ : C(Circle, Q)) :
    (circleMapHomeomorphClosedUnitPath γ : C(I, Q)) = γ.comp unitToCircle := by
  rw [circleMapHomeomorphClosedUnitPath, Homeomorph.trans_apply]
  exact ContinuousMap.homeomorphFactorsThrough_apply unitToCircle unitToCircle_surjective γ

theorem circleMapHomeomorphClosedUnitPath_apply (γ : C(Circle, Q)) (t : I) :
    (circleMapHomeomorphClosedUnitPath γ).1 t = γ (unitToCircle t) := by
  rw [coe_circleMapHomeomorphClosedUnitPath, ContinuousMap.comp_apply]

@[simp]
theorem circleMapHomeomorphClosedUnitPath_symm_unitToCircle (p : ClosedUnitPath Q) (t : I) :
    circleMapHomeomorphClosedUnitPath.symm p (unitToCircle t) = p.1 t := by
  have h := circleMapHomeomorphClosedUnitPath_apply (circleMapHomeomorphClosedUnitPath.symm p) t
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem circleMapHomeomorphClosedUnitPath_symm_one (p : ClosedUnitPath Q) :
    circleMapHomeomorphClosedUnitPath.symm p 1 = p.1 0 := by
  rw [← unitToCircle_zero, circleMapHomeomorphClosedUnitPath_symm_unitToCircle]

@[simp]
theorem circleMapHomeomorphClosedUnitPath_const (q : Q) :
    circleMapHomeomorphClosedUnitPath (ContinuousMap.const Circle q) =
      ⟨ContinuousMap.const I q, rfl⟩ :=
  Subtype.ext (ContinuousMap.ext fun _ ↦ circleMapHomeomorphClosedUnitPath_apply _ _)

@[simp]
theorem circleMapHomeomorphClosedUnitPath_symm_const (q : Q) :
    circleMapHomeomorphClosedUnitPath.symm ⟨ContinuousMap.const I q, rfl⟩ =
      ContinuousMap.const Circle q :=
  circleMapHomeomorphClosedUnitPath.injective (by simp)

/-- Restricting `circleMapHomeomorphClosedUnitPath` to the fibre of evaluation at `1 ∈ Circle` over
`x` gives the homeomorphism `BasedMap Circle Q 1 x ≃ₜ Path x x`. -/
def basedMapCircleOneHomeomorphPath (x : Q) : BasedMap Circle Q 1 x ≃ₜ Path x x :=
  (Homeomorph.subtype (q := fun p : ClosedUnitPath Q ↦ p.1 0 = x)
    circleMapHomeomorphClosedUnitPath fun γ ↦ by
      rw [← unitToCircle_zero, ← circleMapHomeomorphClosedUnitPath_apply]).trans
    { toFun p := ⟨p.1.1, p.2, p.1.2.symm.trans p.2⟩
      invFun ω := ⟨⟨ω.toContinuousMap, ω.source.trans ω.target.symm⟩, ω.source⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_induced_rng.2 continuous_subtype_val.subtype_val
      continuous_invFun :=
        ((continuous_induced_dom :
          Continuous (Path.toContinuousMap : Path x x → C(I, Q))).subtype_mk _).subtype_mk _ }

@[simp]
theorem basedMapCircleOneHomeomorphPath_apply (x : Q) (γ : BasedMap Circle Q 1 x) (t : I) :
    basedMapCircleOneHomeomorphPath x γ t = γ.1 (unitToCircle t) := by
  simp [basedMapCircleOneHomeomorphPath]

@[simp]
theorem basedMapCircleOneHomeomorphPath_symm_unitToCircle (x : Q) (ω : Path x x) (t : I) :
    ((basedMapCircleOneHomeomorphPath x).symm ω).1 (unitToCircle t) = ω t := by
  have h := basedMapCircleOneHomeomorphPath_apply x ((basedMapCircleOneHomeomorphPath x).symm ω) t
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem basedMapCircleOneHomeomorphPath_symm_refl (x : Q) :
    (basedMapCircleOneHomeomorphPath x).symm (Path.refl x) = ⟨ContinuousMap.const Circle x, rfl⟩ :=
  (basedMapCircleOneHomeomorphPath x).injective (by ext t; simp)

/-- The underlying circle map of `(basedMapCircleOneHomeomorphPath x).symm ω` agrees with
`Path.toCircle ω`. -/
theorem coe_basedMapCircleOneHomeomorphPath_symm (x : Q) (ω : Path x x) :
    ((basedMapCircleOneHomeomorphPath x).symm ω).1 = ω.toCircle := by
  ext z
  obtain ⟨t, rfl⟩ := unitToCircle_surjective z
  rw [basedMapCircleOneHomeomorphPath_symm_unitToCircle, unitToCircle_apply, ω.toCircle_exp]

/-! ### Basepoint evaluation and `unitPathsBetween` on contractible free loops -/

/-- Basepoint evaluation `𝓛₀Q → Q` at `1 ∈ Circle`. -/
def basepointContractibleLoop : C(contractibleLoops Q, Q) :=
  (mappingSpaceEval (1 : Circle)).comp (ContinuousMap.subtypeVal (contractibleLoops Q))

@[simp]
theorem basepointContractibleLoop_apply (γ : contractibleLoops Q) :
    basepointContractibleLoop γ = γ.1 1 := by
  simp [basepointContractibleLoop]

theorem basepointContractibleLoop_constContractibleLoop (q : Q) :
    basepointContractibleLoop (constContractibleLoop q) = q := by
  simp [basepointContractibleLoop_apply]

@[simp]
theorem basepointContractibleLoop_comp_constContractibleLoop :
    (basepointContractibleLoop (Q := Q)).comp constContractibleLoop = ContinuousMap.id Q :=
  ContinuousMap.ext basepointContractibleLoop_constContractibleLoop

/-- A circle loop is contractible if and only if it is joined in `C(Circle, Q)` to the constant
loop at its own basepoint `γ 1`. -/
theorem mem_contractibleLoops_iff_joined_const {γ : C(Circle, Q)} :
    γ ∈ contractibleLoops Q ↔ Joined γ (ContinuousMap.const Circle (γ 1)) := by
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, fun h ↦ ⟨γ 1, h⟩⟩
  have hc := (hq.map (mappingSpaceEval (1 : Circle)).continuous).map
    (ContinuousMap.continuous_const' (X := Circle) (Y := Q))
  simp only [mappingSpaceEval_apply, ContinuousMap.const_apply] at hc
  exact hq.trans hc.symm

/-- `constContractibleLoop` identifies `Q` homeomorphically with its image in `𝓛₀Q`, with explicit
continuous inverse given by evaluation at `1 ∈ Circle`. -/
def constContractibleLoopRangeHomeomorph :
    Q ≃ₜ Set.range (constContractibleLoop (Q := Q)) where
  toFun q := ⟨constContractibleLoop q, q, rfl⟩
  invFun γ := basepointContractibleLoop γ.1
  left_inv := basepointContractibleLoop_constContractibleLoop
  right_inv := by
    rintro ⟨_, q, rfl⟩
    exact Subtype.ext (congrArg constContractibleLoop
      (basepointContractibleLoop_constContractibleLoop q))
  continuous_toFun := constContractibleLoop.continuous.subtype_mk _
  continuous_invFun := basepointContractibleLoop.continuous.comp continuous_subtype_val

@[simp]
theorem coe_constContractibleLoopRangeHomeomorph (q : Q) :
    (constContractibleLoopRangeHomeomorph q : contractibleLoops Q) = constContractibleLoop q :=
  (rfl)

@[simp]
theorem constContractibleLoopRangeHomeomorph_symm_apply
    (γ : Set.range (constContractibleLoop (Q := Q))) :
    constContractibleLoopRangeHomeomorph.symm γ = basepointContractibleLoop γ.1 :=
  (rfl)

/-- `ContractibleConstLoopPath Q` is canonically homeomorphic to `unitPathsBetween` from
`range constContractibleLoop` to `range constContractibleLoop` in `𝓛₀Q`. -/
def contractibleConstLoopPathHomeomorphUnitPathsBetween :
    ContractibleConstLoopPath Q ≃ₜ
      unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
        (Set.range (constContractibleLoop (Q := Q))) where
  toFun p := ⟨p.1, (mem_unitPathsBetween _ _).2
    ⟨let ⟨q, hq⟩ := p.2.1; ⟨q, hq.symm⟩, let ⟨q, hq⟩ := p.2.2; ⟨q, hq.symm⟩⟩⟩
  invFun r :=
    let hr := (mem_unitPathsBetween _ _).1 r.2
    ⟨r.1, ⟨let ⟨q, hq⟩ := hr.1; ⟨q, hq.symm⟩, let ⟨q, hq⟩ := hr.2; ⟨q, hq.symm⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coe_contractibleConstLoopPathHomeomorphUnitPathsBetween (p : ContractibleConstLoopPath Q) :
    (contractibleConstLoopPathHomeomorphUnitPathsBetween p : C(I, contractibleLoops Q)) = p.1 :=
  (rfl)

@[simp]
theorem coe_contractibleConstLoopPathHomeomorphUnitPathsBetween_symm
    (r : unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q)))) :
    (contractibleConstLoopPathHomeomorphUnitPathsBetween.symm r).1 = r.1 :=
  (rfl)

/-- `BasedContractibleConstLoopPath Q x` is canonically homeomorphic to `unitPathsBetween` from
`{constContractibleLoop x}` to `range constContractibleLoop` in `𝓛₀Q`. -/
def basedContractibleConstLoopPathHomeomorphUnitPathsBetween (x : Q) :
    BasedContractibleConstLoopPath Q x ≃ₜ
      unitPathsBetween {constContractibleLoop x}
        (Set.range (constContractibleLoop (Q := Q))) where
  toFun p := ⟨p.1.1, (mem_unitPathsBetween _ _).2 ⟨p.2, let ⟨q, hq⟩ := p.1.2.2; ⟨q, hq.symm⟩⟩⟩
  invFun r :=
    let hr := (mem_unitPathsBetween _ _).1 r.2
    ⟨⟨r.1, ⟨⟨x, hr.1⟩, let ⟨q, hq⟩ := hr.2; ⟨q, hq.symm⟩⟩⟩, hr.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem coe_basedContractibleConstLoopPathHomeomorphUnitPathsBetween (x : Q)
    (p : BasedContractibleConstLoopPath Q x) :
    (basedContractibleConstLoopPathHomeomorphUnitPathsBetween x p : C(I, contractibleLoops Q)) =
      p.1.1 :=
  (rfl)

@[simp]
theorem coe_basedContractibleConstLoopPathHomeomorphUnitPathsBetween_symm (x : Q)
    (r : unitPathsBetween {constContractibleLoop x}
      (Set.range (constContractibleLoop (Q := Q)))) :
    ((basedContractibleConstLoopPathHomeomorphUnitPathsBetween x).symm r).1.1 = r.1 :=
  (rfl)

end TauCeti
