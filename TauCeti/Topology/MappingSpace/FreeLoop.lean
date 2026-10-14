/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.UnitInterval

/-!
# Paths of free loops and the contractible free loops

The free loop space of a space `Q` is the space `C(S¹, Q)` of maps from the circle, with the
compact-open topology. Its subspace `𝓛₀Q` of **contractible** loops (`TauCeti.contractibleLoops`)
consists of the loops joined by a path in the free loop space to a constant loop. The constant
loops embed in `𝓛₀Q` (`TauCeti.isEmbedding_constContractibleLoop`). A path in the free loop space
that starts at a constant loop stays in `𝓛₀Q`
(`TauCeti.constLoopPath_mem_contractibleLoops`), so the paths from a constant loop to a constant
loop, `TauCeti.ConstLoopPath`, are the same as such paths in `𝓛₀Q`
(`TauCeti.constLoopPathHomeomorph`).

## Main declarations

* `TauCeti.contractibleLoops`: the contractible free loops `𝓛₀Q`.
* `TauCeti.constContractibleLoop`: the constant loops as a continuous map `Q → 𝓛₀Q`, an
  embedding by `TauCeti.isEmbedding_constContractibleLoop`.
* `TauCeti.ConstLoopPath`: the paths of free loops from a constant loop to a constant loop, and
  `TauCeti.ContractibleConstLoopPath` the paths in `𝓛₀Q` with the same end points.
* `TauCeti.constLoopPathHomeomorph`: the homeomorphism between the two.
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
  rfl

/-- The constant loops form a topological embedding `Q → 𝓛₀Q`: evaluation at the point
`1` of the circle is a continuous left inverse. -/
theorem isEmbedding_constContractibleLoop :
    Topology.IsEmbedding (constContractibleLoop (Q := Q)) :=
  Function.LeftInverse.isEmbedding (f := fun γ : contractibleLoops Q => (γ : C(Circle, Q)) 1)
    (fun _ => rfl) ((continuous_eval_const (1 : Circle)).comp continuous_subtype_val)
    constContractibleLoop.continuous

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

end TauCeti
