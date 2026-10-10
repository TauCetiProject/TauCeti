/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore
public import Mathlib.Topology.Connected.PathConnected

/-!
# The free Moore loop space

The **free Moore loops** in `X` are the Moore paths whose two end points agree: the free loop
space `𝓛X`, with the evaluation `basepoint : 𝓛X → X` at the common end point.  The based Moore
loops at `x` are the fibre of `basepoint` over `x` (`MooreLoopSpace.range_toFreeLoop`).

The constant loops of length zero form a closed embedding `X → 𝓛X`, a section of `basepoint`
(`isClosedEmbedding_const`): they are exactly the loops of length zero, and the length is
continuous.

A free loop is **contractible** when it is joined, in `𝓛X`, to a constant loop, that is, freely
homotopic to a constant loop through Moore loops of varying lengths.  The contractible loops form
the subspace `𝓛₀X = contractibleLoops X`; for a path-connected `X` it is the path component of any
constant loop, and the constant loops `X → 𝓛₀X` are again a closed embedding
(`isClosedEmbedding_constContractible`).

## Main definitions

* `TauCeti.MooreFreeLoopSpace X`: the free Moore loops `𝓛X`, with `basepoint` and `length`.
* `TauCeti.MooreFreeLoopSpace.const x`: the constant loop at `x` of length zero.
* `TauCeti.MooreLoopSpace.toFreeLoop`: a based Moore loop as a free loop.
* `TauCeti.MooreFreeLoopSpace.contractibleLoops X`: the contractible free loops `𝓛₀X`, and
  `TauCeti.MooreFreeLoopSpace.constContractible x`, the constant loop at `x` as a point of `𝓛₀X`.

## Main results

* `TauCeti.MooreFreeLoopSpace.isClosedEmbedding_const`,
  `TauCeti.MooreFreeLoopSpace.isClosedEmbedding_constContractible`: the constant loops are a
  closed embedding of `X` into `𝓛X` and into `𝓛₀X`.
* `TauCeti.MooreLoopSpace.isEmbedding_toFreeLoop`, `TauCeti.MooreLoopSpace.range_toFreeLoop`: the
  based loops at `x` are the fibre of `basepoint` over `x`.
* `TauCeti.MooreFreeLoopSpace.contractibleLoops_eq_pathComponent`: for a path-connected `X`, the
  contractible loops are the path component of any constant loop.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7.1.
-/

public noncomputable section

open scoped NNReal
open Topology

namespace TauCeti

/-- The **free Moore loops** in `X`: the Moore paths whose two end points agree.  This is the free
loop space `𝓛X`, with the subspace topology of the Moore paths. -/
structure MooreFreeLoopSpace (X : Type*) [TopologicalSpace X] where
  /-- The underlying Moore path. -/
  toMoorePath : MoorePath X
  /-- The loop ends where it starts. -/
  target_eq_source : toMoorePath.target = toMoorePath.source

namespace MooreFreeLoopSpace

variable {X : Type*} [TopologicalSpace X]

theorem toMoorePath_injective :
    Function.Injective (toMoorePath : MooreFreeLoopSpace X → MoorePath X) := by
  rintro ⟨γ, _⟩ ⟨δ, _⟩ rfl
  rfl

@[ext]
theorem ext {γ δ : MooreFreeLoopSpace X} (h : γ.toMoorePath = δ.toMoorePath) : γ = δ :=
  toMoorePath_injective h

/-- Free Moore loops carry the subspace topology of the Moore paths. -/
instance : TopologicalSpace (MooreFreeLoopSpace X) :=
  TopologicalSpace.induced toMoorePath inferInstance

theorem isEmbedding_toMoorePath :
    IsEmbedding (toMoorePath : MooreFreeLoopSpace X → MoorePath X) :=
  ⟨⟨rfl⟩, toMoorePath_injective⟩

@[fun_prop]
theorem continuous_toMoorePath : Continuous (toMoorePath : MooreFreeLoopSpace X → MoorePath X) :=
  isEmbedding_toMoorePath.continuous

/-- The base point of a free loop: its common starting and end point. -/
def basepoint (γ : MooreFreeLoopSpace X) : X :=
  γ.toMoorePath.source

@[simp]
theorem source_toMoorePath (γ : MooreFreeLoopSpace X) : γ.toMoorePath.source = γ.basepoint :=
  (rfl)

@[simp]
theorem target_toMoorePath (γ : MooreFreeLoopSpace X) : γ.toMoorePath.target = γ.basepoint :=
  γ.target_eq_source

@[fun_prop]
theorem continuous_basepoint : Continuous (basepoint : MooreFreeLoopSpace X → X) :=
  MoorePath.continuous_source.comp continuous_toMoorePath

/-- The length of a free loop. -/
def length (γ : MooreFreeLoopSpace X) : ℝ≥0 :=
  γ.toMoorePath.length

@[simp]
theorem length_toMoorePath (γ : MooreFreeLoopSpace X) : γ.toMoorePath.length = γ.length :=
  (rfl)

@[fun_prop]
theorem continuous_length : Continuous (length : MooreFreeLoopSpace X → ℝ≥0) :=
  MoorePath.continuous_length.comp continuous_toMoorePath

/-! ### Constant loops -/

/-- The constant loop at `x`, of length zero. -/
def const (x : X) : MooreFreeLoopSpace X :=
  ⟨MoorePath.refl x, by rw [MoorePath.target_refl, MoorePath.source_refl]⟩

@[simp]
theorem toMoorePath_const (x : X) : (const x).toMoorePath = MoorePath.refl x :=
  (rfl)

@[simp]
theorem basepoint_const (x : X) : (const x).basepoint = x :=
  MoorePath.source_refl x

@[simp]
theorem length_const (x : X) : (const x).length = 0 :=
  MoorePath.length_refl x

@[fun_prop]
theorem continuous_const : Continuous (const : X → MooreFreeLoopSpace X) :=
  isEmbedding_toMoorePath.continuous_iff.2 MoorePath.continuous_refl

/-- A free loop of length zero is the constant loop at its base point. -/
theorem eq_const_of_length_eq_zero {γ : MooreFreeLoopSpace X} (h : γ.length = 0) :
    γ = const γ.basepoint :=
  ext (MoorePath.eq_refl_of_length_eq_zero h)

/-- The constant loops are exactly the loops of length zero. -/
theorem range_const : Set.range (const : X → MooreFreeLoopSpace X) = {γ | γ.length = 0} := by
  ext γ
  constructor
  · rintro ⟨x, rfl⟩
    exact length_const x
  · exact fun h ↦ ⟨γ.basepoint, (eq_const_of_length_eq_zero h).symm⟩

/-- The constant loops form a closed embedding `X → 𝓛X`, a section of `basepoint`. -/
theorem isClosedEmbedding_const : IsClosedEmbedding (const : X → MooreFreeLoopSpace X) where
  toIsEmbedding := IsEmbedding.of_leftInverse basepoint_const continuous_basepoint continuous_const
  isClosed_range := by
    rw [range_const]
    exact isClosed_eq continuous_length _root_.continuous_const

end MooreFreeLoopSpace

/-! ### Based loops as free loops -/

namespace MooreLoopSpace

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- A based Moore loop at `x`, as a free loop. -/
def toFreeLoop (γ : MooreLoopSpace X x) : MooreFreeLoopSpace X :=
  ⟨γ.toMoorePath, by rw [γ.target_eq, γ.source_eq]⟩

@[simp]
theorem toMoorePath_toFreeLoop (γ : MooreLoopSpace X x) :
    γ.toFreeLoop.toMoorePath = γ.toMoorePath :=
  (rfl)

@[simp]
theorem basepoint_toFreeLoop (γ : MooreLoopSpace X x) : γ.toFreeLoop.basepoint = x :=
  γ.source_eq

theorem toFreeLoop_injective :
    Function.Injective (toFreeLoop : MooreLoopSpace X x → MooreFreeLoopSpace X) :=
  fun _ _ h ↦ ext (congrArg MooreFreeLoopSpace.toMoorePath h)

/-- The based loops at `x` embed into the free loops. -/
theorem isEmbedding_toFreeLoop :
    IsEmbedding (toFreeLoop : MooreLoopSpace X x → MooreFreeLoopSpace X) :=
  (MooreFreeLoopSpace.isEmbedding_toMoorePath.of_comp_iff (f := toFreeLoop)).1
    isEmbedding_toMoorePath

@[fun_prop]
theorem continuous_toFreeLoop :
    Continuous (toFreeLoop : MooreLoopSpace X x → MooreFreeLoopSpace X) :=
  isEmbedding_toFreeLoop.continuous

/-- The based loops at `x` are the fibre of `basepoint` over `x`. -/
theorem range_toFreeLoop :
    Set.range (toFreeLoop : MooreLoopSpace X x → MooreFreeLoopSpace X) =
      MooreFreeLoopSpace.basepoint ⁻¹' {x} := by
  ext γ
  constructor
  · rintro ⟨δ, rfl⟩
    exact basepoint_toFreeLoop δ
  · exact fun h ↦ ⟨⟨γ.toMoorePath, h, γ.target_eq_source.trans h⟩, rfl⟩

end MooreLoopSpace

namespace MooreFreeLoopSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### Contractible loops -/

variable (X) in
/-- The **contractible** free loops, `𝓛₀X`: the loops joined in `𝓛X` to a constant loop, that is,
freely homotopic to a constant loop. -/
def contractibleLoops : Set (MooreFreeLoopSpace X) :=
  {γ | ∃ x, Joined (const x) γ}

theorem mem_contractibleLoops {γ : MooreFreeLoopSpace X} :
    γ ∈ contractibleLoops X ↔ ∃ x, Joined (const x) γ :=
  Iff.rfl

theorem const_mem_contractibleLoops (x : X) : const x ∈ contractibleLoops X :=
  ⟨x, Joined.refl _⟩

/-- A loop joined to a contractible loop is contractible. -/
theorem mem_contractibleLoops_of_joined {γ δ : MooreFreeLoopSpace X}
    (hγ : γ ∈ contractibleLoops X) (h : Joined γ δ) : δ ∈ contractibleLoops X :=
  let ⟨x, hx⟩ := hγ
  ⟨x, hx.trans h⟩

/-- A contractible loop is joined to the constant loop at its own base point. -/
theorem mem_contractibleLoops_iff_joined_const {γ : MooreFreeLoopSpace X} :
    γ ∈ contractibleLoops X ↔ Joined (const γ.basepoint) γ := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun h ↦ ⟨_, h⟩⟩
  -- `basepoint` carries a path from `const x` to `γ` to a path from `x` to `γ.basepoint` in `X`,
  -- hence to a path of constant loops from `const x` to `const γ.basepoint`.
  have hc := (hx.map continuous_basepoint).map continuous_const
  rw [basepoint_const] at hc
  exact hc.symm.trans hx

theorem contractibleLoops_eq_iUnion_pathComponent :
    contractibleLoops X = ⋃ x, pathComponent (const x) := by
  ext γ
  simp only [mem_contractibleLoops, Set.mem_iUnion, mem_pathComponent_iff]

/-- For a path-connected `X`, the contractible loops are the path component of any constant
loop. -/
theorem contractibleLoops_eq_pathComponent [PathConnectedSpace X] (x : X) :
    contractibleLoops X = pathComponent (const x) := by
  ext γ
  rw [mem_pathComponent_iff, mem_contractibleLoops_iff_joined_const]
  have hc : Joined (const x) (const γ.basepoint) :=
    (PathConnectedSpace.joined x γ.basepoint).map continuous_const
  exact ⟨hc.trans, hc.symm.trans⟩

theorem isPathConnected_contractibleLoops [PathConnectedSpace X] :
    IsPathConnected (contractibleLoops X) := by
  obtain ⟨x⟩ := PathConnectedSpace.nonempty (X := X)
  rw [contractibleLoops_eq_pathComponent x]
  exact isPathConnected_pathComponent

/-- The constant loop at `x`, as a point of `𝓛₀X`. -/
def constContractible : X → contractibleLoops X :=
  Set.codRestrict const (contractibleLoops X) const_mem_contractibleLoops

@[simp]
theorem coe_constContractible (x : X) : (constContractible x : MooreFreeLoopSpace X) = const x :=
  (rfl)

@[fun_prop]
theorem continuous_constContractible : Continuous (constContractible : X → contractibleLoops X) :=
  continuous_const.codRestrict _

/-- The constant loops form a closed embedding `X → 𝓛₀X`. -/
theorem isClosedEmbedding_constContractible :
    IsClosedEmbedding (constContractible : X → contractibleLoops X) where
  toIsEmbedding := isClosedEmbedding_const.isEmbedding.codRestrict _ _
  isClosed_range := by
    rw [constContractible, Set.range_codRestrict]
    exact isClosedEmbedding_const.isClosed_range.preimage continuous_subtype_val

end MooreFreeLoopSpace

end TauCeti
