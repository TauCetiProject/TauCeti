/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.CompactOpen
public import TauCeti.Topology.ContinuousMap.Precomp
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.MappingSpace.Group
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup
import TauCeti.Topology.Homotopy.Homotopic.With
import TauCeti.Topology.PathComponent

/-!
# Paths of free loops, closed unit-interval paths, and contractible free loops

The free loop space of a space `Q` is the space `C(S¹, Q)` of maps from the circle, with the
compact-open topology. Precomposition with the standard quotient `unitToCircle : I → S¹`,
`t ↦ exp(2πit)`, identifies `C(S¹, Q)` homeomorphically with the subspace `ClosedUnitPath Q` of
closed unit-interval paths `{p : C(I, Q) // p 0 = p 1}` (`circleMapHomeomorphClosedUnitPath`),
compatibly with evaluation at `1 ∈ S¹`, constant loops, and the based loop fibre
`BasedMap Circle Q 1 x ≃ₜ Path x x` (`basedMapCircleOneHomeomorphPath`).

The free loop space of a topological group `G` is the product of the group and its based loop
space at `1`, `G × ΩG ≃ₜ C(S¹, G)` (`TauCeti.circleMapGroupHomeomorphLoopSpace`), through this
identification of loops based at `1 ∈ S¹` with paths.

Its subspace `𝓛₀Q` of **contractible** loops (`TauCeti.contractibleLoops`) consists of the loops
joined by a path in the free loop space to a constant loop, equivalently to the constant loop at
their own basepoint (`mem_contractibleLoops_iff_joined_const`), so `𝓛₀Q` is the union of the
path components of the constant loops (`pathComponent_const_subset_contractibleLoops`), and so is
open when the free loop space is locally path-connected (`TauCeti.isOpen_contractibleLoops`). It
contains the path component of each of its points
(`TauCeti.pathComponent_subset_contractibleLoops`), so it inherits local path-connectedness from
the free loop space (`TauCeti.locallyPathConnectedSpace_contractibleLoops`). For
a path-connected `Q` it is a single path component (`TauCeti.contractibleLoops_eq_pathComponent`),
so `𝓛₀Q` is path connected (`TauCeti.isPathConnected_contractibleLoops`). The
constant loops embed in `𝓛₀Q` (`TauCeti.isEmbedding_constContractibleLoop`), with retraction
`TauCeti.basepointContractibleLoop` given by evaluation at `1`. A path in the free loop space
that starts at a constant loop stays in `𝓛₀Q` (`TauCeti.constLoopPath_mem_contractibleLoops`),
so the paths from a constant loop to a constant loop, `TauCeti.ConstLoopPath`, are the same as
such paths in `𝓛₀Q` (`TauCeti.constLoopPathHomeomorph`).

## Main declarations

* `TauCeti.ClosedUnitPath`, `TauCeti.circleMapHomeomorphClosedUnitPath`:
  `C(Circle, Q) ≃ₜ {p : C(I, Q) // p 0 = p 1}`.
* `TauCeti.unitAddCircleMapHomeomorphClosedUnitPath`: the same for maps from `UnitAddCircle`.
* `GenLoop.exists_unitAddCircle_apply_eq`: a generalized loop of dimension one is traced by a map
  from `UnitAddCircle`.
* `TauCeti.basedMapCircleOneHomeomorphPath`: `BasedMap Circle Q 1 x ≃ₜ Path x x`.
* `TauCeti.circleMapGroupHomeomorphLoopSpace`: `G × ΩG ≃ₜ C(S¹, G)` for a topological group `G`,
  sending `(g, γ)` to the loop `t ↦ g γ(t)`, with the characteristic lemmas `_apply_unitToCircle`,
  `_symm_fst` and `_symm_snd_apply`.
* `Path.continuous_toCircle`: reading loops as circle maps is continuous.
* `Path.joined_toCircle_iff_homotopicWith`: two loops are joined in `C(Circle, Q)` exactly when
  they are homotopic through closed paths `I → Q`.
* `TauCeti.contractibleLoops`, `TauCeti.basepointContractibleLoop`: the contractible free loops
  `𝓛₀Q` and basepoint evaluation `𝓛₀Q → Q` at `1 ∈ Circle`.
* `TauCeti.constContractibleLoop`: the constant loops as a continuous map `Q → 𝓛₀Q`, an
  embedding by `TauCeti.isEmbedding_constContractibleLoop`.
* `TauCeti.isPathConnected_contractibleLoops`: `𝓛₀Q` is path connected when `Q` is.
* `TauCeti.locallyPathConnectedSpace_contractibleLoops`: `𝓛₀Q` is locally path-connected when
  `C(S¹, Q)` is.
* `TauCeti.ConstLoopPath`, `TauCeti.ContractibleConstLoopPath`, `TauCeti.constLoopPathHomeomorph`,
  `TauCeti.BasedConstLoopPath`, `TauCeti.BasedContractibleConstLoopPath`.
-/

public section

noncomputable section

open scoped unitInterval Topology.Homotopy

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
    p.val t ∈ contractibleLoops Q := by
  obtain ⟨⟨q, hq⟩, -⟩ := p.property
  have h : Joined (0 : I) t := ⟨⟨⟨fun s => s * t, by fun_prop⟩, by simp, by simp⟩⟩
  have h' := h.map p.val.continuous
  rw [hq] at h'
  exact ⟨q, h'.symm⟩

variable (Q) in
/-- The paths in the free loop space from the constant loop at `x` to a constant loop. -/
abbrev BasedConstLoopPath (x : Q) : Type _ :=
  {p : ConstLoopPath Q // p.val 0 = ContinuousMap.const Circle x}

variable (Q) in
/-- The paths in the contractible free loops `𝓛₀Q` from a constant loop to a constant loop. -/
abbrev ContractibleConstLoopPath : Type _ :=
  {p : C(I, contractibleLoops Q) //
    (∃ q, p 0 = constContractibleLoop q) ∧ ∃ q, p 1 = constContractibleLoop q}

/-- A path of free loops from a constant loop to a constant loop is a path in the contractible free
loops `𝓛₀Q`. -/
def constLoopPathHomeomorph : ConstLoopPath Q ≃ₜ ContractibleConstLoopPath Q where
  toFun p := ⟨⟨fun t => ⟨p.val t, constLoopPath_mem_contractibleLoops p t⟩,
      p.val.continuous.subtype_mk _⟩,
    ⟨p.property.1.choose, Subtype.ext p.property.1.choose_spec⟩, ⟨p.property.2.choose,
        Subtype.ext p.property.2.choose_spec⟩⟩
  invFun r := ⟨(ContinuousMap.mk Subtype.val continuous_subtypeVal).comp r.val,
    ⟨r.property.1.choose, congrArg Subtype.val r.property.1.choose_spec⟩,
    ⟨r.property.2.choose, congrArg Subtype.val r.property.2.choose_spec⟩⟩
  -- both composites rebuild the same data, by the definitional eta rules for subtypes
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    refine ((ContinuousMap.isInducing_postcomp (ContinuousMap.mk Subtype.val
      continuous_subtypeVal) Topology.IsInducing.subtypeVal).continuous_iff).2 ?_
    exact continuous_subtypeVal
  continuous_invFun :=
    continuous_induced_rng.2 ((ContinuousMap.continuous_postcomp _).comp continuous_subtypeVal)

/-- The path of contractible loops, read in the free loop space, is the original path. -/
@[simp]
theorem coe_constLoopPathHomeomorph (p : ConstLoopPath Q) (t : I) :
    ((constLoopPathHomeomorph p).val t : C(Circle, Q)) = p.val t := by
  rw [constLoopPathHomeomorph]
  -- the underlying free loop at `t` is `p.1 t`, by construction of `toFun`
  rfl

variable (Q) in
/-- The paths in the contractible free loops from the constant loop at `x` to a constant loop. -/
abbrev BasedContractibleConstLoopPath (x : Q) : Type _ :=
  {p : ContractibleConstLoopPath Q // p.val 0 = constContractibleLoop x}

/-- The inverse of `constLoopPathHomeomorph` reads a path in the contractible loops in the free
loop space. -/
@[simp]
theorem coe_constLoopPathHomeomorph_symm (r : ContractibleConstLoopPath Q) (t : I) :
    (constLoopPathHomeomorph.symm r).val t = (r.val t : C(Circle, Q)) := by
  have h := coe_constLoopPathHomeomorph (constLoopPathHomeomorph.symm r) t
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-! ### Closed unit-interval paths and circle maps -/

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
  (ContinuousMap.homeomorphFactorsThrough unitToCircle unitToCircle.continuous.isProperMap
      unitToCircle_surjective).trans
    { toFun g := ⟨g.val, (factorsThrough_unitToCircle_iff g.val).1 g.property⟩
      invFun p := ⟨p.val, (factorsThrough_unitToCircle_iff p.val).2 p.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_subtypeVal.subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtype_mk _ }

@[simp]
theorem coe_circleMapHomeomorphClosedUnitPath (γ : C(Circle, Q)) :
    (circleMapHomeomorphClosedUnitPath γ : C(I, Q)) = γ.comp unitToCircle := by
  rw [circleMapHomeomorphClosedUnitPath, Homeomorph.trans_apply]
  exact ContinuousMap.homeomorphFactorsThrough_apply unitToCircle
    unitToCircle.continuous.isProperMap unitToCircle_surjective γ

theorem circleMapHomeomorphClosedUnitPath_apply (γ : C(Circle, Q)) (t : I) :
    (circleMapHomeomorphClosedUnitPath γ).val t = γ (unitToCircle t) := by
  rw [coe_circleMapHomeomorphClosedUnitPath, ContinuousMap.comp_apply]

@[simp]
theorem circleMapHomeomorphClosedUnitPath_symm_unitToCircle (p : ClosedUnitPath Q) (t : I) :
    circleMapHomeomorphClosedUnitPath.symm p (unitToCircle t) = p.val t := by
  have h := circleMapHomeomorphClosedUnitPath_apply (circleMapHomeomorphClosedUnitPath.symm p) t
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem circleMapHomeomorphClosedUnitPath_symm_one (p : ClosedUnitPath Q) :
    circleMapHomeomorphClosedUnitPath.symm p 1 = p.val 0 := by
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

/-- **Maps from `UnitAddCircle` are closed unit-interval paths**:
`circleMapHomeomorphClosedUnitPath` after identifying `UnitAddCircle` with `Circle` by
`AddCircle.homeomorphCircle`. -/
def unitAddCircleMapHomeomorphClosedUnitPath : C(UnitAddCircle, Q) ≃ₜ ClosedUnitPath Q :=
  ((AddCircle.homeomorphCircle one_ne_zero).arrowCongr (Homeomorph.refl Q)).trans
    circleMapHomeomorphClosedUnitPath

@[simp]
theorem unitAddCircleMapHomeomorphClosedUnitPath_apply (γ : C(UnitAddCircle, Q)) (t : I) :
    (unitAddCircleMapHomeomorphClosedUnitPath γ).val t = γ ((t : ℝ) : UnitAddCircle) := by
  rw [unitAddCircleMapHomeomorphClosedUnitPath, Homeomorph.trans_apply,
    circleMapHomeomorphClosedUnitPath_apply]
  exact congrArg γ (homeomorphCircle_symm_unitToCircle t)

/-- The map from `UnitAddCircle` of a closed path `p` sends the class of `t` to `p t`. -/
@[simp]
theorem unitAddCircleMapHomeomorphClosedUnitPath_symm_apply (p : ClosedUnitPath Q) (t : I) :
    unitAddCircleMapHomeomorphClosedUnitPath.symm p ((t : ℝ) : UnitAddCircle) = p.val t := by
  rw [← unitAddCircleMapHomeomorphClosedUnitPath_apply, Homeomorph.apply_symm_apply]

/-- A generalized loop of dimension one is traced by a map from the circle `ℝ / ℤ`. -/
theorem _root_.GenLoop.exists_unitAddCircle_apply_eq {x : Q} (p : Ω^ (Fin 1) Q x) :
    ∃ ℓ : C(UnitAddCircle, Q), ∀ t : I, ℓ (t : ℝ) = p (fun _ ↦ t) :=
  ⟨unitAddCircleMapHomeomorphClosedUnitPath.symm
      ⟨⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩,
        (GenLoop.boundary p _ ⟨0, Or.inl rfl⟩).trans
          (GenLoop.boundary p _ ⟨0, Or.inr rfl⟩).symm⟩,
    fun t ↦ unitAddCircleMapHomeomorphClosedUnitPath_symm_apply _ t⟩

/-- Restricting `circleMapHomeomorphClosedUnitPath` to the fibre of evaluation at `1 ∈ Circle` over
`x` gives the homeomorphism `BasedMap Circle Q 1 x ≃ₜ Path x x`. -/
def basedMapCircleOneHomeomorphPath (x : Q) : BasedMap Circle Q 1 x ≃ₜ Path x x :=
  (Homeomorph.subtype (q := fun p : ClosedUnitPath Q ↦ p.val 0 = x)
    circleMapHomeomorphClosedUnitPath fun γ ↦ by
      rw [← unitToCircle_zero, ← circleMapHomeomorphClosedUnitPath_apply]).trans
    { toFun p := ⟨p.val.val, p.property, p.val.property.symm.trans p.property⟩
      invFun ω := ⟨⟨ω.toContinuousMap, ω.source.trans ω.target.symm⟩, ω.source⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_induced_rng.2 continuous_subtypeVal.subtypeVal
      continuous_invFun :=
        ((continuous_induced_dom :
          Continuous (Path.toContinuousMap : Path x x → C(I, Q))).subtype_mk _).subtype_mk _ }

@[simp]
theorem basedMapCircleOneHomeomorphPath_apply (x : Q) (γ : BasedMap Circle Q 1 x) (t : I) :
    basedMapCircleOneHomeomorphPath x γ t = γ.val (unitToCircle t) := by
  simp [basedMapCircleOneHomeomorphPath]

@[simp]
theorem basedMapCircleOneHomeomorphPath_symm_unitToCircle (x : Q) (ω : Path x x) (t : I) :
    ((basedMapCircleOneHomeomorphPath x).symm ω).val (unitToCircle t) = ω t := by
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
    ((basedMapCircleOneHomeomorphPath x).symm ω).val = ω.toCircle := by
  ext z
  obtain ⟨t, rfl⟩ := unitToCircle_surjective z
  rw [basedMapCircleOneHomeomorphPath_symm_unitToCircle, ω.toCircle_unitToCircle]

/-! ### The free loop space of a topological group -/

section TopologicalGroup

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **The free loop space of a topological group is a product**, `G × ΩG ≃ₜ C(S¹, G)`: the pair
`(g, γ)` of a group element and a loop at `1` goes to the free loop `t ↦ g γ(t)`, read on the
circle through `TauCeti.basedMapCircleOneHomeomorphPath`. The inverse records the value at `1 ∈ S¹`
and translates the loop back to `1`. -/
def circleMapGroupHomeomorphLoopSpace : G × Path (1 : G) 1 ≃ₜ C(Circle, G) :=
  (Homeomorph.prodCongr (Homeomorph.refl G) (basedMapCircleOneHomeomorphPath (1 : G)).symm).trans
    (mappingSpaceGroupHomeomorph 1)

variable {G}

/-- The free loop of `(g, γ)` at the image `unitToCircle t` of a time `t` is `g γ(t)`. -/
@[simp]
theorem circleMapGroupHomeomorphLoopSpace_apply_unitToCircle (g : G) (γ : Path (1 : G) 1)
    (t : unitInterval) :
    circleMapGroupHomeomorphLoopSpace G (g, γ) (unitToCircle t) = g * γ t := by
  simp [circleMapGroupHomeomorphLoopSpace]

/-- The group coordinate of a free loop in `G` is its value at `1 ∈ S¹`. -/
@[simp]
theorem circleMapGroupHomeomorphLoopSpace_symm_fst (f : C(Circle, G)) :
    ((circleMapGroupHomeomorphLoopSpace G).symm f).1 = f 1 :=
  mappingSpaceGroupHomeomorph_symm_fst 1 f

/-- The loop coordinate of a free loop `f` in `G` is the loop `t ↦ f(1)⁻¹ f(t)` at `1`. -/
@[simp]
theorem circleMapGroupHomeomorphLoopSpace_symm_snd_apply (f : C(Circle, G)) (t : unitInterval) :
    ((circleMapGroupHomeomorphLoopSpace G).symm f).2 t = (f 1)⁻¹ * f (unitToCircle t) := by
  simp [circleMapGroupHomeomorphLoopSpace]

end TopologicalGroup

/-! ### Basepoint evaluation on contractible free loops -/

/-- Basepoint evaluation `𝓛₀Q → Q` at `1 ∈ Circle`. -/
def basepointContractibleLoop : C(contractibleLoops Q, Q) :=
  (mappingSpaceEval (1 : Circle)).comp (ContinuousMap.subtypeVal (contractibleLoops Q))

@[simp]
theorem basepointContractibleLoop_apply (γ : contractibleLoops Q) :
    basepointContractibleLoop γ = γ.val 1 := by
  simp [basepointContractibleLoop]

theorem basepointContractibleLoop_constContractibleLoop (q : Q) :
    basepointContractibleLoop (constContractibleLoop q) = q := by
  simp [basepointContractibleLoop_apply]

@[simp]
theorem basepointContractibleLoop_comp_constContractibleLoop :
    (basepointContractibleLoop (Q := Q)).comp constContractibleLoop = ContinuousMap.id Q :=
  ContinuousMap.ext basepointContractibleLoop_constContractibleLoop

/-- The contractible free loops contain the path component of every constant loop. -/
theorem pathComponent_const_subset_contractibleLoops (q : Q) :
    pathComponent (ContinuousMap.const Circle q) ⊆ contractibleLoops Q :=
  fun _ h ↦ mem_contractibleLoops_iff.2 ⟨q, h.symm⟩

/-- The contractible free loops contain the path component of each of their points. -/
theorem pathComponent_subset_contractibleLoops {γ : C(Circle, Q)} (hγ : γ ∈ contractibleLoops Q) :
    pathComponent γ ⊆ contractibleLoops Q := by
  obtain ⟨q, hq⟩ := mem_contractibleLoops_iff.1 hγ
  exact (pathComponent_congr hq.symm).subset.trans (pathComponent_const_subset_contractibleLoops q)

/-- For a path-connected `Q`, the contractible free loops are the path component of any constant
loop. -/
theorem contractibleLoops_eq_pathComponent [PathConnectedSpace Q] (q : Q) :
    contractibleLoops Q = pathComponent (ContinuousMap.const Circle q) := by
  refine Set.Subset.antisymm (fun γ ⟨q', hq'⟩ ↦ ?_) (pathComponent_const_subset_contractibleLoops q)
  exact ((PathConnectedSpace.joined q q').map
    (ContinuousMap.continuous_const' (X := Circle) (Y := Q))).trans hq'.symm

variable (Q) in
/-- For a path-connected `Q`, the contractible free loops `𝓛₀Q` are path connected. -/
theorem isPathConnected_contractibleLoops [PathConnectedSpace Q] :
    IsPathConnected (contractibleLoops Q) := by
  obtain ⟨q⟩ := PathConnectedSpace.nonempty (X := Q)
  rw [contractibleLoops_eq_pathComponent q]
  exact isPathConnected_pathComponent

/-- For a path-connected `Q`, the contractible free loops `𝓛₀Q` form a path-connected space. -/
instance pathConnectedSpace_contractibleLoops [PathConnectedSpace Q] :
    PathConnectedSpace (contractibleLoops Q) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_contractibleLoops Q)

/-- A circle loop is contractible if and only if it is joined in `C(Circle, Q)` to the constant
loop at its own basepoint `γ 1`. -/
theorem mem_contractibleLoops_iff_joined_const {γ : C(Circle, Q)} :
    γ ∈ contractibleLoops Q ↔ Joined γ (ContinuousMap.const Circle (γ 1)) := by
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, fun h ↦ ⟨γ 1, h⟩⟩
  have hc := (hq.map (mappingSpaceEval (1 : Circle)).continuous).map
    (ContinuousMap.continuous_const' (X := Circle) (Y := Q))
  simp only [mappingSpaceEval_apply, ContinuousMap.const_apply] at hc
  exact hq.trans hc.symm

variable (Q) in
/-- In a locally path-connected free loop space, the contractible free loops form an open set:
they are the union of the path components of the constant loops, and path components are open. -/
theorem isOpen_contractibleLoops [LocallyPathConnectedSpace C(Circle, Q)] :
    IsOpen (contractibleLoops Q) := by
  have : contractibleLoops Q = ⋃ q, pathComponent (ContinuousMap.const Circle q) := by
    ext γ
    simp only [mem_contractibleLoops_iff, Set.mem_iUnion]
    exact exists_congr fun _ => ⟨Joined.symm, Joined.symm⟩
  rw [this]
  exact isOpen_iUnion fun q => IsOpen.pathComponent _

/-- The contractible free loops `𝓛₀Q` are locally path-connected when the free loop space is:
they form an open subset of it. -/
instance locallyPathConnectedSpace_contractibleLoops [LocallyPathConnectedSpace C(Circle, Q)] :
    LocallyPathConnectedSpace (contractibleLoops Q) :=
  (isOpen_contractibleLoops Q).locallyPathConnectedSpace

end TauCeti

/-! ### Free loops as loops, and free homotopies of loops -/

section FreeLoop

variable {X : Type*} [TopologicalSpace X]

namespace Path

variable {x y : X}

/-- Reading loops at `x` as maps from the circle is continuous. -/
theorem continuous_toCircle (x : X) : Continuous fun γ : Path x x ↦ γ.toCircle := by
  simp_rw [← TauCeti.coe_basedMapCircleOneHomeomorphPath_symm]
  exact continuous_subtypeVal.comp (TauCeti.basedMapCircleOneHomeomorphPath x).symm.continuous

/-- **Free homotopy of loops is homotopy through closed paths.** Two loops, at possibly different
points, are joined by a path in `C(S¹, X)` exactly when they are homotopic as maps `I → X` through
maps taking the same value at `0` and at `1`. -/
theorem joined_toCircle_iff_homotopicWith (γ : Path x x) (γ' : Path y y) :
    Joined γ.toCircle γ'.toCircle ↔
      (γ : C(I, X)).HomotopicWith (γ' : C(I, X)) fun p ↦ p 0 = p 1 := by
  have h {z : X} (ω : Path z z) : TauCeti.circleMapHomeomorphClosedUnitPath ω.toCircle =
      ⟨ω, by simp⟩ := by
    ext t
    simp
  rw [← (TauCeti.circleMapHomeomorphClosedUnitPath (Q := X)).joined_iff, h, h,
    ContinuousMap.homotopicWith_iff_joined]

end Path

end FreeLoop
