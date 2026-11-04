/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.MappingSpace.FreeLoop
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop

/-!
# Comparing Moore and circle-mapping free loop spaces

The free Moore loop space `MooreFreeLoopSpace X` (`𝓛X`) compares with the circle-mapping free loop
space `C(Circle, X)` by factoring through the closed unit-interval paths `ClosedUnitPath X`:

* `MooreFreeLoopSpace.toCircleMap` reparametrizes a free Moore loop `γ` to the closed unit-interval
  path `γ.toMoorePath.toUnitPath` and descends along `unitToCircle : I → Circle`;
* `MooreFreeLoopSpace.ofCircleMap` precomposes a circle map with `unitToCircle` and regards the
  resulting closed unit-interval path as a Moore loop of duration one;
* `toCircleMap ∘ ofCircleMap` is the identity on the nose (`toCircleMap_ofCircleMap`), while
  `ofCircleMap ∘ toCircleMap` is homotopic to the identity through basepoint-preserving maps via
  `MoorePath.unitHomotopy` (`MooreFreeLoopSpace.unitHomotopy`).

Accordingly `MooreFreeLoopSpace.fiberHomotopyEquivCircleMap` is a fibre homotopy equivalence over
`X` between `basepoint : 𝓛X → X` and evaluation at `1 ∈ Circle`, compatible with the based loop
comparison `MooreLoopSpace X x ≃ₕ Path x x ≃ₜ BasedMap Circle X 1 x` (`toCircleMap_toFreeLoop`,
`ofCircleMap_coe_basedMap`). Forward comparison sends constant Moore loops of duration zero to
constant circle loops (`toCircleMap_const`), and `constCircleHomotopy` shrinks the duration-one
image of constant circle loops back to duration zero over `X`.

Both comparison maps and `unitHomotopy` preserve the subspaces of contractible free loops, yielding
`MooreFreeLoopSpace.fiberHomotopyEquivContractibleLoops` over `X` between
`MooreFreeLoopSpace.contractibleLoops X` and `TauCeti.contractibleLoops X`, again compatible with
constant sections (`toCircleMapContractible_constContractible`, `constContractibleHomotopy`).

## Main declarations

* `TauCeti.MooreFreeLoopSpace.toCircleMap`, `TauCeti.MooreFreeLoopSpace.ofCircleMap`: comparison
  maps between `MooreFreeLoopSpace X` and `C(Circle, X)`.
* `TauCeti.MooreFreeLoopSpace.fiberHomotopyEquivCircleMap`,
  `TauCeti.MooreFreeLoopSpace.homotopyEquivCircleMap`: fibre homotopy equivalence over `X` and
  underlying homotopy equivalence `MooreFreeLoopSpace X ≃ₕ C(Circle, X)`.
* `TauCeti.MooreFreeLoopSpace.constCircleHomotopy`: basepoint-preserving homotopy comparing the
  constant-loop sections.
* `TauCeti.MooreFreeLoopSpace.fiberHomotopyEquivContractibleLoops`,
  `TauCeti.MooreFreeLoopSpace.homotopyEquivContractibleLoops`,
  `TauCeti.MooreFreeLoopSpace.constContractibleHomotopy`: restricted comparison on contractible
  free loops `𝓛₀X`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2 and §7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open scoped NNReal unitInterval ContinuousMap
open Topology unitInterval

namespace TauCeti

namespace MooreFreeLoopSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### Comparison with closed unit-interval paths and circle maps -/

/-- Reparametrize a free Moore loop to a closed path on the unit interval. -/
def toClosedUnitPath : C(MooreFreeLoopSpace X, ClosedUnitPath X) where
  toFun γ := ⟨γ.toMoorePath.toUnitPath,
    γ.toMoorePath.toUnitPath_zero.trans
      (γ.target_eq_source.symm.trans γ.toMoorePath.toUnitPath_one.symm)⟩
  continuous_toFun := (MoorePath.continuous_toUnitPath.comp continuous_toMoorePath).subtype_mk _

@[simp]
theorem coe_toClosedUnitPath (γ : MooreFreeLoopSpace X) :
    (toClosedUnitPath γ : C(I, X)) = γ.toMoorePath.toUnitPath :=
  (rfl)

theorem toClosedUnitPath_zero (γ : MooreFreeLoopSpace X) :
    (toClosedUnitPath γ).1 0 = γ.basepoint := by
  rw [coe_toClosedUnitPath, MoorePath.toUnitPath_zero, source_toMoorePath]

/-- Regard a closed path on the unit interval as a free Moore loop of duration one. -/
def ofClosedUnitPath : C(ClosedUnitPath X, MooreFreeLoopSpace X) where
  toFun p := ⟨MoorePath.ofUnitPath p.1,
    (MoorePath.target_ofUnitPath p.1).trans
      (p.2.symm.trans (MoorePath.source_ofUnitPath p.1).symm)⟩
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.2
    (MoorePath.continuous_ofUnitPath.comp continuous_subtype_val)

@[simp]
theorem toMoorePath_ofClosedUnitPath (p : ClosedUnitPath X) :
    (ofClosedUnitPath p).toMoorePath = MoorePath.ofUnitPath p.1 :=
  (rfl)

@[simp]
theorem basepoint_ofClosedUnitPath (p : ClosedUnitPath X) :
    (ofClosedUnitPath p).basepoint = p.1 0 := by
  rw [← source_toMoorePath, toMoorePath_ofClosedUnitPath, MoorePath.source_ofUnitPath]

@[simp]
theorem toClosedUnitPath_ofClosedUnitPath (p : ClosedUnitPath X) :
    toClosedUnitPath (ofClosedUnitPath p) = p :=
  Subtype.ext (MoorePath.toUnitPath_ofUnitPath p.1)

/-- Send a free Moore loop to a circle map via `toClosedUnitPath` and
`circleMapHomeomorphClosedUnitPath.symm`. -/
def toCircleMap : C(MooreFreeLoopSpace X, C(Circle, X)) :=
  ((circleMapHomeomorphClosedUnitPath (Q := X)).symm : C(ClosedUnitPath X, C(Circle, X))).comp
    toClosedUnitPath

@[simp]
theorem toCircleMap_unitToCircle (γ : MooreFreeLoopSpace X) (t : I) :
    toCircleMap γ (unitToCircle t) = γ.toMoorePath.toUnitPath t := by
  rw [toCircleMap, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
    circleMapHomeomorphClosedUnitPath_symm_unitToCircle, coe_toClosedUnitPath]

@[simp]
theorem toCircleMap_one (γ : MooreFreeLoopSpace X) : toCircleMap γ 1 = γ.basepoint := by
  rw [← unitToCircle_zero, toCircleMap_unitToCircle, MoorePath.toUnitPath_zero, source_toMoorePath]

@[simp]
theorem toCircleMap_const (x : X) : toCircleMap (const x) = ContinuousMap.const Circle x := by
  ext z
  obtain ⟨t, rfl⟩ := unitToCircle_surjective z
  rw [toCircleMap_unitToCircle]
  simp

@[simp]
theorem toCircleMap_comp_constMap :
    (toCircleMap (X := X)).comp (constMap X) = ContinuousMap.const' :=
  ContinuousMap.ext fun x ↦ by simp

/-- Regard a circle map as a free Moore loop of duration one by precomposing with `unitToCircle`. -/
def ofCircleMap : C(C(Circle, X), MooreFreeLoopSpace X) :=
  ofClosedUnitPath.comp
    (circleMapHomeomorphClosedUnitPath (Q := X) : C(C(Circle, X), ClosedUnitPath X))

@[simp]
theorem toMoorePath_ofCircleMap (f : C(Circle, X)) :
    (ofCircleMap f).toMoorePath = MoorePath.ofUnitPath (f.comp unitToCircle) := by
  simp [ofCircleMap]

@[simp]
theorem basepoint_ofCircleMap (f : C(Circle, X)) : (ofCircleMap f).basepoint = f 1 := by
  simp [ofCircleMap]

@[simp]
theorem toCircleMap_ofCircleMap (f : C(Circle, X)) : toCircleMap (ofCircleMap f) = f := by
  simp [toCircleMap, ofCircleMap]

/-- On the based Moore loop fibre over `x`, `toCircleMap` agrees with `MooreLoopSpace.toPath`
composed with `(basedMapCircleOneHomeomorphPath x).symm`. -/
theorem toCircleMap_toFreeLoop (x : X) (γ : MooreLoopSpace X x) :
    toCircleMap γ.toFreeLoop = ((basedMapCircleOneHomeomorphPath x).symm γ.toPath).1 := by
  ext z
  obtain ⟨t, rfl⟩ := unitToCircle_surjective z
  rw [toCircleMap_unitToCircle, basedMapCircleOneHomeomorphPath_symm_unitToCircle]
  simp

/-- For a based Moore loop `γ`, `toCircleMap γ.toFreeLoop` agrees with `γ.toPath.toCircle`. -/
theorem toCircleMap_toFreeLoop_eq_toCircle (x : X) (γ : MooreLoopSpace X x) :
    toCircleMap γ.toFreeLoop = γ.toPath.toCircle :=
  (toCircleMap_toFreeLoop x γ).trans (coe_basedMapCircleOneHomeomorphPath_symm x γ.toPath)

/-- On the based circle-map fibre over `x`, `ofCircleMap` agrees with
`basedMapCircleOneHomeomorphPath x` followed by `Path.toMooreLoop` and `toFreeLoop`. -/
theorem ofCircleMap_coe_basedMap (x : X) (f : BasedMap Circle X 1 x) :
    ofCircleMap f.1 = (basedMapCircleOneHomeomorphPath x f).toMooreLoop.toFreeLoop := by
  apply ext
  refine MoorePath.ext (by simp) fun t ↦ ?_
  rw [toMoorePath_ofCircleMap, MoorePath.ofUnitPath_apply, ContinuousMap.comp_apply,
    ← basedMapCircleOneHomeomorphPath_apply x f, MooreLoopSpace.toMoorePath_toFreeLoop,
    Path.toMoorePath_toMooreLoop, Path.toMoorePath_apply]
  rfl

/-! ### Basepoint-preserving homotopy equivalence -/

/-- `ofCircleMap ∘ toCircleMap` is homotopic to the identity of `MooreFreeLoopSpace X` through
maps preserving `basepoint`, by restricting `MoorePath.unitHomotopy`. -/
def unitHomotopy :
    ContinuousMap.HomotopyWith ((ofCircleMap (X := X)).comp toCircleMap)
      (ContinuousMap.id (MooreFreeLoopSpace X))
      (fun h ↦ ∀ γ, (h γ).basepoint = γ.basepoint) where
  toFun p := ⟨MoorePath.unitHomotopy (p.1, p.2.toMoorePath),
    (MoorePath.unitHomotopy_target p.1 p.2.toMoorePath).trans
      (p.2.target_eq_source.trans (MoorePath.unitHomotopy_source p.1 p.2.toMoorePath).symm)⟩
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.2
    ((MoorePath.unitHomotopy (X := X)).continuous.comp
      (continuous_fst.prodMk (continuous_toMoorePath.comp continuous_snd)))
  map_zero_left γ := by
    apply ext
    dsimp only
    have hcomp : (toCircleMap γ).comp unitToCircle = γ.toMoorePath.toUnitPath := by
      ext t
      exact toCircleMap_unitToCircle γ t
    rw [MoorePath.unitHomotopy_apply_zero, ContinuousMap.comp_apply, toMoorePath_ofCircleMap, hcomp]
  map_one_left γ := ext (MoorePath.unitHomotopy_apply_one γ.toMoorePath)
  prop' s γ := by
    rw [ContinuousMap.coe_mk, ← source_toMoorePath, MoorePath.unitHomotopy_source,
      source_toMoorePath]

@[simp]
theorem toMoorePath_unitHomotopy (s : I) (γ : MooreFreeLoopSpace X) :
    (unitHomotopy (s, γ)).toMoorePath = MoorePath.unitHomotopy (s, γ.toMoorePath) :=
  (rfl)

@[simp]
theorem basepoint_unitHomotopy (s : I) (γ : MooreFreeLoopSpace X) :
    (unitHomotopy (s, γ)).basepoint = γ.basepoint :=
  (unitHomotopy (X := X)).prop s γ

variable (X) in
/-- **Free Moore loops and circle maps are fibre homotopy equivalent over `X`.** -/
def fiberHomotopyEquivCircleMap :
    FiberHomotopyEquiv (basepointMap X) (mappingSpaceEval (X := X) (1 : Circle)) where
  toFun := toCircleMap
  invFun := ofCircleMap
  comp_toFun := ContinuousMap.ext fun γ ↦ by simp
  comp_invFun := ContinuousMap.ext fun f ↦ by simp
  left_inv := ⟨{
    toHomotopy := (unitHomotopy (X := X)).toHomotopy
    prop' := fun s ↦ ContinuousMap.ext fun γ ↦ by simp }⟩
  right_inv := by
    have h : (toCircleMap (X := X)).comp ofCircleMap = ContinuousMap.id C(Circle, X) :=
      ContinuousMap.ext toCircleMap_ofCircleMap
    rw [h]
    exact ContinuousMap.HomotopicWith.refl _ (ContinuousMap.comp_id _)

@[simp]
theorem fiberHomotopyEquivCircleMap_toFun :
    (fiberHomotopyEquivCircleMap X).toFun = toCircleMap :=
  (rfl)

@[simp]
theorem fiberHomotopyEquivCircleMap_invFun :
    (fiberHomotopyEquivCircleMap X).invFun = ofCircleMap :=
  (rfl)

variable (X) in
/-- **Free Moore loops and circle maps are homotopy equivalent.** -/
def homotopyEquivCircleMap : MooreFreeLoopSpace X ≃ₕ C(Circle, X) :=
  (fiberHomotopyEquivCircleMap X).toHomotopyEquiv

@[simp]
theorem homotopyEquivCircleMap_apply (γ : MooreFreeLoopSpace X) :
    homotopyEquivCircleMap X γ = toCircleMap γ := by
  simp [homotopyEquivCircleMap]

@[simp]
theorem homotopyEquivCircleMap_symm_apply (f : C(Circle, X)) :
    (homotopyEquivCircleMap X).symm f = ofCircleMap f := by
  simp [homotopyEquivCircleMap]

/-- Shrinking duration from `1` to `0` compares `ofCircleMap ∘ const` with the duration-zero
constant free Moore loop section `constMap X` through sections of `basepoint`. -/
def constCircleHomotopy :
    ContinuousMap.HomotopyWith ((ofCircleMap (X := X)).comp ContinuousMap.const') (constMap X)
      (fun h ↦ ∀ x, (h x).basepoint = x) where
  toFun p := ⟨MoorePath.constOfLength p.2 (1 - toNNReal p.1), by simp⟩
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.2
    (continuous_snd.moorePath_constOfLength
      (continuous_const.sub (toNNReal_continuous.comp continuous_fst)))
  map_zero_left x := ext (by simp)
  map_one_left x := ext (by simp)
  prop' s x := by
    rw [ContinuousMap.coe_mk, ← source_toMoorePath, MoorePath.source_constOfLength]

@[simp]
theorem toMoorePath_constCircleHomotopy (s : I) (x : X) :
    (constCircleHomotopy (s, x)).toMoorePath = MoorePath.constOfLength x (1 - toNNReal s) :=
  (rfl)

/-! ### Contractible free loops -/

/-- `toCircleMap` sends contractible free Moore loops to contractible circle loops. -/
theorem toCircleMap_mem_contractibleLoops {γ : MooreFreeLoopSpace X}
    (hγ : γ ∈ contractibleLoops X) :
    toCircleMap γ ∈ TauCeti.contractibleLoops X := by
  rw [mem_contractibleLoops] at hγ
  obtain ⟨x, hx⟩ := hγ
  have hc := hx.symm.map toCircleMap.continuous
  rw [toCircleMap_const] at hc
  exact TauCeti.mem_contractibleLoops_iff.2 ⟨x, hc⟩

/-- `ofCircleMap` sends contractible circle loops to contractible free Moore loops. -/
theorem ofCircleMap_mem_contractibleLoops {f : C(Circle, X)}
    (hf : f ∈ TauCeti.contractibleLoops X) :
    ofCircleMap f ∈ contractibleLoops X := by
  rw [TauCeti.mem_contractibleLoops_iff] at hf
  obtain ⟨x, hx⟩ := hf
  have hconst : Joined (const x) (ofCircleMap (ContinuousMap.const Circle x)) := by
    rw [← constMap_apply x]
    exact ⟨((constCircleHomotopy (X := X)).toHomotopy.evalAt x).symm⟩
  exact mem_contractibleLoops.2 ⟨x, hconst.trans (hx.symm.map ofCircleMap.continuous)⟩

-- Not `@[simp]`: `TauCeti.mem_contractibleLoops_iff` already simplifies the left-hand side.
/-- `toCircleMap` detects contractibility of free Moore loops. -/
theorem toCircleMap_mem_contractibleLoops_iff {γ : MooreFreeLoopSpace X} :
    toCircleMap γ ∈ TauCeti.contractibleLoops X ↔ γ ∈ contractibleLoops X where
  mp h := by
    have h0 : ofCircleMap (toCircleMap γ) ∈ contractibleLoops X :=
      ofCircleMap_mem_contractibleLoops h
    exact mem_contractibleLoops_of_joined h0 ⟨(unitHomotopy (X := X)).toHomotopy.evalAt γ⟩
  mpr := toCircleMap_mem_contractibleLoops

/-- `ofCircleMap` detects contractibility of circle loops. -/
@[simp]
theorem ofCircleMap_mem_contractibleLoops_iff {f : C(Circle, X)} :
    ofCircleMap f ∈ contractibleLoops X ↔ f ∈ TauCeti.contractibleLoops X := by
  rw [← toCircleMap_mem_contractibleLoops_iff, toCircleMap_ofCircleMap]

/-- `unitHomotopy` stays inside `contractibleLoops X` at every intermediate time. -/
theorem unitHomotopy_mem_contractibleLoops (s : I) {γ : MooreFreeLoopSpace X}
    (hγ : γ ∈ contractibleLoops X) :
    unitHomotopy (s, γ) ∈ contractibleLoops X := by
  have hI : PathConnectedSpace I :=
    (Set.projIcc_surjective (zero_le_one : (0 : ℝ) ≤ 1)).pathConnectedSpace continuous_projIcc
  have hγs := (hI.joined 1 s).map
    ((unitHomotopy (X := X)).continuous.comp (Continuous.prodMk_left γ))
  simp only [Function.comp_apply, unitHomotopy.apply_one, ContinuousMap.id_apply] at hγs
  exact mem_contractibleLoops_of_joined hγ hγs

/-- Forward comparison restricted to contractible free loops. -/
def toCircleMapContractible : C(contractibleLoops X, TauCeti.contractibleLoops X) where
  toFun γ := ⟨toCircleMap γ.1, toCircleMap_mem_contractibleLoops γ.2⟩
  continuous_toFun := (toCircleMap.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_toCircleMapContractible (γ : contractibleLoops X) :
    (toCircleMapContractible γ : C(Circle, X)) = toCircleMap γ.1 :=
  (rfl)

/-- Reverse comparison restricted to contractible free loops. -/
def ofCircleMapContractible : C(TauCeti.contractibleLoops X, contractibleLoops X) where
  toFun f := ⟨ofCircleMap f.1, ofCircleMap_mem_contractibleLoops f.2⟩
  continuous_toFun := (ofCircleMap.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_ofCircleMapContractible (f : TauCeti.contractibleLoops X) :
    (ofCircleMapContractible f : MooreFreeLoopSpace X) = ofCircleMap f.1 :=
  (rfl)

@[simp]
theorem toCircleMapContractible_ofCircleMapContractible (f : TauCeti.contractibleLoops X) :
    toCircleMapContractible (ofCircleMapContractible f) = f :=
  Subtype.ext (toCircleMap_ofCircleMap f.1)

@[simp]
theorem toCircleMapContractible_constContractible (x : X) :
    toCircleMapContractible (constContractible x) = constContractibleLoop x :=
  Subtype.ext (by simp)

@[simp]
theorem toCircleMapContractible_comp_constContractibleMap :
    (toCircleMapContractible (X := X)).comp (constContractibleMap X) = constContractibleLoop :=
  ContinuousMap.ext fun x ↦ by simp

/-- `ofCircleMapContractible ∘ toCircleMapContractible` is homotopic to the identity of
`contractibleLoops X` through maps preserving `basepointContractible X`. -/
def unitHomotopyContractible :
    ContinuousMap.HomotopyWith ((ofCircleMapContractible (X := X)).comp toCircleMapContractible)
      (ContinuousMap.id (contractibleLoops X))
      (fun h ↦ ∀ γ, basepointContractible X (h γ) = basepointContractible X γ) where
  toFun p := ⟨unitHomotopy (p.1, p.2.1), unitHomotopy_mem_contractibleLoops p.1 p.2.2⟩
  continuous_toFun := ((unitHomotopy (X := X)).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left γ := Subtype.ext ((unitHomotopy (X := X)).apply_zero γ.1)
  map_one_left γ := Subtype.ext ((unitHomotopy (X := X)).apply_one γ.1)
  prop' s γ := by simp

variable (X) in
/-- **Contractible free Moore loops and contractible circle loops are fibre homotopy equivalent
over `X`.** -/
def fiberHomotopyEquivContractibleLoops :
    FiberHomotopyEquiv (basepointContractible X) (basepointContractibleLoop (Q := X)) where
  toFun := toCircleMapContractible
  invFun := ofCircleMapContractible
  comp_toFun := ContinuousMap.ext fun γ ↦ by simp
  comp_invFun := ContinuousMap.ext fun f ↦ by simp
  left_inv := ⟨{
    toHomotopy := (unitHomotopyContractible (X := X)).toHomotopy
    prop' := fun s ↦ ContinuousMap.ext fun γ ↦ (unitHomotopyContractible (X := X)).prop s γ }⟩
  right_inv := by
    have h : (toCircleMapContractible (X := X)).comp ofCircleMapContractible =
        ContinuousMap.id (TauCeti.contractibleLoops X) :=
      ContinuousMap.ext toCircleMapContractible_ofCircleMapContractible
    rw [h]
    exact ContinuousMap.HomotopicWith.refl _ (ContinuousMap.comp_id _)

@[simp]
theorem fiberHomotopyEquivContractibleLoops_toFun :
    (fiberHomotopyEquivContractibleLoops X).toFun = toCircleMapContractible :=
  (rfl)

@[simp]
theorem fiberHomotopyEquivContractibleLoops_invFun :
    (fiberHomotopyEquivContractibleLoops X).invFun = ofCircleMapContractible :=
  (rfl)

variable (X) in
/-- **Contractible free Moore loops and contractible circle loops are homotopy equivalent.** -/
def homotopyEquivContractibleLoops : contractibleLoops X ≃ₕ TauCeti.contractibleLoops X :=
  (fiberHomotopyEquivContractibleLoops X).toHomotopyEquiv

@[simp]
theorem homotopyEquivContractibleLoops_apply (γ : contractibleLoops X) :
    homotopyEquivContractibleLoops X γ = toCircleMapContractible γ := by
  simp [homotopyEquivContractibleLoops]

@[simp]
theorem homotopyEquivContractibleLoops_symm_apply (f : TauCeti.contractibleLoops X) :
    (homotopyEquivContractibleLoops X).symm f = ofCircleMapContractible f := by
  simp [homotopyEquivContractibleLoops]

/-- `constCircleHomotopy` stays inside `contractibleLoops X` at every intermediate time. -/
theorem constCircleHomotopy_mem_contractibleLoops (s : I) (x : X) :
    constCircleHomotopy (s, x) ∈ contractibleLoops X := by
  have hI : PathConnectedSpace I :=
    (Set.projIcc_surjective (zero_le_one : (0 : ℝ) ≤ 1)).pathConnectedSpace continuous_projIcc
  have hxs := (hI.joined 1 s).map
    ((constCircleHomotopy (X := X)).continuous.comp (Continuous.prodMk_left x))
  simp only [Function.comp_apply, constCircleHomotopy.apply_one, constMap_apply] at hxs
  exact mem_contractibleLoops_of_joined (const_mem_contractibleLoops x) hxs

/-- Shrinking duration from `1` to `0` compares `ofCircleMapContractible ∘ constContractibleLoop`
with `constContractibleMap X` through sections of `basepointContractible X`. -/
def constContractibleHomotopy :
    ContinuousMap.HomotopyWith
      ((ofCircleMapContractible (X := X)).comp constContractibleLoop)
      (constContractibleMap X)
      (fun h ↦ ∀ x, basepointContractible X (h x) = x) where
  toFun p := ⟨constCircleHomotopy p, constCircleHomotopy_mem_contractibleLoops p.1 p.2⟩
  continuous_toFun := (constCircleHomotopy (X := X)).continuous.subtype_mk _
  map_zero_left x := Subtype.ext (by simp)
  map_one_left x := Subtype.ext (((constCircleHomotopy (X := X)).apply_one x).trans (by simp))
  prop' s x := by simpa using (constCircleHomotopy (X := X)).prop s x

@[simp]
theorem coe_constContractibleHomotopy (s : I) (x : X) :
    (constContractibleHomotopy (s, x) : MooreFreeLoopSpace X) = constCircleHomotopy (s, x) :=
  (rfl)

end MooreFreeLoopSpace

end TauCeti
