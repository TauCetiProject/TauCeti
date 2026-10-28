/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop
public import TauCeti.Topology.MappingSpace.FreeLoop
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.ContinuousMap.Precomp
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
import Mathlib.Topology.Subpath

/-!
# Free Moore loops and maps from the circle

Normalizing a free Moore loop of duration `L` gives the circle map
`exp(2πit) ↦ γ(Lt)`. Conversely, a circle map gives a Moore loop of duration one.
These maps form a fibre homotopy equivalence over evaluation at the basepoint,
and restrict to a homotopy equivalence on the subspaces of contractible loops.
All spaces carry their raw compact-open or inherited topologies; the target
space is arbitrary. The bundled comparison is `fiberHomotopyEquivCircle`;
its `toHomotopyEquiv` gives the equivalence of total spaces, and
`homotopyEquivContractibleCircle` gives the contractible-loop restriction.

Constant Moore loops of every duration give constant circle maps. The inverse
comparison uses duration one, so the composite on Moore loops is homotopic to
the identity, rather than equal to it. The homotopy is the endpoint-preserving
Moore-path normalization homotopy.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG
  coefficients. Applications to cotangent bundles*, arXiv:2404.07953, §5.2.
-/

public noncomputable section

open scoped NNReal
open ContinuousMap unitInterval

namespace TauCeti.MooreFreeLoopSpace

variable {X : Type*} [TopologicalSpace X]

/-- Normalize a free Moore loop to a map from the circle, using its duration. -/
def toCircle (γ : MooreFreeLoopSpace X) : C(Circle, X) :=
  (⟨γ.toMoorePath.toUnitPath, γ.toMoorePath.toUnitPath_zero,
    γ.toMoorePath.toUnitPath_one.trans γ.target_eq_source⟩ :
      Path γ.toMoorePath.source γ.toMoorePath.source).toCircle

/-- Normalization evaluates a circle parameter at the corresponding fraction of the duration. -/
@[simp]
theorem toCircle_exp (γ : MooreFreeLoopSpace X) (t : I) :
    γ.toCircle (Circle.exp (2 * Real.pi * t)) = γ.toMoorePath.toUnitPath t :=
  Path.toCircle_exp _ t

/-- Normalization preserves evaluation at the loop basepoint. -/
@[simp]
theorem toCircle_one (γ : MooreFreeLoopSpace X) : γ.toCircle 1 = γ.basepoint := by
  simpa only [Set.Icc.coe_zero, mul_zero, Circle.exp_zero, MoorePath.toUnitPath_zero,
    source_toMoorePath] using toCircle_exp γ 0

@[fun_prop]
theorem continuous_toCircle : Continuous (toCircle : MooreFreeLoopSpace X → C(Circle, X)) := by
  apply (ContinuousMap.isInducing_precomp_of_surjective Circle.expLoop.toContinuousMap
    Circle.expLoop_surjective).continuous_iff.mpr
  have h : (fun γ : MooreFreeLoopSpace X ↦ γ.toCircle.comp Circle.expLoop.toContinuousMap) =
      fun γ ↦ γ.toMoorePath.toUnitPath := by
    funext γ
    ext t
    simpa only [ContinuousMap.comp_apply, Path.coe_toContinuousMap, Circle.expLoop_apply] using
      toCircle_exp γ t
  rw [Function.comp_def, h]
  exact MoorePath.continuous_toUnitPath.comp continuous_toMoorePath

/-- Read a circle map as a free Moore loop of duration one. -/
def ofCircle (f : C(Circle, X)) : MooreFreeLoopSpace X :=
  ⟨MoorePath.ofUnitPath (f.comp Circle.expLoop.toContinuousMap), by simp⟩

@[simp]
theorem toMoorePath_ofCircle (f : C(Circle, X)) :
    (ofCircle f).toMoorePath = MoorePath.ofUnitPath (f.comp Circle.expLoop.toContinuousMap) :=
  (rfl)

@[simp]
theorem length_ofCircle (f : C(Circle, X)) : (ofCircle f).length = 1 := by
  rw [← length_toMoorePath, toMoorePath_ofCircle, MoorePath.length_ofUnitPath]

@[simp]
theorem basepoint_ofCircle (f : C(Circle, X)) : (ofCircle f).basepoint = f 1 := by
  rw [← source_toMoorePath, toMoorePath_ofCircle, MoorePath.source_ofUnitPath]
  simp

@[fun_prop]
theorem continuous_ofCircle : Continuous (ofCircle : C(Circle, X) → MooreFreeLoopSpace X) :=
  isEmbedding_toMoorePath.continuous_iff.mpr
    (MoorePath.continuous_ofUnitPath.comp (ContinuousMap.continuous_precomp _))

/-- A circle map is unchanged after passing to Moore loops and back. -/
@[simp]
theorem toCircle_ofCircle (f : C(Circle, X)) : (ofCircle f).toCircle = f := by
  ext z
  obtain ⟨t, rfl⟩ := Circle.expLoop_surjective z
  simp [toCircle_exp, toMoorePath_ofCircle, MoorePath.toUnitPath_ofUnitPath]

/-- On Moore paths the round trip is the existing normalization to duration one. -/
theorem toMoorePath_ofCircle_toCircle (γ : MooreFreeLoopSpace X) :
    (ofCircle γ.toCircle).toMoorePath = MoorePath.toLengthOne γ.toMoorePath := by
  rw [toMoorePath_ofCircle, MoorePath.toLengthOne_apply]
  congr 1
  ext t
  simpa only [ContinuousMap.comp_apply, Path.coe_toContinuousMap, Circle.expLoop_apply] using
    toCircle_exp γ t

/-- Every constant Moore loop, regardless of duration, normalizes to a constant circle map. -/
@[simp]
theorem toCircle_constOfLength (x : X) (L : ℝ≥0) :
    (⟨MoorePath.constOfLength x L, by simp⟩ : MooreFreeLoopSpace X).toCircle = .const Circle x := by
  ext z
  obtain ⟨t, rfl⟩ := Circle.expLoop_surjective z
  simp [toCircle_exp]

@[simp]
theorem toCircle_const (x : X) : (const x).toCircle = .const Circle x := by
  ext z
  obtain ⟨t, rfl⟩ := Circle.expLoop_surjective z
  simp [toCircle_exp]

/-- The round trip on free Moore loops is homotopic to the identity over the basepoint. -/
def circleHomotopy : HomotopyWith
    ((⟨ofCircle, continuous_ofCircle⟩ : C(C(Circle, X), MooreFreeLoopSpace X)).comp
      ⟨toCircle, continuous_toCircle⟩) (.id (MooreFreeLoopSpace X))
    (fun f ↦ (⟨basepoint, continuous_basepoint⟩ : C(MooreFreeLoopSpace X, X)).comp f =
      ⟨basepoint, continuous_basepoint⟩) where
  toFun p := ⟨MoorePath.unitHomotopy (p.1, p.2.toMoorePath), by
    rw [MoorePath.unitHomotopy_target, MoorePath.unitHomotopy_source, p.2.target_eq_source]⟩
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.mpr
    ((MoorePath.unitHomotopy (X := X)).continuous.comp
      (continuous_fst.prodMk (continuous_toMoorePath.comp continuous_snd)))
  map_zero_left γ := ext <| by
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    rw [toMoorePath_ofCircle_toCircle, MoorePath.toLengthOne_apply]
    exact MoorePath.unitHomotopy_apply_zero _
  map_one_left γ := ext (MoorePath.unitHomotopy_apply_one _)
  prop' t := ContinuousMap.ext fun γ ↦ by
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ← source_toMoorePath] using
      MoorePath.unitHomotopy_source t γ.toMoorePath

/-- The comparison homotopy is the endpoint-preserving Moore-path homotopy. -/
@[simp]
theorem toMoorePath_circleHomotopy (t : I) (γ : MooreFreeLoopSpace X) :
    (circleHomotopy (t, γ)).toMoorePath = MoorePath.unitHomotopy (t, γ.toMoorePath) :=
  (rfl)

/-- Free Moore loops and circle maps are fibre homotopy equivalent over evaluation. -/
def fiberHomotopyEquivCircle : FiberHomotopyEquiv
    (⟨basepoint, continuous_basepoint⟩ : C(MooreFreeLoopSpace X, X))
    ⟨fun f : C(Circle, X) ↦ f 1, continuous_eval_const 1⟩ where
  toFun := ⟨toCircle, continuous_toCircle⟩
  invFun := ⟨ofCircle, continuous_ofCircle⟩
  comp_toFun := ContinuousMap.ext toCircle_one
  comp_invFun := ContinuousMap.ext basepoint_ofCircle
  left_inv := ⟨circleHomotopy⟩
  right_inv := by
    have h : (⟨toCircle, continuous_toCircle⟩ : C(MooreFreeLoopSpace X, C(Circle, X))).comp
        ⟨ofCircle, continuous_ofCircle⟩ = .id _ := ContinuousMap.ext toCircle_ofCircle
    rw [h]
    exact ⟨HomotopyWith.refl _ (ContinuousMap.comp_id _)⟩

@[simp]
theorem fiberHomotopyEquivCircle_toFun (γ : MooreFreeLoopSpace X) :
    fiberHomotopyEquivCircle.toFun γ = γ.toCircle :=
  (rfl)

@[simp]
theorem fiberHomotopyEquivCircle_invFun (f : C(Circle, X)) :
    fiberHomotopyEquivCircle.invFun f = ofCircle f :=
  (rfl)

variable {Y : Type*} [TopologicalSpace Y]

/-- Normalization is natural under continuous maps of the target. -/
@[simp]
theorem toCircle_map (f : C(X, Y)) (γ : MooreFreeLoopSpace X) :
    (map f γ).toCircle = f.comp γ.toCircle := by
  ext z
  obtain ⟨t, rfl⟩ := Circle.expLoop_surjective z
  simp [toCircle_exp, MoorePath.toUnitPath_apply]

/-- The duration-one comparison is natural under continuous maps of the target. -/
@[simp]
theorem ofCircle_comp (f : C(X, Y)) (γ : C(Circle, X)) :
    ofCircle (f.comp γ) = map f (ofCircle γ) := by
  apply ext
  apply MoorePath.ext
  · simp
  · intro t
    simp

/-- Normalization preserves and detects contractibility of free loops. -/
theorem toCircle_mem_contractibleLoops_iff (γ : MooreFreeLoopSpace X) :
    γ.toCircle ∈ TauCeti.contractibleLoops X ↔ γ ∈ contractibleLoops X := by
  rw [TauCeti.mem_contractibleLoops_iff, mem_contractibleLoops]
  constructor
  · rintro ⟨x, hx⟩
    have hconst : Joined (ofCircle (.const Circle x)) (const x) := by
      simpa only [Joined, ContinuousMap.comp_apply, ContinuousMap.coe_mk, toCircle_const,
        ContinuousMap.id_apply] using
        (⟨circleHomotopy.toHomotopy.evalAt (const x)⟩ :
          Joined _ _)
    have hround : Joined (ofCircle γ.toCircle) γ :=
      ⟨circleHomotopy.toHomotopy.evalAt γ⟩
    exact ⟨x, (hconst.symm.trans (hx.map continuous_ofCircle).symm).trans hround⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa only [toCircle_const] using (hx.map continuous_toCircle).symm⟩

/-- A circle map gives a contractible Moore loop exactly when it is contractible. -/
@[simp]
theorem ofCircle_mem_contractibleLoops_iff (f : C(Circle, X)) :
    ofCircle f ∈ contractibleLoops X ↔ f ∈ TauCeti.contractibleLoops X := by
  rw [← toCircle_mem_contractibleLoops_iff, toCircle_ofCircle]

private theorem circleHomotopy_mem_contractibleLoops (t : I)
    (γ : contractibleLoops X) : circleHomotopy (t, γ.val) ∈ contractibleLoops X := by
  have h : Joined (circleHomotopy (1, γ.val)) (circleHomotopy (t, γ.val)) :=
    ⟨(circleHomotopy.toHomotopy.evalAt γ.val).subpath 1 t⟩
  rw [circleHomotopy.apply_one, ContinuousMap.id_apply] at h
  exact mem_contractibleLoops_of_joined γ.property h

/-- The free-loop comparison restricts to the subspaces of contractible loops. -/
def homotopyEquivContractibleCircle :
    contractibleLoops X ≃ₕ TauCeti.contractibleLoops X where
  toFun := ⟨fun γ ↦ ⟨γ.val.toCircle, (toCircle_mem_contractibleLoops_iff γ.val).mpr γ.property⟩,
    (continuous_toCircle.comp continuous_subtype_val).subtype_mk _⟩
  invFun := ⟨fun f ↦ ⟨ofCircle f.val, (ofCircle_mem_contractibleLoops_iff f.val).mpr f.property⟩,
    (continuous_ofCircle.comp continuous_subtype_val).subtype_mk _⟩
  left_inv := ⟨{
    toFun := fun p ↦ ⟨circleHomotopy (p.1, p.2.val), circleHomotopy_mem_contractibleLoops _ _⟩
    continuous_toFun := (circleHomotopy.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun γ ↦ Subtype.ext (circleHomotopy.apply_zero γ.val)
    map_one_left := fun γ ↦ Subtype.ext (circleHomotopy.apply_one γ.val) }⟩
  right_inv := by
    convert (ContinuousMap.Homotopic.refl (.id (TauCeti.contractibleLoops X))) using 1
    apply ContinuousMap.ext
    intro f
    exact Subtype.ext (toCircle_ofCircle f.val)

@[simp]
theorem coe_homotopyEquivContractibleCircle_apply (γ : contractibleLoops X) :
    (homotopyEquivContractibleCircle γ : C(Circle, X)) = γ.val.toCircle :=
  (rfl)

@[simp]
theorem coe_homotopyEquivContractibleCircle_symm_apply (f : TauCeti.contractibleLoops X) :
    (homotopyEquivContractibleCircle.symm f : MooreFreeLoopSpace X) = ofCircle f.val :=
  (rfl)

end TauCeti.MooreFreeLoopSpace

namespace TauCeti.MooreLoopSpace

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The free-loop comparison agrees with the based Moore-loop normalization. -/
theorem toCircle_toFreeLoop (γ : MooreLoopSpace X x) :
    γ.toFreeLoop.toCircle = γ.toPath.toCircle := by
  ext z
  obtain ⟨t, rfl⟩ := Circle.expLoop_surjective z
  simp [MooreFreeLoopSpace.toCircle_exp, Path.toCircle_exp, MoorePath.toUnitPath_apply,
    toPath_apply]

end TauCeti.MooreLoopSpace
