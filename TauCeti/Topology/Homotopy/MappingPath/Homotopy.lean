/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Subpath
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.Homotopy.MappingPath.Functoriality

/-!
# Homotopy invariance of mapping-path fibres

A homotopy `H : f.Homotopy g` gives a map from the mapping-path fibre of `f` over `k` to
that of `g`: prepend the reversed track of `H` to the supplied path. Reversing `H` gives
a fibre homotopy inverse over the common source. Both inverse homotopies are continuous in
the whole mapping-path fibre, including its source point, and preserve that point strictly.
Thus the comparison also restricts to the path spaces over each source point.

The inverse homotopies shrink a track followed by its reverse, then remove the constant-path
delays. No connectedness, nonemptiness, separation or fibration hypothesis is needed.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public noncomputable section

open unitInterval TauCeti TauCeti.MappingPathFiber Topology.Homotopy

universe u v

namespace ContinuousMap.Homotopy

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]
variable {f g : C(B, K)} (H : f.Homotopy g) (k : K)

/-- Prepend the reversed track of a homotopy to a path in its initial mapping-path fibre. -/
def mappingPathFiberMap : C(MappingPathFiber f k, MappingPathFiber g k) where
  toFun p := ⟨(p.val.1,
    ((H.evalAt p.val.1).symm.trans ⟨p.val.2, p.property.1, p.property.2⟩).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine (continuous_subtype_val.fst.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family
      (fun p : MappingPathFiber f k ↦ (H.evalAt p.val.1).symm)
      (H.continuous.comp ((continuous_symm.comp continuous_snd).prodMk
        (continuous_subtype_val.fst.comp continuous_fst)))
      (fun p ↦ ⟨p.val.2, p.property.1, p.property.2⟩)
      (continuous_subtype_val.snd.comp continuous_fst |>.eval continuous_snd)

@[simp]
theorem mappingPathFiberMap_val_fst (p : MappingPathFiber f k) :
    (mappingPathFiberMap H k p).val.1 = p.val.1 := (rfl)

/-- The comparison path is the reversed homotopy track followed by the original path. -/
@[simp]
theorem mappingPathFiberMap_val_snd (p : MappingPathFiber f k) :
    (mappingPathFiberMap H k p).val.2 =
      ((H.evalAt p.val.1).symm.trans ⟨p.val.2, p.property.1, p.property.2⟩).toContinuousMap := (rfl)

/-- The comparison lies strictly over the common source. -/
@[simp]
theorem proj_comp_mappingPathFiberMap : (proj g k).comp (mappingPathFiberMap H k) = proj f k := by
  ext p
  simp

/-- Homotopy comparisons commute with maps of homotopies carrying the chosen endpoint to
the chosen endpoint. The two fibre maps use the squares at times zero and one. -/
theorem mappingPathFiberMap_natural {B' K' : Type*} [TopologicalSpace B'] [TopologicalSpace K']
    {f' g' : C(B', K')} (H' : f'.Homotopy g') (a : C(B, B')) (b : C(K, K'))
    (hs : ∀ s x, b (H (s, x)) = H' (s, a x)) {k' : K'} (hk : b k = k') :
    (map a b (ContinuousMap.ext fun x ↦ by simpa using hs 1 x) hk).comp
        (mappingPathFiberMap H k) =
      (mappingPathFiberMap H' k').comp
        (map a b (ContinuousMap.ext fun x ↦ by simpa using hs 0 x) hk) := by
  ext p : 1
  apply Subtype.ext
  apply Prod.ext
  · simp
  · ext t
    simp only [ContinuousMap.comp_apply, map_val, mappingPathFiberMap_val_snd,
      mappingPathFiberMap_val_fst, Path.coe_toContinuousMap, Path.trans_apply,
      Path.symm_apply, Function.comp_apply, evalAt_apply, Path.coe_mk']
    split_ifs <;> simp [hs]

/-- Remove the constant initial path continuously, keeping the source point fixed. -/
private def reflHomotopy :
    ContinuousMap.HomotopyWith (mappingPathFiberMap (.refl f) k) (.id (MappingPathFiber f k))
      (fun a ↦ (proj f k).comp a = proj f k) where
  toFun q := ⟨(q.2.val.1,
    (Path.delayReflLeft q.1 ⟨q.2.val.2, q.2.property.1, q.2.property.2⟩).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine ((continuous_subtype_val.fst.comp continuous_snd).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.delayReflLeft_continuous_family
      (fun q : I × MappingPathFiber f k ↦
        ⟨q.2.val.2, q.2.property.1, q.2.property.2⟩)
      (((continuous_subtype_val.snd.comp continuous_snd).comp continuous_fst).eval continuous_snd)
      ContinuousMap.fst
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Path.toContinuousMap (Path.delayReflLeft_zero _)
  map_one_left p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Path.toContinuousMap (Path.delayReflLeft_one _)
  prop' _ := by ext; simp [proj_apply]

/-- A constant homotopy induces a comparison homotopic to the identity over the source. -/
theorem mappingPathFiberMap_refl_homotopicWith :
    (mappingPathFiberMap (.refl f) k).HomotopicWith (.id (MappingPathFiber f k))
      (fun a ↦ (proj f k).comp a = proj f k) :=
  ⟨reflHomotopy k⟩

/-- Shrink the two homotopy tracks in the composite simultaneously. -/
private def backtrackHomotopy :
    ContinuousMap.HomotopyWith
      ((mappingPathFiberMap (.refl f) k).comp (mappingPathFiberMap (.refl f) k))
      ((mappingPathFiberMap H.symm k).comp (mappingPathFiberMap H k))
      (fun a ↦ (proj f k).comp a = proj f k) := by
  let α (s : I) (b : B) : Path (f b) (H (s, b)) :=
    ((H.evalAt b).subpath 0 s).cast (H.apply_zero b).symm rfl
  exact {
    toFun q := ⟨(q.2.val.1,
      ((α q.1 q.2.val.1).trans ((α q.1 q.2.val.1).symm.trans
        ⟨q.2.val.2, q.2.property.1, q.2.property.2⟩)).toContinuousMap),
      Path.source _, Path.target _⟩
    continuous_toFun := by
      refine ((continuous_subtype_val.fst.comp continuous_snd).prodMk ?_).subtype_mk _
      apply ContinuousMap.continuous_of_continuous_uncurry
      have hα : Continuous ↿fun q : I × MappingPathFiber f k ↦ α q.1 q.2.val.1 := by
        exact H.continuous.comp
          ((by fun_prop : Continuous (fun q : (I × MappingPathFiber f k) × I ↦
            Set.Icc.convexComb 0 q.1.1 q.2)).prodMk
            (continuous_subtype_val.fst.comp (continuous_snd.comp continuous_fst)))
      let γ (q : I × MappingPathFiber f k) : Path (f q.2.val.1) k :=
        ⟨q.2.val.2, q.2.property.1, q.2.property.2⟩
      have hγ : Continuous ↿γ :=
        (((continuous_subtype_val.snd.comp continuous_snd).comp continuous_fst).eval continuous_snd)
      have hβ := Path.trans_continuous_family
        (fun q : I × MappingPathFiber f k ↦ (α q.1 q.2.val.1).symm)
        (Path.symm_continuous_family _ hα) γ hγ
      exact Path.trans_continuous_family
        (fun q : I × MappingPathFiber f k ↦ α q.1 q.2.val.1) hα
        (fun q ↦ (α q.1 q.2.val.1).symm.trans (γ q)) hβ
    map_zero_left p := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · ext t
        -- Endpoint casts only retype the subpaths; their evaluations are unchanged.
        simp [α, Path.cast, Path.trans_apply]
    map_one_left p := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · ext t
        simp [α, Path.subpath_zero_one, Path.cast, Path.trans_apply, -Path.coe_subpath]
    prop' _ := by ext; simp [proj_apply] }

/-- Reversing the homotopy gives a left inverse up to a homotopy over the source. -/
theorem mappingPathFiberMap_symm_comp_homotopicWith :
    ((mappingPathFiberMap H.symm k).comp (mappingPathFiberMap H k)).HomotopicWith
      (.id (MappingPathFiber f k)) (fun a ↦ (proj f k).comp a = proj f k) := by
  let h := (reflHomotopy (f := f) k).toHomotopy.compContinuousMap (mappingPathFiberMap (.refl f) k)
  -- Compose the first delay-removal homotopy in the fibre over the unchanged source point.
  have h' : ((mappingPathFiberMap (.refl f) k).comp (mappingPathFiberMap (.refl f) k)).HomotopicWith
      (mappingPathFiberMap (.refl f) k) (fun a ↦ (proj f k).comp a = proj f k) := by
    refine ⟨⟨h.cast rfl (ContinuousMap.id_comp _), ?_⟩⟩
    intro s
    ext p
    calc
      _ = proj f k ((reflHomotopy k) (s, mappingPathFiberMap (.refl f) k p)) := rfl
      _ = proj f k (mappingPathFiberMap (.refl f) k p) :=
        ContinuousMap.congr_fun ((reflHomotopy k).prop' s) _
      _ = _ := by simp
  exact ⟨(backtrackHomotopy H k).symm.trans (h'.some.trans (reflHomotopy k))⟩

/-- Homotopic maps have fibre homotopy equivalent mapping-path fibres over their common source.
The forward comparison prepends the reversed track; its inverse uses the reversed homotopy. -/
def mappingPathFiberEquiv :
    FiberHomotopyEquiv (proj f k) (proj g k) where
  toFun := mappingPathFiberMap H k
  invFun := mappingPathFiberMap H.symm k
  comp_toFun := proj_comp_mappingPathFiberMap H k
  comp_invFun := proj_comp_mappingPathFiberMap H.symm k
  left_inv := mappingPathFiberMap_symm_comp_homotopicWith H k
  right_inv := by
    simpa using mappingPathFiberMap_symm_comp_homotopicWith H.symm k

@[simp]
theorem mappingPathFiberEquiv_toFun :
    (mappingPathFiberEquiv H k).toFun = mappingPathFiberMap H k := (rfl)

@[simp]
theorem mappingPathFiberEquiv_invFun :
    (mappingPathFiberEquiv H k).invFun = mappingPathFiberMap H.symm k := (rfl)

/-- Homotopic maps have homotopy equivalent mapping-path fibres at every endpoint. -/
def mappingPathFiberHomotopyEquiv : MappingPathFiber f k ≃ₕ MappingPathFiber g k :=
  (mappingPathFiberEquiv H k).toHomotopyEquiv

@[simp]
theorem mappingPathFiberHomotopyEquiv_apply (p : MappingPathFiber f k) :
    mappingPathFiberHomotopyEquiv H k p = mappingPathFiberMap H k p :=
  FiberHomotopyEquiv.toHomotopyEquiv_apply _ p

@[simp]
theorem mappingPathFiberHomotopyEquiv_symm_apply (p : MappingPathFiber g k) :
    (mappingPathFiberHomotopyEquiv H k).symm p = mappingPathFiberMap H.symm k p :=
  FiberHomotopyEquiv.toHomotopyEquiv_symm_apply _ p

end ContinuousMap.Homotopy
