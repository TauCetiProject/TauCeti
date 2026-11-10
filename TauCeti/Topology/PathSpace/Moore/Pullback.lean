/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Equiv
public import TauCeti.Topology.PathSpace.Moore.From
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Equivariant trivialization of a pulled-back Moore path fibration

`MoorePathPullback f b` is the pullback along `f : D → X` of the endpoint map on
Moore paths starting at `b`. A continuous family of paths `τ d` from `b` to `f d`
gives an explicit fibre homotopy equivalence with `D × Ω_b X`. The forward map
appends `τ d` to a loop; the inverse appends its reversal. Both maps and both
inverse homotopies commute strictly with left concatenation by loops at `b`.
All topologies are the raw compact-open Moore topologies, with duration retained.

For a map on a star-convex set, `radialPaths` supplies this family by following
a chosen path to the centre and then the image of a radial segment. In particular
this applies to characteristic disks. The equivariant comparison is the local
path-fibration input for constructing a cellular free resolution over loop chains.
It is a homotopy trivialization, not a homeomorphism or a strict inverse assertion.

The construction uses the retracing loops of `MoorePathBetween.retrace`,
with endpoints varying continuously with the parameter.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential
  graded coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped NNReal
open unitInterval ContinuousMap

namespace TauCeti

/-- The pullback of the endpoint map on Moore paths starting at `b` along `f`. -/
abbrev MoorePathPullback {D X : Type*} [TopologicalSpace D] [TopologicalSpace X]
    (f : C(D, X)) (b : X) :=
  {z : D × MoorePathFrom X b // z.2.toMoorePath.target = f z.1}

namespace MoorePathPullback

variable {D X : Type*} [TopologicalSpace D] [TopologicalSpace X]
  {f : C(D, X)} {b : X}

/-- The parameter in the base of the pullback. -/
def point (x : MoorePathPullback f b) : D := x.1.1

/-- The path from `b` to the image of the parameter. -/
def path (x : MoorePathPullback f b) : MoorePath X := x.1.2.toMoorePath

/-- Projection to the based path space underlying the pullback. -/
def toMoorePathFrom : C(MoorePathPullback f b, MoorePathFrom X b) :=
  ⟨fun x ↦ x.1.2, continuous_snd.comp continuous_subtype_val⟩

@[simp]
theorem point_mk (d : D) (γ : MoorePathFrom X b) (h : γ.toMoorePath.target = f d) :
    point (f := f) (b := b) ⟨(d, γ), h⟩ = d := (rfl)

@[simp]
theorem path_mk (d : D) (γ : MoorePathFrom X b) (h : γ.toMoorePath.target = f d) :
    path (f := f) (b := b) ⟨(d, γ), h⟩ = γ.toMoorePath := (rfl)

@[simp]
theorem source_path (x : MoorePathPullback f b) : x.path.source = b := MoorePathFrom.source x.1.2

@[simp]
theorem target_path (x : MoorePathPullback f b) : x.path.target = f x.point := x.2

@[ext]
theorem ext {x y : MoorePathPullback f b} (h : x.point = y.point) (h' : x.path = y.path) :
    x = y := Subtype.ext (Prod.ext h (MoorePathFrom.ext h'))

@[fun_prop]
theorem continuous_point : Continuous (point : MoorePathPullback f b → D) :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop]
theorem continuous_path : Continuous (path : MoorePathPullback f b → MoorePath X) :=
  MoorePathFrom.continuous_toMoorePath.comp toMoorePathFrom.continuous

/-- Projection of the pulled-back path space to its parameter. -/
def proj (f : C(D, X)) (b : X) : C(MoorePathPullback f b, D) :=
  ⟨point, continuous_point⟩

@[simp]
theorem proj_apply (x : MoorePathPullback f b) : proj f b x = x.point := (rfl)

/-- Concatenate a loop in front using the action on the based path space. -/
def leftAct (ω : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    MoorePathPullback f b :=
  ⟨(x.1.1, ω • x.1.2), by simpa using x.property⟩

@[simp]
theorem leftAct_one (x : MoorePathPullback f b) : leftAct 1 x = x :=
  Subtype.ext (Prod.ext rfl (one_smul _ _))

@[simp]
theorem leftAct_mul (ω η : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    leftAct (ω * η) x = leftAct ω (leftAct η x) :=
  Subtype.ext (Prod.ext rfl (mul_smul ω η _))

/-- Loops act through the existing action on the based path space. -/
instance : MulAction (MooreLoopSpace X b) (MoorePathPullback f b) where
  smul := leftAct
  one_smul := leftAct_one
  mul_smul := leftAct_mul

@[simp]
theorem smul_eq_leftAct (ω : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    ω • x = leftAct ω x := rfl

@[simp]
theorem toMoorePathFrom_leftAct (ω : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    toMoorePathFrom (leftAct ω x) = ω • toMoorePathFrom x := (rfl)

@[simp]
theorem point_leftAct (ω : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    (leftAct ω x).point = x.point := (rfl)

@[simp]
theorem path_leftAct (ω : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    (leftAct ω x).path = ω.toMoorePath.trans x.path (by simp) :=
  MoorePathFrom.toMoorePath_leftAct ω x.1.2

instance : ContinuousSMul (MooreLoopSpace X b) (MoorePathPullback f b) where
  continuous_smul :=
    ((continuous_point.comp continuous_snd).prodMk
      (continuous_fst.smul (toMoorePathFrom.continuous.comp continuous_snd))).subtype_mk _

variable (τ : C(D, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
  (h₁ : ∀ d, (τ d).target = f d)

/-- Append the chosen path to a loop, giving a path over the parameter. -/
def trivializationMap (τ : C(D, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
    (h₁ : ∀ d, (τ d).target = f d) : C(D × MooreLoopSpace X b, MoorePathPullback f b) where
  toFun z := ⟨(z.1, ⟨z.2.toMoorePath.trans (τ z.1) (by simp [h₀]), by simp⟩),
    by simp [h₁]⟩
  continuous_toFun :=
    (continuous_fst.prodMk
      (((MooreLoopSpace.continuous_toMoorePath.comp continuous_snd).moorePath_trans
        (τ.continuous.comp continuous_fst) (fun z ↦ by simp [h₀])).subtype_mk
          (fun z ↦ by simp))).subtype_mk
          (fun z ↦ by simp [h₁])

@[simp]
theorem point_trivializationMap (z : D × MooreLoopSpace X b) :
    (trivializationMap τ h₀ h₁ z).point = z.1 := (rfl)

@[simp]
theorem path_trivializationMap (z : D × MooreLoopSpace X b) :
    (trivializationMap τ h₀ h₁ z).path = z.2.toMoorePath.trans (τ z.1) (by simp [h₀]) :=
  MoorePathFrom.toMoorePath_mk _ _

/-- Append the reversed chosen path to recover a loop, retaining the parameter. -/
def trivializationInverse (τ : C(D, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
    (h₁ : ∀ d, (τ d).target = f d) : C(MoorePathPullback f b, D × MooreLoopSpace X b) where
  toFun x := (x.point, ⟨x.path.trans (τ x.point).symm (by simp [h₁]), by simp,
    by simp [h₀]⟩)
  continuous_toFun := continuous_point.prodMk
    (MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2
      (continuous_path.moorePath_trans (τ.continuous.comp continuous_point).moorePath_symm
        (fun x ↦ by simp [h₁])))

@[simp]
theorem trivializationInverse_fst (x : MoorePathPullback f b) :
    (trivializationInverse τ h₀ h₁ x).1 = x.point := (rfl)

@[simp]
theorem toMoorePath_trivializationInverse_snd (x : MoorePathPullback f b) :
    (trivializationInverse τ h₀ h₁ x).2.toMoorePath =
      x.path.trans (τ x.point).symm (by simp [h₁]) := (rfl)

/-- The forward map is strictly left-loop-equivariant. -/
theorem trivializationMap_mul (d : D) (ω η : MooreLoopSpace X b) :
    trivializationMap τ h₀ h₁ (d, ω * η) = ω • trivializationMap τ h₀ h₁ (d, η) := by
  refine ext (by simp) ?_
  simp only [path_trivializationMap, smul_eq_leftAct, path_leftAct,
    MooreLoopSpace.toMoorePath_mul]
  exact MoorePath.trans_assoc ..

/-- The inverse map is strictly left-loop-equivariant. -/
theorem trivializationInverse_smul (ω : MooreLoopSpace X b) (x : MoorePathPullback f b) :
    trivializationInverse τ h₀ h₁ (ω • x) =
      (x.point, ω * (trivializationInverse τ h₀ h₁ x).2) := by
  apply Prod.ext (by simp)
  apply MooreLoopSpace.ext
  simp only [toMoorePath_trivializationInverse_snd, smul_eq_leftAct, point_leftAct,
    path_leftAct, MooreLoopSpace.toMoorePath_mul]
  exact MoorePath.trans_assoc ..

/-- The inverse homotopy on the trivial product grows the retracing suffix `τ d ⋆ (τ d)⁻¹`. -/
def trivializationLeftHomotopy :
    HomotopyWith (.id (D × MooreLoopSpace X b))
      ((trivializationInverse τ h₀ h₁).comp (trivializationMap τ h₀ h₁))
      (fun g ↦ ContinuousMap.fst.comp g = ContinuousMap.fst) where
  toFun z := (z.2.1, z.2.2 *
    (MoorePathBetween.retrace ⟨τ z.2.1, h₀ _, h₁ _⟩
      (toNNReal z.1 * (τ z.2.1).length)))
  continuous_toFun := by
    refine continuous_snd.fst.prodMk (continuous_snd.snd.mul
      (MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_))
    simp only [Function.comp_def, MoorePathBetween.toMoorePath_retrace,
      MoorePathBetween.toMoorePath_mk]
    exact (τ.continuous.comp continuous_snd.fst).moorePath_retrace
      ((toNNReal_continuous.comp continuous_fst).mul
        (MoorePath.continuous_length.comp (τ.continuous.comp continuous_snd.fst)))
  map_zero_left z := by
    apply Prod.ext (by simp)
    apply MooreLoopSpace.ext
    simp
  map_one_left z := by
    apply Prod.ext (by simp)
    apply MooreLoopSpace.ext
    simp [MoorePath.trans_assoc]
  prop' _ := ContinuousMap.ext fun _ ↦ rfl

@[simp]
theorem trivializationLeftHomotopy_apply (s : I) (d : D) (ω : MooreLoopSpace X b) :
    trivializationLeftHomotopy τ h₀ h₁ (s, (d, ω)) =
      (d, ω * MoorePathBetween.retrace ⟨τ d, h₀ d, h₁ d⟩
        (toNNReal s * (τ d).length)) := (rfl)

/-- The inverse homotopy on the pullback grows the suffix `(τ d)⁻¹ ⋆ τ d`. -/
def trivializationRightHomotopy :
    HomotopyWith (.id (MoorePathPullback f b))
      ((trivializationMap τ h₀ h₁).comp (trivializationInverse τ h₀ h₁))
      (fun g ↦ (proj f b).comp g = proj f b) where
  toFun z := ⟨(z.2.point, ⟨z.2.path.trans
    ((MoorePathBetween.symm ⟨τ z.2.point, h₀ _, h₁ _⟩).retrace
      (toNNReal z.1 * (τ z.2.point).length)).toMoorePath (by simp [h₁]), by simp⟩),
    by simp [h₁]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine (continuous_point.comp continuous_snd).prodMk
      (((continuous_path.comp continuous_snd).moorePath_trans ?_
        (fun z ↦ by simp [h₁])).subtype_mk _)
    simp only [MoorePathBetween.toMoorePath_retrace, MoorePathBetween.toMoorePath_symm,
      MoorePathBetween.toMoorePath_mk]
    exact (τ.continuous.comp (continuous_point.comp continuous_snd)).moorePath_symm
      |>.moorePath_retrace ((toNNReal_continuous.comp continuous_fst).mul
        (MoorePath.continuous_length.comp
          (τ.continuous.comp (continuous_point.comp continuous_snd))))
  map_zero_left x := ext rfl (by simp)
  map_one_left x := by
    apply ext (by simp)
    simp [MoorePath.trans_assoc, MoorePath.truncate_of_length_le]
  prop' _ := ContinuousMap.ext fun _ ↦ rfl

@[simp]
theorem point_trivializationRightHomotopy (s : I) (x : MoorePathPullback f b) :
    (trivializationRightHomotopy τ h₀ h₁ (s, x)).point = x.point := (rfl)

@[simp]
theorem path_trivializationRightHomotopy (s : I) (x : MoorePathPullback f b) :
    (trivializationRightHomotopy τ h₀ h₁ (s, x)).path =
      x.path.trans ((MoorePathBetween.symm ⟨τ x.point, h₀ _, h₁ _⟩).retrace
        (toNNReal s * (τ x.point).length)).toMoorePath (by simp [h₁]) :=
  MoorePathFrom.toMoorePath_mk _ _

/-- The left inverse homotopy is equivariant at every time. -/
theorem trivializationLeftHomotopy_mul (s : I) (d : D) (ω η : MooreLoopSpace X b) :
    trivializationLeftHomotopy τ h₀ h₁ (s, (d, ω * η)) =
      (d, ω * (trivializationLeftHomotopy τ h₀ h₁ (s, (d, η))).2) := by
  simp only [trivializationLeftHomotopy_apply]
  exact Prod.ext rfl (mul_assoc _ _ _)

/-- The right inverse homotopy is equivariant at every time. -/
theorem trivializationRightHomotopy_smul (s : I) (ω : MooreLoopSpace X b)
    (x : MoorePathPullback f b) :
    trivializationRightHomotopy τ h₀ h₁ (s, ω • x) =
      ω • trivializationRightHomotopy τ h₀ h₁ (s, x) := by
  refine ext (by simp) ?_
  simp only [path_trivializationRightHomotopy, smul_eq_leftAct, point_leftAct, path_leftAct]
  exact MoorePath.trans_assoc ..

/-- A continuous choice of paths gives a fibre homotopy trivialization of the pulled-back
based path fibration, assembled from `trivializationMap`, `trivializationInverse`,
`trivializationLeftHomotopy` and `trivializationRightHomotopy`. Their equivariance is proved in
`trivializationMap_mul`, `trivializationInverse_smul`, `trivializationLeftHomotopy_mul` and
`trivializationRightHomotopy_smul`; the returned structure records only existence of homotopies. -/
def fiberHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.fst : C(D × MooreLoopSpace X b, D)) (proj f b) where
  toFun := trivializationMap τ h₀ h₁
  invFun := trivializationInverse τ h₀ h₁
  comp_toFun := ContinuousMap.ext fun _ ↦ rfl
  comp_invFun := ContinuousMap.ext fun _ ↦ rfl
  left_inv := ⟨(trivializationLeftHomotopy τ h₀ h₁).symm⟩
  right_inv := ⟨(trivializationRightHomotopy τ h₀ h₁).symm⟩

@[simp]
theorem fiberHomotopyEquiv_toFun :
    (fiberHomotopyEquiv τ h₀ h₁).toFun = trivializationMap τ h₀ h₁ := (rfl)

@[simp]
theorem fiberHomotopyEquiv_invFun :
    (fiberHomotopyEquiv τ h₀ h₁).invFun = trivializationInverse τ h₀ h₁ := (rfl)

section Radial

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V] {S : Set V} {c : V}
  (hS : StarConvex ℝ c S) (hc : c ∈ S) (χ : C(S, X))
  (γ : MoorePathBetween X b (χ ⟨c, hc⟩))

/-- Follow a chosen path to the centre, then the image of a radial segment in a star-convex
set. This is a continuous family of Moore paths, including at the centre. -/
def radialPaths (hS : StarConvex ℝ c S) (hc : c ∈ S) (χ : C(S, X))
    (γ : MoorePathBetween X b (χ ⟨c, hc⟩)) : C(S, MoorePath X) :=
  let H : C(I × S, X) := χ.comp
    ⟨fun z ↦ ⟨AffineMap.lineMap c z.2.1 (z.1 : ℝ),
      hS.segment_subset z.2.2 (lineMap_mem_segment ℝ c z.2.1 z.1.2)⟩,
      by simp only [AffineMap.lineMap_apply_module]; fun_prop⟩
  let r : C(S, C(I, X)) := (H.comp ContinuousMap.prodSwap).curry
  ⟨fun v ↦ γ.toMoorePath.trans (.ofUnitPath (r v)) (by simp [r, H]),
    continuous_const.moorePath_trans (MoorePath.continuous_ofUnitPath.comp r.continuous)
      (fun v ↦ by simp [r, H])⟩

@[simp]
theorem source_radialPaths (v : S) : (radialPaths hS hc χ γ v).source = b := by
  simp [radialPaths]

@[simp]
theorem target_radialPaths (v : S) : (radialPaths hS hc χ γ v).target = χ v := by
  simp [radialPaths]

@[simp]
theorem length_radialPaths (v : S) :
    (radialPaths hS hc χ γ v).length = γ.toMoorePath.length + 1 := by
  simp [radialPaths]

/-- After the initial path to the centre, the family follows the image of the radial segment
in one unit of Moore time. -/
theorem radialPaths_apply_length_add (v : S) (t : I) :
    radialPaths hS hc χ γ v (γ.toMoorePath.length + toNNReal t) =
      χ ⟨AffineMap.lineMap c v.1 (t : ℝ),
        hS.segment_subset v.2 (lineMap_mem_segment ℝ c v.1 t.2)⟩ := by
  simp [radialPaths, MoorePath.trans_apply_length_add, MoorePath.ofUnitPath_apply]

/-- The fibre homotopy trivialization `fiberHomotopyEquiv` applied to `radialPaths`.
In particular this constructs the comparison over every characteristic disk. Equivariance of
the underlying maps and homotopies is given by `trivializationMap_mul`,
`trivializationInverse_smul`, `trivializationLeftHomotopy_mul` and
`trivializationRightHomotopy_smul`, rather than stored in the returned structure. -/
def radialFiberHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.fst : C(S × MooreLoopSpace X b, S)) (proj χ b) :=
  fiberHomotopyEquiv (radialPaths hS hc χ γ) (source_radialPaths hS hc χ γ)
    (target_radialPaths hS hc χ γ)

@[simp]
theorem radialFiberHomotopyEquiv_toFun :
    (radialFiberHomotopyEquiv hS hc χ γ).toFun =
      trivializationMap (radialPaths hS hc χ γ) (source_radialPaths hS hc χ γ)
        (target_radialPaths hS hc χ γ) := (rfl)

@[simp]
theorem radialFiberHomotopyEquiv_invFun :
    (radialFiberHomotopyEquiv hS hc χ γ).invFun =
      trivializationInverse (radialPaths hS hc χ γ) (source_radialPaths hS hc χ γ)
        (target_radialPaths hS hc χ γ) := (rfl)

end Radial

end MoorePathPullback
end TauCeti
