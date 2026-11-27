/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.PathSpace.Moore.Between.Equiv
public import TauCeti.Topology.PathSpace.Moore.Replacement.Append

/-!
# Trivializing the pullback of the Moore-path replacement along a family of paths

Let `p : E → B` be a continuous map, `E' = {(e, γ) | γ starts at p e}` the total space of its
Moore-path replacement, with end point map `E' → B`, and `F'_b` its fibre over `b`. The pullback
of the end point map along `f : D → B` (`TauCeti.MooreReplacementPullback p f`) consists of the
pairs of a parameter `d ∈ D` and a point `(e, γ)` of `E'` with `γ` ending at `f d`.

A continuous family `τ` of Moore paths, `τ d` from `b` to `f d`, trivializes this pullback up to
fibre homotopy over `D` (`TauCeti.MooreReplacementPullback.fiberHomotopyEquiv`):

`D × F'_b ≃ f^*E'`,  `(d, (e, γ)) ↦ (d, (e, γ ⋆ τ d))`,

with inverse appending the reversal of `τ d`. The two homotopies grow the retracing loops
`τ d ⋆ (τ d)⁻¹`, acting on `F'_b` from behind, and `(τ d)⁻¹ ⋆ τ d`, appended to the paths of the
pullback. The forward map is the append map `TauCeti.MooreReplacement.Fiber.appendFrom` along
`τ d`. No fibration hypothesis on `p` is needed: the replacement is always a fibration.

For the inclusion of the point `b`, the total space `E'` is the space of Moore paths from `b`, the
fibre `F'_b` is its space of Moore loops, and this is the trivialization
`TauCeti.MoorePathPullback.fiberHomotopyEquiv` of the pulled-back based path fibration. Over a cube
or the disk of a cell, the trivialization computes the relative homology of the pullback over the
boundary from the homology of `F'_b`, which is the cell-by-cell input of the comparison between the
homology of `B` with coefficients in the chains of `F'_b` and the homology of `E'`.

## Main definitions

* `TauCeti.MooreReplacementPullback p f`: the pullback of the end point map of the Moore-path
  replacement of `p` along `f`.
* `TauCeti.MooreReplacementPullback.paramMap`: the map of pullbacks induced by a map of
  parameter spaces, an open embedding when that map is one.
* `TauCeti.MooreReplacementPullback.trivializationMap`: `(d, x) ↦ (d, x ⋆ τ d)`.
* `TauCeti.MooreReplacementPullback.trivializationInverse`: `(d, y) ↦ (d, y ⋆ (τ d)⁻¹)`.
* `TauCeti.MooreReplacementPullback.fiberHomotopyEquiv`: the fibre homotopy equivalence over `D`
  between `D × F'_b` and the pullback.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 and §7.2.
-/

public noncomputable section

open scoped NNReal
open unitInterval ContinuousMap

universe u v w

namespace TauCeti

/-- The pullback of the end point map of the Moore-path replacement of `p` along `f`: the pairs of
a parameter `d` and a point `(e, γ)` of the replacement whose path ends at `f d`. -/
abbrev MooreReplacementPullback {E : Type u} {B : Type v} {D : Type w} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace D] (p : C(E, B)) (f : C(D, B)) :=
  {z : D × MooreReplacement p // MooreReplacement.endpoint p z.2 = f z.1}

namespace MooreReplacementPullback

open MooreReplacement

variable {E : Type u} {B : Type v} {D : Type w} [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace D] {p : C(E, B)} {f : C(D, B)} {b : B}

/-- The parameter in `D` of a point of the pullback. -/
def point (y : MooreReplacementPullback p f) : D := y.val.1

/-- The point of the Moore-path replacement underlying a point of the pullback. -/
def replacement (y : MooreReplacementPullback p f) : MooreReplacement p := y.val.2

@[simp]
theorem point_mk (d : D) (x : MooreReplacement p) (h : endpoint p x = f d) :
    point (p := p) (f := f) ⟨(d, x), h⟩ = d := (rfl)

@[simp]
theorem replacement_mk (d : D) (x : MooreReplacement p) (h : endpoint p x = f d) :
    replacement (p := p) (f := f) ⟨(d, x), h⟩ = x := (rfl)

/-- The path of a point of the pullback ends at the image of its parameter. -/
@[simp]
theorem target_path_replacement (y : MooreReplacementPullback p f) :
    y.replacement.path.target = f y.point :=
  (endpoint_apply y.replacement).symm.trans y.property

@[ext]
theorem ext {y y' : MooreReplacementPullback p f} (h : y.point = y'.point)
    (h' : y.replacement = y'.replacement) : y = y' :=
  Subtype.ext (Prod.ext h h')

@[fun_prop]
theorem continuous_point : Continuous (point : MooreReplacementPullback p f → D) :=
  continuous_fst.comp continuous_subtypeVal

@[fun_prop]
theorem continuous_replacement :
    Continuous (replacement : MooreReplacementPullback p f → MooreReplacement p) :=
  continuous_snd.comp continuous_subtypeVal

variable (p f) in
/-- The projection of the pullback to its parameter. -/
def proj : C(MooreReplacementPullback p f, D) :=
  ⟨point, continuous_point⟩

@[simp]
theorem proj_apply (y : MooreReplacementPullback p f) : proj p f y = y.point := (rfl)

variable (p f) in
/-- The projection of the pullback to the total space of the Moore-path replacement. -/
def toMooreReplacement : C(MooreReplacementPullback p f, MooreReplacement p) :=
  ⟨replacement, continuous_replacement⟩

@[simp]
theorem toMooreReplacement_apply (y : MooreReplacementPullback p f) :
    toMooreReplacement p f y = y.replacement := (rfl)

/-- The projection to the replacement lies over `f`: the end point of `y` is `f` of its
parameter. -/
@[simp]
theorem endpoint_comp_toMooreReplacement :
    (endpoint p).comp (toMooreReplacement p f) = f.comp (proj p f) :=
  ContinuousMap.ext fun y ↦ y.property

section ParamMap

variable {D' : Type*} [TopologicalSpace D'] (g : C(D', D))

/-- The map of pullbacks induced by a map `g : D' → D` of parameter spaces: a point of the
replacement over `f (g d')` lies over `d'` in the pullback along `f ∘ g`, and over `g d'` in the
pullback along `f`. -/
def paramMap : C(MooreReplacementPullback p (f.comp g), MooreReplacementPullback p f) :=
  ⟨fun y ↦ ⟨(g y.point, y.replacement), y.property⟩,
    ((g.continuous.comp continuous_point).prodMk continuous_replacement).subtype_mk _⟩

@[simp]
theorem point_paramMap (y : MooreReplacementPullback p (f.comp g)) :
    (paramMap g y).point = g y.point := (rfl)

@[simp]
theorem replacement_paramMap (y : MooreReplacementPullback p (f.comp g)) :
    (paramMap g y).replacement = y.replacement := (rfl)

/-- The points over the image of `g` are exactly the image of the map induced by `g`. -/
theorem range_paramMap : Set.range (paramMap (p := p) (f := f) g) = point ⁻¹' Set.range g := by
  refine Set.Subset.antisymm ?_ fun y ⟨d', hd'⟩ ↦
    ⟨⟨(d', y.replacement), y.property.trans (congrArg f hd'.symm)⟩, ext hd' rfl⟩
  rintro _ ⟨y, rfl⟩
  exact ⟨y.point, rfl⟩

/-- The map induced by an open embedding of parameter spaces is an open embedding. -/
theorem isOpenEmbedding_paramMap (hg : Topology.IsOpenEmbedding g) :
    Topology.IsOpenEmbedding (paramMap (p := p) (f := f) g) := by
  refine ⟨Topology.IsEmbedding.subtypeVal.of_comp_iff.1 ?_, ?_⟩
  · exact (hg.isEmbedding.prodMap Topology.IsEmbedding.id).comp Topology.IsEmbedding.subtypeVal
  · rw [range_paramMap]
    exact hg.isOpen_range.preimage continuous_point

end ParamMap

/-- The chosen path `τ d`, as a Moore path from `b`. -/
private def pathFrom (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b) (d : D) :
    MoorePathFrom B b :=
  ⟨τ d, h₀ d⟩

/-- The chosen path `τ d`, as a Moore path from `b` to `f d`. -/
private def pathBetween (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b)
    (h₁ : ∀ d, (τ d).target = f d) (d : D) : MoorePathBetween B b (f d) :=
  ⟨τ d, h₀ d, h₁ d⟩

private theorem continuous_pathFrom (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b) :
    Continuous (pathFrom τ h₀) :=
  τ.continuous.subtype_mk _

private theorem endpoint_appendFrom_pathFrom (τ : C(D, MoorePath B))
    (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d) (x : Fiber p b) (d : D) :
    endpoint p (x.appendFrom (pathFrom τ h₀ d)) = f d := by
  rw [Fiber.endpoint_appendFrom, pathFrom, MoorePathFrom.toMoorePath_mk, h₁]

/-- **Append the chosen path**: a point `(e, γ)` of the fibre over `b` and a parameter `d` give the
point `(e, γ ⋆ τ d)` of the pullback over `d`. -/
def trivializationMap (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b)
    (h₁ : ∀ d, (τ d).target = f d) : C(D × Fiber p b, MooreReplacementPullback p f) where
  toFun z := ⟨(z.1, z.2.appendFrom (pathFrom τ h₀ z.1)), endpoint_appendFrom_pathFrom τ h₀ h₁ _ _⟩
  continuous_toFun :=
    (continuous_fst.prodMk (Fiber.continuous_appendFrom.comp
      (continuous_snd.prodMk ((continuous_pathFrom τ h₀).comp continuous_fst)))).subtype_mk
        fun z ↦ endpoint_appendFrom_pathFrom τ h₀ h₁ z.2 z.1

variable (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d)

@[simp]
theorem point_trivializationMap (z : D × Fiber p b) :
    (trivializationMap τ h₀ h₁ z).point = z.1 := (rfl)

@[simp]
theorem replacement_trivializationMap (z : D × Fiber p b) :
    (trivializationMap τ h₀ h₁ z).replacement = z.2.appendFrom ⟨τ z.1, h₀ z.1⟩ := (rfl)

/-- **Append the reversed chosen path**: a point `(e, γ)` of the pullback over `d` gives the point
`(e, γ ⋆ (τ d)⁻¹)` of the fibre over `b`, together with `d`. -/
def trivializationInverse (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b)
    (h₁ : ∀ d, (τ d).target = f d) : C(MooreReplacementPullback p f, D × Fiber p b) where
  toFun y := (y.point, Fiber.mk' (MooreReplacement.mk y.replacement.point
    (y.replacement.path.trans (τ y.point).symm (by simp [h₁])) (by simp)) (by simp [h₀]))
  continuous_toFun := continuous_point.prodMk (Fiber.continuous_mk' (continuous_mk
    (MooreReplacement.continuous_point.comp continuous_replacement)
    ((continuous_path.comp continuous_replacement).moorePath_trans
      (τ.continuous.comp continuous_point).moorePath_symm fun y ↦ by simp [h₁])
    fun y ↦ by simp) fun y ↦ by simp [h₀])

@[simp]
theorem trivializationInverse_fst (y : MooreReplacementPullback p f) :
    (trivializationInverse τ h₀ h₁ y).1 = y.point := (rfl)

@[simp]
theorem point_val_trivializationInverse_snd (y : MooreReplacementPullback p f) :
    (trivializationInverse τ h₀ h₁ y).2.val.point = y.replacement.point := by
  simp [trivializationInverse]

@[simp]
theorem path_val_trivializationInverse_snd (y : MooreReplacementPullback p f) :
    (trivializationInverse τ h₀ h₁ y).2.val.path =
      y.replacement.path.trans (τ y.point).symm (by simp [h₁]) := by
  simp [trivializationInverse]

/-- The homotopy on `D × F'_b` from the identity to the inverse after the forward map: the point
`(e, γ)` over `d` is acted on by the growing retracing loop `τ d ⋆ (τ d)⁻¹`. -/
def trivializationLeftHomotopy :
    HomotopyWith (.id (D × Fiber p b))
      ((trivializationInverse τ h₀ h₁).comp (trivializationMap τ h₀ h₁))
      (fun g ↦ ContinuousMap.fst.comp g = ContinuousMap.fst) where
  toFun z := (z.2.1,
    z.2.2.act ((pathBetween τ h₀ h₁ z.2.1).retrace (toNNReal z.1 * (τ z.2.1).length)))
  continuous_toFun := by
    refine continuous_snd.fst.prodMk (Fiber.continuous_act.comp (continuous_snd.snd.prodMk
      (MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_)))
    simp only [Function.comp_def, MoorePathBetween.toMoorePath_retrace, pathBetween,
      MoorePathBetween.toMoorePath_mk]
    exact (τ.continuous.comp continuous_snd.fst).moorePath_retrace
      ((toNNReal_continuous.comp continuous_fst).mul
        (MoorePath.continuous_length.comp (τ.continuous.comp continuous_snd.fst)))
  map_zero_left z := by simp
  map_one_left z := by
    refine Prod.ext rfl (Fiber.ext (MooreReplacement.ext (by simp) ?_))
    simp [pathBetween, MoorePath.trans_assoc, MoorePath.truncate_length]
  prop' _ := ContinuousMap.ext fun _ ↦ rfl

@[simp]
theorem trivializationLeftHomotopy_apply (s : I) (z : D × Fiber p b) :
    trivializationLeftHomotopy τ h₀ h₁ (s, z) =
      (z.1, z.2.act (MoorePathBetween.retrace ⟨τ z.1, h₀ z.1, h₁ z.1⟩
        (toNNReal s * (τ z.1).length))) := (rfl)

/-- The homotopy on the pullback from the identity to the forward map after the inverse: the
growing retracing loop `(τ d)⁻¹ ⋆ τ d` at `f d` is appended to the path of a point over `d`. -/
def trivializationRightHomotopy :
    HomotopyWith (.id (MooreReplacementPullback p f))
      ((trivializationMap τ h₀ h₁).comp (trivializationInverse τ h₀ h₁))
      (fun g ↦ (proj p f).comp g = proj p f) where
  toFun z := ⟨(z.2.point, MooreReplacement.mk z.2.replacement.point
    (z.2.replacement.path.trans ((pathBetween τ h₀ h₁ z.2.point).symm.retrace
      (toNNReal z.1 * (τ z.2.point).length)).toMoorePath (by simp [pathBetween, h₁]))
    (by simp)), by simp⟩
  continuous_toFun := by
    refine ((continuous_point.comp continuous_snd).prodMk (continuous_mk
      (MooreReplacement.continuous_point.comp (continuous_replacement.comp continuous_snd))
      ((continuous_path.comp (continuous_replacement.comp continuous_snd)).moorePath_trans ?_ _)
      _)).subtype_mk _
    simp only [MoorePathBetween.toMoorePath_retrace, MoorePathBetween.toMoorePath_symm,
      pathBetween, MoorePathBetween.toMoorePath_mk]
    exact (τ.continuous.comp (continuous_point.comp continuous_snd)).moorePath_symm
      |>.moorePath_retrace ((toNNReal_continuous.comp continuous_fst).mul
        (MoorePath.continuous_length.comp
          (τ.continuous.comp (continuous_point.comp continuous_snd))))
  map_zero_left y := ext rfl (MooreReplacement.ext (by simp) (by simp))
  map_one_left y := by
    refine ext rfl (MooreReplacement.ext (by simp) ?_)
    simp [pathBetween, MoorePath.trans_assoc, MoorePath.truncate_of_length_le]
  prop' _ := ContinuousMap.ext fun _ ↦ rfl

@[simp]
theorem point_trivializationRightHomotopy (s : I) (y : MooreReplacementPullback p f) :
    (trivializationRightHomotopy τ h₀ h₁ (s, y)).point = y.point := (rfl)

@[simp]
theorem replacement_trivializationRightHomotopy (s : I) (y : MooreReplacementPullback p f) :
    (trivializationRightHomotopy τ h₀ h₁ (s, y)).replacement =
      MooreReplacement.mk y.replacement.point (y.replacement.path.trans
        ((MoorePathBetween.symm ⟨τ y.point, h₀ _, h₁ _⟩).retrace
          (toNNReal s * (τ y.point).length)).toMoorePath (by simp [h₁])) (by simp) := (rfl)

/-- **The pullback of the Moore-path replacement along `f` is fibre homotopy trivial**, given a
continuous family `τ` of Moore paths from `b` to the points `f d`: appending `τ d` is a fibre
homotopy equivalence over `D` from `D × F'_b` to the pullback, with inverse appending the reversal
of `τ d`. -/
def fiberHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.fst : C(D × Fiber p b, D)) (proj p f) where
  toFun := trivializationMap τ h₀ h₁
  invFun := trivializationInverse τ h₀ h₁
  comp_toFun := ContinuousMap.ext fun _ ↦ rfl
  comp_invFun := ContinuousMap.ext fun _ ↦ rfl
  left_inv := ⟨(trivializationLeftHomotopy τ h₀ h₁).symm⟩
  right_inv := ⟨(trivializationRightHomotopy τ h₀ h₁).symm⟩

@[simp]
theorem fiberHomotopyEquiv_toFun :
    (fiberHomotopyEquiv (p := p) τ h₀ h₁).toFun = trivializationMap τ h₀ h₁ := (rfl)

@[simp]
theorem fiberHomotopyEquiv_invFun :
    (fiberHomotopyEquiv (p := p) τ h₀ h₁).invFun = trivializationInverse τ h₀ h₁ := (rfl)

end MooreReplacementPullback

end TauCeti
