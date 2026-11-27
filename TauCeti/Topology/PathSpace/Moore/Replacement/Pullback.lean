/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.Pullback
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.PathSpace.Moore.Between.Equiv
public import TauCeti.Topology.PathSpace.Moore.Replacement.Append

/-!
# Trivializing the pullback of the Moore-path replacement along a family of paths

Let `p : E → B` be a continuous map, `E' = {(e, γ) | γ starts at p e}` the total space of its
Moore-path replacement, with end point map `E' → B`, and `F'_b` its fibre over `b`. The pullback
of the end point map along `f : D → B` (`TauCeti.MooreReplacementPullback p f`, the fibre product
`Function.Pullback f (endpoint p)`) consists of the pairs of a parameter `d ∈ D` and a point
`(e, γ)` of `E'` with `γ` ending at `f d`. Its projections are `ContinuousMap.pullbackFst` and
`ContinuousMap.pullbackSnd`, and a map of parameter spaces induces the map of pullbacks
`ContinuousMap.mapPullbackFst`.

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
  Function.Pullback ⇑f ⇑(MooreReplacement.endpoint p)

namespace MooreReplacementPullback

open MooreReplacement

variable {E : Type u} {B : Type v} {D : Type w} [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace D] {p : C(E, B)} {f : C(D, B)} {b : B}

/-- The path of a point of the pullback ends at the image of its parameter. -/
@[simp]
theorem target_path_snd (y : MooreReplacementPullback p f) : y.snd.path.target = f y.fst :=
  (endpoint_apply y.snd).symm.trans y.property.symm

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
  toFun z :=
    ⟨(z.1, z.2.appendFrom (pathFrom τ h₀ z.1)), (endpoint_appendFrom_pathFrom τ h₀ h₁ _ _).symm⟩
  continuous_toFun :=
    (continuous_fst.prodMk (Fiber.continuous_appendFrom.comp
      (continuous_snd.prodMk ((continuous_pathFrom τ h₀).comp continuous_fst)))).subtype_mk
        fun z ↦ (endpoint_appendFrom_pathFrom τ h₀ h₁ z.2 z.1).symm

variable (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d)

@[simp]
theorem fst_trivializationMap (z : D × Fiber p b) :
    (trivializationMap τ h₀ h₁ z).fst = z.1 := (rfl)

@[simp]
theorem snd_trivializationMap (z : D × Fiber p b) :
    (trivializationMap τ h₀ h₁ z).snd = z.2.appendFrom ⟨τ z.1, h₀ z.1⟩ := (rfl)

/-- **Append the reversed chosen path**: a point `(e, γ)` of the pullback over `d` gives the point
`(e, γ ⋆ (τ d)⁻¹)` of the fibre over `b`, together with `d`. -/
def trivializationInverse (τ : C(D, MoorePath B)) (h₀ : ∀ d, (τ d).source = b)
    (h₁ : ∀ d, (τ d).target = f d) : C(MooreReplacementPullback p f, D × Fiber p b) where
  toFun y := (y.fst, Fiber.mk' (MooreReplacement.mk y.snd.point
    (y.snd.path.trans (τ y.fst).symm (by simp [h₁])) (by simp)) (by simp [h₀]))
  continuous_toFun := Function.Pullback.continuous_fst.prodMk (Fiber.continuous_mk' (continuous_mk
    (MooreReplacement.continuous_point.comp Function.Pullback.continuous_snd)
    ((continuous_path.comp Function.Pullback.continuous_snd).moorePath_trans
      (τ.continuous.comp Function.Pullback.continuous_fst).moorePath_symm fun y ↦ by simp [h₁])
    fun y ↦ by simp) fun y ↦ by simp [h₀])

@[simp]
theorem trivializationInverse_fst (y : MooreReplacementPullback p f) :
    (trivializationInverse τ h₀ h₁ y).1 = y.fst := (rfl)

@[simp]
theorem point_val_trivializationInverse_snd (y : MooreReplacementPullback p f) :
    (trivializationInverse τ h₀ h₁ y).2.val.point = y.snd.point := by
  simp [trivializationInverse]

@[simp]
theorem path_val_trivializationInverse_snd (y : MooreReplacementPullback p f) :
    (trivializationInverse τ h₀ h₁ y).2.val.path =
      y.snd.path.trans (τ y.fst).symm (by simp [h₁]) := by
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
      (fun g ↦ (pullbackFst ⇑f ⇑(endpoint p)).comp g = pullbackFst ⇑f ⇑(endpoint p)) where
  toFun z := ⟨(z.2.fst, MooreReplacement.mk z.2.snd.point
    (z.2.snd.path.trans ((pathBetween τ h₀ h₁ z.2.fst).symm.retrace
      (toNNReal z.1 * (τ z.2.fst).length)).toMoorePath (by simp [pathBetween, h₁]))
    (by simp)), by simp⟩
  continuous_toFun := by
    have hsnd := Function.Pullback.continuous_snd.comp
      (continuous_snd : Continuous (Prod.snd : I × MooreReplacementPullback p f → _))
    refine ((Function.Pullback.continuous_fst.comp continuous_snd).prodMk (continuous_mk
      (MooreReplacement.continuous_point.comp hsnd)
      ((continuous_path.comp hsnd).moorePath_trans ?_ _) _)).subtype_mk _
    simp only [MoorePathBetween.toMoorePath_retrace, MoorePathBetween.toMoorePath_symm,
      pathBetween, MoorePathBetween.toMoorePath_mk]
    exact (τ.continuous.comp (Function.Pullback.continuous_fst.comp continuous_snd)).moorePath_symm
      |>.moorePath_retrace ((toNNReal_continuous.comp continuous_fst).mul
        (MoorePath.continuous_length.comp
          (τ.continuous.comp (Function.Pullback.continuous_fst.comp continuous_snd))))
  map_zero_left y := Function.Pullback.ext rfl (MooreReplacement.ext (by simp) (by simp))
  map_one_left y := by
    refine Function.Pullback.ext rfl (MooreReplacement.ext (by simp) ?_)
    simp [pathBetween, MoorePath.trans_assoc, MoorePath.truncate_of_length_le]
  prop' _ := ContinuousMap.ext fun _ ↦ by simp

@[simp]
theorem fst_trivializationRightHomotopy (s : I) (y : MooreReplacementPullback p f) :
    (trivializationRightHomotopy τ h₀ h₁ (s, y)).fst = y.fst := (rfl)

@[simp]
theorem snd_trivializationRightHomotopy (s : I) (y : MooreReplacementPullback p f) :
    (trivializationRightHomotopy τ h₀ h₁ (s, y)).snd =
      MooreReplacement.mk y.snd.point (y.snd.path.trans
        ((MoorePathBetween.symm ⟨τ y.fst, h₀ _, h₁ _⟩).retrace
          (toNNReal s * (τ y.fst).length)).toMoorePath (by simp [h₁])) (by simp) :=
  Function.Pullback.snd_mk _ _

/-- **The pullback of the Moore-path replacement along `f` is fibre homotopy trivial**, given a
continuous family `τ` of Moore paths from `b` to the points `f d`: appending `τ d` is a fibre
homotopy equivalence over `D` from `D × F'_b` to the pullback, with inverse appending the reversal
of `τ d`. -/
def fiberHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.fst : C(D × Fiber p b, D))
      (pullbackFst ⇑f ⇑(endpoint p)) where
  toFun := trivializationMap τ h₀ h₁
  invFun := trivializationInverse τ h₀ h₁
  comp_toFun := ContinuousMap.ext fun _ ↦ by simp
  comp_invFun := ContinuousMap.ext fun _ ↦ by simp
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
