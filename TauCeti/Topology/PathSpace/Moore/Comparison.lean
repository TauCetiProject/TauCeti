/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore
public import TauCeti.Topology.UnitInterval.NNReal
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.UnitInterval

/-!
# Moore paths and paths on the unit interval

Moore paths compare with the fixed-interval model `C(I, X)` of paths parametrized by the unit
interval `I = [0, 1]`.  A path `f : C(I, X)` becomes the Moore path `MoorePath.ofUnitPath f` of
length one, stopped at time one; a Moore path `γ` of length `L` becomes the path
`MoorePath.toUnitPath γ : s ↦ γ (L s)` on the unit interval.  Going from `C(I, X)` to the Moore
paths and back is the identity (`toUnitPath_ofUnitPath`); going from the Moore paths to `C(I, X)`
and back changes the length to one and reparametrizes, and the result is homotopic to the original
path through Moore paths with the same end points (`MoorePath.unitHomotopy`).  So the two path
spaces are homotopy equivalent over `X × X` (`MoorePath.homotopyEquivUnitPath`), and the based
version follows: the Moore loops `MooreLoopSpace X x` are homotopy equivalent to Mathlib's loops
`Path x x` (`MooreLoopSpace.homotopyEquivPath`).

The homotopy is assembled from three pieces, each one a homotopy through maps that preserve the
two end points, so that their composite is one as well (`MoorePath.PreservesEndpoints`,
`ContinuousMap.HomotopyWith`):
* appending a constant path of length `s ∈ [0, 1]` at the target, which only changes the length;
* rescaling (`MoorePath.rescale`) the path of length `L + 1` down to length one, which divides by
  lengths at least one;
* the image of the first homotopy under `ofUnitPath ∘ toUnitPath`.

The detour through length `L + 1` avoids dividing by a length that could be zero.

## Main definitions

* `TauCeti.MoorePath.ofUnitPath`, `TauCeti.MoorePath.toUnitPath`: the comparison maps between
  `C(I, X)` and `MoorePath X`.
* `TauCeti.MoorePath.ofUnitPath_toUnitPath`: going to the unit interval and back is
  `MoorePath.rescale γ 1`, the reparametrization to length one.
* `Path.toMoorePath`, `TauCeti.MoorePath.toPath`, `Path.toMooreLoop`,
  `TauCeti.MooreLoopSpace.toPath`: the based comparison maps.
* `TauCeti.MoorePath.unitHomotopy`: the homotopy from `ofUnitPath ∘ toUnitPath` to the identity
  through end-point preserving maps.
* `TauCeti.MooreLoopSpace.unitHomotopy`: its restriction to the Moore loops at `x`.
* `TauCeti.MoorePath.homotopyEquivUnitPath`: the homotopy equivalence `MoorePath X ≃ₕ C(I, X)`.
* `TauCeti.MooreLoopSpace.homotopyEquivPath`: the homotopy equivalence
  `MooreLoopSpace X x ≃ₕ Path x x` with Mathlib's loop space.

## Main results

* `TauCeti.MoorePath.toUnitPath_ofUnitPath`, `Path.toPath_toMoorePath`, `Path.toPath_toMooreLoop`:
  one composite is the identity on the nose.
* `TauCeti.MoorePath.unitHomotopy_source`, `TauCeti.MoorePath.unitHomotopy_target`: the homotopy
  for the other composite preserves the end points.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open scoped NNReal unitInterval ContinuousMap
open Topology Set unitInterval

namespace TauCeti

namespace MoorePath

variable {X : Type*} [TopologicalSpace X]

/-! ### The comparison maps -/

/-- A path on the unit interval, as a Moore path of length one, stopped at time one. -/
def ofUnitPath (f : C(I, X)) : MoorePath X where
  toFun t := f (projIcc 0 1 zero_le_one t)
  continuous_toFun := f.continuous.comp (continuous_projIcc.comp NNReal.continuous_coe)
  length := 1
  apply_of_length_le' t ht := by
    rw [projIcc_of_right_le zero_le_one (by exact_mod_cast ht), NNReal.coe_one, projIcc_right]

@[simp]
theorem ofUnitPath_apply (f : C(I, X)) (t : ℝ≥0) :
    ofUnitPath f t = f (projIcc 0 1 zero_le_one t) :=
  (rfl)

@[simp]
theorem length_ofUnitPath (f : C(I, X)) : (ofUnitPath f).length = 1 :=
  (rfl)

@[simp]
theorem source_ofUnitPath (f : C(I, X)) : (ofUnitPath f).source = f 0 := by
  rw [source_def, ofUnitPath_apply, NNReal.coe_zero, projIcc_left]
  rfl

@[simp]
theorem target_ofUnitPath (f : C(I, X)) : (ofUnitPath f).target = f 1 := by
  rw [target_def, ofUnitPath_apply, length_ofUnitPath, NNReal.coe_one, projIcc_right]
  rfl

@[fun_prop]
theorem continuous_ofUnitPath : Continuous (ofUnitPath : C(I, X) → MoorePath X) :=
  continuous_iff.2 ⟨continuous_const, ContinuousEval.continuous_eval.comp
    (continuous_fst.prodMk ((continuous_projIcc (h := zero_le_one)).comp
      (NNReal.continuous_coe.comp continuous_snd)))⟩

/-- A Moore path of length `L`, reparametrized to the unit interval: `s ↦ γ (L s)`. -/
def toUnitPath (γ : MoorePath X) : C(I, X) where
  toFun s := γ (γ.length * toNNReal s)
  continuous_toFun := γ.continuous.comp (continuous_const.mul toNNReal_continuous)

@[simp]
theorem toUnitPath_apply (γ : MoorePath X) (s : I) : γ.toUnitPath s = γ (γ.length * toNNReal s) :=
  (rfl)

theorem toUnitPath_zero (γ : MoorePath X) : γ.toUnitPath 0 = γ.source := by
  rw [toUnitPath_apply, toNNReal_zero, mul_zero, source_def]

theorem toUnitPath_one (γ : MoorePath X) : γ.toUnitPath 1 = γ.target := by
  rw [toUnitPath_apply, toNNReal_one, mul_one, target_def]

@[fun_prop]
theorem continuous_toUnitPath : Continuous (toUnitPath : MoorePath X → C(I, X)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ <| continuous_eval.comp <| continuous_fst.prodMk
    ((continuous_length.comp continuous_fst).mul (toNNReal_continuous.comp continuous_snd))

/-- A path on the unit interval, sent to the Moore paths and back, is unchanged. -/
@[simp]
theorem toUnitPath_ofUnitPath (f : C(I, X)) : (ofUnitPath f).toUnitPath = f := by
  ext s
  rw [toUnitPath_apply, ofUnitPath_apply, length_ofUnitPath, one_mul]
  exact congr_arg f (projIcc_val zero_le_one s)

@[simp]
theorem toUnitPath_refl (x : X) : (refl x).toUnitPath = .const I x :=
  ContinuousMap.ext fun _ ↦ by rw [toUnitPath_apply, refl_apply, ContinuousMap.const_apply]

@[simp]
theorem toUnitPath_constOfLength (x : X) (L : ℝ≥0) :
    (constOfLength x L).toUnitPath = .const I x :=
  ContinuousMap.ext fun _ ↦ by rw [toUnitPath_apply, constOfLength_apply, ContinuousMap.const_apply]

@[simp]
theorem ofUnitPath_const (x : X) : ofUnitPath (.const I x) = constOfLength x 1 :=
  ext (by rw [length_ofUnitPath, length_constOfLength]) fun _ ↦ by
    rw [ofUnitPath_apply, ContinuousMap.const_apply, constOfLength_apply]

/-- A Moore path sent to the unit interval and back: the path `t ↦ γ (L · min t 1)` of length
one. -/
theorem ofUnitPath_toUnitPath_apply (γ : MoorePath X) (t : ℝ≥0) :
    ofUnitPath γ.toUnitPath t = γ (γ.length * min t 1) := by
  rw [ofUnitPath_apply, toUnitPath_apply, toNNReal_projIcc]

/-- Sending a Moore path to the unit interval and back reparametrizes it to length one. -/
theorem ofUnitPath_toUnitPath (γ : MoorePath X) : ofUnitPath γ.toUnitPath = γ.rescale 1 := by
  refine ext (by rw [length_ofUnitPath, length_rescale]) fun t ↦ ?_
  rw [ofUnitPath_toUnitPath_apply, rescale_apply, div_one]
  rcases le_total t 1 with ht | ht
  · rw [min_eq_left ht]
  · rw [min_eq_right ht, mul_one, γ.apply_of_length_le le_rfl,
      γ.apply_of_length_le (le_mul_of_one_le_right zero_le ht)]

/-! ### The homotopy from `ofUnitPath ∘ toUnitPath` to the identity -/

/-- A self-map of the Moore paths preserves the end points.  The homotopies below are through such
maps, so they are homotopies over `X × X`. -/
def PreservesEndpoints (f : C(MoorePath X, MoorePath X)) : Prop :=
  ∀ γ, (f γ).source = γ.source ∧ (f γ).target = γ.target

/-- Appending the constant path of length one at the target, as a continuous self-map of the
Moore paths. -/
private def appendOne : C(MoorePath X, MoorePath X) :=
  ⟨fun γ ↦ γ.trans (constOfLength γ.target 1) (source_constOfLength _ _).symm,
    continuous_id.moorePath_trans (continuous_target.moorePath_constOfLength continuous_const)
      fun _ ↦ (source_constOfLength _ _).symm⟩

private theorem appendOne_apply (γ : MoorePath X) :
    appendOne γ = γ.trans (constOfLength γ.target 1) (source_constOfLength _ _).symm :=
  (rfl)

/-- The composite `ofUnitPath ∘ toUnitPath`, bundled: a Moore path, reparametrized to length one
(`ofUnitPath_toUnitPath_apply`). -/
def toLengthOne : C(MoorePath X, MoorePath X) :=
  (⟨ofUnitPath, continuous_ofUnitPath⟩ : C(C(I, X), MoorePath X)).comp
    ⟨toUnitPath, continuous_toUnitPath⟩

@[simp]
theorem toLengthOne_apply (γ : MoorePath X) : toLengthOne γ = ofUnitPath γ.toUnitPath :=
  (rfl)

theorem toLengthOne_eq_rescale_one (γ : MoorePath X) : toLengthOne γ = γ.rescale 1 :=
  ofUnitPath_toUnitPath γ

/-- Appending constant paths of growing length at the target: a homotopy from the identity to
`appendOne` through maps preserving the end points. -/
private def appendHomotopy :
    ContinuousMap.HomotopyWith (ContinuousMap.id (MoorePath X)) appendOne PreservesEndpoints where
  toFun p := p.2.trans (constOfLength p.2.target (toNNReal p.1)) (source_constOfLength _ _).symm
  continuous_toFun := continuous_snd.moorePath_trans
    ((continuous_target.comp continuous_snd).moorePath_constOfLength
      (toNNReal_continuous.comp continuous_fst)) fun _ ↦ (source_constOfLength _ _).symm
  map_zero_left γ := by simp
  map_one_left γ := by simp [appendOne_apply]
  prop' _ _ := ⟨source_trans _ _ _, (target_trans _ _ _).trans (target_constOfLength _ _)⟩

/-- The length `L + 1 - s L` of the rescaled path is at least one. -/
private theorem one_le_rescaleLength (s : I) (L : ℝ≥0) : 1 ≤ L + 1 - toNNReal s * L :=
  le_tsub_of_add_le_left (add_le_add_left (mul_le_of_le_one_left (zero_le : (0 : ℝ≥0) ≤ L)
    (toNNReal_le_one s)) 1)

/-- Rescaling `appendOne γ`, of length `L + 1`, to the length `L + 1 - s L`, which runs from
`L + 1` down to `1` as `s` goes from `0` to `1` and stays at least `1`: a homotopy from `appendOne`
to `toLengthOne ∘ appendOne` through maps preserving the end points. -/
private def rescaleHomotopy :
    ContinuousMap.HomotopyWith appendOne ((toLengthOne (X := X)).comp appendOne)
      PreservesEndpoints where
  toFun p := (appendOne p.2).rescale (p.2.length + 1 - toNNReal p.1 * p.2.length)
  continuous_toFun := by
    have hL : Continuous fun p : I × MoorePath X ↦ p.2.length :=
      continuous_length.comp continuous_snd
    exact (appendOne.continuous.comp continuous_snd).moorePath_rescale
      ((hL.add continuous_const).sub ((toNNReal_continuous.comp continuous_fst).mul hL))
      fun p ↦ (zero_lt_one.trans_le (one_le_rescaleLength _ _)).ne'
  map_zero_left γ := by
    rw [toNNReal_zero, zero_mul, tsub_zero, ← length_constOfLength γ.target 1,
      ← length_trans γ _ (source_constOfLength _ _).symm, ← appendOne_apply, rescale_length]
  map_one_left γ := by
    rw [toNNReal_one, one_mul, add_tsub_cancel_left, ContinuousMap.comp_apply,
      toLengthOne_eq_rescale_one]
  prop' s γ := by
    have hℓ : γ.length + 1 - toNNReal s * γ.length ≠ 0 :=
      (zero_lt_one.trans_le (one_le_rescaleLength _ _)).ne'
    refine ⟨?_, ?_⟩
    · rw [ContinuousMap.coe_mk, source_rescale, appendOne_apply, source_trans]
    · rw [ContinuousMap.coe_mk, target_rescale _ hℓ, appendOne_apply, target_trans,
      target_constOfLength]

/-- The image of `appendHomotopy` under `toLengthOne`: a homotopy from `toLengthOne` to
`toLengthOne ∘ appendOne` through maps preserving the end points. -/
private def roundAppendHomotopy :
    ContinuousMap.HomotopyWith toLengthOne ((toLengthOne (X := X)).comp appendOne)
      PreservesEndpoints where
  toFun p := toLengthOne (appendHomotopy p)
  continuous_toFun := (toLengthOne (X := X)).continuous.comp (appendHomotopy (X := X)).continuous
  map_zero_left γ := by rw [appendHomotopy.apply_zero, ContinuousMap.id_apply]
  map_one_left γ := by rw [appendHomotopy.apply_one, ContinuousMap.comp_apply]
  prop' s γ := by
    have h := appendHomotopy.prop s γ
    refine ⟨?_, ?_⟩
    · rw [ContinuousMap.coe_mk, toLengthOne_apply, source_ofUnitPath, toUnitPath_zero]
      exact h.1
    · rw [ContinuousMap.coe_mk, toLengthOne_apply, target_ofUnitPath, toUnitPath_one]
      exact h.2

/-- **The homotopy from `ofUnitPath ∘ toUnitPath` to the identity** of the Moore paths, through
maps preserving the end points: a Moore path is homotopic, through Moore paths with the same end
points, to its reparametrization to length one. -/
def unitHomotopy :
    ContinuousMap.HomotopyWith toLengthOne (ContinuousMap.id (MoorePath X)) PreservesEndpoints :=
  (roundAppendHomotopy (X := X)).trans ((rescaleHomotopy (X := X)).symm.trans
    (appendHomotopy (X := X)).symm)

theorem unitHomotopy_apply_zero (γ : MoorePath X) :
    unitHomotopy (0, γ) = ofUnitPath γ.toUnitPath :=
  (unitHomotopy (X := X)).apply_zero γ

theorem unitHomotopy_apply_one (γ : MoorePath X) : unitHomotopy (1, γ) = γ :=
  (unitHomotopy (X := X)).apply_one γ

theorem unitHomotopy_source (s : I) (γ : MoorePath X) : (unitHomotopy (s, γ)).source = γ.source :=
  ((unitHomotopy (X := X)).prop s γ).1

theorem unitHomotopy_target (s : I) (γ : MoorePath X) : (unitHomotopy (s, γ)).target = γ.target :=
  ((unitHomotopy (X := X)).prop s γ).2

/-- **Moore paths and paths on the unit interval are homotopy equivalent**, by `toUnitPath` and
`ofUnitPath`; the homotopy `unitHomotopy` preserves the end points, so this is a homotopy
equivalence over `X × X`. -/
def homotopyEquivUnitPath : MoorePath X ≃ₕ C(I, X) where
  toFun := ⟨toUnitPath, continuous_toUnitPath⟩
  invFun := ⟨ofUnitPath, continuous_ofUnitPath⟩
  left_inv := ⟨(unitHomotopy (X := X)).toHomotopy⟩
  right_inv := ⟨(ContinuousMap.Homotopy.refl _).cast rfl (ContinuousMap.ext toUnitPath_ofUnitPath)⟩

@[simp]
theorem homotopyEquivUnitPath_apply (γ : MoorePath X) : homotopyEquivUnitPath γ = γ.toUnitPath :=
  (rfl)

@[simp]
theorem homotopyEquivUnitPath_symm_apply (f : C(I, X)) :
    homotopyEquivUnitPath.symm f = ofUnitPath f :=
  (rfl)

end MoorePath

/-! ### The based comparison -/

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- A path on the unit interval from `x` to `y`, as a Moore path of length one. -/
def _root_.Path.toMoorePath (p : Path x y) : MoorePath X :=
  MoorePath.ofUnitPath p.toContinuousMap

@[simp]
theorem _root_.Path.toMoorePath_apply (p : Path x y) (t : ℝ≥0) :
    p.toMoorePath t = p (projIcc 0 1 zero_le_one t) :=
  (rfl)

@[simp]
theorem _root_.Path.length_toMoorePath (p : Path x y) : p.toMoorePath.length = 1 :=
  (rfl)

@[simp]
theorem _root_.Path.source_toMoorePath (p : Path x y) : p.toMoorePath.source = x :=
  (MoorePath.source_ofUnitPath _).trans p.source

@[simp]
theorem _root_.Path.target_toMoorePath (p : Path x y) : p.toMoorePath.target = y :=
  (MoorePath.target_ofUnitPath _).trans p.target

@[fun_prop]
theorem _root_.Path.continuous_toMoorePath :
    Continuous (Path.toMoorePath : Path x y → MoorePath X) :=
  MoorePath.continuous_ofUnitPath.comp continuous_induced_dom

namespace MoorePath

/-- A Moore path, as a path on the unit interval between its end points. -/
def toPath (γ : MoorePath X) : Path γ.source γ.target where
  toContinuousMap := γ.toUnitPath
  source' := γ.toUnitPath_zero
  target' := γ.toUnitPath_one

@[simp]
theorem toPath_apply (γ : MoorePath X) (s : I) : γ.toPath s = γ (γ.length * toNNReal s) :=
  (rfl)

/-- A path on the unit interval, sent to the Moore paths and back, is unchanged, up to the
identification of its end points. -/
@[simp]
theorem _root_.Path.toPath_toMoorePath (p : Path x y) :
    p.toMoorePath.toPath = p.cast (Path.source_toMoorePath p) (Path.target_toMoorePath p) := by
  ext s
  rw [toPath_apply, Path.cast_coe, Path.length_toMoorePath, one_mul, Path.toMoorePath_apply]
  exact congr_arg p (projIcc_val zero_le_one s)

end MoorePath

namespace MooreLoopSpace

/-- A Moore loop at `x`, as a loop on the unit interval. -/
def toPath (γ : MooreLoopSpace X x) : Path x x :=
  γ.toMoorePath.toPath.cast γ.source_eq.symm γ.target_eq.symm

@[simp]
theorem toPath_apply (γ : MooreLoopSpace X x) (s : I) :
    γ.toPath s = γ.toMoorePath (γ.toMoorePath.length * toNNReal s) :=
  (rfl)

@[fun_prop]
theorem continuous_toPath : Continuous (toPath : MooreLoopSpace X x → Path x x) :=
  continuous_induced_rng.2 (MoorePath.continuous_toUnitPath.comp continuous_toMoorePath)

/-- A loop on the unit interval at `x`, as a Moore loop of length one. -/
def _root_.Path.toMooreLoop (p : Path x x) : MooreLoopSpace X x :=
  ⟨p.toMoorePath, Path.source_toMoorePath p, Path.target_toMoorePath p⟩

@[simp]
theorem _root_.Path.toMoorePath_toMooreLoop (p : Path x x) :
    p.toMooreLoop.toMoorePath = p.toMoorePath :=
  (rfl)

@[fun_prop]
theorem _root_.Path.continuous_toMooreLoop :
    Continuous (Path.toMooreLoop : Path x x → MooreLoopSpace X x) :=
  isEmbedding_toMoorePath.continuous_iff.2 Path.continuous_toMoorePath

/-- A loop on the unit interval, sent to the Moore loops and back, is unchanged. -/
@[simp]
theorem _root_.Path.toPath_toMooreLoop (p : Path x x) : p.toMooreLoop.toPath = p := by
  ext s
  rw [toPath_apply, Path.toMoorePath_toMooreLoop, Path.length_toMoorePath, one_mul,
    Path.toMoorePath_apply]
  exact congr_arg p (projIcc_val zero_le_one s)

/-- The composite `Path.toMooreLoop ∘ toPath`, bundled: a Moore loop reparametrized to length
one. -/
def toLengthOne : C(MooreLoopSpace X x, MooreLoopSpace X x) :=
  (⟨Path.toMooreLoop, Path.continuous_toMooreLoop⟩ : C(Path x x, MooreLoopSpace X x)).comp
    ⟨toPath, continuous_toPath⟩

@[simp]
theorem toLengthOne_apply (γ : MooreLoopSpace X x) : toLengthOne γ = γ.toPath.toMooreLoop :=
  (rfl)

theorem toMoorePath_toLengthOne (γ : MooreLoopSpace X x) :
    (toLengthOne γ).toMoorePath = MoorePath.toLengthOne γ.toMoorePath :=
  (rfl)

/-- The homotopy from `toLengthOne` to the identity of the Moore loops at `x`: the restriction of
`MoorePath.unitHomotopy`, which preserves the end points, to the loops. -/
def unitHomotopy :
    ContinuousMap.Homotopy toLengthOne (ContinuousMap.id (MooreLoopSpace X x)) where
  toFun p := ⟨MoorePath.unitHomotopy (p.1, p.2.toMoorePath),
    (MoorePath.unitHomotopy_source _ _).trans p.2.source_eq,
    (MoorePath.unitHomotopy_target _ _).trans p.2.target_eq⟩
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.2
    ((MoorePath.unitHomotopy (X := X)).continuous.comp
      (continuous_fst.prodMk (continuous_toMoorePath.comp continuous_snd)))
  map_zero_left _ := ext (MoorePath.unitHomotopy_apply_zero _)
  map_one_left _ := ext (MoorePath.unitHomotopy_apply_one _)

@[simp]
theorem toMoorePath_unitHomotopy (s : I) (γ : MooreLoopSpace X x) :
    (unitHomotopy (s, γ)).toMoorePath = MoorePath.unitHomotopy (s, γ.toMoorePath) :=
  (rfl)

theorem unitHomotopy_apply_zero (γ : MooreLoopSpace X x) :
    unitHomotopy (0, γ) = γ.toPath.toMooreLoop :=
  (unitHomotopy (X := X) (x := x)).apply_zero γ

theorem unitHomotopy_apply_one (γ : MooreLoopSpace X x) : unitHomotopy (1, γ) = γ :=
  (unitHomotopy (X := X) (x := x)).apply_one γ

/-- **The Moore loop space is homotopy equivalent to Mathlib's loop space** `Path x x` of loops
parametrized by the unit interval, by `toPath` and `Path.toMooreLoop`. -/
def homotopyEquivPath (x : X) : MooreLoopSpace X x ≃ₕ Path x x where
  toFun := ⟨toPath, continuous_toPath⟩
  invFun := ⟨Path.toMooreLoop, Path.continuous_toMooreLoop⟩
  left_inv := ⟨unitHomotopy⟩
  right_inv :=
    ⟨(ContinuousMap.Homotopy.refl _).cast rfl (ContinuousMap.ext Path.toPath_toMooreLoop)⟩

@[simp]
theorem homotopyEquivPath_apply (γ : MooreLoopSpace X x) : homotopyEquivPath x γ = γ.toPath :=
  (rfl)

@[simp]
theorem homotopyEquivPath_symm_apply (p : Path x x) :
    (homotopyEquivPath x).symm p = p.toMooreLoop :=
  (rfl)

end MooreLoopSpace

end TauCeti
