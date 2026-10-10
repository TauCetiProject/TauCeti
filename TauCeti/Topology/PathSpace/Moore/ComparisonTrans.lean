/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison

/-!
# Concatenation under the comparison with the unit interval

The comparison `Path.toMoorePath` of `TauCeti.Topology.PathSpace.Moore.Comparison` does not take
the concatenation `p.trans q` of two paths on the unit interval to the concatenation of their Moore
paths: the first runs through both paths at double speed in length one, the second runs through
them at unit speed in length two.  The two differ by a reparametrization, and this file records
that they are homotopic through a homotopy that is continuous in the pair of paths and preserves
the end points: `p.toMoorePath.trans q.toMoorePath` is `(p.trans q).toMoorePath.rescale 2`
(`Path.transMoorePath_eq_rescale`), and `MoorePath.rescale` from length `1` to length `2` is the
homotopy (`Path.transMoorePathHomotopy`).  This is the compatibility of the comparison with the
concatenation actions of the loop spaces on the path spaces.

For loops, this says that `Path.toMooreLoop : Path x x → MooreLoopSpace X x` is a monoid
homomorphism up to homotopy (`Path.transMooreLoopHomotopy`), and, through the homotopy
equivalence, so is `MooreLoopSpace.toPath` in the other direction
(`MooreLoopSpace.mulToPathHomotopy`): the homotopy equivalence
`MooreLoopSpace.homotopyEquivPath` is multiplicative up to homotopy in both directions.

## Main results

* `Path.transMoorePath_eq_rescale`: `p.toMoorePath.trans q.toMoorePath` is
  `(p.trans q).toMoorePath` reparametrized to length two.
* `Path.transMoorePathHomotopy`: the homotopy from `(p.trans q).toMoorePath` to
  `p.toMoorePath.trans q.toMoorePath`, continuous in `(p, q)`, through paths from `x` to `z`
  (`transMoorePathHomotopy_source`, `transMoorePathHomotopy_target`).
* `Path.transMooreLoopHomotopy`: `Path.toMooreLoop` is multiplicative up to homotopy.
* `TauCeti.MooreLoopSpace.mulToPathHomotopy`: `MooreLoopSpace.toPath` is multiplicative up to
  homotopy.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public noncomputable section

open scoped NNReal unitInterval
open Topology Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-! ### The concatenation of two Moore paths of length one -/

theorem _root_.Path.toMoorePath_apply_eq_extend (p : Path x y) (t : ℝ≥0) :
    p.toMoorePath t = p.extend t :=
  Path.toMoorePath_apply p t

/-- The concatenation of the Moore paths of `p` and `q` is the Moore path of `p.trans q`,
reparametrized from length one to length two. -/
theorem _root_.Path.transMoorePath_eq_rescale (p : Path x y) (q : Path y z) :
    p.toMoorePath.trans q.toMoorePath (by simp) = (p.trans q).toMoorePath.rescale 2 := by
  refine MoorePath.ext (by simp [one_add_one_eq_two]) fun t ↦ ?_
  rw [MoorePath.rescale_apply, Path.length_toMoorePath, one_mul, Path.toMoorePath_apply_eq_extend,
    NNReal.coe_div, NNReal.coe_ofNat]
  rcases le_total t 1 with ht | ht
  · have ht' : t ≤ p.toMoorePath.length := by rwa [Path.length_toMoorePath]
    have h2 : (t : ℝ) / 2 ≤ 1 / 2 := by
      rw [div_le_div_iff_of_pos_right two_pos]
      exact_mod_cast ht
    rw [MoorePath.trans_apply_of_le _ _ _ ht', Path.extend_trans_of_le_half _ _ h2,
      show (2 : ℝ) * (t / 2) = t by ring, Path.toMoorePath_apply_eq_extend]
  · have ht' : p.toMoorePath.length ≤ t := by rwa [Path.length_toMoorePath]
    have h2 : (1 : ℝ) / 2 ≤ t / 2 := by
      rw [div_le_div_iff_of_pos_right two_pos]
      exact_mod_cast ht
    rw [MoorePath.trans_apply_of_length_le _ _ _ ht', Path.extend_trans_of_half_le _ _ h2,
      show (2 : ℝ) * (t / 2) - 1 = t - 1 by ring, Path.toMoorePath_apply_eq_extend,
      Path.length_toMoorePath, NNReal.coe_sub ht, NNReal.coe_one]

end TauCeti

namespace Path

open TauCeti

variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-- The Moore path of the concatenation of two paths on the unit interval, as a continuous map
of the pair. -/
def moorePathTrans (x y z : X) : C(Path x y × Path y z, MoorePath X) :=
  ⟨fun pq ↦ (pq.1.trans pq.2).toMoorePath,
    Path.continuous_toMoorePath.comp (continuous_fst.path_trans continuous_snd)⟩

@[simp]
theorem moorePathTrans_apply (pq : Path x y × Path y z) :
    moorePathTrans x y z pq = (pq.1.trans pq.2).toMoorePath :=
  (rfl)

/-- The concatenation of the Moore paths of two paths on the unit interval, as a continuous map
of the pair. -/
def transMoorePath (x y z : X) : C(Path x y × Path y z, MoorePath X) :=
  ⟨fun pq ↦ pq.1.toMoorePath.trans pq.2.toMoorePath (by simp),
    (Path.continuous_toMoorePath.comp continuous_fst).moorePath_trans
      (Path.continuous_toMoorePath.comp continuous_snd) fun _ ↦ by simp⟩

@[simp]
theorem transMoorePath_apply (pq : Path x y × Path y z) :
    transMoorePath x y z pq = pq.1.toMoorePath.trans pq.2.toMoorePath (by simp) :=
  (rfl)

/-- **The comparison with the unit interval is compatible with concatenation up to homotopy**:
the homotopy from `(p.trans q).toMoorePath` to `p.toMoorePath.trans q.toMoorePath`, continuous in
the pair `(p, q)`, which reparametrizes the Moore path of `p.trans q` from length `1` to length
`2`. -/
def transMoorePathHomotopy (x y z : X) :
    ContinuousMap.Homotopy (moorePathTrans x y z) (transMoorePath x y z) where
  toFun p := (p.2.1.trans p.2.2).toMoorePath.rescale (1 + toNNReal p.1)
  continuous_toFun :=
    (Path.continuous_toMoorePath.comp
      ((continuous_fst.comp continuous_snd).path_trans (continuous_snd.comp continuous_snd)))
        |>.moorePath_rescale (continuous_const.add (toNNReal_continuous.comp continuous_fst))
          fun _ ↦ (add_pos_of_pos_of_nonneg one_pos zero_le).ne'
  map_zero_left pq := by
    rw [toNNReal_zero, add_zero, ← Path.length_toMoorePath (pq.1.trans pq.2),
      MoorePath.rescale_length, moorePathTrans_apply]
  map_one_left pq := by
    rw [toNNReal_one, one_add_one_eq_two, transMoorePath_apply, Path.transMoorePath_eq_rescale]

theorem transMoorePathHomotopy_apply (s : I) (pq : Path x y × Path y z) :
    transMoorePathHomotopy x y z (s, pq) = (pq.1.trans pq.2).toMoorePath.rescale (1 + toNNReal s) :=
  (rfl)

@[simp]
theorem transMoorePathHomotopy_source (s : I) (pq : Path x y × Path y z) :
    (transMoorePathHomotopy x y z (s, pq)).source = x := by
  rw [transMoorePathHomotopy_apply, MoorePath.source_rescale, Path.source_toMoorePath]

@[simp]
theorem transMoorePathHomotopy_target (s : I) (pq : Path x y × Path y z) :
    (transMoorePathHomotopy x y z (s, pq)).target = z := by
  rw [transMoorePathHomotopy_apply,
    MoorePath.target_rescale _ (add_pos_of_pos_of_nonneg one_pos zero_le).ne',
    Path.target_toMoorePath]

/-! ### Loops -/

/-- The Moore loop of the concatenation of two loops on the unit interval. -/
def mooreLoopTrans (x : X) : C(Path x x × Path x x, MooreLoopSpace X x) :=
  ⟨fun pq ↦ (pq.1.trans pq.2).toMooreLoop,
    Path.continuous_toMooreLoop.comp (continuous_fst.path_trans continuous_snd)⟩

@[simp]
theorem mooreLoopTrans_apply (pq : Path x x × Path x x) :
    mooreLoopTrans x pq = (pq.1.trans pq.2).toMooreLoop :=
  (rfl)

/-- The underlying Moore path of a product of Moore loops of two loops on the unit interval. -/
theorem toMoorePath_mul_toMooreLoop (p q : Path x x) :
    (p.toMooreLoop * q.toMooreLoop).toMoorePath = p.toMoorePath.trans q.toMoorePath (by simp) := by
  rw [MooreLoopSpace.toMoorePath_mul]
  refine MoorePath.ext (by rw [MoorePath.length_trans, MoorePath.length_trans,
    Path.toMoorePath_toMooreLoop, Path.toMoorePath_toMooreLoop]) fun t ↦ ?_
  rw [MoorePath.trans_apply, MoorePath.trans_apply, Path.toMoorePath_toMooreLoop,
    Path.toMoorePath_toMooreLoop]

/-- The product of the Moore loops of two loops on the unit interval. -/
def mulMooreLoop (x : X) : C(Path x x × Path x x, MooreLoopSpace X x) :=
  ⟨fun pq ↦ pq.1.toMooreLoop * pq.2.toMooreLoop,
    (Path.continuous_toMooreLoop.comp continuous_fst).mul
      (Path.continuous_toMooreLoop.comp continuous_snd)⟩

@[simp]
theorem mulMooreLoop_apply (pq : Path x x × Path x x) :
    mulMooreLoop x pq = pq.1.toMooreLoop * pq.2.toMooreLoop :=
  (rfl)

/-- **`Path.toMooreLoop` is multiplicative up to homotopy**: the homotopy from
`(p.trans q).toMooreLoop` to `p.toMooreLoop * q.toMooreLoop`, continuous in `(p, q)`. -/
def transMooreLoopHomotopy (x : X) :
    ContinuousMap.Homotopy (mooreLoopTrans x) (mulMooreLoop x) where
  toFun p := ⟨transMoorePathHomotopy x x x p, transMoorePathHomotopy_source _ _,
    transMoorePathHomotopy_target _ _⟩
  continuous_toFun :=
    MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2
      (transMoorePathHomotopy x x x).continuous
  map_zero_left pq := MooreLoopSpace.ext <| by
    rw [mooreLoopTrans_apply, Path.toMoorePath_toMooreLoop]
    exact (transMoorePathHomotopy x x x).apply_zero pq
  map_one_left pq := MooreLoopSpace.ext <| by
    rw [mulMooreLoop_apply, toMoorePath_mul_toMooreLoop]
    exact (transMoorePathHomotopy x x x).apply_one pq

@[simp]
theorem toMoorePath_transMooreLoopHomotopy (s : I) (pq : Path x x × Path x x) :
    (transMooreLoopHomotopy x (s, pq)).toMoorePath = transMoorePathHomotopy x x x (s, pq) :=
  (rfl)

end Path

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x : X}

namespace MooreLoopSpace

/-- The concatenation of the loops on the unit interval of two Moore loops. -/
def transToPath (x : X) : C(MooreLoopSpace X x × MooreLoopSpace X x, Path x x) :=
  ⟨fun γδ ↦ γδ.1.toPath.trans γδ.2.toPath,
    (continuous_toPath.comp continuous_fst).path_trans (continuous_toPath.comp continuous_snd)⟩

@[simp]
theorem transToPath_apply (γδ : MooreLoopSpace X x × MooreLoopSpace X x) :
    transToPath x γδ = γδ.1.toPath.trans γδ.2.toPath :=
  (rfl)

/-- The loop on the unit interval of the product of two Moore loops. -/
def mulToPath (x : X) : C(MooreLoopSpace X x × MooreLoopSpace X x, Path x x) :=
  ⟨fun γδ ↦ (γδ.1 * γδ.2).toPath, continuous_toPath.comp continuous_mul⟩

@[simp]
theorem mulToPath_apply (γδ : MooreLoopSpace X x × MooreLoopSpace X x) :
    mulToPath x γδ = (γδ.1 * γδ.2).toPath :=
  (rfl)

/-- The intermediate map of `mulToPathHomotopy`: the loop of the product of the two loops
reparametrized to length one. -/
private def mulToLengthOneToPath (x : X) :
    C(MooreLoopSpace X x × MooreLoopSpace X x, Path x x) :=
  ⟨fun γδ ↦ (toLengthOne γδ.1 * toLengthOne γδ.2).toPath,
    continuous_toPath.comp (((toLengthOne (X := X) (x := x)).continuous.comp continuous_fst).mul
      ((toLengthOne (X := X) (x := x)).continuous.comp continuous_snd))⟩

/-- The first half of `mulToPathHomotopy`: `Path.transMooreLoopHomotopy` on the two loops on the
unit interval, read back through `toPath`. -/
private def transToPathHomotopy (x : X) :
    ContinuousMap.Homotopy (transToPath x) (mulToLengthOneToPath x) where
  toFun p := (Path.transMooreLoopHomotopy x (p.1, (p.2.1.toPath, p.2.2.toPath))).toPath
  continuous_toFun := continuous_toPath.comp ((Path.transMooreLoopHomotopy x).continuous.comp
    (continuous_fst.prodMk ((continuous_toPath.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_toPath.comp (continuous_snd.comp continuous_snd)))))
  map_zero_left γδ := by
    rw [(Path.transMooreLoopHomotopy x).apply_zero, Path.mooreLoopTrans_apply,
      Path.toPath_toMooreLoop, transToPath_apply]
  map_one_left γδ := by
    rw [(Path.transMooreLoopHomotopy x).apply_one, Path.mulMooreLoop_apply]
    change _ = (toLengthOne γδ.1 * toLengthOne γδ.2).toPath
    rw [toLengthOne_apply, toLengthOne_apply]

/-- The second half of `mulToPathHomotopy`: `unitHomotopy` on both factors, under `mulToPath`. -/
private def mulUnitHomotopy (x : X) :
    ContinuousMap.Homotopy (mulToLengthOneToPath x) (mulToPath x) where
  toFun p := (unitHomotopy (p.1, p.2.1) * unitHomotopy (p.1, p.2.2)).toPath
  continuous_toFun := continuous_toPath.comp
    (((unitHomotopy (X := X) (x := x)).continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
    ((unitHomotopy (X := X) (x := x)).continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  map_zero_left γδ := by
    rw [(unitHomotopy (X := X) (x := x)).apply_zero, (unitHomotopy (X := X) (x := x)).apply_zero]
    rfl
  map_one_left γδ := by
    rw [(unitHomotopy (X := X) (x := x)).apply_one, (unitHomotopy (X := X) (x := x)).apply_one]
    rfl

/-- **`MooreLoopSpace.toPath` is multiplicative up to homotopy**: the homotopy from
`γ.toPath.trans δ.toPath` to `(γ * δ).toPath`, continuous in `(γ, δ)`.  Together with
`Path.transMooreLoopHomotopy`, the homotopy equivalence `homotopyEquivPath` between the Moore loops
and Mathlib's loops is multiplicative up to homotopy in both directions. -/
def mulToPathHomotopy (x : X) : ContinuousMap.Homotopy (transToPath x) (mulToPath x) :=
  (transToPathHomotopy x).trans (mulUnitHomotopy x)

end MooreLoopSpace

end TauCeti
