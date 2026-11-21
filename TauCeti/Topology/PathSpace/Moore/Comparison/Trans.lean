/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Concatenation under the comparison with the unit interval

The comparison `Path.toMoorePath` of `TauCeti.Topology.PathSpace.Moore.Comparison.Basic` does not
take the concatenation `p.trans q` of two paths on the unit interval to the concatenation of their
Moore paths: the first runs through both paths at double speed in length one, the second runs
through them at unit speed in length two.  The two differ by a reparametrization, and this file
records that they are homotopic through a homotopy that is continuous in the pair of paths and
preserves the end points: `p.toMoorePath.trans q.toMoorePath` is `(p.trans q).toMoorePath.rescale
2` (`Path.transMoorePath_eq_rescale`), and `MoorePath.rescale` from length `1` to length `2` is the
homotopy (`Path.transMoorePathHomotopy`).  This is the compatibility of the comparison with the
concatenation actions of the loop spaces on the path spaces.

For two composable Moore paths `γ` and `δ` the comparison goes the other way: the concatenation on
the unit interval of `γ.toPath` and `δ.toPath` is homotopic to the unit-interval path of
`γ.trans δ`, continuously in the pair and through paths from `γ.source` to `δ.target`
(`TauCeti.MoorePath.toUnitPathTransHomotopy`), by reading `γ.trans δ` along a family
`TauCeti.MoorePath.concatTime` of reparametrizations of the unit interval fixing both ends.

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
* `TauCeti.MoorePath.toUnitPathTransHomotopy`: the homotopy from the concatenation on the unit
  interval of `γ.toPath` and `δ.toPath` to `(γ.trans δ).toUnitPath`, continuous in the composable
  pair `(γ, δ)`.
* `Path.transMooreLoopHomotopy`: `Path.toMooreLoop` is multiplicative up to homotopy.
* `Path.homotopic_mooreLoopTrans_comp_prodMap`: the same for families of loops.
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

/-- The concatenation of the Moore paths of `p` and `q` is the Moore path of `p.trans q`,
reparametrized from length one to length two. -/
theorem _root_.Path.transMoorePath_eq_rescale (p : Path x y) (q : Path y z) :
    p.toMoorePath.trans q.toMoorePath (by simp) = (p.trans q).toMoorePath.rescale 2 := by
  refine MoorePath.ext (by simp [one_add_one_eq_two]) fun t ↦ ?_
  rw [MoorePath.rescale_apply, Path.length_toMoorePath, one_mul, Path.toMoorePath_apply,
    NNReal.coe_div, NNReal.coe_ofNat]
  rcases le_total t 1 with ht | ht
  · have ht' : t ≤ p.toMoorePath.length := by rwa [Path.length_toMoorePath]
    have h2 : (t : ℝ) / 2 ≤ 1 / 2 := by
      rw [div_le_div_iff_of_pos_right two_pos]
      exact_mod_cast ht
    have h3 : (2 : ℝ) * (t / 2) = t := by ring
    rw [MoorePath.trans_apply_of_le _ _ _ ht', Path.extend_trans_of_le_half _ _ h2, h3,
      Path.toMoorePath_apply]
  · have ht' : p.toMoorePath.length ≤ t := by rwa [Path.length_toMoorePath]
    have h2 : (1 : ℝ) / 2 ≤ t / 2 := by
      rw [div_le_div_iff_of_pos_right two_pos]
      exact_mod_cast ht
    have h3 : (2 : ℝ) * (t / 2) - 1 = t - 1 := by ring
    rw [MoorePath.trans_apply_of_length_le _ _ _ ht', Path.extend_trans_of_half_le _ _ h2, h3,
      Path.toMoorePath_apply,
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

/-- For families of loops `f` and `g`, the Moore loops `(a, b) ↦ (f a).trans (g b)` are homotopic
to the products `(a, b) ↦ f a * g b` of Moore loops. -/
theorem homotopic_mooreLoopTrans_comp_prodMap {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (f : C(A, Path x x)) (g : C(B, Path x x)) :
    ((mooreLoopTrans x).comp (f.prodMap g)).Homotopic ((mulMooreLoop x).comp (f.prodMap g)) :=
  ⟨(transMooreLoopHomotopy x).compContinuousMap (f.prodMap g)⟩

end Path

namespace TauCeti

namespace MoorePath

variable {X : Type*} [TopologicalSpace X]

/-! ### Two composable Moore paths read on the unit interval -/

/-- The time at which `MoorePath.toUnitPathTransHomotopy` at stage `τ` reads the concatenation
`γ.trans δ` at `s ∈ [0, 1]`, for `γ` of length `L` and `δ` of length `M`. At `τ = 0` it runs
through `γ` on `[0, 1/2]` and through `δ` on `[1/2, 1]`, as the concatenation of paths on the unit
interval does; at `τ = 1` it runs through `γ.trans δ` at constant speed. -/
def concatTime (τ s : I) (L M : ℝ≥0) : ℝ≥0 :=
  toNNReal (σ τ) * (L * min (2 * toNNReal s) 1 + M * (2 * toNNReal s - 1)) +
    toNNReal τ * ((L + M) * toNNReal s)

theorem continuous_concatTime :
    Continuous fun q : (I × I) × ℝ≥0 × ℝ≥0 ↦ concatTime q.1.1 q.1.2 q.2.1 q.2.2 := by
  unfold concatTime
  fun_prop

theorem continuous_concatTime_right (τ : I) (L M : ℝ≥0) :
    Continuous fun s ↦ concatTime τ s L M := by
  unfold concatTime
  fun_prop

@[simp]
theorem concatTime_zero_right (τ : I) (L M : ℝ≥0) : concatTime τ 0 L M = 0 := by
  simp [concatTime]

@[simp]
theorem concatTime_one_right (τ : I) (L M : ℝ≥0) : concatTime τ 1 L M = L + M := by
  simp [concatTime, tsub_eq_of_eq_add (one_add_one_eq_two (R := ℝ≥0)).symm, ← add_mul]

theorem concatTime_zero_left (s : I) (L M : ℝ≥0) :
    concatTime 0 s L M = L * min (2 * toNNReal s) 1 + M * (2 * toNNReal s - 1) := by
  simp [concatTime]

theorem concatTime_one_left (s : I) (L M : ℝ≥0) :
    concatTime 1 s L M = (L + M) * toNNReal s := by
  simp [concatTime]

/-- The concatenation on the unit interval of the unit-interval paths of two composable Moore
paths, as a continuous map of the pair. -/
def transToUnitPath :
    C({q : MoorePath X × MoorePath X // q.1.target = q.2.source}, C(I, X)) where
  toFun q := (q.val.1.toPath.trans (q.val.2.toPath.cast q.property rfl)).toContinuousMap
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have h₁ : Continuous fun q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source} × I ↦
        q.1.val.1.toPath q.2 := by
      simp only [toPath_apply, ← toUnitPath_apply]
      exact ((continuous_toUnitPath.comp continuous_subtypeVal.fst).comp continuous_fst).eval
        continuous_snd
    have h₂ : Continuous fun q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source} × I ↦
        (q.1.val.2.toPath.cast q.1.property rfl) q.2 := by
      simp only [Path.cast_coe, toPath_apply, ← toUnitPath_apply]
      exact ((continuous_toUnitPath.comp continuous_subtypeVal.snd).comp continuous_fst).eval
        continuous_snd
    exact Path.trans_continuous_family
      (fun q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source} ↦ q.val.1.toPath) h₁
      (fun q ↦ q.val.2.toPath.cast q.property rfl) h₂

@[simp]
theorem transToUnitPath_apply (q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source}) :
    transToUnitPath q =
      (q.val.1.toPath.trans (q.val.2.toPath.cast q.property rfl)).toContinuousMap :=
  (rfl)

/-- The unit-interval path of the concatenation of two composable Moore paths, as a continuous
map of the pair. -/
def toUnitPathTrans :
    C({q : MoorePath X × MoorePath X // q.1.target = q.2.source}, C(I, X)) :=
  ⟨fun q ↦ (q.val.1.trans q.val.2 q.property).toUnitPath, continuous_toUnitPath.comp
    (continuous_subtypeVal.fst.moorePath_trans continuous_subtypeVal.snd fun q ↦ q.property)⟩

@[simp]
theorem toUnitPathTrans_apply (q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source}) :
    toUnitPathTrans q = (q.val.1.trans q.val.2 q.property).toUnitPath :=
  (rfl)

/-- At stage `0`, reading `γ.trans δ` at `concatTime 0 s` is the concatenation on the unit
interval of the unit-interval paths of `γ` and `δ`. -/
theorem trans_apply_concatTime_zero (γ δ : MoorePath X) (h : γ.target = δ.source) (s : I) :
    γ.trans δ h (concatTime 0 s γ.length δ.length) =
      (γ.toPath.trans (δ.toPath.cast h rfl)) s := by
  have hle : 2 * toNNReal s ≤ 1 ↔ (s : ℝ) ≤ 1 / 2 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_toNNReal, NNReal.coe_ofNat, NNReal.coe_one]
    constructor <;> intro <;> linarith
  rw [concatTime_zero_left, Path.trans_apply]
  split_ifs with hs
  · -- On `[0, 1/2]` the reparametrization stays in `γ`, at double speed.
    have h₂ : 2 * toNNReal s ≤ 1 := hle.2 hs
    have hL : γ.length * (2 * toNNReal s) ≤ γ.length :=
      mul_le_of_le_one_right zero_le h₂
    rw [min_eq_left h₂, tsub_eq_zero_of_le h₂, mul_zero, add_zero, trans_apply_of_le _ _ _ hL,
      toPath_apply]
    refine congrArg (fun t ↦ γ (γ.length * t)) (NNReal.eq ?_)
    simp
  · -- On `[1/2, 1]` it runs through `δ`, after the whole of `γ`.
    have h₂ : 1 ≤ 2 * toNNReal s := (not_le.1 (mt hle.1 hs)).le
    rw [min_eq_right h₂, mul_one, trans_apply_length_add, Path.cast_coe, toPath_apply]
    refine congrArg (fun t ↦ δ (δ.length * t)) (NNReal.eq ?_)
    simp [NNReal.coe_sub h₂]

/-- **Concatenation on the unit interval and concatenation of Moore paths agree up to
homotopy**: for composable Moore paths `γ` and `δ`, the homotopy from the concatenation on the
unit interval of `γ.toPath` and `δ.toPath` to the unit-interval path of `γ.trans δ`, continuous in
the pair. At each stage it reads `γ.trans δ` along a reparametrization `concatTime` of the unit
interval fixing both ends, so it runs through paths from `γ.source` to `δ.target`
(`toUnitPathTransHomotopy_apply_zero_right`, `toUnitPathTransHomotopy_apply_one_right`). -/
def toUnitPathTransHomotopy :
    ContinuousMap.Homotopy (transToUnitPath (X := X)) toUnitPathTrans where
  toFun q := ⟨fun s ↦
      q.2.val.1.trans q.2.val.2 q.2.property (concatTime q.1 s q.2.val.1.length q.2.val.2.length),
    (q.2.val.1.trans q.2.val.2 q.2.property).continuous.comp (continuous_concatTime_right _ _ _)⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    -- Uncurried, the map is `((τ, (γ, δ)), s) ↦ (γ.trans δ) (concatTime τ s L M)`.
    exact continuous_eval.comp
      (((continuous_subtypeVal.fst.moorePath_trans continuous_subtypeVal.snd
        fun q ↦ q.property).comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_concatTime.comp
          (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
          ((continuous_length.comp (continuous_subtypeVal.fst.comp
            (continuous_snd.comp continuous_fst))).prodMk
            (continuous_length.comp (continuous_subtypeVal.snd.comp
              (continuous_snd.comp continuous_fst)))))))
  map_zero_left q := ContinuousMap.ext fun s ↦ by
    rw [transToUnitPath_apply, Path.coe_toContinuousMap]
    exact trans_apply_concatTime_zero _ _ _ s
  map_one_left q := ContinuousMap.ext fun s ↦ by
    rw [ContinuousMap.coe_mk, concatTime_one_left, toUnitPathTrans_apply, toUnitPath_apply,
      length_trans]

/-- The path of `toUnitPathTransHomotopy` at stage `τ` reads `γ.trans δ` at `concatTime τ s`. -/
@[simp]
theorem toUnitPathTransHomotopy_apply (τ : I)
    (q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source}) (s : I) :
    toUnitPathTransHomotopy (τ, q) s =
      q.val.1.trans q.val.2 q.property (concatTime τ s q.val.1.length q.val.2.length) :=
  (rfl)

/-- Every stage of `toUnitPathTransHomotopy` starts at the source of the first path. -/
theorem toUnitPathTransHomotopy_apply_zero_right (τ : I)
    (q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source}) :
    toUnitPathTransHomotopy (τ, q) 0 = q.val.1.source := by
  rw [toUnitPathTransHomotopy_apply, concatTime_zero_right, ← source_def, source_trans]

/-- Every stage of `toUnitPathTransHomotopy` ends at the target of the second path. -/
theorem toUnitPathTransHomotopy_apply_one_right (τ : I)
    (q : {q : MoorePath X × MoorePath X // q.1.target = q.2.source}) :
    toUnitPathTransHomotopy (τ, q) 1 = q.val.2.target := by
  rw [toUnitPathTransHomotopy_apply, concatTime_one_right, ← length_trans _ _ q.property,
    ← target_def, target_trans]

end MoorePath

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

private theorem mulToLengthOneToPath_apply (γδ : MooreLoopSpace X x × MooreLoopSpace X x) :
    mulToLengthOneToPath x γδ = (toLengthOne γδ.1 * toLengthOne γδ.2).toPath :=
  (rfl)

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
    rw [(Path.transMooreLoopHomotopy x).apply_one, Path.mulMooreLoop_apply,
      mulToLengthOneToPath_apply, toLengthOne_apply, toLengthOne_apply]

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
