/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Twisting a holomorphic vector bundle at a point

Let `X` be a complex curve, that is a manifold modelled on `𝓘(ℂ)`, let `E → X` be a vector bundle
with model fibre `F` whose transition functions are `C^n` over `𝓘(ℂ)`, and let `x : X`. The point
twist `E(x)` is glued from two pieces: over `X \ {x}` it is `E`, and over the source of the chart
`chartAt ℂ x` its local frames are those of `E` divided by the centred chart coordinate
`z ↦ φ z - φ x`, where `φ = chartAt ℂ x`. Its local sections are the sections of `E` with at most a
simple pole at `x`. For `n = ∞`, or `n = ω`, it is a holomorphic bundle; for a holomorphic line
bundle `L` it is the line bundle `L(x) = L ⊗ 𝒪(x)`.

The construction is Mathlib's `VectorBundleCore` gluing. The charts are indexed by `X × Bool`:
the chart `(y, b)` is the preferred trivialization of `E` at `y`, restricted to the complement
of `x` if `b = false` and to the source of `φ` if `b = true`. The coordinate changes are those of
the preferred trivializations of `E`, multiplied by the scalar `TauCeti.pointTwistFactor`, which
is `φ z - φ x` from the outer piece to the chart disc and its inverse in the other direction. No
second line-bundle carrier is introduced, and the model fibre may have any rank.

Multiplication by the canonical section of `𝒪(x)` is the fibre map `TauCeti.pointTwistMul` from
the fibre of `E` at `z` to the fibre of `E(x)` at `z`. It is an isomorphism off `x`, with inverse
`TauCeti.pointTwistDiv`, and zero at `x`; it sends `C^n` sections to `C^n` sections. The canonical
section `TauCeti.pointTwistSection` of `𝒪(x)`, the twist of the trivial line bundle, is its value
on the constant section `1`. It vanishes exactly at `x`, and in the chart of `𝒪(x)` at `x` it is
the centred chart coordinate, so its zero is simple.

A section `τ` of `E(x)` is read as the section `z ↦ pointTwistDiv F E x z (τ z)` of `E`; as for the
divisor sheaves `TauCeti.RiemannSurface.divisorSections`, this section is normalized to zero at the
allowed pole. Its leading coefficient `z ↦ pointTwistPoleMul F E x z (τ z)` is that section
multiplied by `φ z - φ x` off `x`, and reads `τ x` in the chart of `E` at `x`. The section `τ` is
`C^n` exactly when the first is `C^n` off `x` and the second is `C^n` at `x`
(`TauCeti.contMDiff_pointTwist_section_iff`). Conversely, `TauCeti.pointTwistOfPole` builds a
`C^n` section of `E(x)` from every section of `E` that is `C^n` off `x` and whose product with
`φ z - φ x` extends to a section `C^n` at `x`. Thus the holomorphic sections of `L(x)` are the
sections of `L` with at most a simple pole at `x`.

This supplies the twisted bundle, the canonical section and the section comparison of step 4 of
the closed Riemann–Roch argument for McDuff–Salamon, Theorem C.1.10, stated for arbitrary
holomorphic line bundles. The index and first Chern class comparisons of that step are not
proved here.

## Main definitions

* `TauCeti.pointTwistCoord`: the chart coordinate at `x`, centred at `x`.
* `TauCeti.pointTwistFactor`: the scalar transition function of the two-set cover.
* `TauCeti.pointTwistCore`: the coordinate core of the point twist `E(x)`.
* `TauCeti.pointTwistMul`, `TauCeti.pointTwistDiv` and `TauCeti.pointTwistPoleMul`: fibrewise
  multiplication by the canonical section, its inverse off `x`, and the leading coefficient.
* `TauCeti.pointTwistOfPole`: the section of the point twist defined by a section of `E` with at
  most a simple pole at `x`.
* `TauCeti.pointTwistSection`: the canonical section of `𝒪(x)`.

## Main results

* `TauCeti.pointTwistCore.isContMDiff`: the point twist of a `C^n` bundle is a `C^n` bundle; for
  `n = ∞` over `𝓘(ℂ)` this is its holomorphic structure.
* `TauCeti.contMDiff_pointTwistMul_section`: multiplication by the canonical section preserves
  `C^n` sections.
* `TauCeti.contMDiff_pointTwist_section_iff` and `TauCeti.contMDiff_pointTwistOfPole`: the `C^n`
  sections of the twist are the sections of `E` with at most a simple pole at `x`.
* `TauCeti.contMDiff_pointTwistSection`, `TauCeti.pointTwistSection_eq_zero_iff` and
  `TauCeti.pointTwistCore_localTriv_pointTwistSection`: the canonical section of `𝒪(x)` is
  holomorphic and vanishes exactly at `x`, to first order.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 1, Section 1
  (divisors and line bundles).
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### The two-set cover and its scalar cocycle -/

/-- The chart coordinate at `x`, centred so that it vanishes at `x`. -/
def pointTwistCoord (x z : X) : ℂ := chartAt ℂ x z - chartAt ℂ x x

@[simp] theorem pointTwistCoord_self (x : X) : pointTwistCoord x x = 0 :=
  sub_self (chartAt ℂ x x)

/-- On the source of the chart at `x`, the centred coordinate vanishes only at `x`. -/
theorem pointTwistCoord_eq_zero_iff {x z : X} (hz : z ∈ (chartAt ℂ x).source) :
    pointTwistCoord x z = 0 ↔ z = x := by
  refine ⟨fun h ↦ (chartAt ℂ x).injOn hz (mem_chart_source ℂ x) (sub_eq_zero.1 h), ?_⟩
  rintro rfl
  exact pointTwistCoord_self z

theorem pointTwistCoord_ne_zero {x z : X} (hz : z ∈ (chartAt ℂ x).source) (hzx : z ≠ x) :
    pointTwistCoord x z ≠ 0 :=
  (pointTwistCoord_eq_zero_iff hz).not.2 hzx

/-- The two open sets covering `X` used to twist at `x`: the complement of `x` for `false`, and
the source of the chart at `x` for `true`. -/
def pointTwistBaseSet (x : X) : Bool → Set X
  | false => {x}ᶜ
  | true => (chartAt ℂ x).source

@[simp] theorem pointTwistBaseSet_false (x : X) : pointTwistBaseSet x false = {x}ᶜ := (rfl)

@[simp] theorem pointTwistBaseSet_true (x : X) :
    pointTwistBaseSet x true = (chartAt ℂ x).source := (rfl)

theorem isOpen_pointTwistBaseSet (x : X) (b : Bool) : IsOpen (pointTwistBaseSet x b) := by
  have : T1Space X := ChartedSpace.t1Space ℂ X
  cases b
  · exact isOpen_compl_singleton
  · exact (chartAt ℂ x).open_source

/-- The scalar transition function of the point twist at `x`, from the piece `b` to the piece
`b'`: the centred chart coordinate from the complement of `x` to the chart disc, its inverse in
the other direction, and `1` within a piece. -/
def pointTwistFactor (x : X) : Bool → Bool → X → ℂ
  | false, true, z => pointTwistCoord x z
  | true, false, z => (pointTwistCoord x z)⁻¹
  | false, false, _ => 1
  | true, true, _ => 1

@[simp] theorem pointTwistFactor_self (x : X) (b : Bool) (z : X) :
    pointTwistFactor x b b z = 1 := by
  cases b <;> exact (rfl)

@[simp] theorem pointTwistFactor_false_true (x z : X) :
    pointTwistFactor x false true z = pointTwistCoord x z := (rfl)

@[simp] theorem pointTwistFactor_true_false (x z : X) :
    pointTwistFactor x true false z = (pointTwistCoord x z)⁻¹ := (rfl)

/-- The scalar cocycle identity on a triple overlap. -/
theorem pointTwistFactor_mul {x z : X} {b b' b'' : Bool} (hb : z ∈ pointTwistBaseSet x b)
    (hb' : z ∈ pointTwistBaseSet x b') (hb'' : z ∈ pointTwistBaseSet x b'') :
    pointTwistFactor x b' b'' z * pointTwistFactor x b b' z = pointTwistFactor x b b'' z := by
  cases b <;> cases b' <;> cases b'' <;>
    simp only [pointTwistBaseSet_false, pointTwistBaseSet_true, mem_compl_singleton_iff]
      at hb hb' hb'' <;>
    simp [pointTwistCoord_ne_zero, *]

/-- The cocycle identity with the outer piece as source, which also holds at `x` itself. -/
theorem pointTwistFactor_mul_false {x z : X} {b b' : Bool} (hb : z ∈ pointTwistBaseSet x b)
    (hb' : z ∈ pointTwistBaseSet x b') :
    pointTwistFactor x b b' z * pointTwistFactor x false b z = pointTwistFactor x false b' z := by
  by_cases hzx : z = x
  · subst hzx
    cases b <;> cases b' <;> simp_all
  · exact pointTwistFactor_mul (by simpa using hzx) hb hb'

variable {n : ℕ∞ω} [IsManifold 𝓘(ℂ) n X]

omit [IsManifold 𝓘(ℂ) n X] in
theorem contMDiffOn_pointTwistCoord [IsManifold 𝓘(ℂ) n X] (x : X) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (pointTwistCoord x) (chartAt ℂ x).source :=
  (contMDiffOn_chart (I := 𝓘(ℂ))).sub contMDiffOn_const

/-- The scalar transition functions of the point twist are `C^n` on the overlaps. -/
theorem contMDiffOn_pointTwistFactor (x : X) (b b' : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (pointTwistFactor x b b')
      (pointTwistBaseSet x b ∩ pointTwistBaseSet x b') := by
  cases b <;> cases b'
  · exact contMDiffOn_const
  · exact (contMDiffOn_pointTwistCoord x).mono inter_subset_right
  · refine ((contMDiffOn_pointTwistCoord x).mono inter_subset_left).inv₀ ?_
    rintro z ⟨hz, hzx⟩
    exact pointTwistCoord_ne_zero hz hzx
  · exact contMDiffOn_const

/-- From the complement of `x`, the scalar transition functions are `C^n` on the whole target
piece, including at `x`. -/
theorem contMDiffOn_pointTwistFactor_false (x : X) (b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (pointTwistFactor x false b) (pointTwistBaseSet x b) := by
  cases b
  · exact contMDiffOn_const
  · exact contMDiffOn_pointTwistCoord x

/-- Read in the chart at `x`, the centred coordinate is the translation `w ↦ w - φ x`. -/
theorem pointTwistCoord_chartAt_symm {x : X} {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    pointTwistCoord x ((chartAt ℂ x).symm w) = w - chartAt ℂ x x := by
  rw [pointTwistCoord, (chartAt ℂ x).right_inv hw]

omit [IsManifold 𝓘(ℂ) n X] in
theorem continuousOn_pointTwistFactor (x : X) (b b' : Bool) :
    ContinuousOn (pointTwistFactor x b b') (pointTwistBaseSet x b ∩ pointTwistBaseSet x b') :=
  (contMDiffOn_pointTwistFactor (n := 0) x b b').continuousOn

/-! ### The point-twist core -/

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  (E : X → Type*) [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

open Classical in
/-- The coordinate core of the point twist `E(x)`. The chart `(y, b)` is the preferred
trivialization of `E` at `y` over `pointTwistBaseSet x b`, and the coordinate changes are those of
`E` multiplied by `pointTwistFactor`. -/
def pointTwistCore (x : X) : VectorBundleCore ℂ X F (X × Bool) where
  baseSet i := (trivializationAt F E i.1).baseSet ∩ pointTwistBaseSet x i.2
  isOpen_baseSet i := (trivializationAt F E i.1).open_baseSet.inter (isOpen_pointTwistBaseSet x _)
  indexAt z := (z, decide (z = x))
  mem_baseSet_at z := by
    refine ⟨mem_baseSet_trivializationAt F E z, ?_⟩
    by_cases hzx : z = x
    · subst hzx
      simp
    · simp [hzx]
  coordChange i j z := pointTwistFactor x i.2 j.2 z •
    ((trivializationAt F E i.1).coordChangeL ℂ (trivializationAt F E j.1) z : F →L[ℂ] F)
  coordChange_self i z hz v := by
    rw [pointTwistFactor_self, one_smul, ContinuousLinearEquiv.coe_coe,
      Trivialization.coe_coordChangeL (R := ℂ) _ _ ⟨hz.1, hz.1⟩]
    exact ((trivializationAt F E i.1).linearEquivAt ℂ z hz.1).apply_symm_apply v
  continuousOn_coordChange i j := by
    refine ((continuousOn_pointTwistFactor x i.2 j.2).mono ?_).smul
      ((continuousOn_coordChange ℂ (trivializationAt F E i.1) (trivializationAt F E j.1)).mono ?_)
    · exact fun _ hz ↦ ⟨hz.1.2, hz.2.2⟩
    · exact fun _ hz ↦ ⟨hz.1.1, hz.2.1⟩
  coordChange_comp i j k z hz v := by
    simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, smul_smul,
      ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coe_coordChangeL _ _ ⟨hz.1.1.1, hz.1.2.1⟩,
      Trivialization.coe_coordChangeL _ _ ⟨hz.1.2.1, hz.2.1⟩,
      Trivialization.coe_coordChangeL _ _ ⟨hz.1.1.1, hz.2.1⟩,
      mul_comm, pointTwistFactor_mul hz.1.1.2 hz.1.2.2 hz.2.2]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

variable {F E}

theorem pointTwistCore_baseSet (x : X) (i : X × Bool) :
    (pointTwistCore F E x).baseSet i =
      (trivializationAt F E i.1).baseSet ∩ pointTwistBaseSet x i.2 := (rfl)

@[simp] theorem pointTwistCore_localTriv_baseSet (x : X) (i : X × Bool) :
    ((pointTwistCore F E x).localTriv i).baseSet =
      (trivializationAt F E i.1).baseSet ∩ pointTwistBaseSet x i.2 := (rfl)

open Classical in
@[simp] theorem pointTwistCore_indexAt (x z : X) :
    (pointTwistCore F E x).indexAt z = (z, decide (z = x)) := (rfl)

theorem pointTwistCore_coordChange (x : X) (i j : X × Bool) (z : X) :
    (pointTwistCore F E x).coordChange i j z =
      pointTwistFactor x i.2 j.2 z •
        ((trivializationAt F E i.1).coordChangeL ℂ (trivializationAt F E j.1) z : F →L[ℂ] F) :=
  (rfl)

/-- The point twist of a `C^n` vector bundle is a `C^n` vector bundle. Over `𝓘(ℂ)` with `n = ∞`
this is the holomorphic structure of `E(x)`. -/
instance pointTwistCore.isContMDiff [ContMDiffVectorBundle n F E 𝓘(ℂ)] (x : X) :
    (pointTwistCore F E x).IsContMDiff 𝓘(ℂ) n where
  contMDiffOn_coordChange i j := by
    refine ((contMDiffOn_pointTwistFactor x i.2 j.2).mono ?_).smul
      ((contMDiffOn_coordChangeL (IB := 𝓘(ℂ)) (n := n) (trivializationAt F E i.1)
        (trivializationAt F E j.1)).mono ?_)
    · exact fun _ hz ↦ ⟨hz.1.2, hz.2.2⟩
    · exact fun _ hz ↦ ⟨hz.1.1, hz.2.1⟩

/-- The coordinates of the preferred chart of the point twist at `z₀`. -/
theorem pointTwistCore_trivializationAt_apply (x z₀ : X)
    (p : TotalSpace F (pointTwistCore F E x).Fiber) :
    (trivializationAt F (pointTwistCore F E x).Fiber z₀ p).2 =
      (pointTwistCore F E x).coordChange ((pointTwistCore F E x).indexAt p.proj)
        ((pointTwistCore F E x).indexAt z₀) p.proj p.2 :=
  (rfl)

theorem mem_pointTwistCore_trivializationAt_baseSet {x z₀ z : X} :
    z ∈ (trivializationAt F (pointTwistCore F E x).Fiber z₀).baseSet ↔
      z ∈ (pointTwistCore F E x).baseSet ((pointTwistCore F E x).indexAt z₀) :=
  Iff.rfl

/-! ### Multiplication by the canonical section -/

variable (F E) in
open Classical in
/-- Multiplication by the canonical section of `𝒪(x)`, from the fibre of `E` at `z` to the fibre
of the point twist `E(x)`. In the preferred chart at `z` it is the scalar `1` off `x` and `0` at
`x`. -/
def pointTwistMul (x z : X) : E z →L[ℂ] F :=
  pointTwistFactor x false (decide (z = x)) z • (trivializationAt F E z).continuousLinearMapAt ℂ z

variable (F E) in
open Classical in
/-- The inverse of `pointTwistMul` away from `x`, extended by `0` at `x`: it reads a vector of the
point twist as a vector of `E`, normalized to zero at the allowed pole. -/
def pointTwistDiv (x z : X) : F →L[ℂ] E z :=
  (trivializationAt F E z).symmL ℂ z ∘L
    ((pointTwistFactor x false (decide (z = x)) z)⁻¹ • ContinuousLinearMap.id ℂ F)

variable (F E) in
open Classical in
/-- The leading coefficient of a vector of the point twist, as a vector of `E`: away from `x` it
is `pointTwistDiv` multiplied by the centred chart coordinate, and at `x` it reads the chart of
the point twist at `x` in the chart of `E` at `x`. -/
def pointTwistPoleMul (x z : X) : F →L[ℂ] E z :=
  (trivializationAt F E z).symmL ℂ z ∘L
    (pointTwistFactor x (decide (z = x)) true z • ContinuousLinearMap.id ℂ F)

variable (F E) in
@[simp] theorem pointTwistMul_self (x : X) : pointTwistMul F E x x = 0 := by
  simp only [pointTwistMul, decide_true, pointTwistFactor_false_true, pointTwistCoord_self,
    zero_smul]

variable (F E) in
@[simp] theorem pointTwistDiv_self (x : X) : pointTwistDiv F E x x = 0 := by
  simp only [pointTwistDiv, decide_true, pointTwistFactor_false_true, pointTwistCoord_self,
    inv_zero, zero_smul]
  exact ContinuousLinearMap.comp_zero _

open Classical in
theorem pointTwistMul_apply (x z : X) (v : E z) :
    pointTwistMul F E x z v =
      pointTwistFactor x false (decide (z = x)) z • (trivializationAt F E z ⟨z, v⟩).2 := by
  change pointTwistFactor x false (decide (z = x)) z •
    (trivializationAt F E z).continuousLinearMapAt ℂ z v = _
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℂ _
    (mem_baseSet_trivializationAt F E z)]

open Classical in
theorem pointTwistDiv_apply (x z : X) (w : F) :
    pointTwistDiv F E x z w =
      (trivializationAt F E z).symm z ((pointTwistFactor x false (decide (z = x)) z)⁻¹ • w) :=
  (trivializationAt F E z).symmL_apply (mem_baseSet_trivializationAt F E z) _

open Classical in
theorem pointTwistPoleMul_apply (x z : X) (w : F) :
    pointTwistPoleMul F E x z w =
      (trivializationAt F E z).symm z (pointTwistFactor x (decide (z = x)) true z • w) :=
  (trivializationAt F E z).symmL_apply (mem_baseSet_trivializationAt F E z) _

theorem pointTwistMul_apply_of_ne {x z : X} (h : z ≠ x) (v : E z) :
    pointTwistMul F E x z v = (trivializationAt F E z ⟨z, v⟩).2 := by
  classical
  rw [pointTwistMul_apply, decide_eq_false h, pointTwistFactor_self, one_smul]

theorem pointTwistDiv_apply_of_ne {x z : X} (h : z ≠ x) (w : F) :
    pointTwistDiv F E x z w = (trivializationAt F E z).symm z w := by
  classical
  rw [pointTwistDiv_apply, decide_eq_false h, pointTwistFactor_self, inv_one, one_smul]

theorem pointTwistDiv_pointTwistMul {x z : X} (h : z ≠ x) (v : E z) :
    pointTwistDiv F E x z (pointTwistMul F E x z v) = v := by
  rw [pointTwistDiv_apply_of_ne h, pointTwistMul_apply_of_ne h]
  exact (trivializationAt F E z).symm_apply_apply_mk (mem_baseSet_trivializationAt F E z) v

theorem pointTwistMul_pointTwistDiv {x z : X} (h : z ≠ x) (w : F) :
    pointTwistMul F E x z (pointTwistDiv F E x z w) = w := by
  rw [pointTwistDiv_apply_of_ne h, pointTwistMul_apply_of_ne h]
  exact congrArg Prod.snd
    ((trivializationAt F E z).apply_mk_symm (mem_baseSet_trivializationAt F E z) w)

/-- Away from `x`, the leading coefficient is `pointTwistDiv` multiplied by the centred chart
coordinate. -/
theorem pointTwistPoleMul_eq_smul_pointTwistDiv {x z : X} (h : z ≠ x)
    (w : F) :
    pointTwistPoleMul F E x z w = pointTwistCoord x z • pointTwistDiv F E x z w := by
  classical
  have h₀ := mem_baseSet_trivializationAt F E z
  rw [pointTwistPoleMul_apply, pointTwistDiv_apply, decide_eq_false h, pointTwistFactor_self,
    inv_one, one_smul, pointTwistFactor_false_true,
    ← (trivializationAt F E z).symmL_apply (R := ℂ) h₀,
    ← (trivializationAt F E z).symmL_apply (R := ℂ) h₀, map_smul]

open Classical in
/-- In every chart of the point twist, multiplication by the canonical section is the scalar
`pointTwistFactor x false b` in the corresponding chart of `E`. -/
theorem pointTwistCore_localTriv_pointTwistMul {x z : X} {i : X × Bool}
    (hz : z ∈ (pointTwistCore F E x).baseSet i) (v : E z) :
    ((pointTwistCore F E x).localTriv i ⟨z, pointTwistMul F E x z v⟩).2 =
      pointTwistFactor x false i.2 z • (trivializationAt F E i.1 ⟨z, v⟩).2 := by
  have h₀ : z ∈ (trivializationAt F E z).baseSet := mem_baseSet_trivializationAt F E z
  have hb₀ : z ∈ pointTwistBaseSet x (decide (z = x)) := ((pointTwistCore F E x).mem_baseSet_at z).2
  change (pointTwistFactor x (decide (z = x)) i.2 z •
    ((trivializationAt F E z).coordChangeL ℂ (trivializationAt F E i.1) z : F →L[ℂ] F))
      (pointTwistMul F E x z v) = _
  rw [pointTwistMul_apply, smul_apply, map_smul,
    smul_smul, pointTwistFactor_mul_false hb₀ hz.2, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply _ _ ⟨h₀, hz.1⟩]
  congr 2
  rw [(trivializationAt F E z).symm_apply_apply_mk h₀ v]

open Classical in
/-- In every chart of the point twist over the chart disc of `x`, the leading coefficient is the
coordinate in the corresponding chart of `E`. -/
theorem trivializationAt_pointTwistPoleMul {x z : X} {y : X}
    (hz : z ∈ (pointTwistCore F E x).baseSet (y, true)) (w : F) :
    (trivializationAt F E y ⟨z, pointTwistPoleMul F E x z w⟩).2 =
      ((pointTwistCore F E x).localTriv (y, true) ⟨z, w⟩).2 := by
  have h₀ : z ∈ (trivializationAt F E z).baseSet := mem_baseSet_trivializationAt F E z
  change _ = (pointTwistFactor x (decide (z = x)) true z •
    ((trivializationAt F E z).coordChangeL ℂ (trivializationAt F E y) z : F →L[ℂ] F)) w
  rw [pointTwistPoleMul_apply, smul_apply, ContinuousLinearEquiv.coe_coe, ← map_smul,
    Trivialization.coordChangeL_apply _ _ ⟨h₀, hz.1⟩]

theorem trivializationAt_pointTwistDiv {x z : X} {y : X}
    (hz : z ∈ (pointTwistCore F E x).baseSet (y, false)) (w : F) :
    (trivializationAt F E y ⟨z, pointTwistDiv F E x z w⟩).2 =
      ((pointTwistCore F E x).localTriv (y, false) ⟨z, w⟩).2 := by
  classical
  have h₀ : z ∈ (trivializationAt F E z).baseSet := mem_baseSet_trivializationAt F E z
  have hzx : z ≠ x := hz.2
  change _ = (pointTwistFactor x (decide (z = x)) false z •
    ((trivializationAt F E z).coordChangeL ℂ (trivializationAt F E y) z : F →L[ℂ] F)) w
  rw [pointTwistDiv_apply_of_ne hzx, decide_eq_false hzx, pointTwistFactor_self, one_smul,
    ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply _ _ ⟨h₀, hz.1⟩]

open Classical in
theorem pointTwistCore_trivializationAt (x z : X) :
    trivializationAt F (pointTwistCore F E x).Fiber z =
      (pointTwistCore F E x).localTriv (z, decide (z = x)) :=
  (rfl)

variable (F E) in
theorem pointTwistCore_trivializationAt_self (x : X) :
    trivializationAt F (pointTwistCore F E x).Fiber x =
      (pointTwistCore F E x).localTriv (x, true) := by
  classical
  rw [pointTwistCore_trivializationAt, decide_eq_true rfl]

theorem pointTwistCore_trivializationAt_of_ne {x z : X} (h : z ≠ x) :
    trivializationAt F (pointTwistCore F E x).Fiber z =
      (pointTwistCore F E x).localTriv (z, false) := by
  classical
  rw [pointTwistCore_trivializationAt, decide_eq_false h]

/-! ### Sections of the point twist -/

variable [ContMDiffVectorBundle n F E 𝓘(ℂ)]

/-- Multiplication by the canonical section of `𝒪(x)` sends a section of `E` that is `C^n` at
`z₀` to a section of the point twist that is `C^n` at `z₀`. -/
theorem contMDiffAt_pointTwistMul_section {x z₀ : X} {σ : ∀ z, E z}
    (hσ : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z)) z₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
      (fun z ↦ TotalSpace.mk' F (E := (pointTwistCore F E x).Fiber) z
        (pointTwistMul F E x z (σ z))) z₀ := by
  classical
  have hz₀ := (pointTwistCore F E x).mem_baseSet_at z₀
  refine ((trivializationAt F (pointTwistCore F E x).Fiber z₀).contMDiffAt_section_iff
    (E := (pointTwistCore F E x).Fiber) (s := fun z ↦ pointTwistMul F E x z (σ z))
    (mem_baseSet_trivializationAt F _ z₀)).2 ?_
  rw [(trivializationAt F E z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt F E z₀)] at hσ
  have hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (pointTwistFactor x false (decide (z₀ = x))) z₀ :=
    (contMDiffOn_pointTwistFactor_false x _).contMDiffAt
      ((isOpen_pointTwistBaseSet x _).mem_nhds hz₀.2)
  refine (hf.smul hσ).congr_of_eventuallyEq ?_
  filter_upwards [((pointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  exact pointTwistCore_localTriv_pointTwistMul hz (σ z)

/-- Multiplication by the canonical section of `𝒪(x)` sends `C^n` sections of `E` to `C^n`
sections of the point twist. -/
theorem contMDiff_pointTwistMul_section {x : X} {σ : ∀ z, E z}
    (hσ : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
      (fun z ↦ TotalSpace.mk' F (E := (pointTwistCore F E x).Fiber) z
        (pointTwistMul F E x z (σ z))) :=
  fun z₀ ↦ contMDiffAt_pointTwistMul_section (hσ z₀)

/-- Away from `x`, a section of the point twist is `C^n` exactly when it is `C^n` as a section of
`E`. -/
theorem contMDiffAt_pointTwist_section_iff_of_ne {x z₀ : X} (h : z₀ ≠ x)
    {τ : ∀ z, (pointTwistCore F E x).Fiber z} :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)) z₀ ↔
      ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
        (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) z₀ := by
  have hz₀ : z₀ ∈ (pointTwistCore F E x).baseSet (z₀, false) :=
    ⟨mem_baseSet_trivializationAt F E z₀, h⟩
  rw [(trivializationAt F (pointTwistCore F E x).Fiber z₀).contMDiffAt_section_iff
      (mem_baseSet_trivializationAt F _ z₀),
    (trivializationAt F E z₀).contMDiffAt_section_iff (mem_baseSet_trivializationAt F E z₀),
    pointTwistCore_trivializationAt_of_ne h]
  refine Filter.EventuallyEq.contMDiffAt_iff ?_
  filter_upwards [((pointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  exact (trivializationAt_pointTwistDiv hz (τ z)).symm

/-- At `x`, a section of the point twist is `C^n` exactly when its leading coefficient is `C^n` as
a section of `E`. -/
theorem contMDiffAt_pointTwist_section_iff_self {x : X}
    {τ : ∀ z, (pointTwistCore F E x).Fiber z} :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)) x ↔
      ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
        (fun z ↦ TotalSpace.mk' F z (pointTwistPoleMul F E x z (τ z))) x := by
  have hx : x ∈ (pointTwistCore F E x).baseSet (x, true) :=
    ⟨mem_baseSet_trivializationAt F E x, mem_chart_source ℂ x⟩
  rw [(trivializationAt F (pointTwistCore F E x).Fiber x).contMDiffAt_section_iff
      (mem_baseSet_trivializationAt F _ x),
    (trivializationAt F E x).contMDiffAt_section_iff (mem_baseSet_trivializationAt F E x),
    pointTwistCore_trivializationAt_self]
  refine Filter.EventuallyEq.contMDiffAt_iff ?_
  filter_upwards [((pointTwistCore F E x).isOpen_baseSet _).mem_nhds hx] with z hz
  exact (trivializationAt_pointTwistPoleMul hz (τ z)).symm

/-- The `C^n` sections of the point twist `E(x)` are the sections of `E` with at most a simple
pole at `x`: a section `τ` of `E(x)` is `C^n` exactly when, read as a section of `E`, it is `C^n`
off `x`, and its product with the centred chart coordinate extends to a section of `E` that is
`C^n` at `x`, namely its leading coefficient. -/
theorem contMDiff_pointTwist_section_iff {x : X} {τ : ∀ z, (pointTwistCore F E x).Fiber z} :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)) ↔
      ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
          (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) {x}ᶜ ∧
        ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
          (fun z ↦ TotalSpace.mk' F z (pointTwistPoleMul F E x z (τ z))) x := by
  have : T1Space X := ChartedSpace.t1Space ℂ X
  refine ⟨fun h ↦ ⟨fun z hz ↦ ((contMDiffAt_pointTwist_section_iff_of_ne hz).1
    (h z)).contMDiffWithinAt, contMDiffAt_pointTwist_section_iff_self.1 (h x)⟩, ?_⟩
  rintro ⟨h₁, h₂⟩ z
  by_cases hz : z = x
  · subst hz
    exact contMDiffAt_pointTwist_section_iff_self.2 h₂
  · exact (contMDiffAt_pointTwist_section_iff_of_ne hz).2
      (h₁.contMDiffAt (isOpen_compl_singleton.mem_nhds hz))

omit [IsManifold 𝓘(ℂ) n X] [ContMDiffVectorBundle n F E 𝓘(ℂ)] in
open Classical in
variable (F) in
/-- The section of the point twist determined by a section `σ` of `E` with at most a simple pole
at `x`, given a section `ρ` of `E` that agrees with `σ` multiplied by the centred chart coordinate
off `x`. Off `x` it is `pointTwistMul` of `σ`, and at `x` it is the leading coefficient `ρ x`. -/
def pointTwistOfPole (x : X) (σ ρ : ∀ z, E z) (z : X) : (pointTwistCore F E x).Fiber z :=
  if z = x then (trivializationAt F E z ⟨z, ρ z⟩).2 else pointTwistMul F E x z (σ z)

omit [IsManifold 𝓘(ℂ) n X] [ContMDiffVectorBundle n F E 𝓘(ℂ)] in
theorem pointTwistDiv_pointTwistOfPole {x z : X} (h : z ≠ x) (σ ρ : ∀ z, E z) :
    pointTwistDiv F E x z (pointTwistOfPole F x σ ρ z) = σ z := by
  simp only [pointTwistOfPole, h, ↓reduceIte]
  exact pointTwistDiv_pointTwistMul h (σ z)

omit [IsManifold 𝓘(ℂ) n X] [ContMDiffVectorBundle n F E 𝓘(ℂ)] in
theorem pointTwistPoleMul_pointTwistOfPole {x : X} {σ ρ : ∀ z, E z} {z : X}
    (hz : z = x ∨ ρ z = pointTwistCoord x z • σ z) :
    pointTwistPoleMul F E x z (pointTwistOfPole F x σ ρ z) = ρ z := by
  classical
  by_cases h : z = x
  · subst h
    simp only [pointTwistOfPole, ↓reduceIte]
    rw [pointTwistPoleMul_apply, decide_eq_true rfl, pointTwistFactor_self, one_smul]
    exact (trivializationAt F E z).symm_apply_apply_mk (mem_baseSet_trivializationAt F E z) _
  · refine (pointTwistPoleMul_eq_smul_pointTwistDiv h _).trans ?_
    rw [pointTwistDiv_pointTwistOfPole h, hz.resolve_left h]

/-- Conversely to `contMDiff_pointTwist_section_iff`, every section `σ` of `E` that is `C^n` off
`x` and has at most a simple pole at `x`, in the sense that its product with the centred chart
coordinate extends to a section `ρ` that is `C^n` at `x`, comes from a `C^n` section of the point
twist. -/
theorem contMDiff_pointTwistOfPole {x : X} {σ ρ : ∀ z, E z}
    (hσ : ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z)) {x}ᶜ)
    (hρ : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (ρ z)) x)
    (hρσ : ∀ᶠ z in 𝓝[≠] x, ρ z = pointTwistCoord x z • σ z) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n
      (fun z ↦ TotalSpace.mk' F z (pointTwistOfPole F x σ ρ z)) := by
  refine contMDiff_pointTwist_section_iff.2 ⟨hσ.congr fun z hz ↦ ?_, ?_⟩
  · rw [pointTwistDiv_pointTwistOfPole hz]
  · refine hρ.congr_of_eventuallyEq ?_
    have h : ∀ᶠ z in 𝓝 x, z = x ∨ ρ z = pointTwistCoord x z • σ z := by
      rw [← nhdsNE_sup_pure, eventually_sup]
      exact ⟨hρσ.mono fun _ h ↦ Or.inr h, Or.inl rfl⟩
    filter_upwards [h] with z hz
    rw [pointTwistPoleMul_pointTwistOfPole hz]

/-! ### The canonical section of `𝒪(x)` -/

omit [IsManifold 𝓘(ℂ) n X] in
/-- The canonical section of `𝒪(x)`, the point twist of the trivial line bundle: the image of the
constant function `1` under multiplication by the canonical section. -/
def pointTwistSection (x z : X) : (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber z :=
  pointTwistMul ℂ (Bundle.Trivial X ℂ) x z (1 : ℂ)

omit [IsManifold 𝓘(ℂ) n X] in
open Classical in
theorem pointTwistSection_apply (x z : X) :
    pointTwistSection x z = pointTwistFactor x false (decide (z = x)) z := by
  rw [pointTwistSection, pointTwistMul_apply]
  exact mul_one (pointTwistFactor x false (decide (z = x)) z)

omit [IsManifold 𝓘(ℂ) n X] in
/-- The canonical section of `𝒪(x)` vanishes exactly at `x`. -/
@[simp] theorem pointTwistSection_eq_zero_iff {x z : X} : pointTwistSection x z = 0 ↔ z = x := by
  classical
  rw [pointTwistSection_apply]
  by_cases h : z = x
  · subst h
    simp only [decide_true, pointTwistFactor_false_true, pointTwistCoord_self, iff_true]
    rfl
  · simp only [h, decide_false, pointTwistFactor_self, iff_false]
    exact one_ne_zero (α := ℂ)

omit [IsManifold 𝓘(ℂ) n X] in
/-- In the chart of `𝒪(x)` at `x`, the canonical section is the centred chart coordinate, so its
zero at `x` is simple. -/
theorem pointTwistCore_localTriv_pointTwistSection {x z : X} (hz : z ∈ (chartAt ℂ x).source) :
    ((pointTwistCore ℂ (Bundle.Trivial X ℂ) x).localTriv (x, true)
      ⟨z, pointTwistSection x z⟩).2 = pointTwistCoord x z := by
  rw [pointTwistSection, pointTwistCore_localTriv_pointTwistMul ⟨mem_univ z, hz⟩]
  exact mul_one (pointTwistCoord x z)

/-- The canonical section of `𝒪(x)` is `C^n`; over `𝓘(ℂ)` it is holomorphic. -/
theorem contMDiff_pointTwistSection (x : X) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) n
      (fun z ↦ TotalSpace.mk' ℂ z (pointTwistSection x z)) := by
  refine contMDiff_pointTwistMul_section (σ := fun _ ↦ (1 : ℂ)) fun z₀ ↦ ?_
  rw [(trivializationAt ℂ (Bundle.Trivial X ℂ) z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt ℂ _ z₀)]
  exact contMDiffAt_const

end TauCeti
