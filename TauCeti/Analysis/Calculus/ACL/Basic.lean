/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.LineDeriv.Measurable
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# `ACL` and `ACL^p` maps

Let `Ω ⊆ ℝⁿ` be an arbitrary subset (open in the intended applications), with
`ℝⁿ = EuclideanSpace ℝ (Fin n)`, coordinates `xᵢ` and standard basis `eᵢ`, and let `F` be a real
normed space. Openness of `Ω` is assumed only for the `C¹` result.

* `TauCeti.formalDeriv u x` is the *formal derivative* of `u : ℝⁿ → F` at `x`: the continuous
  linear map `ℝⁿ → F` sending `eᵢ` to the partial derivative `∂ᵢu(x) = lineDeriv ℝ u x eᵢ`, which
  is `0` where that derivative does not exist (`TauCeti.formalDeriv_apply_single`). It is the
  Fréchet derivative wherever `u` is differentiable (`TauCeti.formalDeriv_eq_fderiv`), and at `x`
  it depends only on the germ of `u` at `x` (`Filter.EventuallyEq.formalDeriv_eq`).
* `TauCeti.coordinateBox a b` is the closed coordinate box `Π_j [a_j, b_j]`, and
  `TauCeti.lineFunction u x i` is the line function `t ↦ u(x + (t - xᵢ) eᵢ)` of `u` through `x` in
  the `i`-th direction. A box has volume `∏ⱼ ENNReal.ofReal (bⱼ - aⱼ)`
  (`TauCeti.volume_coordinateBox`).
  A point of `ℝⁿ⁺¹` lies in a box iff its `i`-th coordinate lies in `[aᵢ, bᵢ]` and its other
  coordinates lie in the face `Π_{j ≠ i} [a_j, b_j]`
  (`TauCeti.toLp_insertNth_mem_coordinateBox_iff`).
  For `x` in a box and `t ∈ [aᵢ, bᵢ]`, the point `x + (t - xᵢ) eᵢ` stays in the box
  (`TauCeti.add_sub_smul_single_mem_coordinateBox`), and the line function depends only on the
  coordinates of `x` other than the `i`-th (`TauCeti.lineFunction_add_smul_single`). Taking line
  functions commutes with the pointwise operations and with composition
  (`TauCeti.lineFunction_add`, `TauCeti.lineFunction_smul`, `TauCeti.lineFunction_comp`, ...).
* `TauCeti.IsACLOn u Ω`: `u` is continuous on `Ω` and, for every closed coordinate box `Q ⊆ Ω` with
  `aⱼ < bⱼ` for all `j` and every `i`, the line function through `x` is absolutely continuous on
  `[aᵢ, bᵢ]` for almost every `x ∈ Q`.
* `TauCeti.IsACLpOn u p Ω`: `u` is `ACL` on `Ω` and its formal derivative lies in `L^p` on every
  compact subset of `Ω`.

Both classes pass to subsets (`TauCeti.IsACLOn.mono`, `TauCeti.IsACLpOn.mono`), and `ACL^q`
implies `ACL^p` for `p ≤ q` (`TauCeti.IsACLpOn.mono_exponent`). Maps locally Lipschitz on `Ω`
are `ACL` on `Ω` (`LocallyLipschitzOn.isACLOn`); locally Lipschitz maps are `ACL^p` on every set
for every `p`, in particular `ACL^∞` (`LocallyLipschitz.isACLpOn`); maps that are `C¹` on an open
set `Ω` are `ACL^p` on `Ω` for every `p` (`ContDiffOn.isACLpOn`).

## References

* O. Martio, S. Rickman, J. Väisälä, *Definitions for quasiregular mappings*,
  Ann. Acad. Sci. Fenn. Ser. A I 448 (1969). The formal derivative and Definition 2.16 (`ACL` and
  `ACL^p` maps) follow this paper, with closed coordinate boxes in place of open `n`-intervals
  with closure in `Ω`.
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The formal derivative -/

/-- The **formal derivative** of `u : ℝⁿ → F` at `x`: the continuous linear map `ℝⁿ → F` sending
the `i`-th standard basis vector `eᵢ` to the partial derivative `∂ᵢu(x) = lineDeriv ℝ u x eᵢ`,
which is `0` where that partial derivative does not exist. -/
def formalDeriv (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] F :=
  ∑ i, (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin n))).smulRight
    (lineDeriv ℝ u x (EuclideanSpace.single i 1))

/-- The formal derivative applied to `v` is `∑ᵢ vᵢ ∂ᵢu(x)`. -/
theorem formalDeriv_apply (u : EuclideanSpace ℝ (Fin n) → F) (x v : EuclideanSpace ℝ (Fin n)) :
    formalDeriv u x v = ∑ i, v i • lineDeriv ℝ u x (EuclideanSpace.single i 1) := by
  simp [formalDeriv]

/-- The formal derivative sends the `i`-th standard basis vector to the `i`-th partial
derivative. -/
@[simp]
theorem formalDeriv_apply_single (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    formalDeriv u x (EuclideanSpace.single i 1) = lineDeriv ℝ u x (EuclideanSpace.single i 1) := by
  simp [formalDeriv_apply, PiLp.single_apply]

/-- Where `u` is differentiable, its formal derivative is its Fréchet derivative. -/
theorem formalDeriv_eq_fderiv {u : EuclideanSpace ℝ (Fin n) → F} {x : EuclideanSpace ℝ (Fin n)}
    (hu : DifferentiableAt ℝ u x) : formalDeriv u x = fderiv ℝ u x :=
  EuclideanSpace.ext_continuousLinearMap_single fun i ↦ by
    rw [formalDeriv_apply_single, hu.lineDeriv_eq_fderiv]

/-- The formal derivative at `x` depends only on the germ of the map at `x`. -/
theorem _root_.Filter.EventuallyEq.formalDeriv_eq {u v : EuclideanSpace ℝ (Fin n) → F}
    {x : EuclideanSpace ℝ (Fin n)} (h : u =ᶠ[𝓝 x] v) : formalDeriv u x = formalDeriv v x := by
  ext w
  rw [formalDeriv_apply, formalDeriv_apply]
  simp_rw [h.lineDeriv_eq]

/-- The norm of the formal derivative is at most the sum of the norms of the partial
derivatives. -/
theorem norm_formalDeriv_le (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) :
    ‖formalDeriv u x‖ ≤ ∑ i, ‖lineDeriv ℝ u x (EuclideanSpace.single i 1)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  simpa using PiLp.norm_apply_le v i

/-- The formal derivative of a continuous map is strongly measurable. -/
theorem _root_.Continuous.stronglyMeasurable_formalDeriv [CompleteSpace F]
    {u : EuclideanSpace ℝ (Fin n) → F} (hu : Continuous u) :
    StronglyMeasurable (formalDeriv u) := by
  have (i : Fin n) : StronglyMeasurable fun x ↦
      (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin n))).smulRight
        (lineDeriv ℝ u x (EuclideanSpace.single i 1)) :=
    (StrongDual.smulRightL ℝ _ F (EuclideanSpace.proj i)).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_lineDeriv hu)
  convert Finset.stronglyMeasurable_sum Finset.univ fun i _ ↦ this i using 1
  funext x
  simp [formalDeriv]

/-! ### Coordinate boxes and line functions -/

/-- The closed coordinate box `Π_j [a_j, b_j]` in `ℝⁿ`. -/
def coordinateBox (a b : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ j, x j ∈ Icc (a j) (b j)}

@[simp]
theorem mem_coordinateBox {a b : Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ coordinateBox a b ↔ ∀ j, x j ∈ Icc (a j) (b j) :=
  Iff.rfl

/-- A closed coordinate box is the preimage of the order interval `Icc a b` under the
identification of `ℝⁿ` with `Fin n → ℝ`. -/
theorem coordinateBox_eq_preimage_Icc (a b : Fin n → ℝ) :
    coordinateBox a b = (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b := by
  ext x
  simp [Pi.le_def, forall_and]

/-- The point of `ℝⁿ⁺¹` with `i`-th coordinate `t` and the other coordinates `y` lies in the box
`Π_j [a_j, b_j]` iff `t ∈ [aᵢ, bᵢ]` and `y` lies in the face `Π_{j ≠ i} [a_j, b_j]`. -/
theorem toLp_insertNth_mem_coordinateBox_iff {a b : Fin (n + 1) → ℝ} (i : Fin (n + 1))
    (t : ℝ) (y : Fin n → ℝ) :
    (WithLp.toLp 2 (i.insertNth t y) : EuclideanSpace ℝ (Fin (n + 1))) ∈ coordinateBox a b ↔
      t ∈ Icc (a i) (b i) ∧ y ∈ Icc (fun k ↦ a (i.succAbove k)) (fun k ↦ b (i.succAbove k)) := by
  rw [coordinateBox_eq_preimage_Icc, mem_preimage, PiLp.coe_continuousLinearEquiv,
    WithLp.ofLp_toLp, Fin.insertNth_mem_Icc]

/-- A closed coordinate box is compact. -/
theorem isCompact_coordinateBox (a b : Fin n → ℝ) : IsCompact (coordinateBox a b) := by
  rw [coordinateBox_eq_preimage_Icc]
  exact (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.2 isCompact_Icc

/-- A closed coordinate box is closed. -/
theorem isClosed_coordinateBox (a b : Fin n → ℝ) : IsClosed (coordinateBox a b) :=
  (isCompact_coordinateBox a b).isClosed

/-- A closed coordinate box is measurable. -/
theorem measurableSet_coordinateBox (a b : Fin n → ℝ) : MeasurableSet (coordinateBox a b) :=
  (isClosed_coordinateBox a b).measurableSet

/-- The volume of a closed coordinate box is the product of its side lengths. -/
theorem volume_coordinateBox (a b : Fin n → ℝ) :
    volume (coordinateBox a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [coordinateBox_eq_preimage_Icc, PiLp.coe_continuousLinearEquiv,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]

/-- The **line function** of `u` through `x` in the `i`-th coordinate direction,
`t ↦ u(x + (t - xᵢ) eᵢ)`: its value at `t` is the value of `u` at the point obtained from `x` by
replacing the `i`-th coordinate with `t`. -/
def lineFunction (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (t : ℝ) : F :=
  u (x + (t - x i) • EuclideanSpace.single i 1)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem lineFunction_apply (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (t : ℝ) :
    lineFunction u x i t = u (x + (t - x i) • EuclideanSpace.single i 1) := by
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function at the `i`-th coordinate of `x` is the value of `u` at `x`. -/
@[simp]
theorem lineFunction_self (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : lineFunction u x i (x i) = u x := by
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of a constant map is constant. -/
@[simp]
theorem lineFunction_const (c : F) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (fun _ ↦ c) x i = fun _ ↦ c := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of the zero map is zero. -/
@[simp]
theorem lineFunction_zero [Zero F] (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (0 : EuclideanSpace ℝ (Fin n) → F) x i = 0 := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of a sum is the sum of the line functions. -/
@[simp]
theorem lineFunction_add [Add F] (u v : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (u + v) x i = lineFunction u x i + lineFunction v x i := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of a negative is the negative of the line function. -/
@[simp]
theorem lineFunction_neg [Neg F] (u : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (-u) x i = -lineFunction u x i := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of a difference is the difference of the line functions. -/
@[simp]
theorem lineFunction_sub [Sub F] (u v : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (u - v) x i = lineFunction u x i - lineFunction v x i := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of a constant multiple is the constant multiple of the line function. -/
@[simp]
theorem lineFunction_const_smul {M : Type*} [SMul M F] (c : M) (u : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (c • u) x i = c • lineFunction u x i := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of a pointwise product `g • u` is the product of the line functions. -/
@[simp]
theorem lineFunction_smul {M : Type*} [SMul M F] (g : EuclideanSpace ℝ (Fin n) → M)
    (u : EuclideanSpace ℝ (Fin n) → F) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (g • u) x i = lineFunction g x i • lineFunction u x i := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function of `L ∘ u` is `L` composed with the line function of `u`. -/
@[simp]
theorem lineFunction_comp {F' : Type*} (L : F → F') (u : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    lineFunction (L ∘ u) x i = L ∘ lineFunction u x i := by
  funext
  simp [lineFunction]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The line function through `x` in the `i`-th direction depends only on the coordinates of `x`
other than the `i`-th. -/
theorem lineFunction_add_smul_single (u : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s : ℝ) :
    lineFunction u (x + s • EuclideanSpace.single i 1) i = lineFunction u x i := by
  funext t
  simp only [lineFunction]
  congr 1
  ext j
  rw [EuclideanSpace.add_sub_smul_single_apply, EuclideanSpace.add_sub_smul_single_apply]
  split_ifs with h
  · rfl
  · simp [h]

/-- For `x` in a coordinate box and `t ∈ [aᵢ, bᵢ]`, the point `x + (t - xᵢ) eᵢ` lies in the box:
the segment of the line function through `x` is the one of the box. -/
theorem add_sub_smul_single_mem_coordinateBox {a b : Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ coordinateBox a b) {i : Fin n} {t : ℝ} (ht : t ∈ Icc (a i) (b i)) :
    x + (t - x i) • EuclideanSpace.single i 1 ∈ coordinateBox a b := by
  intro j
  rw [EuclideanSpace.add_sub_smul_single_apply]
  split_ifs with h
  · exact h ▸ ht
  · exact hx j

omit [NormedSpace ℝ F] in
/-- If `u` is `C`-Lipschitz on a closed coordinate box containing `x`, the line function of `u`
through `x` in the `i`-th direction is `C`-Lipschitz on `[aᵢ, bᵢ]`. -/
theorem _root_.LipschitzOnWith.lineFunction {u : EuclideanSpace ℝ (Fin n) → F} {C : ℝ≥0}
    {a b : Fin n → ℝ} (hu : LipschitzOnWith C u (coordinateBox a b))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ coordinateBox a b) (i : Fin n) :
    LipschitzOnWith C (lineFunction u x i) (Icc (a i) (b i)) := by
  have h := hu.comp (EuclideanSpace.lipschitzWith_add_sub_smul_single x i).lipschitzOnWith
    fun t ht ↦ add_sub_smul_single_mem_coordinateBox hx ht
  rwa [mul_one, show u ∘ _ = TauCeti.lineFunction u x i from
    funext fun t ↦ (lineFunction_apply u x i t).symm] at h

/-! ### `ACL` and `ACL^p` maps -/

/-- A map `u : ℝⁿ → F` is **`ACL` on `Ω`** when it is continuous on `Ω` and, for every closed
coordinate box `Q = Π_j [a_j, b_j] ⊆ Ω` with `a_j < b_j` for every `j` and every coordinate `i`,
the line function `t ↦ u(x + (t - xᵢ) eᵢ)` is absolutely continuous on `[aᵢ, bᵢ]` for almost
every `x ∈ Q`. -/
structure IsACLOn (u : EuclideanSpace ℝ (Fin n) → F) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Prop where
  /-- An `ACL` map is continuous. -/
  continuousOn : ContinuousOn u Ω
  /-- Along almost every coordinate segment of a closed box in `Ω`, an `ACL` map is absolutely
  continuous. -/
  ae_absolutelyContinuousOnInterval : ∀ a b : Fin n → ℝ, (∀ j, a j < b j) →
    coordinateBox a b ⊆ Ω → ∀ i, ∀ᵐ x ∂volume.restrict (coordinateBox a b),
      AbsolutelyContinuousOnInterval (lineFunction u x i) (a i) (b i)

/-- A map `u : ℝⁿ → F` is **`ACL^p` on `Ω`**, for an exponent `p`, when it is `ACL` on `Ω` and its
formal derivative lies in `L^p` on every compact subset of `Ω`. -/
structure IsACLpOn (u : EuclideanSpace ℝ (Fin n) → F) (p : ℝ≥0∞)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  /-- An `ACL^p` map is `ACL`. -/
  isACLOn : IsACLOn u Ω
  /-- The formal derivative of an `ACL^p` map is in `L^p` on every compact subset. -/
  memLp_formalDeriv : ∀ K ⊆ Ω, IsCompact K → MemLp (formalDeriv u) p (volume.restrict K)

variable {u : EuclideanSpace ℝ (Fin n) → F} {Ω Ω' : Set (EuclideanSpace ℝ (Fin n))}
  {p q : ℝ≥0∞}

omit [NormedSpace ℝ F] in
/-- `ACL` on `Ω` implies `ACL` on every subset of `Ω`. -/
theorem IsACLOn.mono (hu : IsACLOn u Ω) (hΩ : Ω' ⊆ Ω) : IsACLOn u Ω' where
  continuousOn := hu.continuousOn.mono hΩ
  ae_absolutelyContinuousOnInterval a b hab hQ :=
    hu.ae_absolutelyContinuousOnInterval a b hab (hQ.trans hΩ)

/-- `ACL^p` on `Ω` implies `ACL^p` on every subset of `Ω`. -/
theorem IsACLpOn.mono (hu : IsACLpOn u p Ω) (hΩ : Ω' ⊆ Ω) : IsACLpOn u p Ω' where
  isACLOn := hu.isACLOn.mono hΩ
  memLp_formalDeriv K hK := hu.memLp_formalDeriv K (hK.trans hΩ)

/-- `ACL^q` implies `ACL^p` for `p ≤ q`. -/
theorem IsACLpOn.mono_exponent (hu : IsACLpOn u q Ω) (hpq : p ≤ q) : IsACLpOn u p Ω where
  isACLOn := hu.isACLOn
  memLp_formalDeriv K hKΩ hK :=
    have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
    (hu.memLp_formalDeriv K hKΩ hK).mono_exponent hpq

/-- A map that is `ACL` on `Ω` and whose formal derivative is bounded and almost everywhere
strongly measurable on every compact subset of `Ω` is `ACL^p` on `Ω` for every `p`. -/
theorem IsACLOn.isACLpOn_of_bound (hu : IsACLOn u Ω)
    (h : ∀ K ⊆ Ω, IsCompact K → AEStronglyMeasurable (formalDeriv u) (volume.restrict K) ∧
      ∃ C, ∀ x ∈ K, ‖formalDeriv u x‖ ≤ C) :
    IsACLpOn u p Ω where
  isACLOn := hu
  memLp_formalDeriv K hKΩ hK := by
    have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
    obtain ⟨hm, C, hC⟩ := h K hKΩ hK
    exact (memLp_top_of_bound hm C ((ae_restrict_mem hK.measurableSet).mono hC)).mono_exponent
      le_top

/-! ### Lipschitz and `C¹` maps -/

omit [NormedSpace ℝ F] in
/-- A map locally Lipschitz on `Ω` is `ACL` on `Ω`: on every coordinate segment of a closed box in
`Ω` it is Lipschitz, hence absolutely continuous. -/
theorem _root_.LocallyLipschitzOn.isACLOn (hu : LocallyLipschitzOn Ω u) : IsACLOn u Ω where
  continuousOn := hu.continuousOn
  ae_absolutelyContinuousOnInterval a b hab hQ i := by
    obtain ⟨C, hC⟩ := (hu.mono hQ).exists_lipschitzOnWith_of_compact (isCompact_coordinateBox a b)
    refine (ae_restrict_mem (measurableSet_coordinateBox a b)).mono fun x hx ↦ ?_
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := C) ?_
    simpa [uIcc_of_le (hab i).le] using hC.lineFunction hx i

/-- A locally Lipschitz map is `ACL^p` on every set, for every exponent `p`; in particular it is
`ACL^∞`. -/
theorem _root_.LocallyLipschitz.isACLpOn [CompleteSpace F] (hu : LocallyLipschitz u)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (p : ℝ≥0∞) :
    IsACLpOn u p Ω := by
  refine (hu.locallyLipschitzOn.isACLOn).isACLpOn_of_bound fun K _ hK ↦
    ⟨hu.continuous.stronglyMeasurable_formalDeriv.aestronglyMeasurable, ?_⟩
  -- `u` is Lipschitz on the compact neighbourhood `cthickening 1 K` of `K`.
  have hK' : IsCompact (cthickening 1 K) := hK.cthickening
  obtain ⟨C, hC⟩ := hu.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK'
  refine ⟨∑ _i : Fin n, (C : ℝ), fun x hx ↦ (norm_formalDeriv_le u x).trans ?_⟩
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hmem : cthickening 1 K ∈ 𝓝 x := nhds_le_nhdsSet hx (cthickening_mem_nhdsSet K one_pos)
  simpa using norm_lineDeriv_le_of_lipschitzOn ℝ hmem hC (v := EuclideanSpace.single i 1)

/-- A map that is `C¹` on an open set `Ω` is `ACL^p` on `Ω` for every exponent `p`. -/
theorem _root_.ContDiffOn.isACLpOn (hu : ContDiffOn ℝ 1 u Ω) (hΩ : IsOpen Ω) (p : ℝ≥0∞) :
    IsACLpOn u p Ω := by
  have hfd : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have heq : EqOn (formalDeriv u) (fderiv ℝ u) Ω := fun x hx ↦
    formalDeriv_eq_fderiv ((hu.differentiableOn one_ne_zero x hx).differentiableAt
      (hΩ.mem_nhds hx))
  refine (hu.locallyLipschitzOn_of_isOpen hΩ).isACLOn.isACLpOn_of_bound fun K hKΩ hK ↦ ⟨?_, ?_⟩
  · refine ((hfd.mono hKΩ).aestronglyMeasurable hK.measurableSet).congr ?_
    exact (ae_restrict_mem hK.measurableSet).mono fun x hx ↦ (heq (hKΩ hx)).symm
  · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hfd.mono hKΩ)
    exact ⟨C, fun x hx ↦ heq (hKΩ hx) ▸ hC x hx⟩

end TauCeti
