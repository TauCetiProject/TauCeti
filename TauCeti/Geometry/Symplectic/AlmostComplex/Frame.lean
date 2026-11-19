/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Smooth
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Geometry.Symplectic.Transport
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.PolarCompatible

/-!
# The canonical unitary frame of a compatible complex structure

Let `(V, ω)` be a finite-dimensional symplectic vector space whose inner product is the metric
`⟪v, w⟫ = ω(v, J₀ w)` of an `ω`-compatible complex structure `J₀`. Every other `ω`-compatible
complex structure `J` has its own metric `g_J(v, w) = ω(v, J w)`. Its Riesz operator for the inner
product of `V` is `P = -J₀ J`
(`TauCeti.SymplecticForm.continuousLinearMapOfBilin_associatedBilinForm`), and the inverse square
root

`Ψ_J = P ^ (-1/2)`

(`TauCeti.SymplecticForm.unitaryFrame`, the metric change transport
`ContinuousLinearMap.metricChangeTransport` of `g_J`) is the **unitary frame** of `J`:

* it is an isometry from `⟪·, ·⟫` to `g_J`
  (`TauCeti.SymplecticForm.Compatible.apply_unitaryFrame_apply_unitaryFrame`);
* it intertwines the two complex structures, `J Ψ_J = Ψ_J J₀`
  (`TauCeti.SymplecticForm.Compatible.apply_unitaryFrame`);
* it is a linear symplectomorphism of `(V, ω)`
  (`TauCeti.SymplecticForm.Compatible.apply_unitaryFrame_unitaryFrame`);
* it is the identity for `J = J₀` (`TauCeti.SymplecticForm.unitaryFrame_self`).

So `Ψ_J` is a symplectic isomorphism carrying `J₀` to `J`
(`TauCeti.SymplecticForm.Compatible.transport_unitaryFrameEquiv`,
`TauCeti.SymplecticForm.Compatible.isSymplectomorphism_unitaryFrameEquiv`). The intertwining
comes from the identity `J₀ P J₀⁻¹ = P⁻¹`: it shows that `J₀⁻¹ P^(1/2) J₀` is a positive operator
`S` with `S P S = 1`, and the transport is the unique such operator
(`ContinuousLinearMap.metricChangeTransport_eq_iff`).

Unlike a frame built from a choice of basis, `Ψ_J` involves no choices, and it depends smoothly
on `J` (`ContDiffOn.unitaryFrame`). Hence a `C^n` family `J_t` of compatible structures has the
`C^n` family of frames `Ψ_{J_t}`, and when `J_t` is periodic in `t` so are its frames. Along a
Hamiltonian orbit this is a unitary trivialization: it reads the loop of structures `J_t(x(t))`
in the fixed structure `J₀`, as the analysis of the asymptotic operator requires.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Section 2.5
  (compatible complex structures and the polar decomposition of symplectic matrices).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Section 3.1 (unitary trivializations).
-/

public section

noncomputable section

open InnerProductSpace Filter
open scoped RealInnerProductSpace Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J J₀ : AlmostComplexStructure V}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

variable (ω J) in
/-- The **unitary frame** of a complex structure `J`: the inverse square root of the Riesz
operator, for the inner product of `V`, of the metric `ω(·, J ·)`. For an `ω`-compatible `J` it is
an isometry from the inner product of `V` to `ω(·, J ·)`; when the inner product is the metric of
a compatible `J₀`, it is a symplectomorphism carrying `J₀` to `J`. -/
def unitaryFrame : V →L[ℝ] V :=
  (ω.associatedBilinForm J).toContinuousBilinearMap.metricChangeTransport

/-- Unfolding `TauCeti.SymplecticForm.unitaryFrame`. -/
theorem unitaryFrame_def :
    ω.unitaryFrame J = (ω.associatedBilinForm J).toContinuousBilinearMap.metricChangeTransport :=
  (rfl)

/-- The metric `ω(·, J ·)` of a compatible structure has a strictly positive Riesz operator. -/
theorem Compatible.isStrictlyPositive_continuousLinearMapOfBilin (hJ : ω.Compatible J) :
    IsStrictlyPositive (ω.associatedBilinForm J).toContinuousBilinearMap♯ :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.2
    ⟨fun u v ↦ hJ.associatedBilinForm_apply_swap u v, fun _ hv ↦ hJ.associated_pos hv⟩

/-- The unitary frame of a compatible structure is an isometry from the inner product of `V` to
the metric `ω(·, J ·)`. -/
@[simp]
theorem Compatible.apply_unitaryFrame_apply_unitaryFrame (hJ : ω.Compatible J) (u v : V) :
    ω (ω.unitaryFrame J u) (J (ω.unitaryFrame J v)) = ⟪u, v⟫ :=
  ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport
    hJ.isStrictlyPositive_continuousLinearMapOfBilin u v

/-- If the inner product of `V` is the metric `ω(·, J₀ ·)`, the Riesz operator of the metric
`ω(·, J ·)` of a `J`-invariant `ω` is `-J₀ J`. -/
theorem continuousLinearMapOfBilin_associatedBilinForm (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hJ : ω.Invariant J) :
    (ω.associatedBilinForm J).toContinuousBilinearMap♯ =
      -(LinearMap.toContinuousLinearMap J₀.toLinearMap *
        LinearMap.toContinuousLinearMap J.toLinearMap) := by
  refine ContinuousLinearMap.ext fun v ↦ ext_inner_right ℝ fun w ↦ ?_
  rw [continuousLinearMapOfBilin_apply, LinearMap.toContinuousBilinearMap_apply,
    associatedBilinForm_apply, real_inner_comm, ← hg, hJ.associatedBilinForm_apply_swap]
  simp

/-- If the inner product of `V` is the metric `ω(·, J₀ ·)`, a `J`-invariant `ω` has `J = J₀ P` for
the Riesz operator `P` of the metric `ω(·, J ·)`. -/
private theorem toContinuousLinearMap_eq_mul_continuousLinearMapOfBilin
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hJ : ω.Invariant J) :
    LinearMap.toContinuousLinearMap J.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap *
        (ω.associatedBilinForm J).toContinuousBilinearMap♯ := by
  simp [continuousLinearMapOfBilin_associatedBilinForm hg hJ, ← mul_assoc,
    AlmostComplexStructure.toContinuousLinearMap_mul_self]

/-- The unitary frame of the structure `J₀` whose metric is the inner product of `V` is the
identity. -/
@[simp]
theorem unitaryFrame_self (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) : ω.unitaryFrame J₀ = 1 := by
  have hJ₀ : ω.Compatible J₀ := .of_tames (invariant_of_apply_apply_eq_inner hg) fun v hv ↦
    (real_inner_self_pos.2 hv).trans_eq (hg v v).symm
  rw [unitaryFrame_def, ContinuousLinearMap.metricChangeTransport_eq_iff
    hJ₀.isStrictlyPositive_continuousLinearMapOfBilin,
    continuousLinearMapOfBilin_associatedBilinForm hg hJ₀.invariant,
    AlmostComplexStructure.toContinuousLinearMap_mul_self, neg_neg, mul_one, mul_one]
  exact ⟨zero_le_one, rfl⟩

/-- The unitary frame is `-J₀ P^(1/2) J₀` for the Riesz operator `P = -J₀ J`: conjugating by `J₀`
inverts `P`. -/
private theorem unitaryFrame_eq_neg_mul_sqrt_mul (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hJ : ω.Compatible J) :
    ω.unitaryFrame J =
      -(LinearMap.toContinuousLinearMap J₀.toLinearMap) *
        CFC.sqrt (ω.associatedBilinForm J).toContinuousBilinearMap♯ *
          LinearMap.toContinuousLinearMap J₀.toLinearMap := by
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set B := LinearMap.toContinuousLinearMap J.toLinearMap
  set h := (ω.associatedBilinForm J).toContinuousBilinearMap
  have hH := hJ.isStrictlyPositive_continuousLinearMapOfBilin
  have hP : h♯ = -(A * B) := continuousLinearMapOfBilin_associatedBilinForm hg hJ.invariant
  have hAA : A * A = -1 := AlmostComplexStructure.toContinuousLinearMap_mul_self J₀
  have hBB : B * B = -1 := AlmostComplexStructure.toContinuousLinearMap_mul_self J
  set T := h.metricChangeTransport
  set R := CFC.sqrt h♯
  have hRT : R * T = 1 := ContinuousLinearMap.sqrt_mul_metricChangeTransport hH
  have hTR : T * R = 1 := ContinuousLinearMap.metricChangeTransport_mul_sqrt hH
  -- `T * T` is the inverse `-(B * A)` of `h♯ = -(A * B)`.
  have hTT : T * T = -(B * A) := by
    have h2 : h♯ * -(B * A) = 1 := by
      rw [hP, show -(A * B) * -(B * A) = A * (B * B) * A by noncomm_ring, hBB]
      simp [hAA]
    rw [← mul_one (T * T), ← h2, ← mul_assoc,
      ContinuousLinearMap.metricChangeTransport_mul_self_mul hH, one_mul]
  have hstar : star A = -A := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ω.adjoint_eq_neg_of_forall_inner_apply_eq (inner_apply_left_eq_of_apply_apply_eq_inner hg)
  have hpos := star_left_conjugate_nonneg (CFC.sqrt_nonneg h♯) A
  rw [hstar] at hpos
  rw [unitaryFrame_def, ContinuousLinearMap.metricChangeTransport_eq_iff hH]
  refine ⟨hpos, ?_⟩
  -- `A h♯ A = B A = T⁻²`, and `R T T R = 1`.
  have hJP : B = A * h♯ := toContinuousLinearMap_eq_mul_continuousLinearMapOfBilin hg hJ.invariant
  have hAPA : A * h♯ * A = B * A := by rw [hJP]
  calc -A * R * A * h♯ * (-A * R * A)
      = A * R * (A * h♯ * A) * R * A := by noncomm_ring
    _ = -(A * (R * T) * (T * R) * A) := by
        rw [hAPA, ← neg_neg (B * A), ← hTT]
        noncomm_ring
    _ = 1 := by simp [hRT, hTR, hAA]

/-- **The unitary frame intertwines the complex structures**: `J Ψ_J = Ψ_J J₀`, when the inner
product of `V` is the metric `ω(·, J₀ ·)`. -/
theorem Compatible.apply_unitaryFrame (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hJ : ω.Compatible J)
    (v : V) : J (ω.unitaryFrame J v) = ω.unitaryFrame J (J₀ v) := by
  have hH := hJ.isStrictlyPositive_continuousLinearMapOfBilin
  have hAA := AlmostComplexStructure.toContinuousLinearMap_mul_self J₀
  have hRT := ContinuousLinearMap.sqrt_mul_metricChangeTransport hH
  have hΨ := unitaryFrame_eq_neg_mul_sqrt_mul hg hJ
  rw [← unitaryFrame_def] at hRT
  -- Both sides are `J₀ R` for `R = P^(1/2)`: `J = J₀ P = J₀ R R` and `R Ψ = 1`, while
  -- `Ψ J₀ = J₀ R` by the formula `Ψ = -J₀ R J₀`.
  have hL : LinearMap.toContinuousLinearMap J.toLinearMap * ω.unitaryFrame J =
      LinearMap.toContinuousLinearMap J₀.toLinearMap *
        CFC.sqrt (ω.associatedBilinForm J).toContinuousBilinearMap♯ := by
    rw [toContinuousLinearMap_eq_mul_continuousLinearMapOfBilin hg hJ.invariant]
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self _ hH.nonneg]
    rw [mul_assoc, mul_assoc, hRT, mul_one]
  have hR : ω.unitaryFrame J * LinearMap.toContinuousLinearMap J₀.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap *
        CFC.sqrt (ω.associatedBilinForm J).toContinuousBilinearMap♯ := by
    simp [hΨ, mul_assoc, hAA]
  exact congr($(hL.trans hR.symm) v)

/-- **The unitary frame is symplectic**: `ω(Ψ_J u, Ψ_J v) = ω(u, v)`, when the inner product of `V`
is the metric `ω(·, J₀ ·)`. -/
@[simp]
theorem Compatible.apply_unitaryFrame_unitaryFrame (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hJ : ω.Compatible J) (u v : V) :
    ω (ω.unitaryFrame J u) (ω.unitaryFrame J v) = ω u v := by
  -- `ω(a, b) = g_J(a, -J b)` and `-J Ψ v = Ψ (-J₀ v)`.
  have h := hJ.apply_unitaryFrame_apply_unitaryFrame u (-J₀ v)
  rw [map_neg, ← hJ.apply_unitaryFrame hg, map_neg, AlmostComplexStructure.apply_apply,
    neg_neg] at h
  rw [h, inner_neg_right, ← hg, AlmostComplexStructure.apply_apply]
  simp

/-- The unitary frame of a compatible structure as a continuous linear equivalence. Its inverse is
the square root of the Riesz operator of `ω(·, J ·)`. -/
def Compatible.unitaryFrameEquiv (hJ : ω.Compatible J) : V ≃L[ℝ] V :=
  (ω.associatedBilinForm J).toContinuousBilinearMap.metricChangeEquiv
    hJ.isStrictlyPositive_continuousLinearMapOfBilin

/-- The underlying map of `TauCeti.SymplecticForm.Compatible.unitaryFrameEquiv` is the unitary
frame. -/
@[simp]
theorem Compatible.coe_unitaryFrameEquiv (hJ : ω.Compatible J) :
    (hJ.unitaryFrameEquiv : V →L[ℝ] V) = ω.unitaryFrame J :=
  ContinuousLinearMap.coe_metricChangeEquiv _

@[simp]
theorem Compatible.unitaryFrameEquiv_apply (hJ : ω.Compatible J) (v : V) :
    hJ.unitaryFrameEquiv v = ω.unitaryFrame J v :=
  ContinuousLinearMap.metricChangeEquiv_apply _ v

/-- The unitary frame undoes the inverse of
`TauCeti.SymplecticForm.Compatible.unitaryFrameEquiv`. -/
@[simp]
theorem Compatible.unitaryFrame_unitaryFrameEquiv_symm_apply (hJ : ω.Compatible J) (w : V) :
    ω.unitaryFrame J (hJ.unitaryFrameEquiv.symm w) = w := by
  rw [← hJ.unitaryFrameEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse of `TauCeti.SymplecticForm.Compatible.unitaryFrameEquiv` undoes the unitary
frame. -/
@[simp]
theorem Compatible.unitaryFrameEquiv_symm_apply_unitaryFrame (hJ : ω.Compatible J) (v : V) :
    hJ.unitaryFrameEquiv.symm (ω.unitaryFrame J v) = v := by
  rw [← hJ.unitaryFrameEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The inverse of the unitary frame is the square root of the Riesz operator of
`ω(·, J ·)`. -/
theorem Compatible.coe_unitaryFrameEquiv_symm (hJ : ω.Compatible J) :
    (hJ.unitaryFrameEquiv.symm : V →L[ℝ] V) =
      CFC.sqrt (ω.associatedBilinForm J).toContinuousBilinearMap♯ :=
  ContinuousLinearMap.coe_metricChangeEquiv_symm _

/-- The unitary frame of a compatible structure is invertible. -/
theorem Compatible.isInvertible_unitaryFrame (hJ : ω.Compatible J) :
    (ω.unitaryFrame J).IsInvertible :=
  ⟨hJ.unitaryFrameEquiv, hJ.coe_unitaryFrameEquiv⟩

/-- The unitary frame is a linear symplectomorphism of `(V, ω)`. -/
theorem Compatible.isSymplectomorphism_unitaryFrameEquiv (hJ : ω.Compatible J)
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) :
    IsSymplectomorphism ω ω hJ.unitaryFrameEquiv.toLinearEquiv :=
  isSymplectomorphism_iff.2 fun u v ↦ by simpa using hJ.apply_unitaryFrame_unitaryFrame hg u v

/-- The unitary frame carries `J₀` to `J`. -/
theorem Compatible.transport_unitaryFrameEquiv (hJ : ω.Compatible J)
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) :
    J₀.transport hJ.unitaryFrameEquiv.toLinearEquiv = J := by
  refine AlmostComplexStructure.toLinearMap_injective (LinearMap.ext fun w ↦ ?_)
  -- This is `J Ψ = Ψ J₀` at `Ψ⁻¹ w`.
  simpa using (hJ.apply_unitaryFrame hg (hJ.unitaryFrameEquiv.symm w)).symm

/-- **The unitary frames of a smooth family of compatible structures are smooth.** If the
endomorphisms of a family `J x` of `ω`-compatible structures depend `C^n` on `x ∈ s` in the
operator norm, so do their unitary frames. -/
theorem _root_.ContDiffOn.unitaryFrame {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {s : Set P} {n : WithTop ℕ∞} {J : P → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ n (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) s)
    (hc : ∀ x ∈ s, ω.Compatible (J x)) :
    ContDiffOn ℝ n (fun x ↦ ω.unitaryFrame (J x)) s :=
  (hJ.associatedBilinForm ω).metricChangeTransport fun x hx ↦
    (hc x hx).isStrictlyPositive_continuousLinearMapOfBilin

/-- The unitary frames of a family of compatible structures are differentiable at every point
where the endomorphisms of the family are. -/
theorem _root_.DifferentiableAt.unitaryFrame {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {x : P} {J : P → AlmostComplexStructure V}
    (hJ : DifferentiableAt ℝ (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) x)
    (hc : ∀ᶠ y in 𝓝 x, ω.Compatible (J y)) :
    DifferentiableAt ℝ (fun x ↦ ω.unitaryFrame (J x)) x := by
  have hh := hJ.associatedBilinForm ω
  -- The transport is differentiable within the positive metrics, where the family lies near `x`.
  have hT := ContinuousLinearMap.contDiffOn_metricChangeTransport (E := V) (n := 1)
  have hT' := hT.differentiableOn one_ne_zero _
    hc.self_of_nhds.isStrictlyPositive_continuousLinearMapOfBilin
  exact (hT'.comp x (hh.differentiableWithinAt (s := {y | ω.Compatible (J y)})) fun y hy ↦
    Compatible.isStrictlyPositive_continuousLinearMapOfBilin hy).differentiableAt hc

/-- The unitary frames of a `C^n` family of compatible structures form a `C^n` family. -/
theorem _root_.ContDiff.unitaryFrame {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : WithTop ℕ∞} {J : P → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hc : ∀ x, ω.Compatible (J x)) : ContDiff ℝ n fun x ↦ ω.unitaryFrame (J x) :=
  contDiffOn_univ.1 (hJ.contDiffOn.unitaryFrame fun x _ ↦ hc x)

end TauCeti.SymplecticForm
