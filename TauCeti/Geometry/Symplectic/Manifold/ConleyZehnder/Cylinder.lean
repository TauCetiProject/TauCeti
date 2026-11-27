/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder
import TauCeti.Topology.VectorBundle.Contractible

/-!
# The Conley–Zehnder index of a loop through a cylinder to a reference loop

Let `(M, σ)` be a symplectic manifold, `γ₀` a loop in `M` and `φ₀` a symplectic frame of the
tangent bundle along `γ₀` with model a symplectic vector space `(W, ω₀)`, periodic in the sense
that `φ₀(0) = φ₀(1)`. In Hamiltonian Floer theory on all free loops, one such *reference loop* with
its frame is fixed in each free homotopy class, and a one-periodic orbit `γ` in that class is
graded through a cylinder `u` from `γ` to `γ₀` (`TauCeti.IsSmoothCylinder`): the frame `φ₀` extends
over the cylinder to a frame that is periodic on every loop `u(s, ·)`, and its restriction to `γ`
is the frame in which the linearized flow along `γ` is read.

A **frame of the cylinder extending `φ₀`** (`TauCeti.SmoothTwoForm.IsCylinderFrame`) is a symplectic
frame `χ` of the tangent bundle along `u` on the unit square with

* `χ(s, 1) = χ(s, 0)` for every `s ∈ [0, 1]`, so that it is a frame over the cylinder
  `[0, 1] × S¹`, and
* `χ(1, t) = φ₀(t)` for every `t ∈ [0, 1]`.

Such frames exist for every smooth cylinder when `σ` is nondegenerate
(`TauCeti.IsSmoothCylinder.exists_isCylinderFrame`): starting from any symplectic frame `Ψ` along
`u` on the square, which is neither periodic nor equal to `φ₀`, the frame is corrected on the right
by a continuous family of linear symplectic automorphisms of the model, built from the defect
`Ψ(s, 1)⁻¹ Ψ(s, 0)` of periodicity and the defect `Ψ(1, t)⁻¹ φ₀(t)` along the reference loop.

For a continuous family `Φ(t) : T_(γ 0) M ≃ T_(γ t) M` of linear maps preserving `σ`, such as the
linearized flow along a one-periodic orbit, the Conley–Zehnder index of `Φ` read in the restriction
`t ↦ χ(0, t)` does not depend on the frame `χ` of the cylinder
(`TauCeti.SmoothTwoForm.IsCylinderFrame.frameConleyZehnderIndex_eq`): two such frames differ by
a map of the square into the linear symplectic group of the model which is a loop on every
segment `s = const` and is the identity at `s = 1`, a homotopy through loops from their change of
frame along `γ` to the constant loop, so their change of frame has Maslov index zero. This defines
the **Conley–Zehnder index of `Φ` through the cylinder `u`**,
`TauCeti.IsSmoothCylinder.conleyZehnderIndex`, characterized as the index in any frame of the
cylinder extending `φ₀` (`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq`). Its properties:

* along a nondegenerate orbit, where `Φ` starts at the identity and ends at a map `P` without the
  eigenvalue `1`, it is an integer `k` with `(-1) ^ (n - k) = sign det (1 - P)`, `2 n = dim M`
  (`TauCeti.IsSmoothCylinder.exists_int_conleyZehnderIndex_eq_and_negOnePow_eq`);
* replacing the reference frame `φ₀` by another periodic frame `φ₀'` along `γ₀` shifts the index of
  every loop graded through a cylinder to `γ₀` by twice the Maslov index of the change of frame
  `t ↦ φ₀(t)⁻¹ φ₀'(t)` along `γ₀`
  (`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_add_maslovIndex`);
* through the trivial cylinder `(s, t) ↦ γ₀(t)` from the reference loop to itself, the index is
  the index read in the reference frame
  (`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_frameConleyZehnderIndex`).

The index does depend on the cylinder: two cylinders from `γ` to `γ₀` glue to a torus, and when
the first Chern number of the tangent bundle vanishes on tori the two indices agree. That
comparison is not made here.

## Main definitions

* `TauCeti.SmoothTwoForm.IsCylinderFrame`: a symplectic frame of the tangent bundle along a
  cylinder, periodic on its loops and equal to a given frame along the reference loop.
* `TauCeti.IsSmoothCylinder.conleyZehnderIndex`: the Conley–Zehnder index of a family of linear
  symplectic maps along a loop, read in a frame induced from the reference frame through a smooth
  cylinder.

## Main results

* `TauCeti.IsSmoothCylinder.exists_isCylinderFrame`: frames of a cylinder extending a periodic
  reference frame exist.
* `TauCeti.SmoothTwoForm.IsCylinderFrame.frameConleyZehnderIndex_eq`: the index along the loop does
  not depend on the frame of the cylinder.
* `TauCeti.IsSmoothCylinder.exists_int_conleyZehnderIndex_eq`,
  `TauCeti.IsSmoothCylinder.exists_int_conleyZehnderIndex_eq_and_negOnePow_eq`: integrality and
  parity of the index along a nondegenerate orbit.
* `TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_add_maslovIndex`: the change of reference frame.
* `TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq_frameConleyZehnderIndex`: the index of the
  reference loop through the trivial cylinder.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index in a trivialization along a
  periodic orbit).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 (the grading of noncontractible
  orbits through reference loops with fixed trivializations).
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold ContDiff

namespace TauCeti

open SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {ω₀ : SymplecticForm W}
  {γ γ₀ : ℝ → M} {u : ℝ × ℝ → M} {φ₀ φ₀' : ∀ t : unitInterval, W ≃L[ℝ] TangentSpace I (γ₀ t)}

namespace SmoothTwoForm

variable (σ ω₀) in
/-- A **frame of a cylinder extending a reference frame.** Let `u` be a map of the plane, read on
the unit square as a cylinder whose loops `u (s, ·)` end at the loop `γ₀ = u (1, ·)`, and `φ₀` a
frame along `γ₀`. A symplectic frame `χ` of the tangent bundle along `u` on the unit square, with
model `(W, ω₀)`, is a frame of the cylinder extending `φ₀` when it is periodic on every loop,
`χ (s, 1) = χ (s, 0)`, and agrees with `φ₀` along `γ₀`, `χ (1, t) = φ₀ t`. -/
structure IsCylinderFrame (u : ℝ × ℝ → M) (φ₀ : ∀ t : unitInterval, W ≃L[ℝ] TangentSpace I (γ₀ t))
    (χ : ∀ z : unitInterval × unitInterval, W ≃L[ℝ] TangentSpace I (u (z.1, z.2))) : Prop where
  /-- A frame of a cylinder is a symplectic frame along it. -/
  isSymplecticFrame : IsSymplecticFrame σ ω₀ (fun z : unitInterval × unitInterval ↦ u (z.1, z.2)) χ
  /-- A frame of a cylinder takes the same values at the two ends of each loop. -/
  periodic (s : unitInterval) (v : W) : χ (s, 1) v = χ (s, 0) v
  /-- A frame of a cylinder agrees with the reference frame along the reference loop. -/
  apply_one (t : unitInterval) (v : W) : χ (1, t) v = φ₀ t v

namespace IsCylinderFrame

variable {χ χ' : ∀ z : unitInterval × unitInterval, W ≃L[ℝ] TangentSpace I (u (z.1, z.2))}

/-- A frame of a cylinder from `γ` restricts, along the edge `s = 0` where the cylinder runs along
`γ`, to a symplectic frame along `γ`. -/
theorem isSymplecticFrame_apply_zero (hu : IsSmoothCylinder I γ γ₀ u)
    (hχ : IsCylinderFrame σ ω₀ u φ₀ χ) :
    IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ t) fun t ↦ χ (0, t) := by
  refine ⟨(hχ.isSymplecticFrame.continuous.comp
    (((continuous_const (y := (0 : unitInterval))).prodMk continuous_fst).prodMk
      continuous_snd)).congr fun q ↦
      TotalSpace.ext (hu.apply_zero q.1) HEq.rfl, fun t v w ↦ ?_⟩
  rw [← hχ.isSymplecticFrame.apply_apply (0, t) v w, Icc.coe_zero, hu.apply_zero t]

/-- The restriction of a frame of a cylinder to the edge `s = 0` takes the same values at the two
ends of the loop. -/
theorem apply_zero_zero (hχ : IsCylinderFrame σ ω₀ u φ₀ χ) (v : W) : χ (0, 0) v = χ (0, 1) v :=
  (hχ.periodic 0 v).symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]

/-- **The index along the loop does not depend on the frame of the cylinder.** Two frames `χ` and
`χ'` of a smooth cylinder from `γ` to `γ₀`, extending the same reference frame along `γ₀`, give the
same Conley–Zehnder index of every continuous family `Φ` of linear maps along `γ` preserving `σ`,
read in their restrictions to `γ`. -/
theorem frameConleyZehnderIndex_eq (hu : IsSmoothCylinder I γ γ₀ u)
    (hχ : IsCylinderFrame σ ω₀ u φ₀ χ) (hχ' : IsCylinderFrame σ ω₀ u φ₀ χ')
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω₀ (hχ'.isSymplecticFrame_apply_zero hu) hΦ hΦσ =
      frameConleyZehnderIndex ω₀ (hχ.isSymplecticFrame_apply_zero hu) hΦ hΦσ := by
  have hper := trans_symm_zero_eq_trans_symm_one (I := I) (γ := fun t : unitInterval ↦ γ t)
    (χ := fun t ↦ χ (0, t)) (χ' := fun t ↦ χ' (0, t)) hχ.apply_zero_zero hχ'.apply_zero_zero
  rw [frameConleyZehnderIndex_eq_add_maslovIndex (hχ.isSymplecticFrame_apply_zero hu)
    (hχ'.isSymplecticFrame_apply_zero hu) hper]
  suffices hm : ω₀.maslovIndex (transitionLoop (hχ.isSymplecticFrame_apply_zero hu).continuous
      (hχ'.isSymplecticFrame_apply_zero hu).continuous hper)
      (apply_transitionLoop_apply (hχ.isSymplecticFrame_apply_zero hu)
        (hχ'.isSymplecticFrame_apply_zero hu) hper) = 0 by
    rw [hm, Int.cast_zero, mul_zero, add_zero]
  -- The change of frame over the square is a homotopy through loops from the change of frame
  -- along `γ` to the constant loop at the identity.
  let F : C(unitInterval × unitInterval, W →L[ℝ] W) :=
    ⟨fun p ↦ ((χ' p).trans (χ p).symm : W ≃L[ℝ] W),
      continuous_trans_symm_of_continuous_frame hχ'.isSymplecticFrame.continuous
        hχ.isSymplecticFrame.continuous⟩
  have hF (p : unitInterval × unitInterval) (v w : W) : ω₀ (F p v) (F p w) = ω₀ v w :=
    hχ'.isSymplecticFrame.apply_trans_symm_apply hχ.isSymplecticFrame p v w
  -- Along the edge `s = 0` it is the change of frame along `γ`.
  have hF₀ (t : unitInterval) :
      F (0, t) = transitionLoop (I := I) (γ := fun t : unitInterval ↦ γ t)
        (χ := fun t ↦ χ (0, t)) (χ' := fun t ↦ χ' (0, t))
        (hχ.isSymplecticFrame_apply_zero hu).continuous
        (hχ'.isSymplecticFrame_apply_zero hu).continuous hper t := by
    ext v
    exact (transitionLoop_apply (I := I) (γ := fun t : unitInterval ↦ γ t)
      (χ := fun t ↦ χ (0, t)) (χ' := fun t ↦ χ' (0, t)) _ _ hper t v).symm
  -- Along the edge `s = 1` both frames are the reference frame.
  have hF₁ (t : unitInterval) : F (1, t) = Path.refl (1 : W →L[ℝ] W) t := by
    ext v
    -- Both sides are applied pointwise: `F` is the bundled change of frame and `Path.refl 1` is
    -- the identity.
    change (χ (1, t)).symm (χ' (1, t) v) = v
    exact (χ (1, t)).symm_apply_eq.2 ((hχ'.apply_one t v).trans (hχ.apply_one t v).symm)
  -- Each segment `s = const` is a loop.
  have hFper (s : unitInterval) : F (s, 0) = F (s, 1) := by
    ext v
    -- `F` is the bundled change of frame, applied pointwise.
    change (χ (s, 0)).symm (χ' (s, 0) v) = (χ (s, 1)).symm (χ' (s, 1) v)
    rw [hχ'.periodic s v]
    apply (χ (s, 1)).injective
    -- `χ (s, 0)` and `χ (s, 1)` take values in the tangent spaces at `u (s, 0)` and `u (s, 1)`,
    -- equal only definitionally, so the inverses are cancelled by explicit terms rather than `rw`.
    exact ((hχ.periodic s _).trans ((χ (s, 0)).apply_symm_apply _)).trans
      ((χ (s, 1)).apply_symm_apply _).symm
  exact (ω₀.maslovIndex_eq_of_homotopy _ (Path.refl 1) F hF hF₀ hF₁ hFper).trans
    (ω₀.maslovIndex_refl _ _)

end IsCylinderFrame

end SmoothTwoForm

/-! ### Existence of frames of a cylinder -/

section Existence

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Two symplectic frames along maps that agree pointwise differ by a continuous family of linear
symplectic automorphisms of the model. -/
private theorem continuous_trans_symm_of_forall_eq [FiniteDimensional ℝ E] {Y : Type*}
    [TopologicalSpace Y] {f g : Y → M} (hfg : ∀ y, f y = g y)
    {φ : ∀ y, W ≃L[ℝ] TangentSpace I (f y)} {ψ : ∀ y, W ≃L[ℝ] TangentSpace I (g y)}
    (hφ : IsSymplecticFrame σ ω₀ f φ) (hψ : IsSymplecticFrame σ ω₀ g ψ) :
    (Continuous fun y ↦ (((φ y).trans (ψ y).symm : W ≃L[ℝ] W) : W →L[ℝ] W)) ∧
      ∀ y v w, ω₀ ((φ y).trans (ψ y).symm v) ((φ y).trans (ψ y).symm w) = ω₀ v w := by
  obtain rfl : f = g := funext hfg
  exact ⟨continuous_trans_symm_of_continuous_frame hφ.continuous hψ.continuous,
    hφ.apply_trans_symm_apply hψ⟩

/-- The parameter `1 - t (1 - s)` of the correction of a frame of a cylinder, as a map of the unit
square to the unit interval: `1` on the edges `t = 0` and `s = 1`, and `s` on the edge `t = 1`. -/
private def cylinderFrameParam (p : unitInterval × unitInterval) : unitInterval :=
  unitInterval.symm (p.2 * unitInterval.symm p.1)

private theorem continuous_cylinderFrameParam : Continuous cylinderFrameParam :=
  unitInterval.continuous_symm.comp (continuous_induced_rng.2 (by
    simp only [Function.comp_def, Icc.coe_mul, unitInterval.coe_symm_eq]
    fun_prop))

private theorem cylinderFrameParam_zero (s : unitInterval) : cylinderFrameParam (s, 0) = 1 := by
  simp [cylinderFrameParam]

private theorem cylinderFrameParam_one (s : unitInterval) : cylinderFrameParam (s, 1) = s := by
  simp [cylinderFrameParam]

private theorem cylinderFrameParam_one_left (t : unitInterval) : cylinderFrameParam (1, t) = 1 := by
  simp [cylinderFrameParam]

/-- The correction `p ↦ d(r) d(1)⁻¹ b(t)`, `r = 1 - t (1 - s)`, of a frame of a cylinder: for
continuous families `d` and `b` of linear symplectic automorphisms of the model, it is again one. -/
private theorem continuous_cylinderFrameCorrection {d b : unitInterval → W ≃L[ℝ] W}
    (hdc : Continuous fun s ↦ (d s : W →L[ℝ] W)) (hdω : ∀ s v w, ω₀ (d s v) (d s w) = ω₀ v w)
    (hbc : Continuous fun t ↦ (b t : W →L[ℝ] W)) (hbω : ∀ t v w, ω₀ (b t v) (b t w) = ω₀ v w) :
    (Continuous fun p : unitInterval × unitInterval ↦
      (((b p.2).trans ((d 1).symm.trans (d (cylinderFrameParam p))) : W ≃L[ℝ] W) : W →L[ℝ] W)) ∧
      ∀ (p : unitInterval × unitInterval) v w,
        ω₀ ((b p.2).trans ((d 1).symm.trans (d (cylinderFrameParam p))) v)
          ((b p.2).trans ((d 1).symm.trans (d (cylinderFrameParam p))) w) = ω₀ v w := by
  have hd₁ : ∀ v w, ω₀ ((d 1).symm v) ((d 1).symm w) = ω₀ v w :=
    ((SymplecticForm.isSymplectomorphism_iff (e := (d 1).toLinearEquiv)).2 (hdω 1)).symm.apply
  refine ⟨(((hdc.comp continuous_cylinderFrameParam).clm_comp
    (continuous_const (y := ((d 1).symm : W →L[ℝ] W)))).clm_comp
      (hbc.comp continuous_snd)).congr fun p ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun p v w ↦ ?_⟩
  · -- Both sides apply `b`, `d(1)⁻¹` and `d(r)` in turn.
    rfl
  · simp only [ContinuousLinearEquiv.trans_apply, hdω, hd₁, hbω]

/-- **Frames of a cylinder exist.** For a fiberwise nondegenerate two-form `σ` on a Hausdorff
σ-compact manifold, every smooth cylinder from `γ` to `γ₀` carries a frame extending any symplectic
frame `φ₀` along `γ₀` with `φ₀ 0 = φ₀ 1`. -/
theorem IsSmoothCylinder.exists_isCylinderFrame [T2Space M] [SigmaCompactSpace M]
    [FiniteDimensional ℝ W] (h : σ.IsNondegenerate) (hu : IsSmoothCylinder I γ γ₀ u)
    (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀) (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v) :
    ∃ χ, IsCylinderFrame σ ω₀ u φ₀ χ := by
  -- A symplectic frame `Ψ` along the cylinder, neither periodic nor equal to `φ₀`.
  obtain ⟨Ψ, hΨ⟩ := h.exists_isSymplecticFrame (ω₀ := ω₀) (φ₀ 0).toLinearEquiv.finrank_eq
    hu.contMDiff.continuous
  have hΨsq : IsSymplecticFrame σ ω₀ (fun z : unitInterval × unitInterval ↦ u (z.1, z.2))
      fun z ↦ Ψ (z.1, z.2) := hΨ.comp (by fun_prop)
  -- The defect `d s = Ψ(s, 1)⁻¹ Ψ(s, 0)` of periodicity on the loop `u (s, ·)`.
  obtain ⟨hdc, hdω⟩ := continuous_trans_symm_of_forall_eq
    (fun s : unitInterval ↦ (hu.periodic s s.property).symm)
    (hΨ.comp (f := u) (g := fun s : unitInterval ↦ ((s : ℝ), (0 : ℝ))) (by fun_prop))
    (hΨ.comp (f := u) (g := fun s : unitInterval ↦ ((s : ℝ), (1 : ℝ))) (by fun_prop))
  set d : unitInterval → W ≃L[ℝ] W := fun s ↦ (Ψ (s, 0)).trans (Ψ (s, 1)).symm
  -- The defect `b t = Ψ(1, t)⁻¹ φ₀(t)` along the reference loop.
  obtain ⟨hbc, hbω⟩ := continuous_trans_symm_of_forall_eq
    (fun t : unitInterval ↦ (hu.apply_one t t.property).symm) hφ₀
    (hΨ.comp (f := u) (g := fun t : unitInterval ↦ ((1 : ℝ), (t : ℝ))) (by fun_prop))
  set b : unitInterval → W ≃L[ℝ] W := fun t ↦ (φ₀ t).trans (Ψ (1, t)).symm
  -- The correction `A(s, t) = d(r) d(1)⁻¹ b(t)` with `r = 1 - t (1 - s)`.
  obtain ⟨hAc, hAω⟩ := continuous_cylinderFrameCorrection (d := d) (b := b) hdc hdω hbc hbω
  -- The defects in action.
  have hdΨ (s : unitInterval) (x : W) : Ψ ((s : ℝ), 1) (d s x) = Ψ ((s : ℝ), 0) x :=
    (Ψ ((s : ℝ), 1)).apply_symm_apply _
  have hbΨ (t : unitInterval) (x : W) : Ψ (1, (t : ℝ)) (b t x) = φ₀ t x :=
    (Ψ (1, (t : ℝ))).apply_symm_apply _
  have hd₁ (x : W) : (d 1).symm (b 1 x) = b 0 x := by
    refine (d 1).symm_apply_eq.2 ((Ψ (1, 1)).injective ?_)
    -- The frames at `(1, 0)` and `(1, 1)` live over the same point only up to definitional
    -- equality, so the steps are composed as terms.
    exact (((hbΨ 1 x).trans (hφ₀₁ x).symm).trans (hbΨ 0 x).symm).trans (hdΨ 1 (b 0 x)).symm
  refine ⟨fun p ↦ ((b p.2).trans ((d 1).symm.trans (d (cylinderFrameParam p)))).trans
    (Ψ (p.1, p.2)), hΨsq.trans_of_continuous hAc hAω, fun s v ↦ ?_, fun t v ↦ ?_⟩
  · -- The frame applies `b`, `d(1)⁻¹`, `d(r)` and `Ψ` in turn, with `r = s` at `t = 1` and `r = 1`
    -- at `t = 0`. The two ends of the loop live over the same point only up to definitional
    -- equality, so the two computations are composed as terms.
    have h₁ : Ψ ((s : ℝ), 1) (d (cylinderFrameParam (s, 1)) ((d 1).symm (b 1 v))) =
        Ψ ((s : ℝ), 0) (b 0 v) := by
      rw [cylinderFrameParam_one, hd₁, hdΨ]
    have h₀ : Ψ ((s : ℝ), 0) (d (cylinderFrameParam (s, 0)) ((d 1).symm (b 0 v))) =
        Ψ ((s : ℝ), 0) (b 0 v) := by
      rw [cylinderFrameParam_zero, ContinuousLinearEquiv.apply_symm_apply]
    exact h₁.trans h₀.symm
  · -- At `s = 1` the parameter is `r = 1`, so the frame is `Ψ(1, t) b(t) = φ₀(t)`.
    have h₁ : Ψ (1, (t : ℝ)) (d (cylinderFrameParam (1, t)) ((d 1).symm (b t v))) = φ₀ t v := by
      rw [cylinderFrameParam_one_left, ContinuousLinearEquiv.apply_symm_apply, hbΨ]
    exact h₁

end Existence

/-! ### The Conley–Zehnder index through a cylinder -/

section Index

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ W]

/-- The **Conley–Zehnder index through a cylinder.** Let `σ` be a fiberwise nondegenerate two-form,
`u` a smooth cylinder from the loop `γ` to the reference loop `γ₀`, and `φ₀` a symplectic frame
along `γ₀` with `φ₀ 0 = φ₀ 1`. For a continuous family `Φ` of linear maps along `γ` preserving `σ`,
such as the linearized flow along a one-periodic orbit, this is the Conley–Zehnder index of `Φ`
read in the restriction to `γ` of a frame of the cylinder extending `φ₀`. It does not depend on
that frame (`TauCeti.IsSmoothCylinder.conleyZehnderIndex_eq`). -/
def IsSmoothCylinder.conleyZehnderIndex (h : σ.IsNondegenerate) (hu : IsSmoothCylinder I γ γ₀ u)
    (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀) (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) : ℝ :=
  frameConleyZehnderIndex ω₀
    ((hu.exists_isCylinderFrame h hφ₀ hφ₀₁).choose_spec.isSymplecticFrame_apply_zero hu) hΦ hΦσ

/-- **The index through a cylinder in any frame.** The Conley–Zehnder index of `Φ` through the
cylinder `u` is the Conley–Zehnder index of `Φ` read in the restriction to `γ` of any frame of the
cylinder extending the reference frame `φ₀`. -/
theorem IsSmoothCylinder.conleyZehnderIndex_eq (h : σ.IsNondegenerate)
    (hu : IsSmoothCylinder I γ γ₀ u) (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀)
    (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    {χ : ∀ z : unitInterval × unitInterval, W ≃L[ℝ] TangentSpace I (u (z.1, z.2))}
    (hχ : IsCylinderFrame σ ω₀ u φ₀ χ)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ =
      frameConleyZehnderIndex ω₀ (hχ.isSymplecticFrame_apply_zero hu) hΦ hΦσ :=
  ((hu.exists_isCylinderFrame h hφ₀ hφ₀₁).choose_spec.frameConleyZehnderIndex_eq hu hχ hΦ
    hΦσ).symm

/-- **The index through a cylinder along a nondegenerate orbit is an integer.** If the family `Φ`
starts at the identity and its endpoint `Φ(1)` fixes no nonzero vector, as the linearized flow along
a nondegenerate one-periodic orbit does, its Conley–Zehnder index through a cylinder is an
integer. -/
theorem IsSmoothCylinder.exists_int_conleyZehnderIndex_eq (h : σ.IsNondegenerate)
    (hu : IsSmoothCylinder I γ γ₀ u) (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀)
    (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v)
    (hΦ₀ : ∀ v, Φ 0 v = v) (hΦ₁ : ∀ v, Φ 1 v = v → v = 0) :
    ∃ k : ℤ, hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ = k := by
  obtain ⟨χ, hχ⟩ := hu.exists_isCylinderFrame h hφ₀ hφ₀₁
  rw [hu.conleyZehnderIndex_eq h hφ₀ hφ₀₁ hχ]
  exact exists_int_frameConleyZehnderIndex_eq _ hχ.apply_zero_zero hΦ hΦσ hΦ₀ hΦ₁

/-- **The parity of the index through a cylinder.** Let `Φ` be a continuous family of linear maps
along `γ` preserving `σ`, in a manifold of dimension `2 n`, starting at the identity, whose end
value is an endomorphism `P` of `T_(γ 0) M` without the eigenvalue `1`, such as the linearized flow
along a nondegenerate one-periodic orbit. Then its Conley–Zehnder index through a cylinder is an
integer `k` with `(-1) ^ (n - k) = sign det (1 - P)`. -/
theorem IsSmoothCylinder.exists_int_conleyZehnderIndex_eq_and_negOnePow_eq
    (h : σ.IsNondegenerate) (hu : IsSmoothCylinder I γ γ₀ u)
    (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀) (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v)
    (hΦ₀ : ∀ v, Φ 0 v = v) {P : TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ 0)}
    (hP : ∀ v, Φ 1 v = P v) (hPdet : LinearMap.det (1 - P) ≠ 0) :
    ∃ k : ℤ, hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ = k ∧
      ((((finrank ℝ E / 2 : ℕ) : ℤ) - k).negOnePow : ℤ) =
        SignType.sign (LinearMap.det (1 - P)) := by
  obtain ⟨χ, hχ⟩ := hu.exists_isCylinderFrame h hφ₀ hφ₀₁
  rw [hu.conleyZehnderIndex_eq h hφ₀ hφ₀₁ hχ]
  exact exists_int_frameConleyZehnderIndex_eq_and_negOnePow_eq _ hχ.apply_zero_zero hΦ hΦσ hΦ₀ hP
    hPdet

/-- **Change of reference frame.** Replacing the periodic reference frame `φ₀` along `γ₀` by
another periodic reference frame `φ₀'` shifts the Conley–Zehnder index through every cylinder to
`γ₀` by twice the Maslov index of the change of frame `t ↦ φ₀(t)⁻¹ φ₀'(t)` along `γ₀`. -/
theorem IsSmoothCylinder.conleyZehnderIndex_eq_add_maslovIndex (h : σ.IsNondegenerate)
    (hu : IsSmoothCylinder I γ γ₀ u) (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀)
    (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    (hφ₀' : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀')
    (hφ₀₁' : ∀ v, φ₀' 0 v = φ₀' 1 v)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    hu.conleyZehnderIndex h hφ₀' hφ₀₁' hΦ hΦσ = hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ +
      2 * ω₀.maslovIndex (transitionLoop hφ₀.continuous hφ₀'.continuous
        (trans_symm_zero_eq_trans_symm_one hφ₀₁ hφ₀₁'))
        (apply_transitionLoop_apply hφ₀ hφ₀' (trans_symm_zero_eq_trans_symm_one hφ₀₁ hφ₀₁')) := by
  obtain ⟨χ, hχ⟩ := hu.exists_isCylinderFrame h hφ₀ hφ₀₁
  -- The change of reference frame `T(t) = φ₀(t)⁻¹ φ₀'(t)`, a loop.
  have hTc := continuous_trans_symm_of_continuous_frame (f := fun t : unitInterval ↦ γ₀ t)
    (φ := φ₀') (ψ := φ₀) hφ₀'.continuous hφ₀.continuous
  have hT₁ (v : W) : ((φ₀' 1).trans (φ₀ 1).symm) v = ((φ₀' 0).trans (φ₀ 0).symm) v :=
    DFunLike.congr_fun (trans_symm_zero_eq_trans_symm_one hφ₀₁ hφ₀₁').symm v
  -- The frame `χ T` of the cylinder extends `φ₀'`.
  have hχ' : IsCylinderFrame σ ω₀ u φ₀' fun p ↦ ((φ₀' p.2).trans (φ₀ p.2).symm).trans (χ p) :=
    ⟨hχ.isSymplecticFrame.trans_of_continuous (hTc.comp continuous_snd)
      fun p ↦ hφ₀'.apply_trans_symm_apply hφ₀ p.2,
      fun s v ↦ (hχ.periodic s _).trans (congrArg (χ (s, 0)) (hT₁ v)),
      fun t v ↦ (hχ.apply_one t _).trans ((φ₀ t).apply_symm_apply _)⟩
  have hper₀ := trans_symm_zero_eq_trans_symm_one hφ₀₁ hφ₀₁'
  have hper := trans_symm_zero_eq_trans_symm_one (I := I) (γ := fun t : unitInterval ↦ γ t)
    (χ := fun t ↦ χ (0, t)) (χ' := fun t ↦ ((φ₀' t).trans (φ₀ t).symm).trans (χ (0, t)))
    hχ.apply_zero_zero hχ'.apply_zero_zero
  -- Along `γ` the change of frame from `χ` to `χ T` is `T`.
  have hm := ω₀.maslovIndex_congr
    (transitionLoop (hχ.isSymplecticFrame_apply_zero hu).continuous
      (hχ'.isSymplecticFrame_apply_zero hu).continuous hper)
    (transitionLoop hφ₀.continuous hφ₀'.continuous hper₀)
    (apply_transitionLoop_apply (hχ.isSymplecticFrame_apply_zero hu)
      (hχ'.isSymplecticFrame_apply_zero hu) hper)
    fun t ↦ ContinuousLinearMap.ext fun v ↦
      ((transitionLoop_apply _ _ hper t v).trans ((χ (0, t)).symm_apply_apply _)).trans
        (transitionLoop_apply _ _ hper₀ t v).symm
  rw [hu.conleyZehnderIndex_eq h hφ₀' hφ₀₁' hχ', hu.conleyZehnderIndex_eq h hφ₀ hφ₀₁ hχ,
    frameConleyZehnderIndex_eq_add_maslovIndex (hχ.isSymplecticFrame_apply_zero hu)
      (hχ'.isSymplecticFrame_apply_zero hu) hper, hm]

/-- **The index of the reference loop.** Through the trivial cylinder `(s, t) ↦ γ₀(t)` from the
reference loop to itself, the Conley–Zehnder index of a family `Φ` along `γ₀` is its index read in
the reference frame. -/
theorem IsSmoothCylinder.conleyZehnderIndex_eq_frameConleyZehnderIndex (h : σ.IsNondegenerate)
    (hu : IsSmoothCylinder I γ₀ γ₀ fun z ↦ γ₀ z.2)
    (hφ₀ : IsSymplecticFrame σ ω₀ (fun t : unitInterval ↦ γ₀ t) φ₀) (hφ₀₁ : ∀ v, φ₀ 0 v = φ₀ 1 v)
    {Φ : ∀ t : unitInterval, TangentSpace I (γ₀ 0) ≃L[ℝ] TangentSpace I (γ₀ t)}
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ₀ 0) ↦
      (⟨γ₀ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ (t : unitInterval) u v, σ.eval₂ (γ₀ t) (Φ t u) (Φ t v) = σ.eval₂ (γ₀ 0) u v) :
    hu.conleyZehnderIndex h hφ₀ hφ₀₁ hΦ hΦσ = frameConleyZehnderIndex ω₀ hφ₀ hΦ hΦσ := by
  -- The reference frame, constant in `s`, is a frame of the trivial cylinder.
  have hχ : IsCylinderFrame σ ω₀ (fun z ↦ γ₀ z.2) φ₀ fun p ↦ φ₀ p.2 :=
    ⟨hφ₀.comp continuous_snd, fun _ v ↦ (hφ₀₁ v).symm, fun _ _ ↦ rfl⟩
  exact hu.conleyZehnderIndex_eq h hφ₀ hφ₀₁ hχ hΦ hΦσ

end Index

end TauCeti
