/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.AddCircle
public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
public import TauCeti.Geometry.Manifold.Degree.Collapse
public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.UnitSphere
public import TauCeti.Geometry.Manifold.SmoothSingular.Torus
import TauCeti.Geometry.Sphere.Connected

/-!
# Periods on the fundamental class of a closed surface are integrals

Let `C` be a compact connected boundaryless smooth surface with an orientation `o`, and let
`μ ∈ H₂(C; ℤ)` be an integral fundamental class of `C` (`TauCeti.IsFundamentalClass`, a notion
that carries no orientation datum). The period `⟨[η], μ⟩` of a closed two-form `η` on `μ`
(`TauCeti.closedFormHomologyPeriod`) is its integral over a smooth cycle representing `μ`. This
file proves that it is the integral of `η` over the oriented surface, up to one sign `s = ±1`
which does not depend on `η` (`TauCeti.exists_closedFormHomologyPeriod_eq_mul_integralTopForm`):

`⟨[η], μ⟩ = s ∫_C η`.

The sign compares `μ` with `o`; replacing `μ` by `-μ` changes it. In particular a closed two-form
has zero period on `μ` exactly when its integral vanishes, and for a smooth map `u : C → X` the
period of a closed two-form `β` of `X` on the image `u_* μ` is `s ∫_C u^* β`
(`TauCeti.exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm`). So a closed
two-form with zero period on a class `u_* μ` integrates to zero over the surface `u`.

The proof has three steps.

* Integration identifies the top de Rham cohomology of `C` with `ℝ`: a closed two-form of integral
  zero is exact (`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`), and exact
  forms have zero periods. So the period on `μ` is a fixed multiple of the integral, and it remains
  to compute it for one form of nonzero integral.
* A map `f : C → S²` collapsing the complement of a coordinate disc has a regular value with one
  preimage (`TauCeti.exists_contMDiff_sphere_degreeAtRegularValue_eq_one_or_eq_neg_one`), so it has
  degree `±1`. Hence `f_* μ = ±ν` for a fundamental class `ν` of `S²`
  (`TauCeti.Manifold.Orientation.exists_singularHomologyMap_int_eq_degreeAtRegularValue_smul`), and
  `∫_C f^* ω = ±∫_{S²} ω` for the area form `ω` of the sphere
  (`TauCeti.integralTopForm_mpullback_eq_degree_mul`). This reduces the claim for `C` to the claim
  for `S²`.
* On the torus `ℝ / ℤ × ℝ / ℤ` the period of a closed two-form on the class of the torus is its
  integral (`TauCeti.closedFormHomologyPeriod_addCircleProdFundamentalClass`), and that class is a
  fundamental class (`TauCeti.isFundamentalClass_addCircleProdFundamentalClass`). Applying the
  second step to the torus proves the claim for `S²`.

The surface is two-dimensional because the torus comparison is the computation available as a
base case; given the comparison for one closed oriented manifold of dimension `n`, the same three
steps prove it for all of them.

## Main results

* `TauCeti.closedFormHomologyPeriod_mul_integralTopForm_comm`: on a compact preconnected oriented
  boundaryless manifold, the periods of top forms on a fixed class are proportional to their
  integrals.
* `TauCeti.exists_closedFormHomologyPeriod_eq_mul_integralTopForm`: the period of a closed
  two-form on a fundamental class of a closed oriented surface is `±` its integral, with one sign
  for all forms.
* `TauCeti.closedFormHomologyPeriod_eq_zero_iff_integralTopForm_eq_zero`: such a period vanishes
  exactly when the integral does.
* `TauCeti.exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm`,
  `TauCeti.closedFormHomologyPeriod_singularHomologyMap_eq_zero_iff`: the same for the image of the
  fundamental class under a smooth map `u : C → X` and the pullbacks `u^* β`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17 (top de Rham cohomology and the degree) and Chapter 18 (integration
  over smooth chains).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5 (integration and
  the fundamental class).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree).
-/

public section

noncomputable section

open Metric Module CategoryTheory MonoidalCategory AlgebraicTopology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Periods of top forms are proportional to their integrals -/

section Proportional

variable {W H C : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H] {I : ModelWithCorners ℝ W H}
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C] [BoundarylessManifold I C]
  [T2Space C] [CompactSpace C] [PreconnectedSpace C] {n : ℕ}

/-- **Periods of top forms are proportional to their integrals.** On a compact preconnected
oriented boundaryless manifold of dimension `n`, the periods of closed `n`-forms on any fixed class
`c ∈ Hₙ(C; ℤ)` are proportional to their integrals: `⟨[η], c⟩ ∫ η₀ = ⟨[η₀], c⟩ ∫ η`. Indeed a
closed top form of integral zero is exact. -/
theorem closedFormHomologyPeriod_mul_integralTopForm_comm
    (o : Manifold.Orientation I C (Fin n)) (c : ((singularChains ℤ).obj (TopCat.of C)).homology n)
    (η₀ η : closedForms I C n) :
    closedFormHomologyPeriod η c * integralTopForm o η₀.val =
      closedFormHomologyPeriod η₀ c * integralTopForm o η.val := by
  set a := integralTopForm o η₀.val
  set b := integralTopForm o η.val
  set θ : closedForms I C n := a • η - b • η₀
  have hcs (φ : SmoothForm I C ℝ n) : φ ∈ compactlySupportedForms I C n := by
    rw [compactlySupportedForms_eq_top]
    trivial
  have hθ : integralTopForm o θ.val.val = 0 := by
    have h₁ : θ.val = a • η.val - b • η₀.val := rfl
    rw [h₁, integralTopForm_sub_of_mem_compactlySupportedForms o (hcs _) (hcs _)]
    simp only [SetLike.val_smul, integralTopForm_smul, a, b]
    ring
  have hex : θ.val ∈ exactForms I C n := by
    rw [← exactCompactlySupportedForms_eq_exactForms]
    exact (mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o (hcs _)).2 hθ
  have h := DFunLike.congr_fun (closedFormHomologyPeriod_eq_zero_of_mem_exactForms θ hex) c
  simp only [θ, closedFormHomologyPeriod_sub, closedFormHomologyPeriod_smul, AddMonoidHom.sub_apply,
    AddMonoidHom.smul_apply, smul_eq_mul, AddMonoidHom.zero_apply] at h
  linarith

end Proportional

/-! ### Closed surfaces -/

section Surface

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- The outward-normal orientation of the unit sphere `S² ⊆ ℝ³`, for the standard orientation of
`ℝ³`. -/
private abbrev sphereOrientation₂ : Manifold.Orientation (𝓡 2) (sphere (0 : ℝ³) 1) (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation

/-- The area form of the unit sphere `S² ⊆ ℝ³`, as a closed form. -/
private abbrev sphereAreaForm : closedForms (𝓡 2) (sphere (0 : ℝ³) 1) 2 :=
  ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm,
    mem_closedForms_of_finrank_le (𝓡 2) (by simp) _⟩

/-- The area form of the unit sphere has integral `4π ≠ 0`. -/
private theorem integralTopForm_sphereAreaForm :
    integralTopForm sphereOrientation₂ sphereAreaForm.val.val = 4 * Real.pi :=
  Orientation.integralTopForm_sphereOrientation_sphereVolumeForm _

variable {W H C : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H] {I : ModelWithCorners ℝ W H} [I.Boundaryless]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C] [T2Space C] [CompactSpace C]
  [ConnectedSpace C]

/-- Pulling the area form of `S²` back along a map collapsing the complement of a disc of a
compact connected oriented surface `C` multiplies its integral by a sign `d`, and its period on a
fundamental class of `C` is `±d` times its period on a fundamental class of `S²`. -/
private theorem exists_closedFormHomologyPeriod_mpullback_sphereAreaForm (hW : finrank ℝ W = 2)
    (o : Manifold.Orientation I C (Fin 2)) {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
    (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    {ν : ((singularChains ℤ).obj (TopCat.of (sphere (0 : ℝ³) 1))).homology 2}
    (hν : IsFundamentalClass (M := sphere (0 : ℝ³) 1) (N := ModuleCat.of ℤ ℤ) ν) :
    ∃ (f : C → sphere (0 : ℝ³) 1) (hf : ContMDiff I (𝓡 2) ∞ f) (s d : ℤ),
      (s = 1 ∨ s = -1) ∧ (d = 1 ∨ d = -1) ∧
      closedFormHomologyPeriod (closedForms.mpullback f hf 2 sphereAreaForm) μ =
        s * d * closedFormHomologyPeriod sphereAreaForm ν ∧
      integralTopForm o (closedForms.mpullback f hf 2 sphereAreaForm).val.val =
        d * integralTopForm sphereOrientation₂ sphereAreaForm.val.val := by
  have := connectedSpace_sphere (E := ℝ³) 2
  obtain ⟨f, y, hf, hy, hd⟩ :=
    exists_contMDiff_sphere_degreeAtRegularValue_eq_one_or_eq_neg_one hW o sphereOrientation₂
  have hfp : IsProperMap f := hf.continuous.isProperMap
  obtain ⟨s, hs, hmap⟩ :=
    Manifold.Orientation.exists_singularHomologyMap_int_eq_degreeAtRegularValue_smul (k := 1)
    hW finrank_euclideanSpace_fin o sphereOrientation₂ (f := ⟨f, hf.continuous⟩)
    (hf.of_le (by simp)) hy hμ hν
  -- `hmap` is stated in degree `1 + 1` for the bundled map `⟨f, _⟩ : C(C, S²)`; restate it in
  -- degree `2`, which is the same degree by definition, so that it rewrites the period below.
  have hmap' : ContinuousMap.singularHomologyMap ℤ 2 ⟨f, hf.continuous⟩ μ =
      (s * degreeAtRegularValue o sphereOrientation₂ f y) • ν := hmap
  refine ⟨f, hf, s, degreeAtRegularValue o sphereOrientation₂ f y, hs, hd, ?_, ?_⟩
  · rw [closedFormHomologyPeriod_mpullback, hmap', map_zsmul, zsmul_eq_mul]
    push_cast
    ring
  · rw [closedForms.coe_mpullback, SmoothForm.coe_mpullback,
      integralTopForm_mpullback_eq_degree_mul o sphereOrientation₂ hf hfp
        sphereAreaForm.val.isSmoothForm (isClosed_tsupport _).isCompact,
      degree_eq_degreeAtRegularValue o sphereOrientation₂ hf hfp hy]

/-- On `S²` the period of the area form on a fundamental class is `±` its integral. Both are
compared with the torus `ℝ / ℤ × ℝ / ℤ` along a map collapsing the complement of a disc, and on
the torus periods on its class are integrals
(`TauCeti.closedFormHomologyPeriod_addCircleProdFundamentalClass`). -/
private theorem exists_closedFormHomologyPeriod_sphereAreaForm
    {ν : ((singularChains ℤ).obj (TopCat.of (sphere (0 : ℝ³) 1))).homology 2}
    (hν : IsFundamentalClass (M := sphere (0 : ℝ³) 1) (N := ModuleCat.of ℤ ℤ) ν) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ closedFormHomologyPeriod sphereAreaForm ν =
      s * integralTopForm sphereOrientation₂ sphereAreaForm.val.val := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨f, hf, s, d, hs, hd, hper, hint⟩ :=
    exists_closedFormHomologyPeriod_mpullback_sphereAreaForm (I := 𝓘(ℝ).prod 𝓘(ℝ))
      (C := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) (by simp)
      ((AddCircle.orientation 1).prod (AddCircle.orientation 1))
      (isFundamentalClass_addCircleProdFundamentalClass 1 1) hν
  rw [closedFormHomologyPeriod_addCircleProdFundamentalClass, hint] at hper
  refine ⟨s, hs, ?_⟩
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl <;> push_cast at hper ⊢ <;> linarith

/-- **Periods on the fundamental class of a closed surface are integrals.** Let `C` be a compact
connected boundaryless smooth surface with an orientation `o`, and `μ ∈ H₂(C; ℤ)` an integral
fundamental class of `C`. Then there is a sign `s = ±1` such that for every closed two-form `η`
on `C`, the period of `η` on `μ` is `s` times the integral of `η` over `C`. -/
theorem exists_closedFormHomologyPeriod_eq_mul_integralTopForm (hW : finrank ℝ W = 2)
    (o : Manifold.Orientation I C (Fin 2)) {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
    (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ η : closedForms I C 2, closedFormHomologyPeriod η μ = s * integralTopForm o η.val := by
  obtain ⟨ν, hν⟩ := exists_isFundamentalClass_sphere (E := ℝ³) (d := 1) finrank_euclideanSpace_fin ℤ
  obtain ⟨s₀, hs₀, hS⟩ := exists_closedFormHomologyPeriod_sphereAreaForm hν
  obtain ⟨f, hf, s, d, hs, hd, hper, hint⟩ :=
    exists_closedFormHomologyPeriod_mpullback_sphereAreaForm hW o hμ hν
  -- The pulled-back area form `η₀` has nonzero integral and period `s s₀` times its integral.
  set η₀ := closedForms.mpullback f hf 2 sphereAreaForm
  refine ⟨s * s₀, by rcases hs with rfl | rfl <;> rcases hs₀ with rfl | rfl <;> norm_num,
    fun η ↦ ?_⟩
  have hη₀ : integralTopForm o η₀.val.val ≠ 0 := by
    rw [hint, integralTopForm_sphereAreaForm]
    rcases hd with rfl | rfl <;> simp [Real.pi_ne_zero]
  have hP₀ : closedFormHomologyPeriod η₀ μ = (s * s₀ : ℤ) * integralTopForm o η₀.val.val := by
    rw [hper, hS, hint]
    push_cast
    ring
  have key := closedFormHomologyPeriod_mul_integralTopForm_comm o μ η₀ η
  rw [hP₀] at key
  exact mul_right_cancel₀ hη₀ (key.trans (by ring))

/-- **A closed two-form has zero period on the fundamental class of a closed surface exactly when
its integral vanishes.** -/
theorem closedFormHomologyPeriod_eq_zero_iff_integralTopForm_eq_zero (hW : finrank ℝ W = 2)
    (o : Manifold.Orientation I C (Fin 2)) {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
    (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ) (η : closedForms I C 2) :
    closedFormHomologyPeriod η μ = 0 ↔ integralTopForm o η.val = 0 := by
  obtain ⟨s, hs, h⟩ := exists_closedFormHomologyPeriod_eq_mul_integralTopForm hW o hμ
  rw [h η, mul_eq_zero, or_iff_right]
  rcases hs with rfl | rfl <;> norm_num

variable {W' H' X : Type} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ W' H'} [TopologicalSpace X] [ChartedSpace H' X]
  [IsManifold J ∞ X] [T2Space X] [SigmaCompactSpace X]

/-- **The period of a closed two-form on the image of the fundamental class of a closed surface is
the integral of its pullback.** For a smooth map `u : C → X` from a compact connected oriented
boundaryless surface and an integral fundamental class `μ` of `C`, there is a sign `s = ±1` such
that for every closed two-form `β` on `X`, the period of `β` on `u_* μ ∈ H₂(X; ℤ)` is `s` times
`∫_C u^* β`. -/
theorem exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm
    (hW : finrank ℝ W = 2) (o : Manifold.Orientation I C (Fin 2))
    {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
    (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ) {u : C → X}
    (hu : ContMDiff I J ∞ u) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ β : closedForms J X 2,
      closedFormHomologyPeriod β (ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ) =
        s * integralTopForm o (mpullback I J u β.val.val) := by
  obtain ⟨s, hs, h⟩ := exists_closedFormHomologyPeriod_eq_mul_integralTopForm hW o hμ
  refine ⟨s, hs, fun β ↦ ?_⟩
  rw [← closedFormHomologyPeriod_mpullback hu, h, closedForms.coe_mpullback,
    SmoothForm.coe_mpullback]

/-- A closed two-form `β` has zero period on the image `u_* μ` of the fundamental class of a closed
surface exactly when `∫_C u^* β = 0`. -/
theorem closedFormHomologyPeriod_singularHomologyMap_eq_zero_iff (hW : finrank ℝ W = 2)
    (o : Manifold.Orientation I C (Fin 2)) {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
    (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ) {u : C → X}
    (hu : ContMDiff I J ∞ u) (β : closedForms J X 2) :
    closedFormHomologyPeriod β (ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ) = 0 ↔
      integralTopForm o (mpullback I J u β.val.val) = 0 := by
  rw [← closedFormHomologyPeriod_mpullback hu,
    closedFormHomologyPeriod_eq_zero_iff_integralTopForm_eq_zero hW o hμ, closedForms.coe_mpullback,
    SmoothForm.coe_mpullback]

end Surface

end TauCeti
