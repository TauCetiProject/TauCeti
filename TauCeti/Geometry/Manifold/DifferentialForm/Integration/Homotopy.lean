/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Integrals of two-forms over rectangles and their homotopy invariance

The integral of a two-form `φ` on a manifold `M` over a map `u : ℝ × ℝ → M` on the rectangle with
opposite corners `a` and `b` is

`∫_u φ = ∫_{a.1}^{b.1} ∫_{a.2}^{b.2} φ_{u(s, t)}(∂_s u, ∂_t u) dt ds`,

the iterated integral of the pullback `u^* φ` against the coordinate orientation of the plane
(`TauCeti.rectangleIntegral`). For a symplectic form this is the symplectic area of `u`. When
`u(s, ·)` is a loop for every `s`, so that `u` is a cylinder between the loops `u(a.1, ·)` and
`u(b.1, ·)`, it is the area term `∫ ū^* ω` of the Hamiltonian action functional on the free loop
space, in which `ū` joins a loop to a reference loop; and when one of these loops is constant,
`u` is a cap of the other.

The basic property of these integrals is **Stokes' formula for a homotopy**. Let `φ` be closed and
let `Φ : (ℝ × ℝ) × ℝ → M` be a `C²` family of maps `Φ(·, c)` of the plane. The integral of the
closed form `Φ^* φ` over the boundary of the cube `[a, b] × [0, 1]` vanishes, so the difference of
the integrals over the top face `Φ(·, 1)` and the bottom face `Φ(·, 0)` is a signed sum of the
integrals over the four side faces, swept out by the four edges of the rectangle during the
homotopy (`TauCeti.rectangleIntegral_sub_rectangleIntegral_eq_sides`). A side face contributes
nothing when it is degenerate: when its edge stays fixed during the homotopy, or remains a
constant path. Indeed the integral over any map that only depends on one of the two coordinates
vanishes (`TauCeti.rectangleIntegral_comp_fst`, `TauCeti.rectangleIntegral_comp_snd`). Hence the
integral over a cylinder is invariant under homotopies through cylinders whose boundary loops are
each either fixed or constant (`TauCeti.rectangleIntegral_eq_of_homotopy`). This covers homotopies
of cylinders relative to their boundary loops, homotopies of caps relative to the capped loop, and
homotopies of spheres presented as cylinders between constant loops. It is the analytic input for
showing that the Hamiltonian action of a loop does not depend on the choice of cylinder or cap
within a homotopy class.

This is the two-dimensional analogue of the line integral `TauCeti.pathIntegral`: it integrates
along an arbitrary map of the plane, without the integrability conditions of the integral of a top
form over the rectangle manifold. Like the line integral, it is additive over adjacent rectangles
(`TauCeti.rectangleIntegral_add_adjacent`) and invariant under `C¹` reparametrization
(`TauCeti.rectangleIntegral_comp_prodMap`, in the first coordinate), and the two are related by
Stokes' formula: the integral of an exact form `dα` over a map of a rectangle is the signed sum of
the line integrals of `α` along the images of the four edges
(`TauCeti.rectangleIntegral_mextDeriv`).

The proof pulls `φ` back to the flat form `ψ = Φ^* φ` on `(ℝ × ℝ) × ℝ`, which is closed because
pullback commutes with the exterior derivative, and expresses the integral over each face of the
cube as an iterated integral of `ψ` by the chain rule. The flat statement is Stokes' formula on the
boundary of a cube (`TauCeti.integral2_slice_sub_eq_sides`), proved with the cylinder homotopy
operator and Stokes' formula on a rectangle; no Stokes theorem on a manifold with corners is used.

## Main definitions

* `TauCeti.rectangleIntegral φ u a b`: the integral of the two-form `φ` over the map `u` on the
  rectangle with opposite corners `a` and `b`.

## Main results

* `TauCeti.IsSmoothForm.setIntegral_eq_rectangleIntegral`: for a continuous form and a `C¹` map,
  the integral is the integral of `φ_{u(z)}(∂_s u, ∂_t u)` over the rectangle (Fubini).
* `TauCeti.rectangleIntegral_mpullback`: naturality under pullback of forms.
* `TauCeti.rectangleIntegral_congr`: the integral only depends on the map on the closed rectangle.
* `TauCeti.rectangleIntegral_comp_fst`, `TauCeti.rectangleIntegral_comp_snd`: the integral over a
  map depending on only one coordinate vanishes.
* `TauCeti.rectangleIntegral_add_adjacent`: additivity over adjacent rectangles.
* `TauCeti.rectangleIntegral_comp_prodMap`: reparametrization invariance in the first coordinate.
* `TauCeti.hasDerivAt_rectangleIntegral`: the derivative of the integral in its upper first
  coordinate, the integral of `φ(∂_s u, ∂_t u)` along the moving edge.
* `TauCeti.rectangleIntegral_mextDeriv`: Stokes' formula for the integral of an exact form, in
  terms of line integrals along the edges.
* `TauCeti.rectangleIntegral_sub_rectangleIntegral_eq_sides`: Stokes' formula for a homotopy of
  maps of a rectangle, for a closed form.
* `TauCeti.rectangleIntegral_eq_of_homotopy`: homotopy invariance of the integral of a closed form
  over a cylinder whose boundary loops stay fixed or constant.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §4
  (the homotopy operator and homotopy invariance).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (the symplectic action and its dependence on the cylinder).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the action functional on contractible loops).
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Interval ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The integral of a two-form `φ` over a map `u : ℝ × ℝ → M` on the rectangle with opposite
corners `a` and `b`, oriented by the coordinates `(s, t)` of the plane: the iterated integral
`∫_{a.1}^{b.1} ∫_{a.2}^{b.2} φ_{u(s, t)}(∂_s u, ∂_t u) dt ds` of the pullback `u^* φ` evaluated on
the coordinate vectors. Exchanging the two corners in one coordinate changes its sign. -/
def rectangleIntegral (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) : F :=
  ∫ s in a.1..b.1, ∫ t in a.2..b.2, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]

/-- The defining formula of `TauCeti.rectangleIntegral`. -/
theorem rectangleIntegral_def (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ u a b =
      ∫ s in a.1..b.1, ∫ t in a.2..b.2, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)] :=
  (rfl)

/-- The integrand of `TauCeti.rectangleIntegral` is `φ` on the partial derivatives of `u`. -/
private theorem mpullback_apply_coord (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    mpullback 𝓘(ℝ, ℝ × ℝ) I u φ z ![(1, 0), (0, 1)] =
      φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  simp only [mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The integral over a map `u` is the iterated integral of `φ` on the partial derivatives
of `u`. -/
theorem rectangleIntegral_eq (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ u a b = ∫ s in a.1..b.1, ∫ t in a.2..b.2,
      φ (u (s, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (0, 1)] :=
  intervalIntegral.integral_congr fun s _ ↦ intervalIntegral.integral_congr fun t _ ↦
    mpullback_apply_coord φ u (s, t)

/-- For a continuous form `φ` and a `C¹` map `u` of the plane, the integrand
`φ_{u(z)}(∂_s u, ∂_t u)` of the integral over `u` is continuous. -/
theorem IsSmoothForm.continuous_apply_mfderiv [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) :
    Continuous fun z ↦ φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] :=
  (hφ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]).congr fun z ↦ mpullback_apply_coord φ u z

/-- For a continuous form `φ` and a `C¹` map `u`, the integral over `u` on a rectangle is, by
Fubini, the integral of `φ_{u(z)}(∂_s u, ∂_t u)` over the rectangle. -/
theorem IsSmoothForm.setIntegral_eq_rectangleIntegral [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {a b : ℝ × ℝ} (hab : a ≤ b) :
    ∫ z in Icc a b, φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] = rectangleIntegral φ u a b := by
  have hint := (hφ.continuous_apply_mfderiv hu).continuousOn.integrableOn_compact
    (μ := volume) (isCompact_Icc (a := a) (b := b))
  -- Fubini, on the rectangle written as a product of intervals.
  rw [Icc_prod_eq, Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint, rectangleIntegral_eq, intervalIntegral.integral_of_le hab.1,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ ↦ ?_
  rw [intervalIntegral.integral_of_le hab.2, ← integral_Icc_eq_integral_Ioc]

/-- The integral is natural under pullback of forms. -/
theorem rectangleIntegral_mpullback {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {f : M → M'} (φ : RoughForm I' M' F 2) {u : ℝ × ℝ → M} {a b : ℝ × ℝ}
    (hf : ∀ z ∈ [[a.1, b.1]] ×ˢ [[a.2, b.2]], MDifferentiableAt I I' f (u z))
    (hu : ∀ z ∈ [[a.1, b.1]] ×ˢ [[a.2, b.2]], MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
    rectangleIntegral (mpullback I I' f φ) u a b = rectangleIntegral φ (f ∘ u) a b := by
  refine intervalIntegral.integral_congr fun s hs ↦ intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [mpullback_comp_at (hu _ ⟨hs, ht⟩) (hf _ ⟨hs, ht⟩)]

/-- The integral only depends on the map on the closed rectangle. -/
theorem rectangleIntegral_congr {φ : RoughForm I M F 2} {u v : ℝ × ℝ → M} {a b : ℝ × ℝ}
    (h : EqOn u v ([[a.1, b.1]] ×ˢ [[a.2, b.2]])) :
    rectangleIntegral φ u a b = rectangleIntegral φ v a b := by
  -- The maps agree near every interior point, so their pullbacks agree there; the boundary of
  -- the rectangle is a null set.
  have hne (x y : ℝ) : ∀ᵐ r ∂volume, r ≠ max x y := by
    simpa using (countable_singleton (max x y)).ae_notMem volume
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hne a.1 b.1] with s hs₁ hs₂
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hne a.2 b.2] with t ht₁ ht₂
  have hmem : Ioo (min a.1 b.1) (max a.1 b.1) ×ˢ Ioo (min a.2 b.2) (max a.2 b.2) ∈ 𝓝 (s, t) :=
    prod_mem_nhds (Ioo_mem_nhds hs₂.1 (lt_of_le_of_ne hs₂.2 hs₁))
      (Ioo_mem_nhds ht₂.1 (lt_of_le_of_ne ht₂.2 ht₁))
  exact congrFun (congrArg DFunLike.coe ((Filter.eventuallyEq_of_mem hmem
    (h.mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))).mpullback_eq φ)) _

/-- The integral of the zero form vanishes. -/
@[simp]
theorem rectangleIntegral_zero (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral (0 : RoughForm I M F 2) u a b = 0 := by
  simp [rectangleIntegral_def]

/-- The integral of the negative of a form is the negative of its integral. -/
@[simp]
theorem rectangleIntegral_neg (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral (-φ) u a b = -rectangleIntegral φ u a b := by
  simp [rectangleIntegral_eq, intervalIntegral.integral_neg]

/-- The integral is linear in the coefficients for scalar multiplication. -/
@[simp]
theorem rectangleIntegral_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral (c • φ) u a b = c • rectangleIntegral φ u a b := by
  simp [rectangleIntegral_eq, intervalIntegral.integral_smul]

/-- The integral of a sum of forms is the sum of the integrals, as soon as, for both forms, the
inner integrands are interval integrable for every `s` between `a.1` and `b.1` and the inner
integrals are interval integrable in `s`. -/
theorem rectangleIntegral_add {φ ψ : RoughForm I M F 2} {u : ℝ × ℝ → M} {a b : ℝ × ℝ}
    (hφ : ∀ s ∈ [[a.1, b.1]], IntervalIntegrable
      (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]) volume a.2 b.2)
    (hψ : ∀ s ∈ [[a.1, b.1]], IntervalIntegrable
      (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u ψ (s, t) ![(1, 0), (0, 1)]) volume a.2 b.2)
    (hφ' : IntervalIntegrable (fun s ↦ ∫ t in a.2..b.2,
      mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]) volume a.1 b.1)
    (hψ' : IntervalIntegrable (fun s ↦ ∫ t in a.2..b.2,
      mpullback 𝓘(ℝ, ℝ × ℝ) I u ψ (s, t) ![(1, 0), (0, 1)]) volume a.1 b.1) :
    rectangleIntegral (φ + ψ) u a b = rectangleIntegral φ u a b + rectangleIntegral ψ u a b := by
  simp only [rectangleIntegral_def, mpullback_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply]
  rw [← intervalIntegral.integral_add hφ' hψ']
  exact intervalIntegral.integral_congr fun s hs ↦ intervalIntegral.integral_add (hφ s hs) (hψ s hs)

/-- The integral of a difference of forms is the difference of the integrals, as soon as, for both
forms, the inner integrands are interval integrable for every `s` between `a.1` and `b.1` and the
inner integrals are interval integrable in `s`. -/
theorem rectangleIntegral_sub {φ ψ : RoughForm I M F 2} {u : ℝ × ℝ → M} {a b : ℝ × ℝ}
    (hφ : ∀ s ∈ [[a.1, b.1]], IntervalIntegrable
      (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]) volume a.2 b.2)
    (hψ : ∀ s ∈ [[a.1, b.1]], IntervalIntegrable
      (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u ψ (s, t) ![(1, 0), (0, 1)]) volume a.2 b.2)
    (hφ' : IntervalIntegrable (fun s ↦ ∫ t in a.2..b.2,
      mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]) volume a.1 b.1)
    (hψ' : IntervalIntegrable (fun s ↦ ∫ t in a.2..b.2,
      mpullback 𝓘(ℝ, ℝ × ℝ) I u ψ (s, t) ![(1, 0), (0, 1)]) volume a.1 b.1) :
    rectangleIntegral (φ - ψ) u a b = rectangleIntegral φ u a b - rectangleIntegral ψ u a b := by
  rw [sub_eq_add_neg φ, sub_eq_add_neg, ← rectangleIntegral_neg]
  refine rectangleIntegral_add hφ (fun s hs ↦ ?_) hφ' ?_
  · simpa [Pi.neg_def] using (hψ s hs).neg
  · simpa [Pi.neg_def, intervalIntegral.integral_neg] using hψ'.neg

/-- The integral over a rectangle of zero width vanishes. -/
@[simp]
theorem rectangleIntegral_of_fst_eq (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) {a b : ℝ × ℝ}
    (h : a.1 = b.1) : rectangleIntegral φ u a b = 0 := by
  simp [rectangleIntegral_def, h]

/-- The integral over a rectangle of zero height vanishes. -/
@[simp]
theorem rectangleIntegral_of_snd_eq (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) {a b : ℝ × ℝ}
    (h : a.2 = b.2) : rectangleIntegral φ u a b = 0 := by
  simp [rectangleIntegral_def, h]

/-- Exchanging the corners in the first coordinate changes the sign of the integral. -/
theorem rectangleIntegral_symm_fst (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a₁ a₂ b₁ b₂ : ℝ) :
    rectangleIntegral φ u (b₁, a₂) (a₁, b₂) = -rectangleIntegral φ u (a₁, a₂) (b₁, b₂) :=
  intervalIntegral.integral_symm _ _

/-- Exchanging the corners in the second coordinate changes the sign of the integral. -/
theorem rectangleIntegral_symm_snd (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a₁ a₂ b₁ b₂ : ℝ) :
    rectangleIntegral φ u (a₁, b₂) (b₁, a₂) = -rectangleIntegral φ u (a₁, a₂) (b₁, b₂) := by
  simp only [rectangleIntegral_def]
  rw [← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun _ _ ↦ intervalIntegral.integral_symm _ _

/-- The integral of a two-form over a map that only depends on the second coordinate vanishes. -/
@[simp]
theorem rectangleIntegral_comp_snd (φ : RoughForm I M F 2) (γ : ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ (γ ∘ Prod.snd) a b = 0 := by
  have h (z : ℝ × ℝ) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (γ ∘ Prod.snd) φ z ![(1, 0), (0, 1)] = 0 :=
    mpullback_comp_clm_apply_eq_zero φ γ (.snd ℝ ℝ ℝ) (j := fun t ↦ (z.1, t)) (by fun_prop)
      (fun _ ↦ rfl) rfl (i := 0) rfl
  simp [rectangleIntegral_def, h]

/-- The integral of a two-form over a map that only depends on the first coordinate vanishes. -/
@[simp]
theorem rectangleIntegral_comp_fst (φ : RoughForm I M F 2) (γ : ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ (γ ∘ Prod.fst) a b = 0 := by
  have h (z : ℝ × ℝ) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (γ ∘ Prod.fst) φ z ![(1, 0), (0, 1)] = 0 :=
    mpullback_comp_clm_apply_eq_zero φ γ (.fst ℝ ℝ ℝ) (j := fun s ↦ (s, z.2)) (by fun_prop)
      (fun _ ↦ rfl) rfl (i := 1) rfl
  simp [rectangleIntegral_def, h]

section Continuous

variable [IsManifold I 1 M]

/-- For a continuous form and a `C¹` map of the plane, the inner integral defining
`TauCeti.rectangleIntegral` is a continuous function of the first coordinate. -/
private theorem continuous_integral_mpullback_apply {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (c d : ℝ) :
    Continuous fun s ↦ ∫ t in c..d, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)] := by
  have h := isSmoothForm_modelSpace_iff.mp (hφ.mpullback (by simpa using hu))
  have hG : Continuous fun z ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ z ![(1, 0), (0, 1)] :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) F ![(1, 0), (0, 1)]).continuous.comp h.continuous
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by exact hG) c d

/-- **The derivative of the integral over a rectangle in its upper first coordinate.** For a
continuous form `φ` and a `C¹` map `u` of the plane, moving the edge `s = b.1` of the rectangle
changes the integral at the rate of the integral of `φ_{u(b.1, t)}(∂_s u, ∂_t u)` along that
edge. -/
theorem hasDerivAt_rectangleIntegral [CompleteSpace F] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a : ℝ × ℝ)
    (d s : ℝ) :
    HasDerivAt (fun s ↦ rectangleIntegral φ u a (s, d))
      (∫ t in a.2..d, φ (u (s, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (0, 1)]) s :=
  ((continuous_integral_mpullback_apply hφ hu a.2 d).integral_hasStrictDerivAt a.1 s).hasDerivAt
    |>.congr_deriv (intervalIntegral.integral_congr fun t _ ↦ mpullback_apply_coord φ u (s, t))

/-- Integrals over adjacent rectangles `[a.1, b] × [a.2, c.2]` and `[b, c.1] × [a.2, c.2]` add
up, for a continuous form and a `C¹` map of the plane. -/
theorem rectangleIntegral_add_adjacent {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a : ℝ × ℝ) (b : ℝ) (c : ℝ × ℝ) :
    rectangleIntegral φ u a (b, c.2) + rectangleIntegral φ u (b, a.2) c =
      rectangleIntegral φ u a c := by
  have h := continuous_integral_mpullback_apply hφ hu a.2 c.2
  exact intervalIntegral.integral_add_adjacent_intervals (h.intervalIntegrable _ _)
    (h.intervalIntegrable _ _)

/-- **Reparametrization invariance in the first coordinate.** For a continuous form `φ`, a `C¹`
map `u` of the plane and a `C¹` change of parameter `σ`, the integral over
`(s, t) ↦ u (σ s, t)` is the integral over `u` on the rectangle between the image corners. The
change of parameter need not be monotone. -/
theorem rectangleIntegral_comp_prodMap {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {σ σ' : ℝ → ℝ} {a b : ℝ × ℝ}
    (hσ : ∀ s ∈ [[a.1, b.1]], HasDerivAt σ (σ' s) s) (hσ' : ContinuousOn σ' [[a.1, b.1]]) :
    rectangleIntegral φ (u ∘ Prod.map σ id) a b =
      rectangleIntegral φ u (σ a.1, a.2) (σ b.1, b.2) := by
  rw [rectangleIntegral_def, rectangleIntegral_def,
    ← intervalIntegral.integral_deriv_smul_comp hσ hσ'
      (continuous_integral_mpullback_apply hφ hu a.2 b.2)]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [Function.comp_apply, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  -- The derivative of `Prod.map σ id` sends the coordinate vectors to `(σ' s, 0)` and `(0, 1)`.
  let A : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (σ' s)).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hL : HasFDerivAt (Prod.map σ id) A (s, t) :=
    (hσ s hs).hasFDerivAt.prodMap (s, t) (hasFDerivAt_id t)
  have hv : (A ∘ ![(1, 0), (0, 1)]) =
      Function.update ![((1 : ℝ), (0 : ℝ)), (0, 1)] 0 (σ' s • ((1 : ℝ), (0 : ℝ))) := by
    funext i
    fin_cases i <;> simp [A]
  rw [mpullback_comp_apply_of_hasFDerivAt hL ((hu _).mdifferentiableAt one_ne_zero)]
  -- Read the pullback as a flat form on the plane, whose tangent spaces are `ℝ × ℝ` itself.
  let ψ : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ) I u φ
  refine (((ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans
    (congrArg _ hv)).trans ((ψ (σ s, t)).map_update_smul _ _ _ _)).trans ?_
  congr 2
  funext i
  fin_cases i <;> rfl

end Continuous

/-- A side face of a homotopy, over `[y₀, y₁] × [0, 1]`, has zero integral when its edge stays
fixed, or remains a constant path at `y`, during the homotopy. -/
private theorem rectangleIntegral_side_eq_zero (φ : RoughForm I M F 2) {Φ : (ℝ × ℝ) × ℝ → M}
    {x y y₀ y₁ : ℝ}
    (h : (∀ t ∈ [[y₀, y₁]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((x, t), c) = Φ ((x, t), 0)) ∨
      ∀ t ∈ [[y₀, y₁]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((x, t), c) = Φ ((x, y), c)) :
    rectangleIntegral φ (fun p ↦ Φ ((x, p.1), p.2)) (y₀, 0) (y₁, 1) = 0 := by
  rcases h with h | h
  · have hface : EqOn (fun p : ℝ × ℝ ↦ Φ ((x, p.1), p.2)) ((fun t ↦ Φ ((x, t), 0)) ∘ Prod.fst)
        ([[y₀, y₁]] ×ˢ [[0, 1]]) :=
      fun p hp ↦ h p.1 hp.1 p.2 ((uIcc_of_le zero_le_one).subset hp.2)
    rw [rectangleIntegral_congr hface]
    exact rectangleIntegral_comp_fst φ _ _ _
  · have hface : EqOn (fun p : ℝ × ℝ ↦ Φ ((x, p.1), p.2)) ((fun c ↦ Φ ((x, y), c)) ∘ Prod.snd)
        ([[y₀, y₁]] ×ˢ [[0, 1]]) :=
      fun p hp ↦ h p.1 hp.1 p.2 ((uIcc_of_le zero_le_one).subset hp.2)
    rw [rectangleIntegral_congr hface]
    exact rectangleIntegral_comp_snd φ _ _ _

variable [CompleteSpace F] [IsManifold I 2 M]

/-- **Stokes' formula for a homotopy of maps of a rectangle.** Let `φ` be a closed `C¹` two-form
and `Φ : (ℝ × ℝ) × ℝ → M` a `C²` homotopy from `Φ(·, 0)` to `Φ(·, 1)`. The integral of `Φ^* φ`
over the boundary of the cube `[a, b] × [0, 1]` vanishes: the change of the integral over the
rectangle `[a, b]` from `Φ(·, 0)` to `Φ(·, 1)` is the signed sum of the integrals over the side
faces `(t, c) ↦ Φ((a.1, t), c)`, `(t, c) ↦ Φ((b.1, t), c)`, `(s, c) ↦ Φ((s, a.2), c)` and
`(s, c) ↦ Φ((s, b.2), c)` swept out by the edges of the rectangle. -/
theorem rectangleIntegral_sub_rectangleIntegral_eq_sides {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {Φ : (ℝ × ℝ) × ℝ → M}
    (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ) (a b : ℝ × ℝ) :
    rectangleIntegral φ (fun z ↦ Φ (z, 1)) a b - rectangleIntegral φ (fun z ↦ Φ (z, 0)) a b =
      (rectangleIntegral φ (fun p ↦ Φ ((a.1, p.1), p.2)) (a.2, 0) (b.2, 1) -
        rectangleIntegral φ (fun p ↦ Φ ((b.1, p.1), p.2)) (a.2, 0) (b.2, 1)) -
      (rectangleIntegral φ (fun p ↦ Φ ((p.1, a.2), p.2)) (a.1, 0) (b.1, 1) -
        rectangleIntegral φ (fun p ↦ Φ ((p.1, b.2), p.2)) (a.1, 0) (b.1, 1)) := by
  -- The flat closed form `ψ = Φ^* φ` on `(ℝ × ℝ) × ℝ` and its cylinder homotopy `β = h ψ`.
  let ψ : (ℝ × ℝ) × ℝ → ((ℝ × ℝ) × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, (ℝ × ℝ) × ℝ) I Φ φ
  have hΦd : MDifferentiable 𝓘(ℝ, (ℝ × ℝ) × ℝ) I Φ := hΦ.mdifferentiable two_ne_zero
  have hψ : ContDiff ℝ 1 ψ := by
    have h := hφ.mpullback (f := Φ) (by simpa [one_add_one_eq_two] using hΦ)
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    exact (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      (((isSmoothForm_def _ _).mp h x).contMDiffWithinAt (s := univ))).contDiffAt Filter.univ_mem
  have hdψ : extDeriv ψ = 0 := by
    funext x
    rw [← mextDeriv_eq_extDeriv,
      ← mpullback_mextDeriv hΦ ((isSmoothBundleForm_def _ _).mpr hφ.contMDiff), hdφ,
      mpullback_zero]
    -- Both sides are the zero form at `x`, as a manifold form and as a flat form.
    rfl
  -- Every face is a composite `Φ ∘ L` with `L` affine, and its integral is the iterated integral
  -- of `ψ` on the images under `dL` of the coordinate vectors.
  have hface {L : ℝ × ℝ → (ℝ × ℝ) × ℝ} {A : ℝ × ℝ →L[ℝ] (ℝ × ℝ) × ℝ}
      (hL : ∀ p, HasFDerivAt L A p) (a' b' : ℝ × ℝ) :
      rectangleIntegral φ (Φ ∘ L) a' b' =
        ∫ s in a'.1..b'.1, ∫ t in a'.2..b'.2, ψ (L (s, t)) ![A (1, 0), A (0, 1)] := by
    refine intervalIntegral.integral_congr fun s _ ↦ intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [mpullback_comp_apply_of_hasFDerivAt (hL _) (hΦd _)]
    refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans (congrArg _ ?_)
    funext i
    fin_cases i <;> rfl
  have hs (x : ℝ) := hface (L := fun p ↦ ((x, p.1), p.2))
    (fun p ↦ ((hasFDerivAt_const x p).prodMk hasFDerivAt_fst).prodMk hasFDerivAt_snd) (a.2, 0)
    (b.2, 1)
  have ht (y : ℝ) := hface (L := fun p ↦ ((p.1, y), p.2))
    (fun p ↦ (hasFDerivAt_fst.prodMk (hasFDerivAt_const y p)).prodMk hasFDerivAt_snd) (a.1, 0)
    (b.1, 1)
  have hc (c : ℝ) := hface (L := fun z ↦ (z, c)) (fun p ↦ hasFDerivAt_prodMk_left p c) a b
  simp only [Function.comp_def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', zero_apply]
    at hs ht hc
  rw [hc, hc, hs, hs, ht, ht]
  exact integral2_slice_sub_eq_sides hψ hdψ a b

/-- **Homotopy invariance of the integral over a cylinder.** Let `φ` be a closed `C¹` two-form and
`Φ : (ℝ × ℝ) × ℝ → M` a `C²` homotopy through cylinders `Φ(·, c)` on the rectangle `[a, b]`: the
edges `t = a.2` and `t = b.2` of each rectangle are mapped alike, so that `t ↦ Φ((s, t), c)` is a
loop on `[a.2, b.2]` for every `s`. Suppose that each of the two boundary loops `s = a.1` and
`s = b.1` either stays fixed or remains a constant loop during the homotopy. These conditions are
only imposed on the rectangle and for `c ∈ [0, 1]`. Then the integrals of `φ` over `Φ(·, 0)` and
`Φ(·, 1)` agree. -/
theorem rectangleIntegral_eq_of_homotopy {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) {Φ : (ℝ × ℝ) × ℝ → M} (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ)
    {a b : ℝ × ℝ}
    (ha : (∀ t ∈ [[a.2, b.2]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((a.1, t), c) = Φ ((a.1, t), 0)) ∨
      ∀ t ∈ [[a.2, b.2]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((a.1, t), c) = Φ ((a.1, a.2), c))
    (hb : (∀ t ∈ [[a.2, b.2]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((b.1, t), c) = Φ ((b.1, t), 0)) ∨
      ∀ t ∈ [[a.2, b.2]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((b.1, t), c) = Φ ((b.1, b.2), c))
    (hper : ∀ s ∈ [[a.1, b.1]], ∀ c ∈ Icc (0 : ℝ) 1, Φ ((s, b.2), c) = Φ ((s, a.2), c)) :
    rectangleIntegral φ (fun z ↦ Φ (z, 1)) a b = rectangleIntegral φ (fun z ↦ Φ (z, 0)) a b := by
  have h := rectangleIntegral_sub_rectangleIntegral_eq_sides hφ hdφ hΦ a b
  -- The two edges `t = a.2` and `t = b.2` sweep out the same side face.
  have hper' : rectangleIntegral φ (fun p ↦ Φ ((p.1, b.2), p.2)) (a.1, 0) (b.1, 1) =
      rectangleIntegral φ (fun p ↦ Φ ((p.1, a.2), p.2)) (a.1, 0) (b.1, 1) :=
    rectangleIntegral_congr fun p hp ↦ hper p.1 hp.1 p.2 ((uIcc_of_le zero_le_one).subset hp.2)
  rw [rectangleIntegral_side_eq_zero φ ha, rectangleIntegral_side_eq_zero φ hb, hper'] at h
  simpa [sub_eq_zero] using h

omit [CompleteSpace F] in
/-- **Stokes' formula for the integral over a map of a rectangle.** For a `C¹` one-form `α` and a
`C²` map `u`, the integral of `dα` over `u` on the rectangle with corners `a` and `b` is the
signed sum of the line integrals of `α` along the images of its four edges: the right and bottom
edges count positively, the left and top edges negatively. -/
theorem rectangleIntegral_mextDeriv {α : RoughForm I M F 1} (hα : IsSmoothForm I 1 α)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (a b : ℝ × ℝ) :
    rectangleIntegral (mextDeriv α) u a b =
      (pathIntegral α (fun t ↦ u (b.1, t)) a.2 b.2 -
        pathIntegral α (fun t ↦ u (a.1, t)) a.2 b.2) -
      (pathIntegral α (fun s ↦ u (s, b.2)) a.1 b.1 -
        pathIntegral α (fun s ↦ u (s, a.2)) a.1 b.1) := by
  -- The flat one-form `ψ = u^* α` on the plane, whose exterior derivative is `u^* dα`.
  let ψ : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ) I u α
  have hψ : ContDiff ℝ 1 ψ :=
    isSmoothForm_modelSpace_iff.mp (hα.mpullback (by simpa [one_add_one_eq_two] using hu))
  have hdψ (z : ℝ × ℝ) : mpullback 𝓘(ℝ, ℝ × ℝ) I u (mextDeriv α) z = extDeriv ψ z := by
    rw [← mextDeriv_eq_extDeriv,
      mpullback_mextDeriv hu ((isSmoothBundleForm_def _ _).mpr hα.contMDiff)]
  -- Each edge is a composite `u ∘ L` with `L` affine, and its line integral is the integral of
  -- `ψ` on the image under `dL` of the unit vector.
  have hedge {L : ℝ → ℝ × ℝ} {A : ℝ →L[ℝ] ℝ × ℝ} (hL : ∀ r, HasFDerivAt L A r) (c d : ℝ) :
      pathIntegral α (u ∘ L) c d = ∫ r in c..d, ψ (L r) fun _ ↦ A 1 := by
    rw [pathIntegral_eq_integral_mpullback]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    rw [mpullback_comp_apply_of_hasFDerivAt (hL r) ((hu _).mdifferentiableAt two_ne_zero)]
    exact ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _
  have hv (x : ℝ) := hedge (L := fun t ↦ (x, t)) (hasFDerivAt_prodMk_right x)
  have hh (y : ℝ) := hedge (L := fun s ↦ (s, y)) (fun s ↦ hasFDerivAt_prodMk_left s y)
  simp only [Function.comp_def, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply] at hv hh
  rw [hv, hv, hh, hh, rectangleIntegral_def]
  simp only [hdψ]
  exact integral2_extDeriv fun z _ ↦ hψ.contDiffAt

end TauCeti
