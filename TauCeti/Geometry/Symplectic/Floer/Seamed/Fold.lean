/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.TwistedProd
import TauCeti.Geometry.Symplectic.JHolomorphic.Conj
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Folding seamed Floer cylinders into strips

The Floer theory of a symplectomorphism of `(M, σ)` counts seamed cylinders: maps
`v : ℝ × ℝ → M` with the seam condition `v(s, t + 1) = φ(v(s, t))` for a symplectomorphism `φ`,
so that each slice `v(s, ·)` restricts to a `φ`-seamed path (`TauCeti.SeamedPath`), solving the
Cauchy–Riemann equation `∂_s v + J_t ∂_t v = 0` for a family `J_t` of almost complex structures.
Folding such a cylinder
along the line `t = 0` turns it into a strip in the product `M × M` with Lagrangian boundary
conditions on the diagonal and on a graph. Its **fold** is

`w(s, t) = (v(s / 2, t / 2), v(s / 2, -t / 2))` (`TauCeti.Floer.fold`),

on the strip `ℝ × [0, 1]`, so that both the `s`- and the `t`-coordinate are rescaled by `1 / 2`.
The two halves `ℝ × [0, 1/2]` and `ℝ × [-1/2, 0]` of one period of the cylinder become the two
components of the fold; the second is reflected in `t`.

* **Boundary conditions.** On the line `t = 0` the fold lies on the diagonal
  (`TauCeti.Floer.fold_apply_zero`). On the line `t = 1` the seam condition gives
  `w(s, 1) = (φ y, y)` with `y = v(s / 2, -1/2)` (`TauCeti.Floer.fold_apply_one`). For a
  diffeomorphism `φ` this is the graph `{(x, φ⁻¹ x)}` of `φ⁻¹`. For the twisted product form
  `pr₁^* σ - pr₂^* σ` the diagonal and the graph of `φ⁻¹` are Lagrangian when `φ` preserves `σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_diagonal` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_graph_iff`).
* **The equation.** The differential of the fold is
  `dw(a, b) = (½ dv(a, b), ½ dv(a, -b))`, the two components taken at the two points of the
  cylinder (`TauCeti.Floer.tangentSpaceProdEquiv_mfderiv_fold_apply`). The reflection
  `(a, b) ↦ (a, -b)` is antiholomorphic, so `w` is holomorphic for the structure
  `J_{t/2} ⊕ (-J_{-t/2})` exactly when `v` is holomorphic for `J_{t/2}` at `(s / 2, t / 2)` and for
  `J_{-t/2}` at `(s / 2, -t / 2)` (`TauCeti.Floer.isComplexLinearMap_mfderiv_fold_iff`). So the
  fold of `v` solves the Cauchy–Riemann equation on the strip `ℝ × [0, 1]` exactly when `v`
  solves it on `ℝ × [-1/2, 1/2]`
  (`TauCeti.Floer.forall_isComplexLinearMap_mfderiv_fold_iff`, for structures that may depend on
  the domain point). The folded structure is compatible with, or tamed by, the twisted product
  form whenever the `J_t` are with `σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.compatible_symplecticFormAt_twistedProd` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.tames_symplecticFormAt_twistedProd`).
* **Energy.** The symplectic area density of the fold for the twisted product form is
  `¼ (σ(∂_s v, ∂_t v)(s / 2, t / 2) + σ(∂_s v, ∂_t v)(s / 2, -t / 2))`
  (`TauCeti.SmoothTwoForm.floerEnergyDensity_twistedProd_fold`): the reflection reverses the
  orientation and the sign of the second form at once. By the change of variables formula the
  energy of the fold on the strip `ℝ × [0, 1]` is the energy of `v` on one period
  `ℝ × [-1/2, 1/2]` of the cylinder
  (`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_twistedProd_fold`).

These are pointwise and integral identities for classical maps; no completion, compactness or
transversality is involved.

## Main declarations

* `TauCeti.Floer.fold`: the fold `(s, t) ↦ (v(s / 2, t / 2), v(s / 2, -t / 2))` of a map
  `v : ℝ × ℝ → M`.
* `TauCeti.Floer.fold_apply_zero`, `TauCeti.Floer.fold_apply_one`: the diagonal and graph boundary
  conditions.
* `TauCeti.Floer.isComplexLinearMap_mfderiv_fold_iff`,
  `TauCeti.Floer.forall_isComplexLinearMap_mfderiv_fold_iff`: the fold is holomorphic exactly when
  the cylinder is.
* `TauCeti.SmoothTwoForm.floerEnergyDensity_twistedProd_fold`,
  `TauCeti.SmoothTwoForm.integral_floerEnergyDensity_twistedProd_fold`: the energy density of the
  fold and the equality of energies.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Section 9.1 (the graph of a symplectomorphism and the diagonal as
  Lagrangian boundary conditions in `M × M⁻`).
-/

public section

noncomputable section

open Function MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti.Floer

variable {M : Type*} {v : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- **The fold of a map `v : ℝ × ℝ → M`**, the map `(s, t) ↦ (v(s / 2, t / 2), v(s / 2, -t / 2))`
into `M × M`. On the strip `ℝ × [0, 1]` it records one period `ℝ × [-1/2, 1/2]` of `v`, the half
with negative `t` reflected. -/
def fold (v : ℝ × ℝ → M) (z : ℝ × ℝ) : M × M :=
  (v (z.1 / 2, z.2 / 2), v (z.1 / 2, -z.2 / 2))

@[simp]
theorem fold_apply (v : ℝ × ℝ → M) (z : ℝ × ℝ) :
    fold v z = (v (z.1 / 2, z.2 / 2), v (z.1 / 2, -z.2 / 2)) :=
  (rfl)

/-- **The diagonal boundary condition.** On the line `t = 0` the fold lies on the diagonal. -/
theorem fold_apply_zero (v : ℝ × ℝ → M) (s : ℝ) : fold v (s, 0) = (v (s / 2, 0), v (s / 2, 0)) := by
  simp

/-- **The graph boundary condition.** If `v` satisfies the seam condition
`v(s, t + 1) = φ(v(s, t))`, then on the line `t = 1` the fold is the point `(φ y, y)`, with
`y = v(s / 2, -1/2)`. -/
theorem fold_apply_one {φ : M → M} (hv : ∀ z : ℝ × ℝ, v (z.1, z.2 + 1) = φ (v z)) (s : ℝ) :
    fold v (s, 1) = (φ (v (s / 2, -1 / 2)), v (s / 2, -1 / 2)) := by
  rw [fold_apply, ← hv]
  norm_num

/-! ### The two halves of the fold as linear reparametrizations -/

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The linear map `(s, t) ↦ (s / 2, t / 2)` giving the first component of the fold. -/
private def foldUpper : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ).prodMap ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ)

/-- The linear map `(s, t) ↦ (s / 2, -t / 2)` giving the second component of the fold. -/
private def foldLower : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ).prodMap ((-2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ)

private theorem foldUpper_apply (z : ℝ × ℝ) : foldUpper z = (z.1 / 2, z.2 / 2) := by
  ext <;> simp [foldUpper, div_eq_inv_mul]

private theorem foldLower_apply (z : ℝ × ℝ) : foldLower z = (z.1 / 2, -z.2 / 2) := by
  ext <;> simp [foldLower, div_eq_inv_mul]

private theorem abs_det_fderiv_foldUpper (w : ℝ × ℝ) :
    |(fderiv ℝ foldUpper w).det| = 1 / 4 := by
  rw [foldUpper.fderiv]
  norm_num [foldUpper, ContinuousLinearMap.det]

private theorem abs_det_fderiv_foldLower (w : ℝ × ℝ) :
    |(fderiv ℝ foldLower w).det| = 1 / 4 := by
  rw [foldLower.fderiv]
  norm_num [foldLower, ContinuousLinearMap.det, LinearMap.det_prodMap]

private theorem injective_foldUpper : Injective foldUpper := fun x y h ↦ by
  simp only [foldUpper_apply, Prod.mk.injEq] at h
  ext <;> linarith [h.1, h.2]

private theorem injective_foldLower : Injective foldLower := fun x y h ↦ by
  simp only [foldLower_apply, Prod.mk.injEq] at h
  ext <;> linarith [h.1, h.2]

/-- The first half of the fold carries the strip `ℝ × [0, 1]` onto `ℝ × [0, 1/2]`. -/
private theorem image_foldUpper :
    foldUpper '' ((univ : Set ℝ) ×ˢ Icc 0 1) = (univ : Set ℝ) ×ˢ Icc 0 (1 / 2) := by
  ext ⟨a, b⟩
  simp only [mem_image, mem_prod, mem_univ, mem_Icc, true_and, foldUpper_apply, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hy₀, hy₁⟩, -, rfl⟩
    constructor <;> linarith
  · rintro ⟨hb₀, hb₁⟩
    exact ⟨2 * a, 2 * b, ⟨by linarith, by linarith⟩, by ring, by ring⟩

/-- The second half of the fold carries the strip `ℝ × [0, 1]` onto `ℝ × [-1/2, 0]`. -/
private theorem image_foldLower :
    foldLower '' ((univ : Set ℝ) ×ˢ Icc 0 1) = (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) 0 := by
  ext ⟨a, b⟩
  simp only [mem_image, mem_prod, mem_univ, mem_Icc, true_and, foldLower_apply, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hy₀, hy₁⟩, -, rfl⟩
    constructor <;> linarith
  · rintro ⟨hb₀, hb₁⟩
    exact ⟨2 * a, -(2 * b), ⟨by linarith, by linarith⟩, by ring, by ring⟩

private theorem upper_mem_period (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
    (z.1 / 2, z.2 / 2) ∈ (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2) := by
  simp only [mem_prod, mem_univ, mem_Icc, true_and] at hz ⊢
  constructor <;> linarith [hz.1, hz.2]

private theorem lower_mem_period (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
    (z.1 / 2, -z.2 / 2) ∈ (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2) := by
  simp only [mem_prod, mem_univ, mem_Icc, true_and] at hz ⊢
  constructor <;> linarith [hz.1, hz.2]

/-- The reflection `(a, b) ↦ (a, -b)` negates the imaginary unit `(0, 1)` of the plane:
`stdComplexLineConj_apply_imag` with the conjugation written out, as it occurs in the fold. -/
private theorem reflect_stdComplexLineImag :
    ((stdComplexLineImag : ℝ × ℝ).1, -(stdComplexLineImag : ℝ × ℝ).2) = -stdComplexLineImag :=
  (stdComplexLineConj_apply _).symm.trans stdComplexLineConj_apply_imag

/-- The reflection `(a, b) ↦ (a, -b)` fixes the real unit `(1, 0)` of the plane:
`stdComplexLineConj_apply_real` with the conjugation written out, as it occurs in the fold. -/
private theorem reflect_stdComplexLineReal :
    ((stdComplexLineReal : ℝ × ℝ).1, -(stdComplexLineReal : ℝ × ℝ).2) = stdComplexLineReal :=
  (stdComplexLineConj_apply _).symm.trans stdComplexLineConj_apply_real

/-- The linear algebra behind the Cauchy–Riemann equation of the fold: a map
`a ↦ (½ A a, ½ B (a.1, -a.2))` is complex linear for `J₁ ⊕ (-J₂)` exactly when `A` is complex
linear for `J₁` and `B` for `J₂`, since the reflection `(a, b) ↦ (a, -b)` is antiholomorphic. -/
private theorem isComplexLinearMap_of_apply_eq_smul_iff {V W : Type*} [AddCommGroup V]
    [Module ℝ V] [AddCommGroup W] [Module ℝ W] {J₁ : AlmostComplexStructure V}
    {J₂ : AlmostComplexStructure W} {A : ℝ × ℝ →ₗ[ℝ] V} {B : ℝ × ℝ →ₗ[ℝ] W}
    {F : ℝ × ℝ →ₗ[ℝ] V × W} (hF : ∀ a, F a = ((2⁻¹ : ℝ) • A a, (2⁻¹ : ℝ) • B (a.1, -a.2))) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₁.prod (-J₂)) F ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J₁ A ∧
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J₂ B := by
  have h2 : (2⁻¹ : ℝ) ≠ 0 := by norm_num
  rw [isComplexLinearMap_stdComplexLine_iff, isComplexLinearMap_stdComplexLine_iff,
    isComplexLinearMap_stdComplexLine_iff]
  -- The reflection negates the imaginary unit and fixes the real one, and the factor `½` cancels.
  simp only [hF, reflect_stdComplexLineImag, reflect_stdComplexLineReal, map_neg,
    AlmostComplexStructure.prod_apply, AlmostComplexStructure.neg_apply,
    AlmostComplexStructure.apply_smul, Prod.ext_iff, smul_right_inj h2, neg_inj]

/-! ### The differential of the fold and the Cauchy–Riemann equation -/

/-- **The differential of the fold.** If `v` is differentiable at the two points
`(s / 2, ± t / 2)`, then the differential of the fold at `(s, t)` is
`(a, b) ↦ (½ dv(a, b), ½ dv(a, -b))`, the two components taken at `(s / 2, t / 2)` and at
`(s / 2, -t / 2)`. -/
theorem tangentSpaceProdEquiv_mfderiv_fold_apply
    (hv₁ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, z.2 / 2))
    (hv₂ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2)) (a : ℝ × ℝ) :
    Manifold.tangentSpaceProdEquiv (fold v z) (mfderiv 𝓘(ℝ, ℝ × ℝ) (I.prod I) (fold v) z a) =
      ((2⁻¹ : ℝ) • mfderiv 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, z.2 / 2) a,
        (2⁻¹ : ℝ) • mfderiv 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2) (a.1, -a.2)) := by
  rw [← foldUpper_apply] at hv₁ ⊢
  rw [← foldLower_apply] at hv₂ ⊢
  have hfold : fold v = fun w ↦ ((v ∘ foldUpper) w, (v ∘ foldLower) w) := by
    funext w
    simp [foldUpper_apply, foldLower_apply]
  -- The chain rule for the two linear reparametrizations of the domain, whose derivatives are
  -- themselves (`ContinuousLinearMap.mfderiv_eq`).
  have hcomp (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) (hL : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (L z)) :
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (v ∘ L) z = (mfderiv 𝓘(ℝ, ℝ × ℝ) I v (L z)).comp L :=
    (mfderiv_comp z hL L.mdifferentiableAt).trans (congrArg _ L.mfderiv_eq)
  have hd := mfderiv_prodMk (hv₁.comp z foldUpper.mdifferentiableAt)
    (hv₂.comp z foldLower.mdifferentiableAt)
  rw [hcomp _ hv₁, hcomp _ hv₂] at hd
  rw [hfold, hd]
  have hU : foldUpper a = (2⁻¹ : ℝ) • a := by ext <;> simp [foldUpper]
  have hL : foldLower a = (2⁻¹ : ℝ) • (a.1, -a.2) := by ext <;> simp [foldLower]
  -- The identification of the product tangent space is the identity on vectors, so the two
  -- components are the two composites applied to `a`.
  rw [Manifold.tangentSpaceProdEquiv_apply]
  exact Prod.ext ((congrArg (mfderiv 𝓘(ℝ, ℝ × ℝ) I v (foldUpper z)) hU).trans (map_smul _ _ _))
    ((congrArg (mfderiv 𝓘(ℝ, ℝ × ℝ) I v (foldLower z)) hL).trans (map_smul _ _ _))

/-- **The fold is holomorphic exactly when the cylinder is.** At a point `(s, t)` where `v` is
differentiable at `(s / 2, ± t / 2)`, the fold of `v` solves the Cauchy–Riemann equation for the
direct sum `J₁ ⊕ (-J₂)` of a structure `J₁` at `v(s / 2, t / 2)` and the negative of a structure
`J₂` at `v(s / 2, -t / 2)` exactly when `v` solves it at `(s / 2, t / 2)` for `J₁` and at
`(s / 2, -t / 2)` for `J₂`. -/
theorem isComplexLinearMap_mfderiv_fold_iff
    (hv₁ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, z.2 / 2))
    (hv₂ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2))
    (J₁ : AlmostComplexStructure (TangentSpace I (fold v z).1))
    (J₂ : AlmostComplexStructure (TangentSpace I (fold v z).2)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J₁.prod (-J₂)).transport (Manifold.tangentSpaceProdEquiv (fold v z)).symm.toLinearEquiv)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) (I.prod I) (fold v) z :
          ℝ × ℝ →L[ℝ] TangentSpace (I.prod I) (fold v z)).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J₁
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, z.2 / 2) :
            ℝ × ℝ →L[ℝ] TangentSpace I (fold v z).1).toLinearMap ∧
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J₂
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2) :
            ℝ × ℝ →L[ℝ] TangentSpace I (fold v z).2).toLinearMap := by
  rw [ContinuousLinearEquiv.toLinearEquiv_symm]
  refine (LinearEquiv.isComplexLinearMap_transport_symm_iff
    (Manifold.tangentSpaceProdEquiv (fold v z)).toLinearEquiv).trans ?_
  exact isComplexLinearMap_of_apply_eq_smul_iff
    (tangentSpaceProdEquiv_mfderiv_fold_apply hv₁ hv₂)

/-- **The fold of a holomorphic cylinder is a holomorphic strip, and conversely.** Let
`J_{(s, t)}` be a family of almost complex structures on the tangent spaces of `M`, parametrized by
the points of the domain, and let `v` be differentiable on `ℝ × [-1/2, 1/2]`. The fold of `v`
solves the Cauchy–Riemann equation on the strip `ℝ × [0, 1]` for the folded structures
`J_{(s/2, t/2)} ⊕ (-J_{(s/2, -t/2)})` exactly when `v` solves the Cauchy–Riemann equation
`∂_s v + J_{(s, t)} ∂_t v = 0` on `ℝ × [-1/2, 1/2]`. -/
theorem forall_isComplexLinearMap_mfderiv_fold_iff
    (J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x))
    (hv : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z) :
    (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (((J (z.1 / 2, z.2 / 2) (fold v z).1).prod (-J (z.1 / 2, -z.2 / 2) (fold v z).2)).transport
          (Manifold.tangentSpaceProdEquiv (fold v z)).symm.toLinearEquiv)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) (I.prod I) (fold v) z).toLinearMap) ↔
      ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2),
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I v z).toLinearMap := by
  constructor
  · intro h z hz
    simp only [mem_prod, mem_univ, mem_Icc, true_and] at hz
    rcases le_total 0 z.2 with ht | ht
    · -- The upper half of the period is the first component of the fold at `(2 s, 2 t)`.
      have hz' : (2 * z.1, 2 * z.2) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 := by
        simp only [mem_prod, mem_univ, mem_Icc, true_and]
        constructor <;> linarith [hz.1, hz.2]
      have hp : ((2 * z.1) / 2, (2 * z.2) / 2) = z := by ext <;> simp
      exact hp ▸
        ((isComplexLinearMap_mfderiv_fold_iff (hv _ (upper_mem_period hz'))
          (hv _ (lower_mem_period hz')) _ _).1 (h _ hz')).1
    · -- The lower half is the second component of the fold at `(2 s, -2 t)`.
      have hz' : (2 * z.1, -(2 * z.2)) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 := by
        simp only [mem_prod, mem_univ, mem_Icc, true_and]
        constructor <;> linarith [hz.1, hz.2]
      have hp : ((2 * z.1) / 2, -(-(2 * z.2)) / 2) = z := by ext <;> simp
      exact hp ▸
        ((isComplexLinearMap_mfderiv_fold_iff (hv _ (upper_mem_period hz'))
          (hv _ (lower_mem_period hz')) _ _).1 (h _ hz')).2
  · intro h z hz
    exact (isComplexLinearMap_mfderiv_fold_iff (hv _ (upper_mem_period hz))
      (hv _ (lower_mem_period hz)) _ _).2 ⟨h _ (upper_mem_period hz), h _ (lower_mem_period hz)⟩

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {v : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- **The energy density of the fold.** For the twisted product form `pr₁^* σ - pr₂^* σ` on
`M × M`, the symplectic area density of the fold of `v` at `(s, t)` is a quarter of the sum of
the area densities of `v` at `(s / 2, t / 2)` and at `(s / 2, -t / 2)`: the reflection of the
second half reverses the orientation, and the second factor carries `-σ`. -/
theorem floerEnergyDensity_twistedProd_fold (σ : SmoothTwoForm I M)
    (hv₁ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, z.2 / 2))
    (hv₂ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2)) :
    (twistedProd σ σ).floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fold v) z =
      (σ.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) v (z.1 / 2, z.2 / 2) +
        σ.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) v (z.1 / 2, -z.2 / 2)) / 4 := by
  rw [floerEnergyDensity_zero, floerEnergyDensity_zero, floerEnergyDensity_zero, eval₂_twistedProd,
    tangentSpaceProdEquiv_mfderiv_fold_apply hv₁ hv₂,
    tangentSpaceProdEquiv_mfderiv_fold_apply hv₁ hv₂]
  rw [fold_apply]
  simp only [reflect_stdComplexLineImag, reflect_stdComplexLineReal,
    SmoothBundleForm.eval₂_smul_left, SmoothBundleForm.eval₂_smul_right, smul_eq_mul]
  -- The reflected vector `-stdComplexLineImag` is negated in `ℝ × ℝ`; `map_neg` for the linear
  -- derivative is stated with that negation, so that a plain rewrite applies it.
  have hneg : mfderiv 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2) (-stdComplexLineImag : ℝ × ℝ) =
      -mfderiv 𝓘(ℝ, ℝ × ℝ) I v (z.1 / 2, -z.2 / 2) stdComplexLineImag :=
    map_neg _ _
  rw [hneg, SmoothBundleForm.eval₂_neg_right]
  ring

/-- **Folding preserves the energy.** If `v` is differentiable on one period `ℝ × [-1/2, 1/2]`
of the cylinder and its symplectic area density is integrable there, then the energy of its fold
on the strip `ℝ × [0, 1]`, for the twisted product form `pr₁^* σ - pr₂^* σ`, is the energy of `v`
on `ℝ × [-1/2, 1/2]`. -/
theorem integral_floerEnergyDensity_twistedProd_fold (σ : SmoothTwoForm I M)
    (hv : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z)
    (hint : IntegrableOn (σ.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) v)
      ((univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2))) :
    ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        (twistedProd σ σ).floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fold v) z =
      ∫ z in (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2),
        σ.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) v z := by
  set ρ := σ.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) v
  set S : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Icc 0 1
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  -- The two halves of the fold are linear reparametrizations with Jacobian `± 1/4`, which carry
  -- the strip onto the upper and the lower half of the period.
  have hfU (w : ℝ × ℝ) (_ : w ∈ S) :
      (1 / 4 : ℝ) * ρ (foldUpper w) = |(fderiv ℝ foldUpper w).det| • ρ (foldUpper w) := by
    rw [abs_det_fderiv_foldUpper, smul_eq_mul]
  have hfL (w : ℝ × ℝ) (_ : w ∈ S) :
      (1 / 4 : ℝ) * ρ (foldLower w) = |(fderiv ℝ foldLower w).det| • ρ (foldLower w) := by
    rw [abs_det_fderiv_foldLower, smul_eq_mul]
  have hρU : IntegrableOn ρ (foldUpper '' S) := hint.mono_set <| by
    rw [image_foldUpper]
    exact prod_mono subset_rfl (Icc_subset_Icc (by norm_num) le_rfl)
  have hρL : IntegrableOn ρ (foldLower '' S) := hint.mono_set <| by
    rw [image_foldLower]
    exact prod_mono subset_rfl (Icc_subset_Icc le_rfl (by norm_num))
  -- The two halves of the period meet only along the null line `t = 0`.
  have hdisj : AEDisjoint volume ((univ : Set ℝ) ×ˢ Icc (-(1 / 2) : ℝ) 0)
      ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) (1 / 2)) := by
    have h₀ : Icc (-(1 / 2) : ℝ) 0 ∩ Icc 0 (1 / 2) ⊆ {0} := fun x hx ↦ le_antisymm hx.1.2 hx.2.1
    rw [AEDisjoint, prod_inter_prod, univ_inter]
    refine measure_mono_null (prod_mono subset_rfl h₀) ?_
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  calc ∫ w in S, (twistedProd σ σ).floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fold v) w
      = ∫ w in S, ((1 / 4 : ℝ) * ρ (foldUpper w) + (1 / 4 : ℝ) * ρ (foldLower w)) :=
        setIntegral_congr_fun hS fun w hw ↦ by
          rw [floerEnergyDensity_twistedProd_fold σ (hv _ (upper_mem_period hw))
            (hv _ (lower_mem_period hw)), foldUpper_apply, foldLower_apply]
          ring
    _ = (∫ w in foldUpper '' S, ρ w) + ∫ w in foldLower '' S, ρ w := by
        rw [integral_add
          ((integrableOn_image_iff_of_eq_abs_det_smul hS injective_foldUpper.injOn
            (fun w _ ↦ foldUpper.differentiableAt) hfU).1 hρU)
          ((integrableOn_image_iff_of_eq_abs_det_smul hS injective_foldLower.injOn
            (fun w _ ↦ foldLower.differentiableAt) hfL).1 hρL),
          integral_image_eq_integral_of_eq_abs_det_smul hS injective_foldUpper.injOn
            (fun w _ ↦ foldUpper.differentiableAt) hfU,
          integral_image_eq_integral_of_eq_abs_det_smul hS injective_foldLower.injOn
            (fun w _ ↦ foldLower.differentiableAt) hfL]
    _ = ∫ w in (univ : Set ℝ) ×ˢ Icc (-(1 / 2)) (1 / 2), ρ w := by
        rw [image_foldUpper, image_foldLower, add_comm, ← setIntegral_union₀ hdisj
            (MeasurableSet.univ.prod measurableSet_Icc).nullMeasurableSet
            (image_foldLower ▸ hρL) (image_foldUpper ▸ hρU),
          ← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

end TauCeti.SmoothTwoForm
