/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Wedge

/-!
# The Leibniz rule for wedge products of differential forms

For fixed-coefficient forms `φ` of degree `k` and `ψ`, and a fixed continuous bilinear pairing
`μ` of their coefficient spaces, the manifold exterior derivative satisfies

`d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ`.

The coordinate expression of a paired wedge in a chart is the paired wedge of the coordinate
expressions, so the rule follows from the flat Leibniz rule `TauCeti.extDerivWithin_pairedWedge`.
The within-set statement only needs differentiability of both forms at the point and unique
derivatives there, so it applies at boundary and corner points. The degrees `k + 1 + l` and
`k + (l + 1)` of the two terms are identified with `k + l + 1` by `Fin.cast`. The real wedge
`TauCeti.RoughForm.wedge` is the specialization to multiplication.

With this rule the wedge product descends to closed and exact forms, which is what makes de Rham
cohomology a ring.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.23.
-/

public section

noncomputable section

open Set Bundle ContinuousAlternatingMap
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ} {s : Set M} {x : M}

namespace RoughForm

/-- The coordinate expression of a paired wedge is the paired wedge of the coordinate
expressions. -/
@[simp]
theorem inChartAt_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (φ : RoughForm I M F₁ k)
    (ψ : RoughForm I M F₂ l) (x₀ : M) (z : E) :
    (φ.wedgeWith μ ψ).inChartAt x₀ z =
      pairedWedge μ μ.continuous₂ (φ.inChartAt x₀ z) (ψ.inChartAt x₀ z) := by
  ext w
  simp only [inChartAt_apply, wedgeWith_apply, pairedWedge_apply]

end RoughForm

variable [IsManifold I 1 M]

/-- The Leibniz rule for the exterior derivative of a paired wedge within a set:
`d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ` for a `k`-form `φ` and a fixed continuous bilinear
pairing `μ`, at a point of unique differentiability where both forms are differentiable. -/
theorem mextDerivWithin_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {φ : RoughForm I M F₁ k}
    {ψ : RoughForm I M F₂ l}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s x)
    (hψ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s x)
    (hs : UniqueMDiffWithinAt I s x) (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDerivWithin (φ.wedgeWith μ ψ) s x v =
      RoughForm.wedgeWith μ (mextDerivWithin φ s) ψ x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • φ.wedgeWith μ (mextDerivWithin ψ s) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  have hchart : (φ.wedgeWith μ ψ).inChartAt x =
      fun z ↦ pairedWedge μ μ.continuous₂ (φ.inChartAt x z) (ψ.inChartAt x z) :=
    funext (RoughForm.inChartAt_wedgeWith μ φ ψ x)
  rw [mextDerivWithin_def, hchart]
  refine (extDerivWithin_pairedWedge μ hs (φ.differentiableWithinAt_inChartAt hφ)
    (ψ.differentiableWithinAt_inChartAt hψ) v).trans ?_
  rw [RoughForm.wedgeWith_apply', RoughForm.wedgeWith_apply', RoughForm.inChartAt_extChartAt_self,
    RoughForm.inChartAt_extChartAt_self, mextDerivWithin_def, mextDerivWithin_def]
  -- The two sides differ only in reading tangent vectors at `x` as vectors of the model space.
  rfl

/-- The Leibniz rule for the exterior derivative of a paired wedge:
`d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ` for a `k`-form `φ` and a fixed continuous bilinear
pairing `μ`, at a point where both forms are differentiable. -/
theorem mextDeriv_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {φ : RoughForm I M F₁ k}
    {ψ : RoughForm I M F₂ l}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) x)
    (hψ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) x)
    (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDeriv (φ.wedgeWith μ ψ) x v =
      RoughForm.wedgeWith μ (mextDeriv φ) ψ x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • φ.wedgeWith μ (mextDeriv ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  simpa only [mextDerivWithin_univ] using
    mextDerivWithin_wedgeWith μ hφ.mdifferentiableWithinAt hψ.mdifferentiableWithinAt
      (uniqueMDiffWithinAt_univ I) v

/-- The Leibniz rule for the exterior derivative of the real wedge within a set:
`d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ` for a real `k`-form `φ`. -/
theorem mextDerivWithin_wedge {φ : RoughForm I M ℝ k} {ψ : RoughForm I M ℝ l}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (φ y)) s x)
    (hψ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ) y (ψ y)) s x)
    (hs : UniqueMDiffWithinAt I s x) (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDerivWithin (φ.wedge ψ) s x v =
      RoughForm.wedge (mextDerivWithin φ s) ψ x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • φ.wedge (mextDerivWithin ψ s) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  simpa only [RoughForm.wedge_def] using
    mextDerivWithin_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) hφ hψ hs v

/-- The Leibniz rule for the exterior derivative of the real wedge:
`d (φ ∧ ψ) = dφ ∧ ψ + (-1) ^ k • φ ∧ dψ` for a real `k`-form `φ`. -/
theorem mextDeriv_wedge {φ : RoughForm I M ℝ k} {ψ : RoughForm I M ℝ l}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (φ y)) x)
    (hψ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ) y (ψ y)) x)
    (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDeriv (φ.wedge ψ) x v =
      RoughForm.wedge (mextDeriv φ) ψ x (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • φ.wedge (mextDeriv ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  simpa only [RoughForm.wedge_def] using
    mextDeriv_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) hφ hψ v

omit [IsManifold I 1 M] in
/-- Forms of propositionally equal degrees which agree after reindexing their arguments have
exterior derivatives which agree after the same reindexing. This transports the wedge `f ∧ φ`,
of degree `0 + l`, to the pointwise product `f φ`, of degree `l`. -/
private theorem mextDeriv_apply_eq_of_degree_eq {a b : ℕ} (h : a = b) {φ : RoughForm I M ℝ a}
    {ψ : RoughForm I M ℝ b} (hφψ : ∀ y u, φ y u = ψ y (u ∘ Fin.cast h.symm))
    (v : Fin (a + 1) → TangentSpace I x) :
    mextDeriv φ x v = mextDeriv ψ x (v ∘ Fin.cast (congrArg (· + 1) h).symm) := by
  subst h
  have hφψ' : φ = ψ := funext fun y ↦ ContinuousAlternatingMap.ext fun u ↦ by
    rw [hφψ, Fin.cast_refl, Function.comp_id]
  rw [hφψ', Fin.cast_refl, Function.comp_id]

/-- The Leibniz rule for a function times a form: `d (f φ) = df ∧ φ + f dφ`, at a point where
`f` and `φ` are differentiable. The degree `0 + 1 + l` of `df ∧ φ` is identified with
`l + 1` by `Fin.cast`. -/
theorem mextDeriv_fun_smul {f : M → ℝ} {φ : RoughForm I M ℝ l}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ) y (φ y)) x)
    (v : Fin (l + 1) → TangentSpace I x) :
    mextDeriv (fun y ↦ f y • φ y) x v =
      (mextDeriv (RoughForm.ofFunction I f)).wedge φ x
          (v ∘ Fin.cast (show 0 + 1 + l = l + 1 by omega)) +
        f x * mextDeriv φ x v := by
  have hf' := mdifferentiableAt_ofFunction hf
  -- `f φ` is the wedge `f ∧ φ`, read in degree `l` instead of `0 + l`.
  have hsmul : ∀ y (u : Fin l → TangentSpace I y), (f y • φ y) u =
      (RoughForm.ofFunction I f).wedge φ y (u ∘ Fin.cast (zero_add l)) := by
    intro y u
    rw [RoughForm.ofFunction_wedge_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [mextDeriv_apply_eq_of_degree_eq (zero_add l).symm hsmul, mextDeriv_wedge hf' hφ, pow_zero,
    one_smul, RoughForm.ofFunction_wedge_apply]
  simp only [Function.comp_def, Fin.cast_cast, Fin.cast_eq_self]

/-- The Leibniz rule for a function times a one-form: `d (f α) = df ∧ α + f dα`, evaluated on a
pair of tangent vectors, at a point where `f` and `α` are differentiable. -/
theorem mextDeriv_fun_smul_apply {f : M → ℝ} {α : RoughForm I M ℝ 1}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (v w : TangentSpace I x) :
    mextDeriv (fun y ↦ f y • α y) x ![v, w] =
      mvfderiv I f x v * α x ![w] - mvfderiv I f x w * α x ![v] +
        f x * mextDeriv α x ![v, w] := by
  have hvw : ∀ h : 0 + 1 + 1 = 1 + 1, (![v, w] ∘ Fin.cast h : Fin 2 → TangentSpace I x) =
      ![v, w] := fun _ ↦ funext fun i ↦ by fin_cases i <;> rfl
  rw [mextDeriv_fun_smul hf hα, hvw, RoughForm.wedge_apply_one_one, mextDeriv_ofFunction]
  simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_fin_one]

namespace SmoothForm

/-! ### Smooth-form interface -/

/-- The exterior derivative of a paired wedge of smooth forms, evaluated on tangent vectors. -/
theorem mextDeriv_wedgeWith_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) (x : M)
    (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDeriv (RoughForm.wedgeWith μ φ.1 ψ.1) x v =
      RoughForm.wedgeWith μ (mextDeriv φ.1) ψ.1 x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • RoughForm.wedgeWith μ φ.1 (mextDeriv ψ.1) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  exact TauCeti.mextDeriv_wedgeWith μ (φ.mdifferentiableAt x) (ψ.mdifferentiableAt x) v

/-- The exterior derivative of the real wedge `RoughForm.wedge` of the underlying forms of two
smooth forms, evaluated on tangent vectors. See `SmoothForm.mextDerivₗ_wedge` for the bundled
law. -/
theorem mextDeriv_wedge_apply (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) (x : M)
    (v : Fin (k + l + 1) → TangentSpace I x) :
    mextDeriv (RoughForm.wedge φ.1 ψ.1) x v =
      RoughForm.wedge (mextDeriv φ.1) ψ.1 x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • RoughForm.wedge φ.1 (mextDeriv ψ.1) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  simpa only [RoughForm.wedge_def] using
    mextDeriv_wedgeWith_apply (ContinuousLinearMap.mul ℝ ℝ) φ ψ x v

/-- The bundled exterior derivative of a paired wedge of smooth forms. The two terms on the
right are transported across the degree associativity equalities. -/
theorem mextDerivₗ_wedgeWith [IsManifold I 2 M] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    mextDerivₗ I (k + l) (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F₃ q)
        (show k + 1 + l = k + l + 1 by omega)
        (SmoothForm.wedgeWith μ (mextDerivₗ I k φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F₃ q)
        (show k + (l + 1) = k + l + 1 by omega)
        (SmoothForm.wedgeWith μ φ (mextDerivₗ I l ψ)) := by
  apply Subtype.ext
  ext x v
  simpa only [mextDerivₗ_apply, SmoothForm.coe_wedgeWith, Submodule.coe_add,
    Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.cast_apply] using
    mextDeriv_wedgeWith_apply μ φ ψ x v

/-- The bundled exterior derivative of the real wedge of smooth forms. -/
theorem mextDerivₗ_wedge [IsManifold I 2 M] (φ : SmoothForm I M ℝ k)
    (ψ : SmoothForm I M ℝ l) :
    mextDerivₗ I (k + l) (SmoothForm.wedge φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
        (show k + 1 + l = k + l + 1 by omega)
        (SmoothForm.wedge (mextDerivₗ I k φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
        (show k + (l + 1) = k + l + 1 by omega)
        (SmoothForm.wedge φ (mextDerivₗ I l ψ)) := by
  simpa only [SmoothForm.wedge_def] using
    mextDerivₗ_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) φ ψ

end SmoothForm

end TauCeti
