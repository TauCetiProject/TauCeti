/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Gauge
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Regular

/-!
# Uniqueness of action–angle coordinates on a saturated neighbourhood

Let `σ` be a nondegenerate two-form on a boundaryless Hausdorff manifold `M`, let `F : M → ℝ^ι` be
an integrable system for `σ`, and let `U ⊆ ℝ^ι` be an open set of regular values of `F` with
connected fibres, over which `F` is proper. The open set `F⁻¹(U)` is then a saturated neighbourhood
of each of its fibres, and `F` restricts to a regular Lagrangian torus fibration `F⁻¹(U) → U`
(`TauCeti.SmoothTwoForm.IsIntegrableSystem.isLagrangianTorusFibration_restrictPreimage`).

Action–angle coordinates on `F⁻¹(U)` with period `p` are maps `Φ : M → T*(ι → ℝ/pℤ)` which, on
`F⁻¹(U)`, are injective local diffeomorphisms pulling the canonical form back to `σ`, and whose
actions are a function `a ∘ F` of the integrals. This is the form of the local action–angle
coordinates near a compact regular component of a level
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`), restricted to a saturated
neighbourhood inside their domain. This file proves that such coordinates are unique up to the
two expected ambiguities. If `Φ` and `Φ'` are action–angle coordinates on `F⁻¹(U)` with actions
`a ∘ F` and `a' ∘ F`, and the set of actions `a'(U)` is star-convex, for instance a ball, then there
are `P ∈ GL(ι, ℤ)`, `b₀ : ι → ℝ` and a smooth function `S` on `a'(U)` such that `a' = P a + b₀` on
`U` and, at every point `y ∈ F⁻¹(U)` with coordinates `Φ y = κ(θ, a(F y))`,

`Φ' y = κ(θ P⁻¹ + ∇S(a'(F y)), a'(F y))`

(`exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle`, in the namespace
`TauCeti.SmoothTwoForm.IsIntegrableSystem`). In action–angle coordinates this is the change
`(θ, I) ↦ (P⁻ᵀ θ + ∇S(I'), P I + b₀)`: an integral affine change of the actions followed by the
angle gauge of a function of the actions. No section of `F` is chosen, and the two coordinate
systems need not come from the same section.

The proof restricts both coordinate systems to the open submanifold `F⁻¹(U)`, where they become
global action–angle coordinates of the regular Lagrangian torus fibration `F⁻¹(U) → U`, and
applies the uniqueness of global action–angle coordinates over a ball of actions
(`exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`).

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsIntegrableSystem`:

* `exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle`: two systems of
  action–angle coordinates on a saturated neighbourhood over a ball of actions differ by an
  integral affine change of the actions and the gradient of a function of the actions.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the ambiguity of action-angle coordinates).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsIntegrableSystem

open CotangentBundle Matrix

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] {F : M → ι → ℝ}
  (p : ℝ) [Fact (0 < p)]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
/-- Action–angle coordinates on the open set `V ⊆ M`, given pointwise on `V`, restrict to the open
submanifold `V` as a local diffeomorphism pulling the canonical form back to the restriction of
`σ`. -/
private theorem mpullback_comp_subtype_val_symplecticForm {V : Opens M}
    {Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
    (hΦ : ∀ y ∈ V, IsLocalDiffeomorphAt I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y)
    (hΦσ : ∀ y ∈ V, ∀ v w : TangentSpace I y,
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) (Φ y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y w) =
        SmoothBundleForm.eval₂ σ y v w) :
    ∃ hΦV : IsLocalDiffeomorph I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
        (Φ ∘ (Subtype.val : V → M)),
      SmoothForm.mpullback (Φ ∘ (Subtype.val : V → M)) hΦV.contMDiff
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) =
        SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ := by
  have hΦV : IsLocalDiffeomorph I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (Φ ∘ (Subtype.val : V → M)) := fun x ↦
    IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_subtype_val x) (hg := hΦ x x.property)
  refine ⟨hΦV, SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_⟩
  -- Restricting to the open submanifold `V` changes neither the differential of `Φ` nor the
  -- tangent vectors at which `σ` is evaluated.
  rw [SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback,
    Manifold.mfderiv_comp_subtype_val_apply, Manifold.mfderiv_comp_subtype_val_apply,
    Manifold.mfderiv_subtype_val_apply, Manifold.mfderiv_subtype_val_apply]
  exact hΦσ x x.property v w

/-- **Uniqueness of action–angle coordinates on a saturated neighbourhood.** Let `F` be an
integrable system for a nondegenerate form `σ`, and let `U` be an open set of regular values of `F`
with connected fibres, over which `F` is proper. Let `Φ` and `Φ'` be action–angle coordinates with
period `p` on `F⁻¹(U)`: on `F⁻¹(U)` they are injective local diffeomorphisms into `T*(ι → ℝ/pℤ)`
pulling the canonical form back to `σ`, with actions `a ∘ F` and `a' ∘ F`. If the set of actions
`a'(U)` is star-convex, for instance a ball, then there are `P ∈ GL(ι, ℤ)`, `b₀ : ι → ℝ` and a
function `S`, smooth on `a'(U)`, such that `a' = P a + b₀` on `U` and, at every point `y ∈ F⁻¹(U)`
with coordinates `Φ y = κ(θ, a(F y))`,

`Φ' y = κ(θ P⁻¹ + ∇S(a'(F y)), a'(F y))`,

that is, `(θ, I) ↦ (P⁻ᵀ θ + ∇S(I'), P I + b₀)` in action–angle coordinates, where
`∇S(c) = (∂S/∂cᵢ)ᵢ`. -/
theorem exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle [DecidableEq ι]
    (h : σ.IsIntegrableSystem F) (hσ : σ.IsNondegenerate) (U : Opens (ι → ℝ))
    (hreg : ∀ c ∈ U, IsRegularValue I 𝓘(ℝ, ι → ℝ) F c)
    (hconn : ∀ c ∈ U, IsConnected (F ⁻¹' {c}))
    (hprop : IsProperMap ((U : Set (ι → ℝ)).restrictPreimage F))
    {a a' : (ι → ℝ) → ι → ℝ}
    {Φ Φ' : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
    (hΦ : ∀ y ∈ F ⁻¹' U, IsLocalDiffeomorphAt I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y)
    (hΦσ : ∀ y ∈ F ⁻¹' U, ∀ v w : TangentSpace I y,
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) (Φ y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y w) =
        SmoothBundleForm.eval₂ σ y v w)
    (hΦa : ∀ y ∈ F ⁻¹' U, torusActions p (Φ y) = a (F y)) (hΦi : InjOn Φ (F ⁻¹' U))
    (hΦ' : ∀ y ∈ F ⁻¹' U, IsLocalDiffeomorphAt I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ' y)
    (hΦ'σ : ∀ y ∈ F ⁻¹' U, ∀ v w : TangentSpace I y,
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) (Φ' y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ' y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ' y w) =
        SmoothBundleForm.eval₂ σ y v w)
    (hΦ'a : ∀ y ∈ F ⁻¹' U, torusActions p (Φ' y) = a' (F y)) (hΦ'i : InjOn Φ' (F ⁻¹' U))
    {c₀ : ι → ℝ} (hst : StarConvex ℝ c₀ (a' '' U)) :
    ∃ (P : GL ι ℤ) (b₀ : ι → ℝ) (S : (ι → ℝ) → ℝ),
      (∀ c ∈ U, a' c = (P : Matrix ι ι ℤ).map (↑) *ᵥ a c + b₀) ∧
      ContDiffOn ℝ ∞ S (a' '' U) ∧
      ∀ y ∈ F ⁻¹' U, ∀ θ, Φ y = actionAngleCover p (θ, a (F y)) →
        Φ' y = actionAngleCover p
          (θ ᵥ* ((P⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map (↑) +
            (fun i ↦ fderiv ℝ S (a' (F y)) (Pi.single i 1)), a' (F y)) := by
  -- Restrict everything to the open submanifold `V = F⁻¹(U)`, fibred over `U` by `F`.
  set V : Opens M := U.comap ⟨F, h.contMDiff.continuous⟩
  have hfib := h.isLagrangianTorusFibration_restrictPreimage hσ U hreg hconn hprop
  obtain ⟨hΦV, hΦVσ⟩ := mpullback_comp_subtype_val_symplecticForm (V := V) p hΦ hΦσ
  obtain ⟨hΦ'V, hΦ'Vσ⟩ := mpullback_comp_subtype_val_symplecticForm (V := V) p hΦ' hΦ'σ
  have hrange : range (fun c : U ↦ a' c) = a' '' U := by
    ext
    simp
  obtain ⟨P, b₀, S, hP, hS, hΦ'x⟩ :=
    hfib.exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle p
      (a := fun c : U ↦ a c) (a' := fun c : U ↦ a' c) hΦV hΦVσ (fun y ↦ hΦa y y.property)
      hΦ'V hΦ'Vσ (fun y ↦ hΦ'a y y.property) (hrange ▸ hst)
      hΦi.injective hΦ'i.injective
  exact ⟨P, b₀, S, fun c hc ↦ hP ⟨c, hc⟩, hrange ▸ hS, fun y hy θ hθ ↦ hΦ'x ⟨y, hy⟩ θ hθ⟩

end TauCeti.SmoothTwoForm.IsIntegrableSystem
