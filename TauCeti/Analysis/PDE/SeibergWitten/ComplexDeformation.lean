/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ASDDeformation
public import TauCeti.Geometry.Manifold.Riemannian.AlmostComplex
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.AlmostComplexType

/-!
# The complex-linear Seiberg–Witten deformation operator and principal-symbol homotopy

On an oriented Riemannian four-manifold `(M, g, o)` equipped with a smooth almost complex structure
`J` compatible with the metric and orientation
(`TauCeti.SmoothAlmostComplexStructure.IsCompatibleOrientation`), Taubes's Gromov–Seiberg–Witten
theory compares the Atiyah–Hitchin–Singer deformation operator `δ₀(a) = (-d*a, √2 (da)⁺)`
(`TauCeti.SeibergWitten.asdDeformationOperator`) with its complex-linear part

`δ_ω = (δ₀ - J′ ∘ δ₀ ∘ J₁) / 2`

(`TauCeti.SeibergWitten.complexDeformationOperator`). Here `J₁` acts on smooth one-forms by
`(J₁ a)_x(v) = -a_x(J_x v)` (`TauCeti.SmoothAlmostComplexStructure.covectorComplexStructure`), which
intertwines with `J_x` on `T_x M` under the Riesz isomorphism, and `J′` acts on `Ω⁰(M) × Ω⁺(M)` by

`J′(g, η) = (-(√2 / 2) ⟨ω, η⟩, (√2 / 2) ω ∧ g - (1 / 2) D_J η)`

(`TauCeti.SeibergWitten.deformationTargetComplexStructure`), matching the pointwise target complex
structure `TauCeti.SeibergWitten.deformationSelfDualComplexStructure` on every fibre.

Because the principal symbol of `δ₀` is already `(J, J′)`-complex-linear at every point
(`TauCeti.SeibergWitten.deformationSymbol_comp_toLinearMap`), taking the complex-linear part leaves
the principal symbol unchanged: `δ_ω - δ₀` commutes with multiplication by smooth functions
(`TauCeti.SeibergWitten.complexDeformationOperator_sub_asdDeformationOperator_wedge`), so it is a
bundle map of order zero, and every operator along the linear homotopy
`δ_t = (1 - t) δ₀ + t δ_ω` (`TauCeti.SeibergWitten.deformationHomotopy`) has the exact same
elliptic principal symbol as `δ₀`
(`TauCeti.SeibergWitten.deformationHomotopy_commutator_eq`,
`TauCeti.SeibergWitten.deformationHomotopy_commutator_eq_deformationSymbol`).

## Main definitions

* `TauCeti.SeibergWitten.deformationTargetComplexStructure`: the global almost complex structure
  `J′` on `Ω⁰(M) × Ω⁺(M)`.
* `TauCeti.SeibergWitten.complexDeformationOperator`: Taubes's complex-linear operator
  `δ_ω = complexLinearPart J₁ J′ δ₀`.
* `TauCeti.SeibergWitten.deformationHomotopy`: the linear family `δ_t = (1 - t) δ₀ + t δ_ω`.

## Main results

* `TauCeti.SeibergWitten.deformationTargetComplexStructure_apply_fst`,
  `TauCeti.SeibergWitten.coe_deformationTargetComplexStructure_apply_snd`, and
  `TauCeti.SeibergWitten.deformationTargetComplexStructure_apply_eq`: global component formulas and
  fibrewise identification of `J′` with `deformationComplexStructure`.
* `TauCeti.SeibergWitten.isComplexLinearMap_complexDeformationOperator`: `δ_ω` is `(J₁, J′)`-complex
  linear.
* `TauCeti.SeibergWitten.complexDeformationOperator_sub_asdDeformationOperator_wedge`: `δ_ω - δ₀` is
  `C^∞(M)`-linear (an operator of order zero).
* `TauCeti.SeibergWitten.deformationHomotopy_commutator_eq` and
  `TauCeti.SeibergWitten.deformationHomotopy_commutator_eq_deformationSymbol`: `[δ_t, · ∧ f] =
  [δ₀, · ∧ f]` evaluates fibrewise to `deformationSymbol` for all `t : ℝ`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*, J. Amer.
  Math. Soc. 9 (1996), 845–918, §1–2; reprinted in *Seiberg Witten and Gromov Invariants for
  Symplectic 4-Manifolds*, International Press, 2000.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* D. Salamon, *Spin Geometry and Seiberg–Witten Invariants*, Birkhäuser, 1999, §7.4, §12.1.
-/

public section

noncomputable section

open Bundle Module Real Set exteriorPower
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace TauCeti.SeibergWitten

section PrivateHelpers

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Pointwise evaluation `g ↦ g(x)` of a smooth zero-form as a linear map. -/
private def zeroFormEval (x : M) : SmoothForm I M ℝ 0 →ₗ[ℝ] ℝ where
  toFun g := g.1 x 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
private theorem zeroFormEval_apply (x : M) (g : SmoothForm I M ℝ 0) :
    zeroFormEval x g = g.1 x 0 :=
  (rfl)

section TwoFormBivectorEval

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Fibrewise bivector evaluation `η ↦ (alternatingFormEquiv (T_x M) 2).symm η_x` of a smooth
two-form as a linear map. -/
private def twoFormBivectorEval (x : M) [FiniteDimensional ℝ (TangentSpace I x)] :
    SmoothForm I M ℝ 2 →ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace I x) where
  toFun η := (alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
private theorem twoFormBivectorEval_apply (x : M) [FiniteDimensional ℝ (TangentSpace I x)]
    (η : SmoothForm I M ℝ 2) :
    twoFormBivectorEval x η = (alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x) :=
  (rfl)

section TargetEval

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Fibrewise evaluation `(g, η) ↦ (g(x), (alternatingFormEquiv (T_x M) 2).symm η_x)` on
`Ω⁰(M) × Ω⁺(M)`, bundled as a linear map. -/
private def deformationTargetEval (o : Manifold.Orientation I M (Fin (2 + 2))) (x : M) :
    letI := o.fact_finrank_tangentSpace x
    haveI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o →ₗ[ℝ]
      ℝ × ⋀[ℝ]^2 (TangentSpace I x) :=
  letI := o.fact_finrank_tangentSpace x
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  (zeroFormEval x).prodMap (twoFormBivectorEval x ∘ₗ (SmoothForm.selfDualForms o).subtype)

@[simp]
private theorem deformationTargetEval_apply (o : Manifold.Orientation I M (Fin (2 + 2))) (x : M)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (letI := o.fact_finrank_tangentSpace x
     haveI : FiniteDimensional ℝ (TangentSpace I x) :=
       VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     deformationTargetEval o x p) =
      (letI := o.fact_finrank_tangentSpace x
       haveI : FiniteDimensional ℝ (TangentSpace I x) :=
         VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       (p.1.1 x 0,
         (alternatingFormEquiv (TangentSpace I x) 2).symm ((p.2 : SmoothForm I M ℝ 2).1 x))) :=
  (rfl)

/-- Fibrewise extensionality for elements of `Ω⁰(M) × Ω⁺(M)` read via `deformationTargetEval`. -/
private theorem ext_deformationTarget (o : Manifold.Orientation I M (Fin (2 + 2)))
    {p q : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o}
    (h : ∀ x : M, deformationTargetEval o x p = deformationTargetEval o x q) :
    p = q := by
  refine Prod.ext (Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun u ↦ ?_)
    (Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_)
  · rw [Subsingleton.elim u 0]
    exact (Prod.mk.inj (h x)).1
  · let _ := o.fact_finrank_tangentSpace x
    have _ : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    exact (alternatingFormEquiv (TangentSpace I x) 2).symm.injective (Prod.mk.inj (h x)).2

end TargetEval

end TwoFormBivectorEval

end PrivateHelpers

/-! ### Target almost complex structure on `Ω⁰(M) × Ω⁺(M)` -/

section Target

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- The ambient smooth-form linear map underlying `deformationTargetComplexStructure` on
`Ω⁰(M) × Ω²(M)`. -/
private def deformationTargetAmbientMap (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) :
    SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2 →ₗ[ℝ]
      SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2 :=
  ((-((√2 / 2 : ℝ) • SmoothForm.innerZeroForm (k := 2) (l := 2) o (J.kahlerTwoForm hJ))) ∘ₗ
      LinearMap.snd ℝ (SmoothForm I M ℝ 0) (SmoothForm I M ℝ 2)).prod
    (((√2 / 2 : ℝ) • SmoothForm.wedge (J.kahlerTwoForm hJ)) ∘ₗ
        LinearMap.fst ℝ (SmoothForm I M ℝ 0) (SmoothForm I M ℝ 2) -
      ((2⁻¹ : ℝ) • J.toEndomorphism.realAlternatingDerivation (k := 2)) ∘ₗ
        LinearMap.snd ℝ (SmoothForm I M ℝ 0) (SmoothForm I M ℝ 2))

private theorem deformationTargetAmbientMap_fst (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (p : SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2) :
    (deformationTargetAmbientMap o J hJ p).1 =
      -((√2 / 2 : ℝ) • SmoothForm.innerZeroForm (k := 2) (l := 2) o (J.kahlerTwoForm hJ) p.2) :=
  (rfl)

private theorem deformationTargetAmbientMap_snd (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (p : SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2) :
    (deformationTargetAmbientMap o J hJ p).2 =
      (√2 / 2 : ℝ) • SmoothForm.wedge (J.kahlerTwoForm hJ) p.1 -
        (2⁻¹ : ℝ) • J.toEndomorphism.realAlternatingDerivation p.2 :=
  (rfl)

private theorem deformationTargetAmbientMap_apply_eq {J : SmoothAlmostComplexStructure I M}
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (p : SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     ((deformationTargetAmbientMap o J hJ p).1.1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         ((deformationTargetAmbientMap o J hJ p).2.1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationComplexStructure (J.almostComplexStructureAt x)
         (p.1.1 x 0, (alternatingFormEquiv (TangentSpace I x) 2).symm (p.2.1 x))) := by
  let _ := o.fact_finrank_tangentSpace x
  refine Prod.ext ?_ ?_
  · rw [← zeroFormEval_apply, deformationTargetAmbientMap_fst, map_neg, map_smul]
    simp [alternatingFormInner_apply]
  · have hsnd : (deformationTargetAmbientMap o J hJ p).2 =
        (√2 / 2 : ℝ) • SmoothForm.wedge (J.kahlerTwoForm hJ) p.1 +
          (2⁻¹ : ℝ) • (-J.toEndomorphism.realAlternatingDerivation p.2) := by
      rw [deformationTargetAmbientMap_snd, smul_neg, sub_eq_add_neg]
    rw [← twoFormBivectorEval_apply, hsnd, map_add, map_smul, map_smul,
      twoFormBivectorEval_apply, twoFormBivectorEval_apply,
      J.alternatingFormEquiv_symm_neg_realAlternatingDerivation_two hJ]
    simp [SmoothForm.wedge_zero_right_apply_eq_smul, smul_smul]

private theorem deformationTargetAmbientMap_snd_mem_selfDualForms
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetAmbientMap o J hJo.inner_apply_apply
      (p.1, (p.2 : SmoothForm I M ℝ 2))).2 ∈
      SmoothForm.selfDualForms (I := I) (M := M) o := by
  rw [SmoothForm.mem_selfDualForms]
  apply Subtype.ext
  funext x
  let _ := o.fact_finrank_tangentSpace x
  have hkl : 2 + 2 = finrank ℝ (TangentSpace I x) := (o.fact_finrank_tangentSpace x).out.symm
  obtain ⟨e, he, h₀, h₂⟩ := hJo.exists_frame x
  have hp := SmoothForm.hodgeStar_alternatingFormEquiv_symm_of_mem_selfDualForms o p.2.2 x
  have hfib := (Prod.mk.inj (deformationTargetAmbientMap_apply_eq o hJo.inner_apply_apply
    (p.1, (p.2 : SmoothForm I M ℝ 2)) x)).2
  have hsd := hodgeStar_deformationComplexStructure_snd hkl he h₀ h₂
    (p := (p.1.1 x 0,
      (alternatingFormEquiv (TangentSpace I x) 2).symm
        ((p.2 : SmoothForm I M ℝ 2).1 x))) hp
  set η := (deformationTargetAmbientMap o J hJo.inner_apply_apply
    (p.1, (p.2 : SmoothForm I M ℝ 2))).2
  rw [SmoothForm.coe_hodgeStar, RoughForm.hodgeStar_apply]
  apply (alternatingFormEquiv (TangentSpace I x) 2).symm.injective
  have hstar : (alternatingFormEquiv (TangentSpace I x) 2).symm
      ((o.orientationAt x).formHodgeStar hkl (η.1 x)) =
      (o.orientationAt x).hodgeStar hkl
        ((alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x)) := by
    apply (alternatingFormEquiv (TangentSpace I x) 2).injective
    rw [LinearEquiv.apply_symm_apply,
      ← (o.orientationAt x).formHodgeStar_alternatingFormEquiv,
      LinearEquiv.apply_symm_apply]
  rw [hstar, hfib]
  exact hsd

private def deformationTargetLinearMap (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) :
    Module.End ℝ (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :=
  let embed : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o →ₗ[ℝ]
      SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2 :=
    (LinearMap.fst ℝ _ _).prod
      ((SmoothForm.selfDualForms (I := I) (M := M) o).subtype.comp (LinearMap.snd ℝ _ _))
  let F := deformationTargetAmbientMap o J hJo.inner_apply_apply ∘ₗ embed
  (LinearMap.fst ℝ _ _ ∘ₗ F).prod <|
    (LinearMap.snd ℝ _ _ ∘ₗ F).codRestrict _
      (deformationTargetAmbientMap_snd_mem_selfDualForms o J hJo)

private theorem deformationTargetLinearMap_apply_eq (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    deformationTargetEval o x (deformationTargetLinearMap o J hJo p) =
      (letI := o.fact_finrank_tangentSpace x
       deformationComplexStructure (J.almostComplexStructureAt x) (deformationTargetEval o x p)) :=
  deformationTargetAmbientMap_apply_eq o hJo.inner_apply_apply (p.1, (p.2 : SmoothForm I M ℝ 2)) x

private theorem deformationTargetLinearMap_comp_self (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) :
    deformationTargetLinearMap o J hJo ∘ₗ deformationTargetLinearMap o J hJo = -LinearMap.id := by
  refine LinearMap.ext fun p ↦ ext_deformationTarget o fun x ↦ ?_
  let _ := o.fact_finrank_tangentSpace x
  obtain ⟨e, he, h₀, h₂⟩ := hJo.exists_frame x
  rw [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, map_neg,
    deformationTargetLinearMap_apply_eq, deformationTargetLinearMap_apply_eq,
    deformationComplexStructure_deformationComplexStructure
      (o.fact_finrank_tangentSpace x).out.symm he h₀ h₂
      (SmoothForm.hodgeStar_alternatingFormEquiv_symm_of_mem_selfDualForms o p.2.2 x)]

/-- **The global almost complex structure `J′` on `Ω⁰(M) × Ω⁺(M)`** induced by a metric- and
orientation-compatible smooth almost complex structure `J` on `(M, g, o)`. At every point `x : M`,
it acts on `(g(x), η_x)` as `deformationSelfDualComplexStructure` on `ℝ × Λ⁺_x`. -/
def deformationTargetComplexStructure (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) :
    AlmostComplexStructure
      (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) where
  toLinearMap := deformationTargetLinearMap o J hJo
  square_neg := deformationTargetLinearMap_comp_self o J hJo

/-- The zero-form component of `J′(g, η)` is `-(√2 / 2) ⟨ω, η⟩`, where `ω = J.kahlerTwoForm` and
`⟨ω, η⟩ = SmoothForm.innerZeroForm o ω η`. -/
@[simp]
theorem deformationTargetComplexStructure_apply_fst (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetComplexStructure o J hJo p).1 =
      -((√2 / 2 : ℝ) • SmoothForm.innerZeroForm (k := 2) (l := 2) o
        (J.kahlerTwoForm hJo.inner_apply_apply) (p.2 : SmoothForm I M ℝ 2)) :=
  (rfl)

/-- The self-dual two-form component of `J′(g, η)` is `(√2 / 2) (ω ∧ g) - (1 / 2) D_J η`, where
`ω = J.kahlerTwoForm` and `D_J = J.toEndomorphism.realAlternatingDerivation`. -/
@[simp]
theorem coe_deformationTargetComplexStructure_apply_snd (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetComplexStructure o J hJo p).2 : SmoothForm I M ℝ 2) =
      (√2 / 2 : ℝ) • SmoothForm.wedge (J.kahlerTwoForm hJo.inner_apply_apply) p.1 -
        (2⁻¹ : ℝ) • J.toEndomorphism.realAlternatingDerivation (p.2 : SmoothForm I M ℝ 2) :=
  (rfl)

/-- **Fibrewise formula for `deformationTargetComplexStructure`:** at every point `x : M`,
`deformationTargetComplexStructure o J hJo` acts as `deformationComplexStructure
(J.almostComplexStructureAt x)`. -/
theorem deformationTargetComplexStructure_apply_eq (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     ((deformationTargetComplexStructure o J hJo p).1.1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         (((deformationTargetComplexStructure o J hJo p).2 : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationComplexStructure (J.almostComplexStructureAt x)
         (p.1.1 x 0,
           (alternatingFormEquiv (TangentSpace I x) 2).symm ((p.2 : SmoothForm I M ℝ 2).1 x))) :=
  deformationTargetLinearMap_apply_eq o J hJo p x

private theorem deformationTargetEval_complexStructure (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    deformationTargetEval o x (deformationTargetComplexStructure o J hJo p) =
      (letI := o.fact_finrank_tangentSpace x
       deformationComplexStructure (J.almostComplexStructureAt x) (deformationTargetEval o x p)) :=
  deformationTargetComplexStructure_apply_eq o J hJo p x

/-- **Pointwise orthogonality of `deformationTargetComplexStructure`:** at every point `x : M`,
`J′` preserves the pointwise inner product `(p, q) ↦ p.1(x) q.1(x) + ⟨p.2(x), q.2(x)⟩` on
`Ω⁰(M) × Ω⁺(M)`. -/
theorem inner_deformationTargetComplexStructure (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o)
    (p q : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    (deformationTargetComplexStructure o J hJo p).1.1 x 0 *
        (deformationTargetComplexStructure o J hJo q).1.1 x 0 +
      alternatingFormInner (TangentSpace I x) 2
        (((deformationTargetComplexStructure o J hJo p).2 : SmoothForm I M ℝ 2).1 x)
        (((deformationTargetComplexStructure o J hJo q).2 : SmoothForm I M ℝ 2).1 x) =
      p.1.1 x 0 * q.1.1 x 0 +
        alternatingFormInner (TangentSpace I x) 2
          ((p.2 : SmoothForm I M ℝ 2).1 x) ((q.2 : SmoothForm I M ℝ 2).1 x) := by
  let _ := o.fact_finrank_tangentSpace x
  obtain ⟨e, he, h₀, h₂⟩ := hJo.exists_frame x
  have hfp := deformationTargetComplexStructure_apply_eq o J hJo p x
  have hfq := deformationTargetComplexStructure_apply_eq o J hJo q x
  rw [alternatingFormInner_apply, alternatingFormInner_apply,
    (Prod.mk.inj hfp).1, (Prod.mk.inj hfp).2, (Prod.mk.inj hfq).1, (Prod.mk.inj hfq).2]
  exact inner_deformationComplexStructure (o.fact_finrank_tangentSpace x).out.symm he h₀ h₂
    (SmoothForm.hodgeStar_alternatingFormEquiv_symm_of_mem_selfDualForms o p.2.2 x)

/-- `deformationTargetComplexStructure o J hJo` commutes with right multiplication by smooth
functions (`C^∞(M)`-linearity). -/
theorem deformationTargetComplexStructure_mulRight (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) (f : SmoothForm I M ℝ 0)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    deformationTargetComplexStructure o J hJo (deformationTargetMulRight o f p) =
      deformationTargetMulRight o f (deformationTargetComplexStructure o J hJo p) := by
  have hmulfib (r : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
      deformationTargetEval o x (deformationTargetMulRight o f r) =
        f.1 x 0 • deformationTargetEval o x r := by
    let _ := o.fact_finrank_tangentSpace x
    refine Prod.ext ?_ ?_
    · simp [SmoothForm.wedge_apply_zero_right, mul_comm]
    · simp [SmoothForm.wedge_zero_right_apply_eq_smul]
  refine ext_deformationTarget o fun x ↦ ?_
  let _ := o.fact_finrank_tangentSpace x
  rw [deformationTargetEval_complexStructure, hmulfib, map_smul, hmulfib,
    deformationTargetEval_complexStructure]

end Target

/-! ### Taubes's complex-linear operator `δ_ω` and the principal-symbol homotopy -/

section ComplexOperator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Taubes's complex-linear Seiberg–Witten deformation operator**
`δ_ω = complexLinearPart J₁ J′ δ₀ = (δ₀ - J′ ∘ δ₀ ∘ J₁) / 2`, acting from smooth one-forms to
`Ω⁰(M) × Ω⁺(M)` on an oriented Riemannian four-manifold with a compatible almost complex structure
`J`. -/
def complexDeformationOperator (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  TauCeti.complexLinearPart J.covectorComplexStructure.toLinearMap
    (deformationTargetComplexStructure o J hJo).toLinearMap (asdDeformationOperator o)

/-- Unfolding `complexDeformationOperator` as `(2⁻¹ : ℝ) • (δ₀ a - J′ (δ₀ (J₁ a)))`. -/
theorem complexDeformationOperator_apply (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o)
    (a : SmoothForm I M ℝ 1) :
    complexDeformationOperator o J hJo a =
      (2⁻¹ : ℝ) • (asdDeformationOperator o a -
        deformationTargetComplexStructure o J hJo
          (asdDeformationOperator o (J.covectorComplexStructure a))) :=
  TauCeti.complexLinearPart_apply _ _ _ a

/-- **`δ_ω` is complex linear** with respect to `J.covectorComplexStructure` on `Ω¹(M)` and
`deformationTargetComplexStructure o J hJo` on `Ω⁰(M) × Ω⁺(M)`. -/
theorem isComplexLinearMap_complexDeformationOperator (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) :
    IsComplexLinearMap J.covectorComplexStructure (deformationTargetComplexStructure o J hJo)
      (complexDeformationOperator o J hJo) :=
  (isComplexLinearMap_iff_isComplexLinear _ _ _).mpr <|
    TauCeti.complexLinearPart_isComplexLinear J.covectorComplexStructure.square_neg
      (deformationTargetComplexStructure o J hJo).square_neg (asdDeformationOperator o)

/-- The difference `δ_ω - δ₀` is minus the `(J₁, J′)`-complex-antilinear part of `δ₀`. -/
theorem complexDeformationOperator_sub_asdDeformationOperator_eq_neg_complexAntilinearPart
    (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) :
    complexDeformationOperator o J hJo - asdDeformationOperator o =
      -TauCeti.complexAntilinearPart J.covectorComplexStructure.toLinearMap
        (deformationTargetComplexStructure o J hJo).toLinearMap (asdDeformationOperator o) := by
  have key {x y z : SmoothForm I M ℝ 1 →ₗ[ℝ]
      SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o}
      (h : x + y = z) : x - z = -y := by
    subst h
    abel
  exact key (TauCeti.complexLinearPart_add_complexAntilinearPart
    J.covectorComplexStructure.toLinearMap
    (deformationTargetComplexStructure o J hJo).toLinearMap (asdDeformationOperator o))

private theorem complexDeformationOperator_commutator_eq_two_inv_smul
    (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    complexDeformationOperator o J hJo (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (complexDeformationOperator o J hJo a) =
      (2⁻¹ : ℝ) •
        ((asdDeformationOperator o (SmoothForm.wedge a f) -
            deformationTargetMulRight o f (asdDeformationOperator o a)) -
          deformationTargetComplexStructure o J hJo
            (asdDeformationOperator o (SmoothForm.wedge (J.covectorComplexStructure a) f) -
              deformationTargetMulRight o f
                (asdDeformationOperator o (J.covectorComplexStructure a)))) := by
  have hsmul_sub (x y : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
      (2⁻¹ : ℝ) • x - (2⁻¹ : ℝ) • y = (2⁻¹ : ℝ) • (x - y) :=
    (@smul_sub ℝ _ _ Module.toDistribMulAction.toDistribSMul (2⁻¹ : ℝ) x y).symm
  rw [complexDeformationOperator_apply, complexDeformationOperator_apply,
    J.covectorComplexStructure_wedge_zero_right, map_smul, map_sub,
    ← deformationTargetComplexStructure_mulRight, hsmul_sub,
    map_sub (deformationTargetComplexStructure o J hJo).toLinearMap]
  congr 1
  abel

/-- **`δ_ω` and `δ₀` have the exact same commutator with multiplication by smooth functions:**
`δ_ω(a ∧ f) - δ_ω(a) ∧ f = δ₀(a ∧ f) - δ₀(a) ∧ f`. -/
theorem complexDeformationOperator_commutator_eq (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o)
    (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    complexDeformationOperator o J hJo (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (complexDeformationOperator o J hJo a) =
      asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a) := by
  rw [complexDeformationOperator_commutator_eq_two_inv_smul]
  refine ext_deformationTarget o fun x ↦ ?_
  let _ := o.fact_finrank_tangentSpace x
  obtain ⟨e, he, h₀, h₂⟩ := hJo.exists_frame x
  have hCa : deformationTargetEval o x
      (asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a)) = _ :=
    asdDeformationOperator_commutator_eq_deformationSymbol o a f x
  have hCJa : deformationTargetEval o x
      (asdDeformationOperator o (SmoothForm.wedge (J.covectorComplexStructure a) f) -
        deformationTargetMulRight o f
          (asdDeformationOperator o (J.covectorComplexStructure a))) = _ :=
    asdDeformationOperator_commutator_eq_deformationSymbol o
      (J.covectorComplexStructure a) f x
  rw [J.rieszDual_covectorComplexStructure hJo.inner_apply_apply a x,
    ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply] at hCJa
  rw [map_smul, map_sub, deformationTargetEval_complexStructure, hCa, hCJa]
  exact two_inv_smul_sub_deformationComplexStructure_deformationSymbol
    (o.fact_finrank_tangentSpace x).out.symm he h₀ h₂
    (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x))
    (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x))

/-- **`δ_ω - δ₀` is `C^∞(M)`-linear (an operator of order zero):** it commutes with right
multiplication by any smooth function `f ∈ Ω⁰(M)`. -/
theorem complexDeformationOperator_sub_asdDeformationOperator_wedge
    (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    (complexDeformationOperator o J hJo - asdDeformationOperator o) (SmoothForm.wedge a f) =
      deformationTargetMulRight o f
        ((complexDeformationOperator o J hJo - asdDeformationOperator o) a) := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, sub_eq_sub_iff_sub_eq_sub]
  exact complexDeformationOperator_commutator_eq o J hJo a f

/-- **The linear deformation homotopy** `δ_t = (1 - t) δ₀ + t δ_ω` (`t ∈ ℝ`) interpolating between
the real Atiyah–Hitchin–Singer operator `δ₀` (`t = 0`) and Taubes's complex-linear operator `δ_ω`
(`t = 1`). -/
def deformationHomotopy (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) (t : ℝ) :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  (1 - t) • asdDeformationOperator o + t • complexDeformationOperator o J hJo

@[simp]
theorem deformationHomotopy_zero (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) :
    deformationHomotopy o J hJo 0 = asdDeformationOperator o := by
  simp [deformationHomotopy]

@[simp]
theorem deformationHomotopy_one (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) :
    deformationHomotopy o J hJo 1 = complexDeformationOperator o J hJo := by
  simp [deformationHomotopy]

/-- `δ_t = δ₀ + t (δ_ω - δ₀)`: the homotopy perturbs `δ₀` by `t` times the order-zero operator
`δ_ω - δ₀`. -/
theorem deformationHomotopy_eq_add_smul_sub (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) (t : ℝ) :
    deformationHomotopy o J hJo t =
      asdDeformationOperator o +
        t • (complexDeformationOperator o J hJo - asdDeformationOperator o) := by
  rw [deformationHomotopy]
  module

/-- **Invariance of the principal symbol along `deformationHomotopy`:** for every `t : ℝ`,
`[δ_t, · ∧ f] = [δ₀, · ∧ f]`. -/
theorem deformationHomotopy_commutator_eq (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : J.IsCompatibleOrientation o) (t : ℝ)
    (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    deformationHomotopy o J hJo t (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (deformationHomotopy o J hJo t a) =
      asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a) := by
  rw [deformationHomotopy_eq_add_smul_sub, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply,
    complexDeformationOperator_sub_asdDeformationOperator_wedge, map_add, map_smul]
  module

/-- **Every operator `δ_t` along the homotopy has the elliptic principal symbol
`deformationSymbol`:** at every `x : M` and for every `t : ℝ`, `δ_t(a ∧ f) - δ_t(a) ∧ f` evaluates
at `x` to `deformationSymbol (o.orientationAt x) _ (df_x)♯ (a_x)♯`, which is bijective onto
`ℝ × Λ⁺_x` whenever `(df)_x ≠ 0` (`TauCeti.SeibergWitten.deformationSymbolSelfDual_bijective`). -/
theorem deformationHomotopy_commutator_eq_deformationSymbol
    (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
    (hJo : J.IsCompatibleOrientation o) (t : ℝ) (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (((deformationHomotopy o J hJo t (SmoothForm.wedge a f) -
          deformationTargetMulRight o f (deformationHomotopy o J hJo t a)).1).1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         (((deformationHomotopy o J hJo t (SmoothForm.wedge a f) -
            deformationTargetMulRight o f
              (deformationHomotopy o J hJo t a)).2 : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationSymbol (o.orientationAt x) (o.fact_finrank_tangentSpace x).out.symm
         (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x))
         (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x))) := by
  rw [deformationHomotopy_commutator_eq]
  exact asdDeformationOperator_commutator_eq_deformationSymbol o a f x

end ComplexOperator

end TauCeti.SeibergWitten
