/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.AbelianDeformation
public import TauCeti.Analysis.PDE.SeibergWitten.DeformationSymbol
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import TauCeti.LinearAlgebra.Determinant.Line
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The Atiyah–Hitchin–Singer deformation operator and symbol commutator

On an oriented Riemannian four-manifold `(M, g, o)`, the gauge-fixed linearization of the
anti-self-dual equations is the first-order Atiyah–Hitchin–Singer operator

`δ₀ : Ω¹(M) → Ω⁰(M) ⊕ Ω⁺(M)`,   `δ₀(a) = (-d*a, √2 (da)⁺)`.

With the `√2` normalization on the self-dual two-forms `Ω⁺(M)`, the principal symbol of `δ₀` at a
covector `ξ` is `‖ξ‖` times a linear isometry `T_x M → ℝ ⊕ Λ⁺_x`
(`TauCeti.SeibergWitten.deformationSymbol_fst_sq_add_norm_snd_sq`) and becomes `(J, J′)`-complex
linear whenever `J` is an orthogonal almost complex structure inducing `o`.

This file defines `δ₀` on smooth differential forms and proves two foundational bridges:

1. **Determinant line equivalence with `abelianDeformationOperator`:** the diagonal target rescaling
   `(g, η) ↦ (2 g, (√2 / 2) η)` (`TauCeti.SeibergWitten.deformationTargetRescale`) intertwines `δ₀`
   with the Seiberg–Witten abelian deformation operator `T(a) = (-2 d*a, (da)⁺)`, inducing a
   canonical linear equivalence of determinant lines
   `asdDeformationDetLineEquiv : δ₀.detLine ≃ₗ[ℝ] T.detLine`.
2. **Principal symbol via the `C^∞(M)`-commutator:** for any smooth function `f ∈ Ω⁰(M)` and smooth
   one-form `a ∈ Ω¹(M)`, the commutator `δ₀(a ∧ f) - δ₀(a) ∧ f` evaluates at `x : M` to the
   pointwise algebraic symbol `deformationSymbol (o.orientationAt x) _ (df_x)♯ (a_x)♯`
   (`TauCeti.SeibergWitten.asdDeformationOperator_commutator_eq_deformationSymbol`).

## Main definitions

* `TauCeti.SeibergWitten.innerZeroForm`: the smooth zero-form `⋆(α ∧ ⋆β)` representing the pointwise
  inner product of smooth `k`-forms.
* `TauCeti.SeibergWitten.asdDeformationOperator`: the operator `δ₀(a) = (-d*a, √2 (da)⁺)`.
* `TauCeti.SeibergWitten.deformationTargetRescale`,
  `TauCeti.SeibergWitten.asdDeformationDetLineEquiv`: target rescaling intertwining `δ₀` with
  `abelianDeformationOperator` and the induced isomorphism of determinant lines.
* `TauCeti.SeibergWitten.deformationTargetMulRight`: right multiplication by `f ∈ Ω⁰(M)` on
  `Ω⁰(M) × Ω⁺(M)`.

## Main results

* `TauCeti.SeibergWitten.deformationTargetRescale_comp_asdDeformationOperator`:
  `deformationTargetRescale ∘ δ₀ = abelianDeformationOperator`.
* `TauCeti.SeibergWitten.ker_asdDeformationOperator`: on a closed oriented four-manifold,
  `ker δ₀ = ker d ⊓ ker d*`.
* `TauCeti.SeibergWitten.asdDeformationOperator_commutator_eq_deformationSymbol`: the commutator of
  `δ₀` with `· ∧ f` computes `deformationSymbol` fibrewise.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*, J. Amer.
  Math. Soc. 9 (1996), 845–918, §1–2.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Bundle Module Real exteriorPower
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti.SeibergWitten

/-- Direct `AddCommGroup` shortcut on `SmoothForm I M ℝ k`, avoiding nested `Submodule` ring
search on products with `SmoothForm.selfDualForms`. -/
local instance instAddCommGroupSmoothForm {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (k : ℕ) :
    AddCommGroup (SmoothForm I M ℝ k) :=
  Submodule.addCommGroup _

/-- Direct `Module ℝ` shortcut on `SmoothForm I M ℝ k`. -/
local instance instModuleSmoothForm {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (k : ℕ) :
    Module ℝ (SmoothForm I M ℝ k) :=
  Submodule.module _

/-- Direct `AddCommGroup` shortcut on `SmoothForm.selfDualForms o`. -/
local instance instAddCommGroupSelfDualForms {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (2 + 2))) :
    AddCommGroup (SmoothForm.selfDualForms (I := I) (M := M) o) :=
  Submodule.addCommGroup _

/-- Direct `Module ℝ` shortcut on `SmoothForm.selfDualForms o`. -/
local instance instModuleSelfDualForms {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (2 + 2))) :
    Module ℝ (SmoothForm.selfDualForms (I := I) (M := M) o) :=
  Submodule.module _

section Helpers

/-- For a compatible metric and orientation, `⋆(α ∧ ⋆β)` evaluated at `0` recovers the pointwise
form inner product `⟨α, β⟩`. -/
private theorem formHodgeStar_wedge_formHodgeStar_apply_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n k l : ℕ} [_i : Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))
    (hkl : k + l = finrank ℝ V) (hm0 : (k + l) + 0 = finrank ℝ V)
    (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    o.formHodgeStar hm0 (α.wedge (o.formHodgeStar hkl β)) 0 =
      alternatingFormInner V k α β := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V k).surjective α
  obtain ⟨b, rfl⟩ := (alternatingFormEquiv V k).surjective β
  set z : ⋀[ℝ]^(finrank ℝ V) V := ⟨_, by
    rw [← hkl]; exact (exteriorPower.wedge ℝ V k l a (o.hodgeStar hkl b)).2⟩
  have hz : ((exteriorPower.wedge ℝ V k l a (o.hodgeStar hkl b) : ExteriorAlgebra ℝ V) *
      ((ιMulti ℝ 0 (![] : Fin 0 → V)) : ExteriorAlgebra ℝ V)) = (z : ExteriorAlgebra ℝ V) := by
    simp [z, ExteriorAlgebra.ιMulti_zero_apply]
  have h0 : (0 : Fin 0 → V) = ![] := Subsingleton.elim _ _
  rw [o.formHodgeStar_alternatingFormEquiv, ← alternatingFormEquiv_wedge,
    o.formHodgeStar_apply, LinearEquiv.symm_apply_apply,
    alternatingFormInner_alternatingFormEquiv, ← o.wedgePairing_hodgeStar hkl, h0,
    wedgePairing_apply_eq_of_coe_mul_eq _ hm0 _ _ z hz,
    wedgePairing_apply_eq_of_coe_mul_eq _ hkl _ _ z rfl]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The smooth zero-form `⋆(α ∧ ⋆β)`, linear in `β`, representing the pointwise inner product
`⟨α, β⟩` of smooth `k`-forms on an oriented Riemannian `(k + l)`-manifold. -/
def innerZeroForm {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l)))
    (α : SmoothForm I M ℝ k) : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ 0 :=
  SmoothForm.hodgeStar o (Nat.add_zero (k + l)) ∘ₗ
    SmoothForm.wedge α ∘ₗ SmoothForm.hodgeStar o rfl

/-- Evaluating `innerZeroForm o α β` at `x : M` recovers `alternatingFormInner` of `α_x` and
`β_x`. -/
theorem innerZeroForm_apply {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l)))
    (α β : SmoothForm I M ℝ k) (x : M) (u : Fin 0 → TangentSpace I x) :
    (innerZeroForm o α β).1 x u =
      alternatingFormInner (TangentSpace I x) k (α.1 x) (β.1 x) := by
  let _ := o.fact_finrank_tangentSpace x
  have hu : u = 0 := Subsingleton.elim _ _
  rw [hu, innerZeroForm, LinearMap.comp_apply, LinearMap.comp_apply, SmoothForm.coe_hodgeStar,
    RoughForm.hodgeStar_apply]
  have hw : (SmoothForm.wedge α (SmoothForm.hodgeStar o rfl β)).1 x =
      (α.1 x).wedge ((o.orientationAt x).formHodgeStar
        (o.fact_finrank_tangentSpace x).out.symm (β.1 x)) := by
    ext w
    rw [SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
      ← ContinuousAlternatingMap.wedge_def, SmoothForm.coe_hodgeStar, RoughForm.hodgeStar_apply]
  rw [hw]
  exact formHodgeStar_wedge_formHodgeStar_apply_zero (o.orientationAt x) _ _ (α.1 x) (β.1 x)

/-- The Hodge star commutes with right multiplication by a smooth zero-form. -/
private theorem hodgeStar_wedge_zero_right {m k l : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : SmoothForm I M ℝ k) (f : SmoothForm I M ℝ 0) :
    SmoothForm.hodgeStar o hkl (SmoothForm.wedge φ f) =
      SmoothForm.wedge (SmoothForm.hodgeStar o hkl φ) f := by
  apply Subtype.ext
  funext x
  let _ := o.fact_finrank_tangentSpace x
  have hsmul : (SmoothForm.wedge φ f).1 x = f.1 x 0 • φ.1 x := by
    ext v
    rw [SmoothForm.wedge_apply_zero_right, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      mul_comm]
  ext v
  rw [SmoothForm.wedge_apply_zero_right, SmoothForm.coe_hodgeStar, RoughForm.hodgeStar_apply,
    hsmul, map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_comm,
    SmoothForm.coe_hodgeStar, RoughForm.hodgeStar_apply]

/-- The self-dual projection commutes with right multiplication by a smooth zero-form. -/
private theorem selfDualPart_wedge_zero_right {k : ℕ} (o : Manifold.Orientation I M (Fin (k + k)))
    (φ : SmoothForm I M ℝ k) (f : SmoothForm I M ℝ 0) :
    SmoothForm.selfDualPart o (SmoothForm.wedge φ f) =
      SmoothForm.wedge (SmoothForm.selfDualPart o φ) f := by
  apply Subtype.ext
  funext x
  ext v
  simp only [SmoothForm.coe_selfDualPart, RoughForm.selfDualPart_apply,
    SmoothForm.wedge_apply_zero_right, Pi.smul_apply, Pi.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul]
  have hh := congrArg (fun ψ : SmoothForm I M ℝ k ↦ ψ.1 x v)
    (hodgeStar_wedge_zero_right o rfl φ f)
  simp only [SmoothForm.coe_hodgeStar, SmoothForm.wedge_apply_zero_right] at hh
  rw [hh]
  ring

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The Leibniz rule for wedging a smooth `k`-form on the right with a smooth zero-form:
`d(φ ∧ f) = dφ ∧ f + (-1)^k φ ∧ df`. -/
private theorem mextDerivₗ_wedge_zero_right {k : ℕ} (φ : SmoothForm I M ℝ k)
    (f : SmoothForm I M ℝ 0) :
    mextDerivₗ I k (SmoothForm.wedge φ f) =
      SmoothForm.wedge (mextDerivₗ I k φ) f +
        (-1 : ℝ) ^ k • SmoothForm.wedge φ (mextDerivₗ I 0 f) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  exact SmoothForm.mextDerivₗ_wedge (I := I) (k := k) (l := 0) φ f

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Under `alternatingFormEquiv`, a smooth one-form at `x` corresponds to the tangent vector given
by the Riesz dual of `SmoothForm.degreeOneEquiv`. -/
private theorem alternatingFormEquiv_rieszDual_degreeOneEquiv (a : SmoothForm I M ℝ 1) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     alternatingFormEquiv (TangentSpace I x) 1
      (ιMulti ℝ 1 ![Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)])) =
      a.1 x := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  ext w
  have hw : ![w 0] = w := funext fun i ↦ by fin_cases i; rfl
  rw [alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one, Riemannian.Tensor.inner_rieszDual,
    SmoothForm.degreeOneEquiv_apply_apply_vec, hw]

/-- Under `alternatingFormEquiv`, `SmoothForm.selfDualPart` acts fibrewise as `(1 / 2) (y + ⋆y)` on
`⋀² T_x M`. -/
private theorem alternatingFormEquiv_symm_selfDualPart
    (o : Manifold.Orientation I M (Fin (2 + 2))) (η : SmoothForm I M ℝ 2) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (alternatingFormEquiv (TangentSpace I x) 2).symm ((SmoothForm.selfDualPart o η).1 x)) =
      (letI := o.fact_finrank_tangentSpace x
       (2⁻¹ : ℝ) • ((alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x) +
         (o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
           ((alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x)))) := by
  let _ := o.fact_finrank_tangentSpace x
  apply (alternatingFormEquiv (TangentSpace I x) 2).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, map_add,
    ← (o.orientationAt x).formHodgeStar_alternatingFormEquiv, LinearEquiv.apply_symm_apply,
    SmoothForm.coe_selfDualPart, RoughForm.selfDualPart_apply, Pi.smul_apply, Pi.add_apply,
    RoughForm.hodgeStar_apply]

end Helpers

/-! ### The Atiyah–Hitchin–Singer operator `δ₀` and its determinant line -/

section ASDDeformation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- **Taubes's Atiyah–Hitchin–Singer deformation operator** `δ₀(a) = (-d*a, √2 (da)⁺)` on an
oriented Riemannian four-manifold, mapping smooth one-forms to pairs of a smooth zero-form and a
smooth self-dual two-form. With the `√2` normalization on `Ω⁺`, its principal symbol is an isometry
up to `‖ξ‖` and intertwines the domain and target almost complex structures of a compatible
almost-Kähler metric. -/
def asdDeformationOperator :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  (-SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl)).prod
    ((√2 • (SmoothForm.selfDualPart o ∘ₗ mextDerivₗ I 1)).codRestrict _ fun a ↦ by
      rw [LinearMap.smul_apply, LinearMap.comp_apply]
      exact Submodule.smul_mem _ _ (SmoothForm.selfDualPart_mem_selfDualForms o even_two _))

/-- The function component of `δ₀(a)` is `-d*a`. -/
@[simp]
theorem asdDeformationOperator_apply_fst (a : SmoothForm I M ℝ 1) :
    (asdDeformationOperator o a).1 =
      -SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl) a :=
  (rfl)

/-- The self-dual two-form component of `δ₀(a)` is `√2 (da)⁺`. -/
@[simp]
theorem coe_asdDeformationOperator_apply_snd (a : SmoothForm I M ℝ 1) :
    ((asdDeformationOperator o a).2 : SmoothForm I M ℝ 2) =
      √2 • SmoothForm.selfDualPart o (mextDerivₗ I 1 a) :=
  (rfl)

/-- The diagonal target rescaling `(g, η) ↦ (2 g, (√2 / 2) η)` intertwining `δ₀` with the
Seiberg–Witten `abelianDeformationOperator` `T(a) = (-2 d*a, (da)⁺)`. -/
def deformationTargetRescale :
    (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) ≃ₗ[ℝ]
      (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) where
  toFun p := ((2 : ℝ) • p.1, (√2 / 2 : ℝ) • p.2)
  invFun p := ((2⁻¹ : ℝ) • p.1, √2 • p.2)
  map_add' p q := Prod.ext (smul_add _ _ _) (smul_add _ _ _)
  map_smul' c p := Prod.ext (smul_comm _ _ _) (smul_comm _ _ _)
  left_inv p := Prod.ext (by module) <| Subtype.ext <| by
    simp only [SetLike.val_smul, smul_smul]
    have h : √2 * (√2 / 2) = (1 : ℝ) := by
      linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
    rw [h, one_smul]
  right_inv p := Prod.ext (by module) <| Subtype.ext <| by
    simp only [SetLike.val_smul, smul_smul]
    have h : √2 / 2 * √2 = (1 : ℝ) := by
      linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
    rw [h, one_smul]

@[simp]
theorem deformationTargetRescale_apply_fst
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetRescale o p).1 = (2 : ℝ) • p.1 :=
  (rfl)

@[simp]
theorem coe_deformationTargetRescale_apply_snd
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetRescale o p).2 : SmoothForm I M ℝ 2) =
      (√2 / 2 : ℝ) • (p.2 : SmoothForm I M ℝ 2) :=
  (rfl)

@[simp]
theorem deformationTargetRescale_symm_apply_fst
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetRescale o).symm p).1 = (2⁻¹ : ℝ) • p.1 :=
  (rfl)

@[simp]
theorem coe_deformationTargetRescale_symm_apply_snd
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (((deformationTargetRescale o).symm p).2 : SmoothForm I M ℝ 2) =
      √2 • (p.2 : SmoothForm I M ℝ 2) :=
  (rfl)

/-- **Target rescaling intertwines `δ₀` with `abelianDeformationOperator`:**
`deformationTargetRescale ∘ δ₀ = T`. -/
theorem deformationTargetRescale_comp_asdDeformationOperator :
    (deformationTargetRescale o).toLinearMap ∘ₗ asdDeformationOperator o =
      abelianDeformationOperator o := by
  ext a : 1
  refine Prod.ext ?_ (Subtype.ext ?_)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, deformationTargetRescale_apply_fst,
      asdDeformationOperator_apply_fst, abelianDeformationOperator_apply_fst]
    module
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coe_deformationTargetRescale_apply_snd,
      coe_asdDeformationOperator_apply_snd, coe_abelianDeformationOperator_apply_snd, smul_smul]
    have h : √2 / 2 * √2 = (1 : ℝ) := by
      linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
    rw [h, one_smul]

/-- **Canonical isomorphism of determinant lines** between `δ₀` and `abelianDeformationOperator`,
induced by the identity on `Ω¹(M)` and `deformationTargetRescale` on `Ω⁰(M) × Ω⁺(M)`. -/
def asdDeformationDetLineEquiv :
    (asdDeformationOperator o).detLine ≃ₗ[ℝ] (abelianDeformationOperator o).detLine :=
  LinearMap.detLineCongr (asdDeformationOperator o) (LinearEquiv.refl ℝ _)
    (deformationTargetRescale o)
    (by rw [LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
      deformationTargetRescale_comp_asdDeformationOperator])

section ClosedManifold

variable [CompactSpace M] [BoundarylessManifold I M] [T2Space M]

/-- On a closed oriented Riemannian four-manifold, `δ₀(a) = (-d*a, √2 (da)⁺)` vanishes if and only
if `a` is closed and coclosed. -/
theorem asdDeformationOperator_eq_zero_iff (a : SmoothForm I M ℝ 1) :
    asdDeformationOperator o a = 0 ↔
      mextDerivₗ I 1 a = 0 ∧
        SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl) a = 0 := by
  rw [← abelianDeformationOperator_eq_zero_iff o a,
    ← deformationTargetRescale_comp_asdDeformationOperator o, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]

/-- On a closed oriented Riemannian four-manifold, `ker δ₀ = ker T = ker d ⊓ ker d*`. -/
theorem ker_asdDeformationOperator :
    LinearMap.ker (asdDeformationOperator o) =
      LinearMap.ker (mextDerivₗ I (F := ℝ) 1) ⊓
        LinearMap.ker (SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl)) := by
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_inf, asdDeformationOperator_eq_zero_iff]

end ClosedManifold

end ASDDeformation

/-! ### `C^∞(M)`-commutator and identification with `deformationSymbol` -/

section SymbolCommutator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- Right multiplication `(g, η) ↦ (g ∧ f, η ∧ f)` by a smooth function `f ∈ Ω⁰(M)` on the target
`Ω⁰(M) × Ω⁺(M)` of the deformation operator. -/
def deformationTargetMulRight (f : SmoothForm I M ℝ 0) :
    Module.End ℝ (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :=
  (SmoothForm.wedge.flip f ∘ₗ LinearMap.fst ℝ _ _).prod <|
    (SmoothForm.wedge.flip f ∘ₗ (SmoothForm.selfDualForms (I := I) (M := M) o).subtype ∘ₗ
      LinearMap.snd ℝ _ _).codRestrict _ fun p ↦ by
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, Submodule.coe_subtype,
        LinearMap.snd_apply, SmoothForm.mem_selfDualForms, hodgeStar_wedge_zero_right]
      rw [SmoothForm.mem_selfDualForms.1 p.2.2]

@[simp]
theorem deformationTargetMulRight_apply_fst (f : SmoothForm I M ℝ 0)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetMulRight o f p).1 = SmoothForm.wedge p.1 f :=
  (rfl)

@[simp]
theorem coe_deformationTargetMulRight_apply_snd (f : SmoothForm I M ℝ 0)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    ((deformationTargetMulRight o f p).2 : SmoothForm I M ℝ 2) =
      SmoothForm.wedge (p.2 : SmoothForm I M ℝ 2) f :=
  (rfl)

/-- **Function component of `[δ₀, · ∧ f]`:** `-d*(a ∧ f) - (-d*a) ∧ f = ⟨df, a⟩` at every point. -/
theorem asdDeformationOperator_wedge_sub_fst_apply (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) (x : M) (u : Fin 0 → TangentSpace I x) :
    ((asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a)).1).1 x u =
      alternatingFormInner (TangentSpace I x) 1 ((mextDerivₗ I 0 f).1 x) (a.1 x) := by
  have h13 : 0 + 1 + 3 = 2 + 2 := rfl
  have h310 : 3 + 1 + 0 = 2 + 2 := rfl
  have hcod (b : SmoothForm I M ℝ 1) :
      -SmoothForm.codifferential o h13 b =
        SmoothForm.hodgeStar o h310 (mextDerivₗ I 3 (SmoothForm.hodgeStar o h13 b)) := by
    rw [SmoothForm.codifferential_apply o h13 h310]
    have hs : (-1 : ℝ) ^ ((2 + 2) * (0 + 2) + 1) = -1 := by norm_num
    rw [hs]
    module
  have hwcomm : SmoothForm.wedge (SmoothForm.hodgeStar o h13 a) (mextDerivₗ I 0 f) =
      -SmoothForm.wedge (mextDerivₗ I 0 f) (SmoothForm.hodgeStar o h13 a) := by
    apply Subtype.ext
    funext y
    ext w
    rw [SmoothForm.wedge_comm, Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
    have hcast : w ∘ Fin.cast (Nat.add_comm 1 3) = w := rfl
    rw [hcast]
    norm_num
  have hsub : (asdDeformationOperator o (SmoothForm.wedge a f) -
      deformationTargetMulRight o f (asdDeformationOperator o a)).1 =
      innerZeroForm (k := 1) (l := 3) o (mextDerivₗ I 0 f) a := by
    rw [Prod.fst_sub, asdDeformationOperator_apply_fst, deformationTargetMulRight_apply_fst,
      asdDeformationOperator_apply_fst, hcod, hcod, hodgeStar_wedge_zero_right o h13 a f,
      mextDerivₗ_wedge_zero_right, map_add, map_smul, hodgeStar_wedge_zero_right o h310 _ f,
      hwcomm, map_neg]
    have hpow : (-1 : ℝ) ^ 3 = -1 := by norm_num
    rw [hpow, innerZeroForm, LinearMap.comp_apply, LinearMap.comp_apply]
    module
  rw [hsub, innerZeroForm_apply]

/-- **Self-dual two-form component of `[δ₀, · ∧ f]`:**
`√2 (d(a ∧ f))⁺ - √2 (da)⁺ ∧ f = √2 (df ∧ a)⁺`. -/
theorem coe_asdDeformationOperator_wedge_sub_snd (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) :
    ((asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a)).2 : SmoothForm I M ℝ 2) =
      √2 • SmoothForm.selfDualPart o (SmoothForm.wedge (mextDerivₗ I 0 f) a) := by
  have hwcomm : SmoothForm.wedge a (mextDerivₗ I 0 f) =
      -SmoothForm.wedge (mextDerivₗ I 0 f) a := by
    apply Subtype.ext
    funext y
    ext w
    rw [SmoothForm.wedge_comm, Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
    have hcast : w ∘ Fin.cast (Nat.add_comm 1 1) = w := rfl
    rw [hcast]
    norm_num
  have hneg : (-1 : ℝ) ^ 1 • (-SmoothForm.wedge (mextDerivₗ I 0 f) a) =
      SmoothForm.wedge (mextDerivₗ I 0 f) a := by module
  rw [Prod.snd_sub, Submodule.coe_sub, coe_asdDeformationOperator_apply_snd,
    coe_deformationTargetMulRight_apply_snd, coe_asdDeformationOperator_apply_snd,
    mextDerivₗ_wedge_zero_right, hwcomm, hneg, map_add, smul_add,
    selfDualPart_wedge_zero_right, LinearMap.map_smul₂ SmoothForm.wedge, add_sub_cancel_left]

/-- **The `C^∞(M)`-commutator of `δ₀` computes `deformationSymbol` fibrewise:** at every `x : M`,
reading `(df)_x` and `a_x` as tangent vectors via `Riemannian.Tensor.rieszDual` and two-forms as
bivectors via `(alternatingFormEquiv (TangentSpace I x) 2).symm`, the commutator
`δ₀(a ∧ f) - δ₀(a) ∧ f` equals `deformationSymbol (o.orientationAt x) _ (df_x)♯ (a_x)♯`. -/
theorem asdDeformationOperator_commutator_eq_deformationSymbol (a : SmoothForm I M ℝ 1)
    (f : SmoothForm I M ℝ 0) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (((asdDeformationOperator o (SmoothForm.wedge a f) -
          deformationTargetMulRight o f (asdDeformationOperator o a)).1).1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         (((asdDeformationOperator o (SmoothForm.wedge a f) -
            deformationTargetMulRight o f
              (asdDeformationOperator o a)).2 : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationSymbol (o.orientationAt x) (o.fact_finrank_tangentSpace x).out.symm
         (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x))
         (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x))) := by
  let _ := o.fact_finrank_tangentSpace x
  set ξ := Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)
  set v := Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)
  have hξ := alternatingFormEquiv_rieszDual_degreeOneEquiv (mextDerivₗ I 0 f) x
  have hv := alternatingFormEquiv_rieszDual_degreeOneEquiv a x
  have hzv : (alternatingFormEquiv (TangentSpace I x) 2).symm
      ((SmoothForm.wedge (mextDerivₗ I 0 f) a).1 x) = ιMulti ℝ 2 ![ξ, v] := by
    apply (alternatingFormEquiv (TangentSpace I x) 2).injective
    rw [LinearEquiv.apply_symm_apply]
    ext w
    have hw : ![w 0, w 1] = w := funext fun i ↦ by fin_cases i <;> rfl
    rw [← hw, SmoothForm.wedge_apply_one_one, alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ← SmoothForm.degreeOneEquiv_apply_apply_vec, ← Riemannian.Tensor.inner_rieszDual, ξ, v]
    ring
  refine Prod.ext ?_ ?_
  · rw [asdDeformationOperator_wedge_sub_fst_apply, deformationSymbol_apply_fst,
      ← hξ, ← hv, alternatingFormInner_alternatingFormEquiv, inner_ιMulti_ιMulti,
      Matrix.det_fin_one]
    simp [ξ, v]
  · rw [coe_asdDeformationOperator_wedge_sub_snd, Submodule.coe_smul, Pi.smul_apply, map_smul,
      alternatingFormEquiv_symm_selfDualPart, hzv, smul_smul, ← div_eq_mul_inv,
      deformationSymbol_apply_snd]

end SymbolCommutator

end TauCeti.SeibergWitten
