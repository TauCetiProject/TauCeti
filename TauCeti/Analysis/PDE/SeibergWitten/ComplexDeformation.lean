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
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.LinearAlgebra.Determinant.Line
import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The complex-linear Seiberg–Witten deformation operator and principal-symbol homotopy

On an oriented Riemannian four-manifold `(M, g, o)`, Taubes's Gromov–Seiberg–Witten theory compares
the first-order Atiyah–Hitchin–Singer deformation operator

`δ₀ : Ω¹(M) → Ω⁰(M) ⊕ Ω⁺(M)`,   `δ₀(a) = (-d*a, √2 (da)⁺)`

with its complex-linear part

`δ_ω = (δ₀ - J′ ∘ δ₀ ∘ J₁) / 2`

for a smooth almost complex structure `J` compatible with the metric and inducing the orientation
`o` (`TauCeti.SeibergWitten.IsCompatibleOrientation`). Here `J₁` acts on smooth one-forms by
`(J₁ a)_x(v) = -a_x(J_x v)` (`TauCeti.SeibergWitten.covectorComplexStructure`), which intertwines
with `J_x` on `T_x M` under the Riesz isomorphism, and `J′` acts on `Ω⁰(M) × Ω⁺(M)` by

`J′(g, η) = (-(√2 / 2) ⟨ω, η⟩, (√2 / 2) g ω + (1 / 2) D_J η)`

(`TauCeti.SeibergWitten.deformationTargetComplexStructure`), matching the pointwise target complex
structure `TauCeti.SeibergWitten.deformationSelfDualComplexStructure` on every fibre.

Because the principal symbol of `δ₀` is already `(J, J′)`-complex-linear at every point
(`TauCeti.SeibergWitten.deformationSymbol_comp_toLinearMap`), taking the complex-linear part leaves
the principal symbol unchanged:

1. **Determinant line equivalence with `abelianDeformationOperator`:** the diagonal target rescaling
   `(g, η) ↦ (2 g, (√2 / 2) η)` (`TauCeti.SeibergWitten.deformationTargetRescale`) intertwines `δ₀`
   with `T a = (-2 d*a, (da)⁺)`, inducing a canonical isomorphism of determinant lines
   `asdDeformationDetLineEquiv : δ₀.detLine ≃ₗ[ℝ] T.detLine`.
2. **Principal symbol via the `C^∞(M)`-commutator:** for any smooth function `f ∈ Ω⁰(M)` and smooth
   one-form `a ∈ Ω¹(M)`, the commutator `δ₀(a ∧ f) - δ₀(a) ∧ f` evaluates at `x` to the algebraic
   principal symbol `deformationSymbol (o.orientationAt x) _ (df_x)♯ (a_x)♯`
   (`TauCeti.SeibergWitten.asdDeformationOperator_commutator_eq_deformationSymbol`).
3. **Order-zero difference and elliptic homotopy:** `δ_ω - δ₀` commutes with multiplication by
   smooth functions
   (`TauCeti.SeibergWitten.complexDeformationOperator_sub_asdDeformationOperator_wedge`), so it is a
   bundle map of order zero, and every operator along the linear homotopy
   `δ_t = (1 - t) δ₀ + t δ_ω` (`TauCeti.SeibergWitten.deformationHomotopy`) has the exact same
   elliptic principal symbol as `δ₀`
   (`TauCeti.SeibergWitten.deformationHomotopy_commutator_eq`,
   `TauCeti.SeibergWitten.deformationHomotopy_commutator_eq_deformationSymbol`).

## Main definitions

* `TauCeti.SeibergWitten.asdDeformationOperator`: the operator `δ₀(a) = (-d*a, √2 (da)⁺)`.
* `TauCeti.SeibergWitten.deformationTargetRescale`,
  `TauCeti.SeibergWitten.asdDeformationDetLineEquiv`: target rescaling intertwining `δ₀` with
  `abelianDeformationOperator` and the induced isomorphism of determinant lines.
* `TauCeti.SeibergWitten.deformationTargetMulRight`: right multiplication by `f ∈ Ω⁰(M)` on
  `Ω⁰(M) × Ω⁺(M)`.
* `TauCeti.SeibergWitten.covectorComplexStructure`: the almost complex structure `J₁` on `Ω¹(M)`
  dual to `J`.
* `TauCeti.SeibergWitten.IsCompatibleOrientation`: existence at every point of a positively oriented
  unitary orthonormal tangent frame for `(o, J)`, satisfied by any nondegenerate two-form `σ` whose
  associated bilinear form `σ(·, J ·)` is the metric and whose symplectic orientation agrees with
  `o` (`TauCeti.SeibergWitten.isCompatibleOrientation_of_symplectic`).
* `TauCeti.SeibergWitten.deformationTargetComplexStructure`: the global almost complex structure
  `J′` on `Ω⁰(M) × Ω⁺(M)`.
* `TauCeti.SeibergWitten.complexDeformationOperator`: Taubes's complex-linear operator
  `δ_ω = complexLinearPart J₁ J′ δ₀`.
* `TauCeti.SeibergWitten.deformationHomotopy`: the linear family `δ_t = (1 - t) δ₀ + t δ_ω`.

## Main results

* `TauCeti.SeibergWitten.asdDeformationOperator_commutator_eq_deformationSymbol`: the commutator of
  `δ₀` with `· ∧ f` computes `deformationSymbol` fibrewise.
* `TauCeti.SeibergWitten.isComplexLinearMap_complexDeformationOperator`: `δ_ω` is `(J₁, J′)`-complex
  linear.
* `TauCeti.SeibergWitten.complexDeformationOperator_sub_asdDeformationOperator_wedge`: `δ_ω - δ₀` is
  `C^∞(M)`-linear (an operator of order zero).
* `TauCeti.SeibergWitten.deformationHomotopy_commutator_eq`: `[δ_t, · ∧ f] = [δ₀, · ∧ f]` for all
  `t : ℝ`.

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

section PrivateHelpers

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth endomorphism field `A` of `TM` acts smoothly on real `k`-forms by applying `A` as a
derivation in the slots of the alternating form, obtained by restricting
`ContMDiffSection.alternatingDerivation` from complexified forms. -/
private def realAlternatingDerivation [IsManifold I 1 M] (k : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) :
    Module.End ℝ (SmoothForm I M ℝ k) :=
  SmoothForm.mapCoeff Complex.reCLM ∘ₗ
    (A.alternatingDerivation (F := ℂ) (k := k)).restrictScalars ℝ ∘ₗ
      SmoothForm.mapCoeff Complex.ofRealCLM

private theorem realAlternatingDerivation_apply [IsManifold I 1 M] {k : ℕ}
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ : SmoothForm I M ℝ k) (x : M) (v : Fin k → TangentSpace I x) :
    (realAlternatingDerivation k A φ).1 x v =
      ∑ i, φ.1 x (Function.update v i (A x (v i))) := by
  rw [realAlternatingDerivation, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply,
    A.coe_alternatingDerivation, ContinuousLinearMap.alternatingDerivation_apply, map_sum]
  simp

private theorem almostComplexStructureAt_inner [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {J : SmoothAlmostComplexStructure I M}
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) (x : M)
    (u w : TangentSpace I x) :
    ⟪J.almostComplexStructureAt x u, J.almostComplexStructureAt x w⟫ = ⟪u, w⟫ := by
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  exact hJ x u w

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

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The smooth zero-form `⋆(α ∧ ⋆β)`, linear in `β`, representing the pointwise inner product
`⟨α, β⟩` of smooth `k`-forms on an oriented Riemannian `(k + l)`-manifold. -/
private def innerZeroForm {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l)))
    (α : SmoothForm I M ℝ k) : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ 0 :=
  SmoothForm.hodgeStar o (Nat.add_zero (k + l)) ∘ₗ
    SmoothForm.wedge α ∘ₗ SmoothForm.hodgeStar o rfl

private theorem innerZeroForm_apply {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l)))
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

/-- The smooth Kähler two-form `ω_x(u, w) = ⟪J_x u, w⟫` associated to an orthogonal smooth almost
complex structure `J`. -/
private def kahlerTwoForm (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) :
    SmoothForm I M ℝ 2 :=
  ⟨fun x ↦ alternatingFormEquiv (TangentSpace I x) 2 (J.almostComplexStructureAt x).kahlerForm, by
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    apply IsSmoothForm.mem_smoothBundleForms
    rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
    intro x v
    set e := trivializationAt E (TangentSpace I) x
    let b := Module.finBasis ℝ E
    have hbase : e.baseSet ∈ 𝓝 x :=
      e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
    have hexp (y : M) (w : E) : e.symmL ℝ y w =
        ∑ k, b.repr w k • Riemannian.Tensor.chartLocalFrame (I := I) x k y := by
      conv_lhs => rw [← b.sum_repr w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_smul, Riemannian.Tensor.chartLocalFrame_eq_symmL]
    have hval (y : M) : alternatingFormEquiv (TangentSpace I y) 2
        (J.almostComplexStructureAt y).kahlerForm (e.symmL ℝ y ∘ v) =
        ∑ i, b.repr (v 0) i * ∑ j, b.repr (v 1) j *
          ⟪J y (Riemannian.Tensor.chartLocalFrame (I := I) x i y),
            Riemannian.Tensor.chartLocalFrame (I := I) x j y⟫ := by
      let _ : FiniteDimensional ℝ (TangentSpace I y) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) y
      have hv : e.symmL ℝ y ∘ v = ![e.symmL ℝ y (v 0), e.symmL ℝ y (v 1)] :=
        funext fun k ↦ by fin_cases k <;> rfl
      rw [hv, alternatingFormEquiv_apply,
        AlmostComplexStructure.inner_kahlerForm_ιMulti (almostComplexStructureAt_inner hJ y),
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
      change ⟪(J.toEndomorphism y) (e.symmL ℝ y (v 0)), e.symmL ℝ y (v 1)⟫ = _
      rw [hexp y (v 0), hexp y (v 1), map_sum, sum_inner]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, real_inner_smul_left, inner_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_smul_right]
    have hinner (i j : Fin (Module.finrank ℝ E)) : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y ↦ ⟪J y (Riemannian.Tensor.chartLocalFrame (I := I) x i y),
          Riemannian.Tensor.chartLocalFrame (I := I) x j y⟫) x := by
      have hJcoord : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
          (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
            x y x y (J.toEndomorphism y)) x :=
        ((contMDiffAt_hom_bundle _).mp (J.toEndomorphism.contMDiff x)).2
      let u : M → E := fun y ↦
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          x y x y (J.toEndomorphism y) (b i)
      have hu : ContMDiffAt I 𝓘(ℝ, E) ∞ u x := hJcoord.clm_apply contMDiffAt_const
      have hcoord (k : Fin (Module.finrank ℝ E)) :
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y ↦ b.repr (u y) k) x :=
        ((ContinuousLinearMap.proj k).comp
          b.equivFun.toLinearMap.toContinuousLinearMap).contDiff.comp_contMDiffAt hu
      have hG (k : Fin (Module.finrank ℝ E)) :
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞
            (fun y ↦ Riemannian.Tensor.chartGramMatrix (I := I) x y k j) x :=
        (Riemannian.Tensor.contMDiffOn_chartGramMatrix_entry (I := I) (n := ∞) x k j).contMDiffAt
          hbase
      refine (contMDiffAt_finsetSum (t := Finset.univ) fun k _ ↦
        (hcoord k).mul (hG k)).congr_of_eventuallyEq ?_
      filter_upwards [hbase] with y hy
      have hu_eq : e.symmL ℝ y (u y) =
          (J.toEndomorphism y) (Riemannian.Tensor.chartLocalFrame (I := I) x i y) := by
        simp only [u, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
          Function.comp_apply]
        rw [e.symmL_continuousLinearMapAt hy, Riemannian.Tensor.chartLocalFrame_eq_symmL]
      simp only [Pi.mul_apply, Riemannian.Tensor.chartGramMatrix_apply]
      rw [← hu_eq, hexp y (u y), sum_inner]
      exact Finset.sum_congr rfl fun k _ ↦ real_inner_smul_left _ _ _
    exact (contMDiffAt_finsetSum (t := Finset.univ) fun i _ ↦
      (contMDiffAt_const (c := b.repr (v 0) i)).mul <|
      contMDiffAt_finsetSum (t := Finset.univ) fun j _ ↦
        (contMDiffAt_const (c := b.repr (v 1) j)).mul (hinner i j)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simpa only [Pi.mul_apply] using hval y)⟩

private theorem alternatingFormEquiv_symm_kahlerTwoForm (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     (alternatingFormEquiv (TangentSpace I x) 2).symm ((kahlerTwoForm J hJ).1 x)) =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       (J.almostComplexStructureAt x).kahlerForm) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  exact LinearEquiv.symm_apply_apply _ _

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

/-- Every smooth self-dual two-form `η ∈ Ω⁺(M)` corresponds at `x` to a self-dual bivector under
`alternatingFormEquiv`. -/
private theorem hodgeStar_symm_selfDualForms (o : Manifold.Orientation I M (Fin (2 + 2)))
    (η : SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     (o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
       ((alternatingFormEquiv (TangentSpace I x) 2).symm
         ((η : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         ((η : SmoothForm I M ℝ 2).1 x)) := by
  let _ := o.fact_finrank_tangentSpace x
  apply (alternatingFormEquiv (TangentSpace I x) 2).injective
  rw [← (o.orientationAt x).formHodgeStar_alternatingFormEquiv, LinearEquiv.apply_symm_apply]
  simpa only [SmoothForm.coe_hodgeStar, RoughForm.hodgeStar_apply] using
    congrArg (fun ψ : SmoothForm I M ℝ 2 ↦ ψ.1 x) (SmoothForm.mem_selfDualForms.1 η.2)

/-- Fibrewise extensionality for elements of `Ω⁰(M) × Ω⁺(M)` read in `ℝ × ⋀² T_x M`. -/
private theorem ext_deformationTarget (o : Manifold.Orientation I M (Fin (2 + 2)))
    {p q : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o}
    (h : ∀ x : M,
      (letI := o.fact_finrank_tangentSpace x
       (p.1.1 x 0,
         (alternatingFormEquiv (TangentSpace I x) 2).symm
           ((p.2 : SmoothForm I M ℝ 2).1 x))) =
        (letI := o.fact_finrank_tangentSpace x
         (q.1.1 x 0,
           (alternatingFormEquiv (TangentSpace I x) 2).symm
             ((q.2 : SmoothForm I M ℝ 2).1 x)))) :
    p = q := by
  refine Prod.ext (Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun u ↦ ?_)
    (Subtype.ext <| Subtype.ext <| funext fun x ↦ ?_)
  · rw [Subsingleton.elim u 0]
    exact (Prod.mk.inj (h x)).1
  · let _ := o.fact_finrank_tangentSpace x
    exact (alternatingFormEquiv (TangentSpace I x) 2).symm.injective (Prod.mk.inj (h x)).2

end PrivateHelpers

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

/-! ### Domain and target almost complex structures on smooth forms -/

section AlmostComplex

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Covector

variable [IsManifold I ∞ M]

/-- **The almost complex structure `J₁` on smooth one-forms** dual to a smooth almost complex
structure `J` on `M`, given by `(J₁ a)_x(v) = -a_x(J_x v)`. For an orthogonal `J` this intertwines
with `J_x` on `T_x M` under `Riemannian.Tensor.rieszDual`
(`TauCeti.SeibergWitten.rieszDual_covectorComplexStructure`). -/
def covectorComplexStructure (J : SmoothAlmostComplexStructure I M) :
    AlmostComplexStructure (SmoothForm I M ℝ 1) where
  toLinearMap := -realAlternatingDerivation 1 J.toEndomorphism
  square_neg := by
    ext a x w
    have hw : ![w 0] = w := funext fun i ↦ by fin_cases i; rfl
    rw [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.neg_apply, Submodule.coe_neg,
      Pi.neg_apply, ContinuousAlternatingMap.neg_apply, realAlternatingDerivation_apply,
      Fin.sum_univ_one]
    have hu1 : Function.update w 0 (J.toEndomorphism x (w 0)) = ![J x (w 0)] :=
      funext fun i ↦ by fin_cases i; rfl
    rw [hu1, Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, neg_neg,
      realAlternatingDerivation_apply, Fin.sum_univ_one]
    have hu2 : Function.update ![J x (w 0)] 0 (J.toEndomorphism x (![J x (w 0)] 0)) = ![-w 0] :=
      funext fun i ↦ by fin_cases i; exact J.apply_apply x (w 0)
    have hmap : a.1 x ![-w 0] = -a.1 x ![w 0] := by
      rw [← SmoothForm.degreeOneEquiv_apply_apply_vec, map_neg,
        SmoothForm.degreeOneEquiv_apply_apply_vec]
    rw [hu2, hmap, hw]
    rfl

@[simp]
theorem covectorComplexStructure_apply_vec (J : SmoothAlmostComplexStructure I M)
    (a : SmoothForm I M ℝ 1) (x : M) (v : TangentSpace I x) :
    (covectorComplexStructure J a).1 x ![v] = -a.1 x ![J x v] := by
  change (-realAlternatingDerivation 1 J.toEndomorphism a).1 x ![v] = _
  rw [Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    realAlternatingDerivation_apply, Fin.sum_univ_one]
  congr 2
  exact funext fun i ↦ by fin_cases i; rfl

/-- `covectorComplexStructure J` commutes with right multiplication by smooth functions. -/
theorem covectorComplexStructure_wedge_zero_right (J : SmoothAlmostComplexStructure I M)
    (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    covectorComplexStructure J (SmoothForm.wedge a f) =
      SmoothForm.wedge (covectorComplexStructure J a) f := by
  apply Subtype.ext
  funext x
  ext w
  have hw : ![w 0] = w := funext fun i ↦ by fin_cases i; rfl
  rw [← hw, covectorComplexStructure_apply_vec, SmoothForm.wedge_apply_zero_right,
    SmoothForm.wedge_apply_zero_right, covectorComplexStructure_apply_vec, neg_mul]

/-- When `J` is fibrewise orthogonal, `covectorComplexStructure J` corresponds under the Riesz
isomorphism on `T_x M` to `J_x`. -/
theorem rieszDual_covectorComplexStructure [FiniteDimensional ℝ E]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {J : SmoothAlmostComplexStructure I M}
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (a : SmoothForm I M ℝ 1) (x : M) :
    Riemannian.Tensor.rieszDual (I := I) x
        (SmoothForm.degreeOneEquiv (covectorComplexStructure J a) x) =
      J x (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  symm
  rw [Riemannian.Tensor.eq_rieszDual_iff_inner_eq]
  intro w
  rw [SmoothForm.degreeOneEquiv_apply_apply_vec, covectorComplexStructure_apply_vec,
    ← SmoothForm.degreeOneEquiv_apply_apply_vec, ← Riemannian.Tensor.inner_rieszDual]
  have hskew := AlmostComplexStructure.inner_apply_left (almostComplexStructureAt_inner hJ x)
    (Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)) w
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hskew

end Covector

section Target

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A smooth almost complex structure `J` on an oriented Riemannian four-manifold `(M, g, o)` is
**compatible with the metric and orientation** if every tangent space `T_x M` admits a positively
oriented orthonormal basis `(e₀, e₁, e₂, e₃)` with `J_x e₀ = e₁` and `J_x e₂ = e₃`. -/
def IsCompatibleOrientation (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) : Prop :=
  ∀ x : M, ∃ e : OrthonormalBasis (Fin 4) ℝ (TangentSpace I x),
    e.toBasis.orientation = o.orientationAt x ∧ J x (e 0) = e 1 ∧ J x (e 2) = e 3

/-- A metric- and orientation-compatible smooth almost complex structure is fibrewise orthogonal. -/
theorem IsCompatibleOrientation.inner_apply_apply {o : Manifold.Orientation I M (Fin (2 + 2))}
    {J : SmoothAlmostComplexStructure I M} (hJo : IsCompatibleOrientation o J)
    (x : M) (u w : TangentSpace I x) :
    ⟪J x u, J x w⟫ = ⟪u, w⟫ := by
  let _ := o.fact_finrank_tangentSpace x
  obtain ⟨e, _, h₀, h₂⟩ := hJo x
  have h₀' : J.almostComplexStructureAt x (e 0) = e 1 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have h₂' : J.almostComplexStructureAt x (e 2) = e 3 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have horth := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀' h₂' u w
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using horth

/-- **Any nondegenerate two-form `σ` whose associated bilinear form `σ(·, J ·)` is the Riemannian
bundle metric and whose symplectic orientation agrees with `o` satisfies
`IsCompatibleOrientation o J`.** -/
theorem isCompatibleOrientation_of_symplectic (o : Manifold.Orientation I M (Fin (2 + 2)))
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {J : SmoothAlmostComplexStructure I M}
    (hg : ∀ (x : M) (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (ho : ∀ x : M,
      (letI : Fact (finrank ℝ (TangentSpace I x) = 4) := o.fact_finrank_tangentSpace x
       (hσ.symplecticFormAt x).orientation Fact.out) = o.orientationAt x) :
    IsCompatibleOrientation o J := by
  intro x
  let _ : Fact (finrank ℝ (TangentSpace I x) = 4) := o.fact_finrank_tangentSpace x
  have hg' : ∀ v w : TangentSpace I x,
      ⟪v, w⟫ = (hσ.symplecticFormAt x) v (J.almostComplexStructureAt x w) := fun v w ↦ by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
      hσ.symplecticFormAt_apply, hg x v w]
  obtain ⟨e, he, h₀, h₂⟩ := exists_orthonormalBasis_symplecticOrientation hg'
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] at h₀ h₂
  exact ⟨e, he.trans (ho x), h₀, h₂⟩

/-- Under `(alternatingFormEquiv _ 2).symm`, `-realAlternatingDerivation 2 J.toEndomorphism` of an
orthogonal `J` acts on two-forms as `exteriorPower.lieMap 2 J_x`. -/
private theorem alternatingFormEquiv_symm_neg_realAlternatingDerivation_two
    {J : SmoothAlmostComplexStructure I M}
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (η : SmoothForm I M ℝ 2) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     (alternatingFormEquiv (TangentSpace I x) 2).symm
       ((-realAlternatingDerivation 2 J.toEndomorphism η).1 x)) =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       exteriorPower.lieMap 2 (J.almostComplexStructureAt x).toLinearMap
         ((alternatingFormEquiv (TangentSpace I x) 2).symm (η.1 x))) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have hskew := AlmostComplexStructure.inner_apply_left (almostComplexStructureAt_inner hJ x)
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_alternatingFormEquiv_symm_ιMulti, inner_lieMap_left hskew,
    lieMap_two_apply_ιMulti, inner_add_right, inner_alternatingFormEquiv_symm_ιMulti,
    inner_alternatingFormEquiv_symm_ιMulti, Submodule.coe_neg, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, realAlternatingDerivation_apply, Fin.sum_univ_two]
  have hu0 : Function.update ![u, w] 0 (J.toEndomorphism x (![u, w] 0)) = ![J x u, w] :=
    funext fun i ↦ by fin_cases i <;> rfl
  have hu1 : Function.update ![u, w] 1 (J.toEndomorphism x (![u, w] 1)) = ![u, J x w] :=
    funext fun i ↦ by fin_cases i <;> rfl
  rw [hu0, hu1, SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
  rfl

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- The ambient smooth-form linear map underlying `deformationTargetComplexStructure` on
`Ω⁰(M) × Ω²(M)`. -/
private def deformationTargetAmbientMap (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) :
    SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2 →ₗ[ℝ]
      SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2 :=
  ((-((√2 / 2 : ℝ) • innerZeroForm (k := 2) (l := 2) o (kahlerTwoForm J hJ))) ∘ₗ
      LinearMap.snd ℝ (SmoothForm I M ℝ 0) (SmoothForm I M ℝ 2)).prod
    (((√2 / 2 : ℝ) • SmoothForm.wedge (kahlerTwoForm J hJ)) ∘ₗ
        LinearMap.fst ℝ (SmoothForm I M ℝ 0) (SmoothForm I M ℝ 2) -
      ((2⁻¹ : ℝ) • realAlternatingDerivation 2 J.toEndomorphism) ∘ₗ
        LinearMap.snd ℝ (SmoothForm I M ℝ 0) (SmoothForm I M ℝ 2))

private theorem deformationTargetAmbientMap_fst (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (p : SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2) :
    (deformationTargetAmbientMap o J hJ p).1 =
      -((√2 / 2 : ℝ) • innerZeroForm (k := 2) (l := 2) o (kahlerTwoForm J hJ) p.2) :=
  (rfl)

private theorem deformationTargetAmbientMap_snd (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
    (p : SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2) :
    (deformationTargetAmbientMap o J hJ p).2 =
      (√2 / 2 : ℝ) • SmoothForm.wedge (kahlerTwoForm J hJ) p.1 -
        (2⁻¹ : ℝ) • realAlternatingDerivation 2 J.toEndomorphism p.2 :=
  (rfl)

private theorem deformationTargetAmbientMap_fiberwise {J : SmoothAlmostComplexStructure I M}
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
  · rw [deformationTargetAmbientMap_fst, Submodule.coe_neg, Submodule.coe_smul, Pi.neg_apply,
      Pi.smul_apply, ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, innerZeroForm_apply, alternatingFormInner_apply,
      alternatingFormEquiv_symm_kahlerTwoForm, deformationComplexStructure_apply_fst]
  · have hwedge : ((kahlerTwoForm J hJ).wedge p.1).1 x =
        p.1.1 x 0 • (kahlerTwoForm J hJ).1 x := by
      ext w
      rw [SmoothForm.wedge_apply_zero_right, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
        mul_comm]
    have hsub : ((deformationTargetAmbientMap o J hJ p).2).1 x =
        (√2 / 2 * p.1.1 x 0) • (kahlerTwoForm J hJ).1 x +
          (2⁻¹ : ℝ) • (-realAlternatingDerivation 2 J.toEndomorphism p.2).1 x := by
      ext w
      rw [deformationTargetAmbientMap_snd, Submodule.coe_sub, Submodule.coe_smul,
        Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
        ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
        ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
        Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, hwedge,
        ContinuousAlternatingMap.smul_apply]
      simp only [smul_eq_mul]
      ring
    rw [hsub, map_add, map_smul, map_smul, alternatingFormEquiv_symm_kahlerTwoForm,
      alternatingFormEquiv_symm_neg_realAlternatingDerivation_two hJ,
      deformationComplexStructure_apply_snd]

private theorem deformationTargetAmbientMap_snd_mem_selfDualForms
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (deformationTargetAmbientMap o J hJo.inner_apply_apply
      (p.1, (p.2 : SmoothForm I M ℝ 2))).2 ∈
      SmoothForm.selfDualForms (I := I) (M := M) o := by
  rw [SmoothForm.mem_selfDualForms]
  apply Subtype.ext
  funext x
  let _ := o.fact_finrank_tangentSpace x
  have hkl : 2 + 2 = finrank ℝ (TangentSpace I x) := (o.fact_finrank_tangentSpace x).out.symm
  obtain ⟨e, he, h₀, h₂⟩ := hJo x
  have h₀' : J.almostComplexStructureAt x (e 0) = e 1 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have h₂' : J.almostComplexStructureAt x (e 2) = e 3 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have hp := hodgeStar_symm_selfDualForms o p.2 x
  have hfib := (Prod.mk.inj (deformationTargetAmbientMap_fiberwise o hJo.inner_apply_apply
    (p.1, (p.2 : SmoothForm I M ℝ 2)) x)).2
  have hsd := hodgeStar_deformationComplexStructure_snd hkl he h₀' h₂'
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
    (hJo : IsCompatibleOrientation o J) :
    Module.End ℝ (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :=
  let embed : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o →ₗ[ℝ]
      SmoothForm I M ℝ 0 × SmoothForm I M ℝ 2 :=
    (LinearMap.fst ℝ _ _).prod
      ((SmoothForm.selfDualForms (I := I) (M := M) o).subtype.comp (LinearMap.snd ℝ _ _))
  let F := deformationTargetAmbientMap o J hJo.inner_apply_apply ∘ₗ embed
  (LinearMap.fst ℝ _ _ ∘ₗ F).prod <|
    (LinearMap.snd ℝ _ _ ∘ₗ F).codRestrict _
      (deformationTargetAmbientMap_snd_mem_selfDualForms o J hJo)

private theorem deformationTargetLinearMap_fiberwise (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     ((deformationTargetLinearMap o J hJo p).1.1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         (((deformationTargetLinearMap o J hJo p).2 : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationComplexStructure (J.almostComplexStructureAt x)
         (p.1.1 x 0,
           (alternatingFormEquiv (TangentSpace I x) 2).symm ((p.2 : SmoothForm I M ℝ 2).1 x))) :=
  deformationTargetAmbientMap_fiberwise o hJo.inner_apply_apply (p.1, (p.2 : SmoothForm I M ℝ 2)) x

private theorem deformationTargetLinearMap_comp_self (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J) :
    deformationTargetLinearMap o J hJo ∘ₗ deformationTargetLinearMap o J hJo = -LinearMap.id := by
  refine LinearMap.ext fun p ↦ ext_deformationTarget o fun x ↦ ?_
  let _ := o.fact_finrank_tangentSpace x
  obtain ⟨e, he, h₀, h₂⟩ := hJo x
  have h₀' : J.almostComplexStructureAt x (e 0) = e 1 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have h₂' : J.almostComplexStructureAt x (e 2) = e 3 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  rw [LinearMap.comp_apply, deformationTargetLinearMap_fiberwise,
    deformationTargetLinearMap_fiberwise,
    deformationComplexStructure_deformationComplexStructure
      (o.fact_finrank_tangentSpace x).out.symm he h₀' h₂' (hodgeStar_symm_selfDualForms o p.2 x)]
  refine Prod.ext ?_ ?_
  · simp
  · simp [map_neg]

/-- **The global almost complex structure `J′` on `Ω⁰(M) × Ω⁺(M)`** induced by a metric- and
orientation-compatible smooth almost complex structure `J` on `(M, g, o)`. At every point `x : M`,
it acts on `(g(x), η_x)` as `deformationSelfDualComplexStructure` on `ℝ × Λ⁺_x`. -/
def deformationTargetComplexStructure (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J) :
    AlmostComplexStructure
      (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) where
  toLinearMap := deformationTargetLinearMap o J hJo
  square_neg := deformationTargetLinearMap_comp_self o J hJo

/-- **Fibrewise formula for `deformationTargetComplexStructure`:** at every point `x : M`,
`deformationTargetComplexStructure o J hJo` acts as `deformationComplexStructure
(J.almostComplexStructureAt x)`. -/
theorem deformationTargetComplexStructure_fiberwise (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
    (letI := o.fact_finrank_tangentSpace x
     ((deformationTargetComplexStructure o J hJo p).1.1 x 0,
       (alternatingFormEquiv (TangentSpace I x) 2).symm
         (((deformationTargetComplexStructure o J hJo p).2 : SmoothForm I M ℝ 2).1 x))) =
      (letI := o.fact_finrank_tangentSpace x
       deformationComplexStructure (J.almostComplexStructureAt x)
         (p.1.1 x 0,
           (alternatingFormEquiv (TangentSpace I x) 2).symm ((p.2 : SmoothForm I M ℝ 2).1 x))) :=
  deformationTargetLinearMap_fiberwise o J hJo p x

/-- **Pointwise orthogonality of `deformationTargetComplexStructure`:** at every point `x : M`,
`J′` preserves the pointwise inner product `(p, q) ↦ p.1(x) q.1(x) + ⟨p.2(x), q.2(x)⟩` on
`Ω⁰(M) × Ω⁺(M)`. -/
theorem inner_deformationTargetComplexStructure (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J)
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
  obtain ⟨e, he, h₀, h₂⟩ := hJo x
  have h₀' : J.almostComplexStructureAt x (e 0) = e 1 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have h₂' : J.almostComplexStructureAt x (e 2) = e 3 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have hfp := deformationTargetComplexStructure_fiberwise o J hJo p x
  have hfq := deformationTargetComplexStructure_fiberwise o J hJo q x
  rw [alternatingFormInner_apply, alternatingFormInner_apply,
    (Prod.mk.inj hfp).1, (Prod.mk.inj hfp).2, (Prod.mk.inj hfq).1, (Prod.mk.inj hfq).2]
  exact inner_deformationComplexStructure (o.fact_finrank_tangentSpace x).out.symm he h₀' h₂'
    (hodgeStar_symm_selfDualForms o p.2 x)

/-- `deformationTargetComplexStructure o J hJo` commutes with right multiplication by smooth
functions (`C^∞(M)`-linearity). -/
theorem deformationTargetComplexStructure_mulRight (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J) (f : SmoothForm I M ℝ 0)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    deformationTargetComplexStructure o J hJo (deformationTargetMulRight o f p) =
      deformationTargetMulRight o f (deformationTargetComplexStructure o J hJo p) := by
  have hmulfib (r : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) (x : M) :
      (letI := o.fact_finrank_tangentSpace x
       ((deformationTargetMulRight o f r).1.1 x 0,
         (alternatingFormEquiv (TangentSpace I x) 2).symm
           (((deformationTargetMulRight o f r).2 : SmoothForm I M ℝ 2).1 x))) =
        (letI := o.fact_finrank_tangentSpace x
         f.1 x 0 • (r.1.1 x 0,
           (alternatingFormEquiv (TangentSpace I x) 2).symm
             ((r.2 : SmoothForm I M ℝ 2).1 x))) := by
    let _ := o.fact_finrank_tangentSpace x
    refine Prod.ext ?_ ?_
    · rw [deformationTargetMulRight_apply_fst, SmoothForm.wedge_apply_zero_right, Prod.smul_fst,
        smul_eq_mul, mul_comm]
    · have hw : (SmoothForm.wedge (r.2 : SmoothForm I M ℝ 2) f).1 x =
          f.1 x 0 • (r.2 : SmoothForm I M ℝ 2).1 x := by
        ext v
        rw [SmoothForm.wedge_apply_zero_right, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
          mul_comm]
      rw [coe_deformationTargetMulRight_apply_snd, hw, map_smul, Prod.smul_snd]
  refine ext_deformationTarget o fun x ↦ ?_
  let _ := o.fact_finrank_tangentSpace x
  rw [deformationTargetComplexStructure_fiberwise, hmulfib p x, map_smul,
    ← deformationTargetComplexStructure_fiberwise, hmulfib _ x]

end Target

end AlmostComplex

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
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  TauCeti.complexLinearPart (covectorComplexStructure J).toLinearMap
    (deformationTargetComplexStructure o J hJo).toLinearMap (asdDeformationOperator o)

/-- Unfolding `complexDeformationOperator` as `(2⁻¹ : ℝ) • (δ₀ a - J′ (δ₀ (J₁ a)))`. -/
theorem complexDeformationOperator_apply (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J)
    (a : SmoothForm I M ℝ 1) :
    complexDeformationOperator o J hJo a =
      (2⁻¹ : ℝ) • (asdDeformationOperator o a -
        deformationTargetComplexStructure o J hJo
          (asdDeformationOperator o (covectorComplexStructure J a))) :=
  TauCeti.complexLinearPart_apply _ _ _ a

/-- **`δ_ω` is complex linear** with respect to `covectorComplexStructure J` on `Ω¹(M)` and
`deformationTargetComplexStructure o J hJo` on `Ω⁰(M) × Ω⁺(M)`. -/
theorem isComplexLinearMap_complexDeformationOperator (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) :
    IsComplexLinearMap (covectorComplexStructure J) (deformationTargetComplexStructure o J hJo)
      (complexDeformationOperator o J hJo) :=
  TauCeti.complexLinearPart_isComplexLinear (covectorComplexStructure J).square_neg
    (deformationTargetComplexStructure o J hJo).square_neg (asdDeformationOperator o)

/-- The difference `δ_ω - δ₀` is minus the `(J₁, J′)`-complex-antilinear part of `δ₀`. -/
theorem complexDeformationOperator_sub_asdDeformationOperator_eq_neg_complexAntilinearPart
    (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J) :
    complexDeformationOperator o J hJo - asdDeformationOperator o =
      -TauCeti.complexAntilinearPart (covectorComplexStructure J).toLinearMap
        (deformationTargetComplexStructure o J hJo).toLinearMap (asdDeformationOperator o) := by
  have key {x y z : SmoothForm I M ℝ 1 →ₗ[ℝ]
      SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o}
      (h : x + y = z) : x - z = -y := by
    subst h
    abel
  exact key (TauCeti.complexLinearPart_add_complexAntilinearPart
    (covectorComplexStructure J).toLinearMap
    (deformationTargetComplexStructure o J hJo).toLinearMap (asdDeformationOperator o))

/-- **`δ_ω` and `δ₀` have the exact same commutator with multiplication by smooth functions:**
`δ_ω(a ∧ f) - δ_ω(a) ∧ f = δ₀(a ∧ f) - δ₀(a) ∧ f`. -/
theorem complexDeformationOperator_commutator_eq (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J)
    (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    complexDeformationOperator o J hJo (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (complexDeformationOperator o J hJo a) =
      asdDeformationOperator o (SmoothForm.wedge a f) -
        deformationTargetMulRight o f (asdDeformationOperator o a) := by
  set C : SmoothForm I M ℝ 1 →
      SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
    fun b ↦ asdDeformationOperator o (SmoothForm.wedge b f) -
      deformationTargetMulRight o f (asdDeformationOperator o b)
  have hcomm : complexDeformationOperator o J hJo (SmoothForm.wedge a f) -
      deformationTargetMulRight o f (complexDeformationOperator o J hJo a) =
      (2⁻¹ : ℝ) • (C a - deformationTargetComplexStructure o J hJo
        (C (covectorComplexStructure J a))) := by
    rw [complexDeformationOperator_apply, complexDeformationOperator_apply,
      covectorComplexStructure_wedge_zero_right, map_smul, map_sub,
      ← deformationTargetComplexStructure_mulRight]
    simp only [C, map_sub]
    module
  rw [hcomm]
  refine ext_deformationTarget o fun x ↦ ?_
  let _ := o.fact_finrank_tangentSpace x
  obtain ⟨e, he, h₀, h₂⟩ := hJo x
  have h₀' : J.almostComplexStructureAt x (e 0) = e 1 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  have h₂' : J.almostComplexStructureAt x (e 2) = e 3 := by
    rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  set ξ := Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)
  set v := Riemannian.Tensor.rieszDual (I := I) x (SmoothForm.degreeOneEquiv a x)
  have hCa := asdDeformationOperator_commutator_eq_deformationSymbol o a f x
  have hCJa := asdDeformationOperator_commutator_eq_deformationSymbol o
    (covectorComplexStructure J a) f x
  rw [rieszDual_covectorComplexStructure hJo.inner_apply_apply a x,
    ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply] at hCJa
  have hJCJa := deformationTargetComplexStructure_fiberwise o J hJo
    (C (covectorComplexStructure J a)) x
  have hpair (p q : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
      ((((2⁻¹ : ℝ) • (p - q)).1).1 x 0,
        (alternatingFormEquiv (TangentSpace I x) 2).symm
          ((((2⁻¹ : ℝ) • (p - q)).2 : SmoothForm I M ℝ 2).1 x)) =
      (2⁻¹ : ℝ) • ((p.1.1 x 0,
          (alternatingFormEquiv (TangentSpace I x) 2).symm
            ((p.2 : SmoothForm I M ℝ 2).1 x)) -
        (q.1.1 x 0,
          (alternatingFormEquiv (TangentSpace I x) 2).symm
            ((q.2 : SmoothForm I M ℝ 2).1 x))) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp [map_smul, map_sub]
  rw [hpair, hJCJa, hCa, hCJa]
  exact two_inv_smul_sub_deformationComplexStructure_deformationSymbol
    (o.fact_finrank_tangentSpace x).out.symm he h₀' h₂' ξ v

/-- **`δ_ω - δ₀` is `C^∞(M)`-linear (an operator of order zero):** it commutes with right
multiplication by any smooth function `f ∈ Ω⁰(M)`. -/
theorem complexDeformationOperator_sub_asdDeformationOperator_wedge
    (o : Manifold.Orientation I M (Fin (2 + 2))) (J : SmoothAlmostComplexStructure I M)
    (hJo : IsCompatibleOrientation o J) (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    (complexDeformationOperator o J hJo - asdDeformationOperator o) (SmoothForm.wedge a f) =
      deformationTargetMulRight o f
        ((complexDeformationOperator o J hJo - asdDeformationOperator o) a) := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, sub_eq_sub_iff_sub_eq_sub]
  exact complexDeformationOperator_commutator_eq o J hJo a f

/-- **The linear deformation homotopy** `δ_t = (1 - t) δ₀ + t δ_ω` (`t ∈ ℝ`) interpolating between
the real Atiyah–Hitchin–Singer operator `δ₀` (`t = 0`) and Taubes's complex-linear operator `δ_ω`
(`t = 1`). -/
def deformationHomotopy (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) (t : ℝ) :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  (1 - t) • asdDeformationOperator o + t • complexDeformationOperator o J hJo

@[simp]
theorem deformationHomotopy_zero (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) :
    deformationHomotopy o J hJo 0 = asdDeformationOperator o := by
  simp [deformationHomotopy]

@[simp]
theorem deformationHomotopy_one (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) :
    deformationHomotopy o J hJo 1 = complexDeformationOperator o J hJo := by
  simp [deformationHomotopy]

/-- `δ_t = δ₀ + t (δ_ω - δ₀)`: the homotopy perturbs `δ₀` by `t` times the order-zero operator
`δ_ω - δ₀`. -/
theorem deformationHomotopy_eq_add_smul_sub (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) (t : ℝ) :
    deformationHomotopy o J hJo t =
      asdDeformationOperator o +
        t • (complexDeformationOperator o J hJo - asdDeformationOperator o) := by
  rw [deformationHomotopy]
  module

/-- **Invariance of the principal symbol along `deformationHomotopy`:** for every `t : ℝ`,
`[δ_t, · ∧ f] = [δ₀, · ∧ f]`. -/
theorem deformationHomotopy_commutator_eq (o : Manifold.Orientation I M (Fin (2 + 2)))
    (J : SmoothAlmostComplexStructure I M) (hJo : IsCompatibleOrientation o J) (t : ℝ)
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
    (hJo : IsCompatibleOrientation o J) (t : ℝ) (a : SmoothForm I M ℝ 1)
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
