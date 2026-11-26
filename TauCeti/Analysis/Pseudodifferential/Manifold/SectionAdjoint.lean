/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle
public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
import TauCeti.Analysis.InnerProductSpace.Complex
import TauCeti.Geometry.Manifold.PartitionOfUnity.Square
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# Formal adjoints of pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E` and `F` be smooth complex vector bundles of finite
rank over `M` and let `μ` be a measure on `M` with a smooth positive density
(`TauCeti.HasSmoothPositiveDensity`). The fibres carry smooth real inner products that are
invariant under multiplication by `i`; these are exactly the real parts of Hermitian metrics
`⟪v, w⟫_ℂ = ⟪v, w⟫ - i ⟪v, i w⟫` (`TauCeti.extendRCLike_innerₗ_apply`). An operator
`Q : Γ(F) → Γ(E)` is a formal adjoint of `P : Γ(E) → Γ(F)` when `∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ`
for compactly supported smooth sections (`LinearMap.IsFormalAdjoint`, for the real inner
products). For complex-linear `P` and `Q` this is the same as the identity for the Hermitian
metrics, since the imaginary part of `⟪v, w⟫_ℂ` is `-⟪v, i w⟫`.

This file shows that a properly supported formal adjoint of a classical pseudodifferential
operator `P` of order `m` from `E` to `F` (`TauCeti.sectionClassicalPseudodifferentialOperators`)
is a classical pseudodifferential operator of order `m` from `F` to `E`
(`TauCeti.mem_sectionClassicalPseudodifferentialOperators_of_isFormalAdjoint`). This is the bundle
form of the scalar theorem
`TauCeti.mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq`, to which it is
reduced. As there, proper support of `Q` is a hypothesis: the adjoint identity only involves the
values of `Q` on compactly supported sections.

## The argument

An entry `f ↦ χ ℓ(t' (Q (f ψ t⁻¹ w)))` of `Q` (`TauCeti.sectionEntry`) is read on functions `f`
supported in a compact set `K`, on which `ψ t⁻¹ w` may be replaced by a compactly supported
section `σ` (`IsCompact.exists_isCompact_tsupport_forall_smul_eq`). The values `y = Q (f σ) x`
then lie over a compact set `K'`. Cover it by open sets carrying real orthonormal frames `(e a)`
of `E` (`TauCeti.exists_nhds_orthonormal_sections`), with functions `gᵢ` such that `∑ᵢ gᵢ² = 1`
on `K'` (`IsCompact.exists_sum_sq_eq_one`). In a real orthonormal basis every complex-linear
functional `λ` is `λ y = ½ ∑ₐ λ (e a) ⟪e a, y⟫_ℂ`
(`OrthonormalBasis.eq_sum_mul_extendRCLike_innerₗ`), so with `λ = ℓ ∘ t'ₓ` the entry is a sum of
smooth multiples of the operators
`f ↦ ⟪s, Q (f σ)⟫_ℂ` for the compactly supported sections `s = gᵢ e a`.

Each of these is a properly supported formal adjoint, for `μ`, of the scalar operator
`g ↦ ⟪σ, P (g s)⟫_ℂ`: the Hermitian metrics are conjugate-linear in the first argument and
Hermitian (`TauCeti.extendRCLike_innerₗ_smul_left`, `TauCeti.conj_extendRCLike_innerₗ`), which
turns the scalar adjoint identity into the adjoint identity of `P` and `Q` for the sections `g s`
and `f σ`. Over the support of `σ`, the pairing with `σ` is a sum of cut-off frame coefficients
with smooth coefficients, so `g ↦ ⟪σ, P (g s)⟫_ℂ` is a classical pseudodifferential operator of
order `m` by
`TauCeti.cutoffFrameCoeff_comp_comp_toSpanSingleton_mem_classicalPseudodifferentialOperators`.
The scalar theorem then applies.

## Main results

* `TauCeti.mem_sectionClassicalPseudodifferentialOperators_of_isFormalAdjoint`: a properly
  supported formal adjoint of a classical pseudodifferential operator of order `m` between vector
  bundles is a classical pseudodifferential operator of order `m`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7
  (adjoints on `ℝⁿ`) and §18.1 after Definition 18.1.20 (operators between sections of vector
  bundles).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3) and §8.
-/

public section

noncomputable section

open Bundle Set MeasureTheory TauCeti
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

/-! ### Pairing sections -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [FiberBundle V E] [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, NormedAddCommGroup (F x)]
  [∀ x, InnerProductSpace ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, IsScalarTower ℝ ℂ (F x)]
  [FiberBundle W F] [VectorBundle ℝ W F] [VectorBundle ℂ W F]

section SectionPairing

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, CoordinateSpace n) ∞ V E]

/-- The pointwise pairing `x ↦ ⟪s x, r x⟫_ℂ` of two smooth sections, a smooth function. -/
private def pairingFun (s r : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨fun x ↦ Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ _ (s x)) (r x), by
    have h₁ := s.contMDiff.inner_bundle r.contMDiff
    have h₂ := s.contMDiff.inner_bundle (Complex.I • r).contMDiff
    refine ((Complex.ofRealCLM.contMDiff.comp h₁).sub
      ((contMDiff_const (c := Complex.I)).mul (Complex.ofRealCLM.contMDiff.comp h₂))).congr
      fun x ↦ ?_
    simp [extendRCLike_innerₗ_apply]⟩

private theorem pairingFun_apply (s r : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (x : M) :
    pairingFun s r x = Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ _ (s x)) (r x) :=
  (rfl)

/-- Pairing with a fixed smooth section `s`, `r ↦ (x ↦ ⟪s x, r x⟫_ℂ)`, as a complex-linear map from
smooth sections to complex-valued smooth functions. -/
private def pairingSection (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := pairingFun s
  map_add' r r' := by
    ext x
    simp [pairingFun_apply]
  map_smul' c r := by
    ext x
    simp [pairingFun_apply, ContMDiffMap.complex_smul_apply]

private theorem pairingSection_apply (s r : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (x : M) :
    pairingSection s r x = Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ _ (s x)) (r x) :=
  (rfl)

end SectionPairing

/-! ### Formal adjoints -/

section Adjoint

variable [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, CoordinateSpace n) ∞ V E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, CoordinateSpace n) ∞ W F] {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
  {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}

omit [∀ x, IsScalarTower ℝ ℂ (E x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, CoordinateSpace n) ∞ V E] in
/-- Reading `P` along a section `s` of `E` and pairing the result with a compactly supported section
`σ` of `F`, `f ↦ ⟪σ, P (f · s)⟫_ℂ`, gives a classical pseudodifferential operator of order `m`: over
the support of `σ`, the pairing with `σ` is a sum of cut-off frame coefficients with smooth
coefficients. -/
private theorem pairingSection_comp_comp_toSpanSingleton_mem [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {σ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hσ : IsCompact σ.tsupport) :
    pairingSection σ ∘ₗ P ∘ₗ (LinearMap.toSpanSingleton _ _ s).restrictScalars ℂ ∈
      classicalPseudodifferentialOperators m := by
  set b := Module.finBasis ℂ W
  obtain ⟨ι, _, c, ρ, ψ, hρ, hψ, hsum⟩ :=
    hσ.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
      (I := 𝓘(ℝ, CoordinateSpace n)) (F := F) b
  have heq : pairingSection σ ∘ₗ P ∘ₗ
      (LinearMap.toSpanSingleton C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ _ s).restrictScalars
        ℂ =
      ∑ i, ∑ j, LinearMap.mulLeft ℂ (pairingSection σ
        ((trivializationAt W F (c i)).cutoffFrameSection (ψ i) (hψ i) (b j))) ∘ₗ
          ((trivializationAt W F (c i)).cutoffFrameCoeff (ρ i) (hρ i)
            (b.coord j).toContinuousLinearMap ∘ₗ P ∘ₗ
              (LinearMap.toSpanSingleton _ _ s).restrictScalars ℂ) := by
    refine LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply, LinearMap.sum_apply, ContMDiffMap.coe_sum,
      Finset.sum_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      pairingSection_apply]
    by_cases hx : x ∈ σ.tsupport
    · -- Over the support of `σ`, `P (f s)` is the sum of its cut-off frame expansion.
      rw [← hsum (P (f • s)) x hx, ContMDiffSection.coe_sum, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ContMDiffSection.coe_sum, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ContMDiffSection.smul_apply_of_normedAlgebra, map_smul, smul_eq_mul, mul_comm]
    · simp only [extendRCLike_innerₗ_apply, σ.eq_zero_of_notMem_tsupport hx, inner_zero_left,
        Complex.ofReal_zero, mul_zero, sub_zero, zero_mul, Finset.sum_const_zero]
  rw [heq]
  exact sum_mem fun i _ ↦ sum_mem fun j _ ↦ mulLeft_comp_mem_classicalPseudodifferentialOperators
    (cutoffFrameCoeff_comp_comp_toSpanSingleton_mem_classicalPseudodifferentialOperators _ _ _ _
      hP s) _

omit [∀ x, IsScalarTower ℝ ℂ (F x)] [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, CoordinateSpace n) ∞ W F] in
/-- Reading a properly supported operator `Q` along a section `σ` and pairing the result with a
section `s`, `f ↦ ⟪s, Q (f · σ)⟫_ℂ`, gives a properly supported operator. -/
private theorem isProperlySupported_pairingSection_comp_comp_toSpanSingleton
    (hQ : IsSectionProperlySupported Q) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯)
    (σ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) :
    IsProperlySupported (pairingSection s ∘ₗ Q ∘ₗ
      (LinearMap.toSpanSingleton _ _ σ).restrictScalars ℂ) := by
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  obtain ⟨K', hK', hQ₁, hQ₂⟩ := isSectionProperlySupported_iff.1 hQ K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · have h₂ := hQ₁ _ ((ContMDiffSection.tsupport_smul_function_subset_of_normedAlgebra f
      σ).trans (inter_subset_left.trans hf))
    rw [ContMDiffSection.tsupport_def] at h₂
    refine (closure_mono fun y hy ↦ ?_).trans h₂
    simp only [Function.mem_support, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply, pairingSection_apply] at hy
    exact fun h ↦ hy (by rw [h, map_zero])
  · have h := hQ₂ (f • σ) (hf.mono fun y hy ↦ by simp [hy]) x hx
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply]
    rw [pairingSection_apply, h, map_zero]

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
/-- **Integration by parts for the complex pairings.** If `Q` is a formal adjoint of `P` for the
real inner products, then `∫ ⟪P a, b⟫_ℂ dμ = ∫ ⟪a, Q b⟫_ℂ dμ` for the complex pairings, for
compactly supported sections `a` and `b`. -/
private theorem integral_pairing_eq [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M}
    [IsFiniteMeasureOnCompacts μ]
    (hPQ : (P.restrictScalars ℝ).IsFormalAdjoint (Q.restrictScalars ℝ) μ)
    {a : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯} (ha : IsCompact a.tsupport)
    {b : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯} (hb : IsCompact b.tsupport) :
    ∫ x, pairingSection (P a) b x ∂μ = ∫ x, pairingSection a (Q b) x ∂μ := by
  have hb' : IsCompact (Complex.I • b).tsupport := by
    rwa [ContMDiffSection.tsupport_smul_of_normedAlgebra _ _ Complex.I_ne_zero]
  -- The real pairings are continuous with compact support, hence integrable.
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := 𝓘(ℝ, CoordinateSpace n)) (n := ∞) (F := V) (V := E)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := 𝓘(ℝ, CoordinateSpace n)) (n := ∞) (F := W) (V := F)
  have hP' (x : M) : pairingSection (P a) b x =
      (⟪P a x, b x⟫ : ℂ) - Complex.I * (⟪P a x, (Complex.I • b) x⟫ : ℂ) := by
    rw [pairingSection_apply, extendRCLike_innerₗ_apply,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply]
  have hQ' (x : M) : pairingSection a (Q b) x =
      (⟪a x, Q b x⟫ : ℂ) - Complex.I * (⟪a x, Q (Complex.I • b) x⟫ : ℂ) := by
    rw [pairingSection_apply, extendRCLike_innerₗ_apply, map_smul,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply]
  simp only [hP', hQ']
  rw [integral_sub (ContMDiffSection.integrable_inner (Or.inr hb)).ofReal
      ((ContMDiffSection.integrable_inner (Or.inr hb')).ofReal.const_mul _),
    integral_sub (ContMDiffSection.integrable_inner (Or.inl ha)).ofReal
      ((ContMDiffSection.integrable_inner (Or.inl ha)).ofReal.const_mul _),
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]
  have h₁ := hPQ.integral_inner_eq (s := a) (t := b) (Or.inl ha)
  have h₂ := hPQ.integral_inner_eq (s := a) (t := Complex.I • b) (Or.inl ha)
  simp only [LinearMap.coe_restrictScalars] at h₁ h₂
  rw [h₁, h₂]

/-- Reading `Q` along a compactly supported section `σ` of `F` and pairing the result with a
compactly supported section `s` of `E`, `f ↦ ⟪s, Q (f · σ)⟫_ℂ`, gives a classical
pseudodifferential operator of order `m`: it is a properly supported formal adjoint of the
operator `g ↦ ⟪σ, P (g · s)⟫_ℂ` of `TauCeti.pairingSection_comp_comp_toSpanSingleton_mem`. -/
private theorem pairingSection_comp_comp_toSpanSingleton_mem_of_isFormalAdjoint
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [MeasurableSpace M] [OpensMeasurableSpace M]
    {μ : Measure M} [IsFiniteMeasureOnCompacts μ]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hE : ∀ x (v w : E x), ⟪Complex.I • v, Complex.I • w⟫ = ⟪v, w⟫)
    (hF : ∀ x (v w : F x), ⟪Complex.I • v, Complex.I • w⟫ = ⟪v, w⟫)
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hQ : IsSectionProperlySupported Q)
    (hPQ : (P.restrictScalars ℝ).IsFormalAdjoint (Q.restrictScalars ℝ) μ)
    {s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯} (hs : IsCompact s.tsupport)
    {σ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯} (hσ : IsCompact σ.tsupport) :
    pairingSection s ∘ₗ Q ∘ₗ
      (LinearMap.toSpanSingleton _ _ σ).restrictScalars ℂ ∈
        classicalPseudodifferentialOperators m := by
  refine mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq hμ
    (pairingSection_comp_comp_toSpanSingleton_mem hP s hσ)
    (isProperlySupported_pairingSection_comp_comp_toSpanSingleton hQ s σ) fun u v _ _ ↦ ?_
  have ha : IsCompact (u • s).tsupport := hs.of_isClosed_subset
    (ContMDiffSection.isClosed_tsupport _)
    ((ContMDiffSection.tsupport_smul_function_subset_of_normedAlgebra u s).trans inter_subset_right)
  have hb : IsCompact (v • σ).tsupport := hσ.of_isClosed_subset
    (ContMDiffSection.isClosed_tsupport _)
    ((ContMDiffSection.tsupport_smul_function_subset_of_normedAlgebra v σ).trans inter_subset_right)
  -- Pointwise, the two integrands are the complex pairings of `integral_pairing_eq`.
  have h₁ (x : M) : inner ℂ (pairingSection σ (P (u • s)) x) (v x) =
      pairingSection (P (u • s)) (v • σ) x := by
    rw [pairingSection_apply, pairingSection_apply, RCLike.inner_apply',
      conj_extendRCLike_innerₗ (hF x), ContMDiffSection.smul_apply_of_normedAlgebra,
      (Module.Dual.extendRCLike (innerₗ _ (P (u • s) x))).map_smul, smul_eq_mul, mul_comm]
  have h₂ (x : M) : inner ℂ (u x) (pairingSection s (Q (v • σ)) x) =
      pairingSection (u • s) (Q (v • σ)) x := by
    rw [pairingSection_apply, pairingSection_apply, RCLike.inner_apply',
      ContMDiffSection.smul_apply_of_normedAlgebra, extendRCLike_innerₗ_smul_left (hE x)]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, h₁, h₂]
  exact integral_pairing_eq hPQ ha hb

omit [∀ x, IsScalarTower ℝ ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (F x)] in
/-- The fibrewise expansion behind
`TauCeti.mem_sectionClassicalPseudodifferentialOperators_of_isFormalAdjoint`: if `∑ᵢ rᵢ² = 1` and
`(eᵢ a)ₐ` is a real orthonormal basis whenever `rᵢ ≠ 0`, then every complex-linear functional is
`l y = ∑ᵢ ∑ₐ ½ rᵢ l (eᵢ a) ⟪rᵢ eᵢ a, y⟫_ℂ`. -/
private theorem sum_sum_mul_extendRCLike_innerₗ_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G] {ι κ : Type*} [Fintype ι]
    [Fintype κ] {r : ι → ℝ} (hr : ∑ i, r i ^ 2 = 1) {e : ι → κ → G}
    (he : ∀ i, r i ≠ 0 → Orthonormal ℝ (e i) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (e i)))
    (l : Module.Dual ℂ G) (y : G) :
    ∑ i, ∑ a, 2⁻¹ * (r i * l (e i a)) *
      Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ G (r i • e i a)) y = l y := by
  have key (i : ι) : ∑ a, 2⁻¹ * (r i * l (e i a)) *
      Module.Dual.extendRCLike (𝕜 := ℂ) (innerₗ G (r i • e i a)) y = ((r i ^ 2 : ℝ) : ℂ) * l y := by
    by_cases hri : r i = 0
    · simp [hri]
    obtain ⟨hon, hsp⟩ := he i hri
    rw [(OrthonormalBasis.mk hon hsp).eq_sum_mul_extendRCLike_innerₗ l y, OrthonormalBasis.coe_mk,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [extendRCLike_innerₗ_apply, real_inner_smul_left]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ key i, ← Finset.sum_mul, ← Complex.ofReal_sum, hr,
    Complex.ofReal_one, one_mul]

/-- **Formal adjoints of pseudodifferential operators between vector bundles.** Let `E` and `F` be
smooth complex vector bundles of finite rank over a manifold `M` modelled on `ℝⁿ`, whose fibres
carry smooth real inner products invariant under multiplication by `i`, the real parts of
Hermitian metrics, and let `μ` be a measure on `M`, finite on compact sets, with a smooth positive
density (`TauCeti.HasSmoothPositiveDensity`). If `P : Γ(E) → Γ(F)` is a classical
pseudodifferential operator of order `m` and `Q : Γ(F) → Γ(E)` is a properly supported formal
adjoint of `P` for these inner products and `μ` (`LinearMap.IsFormalAdjoint`), then `Q` is a
classical pseudodifferential operator of order `m`. -/
theorem mem_sectionClassicalPseudodifferentialOperators_of_isFormalAdjoint
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [MeasurableSpace M] [OpensMeasurableSpace M]
    {μ : Measure M} [IsFiniteMeasureOnCompacts μ]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hE : ∀ x (v w : E x), ⟪Complex.I • v, Complex.I • w⟫ = ⟪v, w⟫)
    (hF : ∀ x (v w : F x), ⟪Complex.I • v, Complex.I • w⟫ = ⟪v, w⟫)
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hQ : IsSectionProperlySupported Q)
    (hPQ : (P.restrictScalars ℝ).IsFormalAdjoint (Q.restrictScalars ℝ) μ) :
    Q ∈ sectionClassicalPseudodifferentialOperators m := by
  refine mem_sectionClassicalPseudodifferentialOperators_iff.2
    ⟨hQ, fun t _ ψ hψ w t' _ χ hχ ℓ ↦ ?_⟩
  refine mem_classicalPseudodifferentialOperators_iff_forall_isCompact.2
    ⟨hQ.sectionEntry t ψ hψ w t' χ hχ ℓ, fun K hK ↦ ?_⟩
  -- On functions supported in `K`, the cut-off frame section `ψ t⁻¹ w` may be replaced by a
  -- section `σ` with compact support. The outputs `Q (f σ)` are then supported in a compact set
  -- `K'`, covered by finitely many open sets `N (c i)` carrying orthonormal frames `e (c i)`, with
  -- `∑ᵢ gᵢ² = 1` on `K'`.
  obtain ⟨σ, hσ, hfσ⟩ := hK.exists_isCompact_tsupport_forall_smul_eq (t.cutoffFrameSection ψ hψ w)
  obtain ⟨K', hK', hQK', -⟩ := isSectionProperlySupported_iff.1 hQ K hK
  choose N hN _ e he using fun x : M ↦ exists_nhds_orthonormal_sections
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞) (F := V) (V := E) x
  obtain ⟨ι, _, c, g, hg, hg1⟩ :=
    hK'.exists_sum_sq_eq_one 𝓘(ℝ, CoordinateSpace n) (U := N) fun x _ ↦ hN x
  -- The entry of `Q` at `x` is `χ λ(y)` for `y = Q (f σ) x` and `λ = ℓ ∘ t'ₓ`. Expanding `λ` in
  -- the orthonormal frames, it is a sum of multiples of the pairings of `y` with the sections
  -- `gᵢ e (c i) a`, each of which is a pseudodifferential operator of order `m`.
  have hs (i : ι) (a : Fin (Module.finrank ℝ V)) : IsCompact (g i • e (c i) a).tsupport :=
    (hg i).1.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
      ((ContMDiffSection.tsupport_smul_function_subset _ _).trans inter_subset_left)
  set coef : ι → Fin (Module.finrank ℝ V) → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    fun i a ↦ (2⁻¹ : ℂ) • (ContMDiffMap.ofReal (g i) * t'.cutoffFrameCoeff χ hχ ℓ (e (c i) a))
  refine ⟨∑ i, ∑ a, LinearMap.mulLeft ℂ (coef i a) ∘ₗ (pairingSection (g i • e (c i) a) ∘ₗ Q ∘ₗ
      (LinearMap.toSpanSingleton _ _ σ).restrictScalars ℂ),
    sum_mem fun i _ ↦ sum_mem fun a _ ↦ mulLeft_comp_mem_classicalPseudodifferentialOperators
      (pairingSection_comp_comp_toSpanSingleton_mem_of_isFormalAdjoint hμ hE hF hP hQ hPQ
        (hs i a) hσ) _,
    fun f hf ↦ ContMDiffMap.ext fun x ↦ ?_⟩
  simp only [sectionEntry_apply, hfσ f hf, LinearMap.sum_apply, ContMDiffMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul,
    Pi.mul_apply, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply,
    pairingSection_apply]
  by_cases hy : Q (f • σ) x = 0
  · simp [hy]
  have hxK' : x ∈ K' := hQK' (f • σ)
    ((ContMDiffSection.tsupport_smul_function_subset_of_normedAlgebra f σ).trans
      (inter_subset_left.trans hf))
    (by rw [ContMDiffSection.tsupport_def]; exact subset_closure hy)
  have h := sum_sum_mul_extendRCLike_innerₗ_eq (hg1 x hxK')
    (fun i hi ↦ he (c i) x ((hg i).2 (subset_tsupport _ hi)))
    (χ x • (ℓ.comp (t'.continuousLinearMapAt ℂ x)).toLinearMap) (Q (f • σ) x)
  simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
    Function.comp_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  simp [coef, ContMDiffMap.complex_smul_apply, mul_assoc]

end Adjoint

end TauCeti
