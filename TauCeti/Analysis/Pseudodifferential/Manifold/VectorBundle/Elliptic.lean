/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.SymbolQuantization
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Parametrices of elliptic operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. A classical pseudodifferential operator
`P : Γ(E) → Γ(F)` of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`) is
elliptic (`TauCeti.IsSectionClassicalElliptic`) when its principal symbol
`σ_m(P)(x, ξ) : E_x → F_x` is bijective at every nonzero covector `ξ ∈ T*ₓM`. This file constructs
parametrices of elliptic operators between bundles on a compact manifold: operators
`Q : Γ(F) → Γ(E)` of order `-m` inverting `P` on both sides modulo operators of order `-∞`. They
are the bundle counterpart of the scalar parametrices of `Manifold/Parametrix.lean`, and the input
of the elliptic estimates and of the Fredholm theory of `P` between Sobolev spaces of sections.

**The inverse principal symbol is a symbol.** The fibrewise inverses `σ_m(P)(x, ξ)⁻¹ : F_x → E_x`
form a smooth positively homogeneous `Hom(F, E)`-valued symbol of degree `-m`
(`TauCeti.IsSectionClassicalElliptic.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`), in
the sense of `TauCeti.sectionHomogeneousCotangentSymbols`: all its readings
`(x, ξ) ↦ χ(x) ψ(x) ℓ(t'ₓ (σ_m(P)(x, ξ)⁻¹ (tₓ⁻¹ w)))` in trivializations `t` of `F` and `t'` of `E`
are smooth homogeneous functions on the cotangent bundle. Homogeneity is inherited from that of
`σ_m(P)`. For smoothness near a point `x` of the support of `χ ψ`, take a cutoff `φ` equal to `1`
near `x` and supported in the common base set of `t` and `t'`. The readings of `σ_m(P)` through `φ`
in bases of `V` and `W` are smooth, and near `x` they are the entries of the matrix
`A(x, ξ) = tₓ ∘ σ_m(P)(x, ξ) ∘ t'ₓ⁻¹ : V → W`. The reading of the inverse is then read off from
`A(x, ξ)⁻¹`, and inversion is smooth on the invertible maps `V → W`
(`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`). The scalar statement is
`TauCeti.IsClassicalElliptic.inv_classicalPrincipalSymbol_mem_homogeneousCotangentSymbols`.

**Parametrices.** On a compact manifold every smooth homogeneous `Hom(F, E)`-valued symbol is a
principal symbol (`TauCeti.sectionClassicalPrincipalSymbolLinearMap_surjective`), so there is an
operator `Q₀` of order `-m` with principal symbol `σ_m(P)⁻¹`
(`TauCeti.IsSectionClassicalElliptic.exists_sectionClassicalPrincipalSymbol_comp_eq_id`). The
principal symbols of `P Q₀` and `Q₀ P` are those of the identities, so `P Q₀ = 1 - R` and
`Q₀ P = 1 - L` with `R` and `L` of order `-1`. The Neumann series on a bundle
(`exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators`) inverts
`1 - R` and `1 - L` modulo operators of every order `-N`, by operators `S` and `S'`. Then
`Q = Q₀ S` is a right parametrix and `Q' = S' Q₀` a left parametrix, and they agree modulo order
`-∞`, since `Q' - Q = Q' (1 - P Q) + (Q' P - 1) Q`. So `Q` is a two-sided parametrix:
`P Q - 1` and `Q P - 1` have every order `-N`
(`IsSectionClassicalElliptic.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators`).
Conversely an operator with such a parametrix is elliptic
(`TauCeti.IsSectionClassicalEllipticAt.of_comp_sub_id_mem`), so on a compact manifold the elliptic
operators between bundles are exactly those invertible modulo operators of order `-∞`
(`TauCeti.isSectionClassicalElliptic_iff_exists_comp_sub_id_mem`).

## Main results

* `TauCeti.IsSectionClassicalElliptic.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`:
  the inverse principal symbol of an elliptic operator between bundles is a smooth positively
  homogeneous `Hom(F, E)`-valued symbol of degree `-m`.
* `TauCeti.IsSectionClassicalElliptic.exists_sectionClassicalPrincipalSymbol_comp_eq_id`: on a
  compact manifold, it is the principal symbol of an operator of order `-m`.
* `IsSectionClassicalElliptic.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators`:
  on a compact manifold, an elliptic operator between bundles has a two-sided parametrix of order
  `-m` modulo operators of every order `-N`.
* `TauCeti.isSectionClassicalElliptic_iff_exists_comp_sub_id_mem`: on a compact manifold,
  ellipticity is invertibility modulo operators of order `-∞`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (parametrices
  of elliptic operators, and operators between vector bundles after Definition 18.1.20).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.1)–(4.6), and §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-! ### The inverse principal symbol -/

variable (m P) in
/-- The fibrewise inverse `σ_m(P)(x, ξ)⁻¹ : F_x → E_x` of the principal symbol, where it is
bijective, and `0` elsewhere. -/
private def inversePrincipalSymbol (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    F x →ₗ[ℂ] E x :=
  open Classical in
  if h : Function.Bijective (sectionClassicalPrincipalSymbol m P x ξ) then
    (LinearEquiv.ofBijective _ h).symm.toLinearMap
  else 0

private theorem sectionClassicalPrincipalSymbol_inversePrincipalSymbol_apply {x : M}
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ}
    (h : Function.Bijective (sectionClassicalPrincipalSymbol m P x ξ)) (y : F x) :
    sectionClassicalPrincipalSymbol m P x ξ (inversePrincipalSymbol m P x ξ y) = y := by
  simp only [inversePrincipalSymbol, h, ↓reduceDIte, LinearEquiv.coe_coe,
    LinearEquiv.apply_ofBijective_symm_apply]

private theorem inversePrincipalSymbol_sectionClassicalPrincipalSymbol_apply {x : M}
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ}
    (h : Function.Bijective (sectionClassicalPrincipalSymbol m P x ξ)) (u : E x) :
    inversePrincipalSymbol m P x ξ (sectionClassicalPrincipalSymbol m P x ξ u) = u := by
  simp only [inversePrincipalSymbol, h, ↓reduceDIte, LinearEquiv.coe_coe,
    LinearEquiv.ofBijective_symm_apply_apply]

private theorem inversePrincipalSymbol_zero_covector (x : M) :
    inversePrincipalSymbol m P x 0 = 0 := by
  by_cases h : Function.Bijective (sectionClassicalPrincipalSymbol m P x 0)
  · -- The zero map is bijective, so `E_x` is trivial.
    refine LinearMap.ext fun y ↦ h.1 ?_
    simp
  · simp only [inversePrincipalSymbol, h, ↓reduceDIte]

private theorem inversePrincipalSymbol_smul_covector (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) :
    inversePrincipalSymbol m P x (c • ξ) =
      (((c ^ m : ℝ) : ℂ))⁻¹ • inversePrincipalSymbol m P x ξ := by
  have hcm : ((c ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hc m).ne'
  have hσ := sectionClassicalPrincipalSymbol_smul_covector (m := m) (P := P) x ξ hc
  by_cases h : Function.Bijective (sectionClassicalPrincipalSymbol m P x ξ)
  · have h' : Function.Bijective (sectionClassicalPrincipalSymbol m P x (c • ξ)) := by
      rw [hσ, LinearMap.coe_smul]
      exact (MulAction.bijective (Units.mk0 _ hcm)).comp h
    refine LinearMap.ext fun y ↦ h'.1 ?_
    rw [sectionClassicalPrincipalSymbol_inversePrincipalSymbol_apply h', LinearMap.smul_apply,
      map_smul, hσ, LinearMap.smul_apply,
      sectionClassicalPrincipalSymbol_inversePrincipalSymbol_apply h, smul_smul,
      inv_mul_cancel₀ hcm, one_smul]
  · have h' : ¬ Function.Bijective (sectionClassicalPrincipalSymbol m P x (c • ξ)) := by
      rw [hσ, LinearMap.coe_smul]
      exact fun h' ↦ h ((MulAction.bijective (Units.mk0 _ hcm)).of_comp_iff' _ |>.1 h')
    simp only [inversePrincipalSymbol, h, h', ↓reduceDIte, smul_zero]

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [∀ x, Module ℝ (E x)]
  [VectorBundle ℝ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)] [∀ x, Module ℝ (F x)]
  [VectorBundle ℝ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
/-- **Inverting a frame reading.** Over a point `x` of the base sets of trivializations `t'` of `E`
and `t` of `F`, let a continuous linear map `A : V → W` read a bijective map `S : E_x → F_x` in
these frames, `A v = tₓ (S (t'ₓ⁻¹ v))`. Then `A` is invertible, and its inverse reads the inverse
`S'` of `S`. -/
private theorem isInvertible_and_inverse_apply_eq {x : M}
    {t' : Trivialization V (π V E)} [MemTrivializationAtlas t'] (hx' : x ∈ t'.baseSet)
    {t : Trivialization W (π W F)} [MemTrivializationAtlas t] (hx : x ∈ t.baseSet)
    {S : E x →ₗ[ℂ] F x} (hS : Function.Bijective S) {S' : F x →ₗ[ℂ] E x} (hSS' : ∀ y, S (S' y) = y)
    {A : V →L[ℂ] W} (hA : ∀ v, A v = t.continuousLinearMapAt ℂ x (S (t'.symm x v))) :
    A.IsInvertible ∧ ∀ w, A.inverse w = t'.continuousLinearMapAt ℂ x (S' (t.symm x w)) := by
  -- In these frames `A` is `S` conjugated by the trivializations at `x`.
  have hAeq : ⇑A = ⇑(t.continuousLinearEquivAt ℂ x hx) ∘ S ∘
      ⇑(t'.continuousLinearEquivAt ℂ x hx').symm := by
    ext v
    rw [hA, Function.comp_apply, Function.comp_apply,
      Trivialization.continuousLinearEquivAt_symm_apply,
      t.coe_continuousLinearEquivAt_eq (R := ℂ) hx]
  have hAi : A.IsInvertible := ContinuousLinearMap.isInvertible_iff_bijective.2 <| by
    rw [hAeq]
    exact (t.continuousLinearEquivAt ℂ x hx).bijective.comp
      (hS.comp (t'.continuousLinearEquivAt ℂ x hx').symm.bijective)
  refine ⟨hAi, fun w ↦ ?_⟩
  have hw : A (t'.continuousLinearMapAt ℂ x (S' (t.symm x w))) = w := by
    rw [hA, ← t'.symmL_apply (R := ℂ) hx', t'.symmL_continuousLinearMapAt hx', hSS',
      ← t.symmL_apply (R := ℂ) hx, t.continuousLinearMapAt_symmL hx]
  conv_lhs => rw [← hw]
  exact hAi.inverse_apply_self _

/-- **The matrix of the principal symbol in a pair of frames.** In a chart `e` of the maximal atlas,
let `φ` be a smooth function supported in the common base set of trivializations `t'` of `E` and
`t` of `F`. There is a smooth family `A(y, η) : V → W` over `e.target × {η ≠ 0}` which, wherever
`φ(x) = 1` with `x = e⁻¹ y` and `ξ = ⟪η, ·⟫ ∘ de_x`, reads `σ_m(P)(x, ξ)` in these frames. If `P`
is elliptic, `A(y, η)` is invertible there and its inverse reads `σ_m(P)(x, ξ)⁻¹`.

Its entries are the readings of `σ_m(P)` through `φ`, which are smooth since `σ_m(P)` is a smooth
homogeneous symbol. -/
private theorem exists_contDiffOn_frameMatrix (hPe : IsSectionClassicalElliptic m P)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {t' : Trivialization V (π V E)} [MemTrivializationAtlas t']
    {t : Trivialization W (π W F)} [MemTrivializationAtlas t]
    {φ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hφU : tsupport φ ⊆ t'.baseSet ∩ t.baseSet) :
    ∃ A : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W,
      ContDiffOn ℝ ∞ A (e.target ×ˢ {η | η ≠ 0}) ∧
      ∀ q ∈ e.target ×ˢ {η | η ≠ 0}, φ (e.symm q.1) = 1 → (A q).IsInvertible ∧ ∀ w,
        (A q).inverse w = t'.continuousLinearMapAt ℂ (e.symm q.1)
          (inversePrincipalSymbol m P (e.symm q.1) ((innerSL ℝ q.2).comp
            (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1))) (t.symm (e.symm q.1) w)) := by
  set b := finBasis ℂ V
  set c := finBasis ℂ W
  set G := fun (j : Fin (finrank ℂ W)) (k : Fin (finrank ℂ V))
      (q : CoordinateSpace n × CoordinateSpace n) ↦
    ((φ (e.symm q.1) * φ (e.symm q.1) : ℝ) : ℂ) * (c.coord j).toContinuousLinearMap
      (t.continuousLinearMapAt ℂ (e.symm q.1) (sectionClassicalPrincipalSymbol m P (e.symm q.1)
        ((innerSL ℝ q.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1)))
        (t'.symm (e.symm q.1) (b k))))
  refine ⟨fun q ↦ ∑ j, ∑ k, G j k q • (b.coord k).toContinuousLinearMap.smulRight (c j),
    ContDiffOn.sum fun j _ ↦ ContDiffOn.sum fun k _ ↦ ContDiffOn.smul
      ((mem_homogeneousCotangentSymbols_iff.1 (mem_sectionHomogeneousCotangentSymbols_iff.1
          (sectionClassicalPrincipalSymbol_mem_sectionHomogeneousCotangentSymbols (m := m) (P := P))
          t' φ (hφU.trans inter_subset_left) (b k) t φ (hφU.trans inter_subset_right)
          (c.coord j).toContinuousLinearMap)).2.2 e he) contDiffOn_const,
    fun q hq hφq ↦ ?_⟩
  have hqU : e.symm q.1 ∈ t'.baseSet ∩ t.baseSet :=
    hφU (subset_tsupport _ (by simp [hφq]))
  have hξ := (innerSL_comp_mvfderiv_eq_zero_iff
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) (e.map_target hq.1)).not.2 hq.2
  have hb := isSectionClassicalEllipticAt_iff.1 (isSectionClassicalElliptic_iff.1 hPe _) _ hξ
  refine isInvertible_and_inverse_apply_eq hqU.1 hqU.2 hb
    (sectionClassicalPrincipalSymbol_inversePrincipalSymbol_apply hb) fun v ↦ ?_
  -- Where `φ = 1`, the matrix entries are those of `σ_m(P)` read in the frames.
  rw [← t'.symmL_apply (R := ℂ) hqU.1]
  set L : V →ₗ[ℂ] W := (t.continuousLinearMapAt ℂ (e.symm q.1)).toLinearMap ∘ₗ
    sectionClassicalPrincipalSymbol m P (e.symm q.1) ((innerSL ℝ q.2).comp
      (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1))) ∘ₗ
    (t'.symmL ℂ (e.symm q.1)).toLinearMap
  have hL : ((∑ j, ∑ k, G j k q • (b.coord k).toContinuousLinearMap.smulRight (c j) :
      V →L[ℂ] W) : V →ₗ[ℂ] W) = L := b.ext fun k ↦ by
    simp [G, hφq, L, t'.symmL_apply hqU.1, Finsupp.single_apply, c.sum_repr]
  exact congr($hL v)

/-- **Smoothness of the inverse reading at a point of the support.** In a chart `e` of the maximal
atlas, let `g` be a smooth function supported in the common base set of trivializations `t'` of
`E` and `t` of `F`. If `P` is elliptic, the reading
`(y, η) ↦ g(x) ℓ(t'ₓ (σ_m(P)(x, ξ)⁻¹ (tₓ⁻¹ w)))`, with `x = e⁻¹ y` and `ξ = ⟪η, ·⟫ ∘ de_x`, is
smooth near every point of `e.target × {η ≠ 0}` over the support of `g`: near such a point it is
read from the inverse of the matrix of `σ_m(P)`, and inversion is smooth on the invertible maps
`V → W`. -/
private theorem contDiffWithinAt_inversePrincipalSymbol_reading
    (hPe : IsSectionClassicalElliptic m P) {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {t' : Trivialization V (π V E)} [MemTrivializationAtlas t']
    {t : Trivialization W (π W F)} [MemTrivializationAtlas t]
    {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ) ∞ g)
    (hgt : tsupport g ⊆ t'.baseSet ∩ t.baseSet) (w : W) (ℓ : V →L[ℂ] ℂ)
    {p : CoordinateSpace n × CoordinateSpace n} (hp : p ∈ e.target ×ˢ {η | η ≠ 0})
    (hpg : e.symm p.1 ∈ tsupport g) :
    ContDiffWithinAt ℝ ∞ (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (g (e.symm q.1) : ℂ) * ℓ (t'.continuousLinearMapAt ℂ (e.symm q.1)
        (inversePrincipalSymbol m P (e.symm q.1) ((innerSL ℝ q.2).comp
          (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1))) (t.symm (e.symm q.1) w))))
      (e.target ×ˢ {η | η ≠ 0}) p := by
  -- A cutoff `φ` equal to `1` near `e⁻¹ p.1`, and the matrix `A` of `σ_m(P)` read through it.
  obtain ⟨φ, hφU, hφ1⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    ((t'.open_baseSet.inter t.open_baseSet).mem_nhds (hgt hpg))
  obtain ⟨A, hA, hAinv⟩ := exists_contDiffOn_frameMatrix (m := m) (P := P) hPe he hφU
  have hev : ∀ᶠ q in 𝓝 p, φ (e.symm q.1) = 1 :=
    Filter.Tendsto.eventually ((e.continuousAt_symm hp.1).comp continuousAt_fst) hφ1
  -- So the reading agrees near `p` with `g(x) ℓ(A⁻¹ w)`, which is smooth at `p`.
  have hge : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target :=
    contMDiffOn_iff_contDiffOn.1 (hg.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he))
  have hinv := ((hAinv p hp hev.self_of_nhds).1.contDiffAt_map_inverse (n := ∞)).restrict_scalars
    ℝ |>.comp_contDiffWithinAt p (hA p hp)
  refine ((Complex.ofRealCLM.contDiff.contDiffAt.comp_contDiffWithinAt p
      ((hge.comp contDiffOn_fst mapsTo_fst_prod) p hp)).mul
    (((ℓ.comp (ContinuousLinearMap.apply ℂ V w)).restrictScalars ℝ).contDiff.contDiffAt
      |>.comp_contDiffWithinAt p hinv)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hev]
      with q hq hqφ
    simp [(hAinv q hq hqφ).2 w]
  · simp [(hAinv p hp hev.self_of_nhds).2 w]

/-- **The inverse principal symbol is a smooth homogeneous symbol.** -/
private theorem inversePrincipalSymbol_mem_sectionHomogeneousCotangentSymbols
    (hPe : IsSectionClassicalElliptic m P) :
    inversePrincipalSymbol m P ∈ sectionHomogeneousCotangentSymbols n W F V E (-m) := by
  refine mem_sectionHomogeneousCotangentSymbols_iff.2 fun t _ ψ hψ w t' _ χ hχ ℓ ↦ ?_
  refine mem_homogeneousCotangentSymbols_iff.2 ⟨fun x ↦ ?_, fun x ξ c hc ↦ ?_, fun e he p hp ↦ ?_⟩
  · simp [inversePrincipalSymbol_zero_covector]
  · rw [inversePrincipalSymbol_smul_covector x ξ hc, LinearMap.smul_apply, map_smul, map_smul,
      smul_eq_mul, Real.rpow_neg hc.le, Complex.ofReal_inv]
    ring
  have hgt : tsupport (fun y ↦ χ y * ψ y) ⊆ t'.baseSet ∩ t.baseSet := fun y hy ↦
    ⟨hχ (tsupport_mul_subset_left hy), hψ (tsupport_mul_subset_right hy)⟩
  by_cases hpg : e.symm p.1 ∈ tsupport (fun y ↦ χ y * ψ y)
  · exact contDiffWithinAt_inversePrincipalSymbol_reading hPe he (χ.contMDiff.mul ψ.contMDiff)
      hgt w ℓ hp hpg
  · -- Off the support of `χ ψ`, the reading vanishes near `p`.
    have hc : ∀ᶠ q in 𝓝 p, χ (e.symm (q : CoordinateSpace n × CoordinateSpace n).1) *
        ψ (e.symm q.1) = 0 := by
      filter_upwards [((e.continuousAt_symm hp.1).comp continuousAt_fst).preimage_mem_nhds
        ((isClosed_tsupport _).isOpen_compl.mem_nhds hpg)] with q hq
      exact image_eq_zero_of_notMem_tsupport (f := fun y ↦ χ y * ψ y) hq
    exact (contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (eventually_nhdsWithin_of_eventually_nhds (hc.mono fun q hq ↦ by simp [hq]))
      (by simp [image_eq_zero_of_notMem_tsupport hpg])

/-- **The inverse principal symbol.** If `P : Γ(E) → Γ(F)` is elliptic of order `m`, the fibrewise
inverses `σ_m(P)(x, ξ)⁻¹ : F_x → E_x` at nonzero covectors form a smooth positively homogeneous
`Hom(F, E)`-valued symbol of degree `-m`: there is `s` in
`TauCeti.sectionHomogeneousCotangentSymbols n W F V E (-m)` with `s(x, ξ) ∘ σ_m(P)(x, ξ) = 1` and
`σ_m(P)(x, ξ) ∘ s(x, ξ) = 1` for every nonzero covector `ξ ∈ T*ₓM`. -/
theorem IsSectionClassicalElliptic.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id
    (hPe : IsSectionClassicalElliptic m P) :
    ∃ s ∈ sectionHomogeneousCotangentSymbols n W F V E (-m), ∀ x ξ, ξ ≠ 0 →
      s x ξ ∘ₗ sectionClassicalPrincipalSymbol m P x ξ = LinearMap.id ∧
        sectionClassicalPrincipalSymbol m P x ξ ∘ₗ s x ξ = LinearMap.id := by
  refine ⟨inversePrincipalSymbol m P,
    inversePrincipalSymbol_mem_sectionHomogeneousCotangentSymbols hPe, fun x ξ hξ ↦ ?_⟩
  have hb := isSectionClassicalEllipticAt_iff.1 (isSectionClassicalElliptic_iff.1 hPe x) ξ hξ
  exact ⟨LinearMap.ext (inversePrincipalSymbol_sectionClassicalPrincipalSymbol_apply hb),
    LinearMap.ext (sectionClassicalPrincipalSymbol_inversePrincipalSymbol_apply hb)⟩

/-- **Quantizing the inverse principal symbol.** On a compact manifold, an elliptic operator
`P : Γ(E) → Γ(F)` of order `m` has an operator `Q : Γ(F) → Γ(E)` of order `-m` whose principal
symbol is the fibrewise inverse of that of `P`: `σ_{-m}(Q)(x, ξ) ∘ σ_m(P)(x, ξ) = 1` and
`σ_m(P)(x, ξ) ∘ σ_{-m}(Q)(x, ξ) = 1` at every nonzero covector `ξ ∈ T*ₓM`. -/
theorem IsSectionClassicalElliptic.exists_sectionClassicalPrincipalSymbol_comp_eq_id
    [CompactSpace M] (hPe : IsSectionClassicalElliptic m P) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
      ∀ x ξ, ξ ≠ 0 →
        sectionClassicalPrincipalSymbol (-m) Q x ξ ∘ₗ sectionClassicalPrincipalSymbol m P x ξ =
          LinearMap.id ∧
        sectionClassicalPrincipalSymbol m P x ξ ∘ₗ sectionClassicalPrincipalSymbol (-m) Q x ξ =
          LinearMap.id := by
  obtain ⟨s, hs, hsP⟩ := hPe.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id
  obtain ⟨⟨Q, hQ⟩, hQs⟩ := sectionClassicalPrincipalSymbolLinearMap_surjective
    (n := n) (V := W) (E := F) (W := V) (F := E) (m := -m) ⟨s, hs⟩
  have hσ : sectionClassicalPrincipalSymbol (-m) Q = s := by
    simpa using congrArg Subtype.val hQs
  exact ⟨Q, hQ, fun x ξ hξ ↦ hσ ▸ hsP x ξ hξ⟩

/-! ### Parametrices -/

/-- **Inverting the principal symbol.** On a compact manifold, an elliptic operator `P` of order
`m` between bundles has an inverse modulo operators of order `-1`: an operator `Q` of order `-m`
whose principal symbol is the inverse of that of `P`. -/
private theorem IsSectionClassicalElliptic.exists_comp_sub_id_mem_neg_one [CompactSpace M]
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hPe : IsSectionClassicalElliptic m P) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
      P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1) ∧
        Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1) := by
  obtain ⟨Q, hQ, hσ⟩ := hPe.exists_sectionClassicalPrincipalSymbol_comp_eq_id
  have hPQ : P ∘ₗ Q ∈ sectionClassicalPseudodifferentialOperators 0 := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hP hQ
  have hQP : Q ∘ₗ P ∈ sectionClassicalPseudodifferentialOperators 0 := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hQ hP
  -- Both products have the principal symbol of the identity.
  rw [show (-1 : ℝ) = 0 - 1 by norm_num]
  refine ⟨Q, hQ,
    sub_mem_sectionClassicalPseudodifferentialOperators_of_sectionClassicalPrincipalSymbol_eq hPQ
      id_mem_sectionClassicalPseudodifferentialOperators fun x ξ ↦ ?_,
    sub_mem_sectionClassicalPseudodifferentialOperators_of_sectionClassicalPrincipalSymbol_eq hQP
      id_mem_sectionClassicalPseudodifferentialOperators fun x ξ ↦ ?_⟩
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · have h := sectionClassicalPrincipalSymbol_comp hP hQ x ξ
      rw [add_neg_cancel] at h
      rw [h, (hσ x ξ hξ).2, sectionClassicalPrincipalSymbol_id x hξ]
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · have h := sectionClassicalPrincipalSymbol_comp hQ hP x ξ
      rw [neg_add_cancel] at h
      rw [h, (hσ x ξ hξ).1, sectionClassicalPrincipalSymbol_id x hξ]

/-- **Parametrices of elliptic operators between bundles.** On a compact manifold, let
`P : Γ(E) → Γ(F)` be an elliptic classical pseudodifferential operator of order `m` between
bundles with finite-dimensional fibres. Then there is a classical pseudodifferential operator
`Q : Γ(F) → Γ(E)` of order `-m` that inverts `P` on both sides modulo operators of order `-∞`:
`P ∘ Q - 1` and `Q ∘ P - 1` have every order `-N`. -/
theorem
    IsSectionClassicalElliptic.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators
    [CompactSpace M] (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hPe : IsSectionClassicalElliptic m P) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
      ∀ N : ℕ, P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) ∧
        Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) := by
  obtain ⟨Q₀, hQ₀, hPQ₀, hQ₀P⟩ := hPe.exists_comp_sub_id_mem_neg_one hP
  -- With `P Q₀ = 1 - R` and `Q₀ P = 1 - L`, both `R` and `L` of order `-1`, the Neumann series
  -- inverts `1 - R` and `1 - L` modulo order `-∞`; so `Q = Q₀ S` is a right parametrix and
  -- `Q' = S' Q₀` a left parametrix.
  obtain ⟨S, hS, hSN⟩ :=
    exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators
      (R := LinearMap.id - P ∘ₗ Q₀) (by simpa using neg_mem hPQ₀)
  obtain ⟨S', hS', hS'N⟩ :=
    exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators
      (R := LinearMap.id - Q₀ ∘ₗ P) (by simpa using neg_mem hQ₀P)
  have hQ : Q₀ ∘ₗ S ∈ sectionClassicalPseudodifferentialOperators (-m) := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hQ₀ hS
  have hQ' : S' ∘ₗ Q₀ ∈ sectionClassicalPseudodifferentialOperators (-m) := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hS' hQ₀
  have hPQ (N : ℕ) :
      P ∘ₗ (Q₀ ∘ₗ S) - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.comp_assoc] using (hSN N).1
  have hQ'P (N : ℕ) :
      (S' ∘ₗ Q₀) ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.comp_assoc] using (hS'N N).2
  -- The left and right parametrices agree modulo order `-∞`:
  -- `Q' - Q = Q' (1 - P Q) + (Q' P - 1) Q`, so `(Q' - Q) P` has every order `-N`.
  have hdiff (N : ℕ) : (S' ∘ₗ Q₀ - Q₀ ∘ₗ S) ∘ₗ P ∈
      sectionClassicalPseudodifferentialOperators (-N) := by
    have h₁ := comp_mem_sectionClassicalPseudodifferentialOperators hQ' (neg_mem (hPQ N))
    have h₂ := comp_mem_sectionClassicalPseudodifferentialOperators (hQ'P N) hQ
    rw [add_comm] at h₂
    have h := comp_mem_sectionClassicalPseudodifferentialOperators (add_mem h₁ h₂) hP
    rw [show -m + -(N : ℝ) + m = -N by ring] at h
    convert h using 1
    ext u : 1
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.id_apply, map_neg, map_sub]
    abel
  refine ⟨Q₀ ∘ₗ S, hQ, fun N ↦ ⟨hPQ N, ?_⟩⟩
  rw [show (Q₀ ∘ₗ S) ∘ₗ P - LinearMap.id =
      ((S' ∘ₗ Q₀) ∘ₗ P - LinearMap.id) - (S' ∘ₗ Q₀ - Q₀ ∘ₗ S) ∘ₗ P by
    ext u : 1
    simp]
  exact sub_mem (hQ'P N) (hdiff N)

/-- **Ellipticity is invertibility modulo order `-∞`.** On a compact manifold, a classical
pseudodifferential operator `P : Γ(E) → Γ(F)` of order `m` between bundles with
finite-dimensional fibres is elliptic exactly when it has a two-sided parametrix of order `-m`: an
operator `Q : Γ(F) → Γ(E)` of order `-m` with `P ∘ Q - 1` and `Q ∘ P - 1` of every order `-N`. -/
theorem isSectionClassicalElliptic_iff_exists_comp_sub_id_mem
    [CompactSpace M] (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    IsSectionClassicalElliptic m P ↔
      ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
        ∀ N : ℕ, P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) ∧
          Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) :=
  ⟨fun hPe ↦ hPe.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators hP,
    fun ⟨Q, hQ, hN⟩ ↦ isSectionClassicalElliptic_iff.2 fun x ↦
      IsSectionClassicalEllipticAt.of_comp_sub_id_mem hQ hP (neg_add_cancel m)
        (by simpa using (hN 1).2) (by simpa using (hN 1).1) x⟩

end TauCeti
