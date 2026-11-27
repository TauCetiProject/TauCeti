/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CharacteristicSet
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Elliptic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The characteristic set of a pseudodifferential operator between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. A classical pseudodifferential operator
`P : Γ(E) → Γ(F)` of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`) has a
principal symbol `σ_m(P)(x, ξ) : E_x → F_x` at every covector `ξ ∈ T*ₓM`
(`TauCeti.sectionClassicalPrincipalSymbol`). Its **characteristic set**
(`TauCeti.sectionClassicalCharacteristicSet`) is the set of nonzero covectors at which
`σ_m(P)(x, ξ)` is not bijective, a subset of the cotangent bundle `TauCeti.CotangentBundle`. It is
the set that microlocal elliptic regularity, `WF(u) ⊆ WF(P u) ∪ Char(P)`, adds to the wave front
set of `P u`. It is the counterpart for bundles of the scalar characteristic set
`TauCeti.classicalCharacteristicSet`, where the principal symbol is a number and is bijective
exactly when it is nonzero.

The characteristic set is conic, and empty exactly when `P` is elliptic
(`TauCeti.sectionClassicalCharacteristicSet_eq_empty_iff`); more precisely `P` is elliptic at `x`
exactly when no covector at `x` is characteristic. It only depends on the principal symbol, so it
ignores operators of order `m - 1` and nonzero scalar factors. Between bundles of different ranks
a linear map between the fibres is never bijective, so every nonzero covector is characteristic
(`TauCeti.sectionClassicalCharacteristicSet_of_finrank_ne`); the same holds for an operator of
order `m - 1` unless both bundles have rank zero
(`TauCeti.sectionClassicalCharacteristicSet_of_mem_sub_one`).

For a composition `R ∘ P`, the principal symbol is the composition of the principal symbols
(`TauCeti.sectionClassicalPrincipalSymbol_comp`), and a composition of linear maps is bijective
when both factors are. So `Char(R ∘ P) ⊆ Char(R) ∪ Char(P)`
(`TauCeti.sectionClassicalCharacteristicSet_comp_subset`), and an elliptic factor does not change
the characteristic set: `Char(R ∘ P) = Char(P)` when `R` is elliptic, and `Char(R ∘ P) = Char(R)`
when `P` is elliptic. This is how an elliptic parametrix or an elliptic change of order is
composed with an operator without changing where it is characteristic.

The characteristic set is intrinsic and agrees in every chart with the characteristic set of the
chart symbol, defined on `ℝⁿ` by ellipticity in conic neighbourhoods at large frequencies
(`TauCeti.Symbol.characteristicSet`), which for a matrix-valued classical symbol `a` consists of
the points at which the principal symbol of `a` is not invertible
(`TauCeti.ClassicalSymbol.mem_characteristicSet_toSymbol_iff`). If `a` is the symbol of the chart
compression `u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹` of `P` in a chart `e` and frames `t`, `t'`,
then at a point `x` where `φ ψ` does not vanish the covector `⟪η, ·⟫ ∘ de_x` is characteristic for
`P` exactly when `(e x, η)` is characteristic for `a`
(`TauCeti.mk_mem_sectionClassicalCharacteristicSet_iff_mem_characteristicSet`). This comparison
carries the Euclidean microlocal elliptic regularity of matrix-valued symbols,
`TauCeti.Symbol.vectorWaveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`,
to the chart symbols of `P`.

## Main definitions

* `TauCeti.sectionClassicalCharacteristicSet m P`: the nonzero covectors at which `σ_m(P)` is not
  bijective.

## Main results

* `TauCeti.mk_smul_mem_sectionClassicalCharacteristicSet_iff`: the characteristic set is conic.
* `TauCeti.isSectionClassicalEllipticAt_iff_forall_notMem_sectionClassicalCharacteristicSet`,
  `TauCeti.sectionClassicalCharacteristicSet_eq_empty_iff`: `P` is elliptic at `x` exactly when
  no covector at `x` is characteristic, and elliptic exactly when its characteristic set is empty.
* `TauCeti.sectionClassicalCharacteristicSet_add_of_mem_sub_one`,
  `TauCeti.sectionClassicalCharacteristicSet_smul`: operators of order `m - 1` and nonzero scalar
  factors do not change the characteristic set.
* `TauCeti.sectionClassicalCharacteristicSet_of_finrank_ne`,
  `TauCeti.sectionClassicalCharacteristicSet_of_mem_sub_one`: between bundles of different ranks,
  or for an operator of order `m - 1` between bundles not both of rank zero, every nonzero covector
  is characteristic.
* `TauCeti.sectionClassicalCharacteristicSet_comp_subset`,
  `TauCeti.sectionClassicalCharacteristicSet_comp_of_isSectionClassicalElliptic_left`,
  `TauCeti.sectionClassicalCharacteristicSet_comp_of_isSectionClassicalElliptic_right`: the
  characteristic set of a composition.
* `TauCeti.mk_mem_sectionClassicalCharacteristicSet_iff_mem_characteristicSet`,
  `TauCeti.mem_sectionClassicalCharacteristicSet_iff_mem_characteristicSet`: the characteristic
  set read in a chart and frames is the characteristic set of the chart symbol.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (the characteristic set of a pseudodifferential operator between sections of vector
  bundles, defined by its principal symbol, and microlocal elliptic regularity).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§7–8.
-/

public section

noncomputable section

open Bundle Module Set
open scoped ContDiff Manifold Distributions SchwartzMap

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
  {P Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-! ### The characteristic set -/

variable (m P) in
/-- The **characteristic set** of a classical pseudodifferential operator `P : Γ(E) → Γ(F)` of
order `m`: the nonzero covectors `ξ ∈ T*ₓM` at which its principal symbol
`σ_m(P)(x, ξ) : E_x → F_x` (`TauCeti.sectionClassicalPrincipalSymbol`) is not bijective. If `P` is
not of order `m`, its principal symbol is `0` by convention, and every nonzero covector at which
`E_x` or `F_x` is nonzero is characteristic. -/
def sectionClassicalCharacteristicSet : Set (CotangentBundle 𝓘(ℝ, CoordinateSpace n) M) :=
  {p | p.snd ≠ 0 ∧ ¬ Function.Bijective (sectionClassicalPrincipalSymbol m P p.proj p.snd)}

@[simp]
theorem mem_sectionClassicalCharacteristicSet_iff
    {p : CotangentBundle 𝓘(ℝ, CoordinateSpace n) M} :
    p ∈ sectionClassicalCharacteristicSet m P ↔
      p.snd ≠ 0 ∧ ¬ Function.Bijective (sectionClassicalPrincipalSymbol m P p.proj p.snd) :=
  Iff.rfl

/-- The characteristic set is conic: it depends on a covector only through its ray. -/
theorem mk_smul_mem_sectionClassicalCharacteristicSet_iff {x : M}
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} {t : ℝ} (ht : 0 < t) :
    TotalSpace.mk x (t • ξ) ∈ sectionClassicalCharacteristicSet m P ↔
      TotalSpace.mk x ξ ∈ sectionClassicalCharacteristicSet m P := by
  have hc : ((t ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ht m).ne'
  simp only [mem_sectionClassicalCharacteristicSet_iff,
    sectionClassicalPrincipalSymbol_smul_covector x ξ ht, ne_eq, smul_eq_zero, ht.ne', false_or,
    LinearMap.coe_smul]
  exact and_congr_right fun _ ↦ not_congr ((MulAction.bijective (Units.mk0 _ hc)).of_comp_iff' _)

/-- **Ellipticity and the characteristic set.** `P` is elliptic at `x` exactly when no covector at
`x` is characteristic. -/
theorem isSectionClassicalEllipticAt_iff_forall_notMem_sectionClassicalCharacteristicSet {x : M} :
    IsSectionClassicalEllipticAt m P x ↔ ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ,
      TotalSpace.mk x ξ ∉ sectionClassicalCharacteristicSet m P := by
  simp [isSectionClassicalEllipticAt_iff]

/-- `P` is elliptic exactly when its characteristic set is empty. -/
@[simp]
theorem sectionClassicalCharacteristicSet_eq_empty_iff :
    sectionClassicalCharacteristicSet m P = ∅ ↔ IsSectionClassicalElliptic m P := by
  simp only [isSectionClassicalElliptic_iff,
    isSectionClassicalEllipticAt_iff_forall_notMem_sectionClassicalCharacteristicSet,
    eq_empty_iff_forall_notMem]
  exact ⟨fun h x ξ ↦ h _, fun h p ↦ h p.proj p.snd⟩

/-- **The characteristic set ignores lower order terms.** Adding an operator of order `m - 1` does
not change the characteristic set. -/
theorem sectionClassicalCharacteristicSet_add_of_mem_sub_one
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators (m - 1)) :
    sectionClassicalCharacteristicSet m (P + Q) = sectionClassicalCharacteristicSet m P := by
  ext p
  simp [sectionClassicalPrincipalSymbol_add_of_mem_sub_one hQ]

/-- Multiplying by a nonzero complex number does not change the characteristic set. -/
@[simp]
theorem sectionClassicalCharacteristicSet_smul {c : ℂ} (hc : c ≠ 0) :
    sectionClassicalCharacteristicSet m (c • P) = sectionClassicalCharacteristicSet m P := by
  ext p
  refine and_congr_right fun _ ↦ not_congr ?_
  rw [sectionClassicalPrincipalSymbol_smul_of_ne_zero hc, LinearMap.coe_smul]
  exact (MulAction.bijective (Units.mk0 c hc)).of_comp_iff' _

/-- The identity of `Γ(E)` has no characteristic covectors in order `0`. -/
@[simp]
theorem sectionClassicalCharacteristicSet_id :
    sectionClassicalCharacteristicSet 0 (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) = ∅ :=
  sectionClassicalCharacteristicSet_eq_empty_iff.2 isSectionClassicalElliptic_id

/-! ### Characteristic covectors everywhere -/

/-- **Bundles of different ranks.** If `E` and `F` have different ranks, no linear map `E_x → F_x`
is bijective, so every nonzero covector is characteristic for every operator `Γ(E) → Γ(F)`. -/
theorem sectionClassicalCharacteristicSet_of_finrank_ne (h : finrank ℂ V ≠ finrank ℂ W) :
    sectionClassicalCharacteristicSet m P = {p | p.snd ≠ 0} := by
  ext p
  exact and_iff_left_of_imp fun _ hbij ↦ h (finrank_eq_of_bijective_fiber hbij)

/-- **Operators of lower order are characteristic everywhere.** Unless both bundles have rank
zero, an operator of order `m - 1` is characteristic in order `m` at every nonzero covector: its
principal symbol of order `m` is `0`, which is not bijective between fibres not both zero. -/
theorem sectionClassicalCharacteristicSet_of_mem_sub_one (hVW : Nontrivial V ∨ Nontrivial W)
    (hP : P ∈ sectionClassicalPseudodifferentialOperators (m - 1)) :
    sectionClassicalCharacteristicSet m P = {p | p.snd ≠ 0} := by
  ext p
  refine and_iff_left_of_imp fun _ hbij ↦ ?_
  rw [sectionClassicalPrincipalSymbol_eq_zero_of_mem_sub_one hP] at hbij
  obtain ⟨hV, hW⟩ := subsingleton_of_bijective_zero_fiber (V := V) (W := W) p.proj hbij
  exact hVW.elim (fun _ ↦ not_subsingleton V hV) fun _ ↦ not_subsingleton W hW

/-! ### Compositions -/

section Composition

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]
  {G : M → Type*} [TopologicalSpace (TotalSpace U G)] [∀ x, AddCommGroup (G x)]
  [∀ x, Module ℝ (G x)] [∀ x, Module ℂ (G x)] [∀ x, TopologicalSpace (G x)] [FiberBundle U G]
  [VectorBundle ℝ U G] [VectorBundle ℂ U G] [ContMDiffVectorBundle ∞ U G 𝓘(ℝ, CoordinateSpace n)]
  {m' : ℝ}
  {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, G⟯}

/-- **The characteristic set of a composition.** For `P : Γ(E) → Γ(F)` of order `m` and
`R : Γ(F) → Γ(G)` of order `m'`, a covector characteristic for `R ∘ P` in order `m' + m` is
characteristic for `R` or for `P`. -/
theorem sectionClassicalCharacteristicSet_comp_subset
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    sectionClassicalCharacteristicSet (m' + m) (R ∘ₗ P) ⊆
      sectionClassicalCharacteristicSet m' R ∪ sectionClassicalCharacteristicSet m P := by
  rintro p ⟨hp, hRP⟩
  by_contra h
  simp only [mem_union, mem_sectionClassicalCharacteristicSet_iff, hp, ne_eq, not_false_eq_true,
    true_and, not_or, not_not] at h
  rw [sectionClassicalPrincipalSymbol_comp hR hP, LinearMap.coe_comp] at hRP
  exact hRP (h.1.comp h.2)

/-- **An elliptic left factor keeps the characteristic set.** If `R : Γ(F) → Γ(G)` of order `m'`
is elliptic, then `R ∘ P` is characteristic in order `m' + m` exactly where `P` is characteristic
in order `m`. -/
theorem sectionClassicalCharacteristicSet_comp_of_isSectionClassicalElliptic_left
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hRe : IsSectionClassicalElliptic m' R) :
    sectionClassicalCharacteristicSet (m' + m) (R ∘ₗ P) =
      sectionClassicalCharacteristicSet m P := by
  ext p
  refine and_congr_right fun hp ↦ not_congr ?_
  rw [sectionClassicalPrincipalSymbol_comp hR hP, LinearMap.coe_comp]
  exact (isSectionClassicalEllipticAt_iff.1 (isSectionClassicalElliptic_iff.1 hRe p.proj) p.snd
    hp).of_comp_iff' _

/-- **An elliptic right factor keeps the characteristic set.** If `P : Γ(E) → Γ(F)` of order `m`
is elliptic, then `R ∘ P` is characteristic in order `m' + m` exactly where `R` is characteristic
in order `m'`. -/
theorem sectionClassicalCharacteristicSet_comp_of_isSectionClassicalElliptic_right
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hPe : IsSectionClassicalElliptic m P) :
    sectionClassicalCharacteristicSet (m' + m) (R ∘ₗ P) =
      sectionClassicalCharacteristicSet m' R := by
  ext p
  refine and_congr_right fun hp ↦ not_congr ?_
  rw [sectionClassicalPrincipalSymbol_comp hR hP, LinearMap.coe_comp]
  exact Function.Bijective.of_comp_iff _
    (isSectionClassicalEllipticAt_iff.1 (isSectionClassicalElliptic_iff.1 hPe p.proj) p.snd hp)

end Composition

/-! ### The characteristic set in a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {t : Trivialization V (π V E)} [MemTrivializationAtlas t] {hE : e.source ⊆ t.baseSet}
  {t' : Trivialization W (π W F)} [MemTrivializationAtlas t']
  {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n V W m}

/-- **The characteristic set in a chart.** Let `a` be the symbol of the chart compression
`u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹` of a classical pseudodifferential operator `P` of order
`m` between bundles, in a chart `e` whose source lies in the base sets of the trivializations `t`
and `t'`. At a point `x` of the chart source where `φ ψ` does not vanish, the covector
`⟪η, ·⟫ ∘ de_x` is characteristic for `P` exactly when `(e x, η)` lies in the characteristic set of
`a` (`TauCeti.Symbol.characteristicSet`), defined by ellipticity of `a` in conic neighbourhoods at
large frequencies. -/
theorem mk_mem_sectionClassicalCharacteristicSet_iff_mem_characteristicSet
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {x : M} (hx : x ∈ e.source) (hφψ : φ (e x) * ψ (e x) ≠ 0) (η : CoordinateSpace n) :
    TotalSpace.mk x ((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x)) ∈
        sectionClassicalCharacteristicSet m P ↔ (e x, η) ∈ a.toSymbol.characteristicSet := by
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  rw [ClassicalSymbol.mem_characteristicSet_toSymbol_iff, mem_sectionClassicalCharacteristicSet_iff,
    isInvertible_coefficient_principal_iff_bijective_sectionClassicalPrincipalSymbol hP hF ha hx
      hφψ]
  exact and_congr_left' (innerSL_comp_mvfderiv_eq_zero_iff he₁ hx).not

/-- **The characteristic set in a chart, at a given covector.** Let `a` be the symbol of the chart
compression of `P` by `φ`, `ψ` in a chart `e` and frames `t`, `t'`. At a point `x` of the chart
source where `φ ψ` does not vanish, a covector `ξ ∈ T*ₓM` is characteristic for `P` exactly when
`(e x, η)` lies in the characteristic set of `a`, for the chart frequency `η` dual to
`ξ ∘ (de_x)⁻¹`. -/
theorem mem_sectionClassicalCharacteristicSet_iff_mem_characteristicSet
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {x : M} (hx : x ∈ e.source) (hφψ : φ (e x) * ψ (e x) ≠ 0)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    TotalSpace.mk x ξ ∈ sectionClassicalCharacteristicSet m P ↔
      (e x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
        (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse)) ∈
        a.toSymbol.characteristicSet := by
  conv_lhs => rw [← innerSL_toDual_symm_comp_inverse_mvfderiv
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx ξ]
  exact mk_mem_sectionClassicalCharacteristicSet_iff_mem_characteristicSet hP hF ha hx hφψ _

end Chart

end TauCeti
