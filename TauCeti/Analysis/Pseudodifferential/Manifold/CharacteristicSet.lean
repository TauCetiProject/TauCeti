/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CharacteristicSet
public import TauCeti.Analysis.Pseudodifferential.Manifold.Diffeomorph
public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The characteristic set of a classical pseudodifferential operator on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on `ℝⁿ`
(`TauCeti.classicalPseudodifferentialOperators`), with principal symbol `σ_m(P)` on the cotangent
bundle (`TauCeti.classicalPrincipalSymbol`). Its **characteristic set**
(`TauCeti.classicalCharacteristicSet`) is the set of nonzero covectors `ξ ∈ T*ₓM` at which
`σ_m(P)(x, ξ) = 0`, a subset of the cotangent bundle `TauCeti.CotangentBundle`. It is empty
exactly when `P` is elliptic (`TauCeti.classicalCharacteristicSet_eq_empty_iff`), and it is the set
that microlocal elliptic regularity, `WF(u) ⊆ WF(P u) ∪ Char(P)`, adds to the wave front set of
`P u`.

The characteristic set is intrinsic and agrees in every chart with the characteristic set of the
chart symbol, defined on `ℝⁿ` by ellipticity in conic neighbourhoods at large frequencies
(`TauCeti.Symbol.characteristicSet`). For a classical symbol `a` that set consists of the points at
which the principal symbol of `a` is not invertible
(`TauCeti.ClassicalSymbol.mem_characteristicSet_toSymbol_iff`). So if `a` is the symbol of the chart
compression `u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` of `P` in a chart `e`, then at a point `x` where
`φ ψ` does not vanish the covector `⟪η, ·⟫ ∘ de_x` is characteristic for `P` exactly when `(e x, η)`
is characteristic for `a`
(`TauCeti.mk_mem_classicalCharacteristicSet_iff_mem_characteristicSet`). This comparison carries
statements phrased with the Euclidean characteristic set, such as the microlocal elliptic regularity
`TauCeti.Symbol.waveFrontSet_toDistribution_subset_quantizeSobolev_union_characteristicSet`, to
chart symbols of `P`.

## Main definitions

* `TauCeti.classicalCharacteristicSet m P`: the nonzero covectors at which `σ_m(P)` vanishes.

## Main results

* `TauCeti.mk_smul_mem_classicalCharacteristicSet_iff`: the characteristic set is conic.
* `TauCeti.isClassicalEllipticAt_iff_forall_notMem_classicalCharacteristicSet`,
  `TauCeti.classicalCharacteristicSet_eq_empty_iff`: `P` is elliptic at `x` exactly when no
  covector at `x` is characteristic, and elliptic exactly when its characteristic set is empty.
* `TauCeti.classicalCharacteristicSet_add_of_mem_sub_one`,
  `TauCeti.classicalCharacteristicSet_smul`: adding an operator of order `m - 1` or multiplying by
  a nonzero constant does not change the characteristic set, and
  `TauCeti.classicalCharacteristicSet_of_mem_sub_one`: an operator of order `m - 1` is
  characteristic in order `m` at every nonzero covector.
* `TauCeti.mk_mem_classicalCharacteristicSet_iff_mem_characteristicSet`,
  `TauCeti.mem_classicalCharacteristicSet_iff_mem_characteristicSet`: the characteristic set
  read in a chart is the characteristic set of the chart symbol.
* `TauCeti.mk_mem_classicalCharacteristicSet_pushforwardOperator_iff`: under a diffeomorphism `Φ`
  the characteristic set is carried by the cotangent map, `ξ ∈ Char(Φ_* P)` over `Φ x` exactly
  when `ξ ∘ dΦ_x ∈ Char(P)`.
* `TauCeti.mk_mem_classicalCharacteristicSet_complexifyLinearMap_iff`: for the complexification
  of a differential operator `D` of order at most `m`, the characteristic set is the set of nonzero
  covectors at which the geometric principal symbol of `D` vanishes;
  `TauCeti.IsLaplaceType.classicalCharacteristicSet_complexifyLinearMap_eq_empty`: for an operator
  of Laplace type it is empty.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (the characteristic set of a classical pseudodifferential operator, defined by its
  principal symbol, and microlocal elliptic regularity).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold Distributions SchwartzMap

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### The characteristic set -/

variable (m P) in
/-- The **characteristic set** of a classical pseudodifferential operator `P` of order `m` on `M`:
the nonzero covectors `ξ ∈ T*ₓM` at which its principal symbol `σ_m(P)(x, ξ)`
(`TauCeti.classicalPrincipalSymbol`) vanishes. If `P` is not of order `m`, its principal symbol is
`0` by convention and every nonzero covector is characteristic. -/
def classicalCharacteristicSet : Set (CotangentBundle 𝓘(ℝ, CoordinateSpace n) M) :=
  {p | p.snd ≠ 0 ∧ classicalPrincipalSymbol m P p.proj p.snd = 0}

@[simp]
theorem mem_classicalCharacteristicSet_iff {p : CotangentBundle 𝓘(ℝ, CoordinateSpace n) M} :
    p ∈ classicalCharacteristicSet m P ↔
      p.snd ≠ 0 ∧ classicalPrincipalSymbol m P p.proj p.snd = 0 :=
  Iff.rfl

/-- The characteristic set is conic: it depends on a covector only through its ray. -/
theorem mk_smul_mem_classicalCharacteristicSet_iff {x : M}
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} {t : ℝ} (ht : 0 < t) :
    TotalSpace.mk x (t • ξ) ∈ classicalCharacteristicSet m P ↔
      TotalSpace.mk x ξ ∈ classicalCharacteristicSet m P := by
  simp [classicalPrincipalSymbol_smul_covector x ξ ht, ht.ne', (Real.rpow_pos_of_pos ht m).ne']

/-- **Ellipticity and the characteristic set.** `P` is elliptic at `x` exactly when no covector at
`x` is characteristic. -/
theorem isClassicalEllipticAt_iff_forall_notMem_classicalCharacteristicSet {x : M} :
    IsClassicalEllipticAt m P x ↔ ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ,
      TotalSpace.mk x ξ ∉ classicalCharacteristicSet m P := by
  simp [isClassicalEllipticAt_iff]

/-- `P` is elliptic exactly when its characteristic set is empty. -/
@[simp]
theorem classicalCharacteristicSet_eq_empty_iff :
    classicalCharacteristicSet m P = ∅ ↔ IsClassicalElliptic m P := by
  simp only [isClassicalElliptic_iff,
    isClassicalEllipticAt_iff_forall_notMem_classicalCharacteristicSet, eq_empty_iff_forall_notMem]
  exact ⟨fun h x ξ ↦ h _, fun h p ↦ h p.proj p.snd⟩

/-- **The characteristic set ignores lower order terms.** Adding an operator of order `m - 1` does
not change the characteristic set. -/
theorem classicalCharacteristicSet_add_of_mem_sub_one
    (hQ : Q ∈ classicalPseudodifferentialOperators (m - 1)) :
    classicalCharacteristicSet m (P + Q) = classicalCharacteristicSet m P := by
  ext p
  simp [classicalPrincipalSymbol_add_of_mem_sub_one hQ]

/-- Multiplying by a nonzero complex number does not change the characteristic set. -/
@[simp]
theorem classicalCharacteristicSet_smul {c : ℂ} (hc : c ≠ 0) :
    classicalCharacteristicSet m (c • P) = classicalCharacteristicSet m P := by
  ext p
  simp [classicalPrincipalSymbol_smul_of_ne_zero hc, hc]

/-- An operator of order `m - 1` is characteristic in order `m` at every nonzero covector. -/
theorem classicalCharacteristicSet_of_mem_sub_one
    (hP : P ∈ classicalPseudodifferentialOperators (m - 1)) :
    classicalCharacteristicSet m P = {p | p.snd ≠ 0} := by
  ext p
  simp [classicalPrincipalSymbol_eq_zero_of_mem_sub_one hP]

/-! ### The characteristic set in a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n ℂ ℂ m}

/-- **The characteristic set in a chart.** Let `a` be the symbol of the chart compression
`u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` of a classical pseudodifferential operator `P` of order `m`. At a
point `x` of the chart source where `φ ψ` does not vanish, the covector `⟪η, ·⟫ ∘ de_x` is
characteristic for `P` exactly when `(e x, η)` lies in the characteristic set of `a`
(`TauCeti.Symbol.characteristicSet`), defined by ellipticity of `a` in conic neighbourhoods at large
frequencies. -/
theorem mk_mem_classicalCharacteristicSet_iff_mem_characteristicSet
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (hφψ : φ (e x) * ψ (e x) ≠ 0) (η : CoordinateSpace n) :
    TotalSpace.mk x ((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x)) ∈
        classicalCharacteristicSet m P ↔ (e x, η) ∈ a.toSymbol.characteristicSet := by
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hc : ((φ (e x) * ψ (e x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hφψ
  rw [ClassicalSymbol.mem_characteristicSet_toSymbol_iff, mem_classicalCharacteristicSet_iff,
    coefficient_principal_eq_classicalPrincipalSymbol hP he φ ψ ha hx,
    ContinuousLinearMap.isInvertible_smul_id_iff, mul_ne_zero_iff, and_iff_right hc, not_not]
  exact and_congr_left' (innerSL_comp_mvfderiv_eq_zero_iff he₁ hx).not

/-- **The characteristic set in a chart, at a given covector.** Let `a` be the symbol of the chart
compression of `P` by `φ`, `ψ` in a chart `e`. At a point `x` of the chart source where `φ ψ` does
not vanish, a covector `ξ ∈ T*ₓM` is characteristic for `P` exactly when `(e x, η)` lies in the
characteristic set of `a`, for the chart frequency `η` dual to `ξ ∘ (de_x)⁻¹`. -/
theorem mem_classicalCharacteristicSet_iff_mem_characteristicSet
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (hφψ : φ (e x) * ψ (e x) ≠ 0)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    TotalSpace.mk x ξ ∈ classicalCharacteristicSet m P ↔
      (e x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
        (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse)) ∈
        a.toSymbol.characteristicSet := by
  conv_lhs => rw [← innerSL_toDual_symm_comp_inverse_mvfderiv
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx ξ]
  exact mk_mem_classicalCharacteristicSet_iff_mem_characteristicSet hP ha hx hφψ _

end Chart

/-! ### Diffeomorphisms -/

/-- **The characteristic set under diffeomorphisms.** A covector `ξ` at `Φ x` is characteristic for
the pushforward `u ↦ P (u ∘ Φ) ∘ Φ⁻¹` exactly when the pulled-back covector `ξ ∘ dΦ_x` is
characteristic for `P`. -/
theorem mk_mem_classicalCharacteristicSet_pushforwardOperator_iff {N : Type*} [TopologicalSpace N]
    [ChartedSpace (CoordinateSpace n) N] [T2Space N] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ N]
    (Φ : M ≃ₘ^∞⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ N) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) (Φ x) →L[ℝ] ℝ) :
    TotalSpace.mk (Φ x) ξ ∈ classicalCharacteristicSet m (Φ.pushforwardOperator P) ↔
      TotalSpace.mk x (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ x)) ∈
        classicalCharacteristicSet m P := by
  -- The differential `dΦ_x` is invertible, so `ξ ∘ dΦ_x` vanishes only for `ξ = 0`.
  obtain ⟨L, hL⟩ := Φ.isInvertible_mfderiv (x := x) (by simp)
  have hξ : ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ x) = 0 ↔ ξ = 0 := by
    rw [← hL]
    exact ξ.comp_continuousLinearEquiv_eq_zero_iff L
  simp only [mem_classicalCharacteristicSet_iff, classicalPrincipalSymbol_pushforwardOperator,
    ne_eq, hξ]

/-! ### Differential operators -/

/-- **The characteristic set of a differential operator.** For the complexification of a
differential operator `D` of order at most `m` on the real-valued smooth functions on `M`, a
nonzero covector is characteristic exactly when the geometric principal symbol of `D`
(`TauCeti.smoothPrincipalSymbol`) vanishes there. -/
theorem mk_mem_classicalCharacteristicSet_complexifyLinearMap_iff {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m) {x : M}
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    TotalSpace.mk x ξ ∈ classicalCharacteristicSet m (ContMDiffMap.complexifyLinearMap D) ↔
      ξ ≠ 0 ∧ smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨D, hD⟩ ξ = 0 := by
  rw [mem_classicalCharacteristicSet_iff]
  refine and_congr_right fun hξ ↦ ?_
  rw [classicalPrincipalSymbol_complexifyLinearMap hD x hξ, mul_eq_zero,
    or_iff_right (pow_ne_zero _ Complex.I_ne_zero), Complex.ofReal_eq_zero]

/-- **Operators of Laplace type have no characteristic covectors.** The complexification of an
operator of Laplace type, such as `-Δ`, has empty characteristic set in order `2`. -/
theorem IsLaplaceType.classicalCharacteristicSet_complexifyLinearMap_eq_empty
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, CoordinateSpace n) x)]
    {D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ 2} {c : ℝ}
    (hD : IsLaplaceType D c) :
    classicalCharacteristicSet 2 (ContMDiffMap.complexifyLinearMap
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)) = ∅ :=
  classicalCharacteristicSet_eq_empty_iff.2 hD.isClassicalElliptic_complexifyLinearMap

end TauCeti
