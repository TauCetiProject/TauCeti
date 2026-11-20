/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.FiniteDimension
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Bounded operators on a finite-dimensional space

Bounded operators out of a finite-dimensional space are determined by the images of a basis,
with operator norm controlled by the norms of those images. Hence such operators into `E` are
approximated in operator norm by operators factoring through any operator `g : F →L[𝕜] E` of
dense range. On a finite-dimensional real domain, strict pointwise norm bounds are equivalent
to strict operator-norm bounds.

Bounded operators between finite-dimensional spaces form a finite-dimensional space over every
finite extension of the scalars acting compatibly on the codomain, for instance over `ℂ` for
real-linear operators into a complex space.

The bordered operator `(w, μ) ↦ (L w + μ ℓ, ℓ w)` of `L : E → E*` and `ℓ ∈ E*`, on a real normed
space `E`, is injective when `L` is symmetric with kernel the line spanned by `v` and `ℓ v = 1`.
If `E` is finite-dimensional, its inverse then gives, for operators `L z` near such an `L z₀`, a
kernel vector of `L z` normalized by `ℓ`, depending continuously on `z` whenever `L z` is
degenerate.

## Main results

* `ContinuousLinearMap.denseRange_comp`: on operators out of a finite-dimensional space,
  postcomposition with an operator of dense range has dense range.
* `ContinuousLinearMap.opNorm_lt_iff`: a strict norm bound can be checked on
  every nonzero vector of a finite-dimensional real domain.
* `ContinuousLinearMap.finiteDimensional_of_isScalarTower`: `E →L[𝕜] F` is finite-dimensional
  over a finite extension `𝕜'` of `𝕜` acting on a finite-dimensional codomain `F`.
* `ContinuousLinearMap.injective_bordered`: the bordered operator of a symmetric operator with a
  one-dimensional kernel is injective.
* `ContinuousLinearMap.exists_tendsto_eventually_apply_eq_zero`: near a symmetric operator with a
  one-dimensional kernel, the kernel vectors of degenerate operators normalized by `ℓ` depend
  continuously on the operator.
* `IsCompact.isCompact_setOfPred_mapsTo`: out of a finite-dimensional space over a complete field,
  the operators sending a neighbourhood of `0` into a compact set form a compact set.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- On continuous linear maps out of a finite-dimensional space, postcomposition with a
continuous linear map of dense range has dense range: each `T : V →L[𝕜] E` is approximated in
operator norm by maps `g.comp U` with `U : V →L[𝕜] F`. -/
theorem denseRange_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {g : F →L[𝕜] E} (hg : DenseRange g) :
    DenseRange (g.comp : (V →L[𝕜] F) → V →L[𝕜] E) := by
  rw [Metric.denseRange_iff]
  intro T r hr
  -- Approximate the images of a basis of `V` by points of the range of `g`.
  let v := Module.finBasis 𝕜 V
  obtain ⟨C, hC, hv⟩ := v.exists_opNorm_le (F := E)
  have hrC : 0 < r / (2 * C) := by positivity
  choose y hy using fun i ↦ Metric.denseRange_iff.1 hg (T (v i)) _ hrC
  refine ⟨v.constrL y, ?_⟩
  rw [dist_eq_norm]
  calc ‖T - g.comp (v.constrL y)‖ ≤ C * (r / (2 * C)) :=
        hv hrC.le fun i ↦ by
          simpa [Module.Basis.constrL_basis, ← dist_eq_norm] using (hy i).le
    _ = r / 2 := by field_simp
    _ < r := half_lt_self hr

section StrictNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a finite-dimensional real domain, a strict pointwise operator bound gives a strict
operator-norm bound. The positivity assumption includes the zero-dimensional domain. -/
theorem opNorm_lt_iff (A : E →L[ℝ] F) {c : ℝ} (hc : 0 < c) :
    ‖A‖ < c ↔ ∀ x ≠ 0, ‖A x‖ < c * ‖x‖ := by
  refine ⟨fun h x hx ↦ (A.le_opNorm x).trans_lt ?_, fun h ↦ ?_⟩
  · exact mul_lt_mul_of_pos_right h (norm_pos_iff.mpr hx)
  · cases subsingleton_or_nontrivial E
    · simpa only [Subsingleton.elim A 0, norm_zero] using hc
    · obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) A.continuous.norm.continuousOn
      have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hxne : x ≠ 0 := by
        intro hx0
        simp [hx0] at hxnorm
      calc
        ‖A‖ ≤ ‖A x‖ := A.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy ↦
          hmax (mem_sphere_zero_iff_norm.mpr hy)
        _ < c := by simpa only [hxnorm, mul_one] using h x hxne

end StrictNorm

section ScalarExtension

variable {𝕜 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [FiniteDimensional 𝕜 𝕜']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [FiniteDimensional 𝕜' F]

/-- Bounded `𝕜`-linear operators between finite-dimensional spaces form a finite-dimensional
space over a finite extension `𝕜'` of `𝕜` acting compatibly on the codomain, for instance over
`ℂ` for real-linear operators into a finite-dimensional complex space. -/
theorem finiteDimensional_of_isScalarTower : FiniteDimensional 𝕜' (E →L[𝕜] F) := by
  have : FiniteDimensional 𝕜 F := Module.Finite.trans 𝕜' F
  exact Module.Finite.of_restrictScalars_finite 𝕜 𝕜' (E →L[𝕜] F)

end ScalarExtension

section Invertible

variable {𝕜 U G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- An injective continuous linear map between finite-dimensional spaces of the same dimension is
invertible. -/
theorem isInvertible_of_injective_of_finrank_eq (A : U →L[𝕜] G)
    (hdim : Module.finrank 𝕜 U = Module.finrank 𝕜 G) (hinj : Function.Injective A) :
    A.IsInvertible := by
  exact ⟨((A : U →ₗ[𝕜] G).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv, rfl⟩

end Invertible

section Bordered

open Filter Function Module Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bordered operator `(w, μ) ↦ (L w + μ ℓ, ℓ w)` of `L : E → E*` and `ℓ ∈ E*`. -/
noncomputable def bordered (L : E →L[ℝ] StrongDual ℝ E) (ℓ : StrongDual ℝ E) :
    E × ℝ →L[ℝ] StrongDual ℝ E × ℝ :=
  prodL ℝ (coprodEquivL ℝ (L, toSpanSingleton ℝ ℓ), ℓ.comp (fst ℝ E ℝ))

@[simp]
theorem bordered_apply (L : E →L[ℝ] StrongDual ℝ E) (ℓ : StrongDual ℝ E) (z : E × ℝ) :
    L.bordered ℓ z = (L z.1 + z.2 • ℓ, ℓ z.1) := by
  simp [bordered]

/-- If the kernel of a symmetric `H₀ : E → E*` is the line spanned by `v` and `ℓ v = 1`, the
bordered operator of `H₀` and `ℓ` is injective. -/
theorem injective_bordered {H₀ : E →L[ℝ] StrongDual ℝ E}
    (hsymm : ∀ u w, H₀ u w = H₀ w u) {v : E} (hv : H₀ v = 0) {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1)
    (hker : ∀ u, H₀ u = 0 → ∃ c : ℝ, u = c • v) : Injective (H₀.bordered ℓ) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨w, μ⟩ h
  rw [bordered_apply, Prod.mk_eq_zero] at h
  obtain ⟨h1, h2⟩ := h
  -- Pairing the first component with `v` kills `H₀ w`, by symmetry, and leaves `μ`.
  have hμ : μ = 0 := by simpa [hsymm w v, hv, hℓ] using congrArg (· v) h1
  subst hμ
  obtain ⟨c, rfl⟩ := hker w (by simpa using h1)
  simp_all

/-- The bordered operator depends continuously on `L`. -/
theorem continuous_bordered (ℓ : StrongDual ℝ E) :
    Continuous fun L : E →L[ℝ] StrongDual ℝ E ↦ L.bordered ℓ :=
  (prodL ℝ).continuous.comp <|
    ((coprodEquivL ℝ).continuous.comp <| continuous_id.prodMk continuous_const).prodMk
      continuous_const

variable [FiniteDimensional ℝ E]

/-- **Kernel vectors near a corank-one symmetric operator.** Let `L z : E → E*` depend continuously
on `z` at `z₀`, with `L z₀` symmetric and its kernel the line spanned by `v`, and let `ℓ v = 1`.
Then there is a function `W`, tending to `v` at `z₀`, such that near `z₀`, whenever `L z` has a
nonzero kernel vector, `W z` is the kernel vector of `L z` normalized by `ℓ`. It is read off the
inverse of the bordered operator of `L z` and `ℓ`, which is invertible near `z₀`. -/
theorem exists_tendsto_eventually_apply_eq_zero {X : Type*} [TopologicalSpace X]
    {L : X → E →L[ℝ] StrongDual ℝ E} {z₀ : X} (hL : ContinuousAt L z₀)
    (hsymm : ∀ u w, L z₀ u w = L z₀ w u) {v : E} (hv : L z₀ v = 0) {ℓ : StrongDual ℝ E}
    (hℓ : ℓ v = 1) (hker : ∀ u, L z₀ u = 0 → ∃ c : ℝ, u = c • v) :
    ∃ W : X → E, Tendsto W (𝓝 z₀) (𝓝 v) ∧
      ∀ᶠ z in 𝓝 z₀, ∀ u, L z u = 0 → u ≠ 0 → L z (W z) = 0 ∧ ℓ (W z) = 1 := by
  set T := fun z ↦ (L z).bordered ℓ
  have hdim : finrank ℝ (E × ℝ) = finrank ℝ (StrongDual ℝ E × ℝ) := by
    simp [dual_finrank_eq]
  have hT₀ : (T z₀).IsInvertible := isInvertible_of_injective_of_finrank_eq _
    hdim (injective_bordered hsymm hv hℓ hker)
  have hTc : ContinuousAt T z₀ := (continuous_bordered ℓ).continuousAt.comp hL
  -- The inverse of the bordered operator at `z₀` sends `(0, 1)` to `(v, 0)`.
  have hT₀v : (T z₀).inverse (0, 1) = (v, 0) :=
    hT₀.inverse_apply_eq.2 (by simp [T, hv, hℓ])
  refine ⟨fun z ↦ ((T z).inverse (0, 1)).1, ?_, ?_⟩
  · have hinv : ContinuousAt (fun z ↦ (T z).inverse) z₀ :=
      (hT₀.contDiffAt_map_inverse (n := 0)).continuousAt.comp hTc
    have h := (continuous_fst.continuousAt.comp
      ((apply ℝ _ ((0 : StrongDual ℝ E), (1 : ℝ))).continuous.continuousAt.comp
        hinv)).tendsto
    simpa [Function.comp_def, hT₀v] using h
  · filter_upwards [hTc.eventually hT₀.eventually_nhds] with z hz u hu hu0
    -- The kernel vector `u` is not killed by `ℓ`, since `(u, 0)` is not killed by `T z`.
    have hℓu : ℓ u ≠ 0 := fun h0 ↦ hu0 <| congrArg Prod.fst <|
      hz.injective (a₁ := (u, 0)) (a₂ := 0) (by simp [T, hu, h0])
    have hW : (T z).inverse (0, 1) = ((ℓ u)⁻¹ • u, 0) :=
      hz.inverse_apply_eq.2 (by simp [T, hu, hℓu])
    simp [hW, hu, hℓu]

end Bordered

end ContinuousLinearMap

section MapsTo

open Filter Set Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Out of a finite-dimensional normed space over a complete field, the operators sending a
neighbourhood `s` of `0` into a compact set `K` form a compact set. -/
theorem IsCompact.isCompact_setOfPred_mapsTo {K : Set F} (hK : IsCompact K) {s : Set E}
    (hs : s ∈ 𝓝 (0 : E)) : IsCompact {T : E →L[𝕜] F | MapsTo T s K} := by
  -- An operator is determined by its values on a basis contained in `s`, and these values lie
  -- in `K`.
  let v := Module.finBasis 𝕜 E
  -- Some nonzero multiple `a • v` of a basis lies in `s`.
  have hev : ∀ᶠ a in 𝓝[≠] (0 : 𝕜), ∀ i, a • v i ∈ s := eventually_all.2 fun i ↦
    nhdsWithin_le_nhds <| (continuous_id.smul continuous_const).tendsto' 0 (0 : E)
      (zero_smul 𝕜 _) hs
  obtain ⟨a, hav, ha : a ≠ 0⟩ := (hev.and self_mem_nhdsWithin).exists
  -- Operators out of `E` are identified with their values on the basis `w = a • v` inside `s`.
  let w := v.map (LinearEquiv.smulOfNeZero 𝕜 E a ha)
  let e : (E →L[𝕜] F) ≃L[𝕜] (Fin _ → F) :=
    (w.equivFunL.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  refine (e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ ↦ hK)).of_isClosed_subset
    (hK.isClosed.setOfPred_mapsTo fun x _ ↦ continuous_eval_const x) fun T hT ↦ ?_
  simp only [mem_preimage, mem_univ_pi]
  intro i
  -- `piRing` evaluates at `Pi.single i 1`, the coordinate vector of `w i`; the inverse of
  -- `equivFunL` is that of `equivFun` by definition.
  have hwi : w.equivFunL.symm (Pi.single i 1) = w i := Basis.equivFun_symm_single w i
  have hw : w i = a • v i := by simp [w]
  change T (w.equivFunL.symm (Pi.single i 1)) ∈ K
  exact hwi ▸ hw ▸ hT (hav i)

end MapsTo
