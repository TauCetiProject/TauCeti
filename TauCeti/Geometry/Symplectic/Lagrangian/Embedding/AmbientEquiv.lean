/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Empty
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDifferential
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Topology.FiberBundle.Countable
import TauCeti.Topology.FiberBundle.Separation

/-!
# Ambient symplectic tangent equivalences and infinitesimal Lagrangian neighbourhoods

Along a Lagrangian embedding `i : Q → M` into a manifold equipped with a fiberwise nondegenerate
smooth two-form `σ` (not necessarily closed), the pullback `i^* σ` vanishes on `TQ`, whereas a
neighbourhood theorem requires a diffeomorphism whose pulled-back two-form agrees with `σ` on the
**full ambient tangent spaces** `T_(i q) M`. This file constructs the explicit smooth linear
polarization determined by a chosen `σ`-compatible almost complex structure `J_M` and combines it
with the prescribed-differential tubular neighbourhood theorem.

## Mathematical overview

Let `J_M` be a `σ`-compatible smooth almost complex structure on `M`. Then `J_M (di_q(T_q Q))` is
an isotropic complement to `di_q(T_q Q)` in `T_(i q) M`, and the positive-definite bilinear pairing
`γ_q(z, u) := σ_(i q)(di_q u, J_M (di_q z))` identifies `T_q Q` with `T_q^* Q`
(`TauCeti.SmoothEmbedding.inducedMetricFlat`). Inverting `γ_q` yields a smooth isotropic lift
`ℓ_q : (T_q Q →L[ℝ] ℝ) →L[ℝ] T_(i q) M`, `α ↦ J_M (di_q (γ_q⁻¹ α))`
(`TauCeti.SmoothEmbedding.isotropicLift`), and hence the explicit smooth linear polarization
equivalence determined by `J_M` (requiring no further local-frame or pointwise Witt-extension
choices)
`Φ_q : T_q Q × (T_q Q →L[ℝ] ℝ) ≃L[ℝ] T_(i q) M`, `(u, α) ↦ di_q u + ℓ_q α`
(`TauCeti.SmoothEmbedding.lagrangianPolarizationEquiv`), with explicit inverse
`w ↦ (γ_q⁻¹ (σ_(i q)(di_q ·, J_M w)), σ_(i q)(di_q ·, w))`, intertwining `σ_(i q)` with the
canonical linear cotangent pairing `TauCeti.strongDualCotangentSymplecticForm`
(`TauCeti.SmoothEmbedding.eval₂_lagrangianPolarizationEquiv`).

Given two Lagrangian embeddings `i : Q → M` (for `(M, σ)`) and `j : Q' → N` (for `(N, τ)`) over a
diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`, composing `Φ_i⁻¹`, the cotangent lift `(df_q).cotangent`, and
`Φ_j` yields a smooth family of ambient symplectic equivalences
`T_(i q) M ≃L[ℝ] T_(j (f q)) N` extending `df_q`
(`TauCeti.SmoothEmbedding.ambientLagrangianEquiv`). Realizing this family by a partial
diffeomorphism (`exists_partialDiffeomorph_mfderiv_eq`) produces open neighbourhoods `U` of
`range i` and `V` of `range j` and `Ψ : U ≃ₘ⟮I, I'⟯ V` extending `f` along which `Ψ^* (τ|_V)` and
`σ|_U` agree on all ambient tangent spaces along `i(Q)`
(`IsLagrangianEmbedding.exists_diffeomorph_opens_mpullback_apply_eq_subset`), and in particular a
neighbourhood comparison with the zero section of `CotangentBundle J Q`
(`IsLagrangianEmbedding.exists_diffeomorph_opens_cotangent_mpullback_apply_eq_subset`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.4 and Section 9 (Theorem 9.3).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.4, Theorem 3.4.13.
* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346.
-/

public noncomputable section

open Bundle Function Manifold Module Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

section Polarization

variable {F E K H Q M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace K] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The flat musical map `T_q Q →L[ℝ] (T_q Q →L[ℝ] ℝ)` of the metric induced along `i` by `σ` and
`J_M`, sending `z` to `u ↦ σ_(i q)(di_q u, J_M (di_q z))`. -/
def inducedMetricFlat (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) :
    TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ :=
  (i.pairingCovector σ q).comp ((J_M.toEndomorphism (i q)).comp (mfderiv J I i q))

/-- Evaluating `inducedMetricFlat` at `z` pulls back `J_M (di_q z)` via `pairingCovector`. -/
-- Not `@[simp]` so `inducedMetricFlat_apply_apply` remains in `simp` normal form.
theorem inducedMetricFlat_apply (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) (z : TangentSpace J q) :
    i.inducedMetricFlat σ J_M q z =
      i.pairingCovector σ q (J_M (i q) (mfderiv J I i q z)) :=
  (rfl)

/-- Evaluating `inducedMetricFlat` at `z` and `u` computes `σ_(i q)(di_q u, J_M (di_q z))`. -/
@[simp]
theorem inducedMetricFlat_apply_apply (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) (z u : TangentSpace J q) :
    i.inducedMetricFlat σ J_M q z u =
      σ.eval₂ (i q) (mfderiv J I i q u) (J_M (i q) (mfderiv J I i q z)) := by
  simp [inducedMetricFlat_apply]

/-- When `J_M` is `σ`-compatible, `inducedMetricFlat` is injective on every tangent fibre. -/
theorem inducedMetricFlat_injective (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q) :
    Function.Injective (i.inducedMetricFlat σ J_M q) := by
  refine (injective_iff_map_eq_zero (i.inducedMetricFlat σ J_M q)).2 fun z hz ↦ ?_
  by_contra hz0
  have hdz : mfderiv J I i q z ≠ 0 :=
    fun h ↦ hz0 ((i.isImmersion.mfderiv_injective (by simp) q) (h.trans (map_zero _).symm))
  have hpos := (SmoothTwoForm.tames_iff.1 hJM.tames) (i q) (mfderiv J I i q z) hdz
  have hzero : i.inducedMetricFlat σ J_M q z z = 0 := by rw [hz]; rfl
  rw [inducedMetricFlat_apply_apply] at hzero
  exact hpos.ne' hzero

/-- The isotropic lift `(T_q Q →L[ℝ] ℝ) →L[ℝ] T_(i q) M` associated with `σ` and `J_M`, sending a
covector `α` to `J_M (di_q (γ_q⁻¹ α))`. -/
def isotropicLift (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) :
    (TangentSpace J q →L[ℝ] ℝ) →L[ℝ] TangentSpace I (i q) :=
  (J_M.toEndomorphism (i q)).comp
    ((mfderiv J I i q).comp (i.inducedMetricFlat σ J_M q).inverse)

/-- Evaluating `isotropicLift` at `α` applies `J_M (i q) ∘ di_q` to `γ_q⁻¹ α`. -/
-- Not `@[simp]` so higher-level cancellation lemmas (`pairingCovector_isotropicLift`,
-- `eval₂_mfderiv_isotropicLift`, `lagrangianPolarizationEquiv_symm_isotropicLift`) stay in `simp`
-- normal form.
theorem isotropicLift_apply (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) (α : TangentSpace J q →L[ℝ] ℝ) :
    i.isotropicLift σ J_M q α =
      J_M (i q) (mfderiv J I i q ((i.inducedMetricFlat σ J_M q).inverse α)) :=
  (rfl)

/-- Applying `J_M (i q)` to `isotropicLift α` negates the tangent lift `-di_q (γ_q⁻¹ α)`. -/
@[simp]
theorem apply_isotropicLift (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) (α : TangentSpace J q →L[ℝ] ℝ) :
    J_M (i q) (i.isotropicLift σ J_M q α) =
      -mfderiv J I i q ((i.inducedMetricFlat σ J_M q).inverse α) := by
  rw [isotropicLift_apply, J_M.apply_apply]

/-- For an isotropic embedding and a `σ`-invariant almost complex structure `J_M`, the image of
`isotropicLift` is `σ`-isotropic. -/
theorem eval₂_isotropicLift_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsIsotropicMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Invariant J_M) (q : Q)
    (α β : TangentSpace J q →L[ℝ] ℝ) :
    σ.eval₂ (i q) (i.isotropicLift σ J_M q α) (i.isotropicLift σ J_M q β) = 0 := by
  rw [isotropicLift_apply, isotropicLift_apply, hJM.apply (i q)]
  exact (SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff.1 hi) q _ _

variable [FiniteDimensional ℝ F]

/-- When `J_M` is `σ`-compatible, `inducedMetricFlat` is invertible as a continuous linear map on
every tangent fibre. -/
theorem isInvertible_inducedMetricFlat (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q) :
    (i.inducedMetricFlat σ J_M q).IsInvertible := by
  have hinj := i.inducedMetricFlat_injective hJM q
  have hdim : finrank ℝ (TangentSpace J q) = finrank ℝ (TangentSpace J q →L[ℝ] ℝ) := by
    rw [← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]
  have hbij : Function.Bijective (i.inducedMetricFlat σ J_M q).toLinearMap :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  exact ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-- When `J_M` is `σ`-compatible, `(inducedMetricFlat σ J_M q).inverse` is a left inverse to
`inducedMetricFlat σ J_M q`. -/
@[simp]
theorem inverse_inducedMetricFlat_inducedMetricFlat (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    (q : Q) (z : TangentSpace J q) :
    (i.inducedMetricFlat σ J_M q).inverse (i.inducedMetricFlat σ J_M q z) = z :=
  (i.isInvertible_inducedMetricFlat hJM q).inverse_apply_self z

/-- When `J_M` is `σ`-compatible, `(inducedMetricFlat σ J_M q).inverse` is a right inverse to
`inducedMetricFlat σ J_M q`. -/
@[simp]
theorem inducedMetricFlat_inverse_inducedMetricFlat (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    (q : Q) (α : TangentSpace J q →L[ℝ] ℝ) :
    i.inducedMetricFlat σ J_M q ((i.inducedMetricFlat σ J_M q).inverse α) = α :=
  (i.isInvertible_inducedMetricFlat hJM q).self_apply_inverse α

/-- `inducedMetricFlat` is a smooth section of `Hom(TQ, T^*Q)`. -/
theorem contMDiff_inducedMetricFlat [IsManifold J ∞ Q] (i : SmoothEmbedding J I ∞ Q M)
    (σ : SmoothTwoForm I M) (J_M : SmoothAlmostComplexStructure I M) :
    ContMDiff J (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun q : Q ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q
        (i.inducedMetricFlat σ J_M q)) := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  rw [TauCeti.contMDiff_hom_bundle_iff]
  have hproj : ContMDiff (J.prod 𝓘(ℝ, F)) J ∞ (π F (TangentSpace J : Q → Type _)) :=
    contMDiff_proj _
  have htan : ContMDiff (J.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) ∞ (tangentMap J I i) :=
    i.contMDiff.contMDiff_tangentMap le_rfl
  have hJtan : ContMDiff (J.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TangentBundle J Q ↦
        TotalSpace.mk' E (i p.proj) (J_M (i p.proj) (mfderiv J I i p.proj p.snd))) :=
    (J_M.toEndomorphism.contMDiff.comp (i.contMDiff.comp hproj)).clm_bundle_apply htan
  have hpull : ContMDiff (J.prod 𝓘(ℝ, F)) (J.prod 𝓘(ℝ, E)) ∞
      (fun p : TangentBundle J Q ↦
        TotalSpace.mk' E (E := (i : Q → M) *ᵖ (TangentSpace I)) p.proj
          (J_M (i p.proj) (mfderiv J I i p.proj p.snd))) :=
    (Bundle.Pullback.contMDiff_iff (E := TangentSpace I) i i.contMDiff).2 ⟨hproj, hJtan⟩
  exact (i.contMDiff_pairingCovector σ (m := ∞) le_rfl le_rfl).comp hpull

/-- When `J_M` is `σ`-compatible, `isotropicLift` induces a smooth map from `CotangentBundle J Q`
to `TangentBundle I M`. -/
theorem contMDiff_isotropicLift [IsManifold J ∞ Q] (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) :
    ContMDiff (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : CotangentBundle J Q ↦
        (TotalSpace.mk' E (i p.proj)
          (i.isotropicLift σ J_M p.proj p.snd) : TangentBundle I M)) := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  have hproj : ContMDiff (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) J ∞
      (π (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ)) :=
    contMDiff_proj _
  have hinv := ((i.contMDiff_inducedMetricFlat σ J_M).clm_bundle_inverse
    (i.isInvertible_inducedMetricFlat hJM)).comp hproj
  have hw : ContMDiff (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F)) ∞
      (fun p : CotangentBundle J Q ↦
        TotalSpace.mk' F (E := TangentSpace J) p.proj
          ((i.inducedMetricFlat σ J_M p.proj).inverse p.snd)) :=
    ContMDiff.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
      (E₁ := fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) (E₂ := TangentSpace J) hinv contMDiff_id
  have hdw : ContMDiff (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : CotangentBundle J Q ↦
        TotalSpace.mk' E (E := TangentSpace I) (i p.proj)
          (mfderiv J I i p.proj ((i.inducedMetricFlat σ J_M p.proj).inverse p.snd))) :=
    (i.contMDiff.contMDiff_tangentMap le_rfl).comp hw
  exact (J_M.toEndomorphism.contMDiff.comp (i.contMDiff.comp hproj)).clm_bundle_apply hdw

/-- Pairing `isotropicLift α` with tangent vectors of `Q` via `σ` reproduces `α`. -/
@[simp]
theorem pairingCovector_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (α : TangentSpace J q →L[ℝ] ℝ) :
    i.pairingCovector σ q (i.isotropicLift σ J_M q α) = α := by
  rw [isotropicLift_apply, ← inducedMetricFlat_apply,
    i.inducedMetricFlat_inverse_inducedMetricFlat hJM]

/-- Pairing a pushed-forward tangent vector `di_q u` with `isotropicLift α` under `σ` gives
`α u`. -/
-- Not `@[simp]` because `SmoothBundleForm.eval₂_apply` already simplifies `SmoothBundleForm.eval₂`.
theorem eval₂_mfderiv_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (u : TangentSpace J q) (α : TangentSpace J q →L[ℝ] ℝ) :
    σ.eval₂ (i q) (mfderiv J I i q u) (i.isotropicLift σ J_M q α) = α u := by
  rw [← i.pairingCovector_apply_apply, i.pairingCovector_isotropicLift hJM]

/-- For an isotropic embedding `i` and a `σ`-compatible almost complex structure `J_M`, the
coordinate map `w ↦ (γ_q⁻¹ (σ_(i q)(di_q ·, J_M w)), σ_(i q)(di_q ·, w))` is a left inverse to
`(u, α) ↦ di_q u + isotropicLift α`. -/
theorem leftInverse_coprod_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsIsotropicMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q) :
    LeftInverse
      (((i.inducedMetricFlat σ J_M q).inverse.comp
          ((i.pairingCovector σ q).comp (J_M.toEndomorphism (i q)))).prod
        (i.pairingCovector σ q))
      ((mfderiv J I i q).coprod (i.isotropicLift σ J_M q)) := fun ⟨u, α⟩ ↦ by
  simp [← inducedMetricFlat_apply, i.inverse_inducedMetricFlat_inducedMetricFlat hJM,
    i.pairingCovector_mfderiv_eq_zero hi, i.pairingCovector_isotropicLift hJM]

/-- For a coisotropic embedding `i` and a `σ`-compatible almost complex structure `J_M`, the
coordinate map `w ↦ (γ_q⁻¹ (σ_(i q)(di_q ·, J_M w)), σ_(i q)(di_q ·, w))` is injective. -/
theorem prod_pairingCovector_injective (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsCoisotropicMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q) :
    Function.Injective
      (((i.inducedMetricFlat σ J_M q).inverse.comp
          ((i.pairingCovector σ q).comp (J_M.toEndomorphism (i q)))).prod
        (i.pairingCovector σ q)) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  obtain ⟨u₀, rfl⟩ := (i.mem_tangentRange_iff q (by simp) w).1
    (i.mem_tangentRange_of_pairingCovector_eq_zero hi (by simp) q (congrArg Prod.snd hw))
  have hu₀ : u₀ = 0 := by
    simpa [← inducedMetricFlat_apply, i.inverse_inducedMetricFlat_inducedMetricFlat hJM] using
      congrArg Prod.fst hw
  simp [hu₀]

/-- **Explicit polarization of the ambient tangent space along a Lagrangian embedding.** Given a
Lagrangian embedding `i : Q → M` and a `σ`-compatible almost complex structure `J_M`, the map
`(u, α) ↦ di_q u + isotropicLift α` is a continuous linear equivalence
`T_q Q × (T_q Q →L[ℝ] ℝ) ≃L[ℝ] T_(i q) M` with explicit inverse
`w ↦ (γ_q⁻¹ (σ_(i q)(di_q ·, J_M w)), σ_(i q)(di_q ·, w))`. -/
def lagrangianPolarizationEquiv (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q) :
    (TangentSpace J q × (TangentSpace J q →L[ℝ] ℝ)) ≃L[ℝ] TangentSpace I (i q) :=
  let R := (((i.inducedMetricFlat σ J_M q).inverse.comp
      ((i.pairingCovector σ q).comp (J_M.toEndomorphism (i q)))).prod
    (i.pairingCovector σ q))
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((mfderiv J I i q).coprod (i.isotropicLift σ J_M q)) R
    (ContinuousLinearMap.ext fun w ↦
      i.prod_pairingCovector_injective hi.isCoisotropicMap hJM q
        (i.leftInverse_coprod_isotropicLift hi.isIsotropicMap hJM q (R w)))
    (ContinuousLinearMap.ext (i.leftInverse_coprod_isotropicLift hi.isIsotropicMap hJM q))

/-- Evaluating `lagrangianPolarizationEquiv` adds `di_q x.1` and `isotropicLift x.2`. -/
theorem lagrangianPolarizationEquiv_apply (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (x : TangentSpace J q × (TangentSpace J q →L[ℝ] ℝ)) :
    i.lagrangianPolarizationEquiv hi hJM q x =
      mfderiv J I i q x.1 + i.isotropicLift σ J_M q x.2 :=
  (rfl)

/-- Evaluating `(lagrangianPolarizationEquiv)⁻¹` computes the `γ_q⁻¹`-lifted pairing with `J_M w`
and the pairing covector of `w`. -/
theorem lagrangianPolarizationEquiv_symm_apply (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (w : TangentSpace I (i q)) :
    (i.lagrangianPolarizationEquiv hi hJM q).symm w =
      ((i.inducedMetricFlat σ J_M q).inverse (i.pairingCovector σ q (J_M (i q) w)),
        i.pairingCovector σ q w) :=
  (rfl)

/-- On the zero covector factor `(u, 0)`, `lagrangianPolarizationEquiv` reduces to `di_q u`. -/
@[simp]
theorem lagrangianPolarizationEquiv_inl (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (u : TangentSpace J q) :
    i.lagrangianPolarizationEquiv hi hJM q (u, 0) = mfderiv J I i q u := by
  simp [lagrangianPolarizationEquiv_apply]

/-- On the zero tangent factor `(0, α)`, `lagrangianPolarizationEquiv` reduces to
`isotropicLift α`. -/
@[simp]
theorem lagrangianPolarizationEquiv_inr (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (α : TangentSpace J q →L[ℝ] ℝ) :
    i.lagrangianPolarizationEquiv hi hJM q (0, α) = i.isotropicLift σ J_M q α := by
  simp [lagrangianPolarizationEquiv_apply]

/-- The inverse polarization equivalence sends `di_q u` to `(u, 0)`. -/
@[simp]
theorem lagrangianPolarizationEquiv_symm_mfderiv (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (u : TangentSpace J q) :
    (i.lagrangianPolarizationEquiv hi hJM q).symm (mfderiv J I i q u) = (u, 0) :=
  ((i.lagrangianPolarizationEquiv hi hJM q).symm_apply_eq).2
    (i.lagrangianPolarizationEquiv_inl hi hJM q u).symm

/-- The inverse polarization equivalence sends `isotropicLift α` to `(0, α)`. -/
@[simp]
theorem lagrangianPolarizationEquiv_symm_isotropicLift (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (α : TangentSpace J q →L[ℝ] ℝ) :
    (i.lagrangianPolarizationEquiv hi hJM q).symm (i.isotropicLift σ J_M q α) = (0, α) :=
  ((i.lagrangianPolarizationEquiv hi hJM q).symm_apply_eq).2
    (i.lagrangianPolarizationEquiv_inr hi hJM q α).symm

/-- `lagrangianPolarizationEquiv` intertwines the ambient form `σ_(i q)` with the canonical linear
cotangent symplectic form `strongDualCotangentSymplecticForm` on
`T_q Q × (T_q Q →L[ℝ] ℝ)`. -/
theorem eval₂_lagrangianPolarizationEquiv (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (x y : TangentSpace J q × (TangentSpace J q →L[ℝ] ℝ)) :
    σ.eval₂ (i q) (i.lagrangianPolarizationEquiv hi hJM q x)
        (i.lagrangianPolarizationEquiv hi hJM q y) =
      strongDualCotangentSymplecticForm x y := by
  have hswap (u : TangentSpace J q) (α : TangentSpace J q →L[ℝ] ℝ) :
      σ.eval₂ (i q) (i.isotropicLift σ J_M q α) (mfderiv J I i q u) = -α u := by
    rw [SmoothBundleForm.eval₂_swap, i.eval₂_mfderiv_isotropicLift hJM]
  simp only [lagrangianPolarizationEquiv_apply, SmoothBundleForm.eval₂_add_left,
    SmoothBundleForm.eval₂_add_right, ← i.pairingCovector_apply_apply,
    i.pairingCovector_mfderiv_eq_zero hi.isIsotropicMap, zero_apply,
    i.pairingCovector_isotropicLift hJM, hswap,
    i.eval₂_isotropicLift_isotropicLift hi.isIsotropicMap hJM.invariant,
    strongDualCotangentSymplecticForm_apply]
  ring

/-- Smoothness of `lagrangianPolarizationEquiv` applied to smooth sections along a map into `Q`. -/
theorem contMDiffAt_lagrangianPolarizationEquiv_apply {F₀ K₀ Q₀ : Type*}
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [TopologicalSpace K₀]
    {J₀ : ModelWithCorners ℝ F₀ K₀} [TopologicalSpace Q₀] [ChartedSpace K₀ Q₀]
    [IsManifold J ∞ Q] (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {b : Q₀ → Q} {q₀ : Q₀}
    {u : ∀ z : Q₀, TangentSpace J (b z)} {α : ∀ z : Q₀, TangentSpace J (b z) →L[ℝ] ℝ}
    (hu : ContMDiffAt J₀ (J.prod 𝓘(ℝ, F)) ∞
      (fun z ↦ TotalSpace.mk' F (E := TangentSpace J) (b z) (u z)) q₀)
    (hα : ContMDiffAt J₀ (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun z ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) (b z) (α z)) q₀) :
    ContMDiffAt J₀ (I.prod 𝓘(ℝ, E)) ∞
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) (i (b z))
        (i.lagrangianPolarizationEquiv hi hJM (b z) (u z, α z))) q₀ := by
  have hdu : ContMDiffAt J₀ (I.prod 𝓘(ℝ, E)) ∞
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) (i (b z)) (mfderiv J I i (b z) (u z))) q₀ :=
    ((i.contMDiff.contMDiff_tangentMap le_rfl).contMDiffAt).comp q₀ hu
  have hlift : ContMDiffAt J₀ (I.prod 𝓘(ℝ, E)) ∞
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) (i (b z))
        (i.isotropicLift σ J_M (b z) (α z))) q₀ :=
    ((i.contMDiff_isotropicLift hJM).contMDiffAt).comp q₀ hα
  exact hdu.add_sectionAlong hlift

/-- Smoothness of both components of `(lagrangianPolarizationEquiv)⁻¹` applied to a smooth ambient
tangent lift along `i`. -/
theorem contMDiffAt_lagrangianPolarizationEquiv_symm [IsManifold J ∞ Q]
    (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}
    (hi : hσ.IsLagrangianMap J i) {J_M : SmoothAlmostComplexStructure I M}
    (hJM : σ.Compatible J_M) {q₀ : Q} {s : ∀ q : Q, TangentSpace I (i q)}
    (hs : ContMDiffAt J (I.prod 𝓘(ℝ, E)) ∞ (fun q ↦ TotalSpace.mk' E (i q) (s q)) q₀) :
    ContMDiffAt J (J.prod 𝓘(ℝ, F)) ∞
        (fun q ↦ TotalSpace.mk' F q ((i.lagrangianPolarizationEquiv hi hJM q).symm (s q)).1) q₀ ∧
      ContMDiffAt J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ) q
          ((i.lagrangianPolarizationEquiv hi hJM q).symm (s q)).2) q₀ := by
  have : IsManifold J 1 Q := .of_le (n := ∞) (by simp)
  have hpair {w : ∀ q : Q, TangentSpace I (i q)}
      (hw : ContMDiffAt J (I.prod 𝓘(ℝ, E)) ∞ (fun q ↦ TotalSpace.mk' E (i q) (w q)) q₀) :
      ContMDiffAt J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
          (E := fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) q (i.pairingCovector σ q (w q))) q₀ := by
    have hlift : ContMDiffAt J (J.prod 𝓘(ℝ, E)) ∞
        (fun q ↦ TotalSpace.mk' E (E := (i : Q → M) *ᵖ (TangentSpace I)) q (w q)) q₀ :=
      (Bundle.Pullback.contMDiffAt_iff (E := TangentSpace I) i
        (q := fun q ↦ TotalSpace.mk' E (E := (i : Q → M) *ᵖ (TangentSpace I)) q (w q))
        (i.contMDiff q₀)).2 ⟨contMDiffAt_id, hw⟩
    exact ((i.contMDiff_pairingCovector σ (m := ∞) le_rfl le_rfl).contMDiffAt).comp q₀ hlift
  have hJs : ContMDiffAt J (I.prod 𝓘(ℝ, E)) ∞
      (fun q ↦ TotalSpace.mk' E (i q) (J_M (i q) (s q))) q₀ :=
    ((J_M.toEndomorphism.contMDiff.contMDiffAt).comp q₀ (i.contMDiff q₀)).clm_bundle_apply hs
  have hinv := ((i.contMDiff_inducedMetricFlat σ J_M).clm_bundle_inverse
    (i.isInvertible_inducedMetricFlat hJM)) q₀
  exact ⟨ContMDiffAt.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
    (E₁ := fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) (E₂ := TangentSpace J) hinv (hpair hJs),
    hpair hs⟩

end Polarization

section AmbientEquiv

variable {F F' E E' K K' H H' Q Q' M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace K] [TopologicalSpace K']
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {J' : ModelWithCorners ℝ F' K'}
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace Q'] [ChartedSpace K' Q']
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- **Explicit ambient symplectic equivalence between two Lagrangian embeddings.** Given Lagrangian
embeddings `i : Q → M` and `j : Q' → N`, compatible almost complex structures `J_M` and `J_N`, and
a diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`, the composite of `(Φ_i q)⁻¹`, the linear cotangent lift
`(df_q).cotangent`, and `Φ_j (f q)` is a symplectic linear equivalence
`T_(i q) M ≃L[ℝ] T_(j (f q)) N` extending `df_q`. -/
def ambientLagrangianEquiv (i : SmoothEmbedding J I ∞ Q M) (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) :
    TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)) :=
  (i.lagrangianPolarizationEquiv hi hJM q).symm.trans
    ((f.mfderivToContinuousLinearEquiv (by simp) q).cotangent.trans
      (j.lagrangianPolarizationEquiv hj hJN (f q)))

/-- Evaluating `ambientLagrangianEquiv` decomposes `w` via `(lagrangianPolarizationEquiv)⁻¹`,
transports `(u, α)` by `(df_q, · ∘ d(f⁻¹)_(f q))`, and re-embeds via `lagrangianPolarizationEquiv`
along `j`. -/
-- Not `@[simp]` so the summand evaluation lemmas (`ambientLagrangianEquiv_mfderiv` and
-- `ambientLagrangianEquiv_isotropicLift`) remain in `simp` normal form.
theorem ambientLagrangianEquiv_apply (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (w : TangentSpace I (i q)) :
    ambientLagrangianEquiv i j hi hj hJM hJN f q w =
      j.lagrangianPolarizationEquiv hj hJN (f q)
        (mfderiv J J' f q ((i.lagrangianPolarizationEquiv hi hJM q).symm w).1,
          ((i.lagrangianPolarizationEquiv hi hJM q).symm w).2 ∘L
            mfderiv J' J f.symm (f q)) := by
  simp only [ambientLagrangianEquiv, ContinuousLinearEquiv.trans_apply]
  congr 1
  refine Prod.ext (by simp) (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [ContinuousLinearEquiv.cotangent_apply_snd_apply]
  exact congr_arg _ (f.mfderivToContinuousLinearEquiv_symm_apply (by simp) q v)

/-- Evaluating `(ambientLagrangianEquiv)⁻¹` decomposes `z` via `(lagrangianPolarizationEquiv)⁻¹`
along `j`, transports by `(d(f⁻¹)_(f q), · ∘ df_q)`, and re-embeds via `lagrangianPolarizationEquiv`
along `i`. -/
theorem ambientLagrangianEquiv_symm_apply (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (z : TangentSpace I' (j (f q))) :
    (ambientLagrangianEquiv i j hi hj hJM hJN f q).symm z =
      i.lagrangianPolarizationEquiv hi hJM q
        (mfderiv J' J f.symm (f q) ((j.lagrangianPolarizationEquiv hj hJN (f q)).symm z).1,
          ((j.lagrangianPolarizationEquiv hj hJN (f q)).symm z).2 ∘L
            mfderiv J J' f q) := by
  simp only [ambientLagrangianEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.cotangent_symm]
  congr 1
  refine Prod.ext ?_ (ContinuousLinearMap.ext fun _ ↦ by simp)
  simp only [ContinuousLinearEquiv.cotangent_apply_fst]
  exact f.mfderivToContinuousLinearEquiv_symm_apply (by simp) q _

/-- On pushed-forward tangent vectors `di_q u`, `ambientLagrangianEquiv` agrees with
`dj_(f q) (df_q u)`. -/
@[simp]
theorem ambientLagrangianEquiv_mfderiv (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (u : TangentSpace J q) :
    ambientLagrangianEquiv i j hi hj hJM hJN f q (mfderiv J I i q u) =
      mfderiv J' I' j (f q) (mfderiv J J' f q u) := by
  simp only [ambientLagrangianEquiv, ContinuousLinearEquiv.trans_apply,
    lagrangianPolarizationEquiv_symm_mfderiv]
  have hcot : (f.mfderivToContinuousLinearEquiv (by simp) q).cotangent (u, 0) =
      (mfderiv J J' f q u, 0) :=
    Prod.ext (by simp) (ContinuousLinearMap.ext fun _ ↦ by simp)
  rw [hcot, j.lagrangianPolarizationEquiv_inl]

/-- On `i.isotropicLift σ J_M q α`, `ambientLagrangianEquiv` produces `j.isotropicLift` of the
pulled-back covector `α ∘L d(f⁻¹)_(f q)`. -/
@[simp]
theorem ambientLagrangianEquiv_isotropicLift (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (α : TangentSpace J q →L[ℝ] ℝ) :
    ambientLagrangianEquiv i j hi hj hJM hJN f q (i.isotropicLift σ J_M q α) =
      j.isotropicLift τ J_N (f q) (α ∘L mfderiv J' J f.symm (f q)) := by
  simp [ambientLagrangianEquiv_apply]

/-- `(ambientLagrangianEquiv)⁻¹` sends `dj_(f q) v` to `di_q (d(f⁻¹)_(f q) v)`. -/
@[simp]
theorem ambientLagrangianEquiv_symm_mfderiv (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (v : TangentSpace J' (f q)) :
    (ambientLagrangianEquiv i j hi hj hJM hJN f q).symm (mfderiv J' I' j (f q) v) =
      mfderiv J I i q (mfderiv J' J f.symm (f q) v) := by
  simp only [ambientLagrangianEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.cotangent_symm,
    j.lagrangianPolarizationEquiv_symm_mfderiv]
  have hcot : (f.mfderivToContinuousLinearEquiv (by simp) q).symm.cotangent (v, 0) =
      ((f.mfderivToContinuousLinearEquiv (by simp) q).symm v, 0) :=
    Prod.ext (by simp) (ContinuousLinearMap.ext fun _ ↦ by simp)
  rw [hcot, i.lagrangianPolarizationEquiv_inl]
  exact congr_arg (mfderiv J I i q) (f.mfderivToContinuousLinearEquiv_symm_apply (by simp) q v)

/-- `(ambientLagrangianEquiv)⁻¹` sends `j.isotropicLift τ J_N (f q) β` to `i.isotropicLift` of
`β ∘L df_q`. -/
@[simp]
theorem ambientLagrangianEquiv_symm_isotropicLift (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (β : TangentSpace J' (f q) →L[ℝ] ℝ) :
    (ambientLagrangianEquiv i j hi hj hJM hJN f q).symm (j.isotropicLift τ J_N (f q) β) =
      i.isotropicLift σ J_M q (β ∘L mfderiv J J' f q) := by
  simp only [ambientLagrangianEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.cotangent_symm,
    j.lagrangianPolarizationEquiv_symm_isotropicLift]
  have hcot : (f.mfderivToContinuousLinearEquiv (by simp) q).symm.cotangent (0, β) =
      (0, β ∘L mfderiv J J' f q) :=
    Prod.ext (by simp) (ContinuousLinearMap.ext fun _ ↦ by simp)
  rw [hcot, i.lagrangianPolarizationEquiv_inr]

/-- `ambientLagrangianEquiv` extends `df_q` along `i` and `j`. -/
theorem ambientLagrangianEquiv_comp_mfderiv (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) :
    (ambientLagrangianEquiv i j hi hj hJM hJN f q :
        TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i q =
      (mfderiv J' I' j (f q)).comp (mfderiv J J' f q) := by
  ext u
  simp

/-- `ambientLagrangianEquiv` intertwines `σ.eval₂ (i q)` and `τ.eval₂ (j (f q))`. -/
-- Not `@[simp]` because `SmoothBundleForm.eval₂_apply` already simplifies `SmoothBundleForm.eval₂`.
theorem eval₂_ambientLagrangianEquiv (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) (u w : TangentSpace I (i q)) :
    τ.eval₂ (j (f q)) (ambientLagrangianEquiv i j hi hj hJM hJN f q u)
        (ambientLagrangianEquiv i j hi hj hJM hJN f q w) =
      σ.eval₂ (i q) u w := by
  simp only [ambientLagrangianEquiv, ContinuousLinearEquiv.trans_apply,
    j.eval₂_lagrangianPolarizationEquiv hj hJN,
    (f.mfderivToContinuousLinearEquiv (by simp) q).strongDualCotangentSymplecticForm_cotangent,
    ← i.eval₂_lagrangianPolarizationEquiv hi hJM q,
    (i.lagrangianPolarizationEquiv hi hJM q).apply_symm_apply]

/-- `ambientLagrangianEquiv` pulls `τ` at `j (f q)` back to `σ` at `i q` on the full ambient
tangent space. -/
theorem compContinuousLinearMap_ambientLagrangianEquiv (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) :
    (τ.val (j (f q))).compContinuousLinearMap
        (ambientLagrangianEquiv i j hi hj hJM hJN f q :
          TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) =
      σ.val (i q) := by
  ext v
  have hv : v = ![v 0, v 1] := by ext k; fin_cases k <;> rfl
  rw [hv, ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two,
    ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply]
  exact eval₂_ambientLagrangianEquiv i j hi hj hJM hJN f q (v 0) (v 1)

/-- `ambientLagrangianEquiv` depends smoothly on `q` in `inTangentCoordinates`. -/
theorem contMDiffAt_inTangentCoordinates_ambientLagrangianEquiv
    [FiniteDimensional ℝ E] [IsManifold J ∞ Q] [IsManifold J' ∞ Q']
    (i : SmoothEmbedding J I ∞ Q M) (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q₀ : Q) :
    ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') ∞
      (inTangentCoordinates I I' i (j ∘ f)
        (fun q ↦ (ambientLagrangianEquiv i j hi hj hJM hJN f q :
          TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q)))) q₀) q₀ := by
  rw [TauCeti.Manifold.contMDiffAt_inTangentCoordinates_iff (i.contMDiff q₀)
    ((j.contMDiff.comp f.contMDiff) q₀)]
  intro s hs
  obtain ⟨hu, hα⟩ := i.contMDiffAt_lagrangianPolarizationEquiv_symm hi hJM hs
  have hu' : ContMDiffAt J (J'.prod 𝓘(ℝ, F')) ∞
      (fun q ↦ TotalSpace.mk' F' (E := TangentSpace J') (f q)
        (mfderiv J J' f q ((i.lagrangianPolarizationEquiv hi hJM q).symm (s q)).1)) q₀ :=
    ((f.contMDiff.contMDiff_tangentMap le_rfl).contMDiffAt).comp q₀ hu
  have hα' : ContMDiffAt J (J'.prod 𝓘(ℝ, F' →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (F' →L[ℝ] ℝ)
        (E := fun y : Q' ↦ TangentSpace J' y →L[ℝ] ℝ) (f q)
        (((i.lagrangianPolarizationEquiv hi hJM q).symm (s q)).2 ∘L
          mfderiv J' J f.symm (f q))) q₀ :=
    CotangentBundle.contMDiffAt_mk_comp_mfderiv (f := f.symm) (g := f)
      (fun q ↦ (f.left_inv q).symm) hα (f.contMDiff q₀) (f.symm.contMDiff (f q₀)) (by simp)
  simp only [ContinuousLinearEquiv.coe_coe, ambientLagrangianEquiv_apply]
  exact j.contMDiffAt_lagrangianPolarizationEquiv_apply hj hJN hu' hα'

end AmbientEquiv

end TauCeti.SmoothEmbedding

namespace TauCeti.SmoothTwoForm.IsNondegenerate

section TwoEmbeddings

variable {F F' E E' K K' H H' Q Q' M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace K] [TopologicalSpace K'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {J' : ModelWithCorners ℝ F' K'}
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q] [IsManifold J ∞ Q]
  [TopologicalSpace Q'] [ChartedSpace K' Q'] [IsManifold J' ∞ Q']
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}
  {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate}

/-- **Existence of compatible ambient symplectic bundle equivalences.** For any two Lagrangian
embeddings `i : Q → M` and `j : Q' → N` into finite-dimensional Hausdorff σ-compact manifolds
equipped with nondegenerate smooth two-forms `σ` and `τ` and any diffeomorphism
`f : Q ≃ₘ⟮J, J'⟯ Q'`, there exists a smooth family of continuous linear equivalences
`A q : T_(i q) M ≃L[ℝ] T_(j (f q)) N` extending `df_q` and pulling `τ` back to `σ` on every ambient
tangent fibre. -/
theorem IsLagrangianEmbedding.exists_continuousLinearEquiv_compContinuousLinearMap_eq
    [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N]
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i)
    {j : Q' → N} (hj : hτ.IsLagrangianEmbedding J' j) (f : Q ≃ₘ⟮J, J'⟯ Q') :
    ∃ A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)),
      (∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') ∞
        (inTangentCoordinates I I' i (j ∘ f)
          (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q)))) q₀) q₀) ∧
      (∀ q : Q,
        (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i q =
          (mfderiv J' I' j (f q)).comp (mfderiv J J' f q)) ∧
      ∀ q : Q,
        (τ.val (j (f q))).compContinuousLinearMap
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) = σ.val (i q) := by
  by_cases hQ : Nonempty Q
  · obtain ⟨q₀⟩ := hQ
    have : FiniteDimensional ℝ F :=
      finiteDimensional_of_injective_mfderiv (hi.isImmersion.mfderiv_injective (by simp) q₀)
    have : FiniteDimensional ℝ F' :=
      finiteDimensional_of_injective_mfderiv (hj.isImmersion.mfderiv_injective (by simp) (f q₀))
    obtain ⟨J_M, hJM⟩ := hσ.exists_compatible
    obtain ⟨J_N, hJN⟩ := hτ.exists_compatible
    exact ⟨SmoothEmbedding.ambientLagrangianEquiv hi.toSmoothEmbedding hj.toSmoothEmbedding
        hi.isLagrangianMap hj.isLagrangianMap hJM hJN f,
      SmoothEmbedding.contMDiffAt_inTangentCoordinates_ambientLagrangianEquiv
        hi.toSmoothEmbedding hj.toSmoothEmbedding hi.isLagrangianMap hj.isLagrangianMap hJM hJN f,
      SmoothEmbedding.ambientLagrangianEquiv_comp_mfderiv hi.toSmoothEmbedding hj.toSmoothEmbedding
        hi.isLagrangianMap hj.isLagrangianMap hJM hJN f,
      SmoothEmbedding.compContinuousLinearMap_ambientLagrangianEquiv hi.toSmoothEmbedding
        hj.toSmoothEmbedding hi.isLagrangianMap hj.isLagrangianMap hJM hJN f⟩
  · have : IsEmpty Q := not_nonempty_iff.1 hQ
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- **Infinitesimal Lagrangian neighbourhood equivalence (with ambient open bounds).** Given two
Lagrangian embeddings `i : Q → M` and `j : Q' → N` of finite-dimensional boundaryless manifolds into
finite-dimensional Hausdorff second-countable boundaryless manifolds equipped with nondegenerate
smooth two-forms `σ` and `τ` (not necessarily closed) and a diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`,
there exist open neighbourhoods `U ⊆ O_M` of `range i` and `V ⊆ O_N` of `range j` and a smooth
diffeomorphism `Ψ : U ≃ₘ⟮I, I'⟯ V` extending `f` such that `Ψ^* (τ|_V)` and `σ|_U` agree as full
ambient two-forms at every point of `i(Q)`. -/
theorem IsLagrangianEmbedding.exists_diffeomorph_opens_mpullback_apply_eq_subset
    [J.Boundaryless] [I.Boundaryless] [I'.Boundaryless]
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i)
    {j : Q' → N} (hj : hτ.IsLagrangianEmbedding J' j) (f : Q ≃ₘ⟮J, J'⟯ Q')
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_N : Set N} (hON : IsOpen O_N) (hjO : range j ⊆ O_N) :
    ∃ (U : Opens M) (V : Opens N) (Ψ : U ≃ₘ⟮I, I'⟯ V),
      (U : Set M) ⊆ O_M ∧ (V : Set N) ⊆ O_N ∧
      ∀ q : Q, ∃ hq : i q ∈ U, (Ψ ⟨i q, hq⟩ : N) = j (f q) ∧
        (SmoothForm.mpullback Ψ Ψ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtypeVal τ)).val ⟨i q, hq⟩ =
          (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ).val ⟨i q, hq⟩ := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ x.property⟩
    have : IsEmpty (⊥ : Opens N) := ⟨fun y ↦ y.property⟩
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, empty_subset O_M, empty_subset O_N, fun q ↦ isEmptyElim q⟩
  · obtain ⟨q₀⟩ := id hQ
    have : FiniteDimensional ℝ F :=
      finiteDimensional_of_injective_mfderiv (hi.isImmersion.mfderiv_injective (by simp) q₀)
    have : LocallyCompactSpace H := I.locallyCompactSpace
    have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    have : LocallyCompactSpace H' := I'.locallyCompactSpace
    have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
    obtain ⟨A, hA, hAi, hAform⟩ :=
      hi.exists_continuousLinearEquiv_compContinuousLinearMap_eq hj f
    have hg : ContMDiff J I' ∞ (j ∘ f) := hj.isImmersion.contMDiff.comp f.contMDiff
    have hgi : IsInducing (j ∘ f) := hj.isEmbedding.isInducing.comp f.toHomeomorph.isInducing
    have hgO : range (j ∘ f) ⊆ O_N := by
      rintro _ ⟨q, rfl⟩
      exact hjO (mem_range_self (f q))
    have hAi' (q : Q) :
        (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L
            mfderiv J I hi.toSmoothEmbedding q =
          mfderiv J I' (j ∘ f) q :=
      (hAi q).trans (mfderiv_comp q (hj.isImmersion.contMDiff.mdifferentiableAt (by simp))
        (f.contMDiff.mdifferentiableAt (by simp))).symm
    obtain ⟨Ψ, hsrc, hU, hV, hval, hd⟩ :=
      hi.toSmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq hg hgi hA (fun q ↦ ⟨A q, rfl⟩) hAi'
        hOM hiO hON hgO
    refine ⟨⟨Ψ.source, Ψ.open_source⟩, ⟨Ψ.target, Ψ.open_target⟩,
      Ψ.toDiffeomorphSourceTarget, hU, hV, fun q ↦ ?_⟩
    have hq : i q ∈ Ψ.source := hsrc (mem_range_self q)
    refine ⟨hq, (Ψ.toDiffeomorphSourceTarget_apply_coe ⟨i q, hq⟩).trans (hval q), ?_⟩
    simp only [SmoothForm.coe_mpullback]
    exact mpullback_toDiffeomorphSourceTarget_apply_eq_of_mfderiv_eq Ψ (by simp) hq (hval q)
      (hd q) (hAform q)

end TwoEmbeddings

section Cotangent

variable {F E K H Q M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace K] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H}
  [J.Boundaryless] [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace K Q] [IsManifold J ∞ Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}

/-- **Infinitesimal Weinstein Lagrangian neighbourhood comparison with `T^* Q`.** Given a
Lagrangian embedding `i : Q → M` of a finite-dimensional boundaryless manifold into a
finite-dimensional Hausdorff second-countable boundaryless manifold `(M, σ)` (`σ` nondegenerate, not
necessarily closed), and open sets `O_M ⊇ range i` and `O_TQ ⊇ range 0_Q`, there exist open
neighbourhoods `U ⊆ O_M` of `range i` and `V ⊆ O_TQ` of the zero section in `CotangentBundle J Q`
and a smooth diffeomorphism `Ψ : U ≃ₘ⟮I, J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V` sending `i q` to `0_q` such that
`Ψ^* (ω_can|_V)` and `σ|_U` agree as full ambient two-forms at `i q` for every `q : Q`. -/
theorem IsLagrangianEmbedding.exists_diffeomorph_opens_cotangent_mpullback_apply_eq_subset
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i)
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_TQ : Set (CotangentBundle J Q)} (hOTQ : IsOpen O_TQ)
    (h0O : range (zeroSection (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ)) ⊆ O_TQ) :
    ∃ (U : Opens M) (V : Opens (CotangentBundle J Q))
      (Ψ : U ≃ₘ⟮I, J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V),
      (U : Set M) ⊆ O_M ∧ (V : Set (CotangentBundle J Q)) ⊆ O_TQ ∧
      ∀ q : Q, ∃ hq : i q ∈ U,
        (Ψ ⟨i q, hq⟩ : CotangentBundle J Q) =
          zeroSection (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) q ∧
        (SmoothForm.mpullback Ψ Ψ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J Q) contMDiff_subtypeVal
              (CotangentBundle.symplecticForm J Q))).val ⟨i q, hq⟩ =
          (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ).val ⟨i q, hq⟩ := by
  have : T2Space Q := hi.isEmbedding.t2Space
  have : SecondCountableTopology Q := hi.isEmbedding.isInducing.secondCountableTopology
  exact hi.exists_diffeomorph_opens_mpullback_apply_eq_subset
    CotangentBundle.isLagrangianEmbedding_zeroSection (Diffeomorph.refl J Q ∞) hOM hiO hOTQ h0O

/-- **Infinitesimal Weinstein Lagrangian neighbourhood comparison with `T^* Q` (unbounded
ambient neighbourhoods).** Specializes
`exists_diffeomorph_opens_cotangent_mpullback_apply_eq_subset` to `O_M = univ` and `O_TQ = univ`. -/
theorem IsLagrangianEmbedding.exists_diffeomorph_opens_cotangent_mpullback_apply_eq
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i) :
    ∃ (U : Opens M) (V : Opens (CotangentBundle J Q))
      (Ψ : U ≃ₘ⟮I, J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V),
      ∀ q : Q, ∃ hq : i q ∈ U,
        (Ψ ⟨i q, hq⟩ : CotangentBundle J Q) =
          zeroSection (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) q ∧
        (SmoothForm.mpullback Ψ Ψ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J Q) contMDiff_subtypeVal
              (CotangentBundle.symplecticForm J Q))).val ⟨i q, hq⟩ =
          (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ).val ⟨i q, hq⟩ := by
  obtain ⟨U, V, Ψ, -, -, hΨ⟩ :=
    hi.exists_diffeomorph_opens_cotangent_mpullback_apply_eq_subset isOpen_univ (subset_univ _)
      isOpen_univ (subset_univ _)
  exact ⟨U, V, Ψ, hΨ⟩

end Cotangent

end TauCeti.SmoothTwoForm.IsNondegenerate
