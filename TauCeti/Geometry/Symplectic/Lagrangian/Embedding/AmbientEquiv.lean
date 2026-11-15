/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDerivative
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Topology.FiberBundle.Countable
import TauCeti.Topology.FiberBundle.Separation

/-!
# Ambient symplectic tangent equivalences and infinitesimal Lagrangian neighbourhoods

Along a Lagrangian embedding `i : Q → M` into a manifold equipped with a fiberwise nondegenerate
smooth two-form `σ` (not necessarily closed), the pullback `i^* σ` vanishes on `TQ`, whereas a
neighbourhood theorem requires a diffeomorphism whose pulled-back two-form agrees with `σ` on the
**full ambient tangent spaces** `T_(i q) M`. This file constructs the canonical linear polarization
connecting the two and combines it with the prescribed-derivative tubular neighbourhood theorem.

## Mathematical overview

Let `J_M` be a `σ`-compatible smooth almost complex structure on `M`. Then `J_M (di_q(T_q Q))` is
an isotropic complement to `di_q(T_q Q)` in `T_(i q) M`, and the positive-definite bilinear pairing
`γ_q(z, u) := σ_(i q)(di_q u, J_M (di_q z))` identifies `T_q Q` with `T_q^* Q`
(`TauCeti.SmoothEmbedding.inducedMetricFlat`). Inverting `γ_q` yields a smooth isotropic lift
`ℓ_q : (T_q Q →L[ℝ] ℝ) →L[ℝ] T_(i q) M`, `α ↦ J_M (di_q (γ_q⁻¹ α))`
(`TauCeti.SmoothEmbedding.isotropicLift`), and hence an explicit choice-free polarization
equivalence
`Φ_q : T_q Q × (T_q Q →L[ℝ] ℝ) ≃L[ℝ] T_(i q) M`, `(u, α) ↦ di_q u + ℓ_q α`
(`TauCeti.SmoothEmbedding.lagrangianPolarizationEquiv`), with explicit inverse
`w ↦ (γ_q⁻¹ (σ_(i q)(di_q ·, J_M w)), σ_(i q)(di_q ·, w))`, intertwining `σ_(i q)` with the
canonical linear cotangent pairing `((u₁, α₁), (u₂, α₂)) ↦ α₂ u₁ - α₁ u₂`
(`TauCeti.SmoothEmbedding.eval₂_lagrangianPolarizationEquiv`).

Given two Lagrangian embeddings `i : Q → M` (for `(M, σ)`) and `j : Q' → N` (for `(N, τ)`) over a
diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`, composing `Φ_i⁻¹`, the cotangent lift `(u, α) ↦ (df_q u,
α ∘ d(f⁻¹)_(f q))`, and `Φ_j` yields a smooth family of ambient symplectic equivalences
`T_(i q) M ≃L[ℝ] T_(j (f q)) N` extending `df_q`
(`TauCeti.SmoothEmbedding.ambientLagrangianEquiv`). Realizing this family by a tubular
neighbourhood diffeomorphism (`exists_diffeomorph_opens_mfderiv_eq_subset`) produces open
neighbourhoods `U` of `range i` and `V` of `range j` and `Ψ : U ≃ₘ⟮I, I'⟯ V` extending `f` along
which `Ψ^* (τ|_V)` and `σ|_U` agree on all ambient tangent spaces along `i(Q)`
(`IsLagrangianEmbedding.exists_diffeomorph_opens_mpullback_eq_at_subset`), and in particular a
neighbourhood comparison with the zero section of `CotangentBundle J Q`
(`IsLagrangianEmbedding.exists_diffeomorph_opens_cotangent_mpullback_eq_at_subset`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Theorem 3.33.
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

/-- Evaluating `inducedMetricFlat` at `z` and `u` computes `σ_(i q)(di_q u, J_M (di_q z))`. -/
@[simp]
theorem inducedMetricFlat_apply_apply (i : SmoothEmbedding J I ∞ Q M) (σ : SmoothTwoForm I M)
    (J_M : SmoothAlmostComplexStructure I M) (q : Q) (z u : TangentSpace J q) :
    i.inducedMetricFlat σ J_M q z u =
      σ.eval₂ (i q) (mfderiv J I i q u) (J_M (i q) (mfderiv J I i q z)) := by
  simp [inducedMetricFlat]

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

/-- For an isotropic embedding and a `σ`-invariant almost complex structure `J_M`, the image of
`isotropicLift` is `σ`-isotropic. -/
theorem eval₂_isotropicLift_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsIsotropicMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Invariant J_M) (q : Q)
    (α β : TangentSpace J q →L[ℝ] ℝ) :
    σ.eval₂ (i q) (i.isotropicLift σ J_M q α) (i.isotropicLift σ J_M q β) = 0 := by
  -- Unfold `isotropicLift` and evaluate `J_M.toEndomorphism` as `J_M`.
  change σ.eval₂ (i q)
      (J_M (i q) (mfderiv J I i q ((i.inducedMetricFlat σ J_M q).inverse α)))
      (J_M (i q) (mfderiv J I i q ((i.inducedMetricFlat σ J_M q).inverse β))) = 0
  rw [hJM.apply (i q), ← i.pairingCovector_apply_apply,
    i.pairingCovector_eq_zero_of_mem_tangentRange hi (by simp) q
      ((i.mem_tangentRange_iff q (by simp) _).2 ⟨_, rfl⟩),
    zero_apply]

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

/-- `inducedMetricFlat` is a smooth section of `Hom(TQ, T^*Q)`. -/
theorem contMDiff_inducedMetricFlat [IsManifold J ∞ Q] (i : SmoothEmbedding J I ∞ Q M)
    (σ : SmoothTwoForm I M) (J_M : SmoothAlmostComplexStructure I M) :
    ContMDiff J (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun q : Q ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q
        (i.inducedMetricFlat σ J_M q)) := by
  rw [TauCeti.contMDiff_hom_bundle_iff]
  have hproj : ContMDiff (J.prod 𝓘(ℝ, F)) J ∞ (π F (TangentSpace J : Q → Type _)) :=
    contMDiff_proj _
  have htan : ContMDiff (J.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) ∞ (tangentMap J I i) :=
    i.contMDiff.contMDiff_tangentMap le_rfl
  have hJtan : ContMDiff (J.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TangentBundle J Q ↦
        TotalSpace.mk' E (i p.proj) (J_M (i p.proj) (mfderiv J I i p.proj p.2))) :=
    (J_M.toEndomorphism.contMDiff.comp (i.contMDiff.comp hproj)).clm_bundle_apply htan
  have hflat : ContMDiff (J.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : TangentBundle J Q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (i p.proj) ((-σ).flat (i p.proj))) :=
    (-σ).contMDiff_flat.comp (i.contMDiff.comp hproj)
  have hΨ := ContMDiff.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ) (E₁ := TangentSpace I)
    (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) hflat hJtan
  refine (CotangentBundle.contMDiff_mk_comp_mfderiv (f := i) (g := TotalSpace.proj)
    (fun _ ↦ rfl) hΨ hproj i.contMDiff (by simp)).congr fun p ↦ ?_
  simp [inducedMetricFlat, i.pairingCovector_apply]

/-- Pairing `isotropicLift α` with tangent vectors of `Q` via `σ` reproduces `α`. -/
@[simp]
theorem pairingCovector_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (α : TangentSpace J q →L[ℝ] ℝ) :
    i.pairingCovector σ q (i.isotropicLift σ J_M q α) = α := by
  obtain ⟨e, he⟩ := i.isInvertible_inducedMetricFlat hJM q
  -- `pairingCovector ∘ J_M ∘ di_q` is definitionally `inducedMetricFlat`.
  change i.inducedMetricFlat σ J_M q ((i.inducedMetricFlat σ J_M q).inverse α) = α
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply α

/-- Pairing a pushed-forward tangent vector `di_q u` with `isotropicLift α` under `σ` gives
`α u`. -/
theorem eval₂_mfderiv_isotropicLift (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (u : TangentSpace J q) (α : TangentSpace J q →L[ℝ] ℝ) :
    σ.eval₂ (i q) (mfderiv J I i q u) (i.isotropicLift σ J_M q α) = α u := by
  rw [← i.pairingCovector_apply_apply, i.pairingCovector_isotropicLift hJM]

/-- **Explicit polarization of the ambient tangent space along a Lagrangian embedding.** Given a
Lagrangian embedding `i : Q → M` and a `σ`-compatible almost complex structure `J_M`, the map
`(u, α) ↦ di_q u + isotropicLift α` is a continuous linear equivalence
`T_q Q × (T_q Q →L[ℝ] ℝ) ≃L[ℝ] T_(i q) M` with explicit inverse
`w ↦ (γ_q⁻¹ (σ_(i q)(di_q ·, J_M w)), σ_(i q)(di_q ·, w))`. -/
def lagrangianPolarizationEquiv (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q) :
    (TangentSpace J q × (TangentSpace J q →L[ℝ] ℝ)) ≃L[ℝ] TangentSpace I (i q) :=
  let L := (mfderiv J I i q).coprod (i.isotropicLift σ J_M q)
  let R := (((i.inducedMetricFlat σ J_M q).inverse.comp
      ((i.pairingCovector σ q).comp (J_M.toEndomorphism (i q)))).prod
    (i.pairingCovector σ q))
  have hleft : LeftInverse R L := fun ⟨u, α⟩ ↦ by
    obtain ⟨e, he⟩ := i.isInvertible_inducedMetricFlat hJM q
    have hpair_di (z : TangentSpace J q) : i.pairingCovector σ q (mfderiv J I i q z) = 0 :=
      i.pairingCovector_eq_zero_of_mem_tangentRange hi.isIsotropicMap (by simp) q
        ((i.mem_tangentRange_iff q (by simp) _).2 ⟨z, rfl⟩)
    have hsnd : i.pairingCovector σ q (L (u, α)) = α := by
      simp [L, hpair_di u, i.pairingCovector_isotropicLift hJM q α]
    have hJlift : J_M (i q) (i.isotropicLift σ J_M q α) =
        -mfderiv J I i q ((i.inducedMetricFlat σ J_M q).inverse α) := by
      -- Evaluating `J_M (i q)` on `J_M.toEndomorphism (i q) (...)` applies `J_M² = -1`.
      change J_M (i q) (J_M (i q) (mfderiv J I i q ((i.inducedMetricFlat σ J_M q).inverse α))) = _
      exact J_M.apply_apply (i q) _
    have hfst_pair : i.pairingCovector σ q (J_M (i q) (L (u, α))) =
        i.inducedMetricFlat σ J_M q u := by
      have hJadd : J_M (i q) (L (u, α)) =
          J_M (i q) (mfderiv J I i q u) + J_M (i q) (i.isotropicLift σ J_M q α) :=
        map_add (J_M.toEndomorphism (i q)) (mfderiv J I i q u) (i.isotropicLift σ J_M q α)
      rw [hJadd, hJlift, map_add, map_neg, hpair_di, neg_zero, add_zero]
      rfl
    have hfst : (i.inducedMetricFlat σ J_M q).inverse
        (i.pairingCovector σ q (J_M (i q) (L (u, α)))) = u := by
      rw [hfst_pair, ← he, ContinuousLinearMap.inverse_equiv]
      exact e.symm_apply_apply u
    exact Prod.ext hfst hsnd
  have hR_inj : Function.Injective R := (injective_iff_map_eq_zero R).2 fun w hw ↦ by
    obtain ⟨e, he⟩ := i.isInvertible_inducedMetricFlat hJM q
    have hw2 : i.pairingCovector σ q w = 0 := congrArg Prod.snd hw
    obtain ⟨u₀, hu₀⟩ := (i.mem_tangentRange_iff q (by simp) w).1
      (i.mem_tangentRange_of_pairingCovector_eq_zero hi.isCoisotropicMap (by simp) q hw2)
    subst hu₀
    have hw1 : (i.inducedMetricFlat σ J_M q).inverse (i.inducedMetricFlat σ J_M q u₀) = 0 :=
      congrArg Prod.fst hw
    rw [← he, ContinuousLinearMap.inverse_equiv] at hw1
    have hu₀0 : u₀ = 0 := by simpa using congrArg e hw1
    simp [hu₀0]
  ContinuousLinearEquiv.equivOfInverse L R hleft fun w ↦ hR_inj (hleft (R w))

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

/-- The inverse polarization equivalence sends `di_q u` to `(u, 0)`. -/
@[simp]
theorem lagrangianPolarizationEquiv_symm_mfderiv (i : SmoothEmbedding J I ∞ Q M)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (u : TangentSpace J q) :
    (i.lagrangianPolarizationEquiv hi hJM q).symm (mfderiv J I i q u) = (u, 0) :=
  ((i.lagrangianPolarizationEquiv hi hJM q).symm_apply_eq).2
    (i.lagrangianPolarizationEquiv_inl hi hJM q u).symm

/-- `lagrangianPolarizationEquiv` intertwines the ambient form `σ_(i q)` with the canonical linear
cotangent pairing `((u₁, α₁), (u₂, α₂)) ↦ α₂ u₁ - α₁ u₂` on `T_q Q × (T_q Q →L[ℝ] ℝ)`. -/
theorem eval₂_lagrangianPolarizationEquiv (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M) (q : Q)
    (x y : TangentSpace J q × (TangentSpace J q →L[ℝ] ℝ)) :
    σ.eval₂ (i q) (i.lagrangianPolarizationEquiv hi hJM q x)
        (i.lagrangianPolarizationEquiv hi hJM q y) =
      y.2 x.1 - x.2 y.1 := by
  have hiso (u v : TangentSpace J q) :
      σ.eval₂ (i q) (mfderiv J I i q u) (mfderiv J I i q v) = 0 := by
    rw [← i.pairingCovector_apply_apply,
      i.pairingCovector_eq_zero_of_mem_tangentRange hi.isIsotropicMap (by simp) q
        ((i.mem_tangentRange_iff q (by simp) _).2 ⟨v, rfl⟩),
      zero_apply]
  have hswap (u : TangentSpace J q) (α : TangentSpace J q →L[ℝ] ℝ) :
      σ.eval₂ (i q) (i.isotropicLift σ J_M q α) (mfderiv J I i q u) = -α u := by
    rw [SmoothBundleForm.eval₂_swap, i.eval₂_mfderiv_isotropicLift hJM]
  simp only [lagrangianPolarizationEquiv_apply, SmoothBundleForm.eval₂_add_left,
    SmoothBundleForm.eval₂_add_right, hiso, hswap, i.eval₂_mfderiv_isotropicLift hJM,
    i.eval₂_isotropicLift_isotropicLift hi.isIsotropicMap hJM.invariant]
  ring

/-- Smoothness of `lagrangianPolarizationEquiv` applied to smooth sections along a map into `Q`. -/
theorem contMDiffAt_lagrangianPolarizationEquiv_apply {F₀ K₀ Q₀ : Type*}
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [TopologicalSpace K₀]
    {J₀ : ModelWithCorners ℝ F₀ K₀} [TopologicalSpace Q₀] [ChartedSpace K₀ Q₀]
    [IsManifold J ∞ Q] (i : SmoothEmbedding J I ∞ Q M) {σ : SmoothTwoForm I M}
    {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {b : Q₀ → Q} {q₀ : Q₀} (hb : ContMDiffAt J₀ J ∞ b q₀)
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
  have hinv := ((i.contMDiff_inducedMetricFlat σ J_M).clm_bundle_inverse
    (i.isInvertible_inducedMetricFlat hJM)).contMDiffAt.comp q₀ hb
  have hw : ContMDiffAt J₀ (J.prod 𝓘(ℝ, F)) ∞
      (fun z ↦ TotalSpace.mk' F (E := TangentSpace J) (b z)
        ((i.inducedMetricFlat σ J_M (b z)).inverse (α z))) q₀ :=
    ContMDiffAt.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
      (E₁ := fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) (E₂ := TangentSpace J) hinv hα
  have hdw : ContMDiffAt J₀ (I.prod 𝓘(ℝ, E)) ∞
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) (i (b z))
        (mfderiv J I i (b z) ((i.inducedMetricFlat σ J_M (b z)).inverse (α z)))) q₀ :=
    ((i.contMDiff.contMDiff_tangentMap le_rfl).contMDiffAt).comp q₀ hw
  have hlift : ContMDiffAt J₀ (I.prod 𝓘(ℝ, E)) ∞
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) (i (b z))
        (i.isotropicLift σ J_M (b z) (α z))) q₀ :=
    (J_M.toEndomorphism.contMDiff.contMDiffAt.comp q₀ ((i.contMDiff (b q₀)).comp q₀ hb)
      ).clm_bundle_apply hdw
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
  have hpair {w : ∀ q : Q, TangentSpace I (i q)}
      (hw : ContMDiffAt J (I.prod 𝓘(ℝ, E)) ∞ (fun q ↦ TotalSpace.mk' E (i q) (w q)) q₀) :
      ContMDiffAt J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
        (fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
          (E := fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) q (i.pairingCovector σ q (w q))) q₀ := by
    have hflat : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q : Q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (i q) ((-σ).flat (i q))) q₀ :=
      ((-σ).contMDiff_flat.contMDiffAt).comp q₀ (i.contMDiff q₀)
    have hΨ := ContMDiffAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ)
      (E₁ := TangentSpace I) (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) hflat hw
    refine (CotangentBundle.contMDiffAt_mk_comp_mfderiv (f := i) (g := _root_.id) (fun _ ↦ rfl)
      hΨ contMDiffAt_id (i.contMDiff q₀) (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    simp [i.pairingCovector_apply]
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
  [TopologicalSpace K] [TopologicalSpace K'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {J' : ModelWithCorners ℝ F' K'}
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace Q'] [ChartedSpace K' Q']
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- **Explicit ambient symplectic equivalence between two Lagrangian embeddings.** Given Lagrangian
embeddings `i : Q → M` and `j : Q' → N`, compatible almost complex structures `J_M` and `J_N`, and
a diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`, the composite of `(Φ_i q)⁻¹`, the linear cotangent lift
`(u, α) ↦ (df_q u, α ∘ d(f⁻¹)_(f q))`, and `Φ_j (f q)` is a symplectic linear equivalence
`T_(i q) M ≃L[ℝ] T_(j (f q)) N` extending `df_q`. -/
def ambientLagrangianEquiv (i : SmoothEmbedding J I ∞ Q M) (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) :
    TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)) :=
  let df : TangentSpace J q ≃L[ℝ] TangentSpace J' (f q) :=
    ContinuousLinearEquiv.equivOfInverse (mfderiv J J' f q) (mfderiv J' J f.symm (f q))
      (f.mfderiv_symm_apply_mfderiv_apply (by simp) q)
      (f.mfderiv_apply_mfderiv_symm_apply (by simp) q)
  (i.lagrangianPolarizationEquiv hi hJM q).symm.trans
    ((df.prodCongr (df.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).trans
      (j.lagrangianPolarizationEquiv hj hJN (f q)))

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
  dsimp only [ambientLagrangianEquiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, lagrangianPolarizationEquiv_symm_mfderiv,
    ContinuousLinearEquiv.prodCongr_apply, map_zero, lagrangianPolarizationEquiv_inl]
  rfl

/-- `ambientLagrangianEquiv` pulls `τ` at `j (f q)` back to `σ` at `i q` on the full ambient
tangent space. -/
theorem compContinuousLinearMap_ambientLagrangianEquiv (i : SmoothEmbedding J I ∞ Q M)
    (j : SmoothEmbedding J' I' ∞ Q' N)
    {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} (hi : hσ.IsLagrangianMap J i)
    {τ : SmoothTwoForm I' N} {hτ : τ.IsNondegenerate} (hj : hτ.IsLagrangianMap J' j)
    {J_M : SmoothAlmostComplexStructure I M} (hJM : σ.Compatible J_M)
    {J_N : SmoothAlmostComplexStructure I' N} (hJN : τ.Compatible J_N)
    (f : Q ≃ₘ⟮J, J'⟯ Q') (q : Q) :
    (τ.1 (j (f q))).compContinuousLinearMap
        (ambientLagrangianEquiv i j hi hj hJM hJN f q :
          TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) =
      σ.1 (i q) := by
  let A := ambientLagrangianEquiv i j hi hj hJM hJN f q
  have heval (u w : TangentSpace I (i q)) : τ.eval₂ (j (f q)) (A u) (A w) = σ.eval₂ (i q) u w := by
    dsimp only [A, ambientLagrangianEquiv]
    simp only [ContinuousLinearEquiv.trans_apply, j.eval₂_lagrangianPolarizationEquiv hj hJN,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [← i.eval₂_lagrangianPolarizationEquiv hi hJM q,
      (i.lagrangianPolarizationEquiv hi hJM q).apply_symm_apply,
      (i.lagrangianPolarizationEquiv hi hJM q).apply_symm_apply]
  ext v
  have hv : v = ![v 0, v 1] := funext fun k ↦ by fin_cases k <;> rfl
  have hAv : ((A : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘ v) =
      ![A (v 0), A (v 1)] := funext fun k ↦ by fin_cases k <;> rfl
  -- Evaluate `compContinuousLinearMap` as precomposition of the alternating map `τ.1 (j (f q))`.
  change τ.1 (j (f q)) ((A : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘ v) =
    σ.1 (i q) v
  rw [hAv, hv, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply]
  exact heval (v 0) (v 1)

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
    (CotangentBundle.contMDiffAt_mk_comp_mfderiv (f := f.symm) (g := f)
      (fun q ↦ (f.left_inv q).symm) hα (f.contMDiff q₀) (f.symm.contMDiff (f q₀))
      (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  refine (j.contMDiffAt_lagrangianPolarizationEquiv_apply hj hJN
    (f.contMDiff q₀) hu' hα').congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun _ ↦ rfl

end AmbientEquiv

end TauCeti.SmoothEmbedding

namespace TauCeti.CotangentBundle

variable {F K Q : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace K Q] [IsManifold J ∞ Q]

/-- On a finite-dimensional boundaryless manifold, the zero section of the cotangent bundle is a
smooth embedding. -/
theorem isSmoothEmbedding_zeroSection :
    Manifold.IsSmoothEmbedding J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (zeroSection (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ)) :=
  ⟨(contMDiff_zeroSection ℝ _).isImmersion_of_leftInverse (by simp)
      (fun _ ↦ ((contMDiff_proj (n := ∞) _).contMDiffAt).mdifferentiableAt (by simp))
      (fun _ ↦ rfl),
    Function.LeftInverse.isEmbedding (fun _ ↦ rfl) (FiberBundle.continuous_proj _ _)
      (Trivialization.continuous_zeroSection ℝ)⟩

/-- On a finite-dimensional boundaryless manifold, the zero section of the cotangent bundle is a
Lagrangian embedding for `CotangentBundle.symplecticForm`. -/
theorem isLagrangianEmbedding_zeroSection :
    (isSymplectic_symplecticForm (I := J) (M := Q)).isNondegenerate.IsLagrangianEmbedding J
      (zeroSection (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ)) :=
  (SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_iff_of_isSmoothEmbedding
    isSmoothEmbedding_zeroSection).2 isLagrangianMap_zeroSection

end TauCeti.CotangentBundle

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
embeddings `i : Q → M` and `j : Q' → N` into Hausdorff σ-compact manifolds equipped with
nondegenerate smooth two-forms `σ` and `τ` and any diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`, there
exists a smooth family of continuous linear equivalences `A q : T_(i q) M ≃L[ℝ] T_(j (f q)) N`
extending `df_q` and pulling `τ` back to `σ` on every ambient tangent fibre. -/
theorem IsLagrangianEmbedding.exists_ambientSymplecticEquiv
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
        (τ.1 (j (f q))).compContinuousLinearMap
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) = σ.1 (i q) := by
  by_cases hQ : Nonempty Q
  · obtain ⟨q₀⟩ := hQ
    let i_emb : SmoothEmbedding J I ∞ Q M :=
      ⟨⟨i, hi.isImmersion.contMDiff⟩, hi.isSmoothEmbedding⟩
    let j_emb : SmoothEmbedding J' I' ∞ Q' N :=
      ⟨⟨j, hj.isImmersion.contMDiff⟩, hj.isSmoothEmbedding⟩
    have := i_emb.finiteDimensional_tangentSpace q₀ (by simp)
    have : FiniteDimensional ℝ F := (tangentSpaceCastModel J q₀).toLinearEquiv.finiteDimensional
    have := j_emb.finiteDimensional_tangentSpace (f q₀) (by simp)
    have : FiniteDimensional ℝ F' :=
      (tangentSpaceCastModel J' (f q₀)).toLinearEquiv.finiteDimensional
    obtain ⟨J_M, hJM⟩ := hσ.exists_compatible
    obtain ⟨J_N, hJN⟩ := hτ.exists_compatible
    exact ⟨SmoothEmbedding.ambientLagrangianEquiv i_emb j_emb hi.isLagrangianMap
        hj.isLagrangianMap hJM hJN f,
      SmoothEmbedding.contMDiffAt_inTangentCoordinates_ambientLagrangianEquiv i_emb j_emb
        hi.isLagrangianMap hj.isLagrangianMap hJM hJN f,
      SmoothEmbedding.ambientLagrangianEquiv_comp_mfderiv i_emb j_emb hi.isLagrangianMap
        hj.isLagrangianMap hJM hJN f,
      SmoothEmbedding.compContinuousLinearMap_ambientLagrangianEquiv i_emb j_emb
        hi.isLagrangianMap hj.isLagrangianMap hJM hJN f⟩
  · have : IsEmpty Q := not_nonempty_iff.1 hQ
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- **Infinitesimal Lagrangian neighbourhood equivalence (with ambient open bounds).** Given two
Lagrangian embeddings `i : Q → M` and `j : Q' → N` of boundaryless manifolds into Hausdorff
second-countable boundaryless manifolds equipped with nondegenerate smooth two-forms `σ` and `τ`
(not necessarily closed) and a diffeomorphism `f : Q ≃ₘ⟮J, J'⟯ Q'`, there exist open
neighbourhoods `U ⊆ O_M` of `range i` and `V ⊆ O_N` of `range j` and a smooth diffeomorphism
`Ψ : U ≃ₘ⟮I, I'⟯ V` extending `f` such that `Ψ^* (τ|_V)` and `σ|_U` agree as full ambient
two-forms at every point of `i(Q)`. -/
theorem IsLagrangianEmbedding.exists_diffeomorph_opens_mpullback_eq_at_subset
    [FiniteDimensional ℝ F] [J.Boundaryless] [I.Boundaryless] [I'.Boundaryless]
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i)
    {j : Q' → N} (hj : hτ.IsLagrangianEmbedding J' j) (f : Q ≃ₘ⟮J, J'⟯ Q')
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_N : Set N} (hON : IsOpen O_N) (hjO : range j ⊆ O_N) :
    ∃ (U : Opens M) (V : Opens N) (Ψ : U ≃ₘ⟮I, I'⟯ V),
      (U : Set M) ⊆ O_M ∧ (V : Set N) ⊆ O_N ∧
      ∀ q : Q, ∃ hq : i q ∈ U, (Ψ ⟨i q, hq⟩ : N) = j (f q) ∧
        (SmoothForm.mpullback Ψ Ψ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtype_val τ)).1 ⟨i q, hq⟩ =
          (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ).1 ⟨i q, hq⟩ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace H' := I'.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  obtain ⟨A, hA, hAi, hAform⟩ := hi.exists_ambientSymplecticEquiv hj f
  obtain ⟨U, V, Ψ, hU, hV, hΨ⟩ := hi.isSmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq_subset
    hj.isSmoothEmbedding f A hA hAi hOM hiO hON hjO
  refine ⟨U, V, Ψ, hU, hV, fun q ↦ ?_⟩
  obtain ⟨hq, hval, hd⟩ := hΨ q
  exact ⟨hq, hval, SmoothForm.mpullback_eq_at_of_mfderiv_eq Ψ σ τ hval hd (hAform q)⟩

end TwoEmbeddings

section Cotangent

variable {F E K H Q M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace K] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H}
  [J.Boundaryless] [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace K Q] [IsManifold J ∞ Q]
  [T2Space Q] [SecondCountableTopology Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}

/-- **Infinitesimal Weinstein Lagrangian neighbourhood comparison with `T^* Q`.** Given a
Lagrangian embedding `i : Q → M` of a Hausdorff second-countable boundaryless manifold into a
Hausdorff second-countable boundaryless manifold `(M, σ)` (`σ` nondegenerate, not necessarily
closed), and open sets `O_M ⊇ range i` and `O_TQ ⊇ range 0_Q`, there exist open neighbourhoods
`U ⊆ O_M` of `range i` and `V ⊆ O_TQ` of the zero section in `CotangentBundle J Q` and a smooth
diffeomorphism `Ψ : U ≃ₘ⟮I, J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V` sending `i q` to `0_q` such that
`Ψ^* (ω_can|_V)` and `σ|_U` agree as full ambient two-forms at `i q` for every `q : Q`. -/
theorem IsLagrangianEmbedding.exists_diffeomorph_opens_cotangent_mpullback_eq_at_subset
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
            (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J Q) contMDiff_subtype_val
              (CotangentBundle.symplecticForm J Q))).1 ⟨i q, hq⟩ =
          (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ).1 ⟨i q, hq⟩ :=
  hi.exists_diffeomorph_opens_mpullback_eq_at_subset
    CotangentBundle.isLagrangianEmbedding_zeroSection (Diffeomorph.refl J Q ∞) hOM hiO hOTQ h0O

/-- **Infinitesimal Weinstein Lagrangian neighbourhood comparison with `T^* Q` (unbounded
ambient neighbourhoods).** Specializes
`exists_diffeomorph_opens_cotangent_mpullback_eq_at_subset` to `O_M = univ` and `O_TQ = univ`. -/
theorem IsLagrangianEmbedding.exists_diffeomorph_opens_cotangent_mpullback_eq_at
    {i : Q → M} (hi : hσ.IsLagrangianEmbedding J i) :
    ∃ (U : Opens M) (V : Opens (CotangentBundle J Q))
      (Ψ : U ≃ₘ⟮I, J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V),
      ∀ q : Q, ∃ hq : i q ∈ U,
        (Ψ ⟨i q, hq⟩ : CotangentBundle J Q) =
          zeroSection (F →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace J q →L[ℝ] ℝ) q ∧
        (SmoothForm.mpullback Ψ Ψ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J Q) contMDiff_subtype_val
              (CotangentBundle.symplecticForm J Q))).1 ⟨i q, hq⟩ =
          (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ).1 ⟨i q, hq⟩ := by
  obtain ⟨U, V, Ψ, -, -, hΨ⟩ :=
    hi.exists_diffeomorph_opens_cotangent_mpullback_eq_at_subset isOpen_univ (subset_univ _)
      isOpen_univ (subset_univ _)
  exact ⟨U, V, Ψ, hΨ⟩

end Cotangent

end TauCeti.SmoothTwoForm.IsNondegenerate
