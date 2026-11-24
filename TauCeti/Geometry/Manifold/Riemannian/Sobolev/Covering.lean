/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Covering.Deck
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Covering
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry

/-!
# The Sobolev space `H¹` under finite Riemannian coverings

Let a finite group `G` act on a compact Riemannian manifold `M`, and let `q : M → N` be a quotient
covering map for this action (`IsQuotientCoveringMap q G`) which is a local Riemannian isometry
onto a compact Riemannian manifold `N`. This is the situation of the projection `X → X / H` of a
closed Riemannian manifold onto its quotient by a finite group `H` of isometries acting freely,
with the quotient metric. Pulling back along `q` preserves the pointwise inner product
`⟪∇u, ∇v⟫` of gradients and multiplies integrals by the covering degree `|G|`
(`IsQuotientCoveringMap.integral_comp_riemannianVolume`), so on smooth functions

`⟪u ∘ q, v ∘ q⟫_{H¹(M)} = |G| ⟪u, v⟫_{H¹(N)}`.

Hence the **normalized pullback** `J = |G| ^ (-1/2) q^*` extends to a linear isometry

`TauCeti.Manifold.SobolevH1.normalizedPullback hq hf : H¹(N) →ₗᵢ H¹(M)`.

Its value in `L²(M)` is the normalized pullback `IsQuotientCoveringMap.normalizedPullbackLp` of
the value in `L²(N)`, and it preserves the Dirichlet form: `q_M(J w, J v) = q_N(w, v)` for all
`w, v ∈ H¹(N)`. Its range is exactly the deck-invariant subspace of `H¹(M)`: the elements fixed
by pullback along every deck transformation `x ↦ g • x`, which is a Riemannian isometry of `M`
(`IsQuotientCoveringMap.deckIsometry`). One inclusion holds for every Riemannian isometry `Φ` of `M`
with `q ∘ Φ = q`. Conversely, the average `|G|⁻¹ ∑_g (g ·)^*` over the deck transformations fixes
every invariant element. It sends a smooth function to the pullback of a smooth function on `N`,
since smooth invariant functions descend along the local diffeomorphism `q`. So the average maps
`H¹(M)` into the closure of the range, which is closed because `J` is an isometry out of a complete
space.

These are the `H¹` and energy-form parts of Bérard's transplantation of eigenfunctions of the
Laplacian between the quotients of one manifold by almost-conjugate subgroups.

## Main declarations

* `TauCeti.Manifold.SobolevH1.inner_ofSmooth_comp_of_isQuotientCoveringMap`: pullback along `q`
  multiplies the `H¹` inner product of smooth functions by `|G|`.
* `TauCeti.Manifold.SobolevH1.normalizedPullback`: the normalized pullback `H¹(N) →ₗᵢ H¹(M)`,
  with `TauCeti.Manifold.SobolevH1.normalizedPullback_ofSmooth` on smooth functions.
* `TauCeti.Manifold.SobolevH1.toLp_normalizedPullback`: compatibility with the normalized pullback
  on `L²`.
* `TauCeti.Manifold.SobolevH1.dirichletForm_normalizedPullback`: the energy-form identity.
* `TauCeti.Manifold.SobolevH1.compRiemannianIsometry_normalizedPullback`: the range consists of
  deck-invariant elements.
* `TauCeti.Manifold.SobolevH1.mem_range_normalizedPullback_iff`: the range is exactly the
  deck-invariant subspace.

## References

* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Lemma 16 and Comment 18, pp. 159–160.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  {q : M → N}

/-- Precomposition `u ↦ u ∘ q` with a local Riemannian isometry, on smooth functions. -/
private def compSmoothOfIsLocalRiemannianIsometry (hf : IsLocalRiemannianIsometry I I' q) :
    C^∞⟮I', N; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun u := u.comp ⟨q, hf.contMDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The average `|G|⁻¹ ∑_g u ∘ (g • ·)` of a smooth function over the deck transformations is the
pullback of a smooth function on `N`. -/
private theorem exists_comp_eq_smul_sum_comp_deckIsometry [CompleteSpace E]
    [BoundarylessManifold I M] [IsManifold I ∞ M] [IsManifold I' ∞ N]
    {G : Type*} [Group G] [MulAction G M] [Fintype G] (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (u : C^∞⟮I, M; ℝ⟯) :
    ∃ v : C^∞⟮I', N; ℝ⟯, ContMDiffMap.comp v ⟨q, hf.contMDiff⟩ = (Fintype.card G : ℝ)⁻¹ •
      ∑ g : G, u.comp (hq.deckIsometry hf g).toDiffeomorph.toContMDiffMap := by
  set a : C^∞⟮I, M; ℝ⟯ :=
    (Fintype.card G : ℝ)⁻¹ • ∑ g : G, u.comp (hq.deckIsometry hf g).toDiffeomorph.toContMDiffMap
  have ha (x : M) : a x = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, u (g • x) := by
    simp [a, ContMDiffMap.coe_sum]
  have hinv (h : G) (x : M) : a (h • x) = a x := by
    rw [ha, ha]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g ↦ by simp [mul_smul]
  obtain ⟨v, hv, hvq⟩ := hq.exists_contMDiff_comp_eq (hf.isLocalDiffeomorph (n := ∞) (by simp)
    le_rfl) le_rfl a.contMDiff hinv
  exact ⟨⟨v, hv⟩, ContMDiffMap.ext fun x ↦ congrFun hvq x⟩

variable [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold I 1 M] [MeasurableSpace M]
  [BorelSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [CompactSpace N] [IsManifold I' 1 N] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]
  {G : Type*} [Group G] [MulAction G M] [Finite G]

/-- **The `H¹` inner product under a finite covering.** Pullback along a finite quotient covering
map `q : M → N` which is a local Riemannian isometry multiplies
`∫ u v dV + ∫ ⟪∇u, ∇v⟫ dV` by the covering degree `|G|`, for smooth functions `u`, `v` on `N`. -/
theorem inner_ofSmooth_comp_of_isQuotientCoveringMap (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (u v : C^∞⟮I', N; ℝ⟯) :
    ⟪ofSmooth (u.comp ⟨q, hf.contMDiff⟩), ofSmooth (v.comp ⟨q, hf.contMDiff⟩)⟫_ℝ =
      Nat.card G * ⟪ofSmooth u, ofSmooth v⟫_ℝ := by
  have hu := u.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  have hv := v.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  have hgrad (x : M) :
      ⟪mgradient I (u.comp ⟨q, hf.contMDiff⟩) x, mgradient I (v.comp ⟨q, hf.contMDiff⟩) x⟫_ℝ =
        ⟪mgradient I' u (q x), mgradient I' v (q x)⟫_ℝ :=
    hf.inner_mgradient_comp_comp (hu.mdifferentiable one_ne_zero _)
      (hv.mdifferentiable one_ne_zero _)
  rw [inner_ofSmooth, inner_ofSmooth, mul_add]
  simp only [hgrad]
  congr 1
  · rw [← nsmul_eq_mul]
    exact hq.integral_comp_riemannianVolume hf.inner_mfderiv (f := fun y ↦ u y * v y)
      ((map_continuous u).mul (map_continuous v)).aestronglyMeasurable
  · rw [← nsmul_eq_mul]
    exact hq.integral_comp_riemannianVolume hf.inner_mfderiv
      (f := fun y ↦ ⟪mgradient I' u y, mgradient I' v y⟫_ℝ)
      (continuous_inner_mgradient hu hv).aestronglyMeasurable

/-- The normalized pullback `|G| ^ (-1/2) (u ∘ q)` of a smooth function has the `H¹` norm of
`u`. -/
private theorem norm_smul_ofSmooth_compSmooth (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (u : C^∞⟮I', N; ℝ⟯) :
    ‖(Nat.card G : ℝ) ^ (-(1 / 2 : ℝ)) • ofSmooth (compSmoothOfIsLocalRiemannianIsometry hf u)‖ =
      ‖ofSmooth u‖ := by
  have hG : (0 : ℝ) < Nat.card G := Nat.cast_pos.2 Nat.card_pos
  have hnorm : ‖ofSmooth (compSmoothOfIsLocalRiemannianIsometry hf u)‖ =
      Real.sqrt (Nat.card G) * ‖ofSmooth u‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (ofSmooth u),
      ← Real.sqrt_mul hG.le]
    exact congrArg Real.sqrt (inner_ofSmooth_comp_of_isQuotientCoveringMap hq hf u u)
  rw [norm_smul, hnorm, Real.norm_of_nonneg (by positivity), Real.rpow_neg hG.le,
    ← Real.sqrt_eq_rpow, inv_mul_cancel_left₀ (by positivity)]

/-- **The normalized pullback on `H¹`.** For a finite quotient covering map `q : M → N` which is
a local Riemannian isometry, the normalized pullback `u ↦ |G| ^ (-1/2) (u ∘ q)` of smooth
functions extends to a linear isometry `H¹(N) →ₗᵢ H¹(M)`
(`TauCeti.Manifold.SobolevH1.normalizedPullback_ofSmooth`). -/
def normalizedPullback (hq : IsQuotientCoveringMap q G) (hf : IsLocalRiemannianIsometry I I' q) :
    SobolevH1 I' N →ₗᵢ[ℝ] SobolevH1 I M :=
  ((Nat.card G : ℝ) ^ (-(1 / 2 : ℝ)) •
      (ofSmooth ∘ₗ compSmoothOfIsLocalRiemannianIsometry hf)).extendOfIsometry
    denseRange_ofSmooth (norm_smul_ofSmooth_compSmooth hq hf)

/-- The normalized pullback sends the class of a smooth function `u` to `|G| ^ (-1/2)` times the
class of `u ∘ q`. -/
@[simp]
theorem normalizedPullback_ofSmooth (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (u : C^∞⟮I', N; ℝ⟯) :
    normalizedPullback hq hf (ofSmooth u) =
      (Nat.card G : ℝ) ^ (-(1 / 2 : ℝ)) • ofSmooth (u.comp ⟨q, hf.contMDiff⟩) :=
  LinearMap.extendOfIsometry_eq _ _ _ u

/-- **Compatibility with `L²`.** The value in `L²(M)` of the normalized pullback of `w ∈ H¹(N)`
is the normalized pullback `|G| ^ (-1/2) q^*` of the value of `w` in `L²(N)`. -/
theorem toLp_normalizedPullback (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (w : SobolevH1 I' N) :
    toLp (normalizedPullback hq hf w) = hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv (toLp w) := by
  refine congrFun (denseRange_ofSmooth.equalizer
    (g := fun w ↦ toLp (normalizedPullback hq hf w))
    (toLp.continuous.comp (LinearIsometry.continuous _))
    ((LinearIsometry.continuous _).comp toLp.continuous) (funext fun u ↦ ?_)) w
  have hc : (Nat.card G : ℝ) ^ (-(1 / (2 : ENNReal)).toReal) =
      (Nat.card G : ℝ) ^ (-(1 / 2 : ℝ)) := by
    norm_num
  simp only [Function.comp_apply]
  rw [normalizedPullback_ofSmooth, map_smul]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul ((Nat.card G : ℝ) ^ (-(1 / 2 : ℝ)))
      (toLp (ofSmooth (u.comp ⟨q, hf.contMDiff⟩))),
    toLp_ofSmooth_ae_eq (u.comp ⟨q, hf.contMDiff⟩),
    hq.coeFn_normalizedPullbackLp (𝕜 := ℝ) hf.inner_mfderiv (toLp (ofSmooth u)),
    (QuasiMeasurePreserving.of_map_le_smul hq.continuous.aemeasurable
      (hq.map_riemannianVolume hf.inner_mfderiv).le).ae_eq_comp (toLp_ofSmooth_ae_eq u)]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, Algebra.algebraMap_self_apply, hc, Pi.smul_apply, h₂]
  exact congrArg _ h₄.symm

/-- **The energy-form identity.** The normalized pullback preserves the Dirichlet form, the
extension of `∫ ⟪∇u, ∇v⟫ dV` to `H¹`: `q_M(J w, J v) = q_N(w, v)`. -/
@[simp]
theorem dirichletForm_normalizedPullback (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (w v : SobolevH1 I' N) :
    dirichletForm (normalizedPullback hq hf w) (normalizedPullback hq hf v) =
      dirichletForm w v := by
  rw [dirichletForm_apply, dirichletForm_apply, LinearIsometry.inner_map_map,
    toLp_normalizedPullback, toLp_normalizedPullback, LinearIsometry.inner_map_map]

/-- **Deck invariance.** The normalized pullback of `w ∈ H¹(N)` is invariant under pullback along
every Riemannian isometry `Φ` of `M` with `q ∘ Φ = q`, such as a deck transformation of the
covering. -/
@[simp]
theorem compRiemannianIsometry_normalizedPullback (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {Φ : RiemannianIsometry I I M M}
    (hΦ : ∀ x, q (Φ x) = q x) (w : SobolevH1 I' N) :
    compRiemannianIsometry Φ (normalizedPullback hq hf w) = normalizedPullback hq hf w := by
  refine congrFun (denseRange_ofSmooth.equalizer
    ((LinearIsometryEquiv.continuous _).comp (LinearIsometry.continuous _))
    (LinearIsometry.continuous _) (funext fun u ↦ ?_)) w
  simp only [Function.comp_apply]
  rw [normalizedPullback_ofSmooth, map_smul, compRiemannianIsometry_ofSmooth]
  congr 2
  exact ContMDiffMap.ext fun x ↦ congrArg u (hΦ x)

/-! ### The range of the normalized pullback -/

section Range

variable [BoundarylessManifold I M] [IsManifold I ∞ M] [IsManifold I' ∞ N]

/-- **The range of the normalized pullback.** An element of `H¹(M)` is the normalized pullback of
an element of `H¹(N)` exactly when it is invariant under pullback along every deck transformation
of the finite quotient covering `q : M → N`. So `H¹(N)` is identified isometrically with the
deck-invariant subspace of `H¹(M)`. -/
theorem mem_range_normalizedPullback_iff (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {w : SobolevH1 I M} :
    w ∈ Set.range (normalizedPullback hq hf) ↔
      ∀ g : G, compRiemannianIsometry (hq.deckIsometry hf g) w = w := by
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨w, rfl⟩ g
    exact compRiemannianIsometry_normalizedPullback hq hf (fun x ↦ by simp [hq.map_smul]) w
  have := Fintype.ofFinite G
  -- the average over the deck transformations fixes `w` and maps into the closed range
  set A : SobolevH1 I M →L[ℝ] SobolevH1 I M := (Fintype.card G : ℝ)⁻¹ •
    ∑ g : G, ((compRiemannianIsometry (hq.deckIsometry hf g)).toContinuousLinearEquiv :
      SobolevH1 I M →L[ℝ] SobolevH1 I M)
  have hA (w : SobolevH1 I M) : A w =
      (Fintype.card G : ℝ)⁻¹ • ∑ g : G, compRiemannianIsometry (hq.deckIsometry hf g) w := by
    simp [A]
  have hAw : A w = w := by
    rw [hA]
    simp only [hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  have hclosed : IsClosed (Set.range (normalizedPullback hq hf)) :=
    (normalizedPullback hq hf).isometry.isUniformInducing.isComplete_range.isClosed
  rw [← hAw]
  refine induction_on (p := fun w ↦ A w ∈ Set.range (normalizedPullback hq hf)) w
    (hclosed.preimage A.continuous) fun u ↦ ?_
  obtain ⟨v, hv⟩ := exists_comp_eq_smul_sum_comp_deckIsometry hq hf u
  have hG : (0 : ℝ) < Nat.card G := Nat.cast_pos.2 Nat.card_pos
  refine ⟨(Nat.card G : ℝ) ^ (1 / 2 : ℝ) • ofSmooth v, ?_⟩
  -- the normalizing scalars `|G| ^ (1/2)` and `|G| ^ (-1/2)` cancel
  have hc : (Nat.card G : ℝ) ^ (1 / 2 : ℝ) * (Nat.card G : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hG]
    simp
  rw [map_smul, normalizedPullback_ofSmooth, smul_smul, hc, one_smul, hv, hA]
  simp only [map_smul, map_sum, compRiemannianIsometry_ofSmooth]

end Range

end TauCeti.Manifold.SobolevH1
