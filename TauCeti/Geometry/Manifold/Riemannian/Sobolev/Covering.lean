/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Covering
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
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
`w, v ∈ H¹(N)`. Every element of its range is invariant under pullback along the Riemannian
isometries `Φ` of `M` with `q ∘ Φ = q`, such as the deck transformations of the covering.

When `G` acts by Riemannian isometries, the range is exactly the subspace of `G`-invariant elements
of `H¹(M)`, so `J` is a unitary from `H¹(N)` onto that subspace. The averaging operator
`|G|⁻¹ ∑ g, g^*` fixes the invariant elements, and it maps a smooth function `u` to an invariant
smooth function, which is constant on the fibres of `q` and so is the pullback of a smooth function
on `N` because `q` is a local diffeomorphism. Since smooth functions are dense in `H¹(M)` and the
range of the isometry `J` is closed, the average of every element lies in the range.

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
* `TauCeti.Manifold.SobolevH1.mem_range_normalizedPullback_iff`: for an action by Riemannian
  isometries, the range is exactly the subspace of `G`-invariant elements.

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
    (QuasiMeasurePreserving.of_map_le_smul hq.continuous.measurable
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

/-- **The range of the normalized pullback.** Let a finite group `G` act on `M` by the Riemannian
isometries `Φ g`, and let `q : M → N` be a quotient covering map for this action which is a local
Riemannian isometry. Then the normalized pullback `J : H¹(N) → H¹(M)` maps onto the elements of
`H¹(M)` invariant under pullback along every `Φ g`. -/
theorem mem_range_normalizedPullback_iff (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (Φ : G → RiemannianIsometry I I M M)
    (hΦ : ∀ g x, Φ g x = g • x) {w : SobolevH1 I M} :
    w ∈ Set.range (normalizedPullback hq hf) ↔ ∀ g, compRiemannianIsometry (Φ g) w = w := by
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨v, rfl⟩ g
    exact compRiemannianIsometry_normalizedPullback hq hf (fun x ↦ (hΦ g x).symm ▸ hq.map_smul g) v
  have := Fintype.ofFinite G
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
  -- The average `A` over `G` of the pullbacks along the `Φ g` fixes `w`.
  let A : SobolevH1 I M →L[ℝ] SobolevH1 I M := (Fintype.card G : ℝ)⁻¹ •
    ∑ g, ((compRiemannianIsometry (Φ g)).toContinuousLinearEquiv : SobolevH1 I M →L[ℝ] _)
  have hA (w : SobolevH1 I M) :
      A w = (Fintype.card G : ℝ)⁻¹ • ∑ g, compRiemannianIsometry (Φ g) w := by
    simp [A]
  have hAw : A w = w := by
    rw [hA]
    simp only [hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [inv_mul_cancel₀ hG.ne', one_smul]
  rw [← hAw]
  -- By density of smooth functions and closedness of the range, it suffices that `A` maps every
  -- smooth `u` into the range.
  refine induction_on (p := fun w ↦ A w ∈ Set.range (normalizedPullback hq hf)) w
    ((normalizedPullback hq hf).isometry.isClosedEmbedding.isClosed_range.preimage A.continuous)
    fun u ↦ ?_
  -- The average `ū` of `u` is constant on the fibres of `q`, which are the `G`-orbits, so it is
  -- the pullback `v ∘ q` of a smooth function `v` on `N`.
  set ū : C^∞⟮I, M; ℝ⟯ := (Fintype.card G : ℝ)⁻¹ • ∑ g, u.comp (Φ g).toDiffeomorph.toContMDiffMap
  have hū (x : M) : ū x = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, u (g • x) := by
    simp [ū, Finset.sum_apply, hΦ]
  have hfib : Function.FactorsThrough ū q := fun x y hxy ↦ by
    obtain ⟨h, rfl⟩ := hq.apply_eq_iff_mem_orbit.1 hxy
    rw [hū, hū]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g ↦ by simp [mul_smul]
  obtain ⟨v, ⟨hv, hvq⟩, -⟩ := (hf.isLocalDiffeomorph (n := ∞) (by simp) le_rfl
    ).existsUnique_contMDiff_comp_eq hq.surjective le_rfl ū.contMDiff hfib
  let v' : C^∞⟮I', N; ℝ⟯ := ⟨v, hv⟩
  have hvū : v'.comp ⟨q, hf.contMDiff⟩ = ū := ContMDiffMap.ext fun x ↦ congrFun hvq x
  -- Hence `A u = ū = |G| ^ (1/2) J v`.
  refine ⟨(Fintype.card G : ℝ) ^ (1 / 2 : ℝ) • ofSmooth v', ?_⟩
  rw [map_smul, normalizedPullback_ofSmooth, smul_smul, Nat.card_eq_fintype_card,
    ← Real.rpow_add hG, hvū, hA]
  norm_num [ū]

end Range

end TauCeti.Manifold.SobolevH1
