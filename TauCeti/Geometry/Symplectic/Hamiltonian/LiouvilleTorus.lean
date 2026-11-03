/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import TauCeti.Analysis.Calculus.ContDiff.LocalInjectivity
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Topology.Algebra.Module.CompactQuotient

/-!
# Orbits of the Hamiltonian flow action and Liouville tori

Let `σ` be a symplectic form on a `2n`-dimensional boundaryless manifold `M` and let
`F : M → (ι → ℝ)` be `n` smooth, pairwise Poisson-commuting functions whose Hamiltonian vector
fields are complete, with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`.
Their flows generate an action `v ↦ φ_v` of `ι → ℝ` on `M` that preserves each common level of `F`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`). This file proves the topological
part of the Liouville–Arnold theorem: a compact connected component of a level, consisting of
regular points of `F`, is an orbit of this action and is homeomorphic to the torus `(ℝ / ℤ)ⁿ`.

The action is jointly smooth, and the orbit map `v ↦ φ_v(x)` has derivative
`v ↦ ∑ᵢ vᵢ X_{Fᵢ}(x)` at the origin
(`TauCeti.SmoothTwoForm.IsSymplectic.contMDiff_hamiltonianFlowAction_uncurry` and
`TauCeti.SmoothTwoForm.IsSymplectic.hasMFDerivAt_hamiltonianFlowAction_apply_zero`). At a regular
point the vectors `X_{Fᵢ}(x)` are linearly independent and span the kernel of `dF_x`, so the orbit
map is an immersion whose image is open in the common level. Hence:

* the stabilizer of a regular point is a discrete subgroup of `ι → ℝ`;
* if every point of the connected component `L` of `x` in `F⁻¹(F x)` is regular, the orbit of `x`
  is `L`, and the orbit map induces a homeomorphism `(ι → ℝ) ⧸ Λ ≃ₜ L` from the quotient by the
  stabilizer `Λ` of `x`;
* if moreover `L` is compact, `Λ` spans `ι → ℝ`, so it is a full lattice (the period lattice of
  `L`), and a lattice basis identifies `L` with `(ℝ / ℤ)ⁿ`.

Other components of the level need not be regular. The smooth identification of `L` with the torus
and the action-angle coordinates near `L` are not treated here.

## Main definitions

* `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer`: the stabilizer of a point under
  the Hamiltonian flow action.
* `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowQuotientHomeomorph`: the homeomorphism from
  `(ι → ℝ) ⧸ Λ` onto a regular component of a level induced by the orbit map.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.discreteTopology_hamiltonianFlowStabilizer`: the stabilizer
  of a regular point is discrete.
* `TauCeti.SmoothTwoForm.IsSymplectic.image_mem_nhdsWithin_hamiltonianFlowAction`: at a regular
  point, the orbit map is open onto the common level.
* `TauCeti.SmoothTwoForm.IsSymplectic.range_hamiltonianFlowAction_eq_connectedComponentIn`: the
  action is transitive on a regular component of a level.
* `TauCeti.SmoothTwoForm.IsSymplectic.span_hamiltonianFlowStabilizer_eq_top`: the stabilizer of a
  point of a compact regular component spans `ι → ℝ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`: a compact regular
  component of a level is homeomorphic to `(ℝ / ℤ)ⁿ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (the Liouville–Arnold theorem: the level is an orbit
  of the `ℝⁿ`-action, and a compact connected one is a torus).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Function Set Filter Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {x : M}

/-! ### The stabilizer of a point -/

/-- The **stabilizer** of `x` under the Hamiltonian flow action: the vectors `v : ι → ℝ` with
`φ_v(x) = x`. When `x` lies on a compact connected regular component of its common level, this is
the period lattice of that component. -/
def hamiltonianFlowStabilizer (x : M) : AddSubgroup (ι → ℝ) where
  carrier := {v | (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x}
  add_mem' {v w} hv hw := by
    simp only [mem_ofPred_eq, hσ.hamiltonianFlowAction_add_apply hF hcomm hc] at hv hw ⊢
    rw [hw, hv]
  zero_mem' := by simp
  neg_mem' {v} hv := by
    simp only [mem_ofPred_eq] at hv ⊢
    conv_lhs => rw [← hv]
    exact hσ.hamiltonianFlowAction_neg_apply_apply hF hcomm hc v x

/-- A vector lies in the stabilizer of `x` exactly when it fixes `x`. -/
@[simp]
theorem mem_hamiltonianFlowStabilizer {v : ι → ℝ} :
    v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x ↔
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x = x :=
  Iff.rfl

/-- Two vectors move `x` to the same point exactly when their difference stabilizes `x`. -/
theorem hamiltonianFlowAction_apply_eq_apply_iff {v w : ι → ℝ} :
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x =
        (hσ.hamiltonianFlowAction hF hcomm hc w).toMul x ↔
      v - w ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x := by
  have h : (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x =
      (hσ.hamiltonianFlowAction hF hcomm hc w).toMul
        ((hσ.hamiltonianFlowAction hF hcomm hc (v - w)).toMul x) := by
    rw [← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, add_sub_cancel]
  rw [h, mem_hamiltonianFlowStabilizer]
  exact (hσ.hamiltonianFlowAction hF hcomm hc w).toMul.injective.eq_iff

/-- **The stabilizer of a regular point is discrete.** At a regular point `x` of `F` the vectors
`X_{Fᵢ}(x)` are linearly independent, so the orbit map `v ↦ φ_v(x)` is an immersion at the
origin, hence injective near it. -/
theorem discreteTopology_hamiltonianFlowStabilizer
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x) := by
  set a := fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x with ha_def
  have hinj : Injective (mfderiv 𝓘(ℝ, ι → ℝ) I a 0) := by
    rw [(hσ.hasMFDerivAt_hamiltonianFlowAction_apply_zero hF hcomm hc x).mfderiv]
    exact hσ.isNondegenerate.injective_sum_smulRight_hamiltonianVectorField hx
  have hca : ContMDiffAt 𝓘(ℝ, ι → ℝ) I ∞ a 0 :=
    ((hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp
      (contMDiff_id.prodMk contMDiff_const)).contMDiffAt
  obtain ⟨t, ht, htinj⟩ := hca.exists_mem_nhds_injOn (by simp) hinj
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨interior t, isOpen_interior, ?_⟩
  ext ⟨v, hv⟩
  simp only [mem_preimage, mem_singleton_iff, AddSubgroup.mk_eq_zero]
  refine ⟨fun hvt ↦ htinj (interior_subset hvt) (mem_of_mem_nhds ht) ?_, ?_⟩
  · simpa [a] using hv
  · rintro rfl
    exact mem_interior_iff_mem_nhds.2 ht

/-! ### Orbits are open in the common level -/

/-- In the preferred chart at `x`, the orbit map `v ↦ φ_v(x)` has derivative
`v ↦ ∑ᵢ vᵢ X_{Fᵢ}(x)` at the origin. -/
private theorem hasFDerivAt_extChartAt_hamiltonianFlowAction (x : M) :
    HasFDerivAt (fun v ↦ extChartAt I x ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul x))
      (∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
        (σ.hamiltonianVectorField (F · i) x) : (ι → ℝ) →L[ℝ] E) 0 := by
  have ha := hσ.hasMFDerivAt_hamiltonianFlowAction_apply_zero hF hcomm hc x
  have hx0 : (hσ.hamiltonianFlowAction hF hcomm hc 0).toMul x = x := by simp
  have hsrc : (hσ.hamiltonianFlowAction hF hcomm hc 0).toMul x ∈ (chartAt H x).source := by
    rw [hx0]
    exact mem_chart_source H x
  have he := ((contMDiffAt_extChartAt' (I := I) (n := ∞) hsrc).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have hid : mfderiv I 𝓘(ℝ, E) (extChartAt I x)
      ((hσ.hamiltonianFlowAction hF hcomm hc 0).toMul x) = ContinuousLinearMap.id ℝ E := by
    rw [hx0]
    exact mfderiv_extChartAt_self
  rw [hid] at he
  exact (hasMFDerivAt_iff_hasFDerivAt.1 (he.comp 0 ha)).congr_fderiv
    (ContinuousLinearMap.id_comp _)

/-- In the preferred chart `e` at `x`, the map `(v, z) ↦ e(φ_v(e⁻¹ z))` has strict derivative
`(v, z) ↦ ∑ᵢ vᵢ X_{Fᵢ}(x) + z` at `(0, e x)`. -/
private theorem hasStrictFDerivAt_extChartAt_hamiltonianFlowAction (x : M) :
    HasStrictFDerivAt (fun q : (ι → ℝ) × E ↦ extChartAt I x
        ((hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul ((extChartAt I x).symm q.2)))
      ((∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
        (σ.hamiltonianVectorField (F · i) x) : (ι → ℝ) →L[ℝ] E).coprod
          (ContinuousLinearMap.id ℝ E)) (0, extChartAt I x x) := by
  set e := extChartAt I x with he
  set B : (ι → ℝ) × E → E := fun q ↦
    e ((hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (e.symm q.2)) with hB
  -- `B` is smooth at `(0, e x)`: it is the action read in the product chart at `(0, x)`.
  have hBc : ContDiffAt ℝ ∞ B (0, e x) := by
    have hsrc : (hσ.hamiltonianFlowAction hF hcomm hc 0).toMul x ∈ (chartAt H x).source := by
      simp
    have h := ((contMDiffAt_extChartAt' (n := ∞) hsrc).comp ((0 : ι → ℝ), x)
      (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).contMDiffAt
      ).contDiffAt_comp_extChartAt_symm
    have hsymm (q : (ι → ℝ) × E) :
        (extChartAt (𝓘(ℝ, ι → ℝ).prod I) ((0 : ι → ℝ), x)).symm q = (q.1, e.symm q.2) := by
      rw [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
        extChartAt_model_space_eq_id]
      rfl
    have hpt : extChartAt (𝓘(ℝ, ι → ℝ).prod I) ((0 : ι → ℝ), x) ((0 : ι → ℝ), x) =
        (0, e x) := by
      rw [extChartAt_prod, PartialEquiv.prod_coe, extChartAt_model_space_eq_id]
      rfl
    rw [hpt] at h
    convert h using 1
    funext q
    rw [comp_apply, hsymm]
    rfl
  -- Its derivative is determined by its restrictions to the two coordinate axes.
  set B' := fderiv ℝ B (0, e x) with hB'
  have hBd : HasFDerivAt B B' (0, e x) := (hBc.differentiableAt (by simp)).hasFDerivAt
  have h1 (v : ι → ℝ) : B' (v, 0) = (∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
      (σ.hamiltonianVectorField (F · i) x) : (ι → ℝ) →L[ℝ] E) v := by
    have h := (hBd.comp (0 : ι → ℝ) ((hasFDerivAt_id (0 : ι → ℝ)).prodMk
      (hasFDerivAt_const (e x) 0))).unique
        ((hσ.hasFDerivAt_extChartAt_hamiltonianFlowAction hF hcomm hc x).congr_of_eventuallyEq
          (Eventually.of_forall fun v ↦ by simp [B, he]))
    simpa using DFunLike.congr_fun h v
  have h2 (z : E) : B' (0, z) = z := by
    have h := (hBd.comp (e x) ((hasFDerivAt_const (0 : ι → ℝ) (e x)).prodMk
      (hasFDerivAt_id (e x)))).unique ((hasFDerivAt_id (e x)).congr_of_eventuallyEq
        (by filter_upwards [extChartAt_target_mem_nhds (I := I) x] with z hz
            simp [B, e.right_inv hz]))
    simpa using DFunLike.congr_fun h z
  have hB'eq : B' = (∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
      (σ.hamiltonianVectorField (F · i) x) : (ι → ℝ) →L[ℝ] E).coprod
        (ContinuousLinearMap.id ℝ E) := by
    refine ContinuousLinearMap.ext fun q ↦ ?_
    rw [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.id_apply, ← h1 q.1, ← h2 q.2,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [← hB'eq]
  exact hBc.hasStrictFDerivAt hBd (by simp)

/-- Near a regular point `x` of a family of `n` Poisson-commuting functions on a `2n`-dimensional
manifold, every point of the common level of `x` is `φ_v(x)` for a small vector `v`. In a chart,
`(v, w) ↦ φ_v(x + S w)`, for a right inverse `S` of the coordinate derivative of `F`, is a local
diffeomorphism at the origin, and `F(φ_v(x + S w)) = F(x + S w)` determines `w` near `0`. -/
private theorem image_mem_nhdsWithin_zero (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {V : Set (ι → ℝ)} (hV : V ∈ 𝓝 0) :
    (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) '' V ∈ 𝓝[F ⁻¹' {F x}] x := by
  set Φ := fun (v : ι → ℝ) (y : M) ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul y with hΦ
  have hΦ0x : Φ 0 x = x := by simp [Φ]
  have hΦc : Continuous (fun p : (ι → ℝ) × M ↦ Φ p.1 p.2) :=
    (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).continuous
  have hFΦ (v : ι → ℝ) (y : M) : F (Φ v y) = F y := hσ.apply_hamiltonianFlowAction hF hcomm hc v y
  set e := extChartAt I x with he
  have hsrc : e.source ∈ 𝓝 x := extChartAt_source_mem_nhds x
  have hee : e.symm (e x) = x := extChartAt_to_inv x
  -- The coordinate expression of `F` and a right inverse `S` of its derivative `DF`.
  have hFc : ContDiffAt ℝ ∞ (F ∘ e.symm) (e x) := (hF x).contDiffAt_comp_extChartAt_symm
  set DF := fderiv ℝ (F ∘ e.symm) (e x) with hDF
  have hFd : HasFDerivAt (F ∘ e.symm) DF (e x) := (hFc.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨S, hS⟩ := DF.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm)
  -- The orbit map in the chart has injective derivative `D v = ∑ᵢ vᵢ X_{Fᵢ}(x)`, and `F` is
  -- constant along the orbit, so `DF ∘ D = 0`.
  set D : (ι → ℝ) →L[ℝ] E := ∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
    (σ.hamiltonianVectorField (F · i) x) with hD
  have hDe : HasFDerivAt (fun v ↦ e (Φ v x)) D 0 :=
    hσ.hasFDerivAt_extChartAt_hamiltonianFlowAction hF hcomm hc x
  have hDinj : Injective D := hσ.isNondegenerate.injective_sum_smulRight_hamiltonianVectorField hx
  have hDFD (v : ι → ℝ) : DF (D v) = 0 := by
    have hG : HasFDerivAt (F ∘ e.symm) DF (e (Φ 0 x)) := by rw [hΦ0x]; exact hFd
    have hev : ∀ᶠ v in 𝓝 (0 : ι → ℝ), Φ v x ∈ e.source :=
      (hΦc.comp (continuous_id.prodMk continuous_const)).continuousAt.preimage_mem_nhds
        (by simpa only [comp_apply, id, hΦ0x] using hsrc)
    have h := (hG.comp (0 : ι → ℝ) hDe).unique
      ((hasFDerivAt_const (F x) (0 : ι → ℝ)).congr_of_eventuallyEq (by
        filter_upwards [hev] with v hv
        simp only [comp_apply, e.left_inv hv, hFΦ]))
    simpa using DFunLike.congr_fun h v
  have hDFS (w : ι → ℝ) : DF (S w) = w := by simpa using DFunLike.congr_fun hS w
  -- The map `A (v, w) = e (φ_v (e⁻¹ (e x + S w)))` has invertible strict derivative
  -- `A' (v, w) = D v + S w`: apply `DF` to see injectivity, and count dimensions.
  set A : (ι → ℝ) × (ι → ℝ) → E := fun p ↦ e (Φ p.1 (e.symm (e x + S p.2))) with hA
  set A' : (ι → ℝ) × (ι → ℝ) →L[ℝ] E := D.coprod S with hA'
  have hAd : HasStrictFDerivAt A A' 0 := by
    have hB := hσ.hasStrictFDerivAt_extChartAt_hamiltonianFlowAction hF hcomm hc x
    have hL : HasStrictFDerivAt (fun p : (ι → ℝ) × (ι → ℝ) ↦ (p.1, e x + S p.2))
        ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
          (S.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) 0 := by
      have h := (hasStrictFDerivAt_fst (p := (0 : (ι → ℝ) × (ι → ℝ)))).prodMk
        ((hasStrictFDerivAt_const (e x) (0 : (ι → ℝ) × (ι → ℝ))).add
          (S.hasStrictFDerivAt.comp (0 : (ι → ℝ) × (ι → ℝ)) hasStrictFDerivAt_snd))
      rwa [zero_add] at h
    have hB' : HasStrictFDerivAt (fun q : (ι → ℝ) × E ↦ e (Φ q.1 (e.symm q.2)))
        (D.coprod (ContinuousLinearMap.id ℝ E))
        ((fun p : (ι → ℝ) × (ι → ℝ) ↦ (p.1, e x + S p.2)) 0) := by
      have hL0 : (fun p : (ι → ℝ) × (ι → ℝ) ↦ (p.1, e x + S p.2)) 0 = (0, e x) := by simp
      rw [hL0]
      exact hB
    refine (hB'.comp 0 hL).congr_fderiv (ContinuousLinearMap.ext fun p ↦ ?_)
    simp [A']
  have hA'inj : Injective A' := by
    intro p q hpq
    have h1 := congrArg DF hpq
    simp only [A', ContinuousLinearMap.coprod_apply, map_add, hDFD, hDFS, zero_add] at h1 hpq
    rw [h1, add_left_inj] at hpq
    exact Prod.ext (hDinj hpq) h1
  have hA'surj : Surjective A' := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hA'inj
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, ← hdim, two_mul]
  let Aeq : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (A' : (ι → ℝ) × (ι → ℝ) →ₗ[ℝ] E)
      ⟨hA'inj, hA'surj⟩).toContinuousLinearEquiv
  have hAeq : HasStrictFDerivAt A (Aeq : (ι → ℝ) × (ι → ℝ) →L[ℝ] E) 0 := hAd
  have hmap : map A (𝓝 0) = 𝓝 (e x) := by
    rw [hAeq.map_nhds_eq_of_equiv]
    simp [A, Φ, hee]
  -- The value `g w = F (e⁻¹ (e x + S w))` determines `w` near `0`, since `DF ∘ S = id`.
  set g : (ι → ℝ) → ι → ℝ := fun w ↦ (F ∘ e.symm) (e x + S w) with hg
  obtain ⟨W, hW, hWinj⟩ : ∃ W ∈ 𝓝 (0 : ι → ℝ), InjOn g W := by
    have hlin : ContDiff ℝ ∞ (fun w : ι → ℝ ↦ e x + S w) := contDiff_const.add S.contDiff
    have hFc' : ContDiffAt ℝ ∞ (F ∘ e.symm) ((fun w : ι → ℝ ↦ e x + S w) 0) := by
      simpa using hFc
    have hFd' : HasFDerivAt (F ∘ e.symm) DF ((fun w : ι → ℝ ↦ e x + S w) 0) := by
      simpa using hFd
    have hgd : HasFDerivAt ((F ∘ e.symm) ∘ fun w : ι → ℝ ↦ e x + S w)
        (ContinuousLinearMap.id ℝ (ι → ℝ)) 0 := by
      refine (hFd'.comp 0 ((hasFDerivAt_const (e x) 0).add S.hasFDerivAt)).congr_fderiv ?_
      rw [zero_add, hS]
    obtain ⟨t, ht, hinj⟩ := (hFc'.comp 0 hlin.contDiffAt).contDiffWithinAt.exists_nhdsWithin_injOn
      (s := univ) (by simp) convex_univ (mem_univ _) uniqueDiffWithinAt_univ
      (by rw [fderivWithin_univ, hgd.fderiv]; exact injective_id)
    exact ⟨t, by rwa [nhdsWithin_univ] at ht, hinj⟩
  -- A point `y` of the level near `x` is `e⁻¹ (A (v, w))` with `(v, w)` small; then
  -- `g w = F y = F x = g 0`, so `w = 0` and `y = φ_v(x)`.
  set Ψ : (ι → ℝ) × (ι → ℝ) → M := fun p ↦ Φ p.1 (e.symm (e x + S p.2)) with hΨ
  have hP : V ×ˢ W ∩ Ψ ⁻¹' e.source ∈ 𝓝 0 := by
    have hΨc : ContinuousAt Ψ 0 := by
      refine hΦc.continuousAt.comp (f := fun p : (ι → ℝ) × (ι → ℝ) ↦
        (p.1, e.symm (e x + S p.2))) (continuousAt_fst.prodMk ?_)
      refine (continuousAt_extChartAt_symm x).comp_of_eq ?_ (by simp [he])
      exact (continuous_const.add (S.continuous.comp continuous_snd)).continuousAt
    have hΨ0 : Ψ 0 = x := by simp [Ψ, Φ, hee]
    exact inter_mem (prod_mem_nhds hV hW) (hΨc.preimage_mem_nhds (by rwa [hΨ0]))
  have hQ : e.source ∩ e ⁻¹' (A '' (V ×ˢ W ∩ Ψ ⁻¹' e.source)) ∈ 𝓝 x :=
    inter_mem hsrc ((continuousAt_extChartAt x).preimage_mem_nhds
      (by rw [← hmap]; exact image_mem_map hP))
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨_, hQ, ?_⟩
  rintro y ⟨⟨hy, p, ⟨⟨hpV, hpW⟩, hpsrc⟩, hpy⟩, hyF⟩
  have hyeq : y = Φ p.1 (e.symm (e x + S p.2)) := e.injOn hy hpsrc hpy.symm
  have hp2 : p.2 = 0 := by
    refine hWinj hpW (mem_of_mem_nhds hW) ?_
    have : F y = F x := hyF
    simp only [g, comp_apply, map_zero, add_zero, hee]
    rw [← this, hyeq, hFΦ]
  refine ⟨p.1, hpV, ?_⟩
  rw [hyeq, hp2, map_zero, add_zero, hee]

/-- **The orbit map is open onto the common level.** Let `x` be a regular point of a family `F` of
`n` Poisson-commuting functions with complete Hamiltonian vector fields on a `2n`-dimensional
symplectic manifold. Then the orbit map `v ↦ φ_v(x)` sends every neighbourhood of a vector `v₀`
onto a neighbourhood of `φ_{v₀}(x)` within the common level `F⁻¹(F x)`. -/
theorem image_mem_nhdsWithin_hamiltonianFlowAction (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {v₀ : ι → ℝ} {V : Set (ι → ℝ)} (hV : V ∈ 𝓝 v₀) :
    (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) '' V ∈
      𝓝[F ⁻¹' {F x}] ((hσ.hamiltonianFlowAction hF hcomm hc v₀).toMul x) := by
  set φ := (hσ.hamiltonianFlowAction hF hcomm hc v₀).toMul
  have hFφ (y : M) : F (φ y) = F y := hσ.apply_hamiltonianFlowAction hF hcomm hc v₀ y
  -- Translate the statement at the origin by the homeomorphism `φ_{v₀}`, which preserves `F`.
  have hV' : (v₀ + ·) ⁻¹' V ∈ 𝓝 (0 : ι → ℝ) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)
  have h0 := image_mem_nhdsWithin_zero hσ hF hcomm hc hx hdim hV'
  have hmap := image_mem_map (m := φ) h0
  have hemb : Topology.IsEmbedding φ := φ.toHomeomorph.isEmbedding
  rw [hemb.map_nhdsWithin_eq] at hmap
  have hsub : F ⁻¹' {F x} ⊆ φ '' (F ⁻¹' {F x}) := fun y hy ↦
    ⟨φ.symm y, by simpa [mem_preimage, ← hFφ (φ.symm y)] using hy, φ.apply_symm_apply y⟩
  refine mem_of_superset (nhdsWithin_mono _ hsub hmap) ?_
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨v₀ + u, hu, ?_⟩
  exact hσ.hamiltonianFlowAction_add_apply hF hcomm hc v₀ u x

/-- A point lies on the orbit of `x` exactly when its image under any element of the action
does. -/
private theorem apply_mem_range_iff (u : ι → ℝ) (y : M) :
    (hσ.hamiltonianFlowAction hF hcomm hc u).toMul y ∈
        range (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) ↔
      y ∈ range (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨-u + v, ?_⟩
    simp only [hσ.hamiltonianFlowAction_add_apply hF hcomm hc, hv,
      hσ.hamiltonianFlowAction_neg_apply_apply hF hcomm hc]
  · rintro ⟨v, rfl⟩
    exact ⟨u + v, hσ.hamiltonianFlowAction_add_apply hF hcomm hc u v x⟩

/-- **The orbit through a regular point is the connected component of its common level.** If every
point of the connected component of `x` in the common level `F⁻¹(F x)` is a regular point of a
family `F` of `n` Poisson-commuting functions with complete Hamiltonian vector fields on a
`2n`-dimensional symplectic manifold, then the action of `ι → ℝ` is transitive on that component:
it is the orbit of `x`. -/
theorem range_hamiltonianFlowAction_eq_connectedComponentIn
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    range (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) =
      connectedComponentIn (F ⁻¹' {F x}) x := by
  classical
  set C := connectedComponentIn (F ⁻¹' {F x}) x with hC
  set O := range (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) with hO
  have hcont (y : M) : Continuous (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul y) :=
    (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hxC : x ∈ C := mem_connectedComponentIn (by simp)
  have hCF : C ⊆ F ⁻¹' {F x} := connectedComponentIn_subset _ _
  refine (isPreconnected_range (hcont x)).subset_connectedComponentIn ⟨0, by simp⟩
    (range_subset_iff.2 fun v ↦ hσ.apply_hamiltonianFlowAction hF hcomm hc v x) |>.antisymm ?_
  -- Membership in `O` is locally constant on `C`: near each `y ∈ C`, the points of the level are
  -- on the orbit of `y`, which either is `O` or is disjoint from it.
  have hloc : ContinuousOn (fun y ↦ decide (y ∈ O)) C := by
    intro y hy
    have hFy : F y = F x := hCF hy
    have hnhds := image_mem_nhdsWithin_hamiltonianFlowAction hσ hF hcomm hc (x := y) (hreg y hy)
      hdim (v₀ := 0) univ_mem
    simp only [image_univ, map_zero, toMul_zero, Diffeomorph.one_apply, hFy] at hnhds
    rw [ContinuousWithinAt, nhds_discrete]
    refine tendsto_pure.2 (mem_of_superset (nhdsWithin_mono _ hCF hnhds) ?_)
    rintro _ ⟨u, rfl⟩
    simp only [mem_ofPred_eq, decide_eq_decide]
    exact hσ.apply_mem_range_iff hF hcomm hc u y
  intro y hy
  have hxO : x ∈ O := ⟨0, by simp⟩
  have h : decide (y ∈ O) = true :=
    (isPreconnected_connectedComponentIn.constant hloc hy hxC).trans (decide_eq_true hxO)
  exact of_decide_eq_true h

/-- **The component of a regular level is a quotient of `ι → ℝ`.** Under the hypotheses of
`range_hamiltonianFlowAction_eq_connectedComponentIn`, the orbit map induces a homeomorphism from
the quotient of `ι → ℝ` by the stabilizer of `x` onto the connected component of `x` in its
common level. -/
noncomputable def hamiltonianFlowQuotientHomeomorph
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    (ι → ℝ) ⧸ hσ.hamiltonianFlowStabilizer hF hcomm hc x ≃ₜ
      connectedComponentIn (F ⁻¹' {F x}) x :=
  let hrange := hσ.range_hamiltonianFlowAction_eq_connectedComponentIn hF hcomm hc hreg hdim
  let f : (ι → ℝ) → connectedComponentIn (F ⁻¹' {F x}) x := fun v ↦
    ⟨(hσ.hamiltonianFlowAction hF hcomm hc v).toMul x, hrange ▸ mem_range_self v⟩
  have hf : ∀ a b, QuotientAddGroup.leftRel (hσ.hamiltonianFlowStabilizer hF hcomm hc x) a b →
      f a = f b := fun a b hab ↦ Subtype.ext <|
    ((hσ.hamiltonianFlowAction_apply_eq_apply_iff hF hcomm hc).2 (by
      rw [sub_eq_neg_add]
      exact QuotientAddGroup.leftRel_apply.1 hab)).symm
  have hfc : Continuous f := Continuous.subtype_mk
    ((hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).continuous.comp
      (continuous_id.prodMk continuous_const)) _
  let g : (ι → ℝ) ⧸ hσ.hamiltonianFlowStabilizer hF hcomm hc x →
      connectedComponentIn (F ⁻¹' {F x}) x :=
    Quotient.lift (s := QuotientAddGroup.leftRel _) f hf
  have hbij : Bijective g := by
    refine ⟨fun a b hab ↦ ?_, fun y ↦ ?_⟩
    · induction a using QuotientAddGroup.induction_on with | H v => ?_
      induction b using QuotientAddGroup.induction_on with | H w => ?_
      refine QuotientAddGroup.eq.2 ?_
      rw [← neg_mem_iff, neg_add_rev, neg_neg, ← sub_eq_neg_add]
      exact (hσ.hamiltonianFlowAction_apply_eq_apply_iff hF hcomm hc).1
        (congrArg Subtype.val hab)
    · obtain ⟨v, hv⟩ := hrange.ge y.2
      exact ⟨QuotientAddGroup.mk v, Subtype.ext hv⟩
  (Equiv.ofBijective g hbij).toHomeomorphOfContinuousOpen
    (hfc.quotient_lift (s := QuotientAddGroup.leftRel _) hf) <| by
    -- The orbit map is open into the level, hence into the component.
    have hxC : x ∈ connectedComponentIn (F ⁻¹' {F x}) x := mem_connectedComponentIn (by simp)
    intro U hU
    have himage : Equiv.ofBijective g hbij '' U = f '' (QuotientAddGroup.mk ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective a
        exact ⟨v, ha, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨QuotientAddGroup.mk v, hv, rfl⟩
    rw [himage, isOpen_iff_mem_nhds]
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_nhds_subtype_iff_nhdsWithin, image_image]
    exact nhdsWithin_mono _ (connectedComponentIn_subset _ _)
      (hσ.image_mem_nhdsWithin_hamiltonianFlowAction hF hcomm hc (hreg x hxC) hdim
        ((hU.preimage continuous_quotient_mk').mem_nhds hv))

/-- The homeomorphism `hamiltonianFlowQuotientHomeomorph` sends the class of `v` to `φ_v(x)`. -/
@[simp]
theorem coe_hamiltonianFlowQuotientHomeomorph_mk
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) (v : ι → ℝ) :
    (hσ.hamiltonianFlowQuotientHomeomorph hF hcomm hc hreg hdim (QuotientAddGroup.mk v) : M) =
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x :=
  (rfl)

/-- **The period lattice of a compact regular component has full rank.** If the connected
component of `x` in its common level is compact and consists of regular points, then the stabilizer
of `x` spans `ι → ℝ`. Since it is also discrete
(`TauCeti.SmoothTwoForm.IsSymplectic.discreteTopology_hamiltonianFlowStabilizer`), it is a full
lattice. -/
theorem span_hamiltonianFlowStabilizer_eq_top
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    Submodule.span ℝ (hσ.hamiltonianFlowStabilizer hF hcomm hc x : Set (ι → ℝ)) = ⊤ := by
  have := isCompact_iff_compactSpace.1 hK
  have := (hσ.hamiltonianFlowQuotientHomeomorph hF hcomm hc hreg hdim).symm.compactSpace
  exact AddSubgroup.span_eq_top_of_compactSpace_quotient _

include hσ hF hcomm hc in
/-- **Compact regular components are tori** (the topological part of the Liouville–Arnold
theorem). Let `F` be a family of `n` Poisson-commuting functions with complete Hamiltonian vector
fields on a `2n`-dimensional symplectic manifold. If the connected component of `x` in its common
level `F⁻¹(F x)` is compact and consists of regular points of `F`, then it is homeomorphic to the
torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    Nonempty (connectedComponentIn (F ⁻¹' {F x}) x ≃ₜ UnitAddTorus ι) := by
  set Λ := hσ.hamiltonianFlowStabilizer hF hcomm hc x
  have : DiscreteTopology Λ := hσ.discreteTopology_hamiltonianFlowStabilizer hF hcomm hc
    (hreg x (mem_connectedComponentIn (by simp)))
  have : DiscreteTopology Λ.toIntSubmodule := ‹DiscreteTopology Λ›
  have : IsZLattice ℝ Λ.toIntSubmodule :=
    ⟨hσ.span_hamiltonianFlowStabilizer_eq_top hF hcomm hc hreg hdim hK⟩
  exact ⟨(hσ.hamiltonianFlowQuotientHomeomorph hF hcomm hc hreg hdim).symm.trans
    (IsZLattice.basis Λ.toIntSubmodule).quotientLatticeEquiv.toHomeomorph⟩

end IsSymplectic

end SmoothTwoForm

end TauCeti
