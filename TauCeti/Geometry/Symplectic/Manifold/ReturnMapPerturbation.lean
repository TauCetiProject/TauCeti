/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Darboux
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import TauCeti.Geometry.Symplectic.Hamiltonian.RadialTwist
import TauCeti.Geometry.Symplectic.WittExtension
import TauCeti.Data.Set.Function
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation
import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Nondegenerate
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Making a periodic orbit of an area-preserving surface map nondegenerate

Let `(M, σ)` be a boundaryless symplectic surface, `φ : M → M` a map and `p` a periodic point of
`φ` of period `k > 0` whose linearized return map `A = d(φ^[k])_p` has determinant one, as for an
area-preserving map. The orbit is *nondegenerate in all iterates* when `p` is a nondegenerate fixed
point (`TauCeti.IsNondegenerateFixedPt`) of every iterate `φ^[k * n]`, `n > 0`, that is, when no
nonzero power of `A` has the eigenvalue `1`. This is the condition under which the periodic orbits
of an area-preserving surface map give the orbit tori, with their four-twist labels, in Taubes's
count of pseudoholomorphic curves in the product of a circle with the mapping torus of `φ`.

This file shows that the condition can be reached by composing `φ` with a symplectic
diffeomorphism `Φ` of `M` supported in an arbitrarily small neighbourhood of `p`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_isNondegenerateFixedPt_iterate`). When `φ`
preserves `σ`, so does `φ ∘ Φ`. The perturbation fixes `p` and the other points of its orbit, so
the orbit is unchanged and only its linearized return map changes. It is the transplant to `M` of
the planar construction of `TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero`.

In a Darboux chart at `p`, read in `ℂ` through a linear symplectomorphism, `Φ` is the
area-preserving diffeomorphism `TauCeti.exists_diffeomorph_eventuallyEq_rotation`. It rotates a
small disc about `p` by an angle `θ` near its centre and is the identity outside it; it is extended
to `M` by the identity (`PartialDiffeomorph.exists_diffeomorph_eq_symm_apply_apply`). Its
derivative at `p` is the rotation by `θ` read through a fixed identification `L` of `T_p M` with `ℂ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_continuousLinearEquiv_forall_exists_diffeomorph`).
Away from `p` the twist is the identity near the other points of the orbit, so the return map of
`φ ∘ Φ` at `p` is the rotation by `θ` followed by `A`, and `L` conjugates it to `B e^(iθ)` with
`det B = 1`. Only countably many angles make some nonzero power of `B e^(iθ)` have the eigenvalue
`1` (`LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero`), so some angle
makes the orbit nondegenerate in all iterates.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_continuousLinearEquiv_forall_exists_diffeomorph`:
  compactly supported symplectic twists at `p` realizing every rotation of `T_p M ≅ ℂ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_isNondegenerateFixedPt_iterate`: a
  symplectic diffeomorphism supported near a periodic point makes its orbit nondegenerate in all
  iterates.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 3.2 (Darboux charts) and Chapter 11 (nondegenerate fixed points
  of symplectomorphisms).
-/

public section

noncomputable section

open Complex Filter Function Set Module
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The twist of `TauCeti.exists_diffeomorph_eventuallyEq_rotation`, read on a plane `E` through a
linear symplectomorphism `e` onto `ℂ`: it preserves the form, preserves `‖e ·‖`, is the identity
where `‖e ·‖ ≥ R`, and its derivative at `0` is the rotation by `θ` read through `e`. -/
private theorem exists_diffeomorph_of_symplectomorphism {ω₀ : SymplecticForm E} (e : E ≃L[ℝ] ℂ)
    (he : ∀ v w, stdComplexSymplecticForm (e v) (e w) = ω₀ v w) {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ∃ ψ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      (∀ y u v, ω₀ (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) = ω₀ u v) ∧
      (∀ y, ‖e (ψ y)‖ = ‖e y‖) ∧ (∀ y, R ≤ ‖e y‖ → ψ y = y) ∧
      HasFDerivAt ψ (e.symm.toContinuousLinearMap.comp
        ((exp (θ * Complex.I) • ContinuousLinearMap.id ℝ ℂ).comp e.toContinuousLinearMap)) 0 := by
  obtain ⟨ψ₀, hψ₀σ, hψ₀n, hψ₀id, hψ₀rot⟩ := exists_diffeomorph_eventuallyEq_rotation hR θ
  have hψ₀d : Differentiable ℝ ψ₀ :=
    (contMDiff_iff_contDiff.1 ψ₀.contMDiff).differentiable (by simp)
  refine ⟨e.toDiffeomorph.trans (ψ₀.trans e.symm.toDiffeomorph), fun y u v ↦ ?_,
    fun y ↦ by simp [hψ₀n], fun y hy ↦ by simp [hψ₀id _ hy], ?_⟩
  · have hd : fderiv ℝ ((e.symm ∘ ψ₀) ∘ e) y = e.symm.toContinuousLinearMap.comp
        ((fderiv ℝ ψ₀ (e y)).comp e.toContinuousLinearMap) :=
      (e.symm.hasFDerivAt.comp y ((hψ₀d (e y)).hasFDerivAt.comp y e.hasFDerivAt)).fderiv
    simp only [Diffeomorph.coe_trans, ContinuousLinearEquiv.coe_toDiffeomorph]
    rw [hd]
    calc ω₀ _ _ = stdComplexSymplecticForm (fderiv ℝ ψ₀ (e y) (e u))
          (fderiv ℝ ψ₀ (e y) (e v)) := by
          rw [← he]
          simp
      _ = ω₀ u v := by rw [hψ₀σ, he]
  · have h₀ : HasFDerivAt ψ₀ (exp (θ * Complex.I) • ContinuousLinearMap.id ℝ ℂ) (e 0) := by
      rw [map_zero]
      refine ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).const_mul
        (exp (θ * Complex.I))).congr_of_eventuallyEq (hψ₀rot.mono fun w hw ↦ ?_)
      simp [hw, mul_comm]
    exact e.symm.hasFDerivAt.comp _ (h₀.comp _ e.hasFDerivAt)

variable [BoundarylessManifold I M] [T2Space M]

omit [BoundarylessManifold I M] in
/-- The twist by `θ` of a small disc about `κ p = 0` in Darboux coordinates `e ∘ κ`, extended to
`M` by the identity. -/
private theorem exists_diffeomorph_of_darbouxChart {σ : SmoothTwoForm I M}
    {κ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {ω₁ : SymplecticForm E}
    (hκσ : ∀ x ∈ κ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = ω₁ (mvfderiv I κ x v) (mvfderiv I κ x w))
    {e : E ≃L[ℝ] ℂ} (he : ∀ v w, stdComplexSymplecticForm (e v) (e w) = ω₁ v w)
    {p : M} (hpκ : p ∈ κ.source) (hκp : κ p = 0) {U : Set M} {ρ : ℝ} (hρ : 0 < ρ)
    (hρV : ∀ w : ℂ, ‖w‖ < ρ → e.symm w ∈ κ.target ∧ κ.symm (e.symm w) ∈ U) (θ : ℝ) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M,
      (∀ x v w, σ.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ.eval₂ x v w) ∧
      (∃ K, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, Φ x = x) ∧ Φ p = p ∧
      HasMFDerivAt I I Φ p ((mfderiv 𝓘(ℝ, E) I κ.symm (κ p)).comp
        ((e.symm.toContinuousLinearMap.comp ((exp (θ * Complex.I) •
          ContinuousLinearMap.id ℝ ℂ).comp e.toContinuousLinearMap)).comp
            (mfderiv I 𝓘(ℝ, E) κ p))) := by
  have hl : κ.symm (κ p) = p := κ.toPartialEquiv.left_inv hpκ
  have hκt : κ p ∈ κ.target := κ.toPartialEquiv.map_source hpκ
  -- The twist by `θ` of the disc `C` of radius `ρ / 2` in the coordinates `e`, moved to `M`.
  obtain ⟨ψ, hψσ, hψn, hψid, hψd⟩ := exists_diffeomorph_of_symplectomorphism e he (half_pos hρ) θ
  set C : Set E := e ⁻¹' Metric.closedBall 0 (ρ / 2)
  have hCc : IsCompact C := e.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall 0 _)
  have hCV (y : E) (hy : y ∈ C) : e.symm (e y) ∈ κ.target ∧ κ.symm (e.symm (e y)) ∈ U :=
    hρV (e y) (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hy) (half_lt_self hρ))
  have hCt : C ⊆ κ.target := fun y hy ↦ by simpa using (hCV y hy).1
  have hψC (y : E) (hy : y ∉ C) : ψ y = y :=
    hψid y (le_of_lt (not_le.1 (by simpa [C] using hy)))
  have hψt (y : E) (hy : y ∈ κ.target) : ψ y ∈ κ.target :=
    (ψ.injective.apply_mem_iff_of_eq_self hψC hCt y).2 hy
  obtain ⟨Φ, hΦs, hΦC⟩ := κ.exists_diffeomorph_eq_symm_apply_apply ψ hCc hCt hψC
  have hKc : IsCompact (κ.symm '' C) :=
    hCc.image_of_continuousOn (κ.symm.contMDiffOn.continuousOn.mono hCt)
  have hΦid (x : M) (hx : x ∉ κ.symm '' C) : ⇑Φ =ᶠ[𝓝 x] id :=
    eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds hx) hΦC
  have hψ0 : ψ (κ p) = κ p := by
    rw [hκp]
    apply e.injective
    rw [map_zero e, ← norm_eq_zero, hψn, map_zero e, norm_zero]
  refine ⟨Φ, eval₂_mfderiv_eq_of_darbouxChart hκσ hψσ hψt hΦs
    fun x hx ↦ hΦid x fun h ↦ hx ?_, ⟨κ.symm '' C, hKc, ?_, hΦC⟩, ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := h
    exact κ.toPartialEquiv.map_target (hCt hy)
  · rintro _ ⟨y, hy, rfl⟩
    simpa using (hCV y hy).2
  · rw [hΦs p hpκ, hψ0, hl]
  · -- Near `p`, `Φ = κ⁻¹ ∘ ψ ∘ κ`, and `ψ` is the rotation by `θ` near `κ p = 0`.
    have hs : HasMFDerivAt 𝓘(ℝ, E) I κ.symm (ψ (κ p)) (mfderiv 𝓘(ℝ, E) I κ.symm (κ p)) := by
      rw [hψ0]
      exact (κ.symm.mdifferentiableAt (by simp) hκt).hasMFDerivAt
    exact (hs.comp p ((hasMFDerivAt_iff_hasFDerivAt.2 (hκp ▸ hψd)).comp p
      (κ.mdifferentiableAt (by simp) hpκ).hasMFDerivAt)).congr_of_eventuallyEq
      (eventually_of_mem (κ.open_source.mem_nhds hpκ) hΦs)

/-- **Symplectic twists of a surface at a point.** Let `(M, σ)` be a boundaryless symplectic
surface, `p` a point and `U` a neighbourhood of `p`. There is a real-linear identification `L` of
`T_p M` with `ℂ` such that, for every angle `θ`, some diffeomorphism `Φ` of `M` preserving `σ`
fixes `p` and every point outside a compact subset of `U`, and has derivative at `p` the rotation
by `θ` read through `L`. -/
theorem IsSymplectic.exists_continuousLinearEquiv_forall_exists_diffeomorph
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) (hE : finrank ℝ E = 2) {p : M} {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ L : TangentSpace I p ≃L[ℝ] ℂ, ∀ θ : ℝ, ∃ Φ : M ≃ₘ⟮I, I⟯ M,
      (∀ x v w, σ.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ.eval₂ x v w) ∧
      (∃ K, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, Φ x = x) ∧ Φ p = p ∧
      HasMFDerivAt I I Φ p ((L.symm : ℂ →L[ℝ] TangentSpace I p).comp
        ((exp (θ * Complex.I) • ContinuousLinearMap.id ℝ ℂ).comp
          (L : TangentSpace I p →L[ℝ] ℂ))) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  -- Darboux coordinates `κ` at `p`, read in `ℂ` through a linear symplectomorphism `e`.
  obtain ⟨κ, ω₁, hpκ, hκp, hκσ⟩ := hσ.exists_darbouxChart p
  obtain ⟨e₀, he₀⟩ := ω₁.exists_isSymplectomorphism stdComplexSymplecticForm
    (by rw [hE, Complex.finrank_real_complex])
  set e : E ≃L[ℝ] ℂ := e₀.toContinuousLinearEquiv
  have he (v w : E) : stdComplexSymplecticForm (e v) (e w) = ω₁ v w := he₀.apply v w
  have hl : κ.symm (κ p) = p := κ.toPartialEquiv.left_inv hpκ
  have hκt : κ p ∈ κ.target := κ.toPartialEquiv.map_source hpκ
  -- A disc about `0`, in the coordinates `e ∘ κ`, lying over `U`.
  obtain ⟨ρ, hρ, hρV⟩ : ∃ ρ > 0, ∀ w : ℂ, ‖w‖ < ρ →
      e.symm w ∈ κ.target ∧ κ.symm (e.symm w) ∈ U := by
    have hV : IsOpen (e.symm ⁻¹' (κ.target ∩ κ.symm ⁻¹' U)) :=
      (κ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage κ.open_target hU).preimage
        e.symm.continuous
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hV 0
      ⟨by rw [map_zero, ← hκp]; exact hκt, by rw [mem_preimage, map_zero, ← hκp, hl]; exact hpU⟩
    exact ⟨ρ, hρ, fun w hw ↦ hball (by simpa using hw)⟩
  -- The identification `L = e ∘ dκ_p`, with inverse `dκ⁻¹_{κ p} ∘ e⁻¹`.
  set L : TangentSpace I p ≃L[ℝ] ℂ := (ContinuousLinearEquiv.ofContinuousLinearMap
    (mfderiv I 𝓘(ℝ, E) κ p) (mfderiv 𝓘(ℝ, E) I κ.symm (κ p))
    (ContinuousLinearMap.ext fun y ↦ by
      have h := κ.mfderiv_apply_mfderiv_symm_apply (by simp) hκt y
      rwa [hl] at h)
    (ContinuousLinearMap.ext (κ.mfderiv_symm_apply_mfderiv_apply (by simp) hpκ))).trans e
  -- `simp` and `rw` cannot apply `trans_apply` here: the middle space of `L` is the type synonym
  -- `TangentSpace 𝓘(ℝ, E) (κ p)` while `e` is stated on `E`, so the instances only agree up to
  -- unfolding. The lemmas are therefore chained as terms, with the function-valued motive in `hLs`
  -- typed on the synonym for the same reason.
  have hLa (u : TangentSpace I p) : L u = e (mfderiv I 𝓘(ℝ, E) κ p u) :=
    (ContinuousLinearEquiv.trans_apply _ _ u).trans
      (congrArg e (congrFun (ContinuousLinearEquiv.coe_ofContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) κ p) _ _ _) u))
  have hLs (z : ℂ) : L.symm z = mfderiv 𝓘(ℝ, E) I κ.symm (κ p) (e.symm z) :=
    (ContinuousLinearEquiv.symm_trans_apply _ _ z).trans
      ((congrArg (fun f : TangentSpace 𝓘(ℝ, E) (κ p) ≃L[ℝ] TangentSpace I p ↦ f (e.symm z))
        (ContinuousLinearEquiv.symm_ofContinuousLinearMap (mfderiv I 𝓘(ℝ, E) κ p)
          (mfderiv 𝓘(ℝ, E) I κ.symm (κ p)) _ _)).trans
        (congrFun (ContinuousLinearEquiv.coe_ofContinuousLinearMap _ _ _ _) _))
  refine ⟨L, fun θ ↦ ?_⟩
  obtain ⟨Φ, hΦσ, hΦK, hΦp, hΦd⟩ := exists_diffeomorph_of_darbouxChart hκσ he hpκ hκp hρ hρV θ
  -- The derivative is `L⁻¹ ∘ (rotation by θ) ∘ L`, by `hLa` and `hLs`.
  refine ⟨Φ, hΦσ, hΦK, hΦp, hΦd.congr_mfderiv ?_⟩
  ext v
  exact ((congrArg (fun z ↦ L.symm (exp (θ * Complex.I) • z)) (hLa v)).trans (hLs _)).symm

/-- **Making a periodic orbit nondegenerate in all iterates by a symplectic twist.** Let
`(M, σ)` be a boundaryless symplectic surface and `p` a periodic point of period `k > 0` of a map
`φ : M → M`, whose linearized return map `A`, the derivative of `φ^[k]` at `p`, has determinant
one, as for an area-preserving map. Let `U` be a neighbourhood of `p` containing no other point of
its orbit. Then some diffeomorphism `Φ` of `M` preserving `σ`, fixing `p` and every point outside a
compact subset of `U`, makes the orbit nondegenerate in all iterates: `p` is a nondegenerate fixed
point of `(φ ∘ Φ)^[k * n]` for every `n > 0`. Since `Φ` preserves `σ`, the perturbed map `φ ∘ Φ`
is area preserving whenever `φ` is. -/
theorem IsSymplectic.exists_diffeomorph_isNondegenerateFixedPt_iterate
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) (hE : finrank ℝ E = 2)
    {φ : M → M} {p : M} {k : ℕ} (hk : 0 < k) (hp : φ^[k] p = p)
    {A : TangentSpace I p →L[ℝ] TangentSpace I p} (hA : HasMFDerivAt I I φ^[k] p A)
    (hdet : LinearMap.det (A : TangentSpace I p →ₗ[ℝ] TangentSpace I p) = 1)
    (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p)) {U : Set M} (hU : IsOpen U) (hpU : p ∈ U)
    (horb : ∀ j, 0 < j → j < k → φ^[j] p ∉ U) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M,
      (∀ x v w, σ.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ.eval₂ x v w) ∧
      (∃ K, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, Φ x = x) ∧ Φ p = p ∧
      ∀ n, 0 < n → IsNondegenerateFixedPt I (φ ∘ Φ)^[k * n] p := by
  obtain ⟨L, hL⟩ := hσ.exists_continuousLinearEquiv_forall_exists_diffeomorph hE hU hpU
  -- The return map read in `ℂ` through `L`, and an angle `θ` such that no nonzero power of the
  -- rotation by `θ` followed by it has the eigenvalue `1`; all but countably many angles do.
  set B : Module.End ℝ ℂ := (L.toLinearEquiv : TangentSpace I p →ₗ[ℝ] ℂ) ∘ₗ
    (A : TangentSpace I p →ₗ[ℝ] TangentSpace I p) ∘ₗ
      (L.toLinearEquiv.symm : ℂ →ₗ[ℝ] TangentSpace I p)
  have hB : LinearMap.det B = 1 := by rw [LinearMap.det_conj, hdet]
  obtain ⟨θ, hθ⟩ :=
    ((LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero hB).dense_compl
      ℝ).nonempty
  obtain ⟨Φ, hΦσ, ⟨K, hKc, hKU, hΦK⟩, hΦp, hΦd⟩ := hL θ
  refine ⟨Φ, hΦσ, ⟨K, hKc, hKU, hΦK⟩, hΦp, fun n hn ↦ ?_⟩
  -- The return map of `φ ∘ Φ` at `p` is `A` composed with the derivative of `Φ`.
  have hid (j : ℕ) (hj : 0 < j) (hjk : j < k) : ⇑Φ =ᶠ[𝓝 (φ^[j] p)] id :=
    eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds fun h ↦ horb j hj hjk (hKU h)) hΦK
  have heq : (φ ∘ Φ)^[k] =ᶠ[𝓝 p] φ^[k] ∘ Φ :=
    iterate_comp_eventuallyEq_of_eventuallyEq_id hk hΦp Φ.continuous.continuousAt hφ hid
  have hT := ((by rw [hΦp]; exact hA : HasMFDerivAt I I φ^[k] (Φ p) A).comp p
    hΦd).congr_of_eventuallyEq heq
  have hfix : IsFixedPt (φ ∘ Φ)^[k] p := by
    rw [IsFixedPt, heq.eq_of_nhds, comp_apply, hΦp, hp]
  rw [iterate_mul, isNondegenerateFixedPt_iterate_iff hT hfix]
  intro v hv
  -- `L` conjugates the return map to the rotation by `θ` followed by `B`.
  set Bθ : Module.End ℝ ℂ := B * Algebra.lmul ℝ ℂ (exp (θ * Complex.I))
  set D : TangentSpace I p →L[ℝ] TangentSpace I p :=
    A.comp ((L.symm : ℂ →L[ℝ] TangentSpace I p).comp
      ((exp (θ * Complex.I) • ContinuousLinearMap.id ℝ ℂ).comp (L : TangentSpace I p →L[ℝ] ℂ)))
  have hD : L.toLinearEquiv.conjAlgEquiv ℝ (D : Module.End ℝ (TangentSpace I p)) = Bθ := by
    ext z
    simp [D, Bθ, B]
  have hpow (u : TangentSpace I p) : L ((D ^ n) u) = (Bθ ^ n) (L u) := by
    rw [← hD, ← map_pow, LinearEquiv.conjAlgEquiv_apply, ← ContinuousLinearMap.toLinearMap_pow]
    simp [-ContinuousLinearMap.toLinearMap_pow]
  have hinj : Injective ((1 : Module.End ℝ ℂ) - Bθ ^ n) := by
    have hdet : LinearMap.det ((1 : Module.End ℝ ℂ) - Bθ ^ n) ≠ 0 := fun h ↦ hθ ⟨n, hn.ne', h⟩
    exact ((Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))).1
  have hLv : L v = 0 := hinj <| by
    rw [map_zero, LinearMap.sub_apply, ← hpow, one_apply_eq_self, sub_eq_zero]
    exact congrArg L hv.symm
  simpa using hLv

end SmoothTwoForm

end TauCeti
