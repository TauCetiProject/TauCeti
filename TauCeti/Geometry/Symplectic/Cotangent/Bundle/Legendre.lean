/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The Legendre map of a Lagrangian

A *Lagrangian* on a manifold `M` is a function `L : TM → 𝕜` on its tangent bundle. Restricting `L`
to the tangent space `T_x M`, a vector space, and differentiating there gives its **fibre
derivative**, or **Legendre map**, `FL : TM → T*M`
(`TauCeti.legendreMap`): a tangent vector `v` at `x` goes to the covector at `x`

`FL(v)(w) = d/dt|_(t=0) L(v + t w)`,

the derivative at `v` of `L` restricted to the fibre `T_x M`. This needs no chart or connection,
since only derivatives along a single fibre occur, and it covers the identity of `M`. In a bundle
chart with coordinates `(q, v)` it is the partial derivative `(q, v) ↦ (q, ∂L/∂v)`, so it loses one
degree of smoothness: if `L` is `C^n` then `FL` is `C^m` whenever `m + 1 ≤ n`
(`TauCeti.contMDiff_legendreMap`).

The Legendre map carries the canonical structures of `T*M` back to `TM`. The **energy** of `L` is
`E_L(v) = FL(v)(v) - L(v)` (`TauCeti.lagrangianEnergy`), and for real smooth `L` the **Cartan
one-form** `θ_L = FL^*λ` (`TauCeti.cartanForm`) and **Cartan two-form** `ω_L = -dθ_L`
(`TauCeti.cartanTwoForm`) are the pullbacks of the Liouville form `λ` and of the canonical
symplectic form `ω = -dλ` of the cotangent bundle (`TauCeti.mpullback_legendreMap_symplecticForm`).
Explicitly `θ_L(v)(ξ) = FL(v)(dπ ξ)` (`TauCeti.cartanForm_apply`). These are the structures
through which a Lagrangian system on `TM` is compared with a Hamiltonian system on `T*M`: when `FL`
is a diffeomorphism, the corresponding Hamiltonian is `E_L ∘ FL⁻¹`.

Subtracting a potential `V : M → 𝕜` changes neither the Legendre map nor the Cartan forms, and adds
`V` to the energy (`TauCeti.legendreMap_sub_comp_proj`, `TauCeti.lagrangianEnergy_sub_comp_proj`).
The basic example is the Lagrangian `L(v) = ½ g(v, v) - V(x)` of a mechanical system with kinetic
energy given by a fibrewise symmetric bilinear form `g`, such as the `inner` field of a Riemannian
metric (`TauCeti.mechanicalLagrangian`). Its Legendre map is `v ↦ g(v, ·)`, the index-lowering map
of `g`, and its energy is the total energy `½ g(v, v) + V(x)`
(`TauCeti.legendreMap_mechanicalLagrangian_snd`, `TauCeti.lagrangianEnergy_mechanicalLagrangian`).

## Main declarations

* `TauCeti.legendreMap`: the fibre derivative `FL : TM → T*M` of a Lagrangian.
* `TauCeti.contMDiff_legendreMap`: `FL` is `C^m` when `L` is `C^n` and `m + 1 ≤ n`.
* `TauCeti.lagrangianEnergy`: the energy `E_L(v) = FL(v)(v) - L(v)`, with
  `TauCeti.contMDiff_lagrangianEnergy`.
* `TauCeti.cartanForm`, `TauCeti.cartanTwoForm`: the Cartan forms `θ_L = FL^*λ` and
  `ω_L = -dθ_L = FL^*ω`.
* `TauCeti.mechanicalLagrangian`: the Lagrangian `½ g(v, v) - V(x)`, with its Legendre map and
  energy.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 7.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

section LegendreMap

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- The **Legendre map**, or fibre derivative, `FL : TM → T*M` of a Lagrangian `L : TM → 𝕜`: it
sends a tangent vector `v` at `x` to the covector at `x` given by the derivative at `v` of the
restriction of `L` to the tangent space `T_x M`. -/
def legendreMap (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) : CotangentBundle I M :=
  TotalSpace.mk' (E →L[𝕜] 𝕜) v.proj
    (fderiv 𝕜 (fun w : E ↦ L (TotalSpace.mk' E v.proj w)) v.2)

/-- The Legendre map covers the identity of the base. -/
@[simp]
theorem proj_legendreMap (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) :
    (legendreMap L v).proj = v.proj :=
  (rfl)

/-- The covector `FL(v)` is the derivative at `v` of `L` restricted to the fibre through `v`. -/
theorem legendreMap_snd (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) :
    (legendreMap L v).2 = fderiv 𝕜 (fun w : E ↦ L (TotalSpace.mk' E v.proj w)) v.2 :=
  (rfl)

/-- **The Legendre map in a trivialization.** Read in a trivialization `e` of the tangent bundle,
the covector `FL(v)` is the derivative of `u ↦ L(e⁻¹(x, u))` at the fibre coordinate of `v`. -/
private theorem legendreMap_snd_comp_symmL [IsManifold I 1 M] (L : TangentBundle I M → 𝕜)
    {x₀ : M} {v : TangentBundle I M}
    (hv : v.proj ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ((legendreMap L v).2 ∘L (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 v.proj :
        E →L[𝕜] 𝕜) =
      fderiv 𝕜 (fun u : E ↦ L (TotalSpace.mk' E v.proj
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 v.proj u)))
        (trivializationAt E (TangentSpace I) x₀ v).2 := by
  set e := trivializationAt E (TangentSpace I) x₀
  set A : E ≃L[𝕜] E := e.continuousLinearEquivAt 𝕜 v.proj hv
  have hA : ((A.symm : E →L[𝕜] E) : E → E) = e.symmL 𝕜 v.proj :=
    e.symm_continuousLinearEquivAt_eq hv
  have hfun : (fun u : E ↦ L (TotalSpace.mk' E v.proj (e.symmL 𝕜 v.proj u))) =
      (fun w : E ↦ L (TotalSpace.mk' E v.proj w)) ∘ A.symm := by
    funext u
    simp [← hA]
  have hv2 : A.symm (e v).2 = v.2 := e.symm_proj_apply v hv
  rw [hfun, A.symm.comp_right_fderiv, hv2]
  ext u
  exact congrArg (fderiv 𝕜 (fun w : E ↦ L (TotalSpace.mk' E v.proj w)) v.2)
    (congrFun hA u).symm

/-- **The Legendre map is smooth.** If the Lagrangian `L` is `C^n`, its Legendre map is `C^m`
whenever `m + 1 ≤ n`: in bundle coordinates it is the partial derivative of `L` along the fibres. -/
theorem contMDiff_legendreMap [IsManifold I 2 M] {L : TangentBundle I M → 𝕜}
    {m n : WithTop ℕ∞} (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m (legendreMap L) := by
  intro v₀
  set e := trivializationAt E (TangentSpace I) v₀.proj
  have hbase : ∀ᶠ v in 𝓝 v₀, v.proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' v₀.proj))
  have hg : ContMDiffAt I.tangent 𝓘(𝕜, E) m (fun v ↦ (e v).2) v₀ :=
    (contMDiffAt_totalSpace.1 contMDiffAt_id).2
  have hk : ContMDiffAt (I.tangent.prod 𝓘(𝕜, E)) I.tangent n
      (fun p : TangentBundle I M × E ↦ TotalSpace.mk' E p.1.proj (e.symmL 𝕜 p.1.proj p.2))
      (v₀, (e v₀).2) := by
    have hproj : ContMDiffAt (I.tangent.prod 𝓘(𝕜, E)) I n
        (fun p : TangentBundle I M × E ↦ p.1.proj) (v₀, (e v₀).2) :=
      (contMDiffAt_proj (TangentSpace I)).comp (v₀, (e v₀).2)
        (contMDiffAt_fst (I := I.tangent) (J := 𝓘(𝕜, E)))
    rw [contMDiffAt_totalSpace]
    refine ⟨hproj,
      contMDiffAt_snd.congr_of_eventuallyEq ?_⟩
    filter_upwards [continuousAt_fst.preimage_mem_nhds hbase] with p hp
    rw [Trivialization.symmL_apply _ hp, Trivialization.apply_mk_symm _ hp]
  have hd := ContMDiffAt.mfderiv (fun v u ↦ L (TotalSpace.mk' E v.proj (e.symmL 𝕜 v.proj u)))
    (fun v ↦ (e v).2) ((hL _).comp _ hk) hg hmn
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj (TangentSpace I), hd.congr_of_eventuallyEq ?_⟩
  filter_upwards [hbase] with v hv
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp]
  simp +unfoldPartialApp only [inTangentCoordinates, mfderiv_eq_fderiv]
  -- Tangent coordinates on a model space are trivial. The coordinate lemma is stated for linear
  -- maps between model spaces, so it applies to these tangent-space maps only up to unfolding
  -- `TangentSpace`, which `erw` performs.
  erw [inCoordinates_tangent_bundle_core_model_space (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, 𝕜))]
  ext u
  exact DFunLike.congr_fun (legendreMap_snd_comp_symmL L hv) u

/-- The **energy** `E_L(v) = FL(v)(v) - L(v)` of a Lagrangian `L`, where `FL` is its Legendre
map. -/
def lagrangianEnergy (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) : 𝕜 :=
  (legendreMap L v).2 v.2 - L v

/-- The energy is the Legendre map paired with the velocity, minus the Lagrangian. -/
theorem lagrangianEnergy_apply (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) :
    lagrangianEnergy L v = (legendreMap L v).2 v.2 - L v :=
  (rfl)

/-- Subtracting a potential, a function of the base point only, does not change the Legendre
map. -/
@[simp]
theorem legendreMap_sub_comp_proj (L : TangentBundle I M → 𝕜) (V : M → 𝕜) :
    legendreMap (fun v ↦ L v - V v.proj) = legendreMap L := by
  funext v
  refine CotangentBundle.ext rfl fun w ↦ ?_
  rw [legendreMap_snd, legendreMap_snd]
  exact DFunLike.congr_fun
    (fderiv_sub_const (f := fun w : E ↦ L (TotalSpace.mk' E v.proj w)) (V v.proj)) w

/-- Subtracting a potential `V` from a Lagrangian adds `V` to its energy. -/
theorem lagrangianEnergy_sub_comp_proj (L : TangentBundle I M → 𝕜) (V : M → 𝕜)
    (v : TangentBundle I M) :
    lagrangianEnergy (fun v ↦ L v - V v.proj) v = lagrangianEnergy L v + V v.proj := by
  rw [lagrangianEnergy_apply, lagrangianEnergy_apply, legendreMap_sub_comp_proj]
  ring

/-- **The energy is smooth.** If the Lagrangian `L` is `C^n`, its energy is `C^m` whenever
`m + 1 ≤ n`. -/
theorem contMDiff_lagrangianEnergy [IsManifold I 2 M] {L : TangentBundle I M → 𝕜}
    {m n : WithTop ℕ∞} (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent 𝓘(𝕜, 𝕜) m (lagrangianEnergy L) := by
  intro v₀
  set e := trivializationAt E (TangentSpace I) v₀.proj
  have hbase : ∀ᶠ v in 𝓝 v₀, v.proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' v₀.proj))
  have hg : ContMDiffAt I.tangent 𝓘(𝕜, E) m (fun v ↦ (e v).2) v₀ :=
    (contMDiffAt_totalSpace.1 contMDiffAt_id).2
  have hc := ((contMDiffAt_hom_bundle _).1 (contMDiff_legendreMap hL hmn v₀)).2
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    proj_legendreMap] at hc
  refine ((hc.clm_apply hg).sub (hL.of_le (le_self_add.trans hmn) v₀)).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with v hv
  have hv₂ : e.symmL 𝕜 v.proj (e v).2 = v.2 := by
    rw [Trivialization.symmL_apply _ hv, Trivialization.symm_proj_apply _ _ hv]
  rw [lagrangianEnergy_apply, ContinuousLinearMap.comp_apply]
  exact congrArg (fun w ↦ (legendreMap L v).2 w - L v) hv₂.symm

end LegendreMap

section Cartan

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The **Cartan one-form** `θ_L = FL^*λ` of a smooth real Lagrangian `L`: the pullback of the
Liouville form of the cotangent bundle by the Legendre map. -/
def cartanForm (L : TangentBundle I M → ℝ) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    SmoothForm I.tangent (TangentBundle I M) ℝ 1 :=
  SmoothForm.mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl)
    (CotangentBundle.liouvilleForm I M)

/-- The Cartan one-form evaluates a tangent vector `ξ` of `TM` at `v` by applying the covector
`FL(v)` to the image of `ξ` under the derivative of the projection `π : TM → M`. -/
theorem cartanForm_apply {L : TangentBundle I M → ℝ} (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (v : TangentBundle I M) (ξ : Fin 1 → TangentSpace I.tangent v) :
    (cartanForm L hL).1 v ξ =
      (legendreMap L v).2 (mfderiv I.tangent I (π E (TangentSpace I)) v (ξ 0)) := by
  have hcomp := mfderiv_comp v
    ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_legendreMap (m := ∞) hL le_rfl v).mdifferentiableAt (by simp))
  have hπ : π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∘ legendreMap L =
      π E (TangentSpace I) :=
    funext (proj_legendreMap L)
  rw [hπ] at hcomp
  rw [cartanForm, SmoothForm.mpullback_apply, CotangentBundle.liouvilleForm_apply]
  exact congrArg (legendreMap L v).2 (DFunLike.congr_fun hcomp (ξ 0)).symm

/-- The **Cartan two-form** `ω_L = -dθ_L` of a smooth real Lagrangian `L`. It is the pullback of
the canonical symplectic form of the cotangent bundle by the Legendre map
(`TauCeti.mpullback_legendreMap_symplecticForm`). -/
def cartanTwoForm (L : TangentBundle I M → ℝ) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    SmoothTwoForm I.tangent (TangentBundle I M) :=
  -mextDerivₗ I.tangent 1 (cartanForm L hL)

/-- The Cartan two-form is minus the exterior derivative of the Cartan one-form. -/
theorem cartanTwoForm_eq_neg_mextDerivₗ {L : TangentBundle I M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    cartanTwoForm L hL = -mextDerivₗ I.tangent 1 (cartanForm L hL) :=
  (rfl)

/-- The Legendre map pulls the canonical symplectic form `ω = -dλ` of the cotangent bundle back to
the Cartan two-form: `FL^*ω = ω_L`. -/
theorem mpullback_legendreMap_symplecticForm {L : TangentBundle I M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    SmoothForm.mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl)
      (CotangentBundle.symplecticForm I M) = cartanTwoForm L hL := by
  rw [CotangentBundle.symplecticForm_eq_neg_mextDerivₗ, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, cartanTwoForm_eq_neg_mextDerivₗ, cartanForm]

end Cartan

section Mechanical

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The Lagrangian `L(v) = ½ g(v, v) - V(x)` of a mechanical system on `M`, with kinetic energy
given by a family `g` of bilinear forms on the tangent spaces and potential energy `V`. For a
Riemannian metric `g` is its `inner` field. -/
def mechanicalLagrangian (g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (V : M → ℝ) (v : TangentBundle I M) : ℝ :=
  2⁻¹ * g v.proj v.2 v.2 - V v.proj

/-- The mechanical Lagrangian is kinetic minus potential energy. -/
theorem mechanicalLagrangian_apply
    (g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (V : M → ℝ)
    (v : TangentBundle I M) :
    mechanicalLagrangian g V v = 2⁻¹ * g v.proj v.2 v.2 - V v.proj :=
  (rfl)

/-- **A mechanical Lagrangian is smooth** when its kinetic form `g`, as a section of the bundle
of bilinear forms on the tangent spaces, and its potential `V` are smooth. -/
theorem contMDiff_mechanicalLagrangian [IsManifold I ∞ M]
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {V : M → ℝ}
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞ (fun x ↦ TotalSpace.mk'
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] Trivial M ℝ x)
      (E →L[ℝ] E →L[ℝ] ℝ) x (g x)))
    (hV : ContMDiff I 𝓘(ℝ) ∞ V) :
    ContMDiff I.tangent 𝓘(ℝ) ∞ (mechanicalLagrangian g V) := by
  have hq : ContMDiff I.tangent (I.prod 𝓘(ℝ)) ∞ (fun v : TangentBundle I M ↦
      TotalSpace.mk' ℝ (E := Trivial M ℝ) v.proj (g v.proj v.2 v.2)) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (hg.comp (contMDiff_proj _)) contMDiff_id
      contMDiff_id
  have hq' : ContMDiff I.tangent 𝓘(ℝ) ∞ (fun v : TangentBundle I M ↦ g v.proj v.2 v.2) :=
    fun v ↦ (contMDiffAt_totalSpace.1 (hq v)).2
  have hhalf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ 2⁻¹ * t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  rw [funext (mechanicalLagrangian_apply g V)]
  exact (hhalf.comp hq').sub (hV.comp (contMDiff_proj _))

/-- **The Legendre map of a mechanical Lagrangian** lowers the index with the kinetic form: for
symmetric `g` it sends `v` to the covector `g(v, ·)`. -/
theorem legendreMap_mechanicalLagrangian_snd
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) (V : M → ℝ) (v : TangentBundle I M) :
    (legendreMap (mechanicalLagrangian g V) v).2 = g v.proj v.2 := by
  -- The derivative of the quadratic form of a symmetric bilinear form on the model space.
  have key (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (w₀ : E) :
      HasFDerivAt (fun w ↦ 2⁻¹ * B w w) (B w₀) w₀ := by
    refine ((B.hasFDerivAt_of_bilinear (hasFDerivAt_id w₀) (hasFDerivAt_id w₀)).const_mul
      2⁻¹).congr_fderiv ?_
    ext u
    simp [hB u w₀]
    ring
  rw [legendreMap_snd]
  simp only [mechanicalLagrangian_apply]
  exact ((key (g v.proj) (hg v.proj) v.2).sub_const (V v.proj)).fderiv

/-- **The energy of a mechanical Lagrangian** is the total energy `½ g(v, v) + V(x)`, kinetic plus
potential, for symmetric `g`. -/
theorem lagrangianEnergy_mechanicalLagrangian
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) (V : M → ℝ) (v : TangentBundle I M) :
    lagrangianEnergy (mechanicalLagrangian g V) v = 2⁻¹ * g v.proj v.2 v.2 + V v.proj := by
  rw [lagrangianEnergy_apply, legendreMap_mechanicalLagrangian_snd hg, mechanicalLagrangian_apply]
  -- The two occurrences of `g v v` differ only in the fibre they are typed in.
  exact (fun a b ↦ by ring : ∀ a b : ℝ, a - (2⁻¹ * a - b) = 2⁻¹ * a + b) _ _

/-- The Cartan one-form of a smooth mechanical Lagrangian is `θ_L(v)(ξ) = g(v, dπ ξ)`, for
symmetric `g`. -/
theorem cartanForm_mechanicalLagrangian_apply [IsManifold I ∞ M]
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) {V : M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (mechanicalLagrangian g V)) (v : TangentBundle I M)
    (ξ : Fin 1 → TangentSpace I.tangent v) :
    (cartanForm (mechanicalLagrangian g V) hL).1 v ξ =
      g v.proj v.2 (mfderiv I.tangent I (π E (TangentSpace I)) v (ξ 0)) := by
  rw [cartanForm_apply, legendreMap_mechanicalLagrangian_snd hg]
  -- The two sides differ only in the fibre in which `g v` is typed.
  rfl

end Mechanical

end TauCeti
