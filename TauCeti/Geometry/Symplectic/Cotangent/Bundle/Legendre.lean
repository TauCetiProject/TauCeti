/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.FiberBundle.Trivialization
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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

Differentiating the Legendre map once more along the fibre gives the **fibre Hessian**
(`TauCeti.fiberHessian`): at a tangent vector `v` at `x` it is the bilinear form on `T_x M` given by
the second derivative at `v` of `L` restricted to `T_x M`, in coordinates the matrix
`∂²L/∂v∂v`. A Lagrangian is **regular** when all its fibre Hessians are invertible
(`TauCeti.IsRegularLagrangian`). Regularity is exactly the condition for inverting the Legendre
map locally, which relates the Lagrangian and Hamiltonian descriptions of a mechanical system. In
bundle charts with coordinates `(q, v)` and `(q, p)`, the differential of `FL` at a tangent vector
has the block lower triangular form `(δq, δv) ↦ (δq, ∂²L/∂q∂v δq + ∂²L/∂v∂v δv)`, so it is
invertible exactly when the fibre Hessian there is
(`TauCeti.isInvertible_mfderiv_legendreMap_iff`). By the inverse function theorem, the Legendre
map of a `C^(m+1)` Lagrangian, `1 ≤ m`, is a `C^m` local diffeomorphism at an interior tangent
vector exactly when the fibre Hessian there is invertible
(`TauCeti.isLocalDiffeomorphAt_legendreMap_iff`); on a boundaryless manifold it is a local
diffeomorphism exactly when the Lagrangian is regular
(`TauCeti.isLocalDiffeomorph_legendreMap_iff`).

Subtracting a potential `V : M → 𝕜` changes neither the Legendre map, nor the fibre Hessian, nor the
Cartan forms, and adds `V` to the energy (`TauCeti.legendreMap_sub_comp_proj`,
`TauCeti.fiberHessian_sub_comp_proj`, `TauCeti.cartanForm_sub_comp_proj`,
`TauCeti.cartanTwoForm_sub_comp_proj`, `TauCeti.lagrangianEnergy_sub_comp_proj`).
The basic example is the Lagrangian `L(v) = ½ g(v, v) - V(x)` of a mechanical system with kinetic
energy given by a fibrewise symmetric bilinear form `g`, such as the `inner` field of a Riemannian
metric (`TauCeti.mechanicalLagrangian`). Its Legendre map is `v ↦ g(v, ·)`, the index-lowering map
of `g`, and its energy is the total energy `½ g(v, v) + V(x)`
(`TauCeti.legendreMap_mechanicalLagrangian_snd`, `TauCeti.lagrangianEnergy_mechanicalLagrangian`).
Its fibre Hessian is `g` itself (`TauCeti.fiberHessian_mechanicalLagrangian`), so it is regular
exactly when each `g x` is invertible as a map from `T_x M` onto its continuous dual
(`TauCeti.isRegularLagrangian_mechanicalLagrangian_iff`). On a finite-dimensional manifold this
means `g` is nondegenerate, and holds in particular when `g` is positive definite, as for a
Riemannian metric (`TauCeti.isRegularLagrangian_mechanicalLagrangian`).

## Main declarations

* `TauCeti.legendreMap`: the fibre derivative `FL : TM → T*M` of a Lagrangian.
* `TauCeti.contMDiff_legendreMap`: `FL` is `C^m` when `L` is `C^n` and `m + 1 ≤ n`.
* `TauCeti.lagrangianEnergy`: the energy `E_L(v) = FL(v)(v) - L(v)`, with
  `TauCeti.contMDiff_lagrangianEnergy`.
* `TauCeti.fiberHessian`, `TauCeti.IsRegularLagrangian`: the fibre Hessian of a Lagrangian, and
  regular Lagrangians.
* `TauCeti.isInvertible_mfderiv_legendreMap_iff`: the differential of `FL` is invertible exactly
  where the fibre Hessian is.
* `TauCeti.isLocalDiffeomorphAt_legendreMap_iff`, `TauCeti.isLocalDiffeomorph_legendreMap_iff`:
  `FL` is a local diffeomorphism at a tangent vector exactly when the fibre Hessian there is
  invertible, and everywhere exactly when the Lagrangian is regular.
* `TauCeti.cartanForm`, `TauCeti.cartanTwoForm`: the Cartan forms `θ_L = FL^*λ` and
  `ω_L = -dθ_L = FL^*ω`.
* `TauCeti.mechanicalLagrangian`: the Lagrangian `½ g(v, v) - V(x)`, with its Legendre map,
  energy and fibre Hessian, and its regularity for `g` invertible onto the dual, in particular
  for positive definite `g` in finite dimensions.

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
  have hbase := TotalSpace.eventually_proj_mem_baseSet_trivializationAt v₀
  have hg := TotalSpace.contMDiffAt_trivializationAt_snd (IB := I) (n := m) v₀
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
@[simp]
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
  -- Apply the covector `FL(v)` to `v` as sections of bundles over `TM`, then read off the scalar.
  have h := ContMDiff.clm_bundle_apply (E₂ := Trivial M 𝕜) (v := fun v : TangentBundle I M ↦ v.2)
    (contMDiff_legendreMap hL hmn) contMDiff_id
  exact fun v ↦ (contMDiffAt_totalSpace.1 (h v)).2.sub (hL.of_le (le_self_add.trans hmn) v)

end LegendreMap

section FiberHessian

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- The **fibre Hessian** of a Lagrangian `L : TM → 𝕜` at a tangent vector `v` at `x`: the second
derivative at `v` of the restriction of `L` to the tangent space `T_x M`. It is a bilinear form on
`T_x M`, the derivative at `v` of the Legendre map restricted to this fibre
(`TauCeti.fiberHessian_eq_fderiv_legendreMap`). -/
def fiberHessian (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) :
    TangentSpace I v.proj →L[𝕜] TangentSpace I v.proj →L[𝕜] 𝕜 :=
  fderiv 𝕜 (fderiv 𝕜 (fun w : E ↦ L (TotalSpace.mk' E v.proj w))) v.2

/-- The fibre Hessian is the second derivative of the Lagrangian restricted to a fibre. -/
theorem fiberHessian_def (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) :
    fiberHessian L v = fderiv 𝕜 (fderiv 𝕜 (fun w : E ↦ L (TotalSpace.mk' E v.proj w))) v.2 :=
  (rfl)

/-- The fibre Hessian is the derivative of the Legendre map along the fibre: on `T_x M` the
Legendre map is the derivative of `L`, so its derivative at `v` is the fibre Hessian. -/
theorem fiberHessian_eq_fderiv_legendreMap (L : TangentBundle I M → 𝕜) (v : TangentBundle I M) :
    fiberHessian L v =
      fderiv 𝕜 (fun w : E ↦ ((legendreMap L (TotalSpace.mk' E v.proj w)).2 : E →L[𝕜] 𝕜)) v.2 :=
  (rfl)

/-- Subtracting a potential, a function of the base point only, does not change the fibre
Hessian. -/
@[simp]
theorem fiberHessian_sub_comp_proj (L : TangentBundle I M → 𝕜) (V : M → 𝕜) :
    fiberHessian (fun v ↦ L v - V v.proj) = fiberHessian L := by
  funext v
  rw [fiberHessian_def, fiberHessian_def]
  congr 1
  exact funext fun w ↦
    fderiv_sub_const (𝕜 := 𝕜) (f := fun w : E ↦ L (TotalSpace.mk' E v.proj w)) (V v.proj)

/-- A Lagrangian `L : TM → 𝕜` is **regular** when its fibre Hessian is invertible at every
tangent vector: contraction with the fibre Hessian is an isomorphism from each tangent space onto
its dual. -/
def IsRegularLagrangian (L : TangentBundle I M → 𝕜) : Prop :=
  ∀ v : TangentBundle I M, (fiberHessian L v).IsInvertible

/-- A Lagrangian is regular exactly when its fibre Hessian is invertible at every tangent
vector. -/
theorem isRegularLagrangian_iff {L : TangentBundle I M → 𝕜} :
    IsRegularLagrangian L ↔ ∀ v : TangentBundle I M, (fiberHessian L v).IsInvertible :=
  Iff.rfl

/-- Subtracting a potential does not change whether a Lagrangian is regular. -/
@[simp]
theorem isRegularLagrangian_sub_comp_proj_iff {L : TangentBundle I M → 𝕜} {V : M → 𝕜} :
    IsRegularLagrangian (fun v ↦ L v - V v.proj) ↔ IsRegularLagrangian L := by
  simp only [isRegularLagrangian_iff, fiberHessian_sub_comp_proj]

end FiberHessian

section Differential

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {L : TangentBundle I M → 𝕜} {n : WithTop ℕ∞}

/-- In bundle charts, the differential of the Legendre map keeps the base coordinate, because the
Legendre map covers the identity of `M`. -/
private theorem fst_comp_mfderiv_legendreMap (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L)
    (hn : 2 ≤ n) (v : TangentBundle I M) :
    ContinuousLinearMap.fst 𝕜 E (E →L[𝕜] 𝕜) ∘L
        mfderiv I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L) v =
      ContinuousLinearMap.fst 𝕜 E E := by
  have hcomp := mfderiv_comp v
    ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_legendreMap (m := 1) hL (by simpa [one_add_one_eq_two] using hn) v
      ).mdifferentiableAt one_ne_zero)
  have hπ : π (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ∘ legendreMap L =
      π E (TangentSpace I) :=
    funext (proj_legendreMap L)
  rw [hπ, Bundle.mfderiv_proj, Bundle.mfderiv_proj] at hcomp
  exact hcomp.symm

/-- **The differential of the Legendre map on vertical vectors.** In bundle charts, the
differential of the Legendre map at `v` sends the vertical vector with fibre coordinate `w` to the
vertical covector with fibre coordinate the fibre Hessian `∂²L/∂v∂v` applied to `w`. It is stated
for the differential `T` read as a map between the model spaces of the charts. -/
private theorem mfderiv_legendreMap_vertical (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L)
    (hn : 2 ≤ n) (v : TangentBundle I M) {T : E × E →L[𝕜] E × (E →L[𝕜] 𝕜)}
    (hT : mfderiv I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L) v = T)
    (w : TangentSpace I v.proj) :
    T (0, (trivializationAt E (TangentSpace I) v.proj).continuousLinearMapAt 𝕜 v.proj w) =
      (0, (trivializationAt (E →L[𝕜] 𝕜) (fun x ↦ TangentSpace I x →L[𝕜] 𝕜) v.proj
        ).continuousLinearMapAt 𝕜 v.proj (fiberHessian L v w)) := by
  have hn1 : 1 + 1 ≤ n := by simpa [one_add_one_eq_two] using hn
  set eC := trivializationAt (E →L[𝕜] 𝕜) (fun x ↦ TangentSpace I x →L[𝕜] 𝕜) v.proj
  have hxC : v.proj ∈ eC.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  let B : (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) := eC.continuousLinearMapAt 𝕜 v.proj
  -- The line through `v` in its fibre, in the direction `w`.
  let γ : 𝕜 → TangentBundle I M := fun r ↦ TotalSpace.mk' E v.proj (v.2 + r • w)
  have hγ : HasMFDerivAt 𝓘(𝕜) I.tangent γ 0 ((1 : 𝕜 →L[𝕜] 𝕜).smulRight
      ((0 : E), (trivializationAt E (TangentSpace I) v.proj).continuousLinearMapAt 𝕜 v.proj w)) :=
    TauCeti.Manifold.hasMFDerivAt_totalSpaceMk_add_smul (F := E) (V := TangentSpace I) v.proj v.2 w
  have hγ0 : γ 0 = v := by simp [γ]
  -- On the fibre through `v`, the Legendre map is the derivative `D` of the restricted
  -- Lagrangian, whose own derivative at `v` is the fibre Hessian.
  let D : E → E →L[𝕜] 𝕜 := fderiv 𝕜 (fun u : E ↦ L (TotalSpace.mk' E v.proj u))
  let Hs : E →L[𝕜] E →L[𝕜] 𝕜 := fiberHessian L v
  have hD : HasFDerivAt D Hs (id v.2 : E) :=
    (((contMDiff_iff_contDiff.1 (hL.comp (contMDiff_tangentBundle_mk_constBase contMDiff_id v.proj))
      ).fderiv_right (m := 1) hn1).differentiable one_ne_zero _).hasFDerivAt
  have hline : HasDerivAt (fun r : 𝕜 ↦ D (v.2 + r • w)) (Hs w) 0 := by
    have h1 : HasDerivAt (fun r : 𝕜 ↦ (id v.2 : E) + r • (id w : E)) (id w : E) 0 := by
      have h := ((hasDerivAt_id' (0 : 𝕜)).smul_const (id w : E)).const_add (id v.2 : E)
      rwa [one_smul] at h
    have h2 : HasFDerivAt D Hs ((id v.2 : E) + (0 : 𝕜) • (id w : E)) := by
      rwa [zero_smul, add_zero]
    -- Elaborating the chain rule against the goal would look for a norm on `T_x M`; build it on
    -- the model space `E` first, then match it with the goal through `T_x M = E`.
    have h := h2.comp_hasDerivAt (0 : 𝕜) h1
    exact h
  -- So the Legendre map sends the line to a line of covectors, with velocity `(0, B (Hs w))`.
  have hFLγ : HasMFDerivAt 𝓘(𝕜) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L ∘ γ) 0
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight ((0 : E), B (Hs w))) := by
    have hcoord : (fun r : 𝕜 ↦ (eC ((legendreMap L ∘ γ) r)).2) =
        fun r ↦ B (D (v.2 + r • w)) :=
      funext fun r ↦ (Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) eC hxC _).symm
    -- The base point of the line of covectors is `v.proj` by definition.
    have hproj : ((legendreMap L ∘ γ) 0).proj = v.proj := rfl
    rw [TauCeti.Manifold.hasMFDerivAt_totalSpace_curve_iff]
    refine ⟨(FiberBundle.continuousAt_totalSpace _ _).2 ⟨continuousAt_const, ?_⟩,
      hasDerivAt_const (0 : 𝕜) (extChartAt I v.proj v.proj), ?_⟩
    · rw [hproj, hcoord]
      exact B.continuous.continuousAt.comp hline.continuousAt
    · rw [hproj, hcoord]
      exact B.hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hline
  have hTγ : HasMFDerivAt I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L) (γ 0) T := by
    rw [hγ0, ← hT]
    exact ((contMDiff_legendreMap (m := 1) hL hn1 v).mdifferentiableAt one_ne_zero).hasMFDerivAt
  -- Both `T` composed with the velocity of the line and the velocity of the line of covectors
  -- are the derivative of `legendreMap L ∘ γ` at `0`.
  have hEq : T.comp ((1 : 𝕜 →L[𝕜] 𝕜).smulRight
        ((0 : E), (trivializationAt E (TangentSpace I) v.proj).continuousLinearMapAt 𝕜 v.proj w)) =
      (1 : 𝕜 →L[𝕜] 𝕜).smulRight ((0 : E), eC.continuousLinearMapAt 𝕜 v.proj (fiberHessian L v w)) :=
    (hTγ.comp 0 hγ).mfderiv.symm.trans hFLγ.mfderiv
  have h := DFunLike.congr_fun hEq 1
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul] using h

/-- **The differential of the Legendre map is invertible exactly where the fibre Hessian is.** In
bundle charts the differential of `FL` is block lower triangular, keeping the base coordinate and
acting on fibre coordinates by the fibre Hessian, up to the trivializations over `v.proj`. -/
theorem isInvertible_mfderiv_legendreMap_iff (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L)
    (hn : 2 ≤ n) (v : TangentBundle I M) :
    (mfderiv I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L) v).IsInvertible ↔
      (fiberHessian L v).IsInvertible := by
  -- Read the differential as a map between the model spaces of the charts.
  obtain ⟨T, hT⟩ : ∃ T : E × E →L[𝕜] E × (E →L[𝕜] 𝕜),
      mfderiv I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (legendreMap L) v = T := ⟨_, rfl⟩
  set eT := trivializationAt E (TangentSpace I) v.proj
  set eC := trivializationAt (E →L[𝕜] 𝕜) (fun x ↦ TangentSpace I x →L[𝕜] 𝕜) v.proj
  have hxT : v.proj ∈ eT.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hxC : v.proj ∈ eC.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  let A : E ≃L[𝕜] E := eT.continuousLinearEquivAt 𝕜 v.proj hxT
  let B : (E →L[𝕜] 𝕜) ≃L[𝕜] (E →L[𝕜] 𝕜) := eC.continuousLinearEquivAt 𝕜 v.proj hxC
  let Hs : E →L[𝕜] E →L[𝕜] 𝕜 := fiberHessian L v
  have hfst : ContinuousLinearMap.fst 𝕜 E (E →L[𝕜] 𝕜) ∘L T = ContinuousLinearMap.fst 𝕜 E E :=
    hT ▸ fst_comp_mfderiv_legendreMap hL hn v
  -- The diagonal block of `T` is the fibre Hessian, read in the trivializations over `v.proj`.
  have hblock : ContinuousLinearMap.snd 𝕜 E (E →L[𝕜] 𝕜) ∘L T ∘L ContinuousLinearMap.inr 𝕜 E E =
      (B : (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)) ∘L Hs ∘L (A.symm : E →L[𝕜] E) := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    have hA : A (A.symm w) = eT.continuousLinearMapAt 𝕜 v.proj (A.symm w) :=
      congrFun (eT.coe_continuousLinearEquivAt_eq hxT) _
    have hB : B (Hs (A.symm w)) = eC.continuousLinearMapAt 𝕜 v.proj (Hs (A.symm w)) :=
      congrFun (eC.coe_continuousLinearEquivAt_eq hxC) _
    have h := mfderiv_legendreMap_vertical hL hn v hT (A.symm w)
    rw [← hA, A.apply_symm_apply] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearEquiv.coe_coe, h, hB]
    -- `Hs` is the fibre Hessian, read as a bilinear form on the model space.
    rfl
  rw [hT]
  refine (ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq hfst).trans ?_
  rw [hblock, ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv]
  -- `Hs` is the fibre Hessian, read as a bilinear form on the model space.
  exact Iff.rfl

end Differential

section LocalDiffeomorph

variable {𝕜 E H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {L : TangentBundle I M → 𝕜} {m n : WithTop ℕ∞}
  [IsManifold I.tangent m (TangentBundle I M)]
  [IsManifold (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m (CotangentBundle I M)]

/-- **The Legendre map is a local diffeomorphism where the fibre Hessian is invertible.** For a
`C^n` Lagrangian with `m + 1 ≤ n` and `1 ≤ m`, the Legendre map is a `C^m` local diffeomorphism at
an interior tangent vector `v` exactly when the fibre Hessian at `v` is invertible. -/
theorem isLocalDiffeomorphAt_legendreMap_iff (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L)
    (hmn : m + 1 ≤ n) (hm : 1 ≤ m) {v : TangentBundle I M} (hv : I.tangent.IsInteriorPoint v) :
    IsLocalDiffeomorphAt I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m (legendreMap L) v ↔
      (fiberHessian L v).IsInvertible := by
  have h2m : (2 : WithTop ℕ∞) ≤ m + 1 := by
    rw [← one_add_one_eq_two]
    gcongr
  have hn : 2 ≤ n := h2m.trans hmn
  rw [← isInvertible_mfderiv_legendreMap_iff hL hn v]
  exact isLocalDiffeomorphAt_iff_exists_mfderiv_eq (contMDiff_legendreMap hL hmn).contMDiffOn
    isOpen_univ (mem_univ v) hv hm

/-- **The Legendre map is a local diffeomorphism exactly for regular Lagrangians.** On a
boundaryless manifold, the Legendre map of a `C^n` Lagrangian, `m + 1 ≤ n` and `1 ≤ m`, is a
`C^m` local diffeomorphism exactly when the Lagrangian is regular. -/
theorem isLocalDiffeomorph_legendreMap_iff [BoundarylessManifold I.tangent (TangentBundle I M)]
    (hL : ContMDiff I.tangent 𝓘(𝕜, 𝕜) n L) (hmn : m + 1 ≤ n) (hm : 1 ≤ m) :
    IsLocalDiffeomorph I.tangent (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m (legendreMap L) ↔
      IsRegularLagrangian L :=
  forall_congr' fun _ ↦
    isLocalDiffeomorphAt_legendreMap_iff hL hmn hm BoundarylessManifold.isInteriorPoint

end LocalDiffeomorph

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

/-- The Cartan one-form is the pullback of the Liouville form by the Legendre map. -/
theorem cartanForm_eq_mpullback {L : TangentBundle I M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    cartanForm L hL =
      SmoothForm.mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl)
        (CotangentBundle.liouvilleForm I M) :=
  (rfl)

/-- The Cartan one-form evaluates a tangent vector `ξ` of `TM` at `v` by applying the covector
`FL(v)` to the image of `ξ` under the derivative of the projection `π : TM → M`. -/
@[simp]
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

/-- Subtracting a potential, a function of the base point only, does not change the Cartan
one-form. -/
@[simp]
theorem cartanForm_sub_comp_proj {L : TangentBundle I M → ℝ} {V : M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hLV : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (fun v ↦ L v - V v.proj)) :
    cartanForm (fun v ↦ L v - V v.proj) hLV = cartanForm L hL := by
  simp only [cartanForm, legendreMap_sub_comp_proj]

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

/-- Subtracting a potential, a function of the base point only, does not change the Cartan
two-form. -/
@[simp]
theorem cartanTwoForm_sub_comp_proj {L : TangentBundle I M → ℝ} {V : M → ℝ}
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hLV : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (fun v ↦ L v - V v.proj)) :
    cartanTwoForm (fun v ↦ L v - V v.proj) hLV = cartanTwoForm L hL := by
  rw [cartanTwoForm_eq_neg_mextDerivₗ, cartanTwoForm_eq_neg_mextDerivₗ,
    cartanForm_sub_comp_proj hL hLV]

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

/-- **A mechanical Lagrangian is `C^n`** when its kinetic form `g`, as a section of the bundle
of bilinear forms on the tangent spaces, and its potential `V` are `C^n`. -/
theorem contMDiff_mechanicalLagrangian [IsManifold I 1 M] {n : WithTop ℕ∞}
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {V : M → ℝ}
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n (fun x ↦ TotalSpace.mk'
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] Trivial M ℝ x)
      (E →L[ℝ] E →L[ℝ] ℝ) x (g x)))
    (hV : ContMDiff I 𝓘(ℝ) n V) :
    ContMDiff I.tangent 𝓘(ℝ) n (mechanicalLagrangian g V) := by
  have hq : ContMDiff I.tangent (I.prod 𝓘(ℝ)) n (fun v : TangentBundle I M ↦
      TotalSpace.mk' ℝ (E := Trivial M ℝ) v.proj (g v.proj v.2 v.2)) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (hg.comp (contMDiff_proj _)) contMDiff_id
      contMDiff_id
  have hq' : ContMDiff I.tangent 𝓘(ℝ) n (fun v : TangentBundle I M ↦ g v.proj v.2 v.2) :=
    fun v ↦ (contMDiffAt_totalSpace.1 (hq v)).2
  have hhalf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n (fun t : ℝ ↦ 2⁻¹ * t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  rw [funext (mechanicalLagrangian_apply g V)]
  exact (hhalf.comp hq').sub (hV.comp (contMDiff_proj _))

/-- **The Legendre map of a mechanical Lagrangian** lowers the index with the kinetic form: for
symmetric `g` it sends `v` to the covector `g(v, ·)`. -/
theorem legendreMap_mechanicalLagrangian_snd
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) (V : M → ℝ) (v : TangentBundle I M) :
    (legendreMap (mechanicalLagrangian g V) v).2 = g v.proj v.2 := by
  rw [legendreMap_snd]
  simp only [mechanicalLagrangian_apply]
  -- `g v.proj` and `v.2` are read on the model space `E`.
  set B : E →L[ℝ] E →L[ℝ] ℝ := g v.proj
  set y : E := v.2
  refine (((B.hasFDerivAt_apply_self y).const_mul 2⁻¹).sub_const (V v.proj)).fderiv.trans ?_
  ext u
  -- Retype the right side on the model space too, so that both sides share their atoms.
  change _ = B y u
  have hB : B u y = B y u := hg v.proj u y
  simp [hB]
  ring

/-- **The energy of a mechanical Lagrangian** is the total energy `½ g(v, v) + V(x)`, kinetic plus
potential. -/
@[simp]
theorem lagrangianEnergy_mechanicalLagrangian
    (g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (V : M → ℝ)
    (v : TangentBundle I M) :
    lagrangianEnergy (mechanicalLagrangian g V) v = 2⁻¹ * g v.proj v.2 v.2 + V v.proj := by
  rw [lagrangianEnergy_apply, legendreMap_snd]
  simp only [mechanicalLagrangian_apply]
  -- `g v.proj` and `v.2` are read on the model space `E`.
  set B : E →L[ℝ] E →L[ℝ] ℝ := g v.proj
  set y : E := v.2
  have hd := (((B.hasFDerivAt_apply_self y).const_mul 2⁻¹).sub_const (V v.proj)).fderiv
  refine (congrArg (fun f : E →L[ℝ] ℝ ↦ f y - (2⁻¹ * B y y - V v.proj)) hd).trans ?_
  -- Retype the right side on the model space too, so that both sides share their atoms.
  change 2⁻¹ * (B y y + B y y) - (2⁻¹ * B y y - V v.proj) = 2⁻¹ * B y y + V v.proj
  ring

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

/-- **The fibre Hessian of a mechanical Lagrangian** is its kinetic form: for symmetric `g`, the
fibre Hessian at every tangent vector at `x` is `g x`. -/
theorem fiberHessian_mechanicalLagrangian
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) (V : M → ℝ) (v : TangentBundle I M) :
    fiberHessian (mechanicalLagrangian g V) v = g v.proj := by
  -- On the fibre `T_x M`, the Legendre map is the linear map `g x`.
  have h : (fun w : E ↦ ((legendreMap (mechanicalLagrangian g V)
      (TotalSpace.mk' E v.proj w)).2 : E →L[ℝ] ℝ)) = g v.proj :=
    funext fun w ↦ legendreMap_mechanicalLagrangian_snd hg V (TotalSpace.mk' E v.proj w)
  rw [fiberHessian_eq_fderiv_legendreMap, h]
  exact (g v.proj).fderiv

/-- **A mechanical Lagrangian is regular** exactly when its kinetic form is invertible: for
symmetric `g`, its fibre Hessians are invertible exactly when each `g x` is an isomorphism from
`T_x M` onto its continuous dual. In finite dimensions this is nondegeneracy of `g`. -/
theorem isRegularLagrangian_mechanicalLagrangian_iff
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) (V : M → ℝ) :
    IsRegularLagrangian (mechanicalLagrangian g V) ↔ ∀ x, (g x).IsInvertible := by
  simp only [isRegularLagrangian_iff, fiberHessian_mechanicalLagrangian hg]
  exact ⟨fun h x ↦ h (TotalSpace.mk' E x 0), fun h v ↦ h v.proj⟩

/-- **A mechanical Lagrangian with positive definite kinetic form is regular**, on a
finite-dimensional manifold. This covers the Lagrangian `½ |v|² - V(x)` of a Riemannian metric. -/
theorem isRegularLagrangian_mechanicalLagrangian [FiniteDimensional ℝ E]
    {g : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hg : ∀ x v w, g x v w = g x w v) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (V : M → ℝ) :
    IsRegularLagrangian (mechanicalLagrangian g V) :=
  (isRegularLagrangian_mechanicalLagrangian_iff hg V).2 fun x ↦
    ContinuousLinearMap.isInvertible_of_pos (E := E) (hpos x)

end Mechanical

end TauCeti
