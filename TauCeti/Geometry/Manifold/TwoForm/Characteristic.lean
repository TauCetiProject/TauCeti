/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Foliation.Flow
public import TauCeti.Geometry.Manifold.TwoForm.Kernel
public import TauCeti.Geometry.Symplectic.LinearReduction
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Kernel fields of a closed two-form and their flows

Let `σ` be a smooth two-form on a real manifold `M`. A vector field `V` is a *kernel field* of
`σ` when `V x` lies in the kernel `ker σ_x` of `σ_x` at every point, that is, when its contraction
`ι_V σ` vanishes (`TauCeti.SmoothForm.interior_eq_zero_iff_forall_mem_ker`). When `σ` is closed,
Cartan's formula `L_V σ = ι_V dσ + d (ι_V σ)` shows that `σ` is invariant along every
differentiable kernel field (`TauCeti.SmoothForm.mlieDerivForm_eq_zero_of_mem_ker`): this is the
infinitesimal form of the invariance of `σ` along the leaves of its characteristic foliation.

Integrating this along the maximal local flow `φ` of a `C¹` kernel field (`TauCeti.flowOf`), on a
finite-dimensional boundaryless manifold, gives, wherever `φₜ x` is defined:

* `φₜ` preserves `σ` at `x`: `(φₜ^* σ)ₓ = σₓ`
  (`TauCeti.SmoothForm.mpullback_flowOf_apply_of_mem_ker`), that is
  `σ (dφₜ v, dφₜ w) = σ (v, w)` (`TauCeti.SmoothForm.bilinFormAt_mfderiv_flowOf`). For a complete
  kernel field, `ψₜ^* σ = σ` at every time (`TauCeti.SmoothForm.mpullback_globalFlow_of_mem_ker`).
* `dφₜ` carries the kernel of `σ` at `x` onto the kernel at `φₜ x`
  (`TauCeti.SmoothForm.map_mfderiv_flowOf_ker`), since `dφₜ` is invertible
  (`TauCeti.bijective_mfderiv_flowOf`).
* `φₜ x` lies on the leaf through `x` of the characteristic foliation of `σ` when the kernels have
  constant dimension (`TauCeti.SmoothForm.flowOf_mem_leaf_characteristicFoliation`).
* `dφₜ` therefore induces a linear isomorphism of the *reduced tangent spaces*
  `T_x M ⧸ ker σ_x ≃ T_(φₜ x) M ⧸ ker σ_(φₜ x)`
  (`TauCeti.SmoothForm.quotKerFlowEquiv`), which is a linear symplectomorphism for the
  symplectic forms induced by `σ` on these quotients
  (`LinearMap.BilinForm.IsAlt.symplecticFormQuotKer`;
  `TauCeti.SmoothForm.isSymplectomorphism_quotKerFlowEquiv`).

So moving along a characteristic leaf by the flow of a kernel field identifies the quotient tangent
spaces `T M ⧸ ker σ` symplectically. For the pullback of a symplectic form to a coisotropic
submanifold, these quotients are the tangent spaces of the coisotropic reduction.

## References

* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114 (the characteristic foliation of a
  presymplectic form).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 14.35
  (Cartan's formula).
-/

public section

open Module
open scoped ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {σ : SmoothForm I M ℝ 2} {V : (x : M) → TangentSpace I x}

/-! ### Kernel fields and the Lie derivative -/

/-- The contraction `ι_V σ` of a two-form with a vector field vanishes exactly when `V` is a
kernel field of `σ`: `V x` lies in the kernel of `σ_x` at every point. -/
theorem interior_eq_zero_iff_forall_mem_ker :
    RoughForm.interior V σ.val = 0 ↔ ∀ x, V x ∈ LinearMap.ker (σ.bilinFormAt x) :=
  RoughForm.interior_eq_zero_iff.trans <| forall_congr' fun x ↦ by
    simp [LinearMap.ext_iff, bilinFormAt_apply, SmoothBundleForm.eval₂_apply]

/-- The exterior derivative of the contraction `ι_V σ` vanishes for a kernel field `V` of `σ`,
since the contraction itself vanishes. -/
theorem mextDeriv_interior_eq_zero_of_mem_ker
    (hVσ : ∀ x, V x ∈ LinearMap.ker (σ.bilinFormAt x)) :
    mextDeriv (RoughForm.interior V σ.val) = 0 := by
  rw [interior_eq_zero_iff_forall_mem_ker.mpr hVσ, mextDeriv_zero]

/-- **A closed two-form is invariant along its kernel fields.** For a closed two-form `σ` and a
differentiable vector field `V` with `V x ∈ ker σ_x` at every point, `L_V σ = 0`: by Cartan's
formula `L_V σ = ι_V dσ + d (ι_V σ)`, and both terms vanish. -/
theorem mlieDerivForm_eq_zero_of_mem_ker (hσ : σ.IsClosed)
    (hV : MDifferentiable I I.tangent (fun y ↦ (V y : TangentBundle I M)))
    (hVσ : ∀ x, V x ∈ LinearMap.ker (σ.bilinFormAt x)) :
    mlieDerivForm V σ.val = 0 := by
  rw [mlieDerivForm_eq_mextDeriv_interior hV hσ, mextDeriv_interior_eq_zero_of_mem_ker hVσ]

/-! ### Flows of kernel fields -/

section Flow

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I 2 M]
  (hσ : σ.IsClosed) (hV : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)))
  (hVσ : ∀ x, V x ∈ LinearMap.ker (σ.bilinFormAt x)) {t : ℝ} {x : M}
include hσ hV hVσ

/-- **Local flows of kernel fields preserve a closed two-form.** If `V` is a `C¹` kernel field of
a closed two-form `σ`, the time-`t` map of its maximal flow `φ` satisfies `(φₜ^* σ)ₓ = σₓ`
wherever `φₜ x` is defined. The field need not be complete. -/
theorem mpullback_flowOf_apply_of_mem_ker (ht : (t, x) ∈ flowDomain V) :
    TauCeti.mpullback I I (flowOf V t) σ.val x = σ.val x :=
  mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero hV hσ
    (mextDeriv_interior_eq_zero_of_mem_ker hVσ) ht

/-- The local flow `φ` of a `C¹` kernel field of a closed two-form `σ` preserves `σ` on tangent
vectors: `σ (dφₜ v, dφₜ w) = σ (v, w)` wherever `φₜ x` is defined. -/
theorem bilinFormAt_mfderiv_flowOf (ht : (t, x) ∈ flowDomain V) (v w : TangentSpace I x) :
    σ.bilinFormAt (flowOf V t x) (mfderiv I I (flowOf V t) x v) (mfderiv I I (flowOf V t) x w) =
      σ.bilinFormAt x v w := by
  have h := congr($(mpullback_flowOf_apply_of_mem_ker hσ hV hVσ ht) ![v, w])
  rw [mpullback_apply_pair] at h
  simpa only [bilinFormAt_apply, SmoothBundleForm.eval₂_apply] using h

/-- The differential of the local flow `φ` of a `C¹` kernel field of a closed two-form `σ` maps
a tangent vector at `x` into the kernel of `σ` at `φₜ x` exactly when the vector lies in the kernel
of `σ` at `x`. -/
theorem mfderiv_flowOf_mem_ker_iff (ht : (t, x) ∈ flowDomain V) {v : TangentSpace I x} :
    mfderiv I I (flowOf V t) x v ∈ LinearMap.ker (σ.bilinFormAt (flowOf V t x)) ↔
      v ∈ LinearMap.ker (σ.bilinFormAt x) := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    ext w
    rw [← bilinFormAt_mfderiv_flowOf hσ hV hVσ ht, h, LinearMap.zero_apply, LinearMap.zero_apply]
  · intro h
    ext u
    obtain ⟨w, rfl⟩ := (bijective_mfderiv_flowOf hV ht).2 u
    rw [bilinFormAt_mfderiv_flowOf hσ hV hVσ ht, h, LinearMap.zero_apply, LinearMap.zero_apply]

/-- **Local flows of kernel fields preserve the kernels.** The differential of the local flow `φ`
of a `C¹` kernel field of a closed two-form `σ` carries `ker σ_x` onto `ker σ_(φₜ x)`, wherever
`φₜ x` is defined. -/
theorem map_mfderiv_flowOf_ker (ht : (t, x) ∈ flowDomain V) :
    (LinearMap.ker (σ.bilinFormAt x)).map (mfderiv I I (flowOf V t) x).toLinearMap =
      LinearMap.ker (σ.bilinFormAt (flowOf V t x)) := by
  ext u
  obtain ⟨w, rfl⟩ := (bijective_mfderiv_flowOf hV ht).2 u
  rw [Submodule.mem_map, mfderiv_flowOf_mem_ker_iff hσ hV hVσ ht]
  exact ⟨fun ⟨w', hw', h⟩ ↦ (bijective_mfderiv_flowOf hV ht).1 h ▸ hw', fun hw ↦ ⟨w, hw, rfl⟩⟩

/-- The differential of the local flow `φ` of a `C¹` kernel field of a closed two-form `σ`,
descended to the **reduced tangent spaces**: the linear isomorphism
`T_x M ⧸ ker σ_x ≃ T_(φₜ x) M ⧸ ker σ_(φₜ x)`, `[v] ↦ [dφₜ v]`, defined wherever `φₜ x` is
defined. -/
noncomputable def quotKerFlowEquiv (ht : (t, x) ∈ flowDomain V) :
    (TangentSpace I x ⧸ LinearMap.ker (σ.bilinFormAt x)) ≃ₗ[ℝ]
      TangentSpace I (flowOf V t x) ⧸ LinearMap.ker (σ.bilinFormAt (flowOf V t x)) :=
  Submodule.Quotient.equiv _ _
    (LinearEquiv.ofBijective (mfderiv I I (flowOf V t) x).toLinearMap
      (bijective_mfderiv_flowOf hV ht))
    (map_mfderiv_flowOf_ker hσ hV hVσ ht)

/-- `quotKerFlowEquiv` sends the class of `v` to the class of `dφₜ v`. -/
@[simp]
theorem quotKerFlowEquiv_mk (ht : (t, x) ∈ flowDomain V) (v : TangentSpace I x) :
    quotKerFlowEquiv hσ hV hVσ ht (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (mfderiv I I (flowOf V t) x v) :=
  (rfl)

/-- The inverse of `quotKerFlowEquiv` sends the class of `u` to the class of `dφ₋ₜ u`. -/
@[simp]
theorem quotKerFlowEquiv_symm_mk (ht : (t, x) ∈ flowDomain V)
    (u : TangentSpace I (flowOf V t x)) :
    -- `dφ₋ₜ u` is a tangent vector at `flowOf V (-t) (flowOf V t x)`, which equals `x` but not
    -- definitionally; all tangent spaces are the model space, so its class is taken at `x`.
    (quotKerFlowEquiv hσ hV hVσ ht).symm (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (p := LinearMap.ker (σ.bilinFormAt x))
        (mfderiv I I (flowOf V (-t)) (flowOf V t x) u) :=
  -- The right side of `LinearEquiv.symm_apply_eq` is `quotKerFlowEquiv_mk` by definition.
  (LinearEquiv.symm_apply_eq _).2 <|
    congrArg Submodule.Quotient.mk (mfderiv_flowOf_mfderiv_flowOf_neg_apply hV ht u).symm

/-- **Kernel flows are symplectic on the reduced tangent spaces.** The isomorphism
`T_x M ⧸ ker σ_x ≃ T_(φₜ x) M ⧸ ker σ_(φₜ x)` induced by the local flow `φ` of a `C¹` kernel
field of a closed two-form `σ` is a linear symplectomorphism for the symplectic forms that `σ`
induces on these quotients. -/
theorem isSymplectomorphism_quotKerFlowEquiv (ht : (t, x) ∈ flowDomain V) :
    SymplecticForm.IsSymplectomorphism (σ.isAlt_bilinFormAt x).symplecticFormQuotKer
      (σ.isAlt_bilinFormAt (flowOf V t x)).symplecticFormQuotKer
      (quotKerFlowEquiv hσ hV hVσ ht) := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro v w
  induction v using Submodule.Quotient.induction_on with | H v =>
  induction w using Submodule.Quotient.induction_on with | H w =>
  rw [quotKerFlowEquiv_mk, quotKerFlowEquiv_mk,
    LinearMap.BilinForm.IsAlt.symplecticFormQuotKer_mk,
    LinearMap.BilinForm.IsAlt.symplecticFormQuotKer_mk, bilinFormAt_mfderiv_flowOf hσ hV hVσ ht]

omit [IsManifold I 2 M] in
/-- **Flows of kernel fields move along the characteristic leaves.** If the kernels of a closed
two-form `σ` all have dimension `k`, the local flow `φ` of a `C¹` kernel field of `σ` carries `x`
into the leaf through `x` of the characteristic foliation of `σ`, wherever `φₜ x` is defined. -/
theorem flowOf_mem_leaf_characteristicFoliation {n : ℕ∞ω} [ENat.LEInfty n]
    [IsManifold I (n + 1) M] {k : ℕ} (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k)
    (hn : 1 ≤ n) (ht : (t, x) ∈ flowDomain V) :
    flowOf V t x ∈ (σ.characteristicFoliation hσ hk hn).leaf x :=
  Foliation.flowOf_mem_leaf hV (fun y ↦ by simpa using hVσ y) ht

/-- **Flows of complete kernel fields preserve a closed two-form.** If `V` is a complete `C¹`
kernel field of a closed two-form `σ`, its flow `ψ` satisfies `ψₜ^* σ = σ` at every time `t`. -/
theorem mpullback_globalFlow_of_mem_ker (hc : IsCompleteVectorField V) (t : ℝ) :
    TauCeti.mpullback I I (globalFlow V hV hc t) σ.val = σ.val :=
  mpullback_globalFlow_of_mextDeriv_interior_eq_zero hc hV hσ
    (mextDeriv_interior_eq_zero_of_mem_ker hVσ) t

end Flow

end TauCeti.SmoothForm
