/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Vector structures on associated bundles

A continuous linear action on a finite-dimensional normed space makes the existing associated
bundle into a native `VectorBundle`, with its original topology and atlas. A point of the
principal fibre identifies the model vector space linearly with the associated fibre; changing
that point acts by the given representation, with the convention `[p g, v] = [p, g v]`.

Structure on the model that is compatible with the representation therefore descends to the
fibers: an equivariant alternating map `η` induces `TauCeti.AssociatedBundle.alternatingMap`, which
reads `[p, v i] ↦ [p, η v]` in every frame `p` (`TauCeti.AssociatedBundle.alternatingMap_mk`), and
an invariant sesquilinear form `f` induces `TauCeti.AssociatedBundle.sesqForm`, which reads
`[p, v], [p, w] ↦ f v w` in every frame (`TauCeti.AssociatedBundle.sesqForm_mk`).
A nonzero alternating form of top degree with values in a line induces an isomorphism from the
top exterior power of each fiber onto the fiber of the associated line
(`TauCeti.AssociatedBundle.alternatingMapLinearEquiv_bijective`). Symmetry, positivity and
definiteness of an invariant form descend to the induced form
(`TauCeti.AssociatedBundle.isSymm_sesqForm`, `TauCeti.AssociatedBundle.re_sesqForm_self_nonneg`,
`TauCeti.AssociatedBundle.sesqForm_self_eq_zero`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

noncomputable section

open Bundle MulOpposite Set

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]

-- `AssociatedBundle G P F b` is the core's fibre, a type synonym of `F`.
-- These instances deliberately reuse the model's addition, zero and scalar multiplication.
instance instAddCommGroup (b : B) : AddCommGroup (AssociatedBundle G P F b) :=
  inferInstanceAs (AddCommGroup F)

instance instModule (b : B) : Module 𝕜 (AssociatedBundle G P F b) :=
  inferInstanceAs (Module 𝕜 F)

/-- Associated-bundle charts are linear when the structure-group action is linear. -/
instance localTriv_isLinear (b : B) :
    ((associatedBundleCore G P F).localTriv b).IsLinear 𝕜 where
  linear x hx := by
    refine ⟨?_, ?_⟩
    · intro v w
      simp only [FiberBundleCore.localTriv_apply]
      rw [associatedBundleCore_coordChange (F := F) _ _ x (v + w),
        associatedBundleCore_coordChange (F := F) _ _ x v,
        associatedBundleCore_coordChange (F := F) _ _ x w]
      exact smul_add _ _ _
    · intro r v
      simp only [FiberBundleCore.localTriv_apply]
      rw [associatedBundleCore_coordChange (F := F) _ _ x (r • v),
        associatedBundleCore_coordChange (F := F) _ _ x v]
      -- The fibre module is the model module. Specify `F` to select the given
      -- commuting group action on the model rather than on the fibre synonym.
      exact @SMulCommClass.smul_comm G 𝕜 F _ _ ‹SMulCommClass G 𝕜 F› _ r v

/-- A linear action in finite dimension upgrades the associated fibre bundle to a vector
bundle without changing its topology or its chosen trivializations. -/
instance instVectorBundle [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    VectorBundle 𝕜 F (AssociatedBundle G P F) where
  trivialization_linear' e he := by
    obtain ⟨b, rfl⟩ := he
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨b, rfl⟩ := he
    obtain ⟨b', rfl⟩ := he'
    let e := (associatedBundleCore G P F).localTriv b
    let e' := (associatedBundleCore G P F).localTriv b'
    apply continuousOn_clm_apply.mpr
    intro v
    refine ((e.continuousOn_coordChange e').comp
      (continuousOn_id.prodMk (continuousOn_const (c := v)))
      (fun _ hx ↦ ⟨hx, mem_univ _⟩)).congr fun b hb ↦ ?_
    exact e.coordChangeL_apply' e' hb v

/-- Classes in a fixed principal frame respect addition. -/
@[simp]
theorem mk_add {b : B} (p : P b) (v w : F) :
    mk G p (v + w) = mk G p v + mk G p w := by
  simp only [mk_def, smul_add]
  -- The remaining equality identifies the fibre addition with the model addition,
  -- as specified by `instAddCommGroup`.
  rfl

variable (𝕜 G) in
/-- Each principal frame identifies the model with the associated fibre by a continuous
linear equivalence. This uses the existing associated-bundle class map. -/
def mkContinuousLinearEquiv {b : B} (p : P b) :
    F ≃L[𝕜] AssociatedBundle G P F b where
  toFun := mk G p
  -- Associated fibres have the model's topology and linear structure by construction.
  invFun x := @HSMul.hSMul G F F _ (trivializationAt G P b ⟨b, p⟩).2⁻¹ x
  left_inv v := by rw [mk_def]; exact inv_smul_smul _ v
  right_inv x := by
    rw [mk_def]
    -- View `x` in the model `F`, of which the fibre is a type synonym.
    exact @smul_inv_smul G F _ _ _ x
  map_add' := mk_add p
  map_smul' r v := by
    simp only [mk_def]
    -- The fibre scalar multiplication is the model's by `instModule`; specify `F`
    -- so instance search uses the given commuting action on the model.
    exact @SMulCommClass.smul_comm G 𝕜 F _ _ ‹SMulCommClass G 𝕜 F› _ r v
  continuous_toFun := by
    have h := continuous_const_smul (T := F) (trivializationAt G P b ⟨b, p⟩).2
    exact h.congr fun v ↦ (mk_def p v).symm
  continuous_invFun := continuous_const_smul (T := F) _

/-- The frame identification is the quotient class map. -/
@[simp]
theorem mkContinuousLinearEquiv_apply {b : B} (p : P b) (v : F) :
    mkContinuousLinearEquiv 𝕜 G p v = mk G p v := (rfl)

/-- Classes in a fixed principal frame respect scalar multiplication. -/
@[simp]
theorem mk_smul_scalar {b : B} (p : P b) (r : 𝕜) (v : F) :
    mk G p (r • v) = r • mk G p v :=
  by simpa only [mkContinuousLinearEquiv_apply] using
    (mkContinuousLinearEquiv 𝕜 G p).map_smul r v

/-- The zero class is independent of the principal frame. -/
@[simp]
theorem mk_zero {b : B} (p : P b) : mk G p (0 : F) = 0 := by
  simp only [mk_def, smul_zero]
  -- `instAddCommGroup` uses the model zero as the fibre zero.
  rfl

/-- Changing a principal frame transforms the vector coordinate by the division element. -/
@[simp]
theorem mkContinuousLinearEquiv_symm_apply_mk {b : B} (p q : P b) (v : F) :
    (mkContinuousLinearEquiv 𝕜 G p).symm (mk G q v) =
      PrincipalBundle.division G p q • v := by
  apply (mkContinuousLinearEquiv 𝕜 G p).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, mkContinuousLinearEquiv_apply]
  exact ((mk_eq_mk_iff (p := p) (q := q)).mpr rfl).symm

/-- In a local associated chart the linear transition acts by the principal transition. -/
theorem coordChangeL_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {i j b : B} (hb : b ∈ (trivializationAt G P i).baseSet ∩
      (trivializationAt G P j).baseSet) (v : F) :
    (trivializationAt F (AssociatedBundle G P F) i).coordChangeL 𝕜
      (trivializationAt F (AssociatedBundle G P F) j) b v =
        (trivializationAt G P i).coordChange (trivializationAt G P j) b 1 • v := by
  rw [Trivialization.coordChangeL_apply']
  · rw [trivializationAt_eq_localTriv, trivializationAt_eq_localTriv]
    simp only [FiberBundleCore.localTriv_symm_apply, FiberBundleCore.localTriv_apply]
    rw [FiberBundleCore.coordChange_comp, associatedBundleCore_coordChange]
    simp only [FiberBundleCore.baseSet_at, associatedBundleCore_localTriv_baseSet,
      associatedBundleCore_indexAt]
    exact ⟨⟨hb.1, mem_baseSet_trivializationAt G P b⟩, hb.2⟩
  · simpa only [baseSet_trivializationAt] using hb

/-! ### Descent of structure on the model -/

variable (G P) in
/-- The point of the principal fiber over `b` with coordinate `1` in the chart at `b`, used to
read structure on the model in the fibers. -/
private def refPoint (b : B) : P b := (FiberBundle.homeomorphAt G P b).symm 1

variable (𝕜 G P F) in
/-- The associated fibers have the dimension of the model. -/
theorem finrank_eq (b : B) : Module.finrank 𝕜 (AssociatedBundle G P F b) = Module.finrank 𝕜 F :=
  (mkContinuousLinearEquiv 𝕜 G (F := F) (refPoint G P b)).toLinearEquiv.finrank_eq.symm

/-- The associated fibers of a finite-dimensional model are finite-dimensional. -/
instance instFiniteDimensional [FiniteDimensional 𝕜 F] (b : B) :
    FiniteDimensional 𝕜 (AssociatedBundle G P F b) :=
  (mkContinuousLinearEquiv 𝕜 G (F := F) (refPoint G P b)).toLinearEquiv.finiteDimensional

section AlternatingMap

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [DistribMulAction G F'] [SMulCommClass G 𝕜 F'] [ContinuousSMul G F'] {ι : Type*}

variable (G P) in
/-- The alternating map on the fibers over `b` induced by an alternating map `η` on the model,
read through a fixed reference point of the principal fiber over `b`. When `η` is equivariant it
reads `[p, v i] ↦ [p, η v]` in every frame `p` (`TauCeti.AssociatedBundle.alternatingMap_mk`), so it
does not depend on that choice. -/
def alternatingMap (η : F [⋀^ι]→ₗ[𝕜] F') (b : B) :
    AssociatedBundle G P F b [⋀^ι]→ₗ[𝕜] AssociatedBundle G P F' b :=
  ((mkContinuousLinearEquiv 𝕜 G (F := F') (refPoint G P b)).toLinearEquiv :
      F' →ₗ[𝕜] AssociatedBundle G P F' b).compAlternatingMap
    (η.compLinearMap ((mkContinuousLinearEquiv 𝕜 G (F := F) (refPoint G P b)).symm.toLinearEquiv :
      AssociatedBundle G P F b →ₗ[𝕜] F))

/-- **An equivariant alternating map in a frame.** If `η (g • v) = g • η v`, then in every
frame `p` the induced alternating map sends the classes `[p, v i]` to `[p, η v]`. -/
@[simp]
theorem alternatingMap_mk {η : F [⋀^ι]→ₗ[𝕜] F'}
    (hη : ∀ (g : G) (v : ι → F), η (fun i ↦ g • v i) = g • η v) {b : B} (p : P b)
    (v : ι → F) :
    alternatingMap G P η b (fun i ↦ mk G p (v i)) = mk G p (η v) := by
  simp only [alternatingMap, LinearMap.compAlternatingMap_apply,
    AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    mkContinuousLinearEquiv_symm_apply_mk, hη, mkContinuousLinearEquiv_apply]
  rw [← mk_smul, PrincipalBundle.smul_division]

/-- The induced alternating map vanishes only when the model alternating map does. -/
@[simp]
theorem alternatingMap_eq_zero_iff {η : F [⋀^ι]→ₗ[𝕜] F'} (b : B) :
    alternatingMap G P η b = 0 ↔ η = 0 := by
  refine ⟨fun h ↦ AlternatingMap.ext fun v ↦ ?_, fun h ↦ by simp [h, alternatingMap]⟩
  have hv := congrArg (fun η' ↦ η' fun i ↦ mk G (refPoint G P b) (v i)) h
  simp only [alternatingMap, LinearMap.compAlternatingMap_apply,
    AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv,
    mkContinuousLinearEquiv_symm_apply_mk, PrincipalBundle.division_self, one_smul,
    zero_apply, map_eq_zero_iff _ (ContinuousLinearEquiv.injective _)] at hv
  exact hv

/-- **The top exterior power of the fibers.** If the model `F` has dimension `n` and `F'` is a
line, a nonzero alternating `n`-form `η` on the model induces a bijection from `⋀ⁿ` of the fiber
of `P ×_G F` over `b` onto the fiber of `P ×_G F'`. -/
theorem alternatingMapLinearEquiv_bijective [FiniteDimensional 𝕜 F] {n : ℕ}
    (hF : Module.finrank 𝕜 F = n) (hF' : Module.finrank 𝕜 F' = 1)
    {η : F [⋀^Fin n]→ₗ[𝕜] F'} (hη : η ≠ 0) (b : B) :
    Function.Bijective (exteriorPower.alternatingMapLinearEquiv (alternatingMap G P η b)) := by
  set f := exteriorPower.alternatingMapLinearEquiv (alternatingMap G P η b)
  have hdom : Module.finrank 𝕜 (⋀[𝕜]^n (AssociatedBundle G P F b)) = 1 := by
    rw [exteriorPower.finrank_eq, finrank_eq, hF, Nat.choose_self]
  have hcod : Module.finrank 𝕜 (AssociatedBundle G P F' b) = 1 :=
    (finrank_eq 𝕜 G F' P b).trans hF'
  have : FiniteDimensional 𝕜 F' := Module.finite_of_finrank_eq_succ hF'
  have : FiniteDimensional 𝕜 (⋀[𝕜]^n (AssociatedBundle G P F b)) :=
    Module.finite_of_finrank_eq_succ hdom
  -- `f` is nonzero, since it restricts to the induced alternating map on decomposable vectors.
  have hf : f ≠ 0 := by
    intro h0
    apply (alternatingMap_eq_zero_iff (G := G) (P := P) b).not.2 hη
    ext v
    simpa [f] using congrArg (fun g ↦ g (exteriorPower.ιMulti 𝕜 n v)) h0
  have hsurj : Function.Surjective f := surjective_of_ne_zero_of_finrank_eq_one hcod hf
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdom.trans hcod.symm)).2 hsurj, hsurj⟩

end AlternatingMap

section SesqForm

variable {σ : 𝕜 →+* 𝕜}

variable (G P) in
/-- The sesquilinear form on the fiber over `b` induced by a sesquilinear form `f` on the model,
read through a fixed reference point of the principal fiber over `b`. When `f` is invariant it
reads `[p, v], [p, w] ↦ f v w` in every frame `p` (`TauCeti.AssociatedBundle.sesqForm_mk`), so it
does not depend on that choice. -/
def sesqForm (f : F →ₛₗ[σ] F →ₗ[𝕜] 𝕜) (b : B) :
    AssociatedBundle G P F b →ₛₗ[σ] AssociatedBundle G P F b →ₗ[𝕜] 𝕜 :=
  (f.comp ((mkContinuousLinearEquiv 𝕜 G (F := F) (refPoint G P b)).symm.toLinearEquiv :
      AssociatedBundle G P F b →ₗ[𝕜] F)).compl₂
    ((mkContinuousLinearEquiv 𝕜 G (F := F) (refPoint G P b)).symm.toLinearEquiv :
      AssociatedBundle G P F b →ₗ[𝕜] F)

/-- **An invariant sesquilinear form in a frame.** If `f (g • v) (g • w) = f v w`, then in every
frame `p` the induced form of the classes `[p, v]` and `[p, w]` is `f v w`. -/
@[simp]
theorem sesqForm_mk {f : F →ₛₗ[σ] F →ₗ[𝕜] 𝕜} (hf : ∀ (g : G) (v w : F), f (g • v) (g • w) = f v w)
    {b : B} (p : P b) (v w : F) :
    sesqForm G P f b (mk G p v) (mk G p w) = f v w := by
  simp only [sesqForm, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, mkContinuousLinearEquiv_symm_apply_mk, hf]

/-- The form induced by an invariant symmetric sesquilinear form is symmetric. -/
theorem isSymm_sesqForm {f : F →ₛₗ[σ] F →ₗ[𝕜] 𝕜}
    (hf : ∀ (g : G) (v w : F), f (g • v) (g • w) = f v w) (hfs : f.IsSymm) (b : B) :
    (sesqForm G P f b).IsSymm := by
  refine ⟨fun v w ↦ ?_⟩
  obtain ⟨p, v, w, rfl, rfl⟩ := exists_mk_mk v w
  simp only [sesqForm_mk hf, hfs.eq]

/-- The form induced by an invariant definite sesquilinear form is definite. -/
theorem sesqForm_self_eq_zero {f : F →ₛₗ[σ] F →ₗ[𝕜] 𝕜}
    (hf : ∀ (g : G) (v w : F), f (g • v) (g • w) = f v w) (hf₀ : ∀ v, f v v = 0 → v = 0) {b : B}
    {w : AssociatedBundle G P F b} :
    sesqForm G P f b w w = 0 ↔ w = 0 := by
  obtain ⟨p, v, rfl⟩ := exists_mk w
  rw [sesqForm_mk hf, ← mk_zero (G := G) p, (mk_bijective (G := G) p).1.eq_iff]
  exact ⟨hf₀ v, fun h ↦ by simp [h]⟩

end SesqForm

end TauCeti.AssociatedBundle

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F : Type*} [RCLike 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]

/-- The form induced by an invariant positive semidefinite sesquilinear form is positive
semidefinite. -/
theorem re_sesqForm_self_nonneg {f : F →ₗ⋆[𝕜] F →ₗ[𝕜] 𝕜}
    (hf : ∀ (g : G) (v w : F), f (g • v) (g • w) = f v w) (hf₀ : ∀ v, 0 ≤ RCLike.re (f v v))
    {b : B} (w : AssociatedBundle G P F b) :
    0 ≤ RCLike.re (sesqForm G P f b w w) := by
  obtain ⟨p, v, rfl⟩ := exists_mk w
  rw [sesqForm_mk hf]
  exact hf₀ v

end TauCeti.AssociatedBundle
