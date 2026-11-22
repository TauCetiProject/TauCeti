/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Tensoriality of smooth alternating bundle sections

Over a finite-dimensional Hausdorff smooth manifold and a finite-rank smooth real domain bundle
`W`, pointwise evaluation identifies smooth sections of `Alt^ι(W, V)` `C^∞(M, ℝ)`-linearly with
alternating `C^∞(M, ℝ)`-multilinear maps `Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] Γ(V)`
(`ContMDiffSection.alternatingEquiv`), and in the scalar case with
`Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] C^∞(M, ℝ)` (`ContMDiffSection.scalarAlternatingEquiv`).
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold Topology

namespace ContMDiffSection

section RealManifold
variable {E H M FW : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [NormedAddCommGroup FW] [NormedSpace ℝ FW] [FiniteDimensional ℝ FW]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [ContMDiffVectorBundle ∞ FW W I]

section Tensoriality
variable {FV : Type*} [NormedAddCommGroup FV] [NormedSpace ℝ FV] {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

private def liftSection (x : M) (w : W x) : Cₛ^∞⟮I; FW, W⟯ :=
  Classical.choose (evalLinearMap_surjective (I := I) (F := FW) ∞ (V := W) x w)

omit [FiniteDimensional ℝ FW] in
private lemma liftSection_apply (x : M) (w : W x) : liftSection (I := I) (FW := FW) x w x = w := by
  rw [liftSection]; simpa only [evalLinearMap_apply] using
    Classical.choose_spec (evalLinearMap_surjective (I := I) (F := FW) ∞ (V := W) x w)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private lemma fiberAlternatingMap_update {ι : Type*} [Finite ι] [instDec : DecidableEq ι]
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (x : M) (w : ι → W x) (i : ι) (t : Cₛ^∞⟮I; FW, W⟯) (u : W x) (ht : t x = u) :
    Φ (fun r ↦ liftSection x (Function.update w i u r)) x =
      Φ (Function.update (fun r ↦ liftSection x (w r)) i t) x := by
  let _ := Fintype.ofFinite ι; exact Φ.contMDiffSection_eval_congr x fun r ↦ by
    by_cases hr : r = i <;> simp [hr, liftSection_apply, ht]

section FixedIndex
variable {ι : Type*} [Fintype ι]

private def fiberAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) : W x [⋀^ι]→ₗ[ℝ] V x where
  toFun w := Φ (fun i ↦ liftSection x (w i)) x
  map_update_add' := fun {inst} w i u₁ u₂ ↦ by
    have hU := fiberAlternatingMap_update (instDec := inst) Φ x w i
    rw [hU (liftSection x u₁ + liftSection x u₂) (u₁ + u₂) (by simp [liftSection_apply]),
      hU (liftSection x u₁) u₁ (liftSection_apply x u₁),
      hU (liftSection x u₂) u₂ (liftSection_apply x u₂)]
    exact congr_arg (· x)
      (Φ.map_update_add (fun r ↦ liftSection x (w r)) i (liftSection x u₁) (liftSection x u₂))
  map_update_smul' := fun {inst} w i c u ↦ by
    have hU := fiberAlternatingMap_update (instDec := inst) Φ x w i
    rw [hU (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c • liftSection x u) (c • u) (by simp [liftSection_apply]),
      hU (liftSection x u) u (liftSection_apply x u)]
    simpa only [RingHom.id_apply, smul_apply, ContMDiffMap.algebraMap_apply,
      Algebra.algebraMap_self] using congr_arg (· x)
      (Φ.map_update_smul (fun r ↦ liftSection x (w r)) i (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c)
        (liftSection x u))
  map_eq_zero_of_eq' w i j hij hne := by
    classical
    let s : ι → Cₛ^∞⟮I; FW, W⟯ :=
      Function.update (fun r ↦ liftSection x (w r)) j (liftSection x (w i))
    rw [Φ.contMDiffSection_eval_congr x (s' := s) fun r ↦ by
      by_cases hr : r = j <;> simp [s, hr, hij, liftSection_apply]]
    exact congr_arg (· x) (Φ.map_eq_zero_of_eq s (by simp [s, hne]) hne)

private def fiberContinuousAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) : W x [⋀^ι]→L[ℝ] V x :=
  let eW := VectorBundle.continuousLinearEquivAt ℝ FW W x
  (AlternatingMap.toContinuousAlternatingMap
    ((fiberAlternatingMap Φ x).compLinearMap eW.symm.toLinearMap)).compContinuousLinearMap
      (eW : W x →L[ℝ] FW)

private lemma fiberContinuousAlternatingMap_apply
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) (w : ι → W x) :
    fiberContinuousAlternatingMap Φ x w = Φ (fun i ↦ liftSection x (w i)) x := by
  simp only [fiberContinuousAlternatingMap, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    AlternatingMap.coe_toContinuousAlternatingMap, AlternatingMap.compLinearMap_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe, fiberAlternatingMap,
    AlternatingMap.coe_mk, MultilinearMap.coe_mk]
  exact congr_arg (Φ · x) <| funext fun i ↦ congr_arg (liftSection x) <|
    (VectorBundle.continuousLinearEquivAt ℝ FW W x).symm_apply_apply (w i)

private lemma fiberContinuousAlternatingMap_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    fiberContinuousAlternatingMap Φ x (fun i ↦ s i x) = Φ s x :=
  (fiberContinuousAlternatingMap_apply Φ x _).trans <|
    Φ.contMDiffSection_eval_congr x fun i ↦ liftSection_apply x (s i x)

private lemma contMDiff_fiberContinuousAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^ι]→L[ℝ] FV)) ∞
      (fun y ↦ TotalSpace.mk' (FW [⋀^ι]→L[ℝ] FV)
        (E := fun z ↦ W z [⋀^ι]→L[ℝ] V z) y (fiberContinuousAlternatingMap Φ y)) := by
  intro x₀; rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.mpr fun v ↦ ?_⟩
  set eW := trivializationAt FW W x₀ with heW
  have hnhds : eW.baseSet ∈ 𝓝 x₀ :=
    eW.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt FW W x₀)
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hnhds).mem_iff.mp hnhds
  let s : ι → Cₛ^∞⟮I; FW, W⟯ := fun i ↦ ⟨(ρ : M → ℝ) • fun y ↦ eW.symm y (v i),
    ρ.contMDiff.contMDiffOn.smul_section_of_tsupport eW.open_baseSet hρ
      (TauCeti.Manifold.contMDiffOn_symm_baseSet (v i))⟩
  set eV := trivializationAt FV V x₀ with heV
  have hΦs : ContMDiffAt I 𝓘(ℝ, FV) ∞ (fun y ↦ (eV ⟨y, Φ s y⟩).2) x₀ :=
    (contMDiffAt_totalSpace_iff.mp ((Φ s).contMDiff x₀)).2
  refine hΦs.congr_of_eventuallyEq ?_
  filter_upwards [ρ.eventuallyEq_one, hnhds,
    eV.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt FV V x₀)] with y hρ1 hyW hyV
  have hs_eq : (fun i ↦ eW.symmL ℝ y (v i)) = fun i ↦ s i y :=
    funext fun i ↦ by simp [s, hρ1, Trivialization.symmL_apply _ hyW]
  rw [ContinuousAlternatingMap.inCoordinates]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, ← heW, ← heV,
    hs_eq, fiberContinuousAlternatingMap_apply_sections,
    eV.continuousLinearMapAt_apply_of_mem ℝ hyV]

/-- Smooth sections of `x ↦ W x [⋀^ι]→L[ℝ] V x` are `C^∞(M, ℝ)`-linearly equivalent to alternating
`C^∞(M, ℝ)`-multilinear maps `Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] Γ(V)`. -/
def alternatingEquiv :
    Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] FV, fun x ↦ W x [⋀^ι]→L[ℝ] V x⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) where
  toFun := toAlternatingMap
  invFun Φ := ⟨fiberContinuousAlternatingMap Φ, contMDiff_fiberContinuousAlternatingMap Φ⟩
  left_inv φ := by ext x w; simp [fiberContinuousAlternatingMap_apply, liftSection_apply]
  right_inv Φ := by ext s x; rw [toAlternatingMap_apply]; exact
    fiberContinuousAlternatingMap_apply_sections Φ s x
  map_add' _ _ := by ext s x; simp
  map_smul' _ _ := by ext s x; simp

@[simp] theorem alternatingEquiv_apply
    (φ : Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] FV, fun x ↦ W x [⋀^ι]→L[ℝ] V x⟯) (s : ι → Cₛ^∞⟮I; FW, W⟯)
    (x : M) : alternatingEquiv φ s x = φ x (fun i ↦ s i x) := by rw [alternatingEquiv]; simp
@[simp] theorem alternatingEquiv_symm_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (s : ι → Cₛ^∞⟮I; FW, W⟯)
    (x : M) : (alternatingEquiv.symm Φ) x (fun i ↦ s i x) = Φ s x := by
  rw [alternatingEquiv]; exact fiberContinuousAlternatingMap_apply_sections Φ s x
end FixedIndex

@[simp] theorem alternatingEquiv_interior {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (φ : Cₛ^∞⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] V x⟯) :
    alternatingEquiv (interior s φ) = (alternatingEquiv φ).curryLeft s :=
  toAlternatingMap_interior s φ
@[simp] theorem alternatingEquiv_symm_curryLeft {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) :
    alternatingEquiv.symm (Φ.curryLeft s) = interior s (alternatingEquiv.symm Φ) := by
  apply alternatingEquiv.injective; simp
end Tensoriality

section ScalarTensoriality
/-- Scalar-valued smooth alternating bundle sections on `W` are `C^∞(M, ℝ)`-linearly equivalent to
`Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] C^∞(M, ℝ)`. -/
def scalarAlternatingEquiv {ι : Type*} [Fintype ι] :
    Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] ℝ, fun x ↦ W x [⋀^ι]→L[ℝ] ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (alternatingEquiv (FV := ℝ) (V := Bundle.Trivial M ℝ)).trans trivialEquiv.alternatingMapCongrRight

@[simp] theorem scalarAlternatingEquiv_apply {ι : Type*} [Fintype ι]
    (φ : Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] ℝ, fun x ↦ W x [⋀^ι]→L[ℝ] ℝ⟯) (s : ι → Cₛ^∞⟮I; FW, W⟯)
    (x : M) : scalarAlternatingEquiv φ s x = φ x (fun i ↦ s i x) := by
  rw [scalarAlternatingEquiv]; simp
@[simp] theorem scalarAlternatingEquiv_symm_apply_sections {ι : Type*} [Fintype ι]
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) (s : ι → Cₛ^∞⟮I; FW, W⟯)
    (x : M) : (scalarAlternatingEquiv.symm Φ) x (fun i ↦ s i x) = Φ s x := by
  rw [scalarAlternatingEquiv]; simp

@[simp] theorem scalarAlternatingEquiv_interior {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (φ : Cₛ^∞⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯) :
    scalarAlternatingEquiv (interior s φ) = (scalarAlternatingEquiv φ).curryLeft s := by
  simp only [scalarAlternatingEquiv, LinearEquiv.trans_apply, alternatingEquiv_interior]
  ext t x; simp
@[simp] theorem scalarAlternatingEquiv_symm_curryLeft {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    scalarAlternatingEquiv.symm (Φ.curryLeft s) = interior s (scalarAlternatingEquiv.symm Φ) := by
  apply scalarAlternatingEquiv.injective; simp
end ScalarTensoriality
end RealManifold

end ContMDiffSection
