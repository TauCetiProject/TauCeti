/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DeRham.CompactlySupportedMayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing

import Mathlib.Algebra.FiveLemma
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.DeRham.DisjointUnion
import TauCeti.Geometry.Manifold.DeRham.Euclidean
import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DeRham.OrientationCover
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Topology.MayerVietoris

/-!
# De Rham Poincaré duality

On an oriented boundaryless Hausdorff σ-compact finite-dimensional smooth manifold `M` of dimension
`k + l`, with no compactness hypothesis, `TauCeti.poincarePairing` induces a linear isomorphism
`H^k_dR(M) ≃ₗ[ℝ] Module.Dual ℝ (H^l_c(M))` (`TauCeti.bijective_poincarePairing`,
`TauCeti.poincareDuality`), proved by `TauCeti.mayerVietoris_induction` from Euclidean open boxes,
Mayer–Vietoris connecting maps (`TauCeti.poincarePairing_mayerVietorisδ`), and disjoint open unions
(`TauCeti.bijective_poincarePairing_iSup`). Corollaries include nondegeneracy, finite-dimensionality
on compact manifolds (including nonorientable ones via `Manifold.OrientationCover`), Betti-number
symmetry (`TauCeti.finrank_deRhamCohomology_eq_of_orientation`), and evaluations on `S¹` and `ℝ`.

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 and Problems 18-6 to 18-8.
* Raoul Bott and Loring W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Chapter I, §5.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

section Helpers

private theorem exact_dualMap {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃] {f : V₁ →ₗ[K] V₂} {g : V₂ →ₗ[K] V₃}
    (h : Exact f g) : Exact g.dualMap f.dualMap := by
  rwa [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, Subspace.dualAnnihilator_inj, eq_comm,
    ← LinearMap.exact_iff]

private theorem bijective_neg_one_pow_smul {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (m : ℕ) {f : V →ₗ[ℝ] W} (hf : Bijective f) :
    Bijective (((-1 : ℝ) ^ m • f : V →ₗ[ℝ] W)) := by
  have hsq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  refine ⟨fun x y hxy ↦ hf.1 ?_, fun w ↦ ⟨(hf.2 ((-1 : ℝ) ^ m • w)).choose, ?_⟩⟩
  · simpa only [LinearMap.smul_apply, smul_smul, hsq, one_smul] using
      congrArg (((-1 : ℝ) ^ m) • ·) hxy
  · rw [LinearMap.smul_apply, (hf.2 ((-1 : ℝ) ^ m • w)).choose_spec, smul_smul, hsq, one_smul]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

private theorem orientation_reindex_refl {ι : Type*} [Fintype ι]
    (o : Manifold.Orientation I M ι) : o.reindex (Equiv.refl ι) = o := by
  ext x; rw [Manifold.Orientation.orientationAt_reindex, _root_.Orientation.reindex_refl]; rfl

private theorem orientation_reindex_finCongr {m n p : ℕ} (h₁ : m = n) (h₂ : n = p)
    (o : Manifold.Orientation I M (Fin m)) :
    (o.reindex (finCongr h₁)).reindex (finCongr h₂) = o.reindex (finCongr (h₁.trans h₂)) := by
  subst h₁ h₂; rw [finCongr_refl, orientation_reindex_refl]

private theorem orientation_restrict_finCongr {m n : ℕ} (h : m = n)
    (o : Manifold.Orientation I M (Fin m)) (U : Opens M) :
    (o.restrict U).reindex (finCongr h) = (o.reindex (finCongr h)).restrict U := by
  subst h; rw [finCongr_refl, orientation_reindex_refl, orientation_reindex_refl]

end Helpers

section MayerVietorisStokes

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]

omit [BoundarylessManifold I M] in
private def integralWedgeCompactlySupported {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) :
    SmoothForm I M ℝ a →ₗ[ℝ] compactlySupportedForms I M b →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun φ η ↦ integralTopForm o (SmoothForm.wedge φ η.1).1)
    (fun φ φ' η ↦ by
      rw [LinearMap.map_add₂, Submodule.coe_add]
      exact integralTopForm_add o ((SmoothForm.wedge φ η.1).isSmoothForm.of_le (by simp))
        ((SmoothForm.wedge φ' η.1).isSmoothForm.of_le (by simp))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ η.2))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ' η.2)))
    (fun c φ η ↦ by rw [LinearMap.map_smul₂, Submodule.coe_smul]; exact integralTopForm_smul o c _)
    (fun φ η η' ↦ by
      rw [Submodule.coe_add, map_add, Submodule.coe_add]
      exact integralTopForm_add o ((SmoothForm.wedge φ η.1).isSmoothForm.of_le (by simp))
        ((SmoothForm.wedge φ η'.1).isSmoothForm.of_le (by simp))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ η.2))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ η'.2)))
    (fun c φ η ↦ by
      rw [Submodule.coe_smul, map_smul, Submodule.coe_smul]; exact integralTopForm_smul o c _)

omit [BoundarylessManifold I M] [T2Space M] in
private theorem integralWedgeCompactlySupported_apply {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) (φ : SmoothForm I M ℝ a)
    (η : compactlySupportedForms I M b) :
    integralWedgeCompactlySupported o φ η = integralTopForm o (RoughForm.wedge φ.1 η.1.1) := by
  rw [integralWedgeCompactlySupported, LinearMap.mk₂_apply, SmoothForm.coe_wedge]

omit [BoundarylessManifold I M] [T2Space M] in
private theorem integralWedgeCompactlySupported_neg {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) (φ : SmoothForm I M ℝ a)
    (η : compactlySupportedForms I M b) :
    integralWedgeCompactlySupported o φ (-η) = -integralWedgeCompactlySupported o φ η := by
  have h : -η = (-1 : ℝ) • η := Subtype.ext <| Subtype.ext <| by
    rw [Submodule.coe_neg, Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_smul,
      neg_smul, one_smul]
  rw [h, (integralWedgeCompactlySupported o φ).map_smul, smul_eq_mul, neg_one_mul]

omit [BoundarylessManifold I M] [T2Space M] in
private theorem integralWedgeCompactlySupported_sub {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) (φ₁ φ₂ : SmoothForm I M ℝ a)
    (η : compactlySupportedForms I M b) :
    integralWedgeCompactlySupported o (φ₁ - φ₂) η =
      integralWedgeCompactlySupported o φ₁ η - integralWedgeCompactlySupported o φ₂ η := by
  have h : φ₁ - φ₂ = φ₁ + (-1 : ℝ) • φ₂ := Subtype.ext <| by
    rw [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, sub_eq_add_neg, neg_smul,
      one_smul]
  rw [h, LinearMap.map_add₂, LinearMap.map_smul₂, smul_eq_mul, neg_one_mul, ← sub_eq_add_neg]

omit [BoundarylessManifold I M] in
private theorem integralWedgeCompactlySupported_extendByZero {U W : Opens M} {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) (h : U ≤ W)
    (φ : SmoothForm I W ℝ a) (η : compactlySupportedForms I U b) :
    integralWedgeCompactlySupported (o.restrict W) φ (compactlySupportedForms.extendByZero h b η) =
      integralWedgeCompactlySupported (o.restrict U)
        (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ) η := by
  let φU := SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ
  rw [integralWedgeCompactlySupported_apply, integralWedgeCompactlySupported_apply]
  have hwedge : RoughForm.wedge φ.1 (compactlySupportedForms.extendByZero h b η).1.1 =
      RoughForm.extendByZero W (RoughForm.wedge φU.1 η.1.1) := funext fun z ↦ by
    by_cases hz : (z : M) ∈ U
    · obtain ⟨u, rfl⟩ : ∃ u : U, Opens.inclusion h u = z := ⟨⟨z, hz⟩, rfl⟩
      rw [RoughForm.extendByZero_inclusion, SmoothForm.coe_mpullback,
        ← mpullback_inclusion_apply h (RoughForm.wedge φ.1 _), mpullback_wedge,
        compactlySupportedForms.coe_extendByZero, RoughForm.mpullback_inclusion_extendByZero]
    · rw [RoughForm.extendByZero_apply_of_notMem _ hz, RoughForm.wedge_def,
        RoughForm.wedgeWith_apply', compactlySupportedForms.coe_extendByZero,
        RoughForm.extendByZero_apply_of_notMem _ hz,
        ContinuousAlternatingMap.pairedWedge_zero_right]
  rw [hwedge]
  exact integralTopForm_extendByZero o h <| SmoothForm.coe_wedge φU η.1 ▸
    (mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φU η.2)

private theorem integralWedgeCompactlySupported_mextDeriv [SigmaCompactSpace M] {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (α : SmoothForm I M ℝ j) (γ : compactlySupportedForms I M l) :
    integralWedgeCompactlySupported o (mextDerivₗ I j α) γ = (-1 : ℝ) ^ (j + 1) *
      integralWedgeCompactlySupported (o.reindex (finCongr hjl)) α
        (compactlySupportedForms.mextDerivₗ I M l γ) := by
  rw [integralWedgeCompactlySupported_apply, integralWedgeCompactlySupported_apply]
  have h₁ : (j + 1) + l = j + l + 1 := by omega
  have h₂ : j + (l + 1) = j + l + 1 := rfl
  let o₁ : Manifold.Orientation I M (Fin (j + l + 1)) := o.reindex (finCongr h₁)
  let t₁ : SmoothForm I M ℝ (j + l + 1) :=
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h₁
      (SmoothForm.wedge (mextDerivₗ I j α) γ.1)
  let t₂ : SmoothForm I M ℝ (j + l + 1) :=
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h₂
      (SmoothForm.wedge α (compactlySupportedForms.mextDerivₗ I M l γ).1)
  have ht₁_mem : t₁ ∈ compactlySupportedForms I M (j + l + 1) := by
    dsimp only [t₁]; generalize hq : j + l + 1 = q at h₁; subst h₁
    exact SmoothForm.wedge_mem_compactlySupportedForms _ γ.2
  have ht₂_eq : t₂ = SmoothForm.wedge α (compactlySupportedForms.mextDerivₗ I M l γ).1 :=
    Subtype.ext <| funext fun _ ↦ ContinuousAlternatingMap.ext fun _ ↦ by
      dsimp only [t₂]; rw [SmoothForm.cast_apply]; rfl
  have ht₂_mem : (-1 : ℝ) ^ j • t₂ ∈ compactlySupportedForms I M (j + l + 1) :=
    ht₂_eq ▸ Submodule.smul_mem _ _ (SmoothForm.wedge_mem_compactlySupportedForms α
      (compactlySupportedForms.mextDerivₗ I M l γ).2)
  have hstokes : integralTopForm o₁ (t₁ + (-1 : ℝ) ^ j • t₂).1 = 0 := by
    have ht₂ : t₂ = LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h₂
        (SmoothForm.wedge α (mextDerivₗ I l γ.1)) := by
      dsimp only [t₂]; rw [compactlySupportedForms.coe_mextDerivₗ]
    rw [ht₂, ← SmoothForm.mextDerivₗ_wedge α γ.1, mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero o₁
      ((SmoothForm.wedge α γ.1).isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms α γ.2))
  rw [Submodule.coe_add, integralTopForm_add o₁ (t₁.isSmoothForm.of_le (by simp))
      (((-1 : ℝ) ^ j • t₂).isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms I).mp ht₁_mem) ((mem_compactlySupportedForms I).mp ht₂_mem),
    Submodule.coe_smul, integralTopForm_smul] at hstokes
  have hc₁ : integralTopForm o₁ t₁.1 =
      integralTopForm o (RoughForm.wedge (mextDerivₗ I j α).1 γ.1.1) :=
    (integralTopForm_congr_cast h₁.symm o₁ t₁.1 (RoughForm.wedge (mextDerivₗ I j α).1 γ.1.1)
      fun _ _ ↦ by dsimp only [t₁]; rw [SmoothForm.cast_apply, SmoothForm.coe_wedge]).trans <| by
      dsimp only [o₁]; rw [orientation_reindex_finCongr, finCongr_refl, orientation_reindex_refl]
  have hc₂ : integralTopForm o₁ t₂.1 = integralTopForm (o.reindex (finCongr hjl))
      (RoughForm.wedge α.1 (compactlySupportedForms.mextDerivₗ I M l γ).1.1) :=
    (integralTopForm_congr_cast h₂.symm o₁ t₂.1
      (RoughForm.wedge α.1 (compactlySupportedForms.mextDerivₗ I M l γ).1.1)
      fun _ _ ↦ by dsimp only [t₂]; rw [SmoothForm.cast_apply, SmoothForm.coe_wedge]).trans <| by
      dsimp only [o₁]; rw [orientation_reindex_finCongr]
  rw [hc₁, hc₂] at hstokes
  rw [pow_succ, mul_neg, mul_one, neg_mul]; linarith

private theorem integralTopForm_mayerVietoris_step {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    (φ : SmoothForm I (U ⊓ V : Opens M) ℝ j) (α : SmoothForm I U ℝ j) (β : SmoothForm I V ℝ j)
    (hαβ : SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) α -
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) β = φ)
    (σ : SmoothForm I (U ⊔ V : Opens M) ℝ (j + 1))
    (hσU : SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) σ =
      mextDerivₗ I j α)
    (hσV : SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) σ =
      mextDerivₗ I j β)
    (γ : compactlySupportedForms I U l) (δ : compactlySupportedForms I V l)
    (τ : compactlySupportedClosedForms I (U ⊓ V : Opens M) (l + 1))
    (hτU : (compactlySupportedClosedForms.extendByZero inf_le_left (l + 1) τ).1 =
      (compactlySupportedForms.mextDerivₗ I U l γ).1)
    (hτV : (compactlySupportedClosedForms.extendByZero inf_le_right (l + 1) τ).1 =
      -(compactlySupportedForms.mextDerivₗ I V l δ).1) :
    integralTopForm (o.restrict (U ⊔ V)) (RoughForm.wedge σ.1
        (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) l γ +
          compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) l δ).1.1) =
      (-1 : ℝ) ^ (j + 1) * integralTopForm ((o.reindex (finCongr hjl)).restrict (U ⊓ V))
        (RoughForm.wedge φ.1 τ.1.1) := by
  rw [← integralWedgeCompactlySupported_apply,
    (integralWedgeCompactlySupported (o.restrict (U ⊔ V)) σ).map_add,
    integralWedgeCompactlySupported_extendByZero o le_sup_left σ γ,
    integralWedgeCompactlySupported_extendByZero o le_sup_right σ δ, hσU, hσV,
    integralWedgeCompactlySupported_mextDeriv hjl (o.restrict U) α γ,
    integralWedgeCompactlySupported_mextDeriv hjl (o.restrict V) β δ,
    orientation_restrict_finCongr, orientation_restrict_finCongr]
  let τ' : compactlySupportedForms I (U ⊓ V : Opens M) (l + 1) :=
    ⟨τ.1, compactlySupportedClosedForms_le_compactlySupportedForms I (l + 1) τ.2⟩
  have heqU : (compactlySupportedClosedForms.extendByZero inf_le_left (l + 1) τ).1 =
      (compactlySupportedForms.extendByZero (inf_le_left : U ⊓ V ≤ U) (l + 1) τ').1 :=
    Subtype.ext <| by
      rw [compactlySupportedClosedForms.coe_extendByZero, compactlySupportedForms.coe_extendByZero]
  have heqV : (compactlySupportedClosedForms.extendByZero inf_le_right (l + 1) τ).1 =
      (compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (l + 1) τ').1 :=
    Subtype.ext <| by
      rw [compactlySupportedClosedForms.coe_extendByZero, compactlySupportedForms.coe_extendByZero]
  have hdγ : compactlySupportedForms.mextDerivₗ I U l γ =
      compactlySupportedForms.extendByZero (inf_le_left : U ⊓ V ≤ U) (l + 1) τ' :=
    Subtype.ext (hτU.symm.trans heqU)
  have hdδ : compactlySupportedForms.mextDerivₗ I V l δ =
      -compactlySupportedForms.extendByZero (inf_le_right : U ⊓ V ≤ V) (l + 1) τ' :=
    Subtype.ext <| by rw [Submodule.coe_neg, ← heqV, hτV, neg_neg]
  rw [hdγ, hdδ, integralWedgeCompactlySupported_neg,
    integralWedgeCompactlySupported_extendByZero (o.reindex (finCongr hjl)) inf_le_left α τ',
    integralWedgeCompactlySupported_extendByZero (o.reindex (finCongr hjl)) inf_le_right β τ',
    ← mul_add, ← sub_eq_add_neg, ← integralWedgeCompactlySupported_sub, hαβ,
    integralWedgeCompactlySupported_apply]

/-- **Compatibility of the Poincaré pairing with the Mayer–Vietoris connecting maps.** -/
theorem poincarePairing_mayerVietorisδ [SigmaCompactSpace M] {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (x : deRhamCohomology I (U ⊓ V : Opens M) j)
    (y : compactlySupportedDeRhamCohomology I (U ⊔ V : Opens M) l) :
    poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))
        (deRhamCohomology.mayerVietorisδ I U V j x) y = (-1 : ℝ) ^ (j + 1) *
      poincarePairing I (U ⊓ V : Opens M) ((o.reindex (finCongr hjl)).restrict (U ⊓ V))
        x (compactlySupportedDeRhamCohomology.mayerVietorisδ I U V l y) := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I j x
  obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I l y
  obtain ⟨⟨α, β⟩, hαβ⟩ := SmoothForm.surjective_mayerVietoris U V φ.1
  rw [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg] at hαβ
  obtain ⟨σ, hσU, hσV⟩ := exists_closedForms_mpullback_eq_mextDerivₗ α β (hαβ ▸ φ.2)
  obtain ⟨⟨γ, δ⟩, hγδ_sub⟩ := compactlySupportedForms.surjective_coprod_extendByZero U V
    ⟨ψ.1, compactlySupportedClosedForms_le_compactlySupportedForms I l ψ.2⟩
  have hγδ : (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) l γ +
      compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) l δ).1 = ψ.1 :=
    congrArg Subtype.val hγδ_sub
  obtain ⟨τ, hτU, hτV⟩ := exists_compactlySupportedClosedForms_extendByZero_eq_mextDerivₗ γ δ
    (hγδ ▸ compactlySupportedClosedForms_le_closedForms I l ψ.2)
  rw [deRhamCohomology.mayerVietorisδ_mk U V φ α β hαβ σ hσU hσV,
    compactlySupportedDeRhamCohomology.mayerVietorisδ_mk U V ψ γ δ hγδ τ hτU hτV,
    poincarePairing_mk, poincarePairing_mk, ← hγδ]
  exact integralTopForm_mayerVietoris_step hjl o U V φ.1 α β hαβ σ.1 hσU hσV γ δ τ hτU hτV

end MayerVietorisStokes

section MayerVietorisStep

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private def prodPoincarePairing (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b))) :
    (deRhamCohomology I U a × deRhamCohomology I V a) →ₗ[ℝ]
      Module.Dual ℝ
        (compactlySupportedDeRhamCohomology I U b × compactlySupportedDeRhamCohomology I V b) :=
  (Module.dualProdDualEquivDual ℝ _ _).toLinearMap.comp
    ((poincarePairing I U (o.restrict U)).prodMap (poincarePairing I V (o.restrict V)))

omit [SigmaCompactSpace M] in
private theorem bijective_prodPoincarePairing (U V : Opens M) [SigmaCompactSpace U]
    [SigmaCompactSpace V] {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b)))
    (hU : Bijective (poincarePairing I U (o.restrict U)))
    (hV : Bijective (poincarePairing I V (o.restrict V))) : Bijective (prodPoincarePairing U V o) :=
  (Module.dualProdDualEquivDual ℝ _ _).bijective.comp (hU.prodMap hV)

omit [SigmaCompactSpace M] in
private theorem comm_poincarePairing_sup_prod (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] [SigmaCompactSpace (U ⊔ V : Opens M)]
    {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b))) :
    ((compactlySupportedDeRhamCohomology.extendByZero (I := I) (le_sup_left : U ≤ U ⊔ V) b).coprod
        (compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (le_sup_right : V ≤ U ⊔ V) b)).dualMap.comp
      (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) =
    (prodPoincarePairing U V o).comp
      ((deRhamCohomology.map (Opens.inclusion (le_sup_left : U ≤ U ⊔ V))
          (contMDiff_inclusion _) a).prod
        (deRhamCohomology.map (Opens.inclusion (le_sup_right : V ≤ U ⊔ V))
          (contMDiff_inclusion _) a)) :=
  LinearMap.ext fun _ ↦ LinearMap.ext fun ⟨_, _⟩ ↦ by
    simp [prodPoincarePairing, poincarePairing_extendByZero]

omit [SigmaCompactSpace M] in
private theorem comm_poincarePairing_prod_inf (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)]
    {a b : ℕ} (o : Manifold.Orientation I M (Fin (a + b))) :
    ((compactlySupportedDeRhamCohomology.extendByZero (I := I) (inf_le_left : U ⊓ V ≤ U) b).prod
        (-compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (inf_le_right : U ⊓ V ≤ V) b)).dualMap.comp
      (prodPoincarePairing U V o) =
    (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V))).comp
      ((deRhamCohomology.map (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
          (contMDiff_inclusion _) a).coprod
        (-deRhamCohomology.map (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
          (contMDiff_inclusion _) a)) :=
  LinearMap.ext fun ⟨_, _⟩ ↦ LinearMap.ext fun _ ↦ by
    simp [prodPoincarePairing, poincarePairing_extendByZero]

private theorem bijective_poincarePairing_sup {n : ℕ} (o : Manifold.Orientation I M (Fin n))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I U ((o.reindex (finCongr hab.symm)).restrict U)))
    (hV : ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I V ((o.reindex (finCongr hab.symm)).restrict V)))
    (hUV : ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I (U ⊓ V : Opens M)
        ((o.reindex (finCongr hab.symm)).restrict (U ⊓ V)))) :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I (U ⊔ V : Opens M)
        ((o.reindex (finCongr hab.symm)).restrict (U ⊔ V))) := by
  intro a b hab
  let o₁ := o.reindex (finCongr hab.symm)
  cases a with
  | zero =>
    have hl : Module.finrank ℝ E < b + 1 := by
      have hcard := o.card_eq; rw [Fintype.card_fin] at hcard; omega
    have := subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt I (U ⊓ V : Opens M) hl
    have hsurj : Surjective
        ((compactlySupportedDeRhamCohomology.extendByZero (I := I)
            (le_sup_left : U ≤ U ⊔ V) b).coprod
          (compactlySupportedDeRhamCohomology.extendByZero (I := I)
            (le_sup_right : V ≤ U ⊔ V) b)) := fun y ↦
      (compactlySupportedDeRhamCohomology.exact_mayerVietoris₃ U V b y).mp (Subsingleton.elim _ 0)
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact _ _ _ _
      (poincarePairing I (U ⊔ V : Opens M) (o₁.restrict (U ⊔ V))) (prodPoincarePairing U V o₁)
      (poincarePairing I (U ⊓ V : Opens M) (o₁.restrict (U ⊓ V)))
      (comm_poincarePairing_sup_prod U V o₁) (comm_poincarePairing_prod_inf U V o₁)
      (deRhamCohomology.exact_mayerVietoris₂ U V 0)
      (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₂ U V b))
      (bijective_prodPoincarePairing U V o₁ (hU 0 b hab) (hV 0 b hab)) (hUV 0 b hab).1
      (deRhamCohomology.injective_mayerVietoris_zero U V)
      (LinearMap.dualMap_injective_of_surjective hsurj)
  | succ j =>
    have hjb : j + (b + 1) = n := by omega
    have hjl : (j + 1) + b = j + (b + 1) := by omega
    let o' := o₁.reindex (finCongr hjl)
    have hre : o' = o.reindex (finCongr hjb.symm) := orientation_reindex_finCongr _ _ o
    let s : ℝ := (-1 : ℝ) ^ (j + 1)
    have hc₁ : ((compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (inf_le_left : U ⊓ V ≤ U) (b + 1)).prod
          (-compactlySupportedDeRhamCohomology.extendByZero (I := I)
            (inf_le_right : U ⊓ V ≤ V) (b + 1))).dualMap.comp
        (s • prodPoincarePairing U V o') =
        (s • poincarePairing I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V))).comp
          ((deRhamCohomology.map (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
              (contMDiff_inclusion _) j).coprod
            (-deRhamCohomology.map (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
              (contMDiff_inclusion _) j)) := by
      rw [LinearMap.comp_smul, LinearMap.smul_comp, comm_poincarePairing_prod_inf U V o']
    have hc₂ : (compactlySupportedDeRhamCohomology.mayerVietorisδ I U V b).dualMap.comp
        (s • poincarePairing I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V))) =
        (poincarePairing I (U ⊔ V : Opens M) (o₁.restrict (U ⊔ V))).comp
          (deRhamCohomology.mayerVietorisδ I U V j) :=
      LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ by
        simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.smul_apply,
          smul_eq_mul, s, o'] using (poincarePairing_mayerVietorisδ hjl o₁ U V x y).symm
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
      (s • prodPoincarePairing U V o') (s • poincarePairing I (U ⊓ V : Opens M) (o'.restrict _))
      (poincarePairing I (U ⊔ V : Opens M) (o₁.restrict (U ⊔ V))) (prodPoincarePairing U V o₁)
      (poincarePairing I (U ⊓ V : Opens M) (o₁.restrict (U ⊓ V)))
      hc₁ hc₂ (comm_poincarePairing_sup_prod U V o₁) (comm_poincarePairing_prod_inf U V o₁)
      (deRhamCohomology.exact_mayerVietoris₃ U V j) (deRhamCohomology.exact_mayerVietoris₁ U V j)
      (deRhamCohomology.exact_mayerVietoris₂ U V (j + 1))
      (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₁ U V b))
      (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₃ U V b))
      (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₂ U V b))
      (bijective_neg_one_pow_smul (j + 1)
        (bijective_prodPoincarePairing U V o' (hre ▸ hU j (b + 1) hjb) (hre ▸ hV j (b + 1) hjb))).2
      (bijective_neg_one_pow_smul (j + 1) (hre ▸ hUV j (b + 1) hjb))
      (bijective_prodPoincarePairing U V o₁ (hU (j + 1) b hab) (hV (j + 1) b hab))
      (hUV (j + 1) b hab).1

end MayerVietorisStep

section BaseAndGlobalization

section DualityTransport

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N] {k l : ℕ}

private theorem bijective_poincarePairing_of_isEmpty [IsEmpty M]
    (o : Manifold.Orientation I M (Fin (k + l))) : Bijective (poincarePairing I M o) := by
  have : Subsingleton (SmoothForm I M ℝ k) :=
    ⟨fun _ _ ↦ Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  have : Subsingleton (deRhamCohomology I M k) := (deRhamCohomology.mk_surjective I k).subsingleton
  have : Subsingleton (SmoothForm I M ℝ l) :=
    ⟨fun _ _ ↦ Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  have : Subsingleton (compactlySupportedDeRhamCohomology I M l) :=
    (compactlySupportedDeRhamCohomology.mk_surjective I l).subsingleton
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private theorem bijective_poincarePairing_iff_of_isOrientationPreserving
    (Φ : M ≃ₘ⟮I, J⟯ N) (o : Manifold.Orientation I M (Fin (k + l)))
    (o' : Manifold.Orientation J N (Fin (k + l)))
    (hpres : ∀ x : M, o.IsOrientationPreservingAt o' Φ x) :
    Bijective (poincarePairing I M o) ↔ Bijective (poincarePairing J N o') := by
  let e₁ := deRhamCohomology.equivOfDiffeomorph Φ k
  let e₂ := compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ l
  have hfn : ⇑(poincarePairing J N o') = ⇑e₂.dualMap ∘ ⇑(poincarePairing I M o) ∘ ⇑e₁ :=
    funext fun x ↦ LinearMap.ext fun y ↦ by
      simpa only [Function.comp_apply, LinearEquiv.dualMap_apply, e₁, e₂,
        deRhamCohomology.equivOfDiffeomorph_apply,
        compactlySupportedDeRhamCohomology.equivOfDiffeomorph_apply] using
        (poincarePairing_map_diffeomorph o o' Φ hpres x y).symm
  rw [hfn, e₂.dualMap.bijective.of_comp_iff', Bijective.of_comp_iff _ e₁.bijective]

private theorem bijective_poincarePairing_of_diffeomorph
    (Φ : M ≃ₘ⟮I, J⟯ N) (o : Manifold.Orientation I M (Fin (k + l)))
    (hN : ∀ o' : Manifold.Orientation J N (Fin (k + l)), Bijective (poincarePairing J N o')) :
    Bijective (poincarePairing I M o) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact bijective_poincarePairing_of_isEmpty o
  · have hdim : Fintype.card (Fin (k + l)) = Module.finrank ℝ E' :=
      o.card_eq.trans (Φ.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv.finrank_eq
    let o' := o.pullback (Φ.symm.contMDiff.of_le (by simp))
      (fun _ ↦ Φ.symm.isInvertible_mfderiv (by simp)) hdim
    exact (bijective_poincarePairing_iff_of_isOrientationPreserving Φ.symm o' o
      (Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _)).mp (hN o')

end DualityTransport

/-- **Poincaré duality on a finite-dimensional real normed space.** -/
theorem bijective_poincarePairing_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k l : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin (k + l))) :
    Bijective (poincarePairing 𝓘(ℝ, E) E o) := by
  have hdim : k + l = Module.finrank ℝ E := by simpa only [Fintype.card_fin] using o.card_eq
  cases k with
  | zero =>
    have hconst : Bijective (deRhamCohomology.const 𝓘(ℝ, E) E) :=
      ⟨deRhamCohomology.const_injective, fun c ↦
        let ⟨r, hr⟩ := deRhamCohomology.exists_eq_const c; ⟨r, hr.symm⟩⟩
    let eI := LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.bijective_integral (o.reindex (finCongr (zero_add l))))
    let eR : ℝ ≃ₗ[ℝ] Module.Dual ℝ ℝ := (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm
    have hcomm : (poincarePairing 𝓘(ℝ, E) E o).comp (deRhamCohomology.const 𝓘(ℝ, E) E) =
        eI.dualMap.toLinearMap.comp eR.toLinearMap :=
      LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by simp [eI, eR, mul_comm]
    refine (Bijective.of_comp_iff (poincarePairing 𝓘(ℝ, E) E o) hconst).mp ?_
    change Bijective ((poincarePairing 𝓘(ℝ, E) E o).comp (deRhamCohomology.const 𝓘(ℝ, E) E))
    exact hcomm ▸ eI.dualMap.bijective.comp eR.bijective
  | succ j =>
    have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) E (j + 1)) :=
      subsingleton_deRhamCohomology_normedSpace (E := E) j
    have : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E l) :=
      subsingleton_compactlySupportedDeRhamCohomology_normedSpace E (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private theorem bijective_poincarePairing_opens_of_isBasis
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [SecondCountableTopology M] [LocallyCompactSpace M] {n : ℕ}
    (o : Manifold.Orientation I M (Fin n)) (B : Set (Opens M)) (hB : Opens.IsBasis B)
    (hinf : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B)
    (hbase : ∀ U ∈ B, ∀ [SigmaCompactSpace U] (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I U ((o.reindex (finCongr hab.symm)).restrict U)))
    (W : Opens M) [SigmaCompactSpace W] :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I W ((o.reindex (finCongr hab.symm)).restrict W)) := by
  let P (U : Opens M) : Prop :=
    ∀ [SigmaCompactSpace U] (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing I U ((o.reindex (finCongr hab.symm)).restrict U))
  exact mayerVietoris_induction P B hB hinf
    (by
      intro _ a b hab; have : IsEmpty (⊥ : Opens M) := isEmpty_coe_sort.mpr rfl
      exact bijective_poincarePairing_of_isEmpty _)
    hbase
    (fun U V hU hV hUV _ a b hab ↦ by
      have := U.isOpen.locallyCompactSpace; have := V.isOpen.locallyCompactSpace
      have := (U ⊓ V : Opens M).isOpen.locallyCompactSpace
      exact bijective_poincarePairing_sup o U V hU hV hUV a b hab)
    (fun s hs hPs _ a b hab ↦ by
      have (m : ℕ) := (s m).isOpen.locallyCompactSpace
      exact bijective_poincarePairing_iSup (o.reindex (finCongr hab.symm)) hs
        fun m ↦ hPs m a b hab) W

private def openBox {d : ℕ} (a b : Fin d → ℝ) : Opens (EuclideanSpace ℝ (Fin d)) :=
  ⟨{x | ∀ i, EuclideanSpace.equiv (Fin d) ℝ x i ∈ Ioo (a i) (b i)}, by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioo.preimage ((continuous_apply i).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous)⟩

private theorem isBasis_openBoxes (d : ℕ) :
    Opens.IsBasis {U : Opens (EuclideanSpace ℝ (Fin d)) | ∃ a b, U = openBox a b} := by
  rw [Opens.isBasis_iff_nbhd]; intro U x hx
  let L := EuclideanSpace.equiv (Fin d) ℝ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (U.isOpen.preimage L.symm.continuous) (L x) hx
  refine ⟨openBox (fun i ↦ L x i - r) (fun i ↦ L x i + r), ⟨_, _, rfl⟩,
    fun i ↦ ⟨sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩, fun y hy ↦ ?_⟩
  have hyb : L y ∈ Metric.ball (L x) r := by
    rw [ball_pi _ hr]; intro i _; dsimp only; rw [Real.ball_eq_Ioo]; exact hy i
  have hyU : L.symm (L y) ∈ (U : Set (EuclideanSpace ℝ (Fin d))) := hball hyb
  rwa [ContinuousLinearEquiv.symm_apply_apply] at hyU

private def diffeomorphOpenBox {d : ℕ} {a b : Fin d → ℝ} (hab : ∀ i, a i < b i) :
    EuclideanSpace ℝ (Fin d) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin d)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin d))⟯ openBox a b := by
  let L := EuclideanSpace.equiv (Fin d) ℝ
  let c (i : Fin d) : ℝ := (a i + b i) / 2
  let r (i : Fin d) : ℝ := (b i - a i) / 2
  have hr (i : Fin d) : 0 < r i := by dsimp [r]; linarith [hab i]
  let e (i : Fin d) := OpenPartialHomeomorph.univBall (c i) (r i)
  have htarget (i : Fin d) : (e i).target = Ioo (a i) (b i) := by
    rw [OpenPartialHomeomorph.univBall_target _ (hr i), Real.ball_eq_Ioo]
    congr <;> dsimp [c, r] <;> ring
  have hmem (v : EuclideanSpace ℝ (Fin d)) : L.symm (fun i ↦ e i (L v i)) ∈ openBox a b :=
    fun i ↦ by
      change L (L.symm (fun j ↦ e j (L v j))) i ∈ Ioo (a i) (b i)
      rw [L.apply_symm_apply, ← htarget i]; exact (e i).map_source (by simp [e])
  refine
    { toEquiv :=
        { toFun := fun v ↦ ⟨L.symm (fun i ↦ e i (L v i)), hmem v⟩
          invFun := fun u ↦ L.symm (fun i ↦ (e i).symm (L u.1 i))
          left_inv := fun v ↦ L.injective <| funext fun i ↦ by
            simp only [L.apply_symm_apply]; exact (e i).left_inv (by simp [e])
          right_inv := fun u ↦ Subtype.ext <| L.injective <| funext fun i ↦ by
            simp only [L.apply_symm_apply]; exact (e i).right_inv (htarget i ▸ u.2 i) }
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp <|
        L.symm.contDiff.contMDiff.comp <| contMDiff_pi_module_iff.mpr fun i ↦
          OpenPartialHomeomorph.contDiff_univBall.contMDiff.comp
            (((ContinuousLinearMap.proj (R := ℝ) i).comp
              (L : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))).contMDiff)
      contMDiff_invFun := L.symm.contDiff.contMDiff.comp <| contMDiff_pi_module_iff.mpr fun i ↦ by
        have hcd : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (e i).symm (Ioo (a i) (b i)) := by
          rw [← htarget i, OpenPartialHomeomorph.univBall_target _ (hr i)]
          exact (OpenPartialHomeomorph.contDiffOn_univBall_symm (n := (⊤ : ℕ∞))).contMDiffOn
        exact hcd.comp_contMDiff
          ((((ContinuousLinearMap.proj (R := ℝ) i).comp
            (L : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))).contMDiff).comp contMDiff_subtype_val)
          fun u ↦ u.2 i }

private theorem bijective_poincarePairing_opens_euclideanSpace {d n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) (Fin n))
    (W : Opens (EuclideanSpace ℝ (Fin d))) [SigmaCompactSpace W] :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) W
        ((o.reindex (finCongr hab.symm)).restrict W)) :=
  bijective_poincarePairing_opens_of_isBasis o _ (isBasis_openBoxes d)
    (by
      rintro _ ⟨a₁, b₁, rfl⟩ _ ⟨a₂, b₂, rfl⟩
      refine ⟨fun i ↦ max (a₁ i) (a₂ i), fun i ↦ min (b₁ i) (b₂ i), ?_⟩
      ext x
      change (∀ i, _ ∈ Ioo (a₁ i) (b₁ i)) ∧ (∀ i, _ ∈ Ioo (a₂ i) (b₂ i)) ↔
        ∀ i, _ ∈ Ioo (max (a₁ i) (a₂ i)) (min (b₁ i) (b₂ i))
      simp only [← forall_and, ← mem_inter_iff, Ioo_inter_Ioo])
    (by
      rintro U ⟨p, q, rfl⟩ _ a b hab
      by_cases hpq : ∀ i, p i < q i
      · exact bijective_poincarePairing_of_diffeomorph (diffeomorphOpenBox hpq).symm _
          fun o' ↦ bijective_poincarePairing_normedSpace _ o'
      · push Not at hpq; obtain ⟨i, hi⟩ := hpq
        have : IsEmpty (openBox p q) :=
          ⟨fun x ↦ (lt_irrefl _ ((x.2 i).1.trans_le ((x.2 i).2.le.trans hi))).elim⟩
        exact bijective_poincarePairing_of_isEmpty _) W

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

private theorem bijective_poincarePairing_of_le_diffeomorph_euclideanSpace
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    {U W : Opens M} [SigmaCompactSpace W] (hWU : W ≤ U)
    (Φ : U ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    {a b : ℕ} (oM : Manifold.Orientation I M (Fin (a + b))) :
    Bijective (poincarePairing I W (oM.restrict W)) := by
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  let V : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ⟨{z | (Φ.symm z : M) ∈ W}, W.isOpen.preimage (continuous_subtype_val.comp Φ.symm.continuous)⟩
  have : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  let Ψ : W ≃ₘ⟮I, J⟯ V :=
    { toEquiv :=
        { toFun := fun w ↦ ⟨Φ ⟨w.1, hWU w.2⟩, by simp [V, Φ.symm_apply_apply]⟩
          invFun := fun v ↦ ⟨(Φ.symm v.1).1, v.2⟩
          left_inv := fun w ↦ Subtype.ext <| by
            dsimp only; exact congrArg Subtype.val (Φ.symm_apply_apply ⟨w.1, hWU w.2⟩)
          right_inv := fun v ↦ Subtype.ext (Φ.apply_symm_apply v.1) }
      contMDiff_toFun :=
        (ContMDiff.subtypeVal_comp_iff _ _).mp (Φ.contMDiff.comp (contMDiff_inclusion hWU))
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
        ((contMDiff_subtype_val (I := I) (U := U)).comp
          (Φ.symm.contMDiff.comp contMDiff_subtype_val)) }
  let oE : Manifold.Orientation J (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (Fin (a + b)) :=
    (oM.restrict U).pullback (Φ.symm.contMDiff.of_le (by simp))
      (fun _ ↦ Φ.symm.isInvertible_mfderiv (by simp))
      (oM.card_eq.trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := Module.finrank ℝ E)).symm)
  have hΨ_pres (w : W) : (oM.restrict W).IsOrientationPreservingAt (oE.restrict V) Ψ w := by
    have hcomp : ((Subtype.val : U → M) ∘ Φ.symm ∘ (Subtype.val : V → _)) ∘ Ψ =
        (Subtype.val : W → M) :=
      funext fun z ↦ congrArg Subtype.val (Φ.symm_apply_apply ⟨z.1, hWU z.2⟩)
    exact ((oM.isOrientationPreservingAt_restrict U _).comp
      ((Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _ _).comp
        (oE.isOrientationPreservingAt_restrict V (Ψ w)))).of_comp
      (hcomp.symm ▸ oM.isOrientationPreservingAt_restrict W w)
      (Ψ.contMDiff.mdifferentiableAt (by simp))
  refine (bijective_poincarePairing_iff_of_isOrientationPreserving Ψ _ _ hΨ_pres).mpr ?_
  simpa only [finCongr_refl, orientation_reindex_refl] using
    bijective_poincarePairing_opens_euclideanSpace oE V a b rfl

/-- **De Rham Poincaré duality.** On an oriented boundaryless Hausdorff σ-compact finite-dimensional
smooth manifold `M` of dimension `k + l`, with no compactness hypothesis, the Poincaré pairing
`TauCeti.poincarePairing I M o` is a bijection from `H^k_dR(M)` onto the dual of `H^l_c(M)`. -/
theorem bijective_poincarePairing [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    Function.Bijective (poincarePairing I M o : deRhamCohomology I M k →
      Module.Dual ℝ (compactlySupportedDeRhamCohomology I M l)) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace (⊤ : Opens M) := (⊤ : Opens M).isOpen.locallyCompactSpace
  choose U hxU hΦ using fun x : M ↦
    exists_opens_diffeomorph_euclideanSpace (n := ⊤)
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  have htop_kl : Bijective (poincarePairing I (⊤ : Opens M) (o.restrict ⊤)) := by
    simpa only [finCongr_refl, orientation_reindex_refl] using
      bijective_poincarePairing_opens_of_isBasis o {W : Opens M | ∃ x : M, W ≤ U x}
        (Opens.isBasis_iff_nbhd.mpr fun {W x} hxW ↦
          ⟨W ⊓ U x, ⟨x, inf_le_right⟩, ⟨hxW, hxU x⟩, inf_le_left⟩)
        (fun _ ⟨x, hx⟩ _ _ ↦ ⟨x, inf_le_left.trans hx⟩)
        (fun _ ⟨x, hW⟩ _ _ _ hab ↦
          bijective_poincarePairing_of_le_diffeomorph_euclideanSpace hW (hΦ x).some
            (o.reindex (finCongr hab.symm))) ⊤ k l rfl
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  exact (bijective_poincarePairing_iff_of_isOrientationPreserving Φ _ _ fun z ↦ by
    rw [Diffeomorph.coe_ofTop]; exact o.isOrientationPreservingAt_restrict ⊤ z).mp htop_kl

end BaseAndGlobalization

section BundledAPI

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] {k l : ℕ}

/-- **De Rham Poincaré duality** as a linear equivalence `H^k_dR(M) ≃ₗ[ℝ] (H^l_c(M))^*`. -/
def poincareDuality (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k ≃ₗ[ℝ] Module.Dual ℝ (compactlySupportedDeRhamCohomology I M l) :=
  LinearEquiv.ofBijective (poincarePairing I M o) (bijective_poincarePairing o)

/-- `TauCeti.poincareDuality` evaluates as `TauCeti.poincarePairing`. -/
@[simp]
theorem poincareDuality_apply (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) (y : compactlySupportedDeRhamCohomology I M l) :
    poincareDuality o x y = poincarePairing I M o x y := (rfl)

/-- The underlying linear map of `TauCeti.poincareDuality` is `TauCeti.poincarePairing`. -/
@[simp]
theorem poincareDuality_toLinearMap (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincareDuality o).toLinearMap = poincarePairing I M o := (rfl)

/-- Reversing the orientation negates `TauCeti.poincareDuality`. -/
@[simp]
theorem poincareDuality_neg (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) :
    poincareDuality (-o) x = -poincareDuality o x := by ext y; simp [poincareDuality_apply]

/-- The Poincaré pairing is left-separating. -/
theorem poincarePairing_separatingLeft (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).SeparatingLeft :=
  LinearMap.separatingLeft_iff_ker_eq_bot.mpr
    (LinearMap.ker_eq_bot_of_injective (bijective_poincarePairing o).injective)

/-- The Poincaré pairing is right-separating. -/
theorem poincarePairing_separatingRight (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).SeparatingRight := fun y hy ↦
  (Module.forall_dual_apply_eq_zero_iff ℝ y).mp fun φ ↦
    let ⟨x, hx⟩ := (bijective_poincarePairing o).surjective φ; hx ▸ hy x

/-- **Nondegeneracy of the Poincaré pairing** in both arguments. -/
theorem poincarePairing_nondegenerate (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).Nondegenerate :=
  ⟨poincarePairing_separatingLeft o, poincarePairing_separatingRight o⟩

/-- If `x ∈ H^k_dR(M)` pairs to zero with every `y ∈ H^l_c(M)`, then `x = 0`. -/
theorem eq_zero_of_forall_poincarePairing_eq_zero_left
    (o : Manifold.Orientation I M (Fin (k + l))) {x : deRhamCohomology I M k}
    (hx : ∀ y, poincarePairing I M o x y = 0) : x = 0 := poincarePairing_separatingLeft o x hx

/-- If every `x ∈ H^k_dR(M)` pairs to zero with `y ∈ H^l_c(M)`, then `y = 0`. -/
theorem eq_zero_of_forall_poincarePairing_eq_zero_right
    (o : Manifold.Orientation I M (Fin (k + l))) {y : compactlySupportedDeRhamCohomology I M l}
    (hy : ∀ x, poincarePairing I M o x y = 0) : y = 0 := poincarePairing_separatingRight o y hy

end BundledAPI

section CompactManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- On a compact oriented boundaryless manifold of dimension `k + l`, Poincaré duality identifies
`H^k_dR(M)` with the dual of `H^l_dR(M)`. -/
def poincareDualityCompact {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k ≃ₗ[ℝ] Module.Dual ℝ (deRhamCohomology I M l) :=
  (poincareDuality o).trans (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I l)).symm.dualMap

private theorem finiteDimensional_deRhamCohomology_of_orientation
    (o : Manifold.Orientation I M (Fin (Module.finrank ℝ E))) (k : ℕ) :
    FiniteDimensional ℝ (deRhamCohomology I M k) := by
  by_cases hk : k ≤ Module.finrank ℝ E
  · set l := Module.finrank ℝ E - k
    have hkl : k + l = Module.finrank ℝ E := Nat.add_sub_of_le hk
    have hlk : l + k = Module.finrank ℝ E := Nat.add_comm k l ▸ hkl
    let e₁ := poincareDualityCompact (o.reindex (finCongr hkl.symm))
    let e₂ := poincareDualityCompact (o.reindex (finCongr hlk.symm))
    rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
    by_contra! hinf
    have h₁ : Module.rank ℝ (deRhamCohomology I M k) <
        Module.rank ℝ (Module.Dual ℝ (deRhamCohomology I M k)) := by
      simpa only [Cardinal.lift_id'] using lift_rank_lt_rank_dual hinf
    have h₂ : Module.rank ℝ (deRhamCohomology I M l) <
        Module.rank ℝ (Module.Dual ℝ (deRhamCohomology I M l)) := by
      simpa only [Cardinal.lift_id'] using
        lift_rank_lt_rank_dual (hinf.trans (h₁.le.trans_eq e₂.symm.rank_eq))
    exact lt_irrefl _ ((h₁.trans_eq e₂.symm.rank_eq).trans (h₂.trans_eq e₁.symm.rank_eq))
  · push Not at hk
    have := subsingleton_deRhamCohomology_of_finrank_lt I M hk
    infer_instance

/-- **Finite-dimensionality of de Rham cohomology on a compact boundaryless manifold** (orientable
or nonorientable, via injective pullback to `Manifold.OrientationCover`). -/
instance finiteDimensional_deRhamCohomology (k : ℕ) :
    FiniteDimensional ℝ (deRhamCohomology I M k) := by
  have : CompactSpace (Manifold.OrientationCover I M) :=
    ⟨by simpa only [preimage_univ] using
      (Manifold.OrientationCover.isProperMap_proj I M).isCompact_preimage isCompact_univ⟩
  have : FiniteDimensional ℝ (deRhamCohomology I (Manifold.OrientationCover I M) k) :=
    finiteDimensional_deRhamCohomology_of_orientation
      Manifold.OrientationCover.canonicalOrientation k
  exact FiniteDimensional.of_injective _
    (Manifold.OrientationCover.deRhamCohomology_map_proj_injective k)

/-- Compactly supported de Rham cohomology of a compact boundaryless manifold is
finite-dimensional. -/
instance finiteDimensional_compactlySupportedDeRhamCohomology (k : ℕ) :
    FiniteDimensional ℝ (compactlySupportedDeRhamCohomology I M k) :=
  FiniteDimensional.of_injective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k).injective

/-- **Betti-number symmetry on a compact oriented boundaryless manifold.** -/
theorem finrank_deRhamCohomology_eq_of_orientation {k l : ℕ}
    (o : Manifold.Orientation I M (Fin (k + l))) :
    Module.finrank ℝ (deRhamCohomology I M k) = Module.finrank ℝ (deRhamCohomology I M l) :=
  (poincareDualityCompact o).finrank_eq.trans Subspace.dual_finrank_eq

variable (I M) in
/-- The compactly supported degree-zero cohomology class of a constant `r : ℝ`. -/
def compactlySupportedDeRhamCohomology.const :
    ℝ →ₗ[ℝ] compactlySupportedDeRhamCohomology I M 0 :=
  (LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I
    (M := M) 0)).symm.toLinearMap.comp (deRhamCohomology.const I M)

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
/-- Forgetting compact support sends `compactlySupportedDeRhamCohomology.const` to
`deRhamCohomology.const`. -/
@[simp]
theorem compactlySupportedDeRhamCohomology.toDeRhamCohomology_const (r : ℝ) :
    compactlySupportedDeRhamCohomology.toDeRhamCohomology I M 0
        (compactlySupportedDeRhamCohomology.const I M r) = deRhamCohomology.const I M r :=
  (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I 0)).apply_symm_apply _

/-- Pairing `x ∈ H^k_dR(M)` with `compactlySupportedDeRhamCohomology.const I M r` multiplies the
integral of `x` by `r`. -/
@[simp]
theorem poincarePairing_const_right {k : ℕ} (o : Manifold.Orientation I M (Fin (k + 0)))
    (x : deRhamCohomology I M k) (r : ℝ) :
    poincarePairing I M o x (compactlySupportedDeRhamCohomology.const I M r) =
      r * compactlySupportedDeRhamCohomology.integral (o.reindex (finCongr (Nat.add_zero k)))
        ((LinearEquiv.ofBijective _
          (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k)).symm x) := by
  let e := LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I (M := M) k)
  have hxc : compactlySupportedDeRhamCohomology.toDeRhamCohomology I M k (e.symm x) = x :=
    e.apply_symm_apply x
  rw [← hxc, poincarePairing_comm_toDeRhamCohomology,
    compactlySupportedDeRhamCohomology.toDeRhamCohomology_const, Nat.mul_zero, pow_zero, one_mul,
    poincarePairing_const_left, orientation_reindex_finCongr, hxc]

end CompactManifold

section Examples

/-- On the counterclockwise circle `S¹`, `⟨[dθ], [1]⟩ = 2π`. -/
theorem poincarePairing_circleOrientation_circleAngularClosedForm_const_one :
    poincarePairing (𝓡 1) Circle (circleOrientation.reindex (finCongr (Nat.add_zero 1).symm))
        (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm)
        (compactlySupportedDeRhamCohomology.const (𝓡 1) Circle 1) = 2 * Real.pi := by
  let ψ : compactlySupportedClosedForms (𝓡 1) Circle 1 :=
    ⟨circleAngularClosedForm.1, (mem_compactlySupportedClosedForms (𝓡 1)).mpr
      ⟨(mem_compactlySupportedForms (𝓡 1)).mpr
        (isCompact_univ.of_isClosed_subset (_root_.isClosed_tsupport _) (subset_univ _)),
        circleAngularClosedForm.2⟩⟩
  have hmk : (LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective (𝓡 1) 1)).symm
      (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm) =
      compactlySupportedDeRhamCohomology.mk (𝓡 1) 1 ψ :=
    (LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective (𝓡 1) 1)).injective <| by
      rw [LinearEquiv.apply_symm_apply]
      exact (compactlySupportedDeRhamCohomology.toDeRhamCohomology_mk (𝓡 1) 1 ψ).symm
  rw [poincarePairing_const_right, one_mul, hmk, orientation_reindex_finCongr, finCongr_refl,
    orientation_reindex_refl, compactlySupportedDeRhamCohomology.integral_mk]
  change integralTopForm circleOrientation (circleAngularClosedForm : SmoothForm _ _ _ _).1 = _
  rw [coe_circleAngularClosedForm]; exact integralTopForm_circleOrientation_circleAngularForm

/-- For any orientation of `S¹`, `|⟨[dθ], [1]⟩| = 2π`. -/
theorem abs_poincarePairing_circleAngularClosedForm_const_one
    (o : Manifold.Orientation (𝓡 1) Circle (Fin (1 + 0))) :
    |poincarePairing (𝓡 1) Circle o
        (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm)
        (compactlySupportedDeRhamCohomology.const (𝓡 1) Circle 1)| = 2 * Real.pi := by
  rcases o.eq_or_eq_neg (circleOrientation.reindex (finCongr (Nat.add_zero 1).symm)) with rfl | rfl
  · rw [poincarePairing_circleOrientation_circleAngularClosedForm_const_one,
      abs_of_pos Real.two_pi_pos]
  · rw [poincarePairing_neg, LinearMap.neg_apply, LinearMap.neg_apply, abs_neg,
      poincarePairing_circleOrientation_circleAngularClosedForm_const_one,
      abs_of_pos Real.two_pi_pos]

/-- On the oriented real line `ℝ`, `⟨[1], [ψ]⟩ = ∫ t, ψ t (fun _ ↦ 1)`. -/
theorem poincarePairing_real_const_one_mk
    (ψ : compactlySupportedClosedForms 𝓘(ℝ, ℝ) ℝ 1) :
    poincarePairing 𝓘(ℝ, ℝ) ℝ (Manifold.Orientation.real.reindex (finCongr (zero_add 1).symm))
        (deRhamCohomology.const 𝓘(ℝ, ℝ) ℝ 1)
        (compactlySupportedDeRhamCohomology.mk 𝓘(ℝ, ℝ) 1 ψ) = ∫ t : ℝ, ψ.1.1 t (fun _ ↦ 1) := by
  rw [poincarePairing_const_one_left, orientation_reindex_finCongr, finCongr_refl,
    orientation_reindex_refl, compactlySupportedDeRhamCohomology.integral_mk]
  exact integralTopForm_real_eq_integral (ψ.1.isSmoothForm.of_le (by simp))
    ((mem_compactlySupportedForms 𝓘(ℝ, ℝ)).mp
      ((mem_compactlySupportedClosedForms 𝓘(ℝ, ℝ)).mp ψ.2).1)

end Examples

end TauCeti
