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
`k + l`, with no compactness hypothesis, the Poincaré pairing `⟨[φ], [ψ]⟩ = ∫_M φ ∧ ψ` induces a
linear isomorphism

`H^k_dR(M) ≃ₗ[ℝ] Module.Dual ℝ (H^l_c(M))`

in every pair of complementary degrees `k, l` (`TauCeti.bijective_poincarePairing`,
`TauCeti.poincareDuality`).

The proof proceeds by Mayer–Vietoris induction on open subsets (`TauCeti.mayerVietoris_induction`),
without Hodge theory:

1. **Model spaces and open boxes.** On a finite-dimensional real normed space `E`, de Rham
   cohomology is concentrated in degree `0` (constants) while compactly supported de Rham
   cohomology is concentrated in top degree (where integration is an isomorphism); in all other
   complementary pairs `(k, l)` with `k + l = dim E` both sides vanish
   (`TauCeti.bijective_poincarePairing_normedSpace`). Coordinatewise shrinking by
   `OpenPartialHomeomorph.univBall` identifies every nonempty open coordinate box in `ℝ^d` with
   `ℝ^d`, giving an intersection-closed basis of open subsets of `ℝ^d` on which the pairing is
   bijective.
2. **Binary unions.** By Stokes' theorem and the graded Leibniz rule, the Poincaré pairing
   intertwines the ordinary Mayer–Vietoris connecting homomorphism `H^j(U ⊓ V) → H^{j+1}(U ⊔ V)`
   with `(-1)^(j + 1)` times the dual of the compactly supported Mayer–Vietoris connecting
   homomorphism `H^l_c(U ⊔ V) → H^{l+1}_c(U ⊓ V)` (`TauCeti.poincarePairing_mayerVietorisδ`). The
   five lemma (and its left-exact four-lemma variant in degree `0`) carries bijectivity from `U`,
   `V`, and `U ⊓ V` to `U ⊔ V`.
3. **Disjoint unions and globalization.** Pairwise disjoint open unions are handled by
   `TauCeti.bijective_poincarePairing_iSup`. Mayer–Vietoris induction first establishes duality on
   every open subset of `ℝ^d`, and a second Mayer–Vietoris induction on Euclidean chart
   sub-open sets (`TauCeti.exists_opens_diffeomorph_euclideanSpace`) establishes duality on every
   open subset of `M`, in particular `⊤`, hence on `M`.

## Main definitions and results

* `TauCeti.bijective_poincarePairing`: the Poincaré pairing `H^k_dR(M) → (H^l_c(M))^*` is
  bijective.
* `TauCeti.poincareDuality`: the Poincaré duality linear isomorphism
  `H^k_dR(M) ≃ₗ[ℝ] Module.Dual ℝ (H^l_c(M))`.
* `TauCeti.poincarePairing_nondegenerate`, `TauCeti.poincarePairing_separatingLeft`,
  `TauCeti.poincarePairing_separatingRight`: nondegeneracy of the Poincaré pairing in both
  arguments.
* `TauCeti.finiteDimensional_deRhamCohomology`,
  `TauCeti.finiteDimensional_compactlySupportedDeRhamCohomology`: de Rham cohomology of a compact
  boundaryless Hausdorff smooth manifold is finite-dimensional in every degree (including the
  nonorientable case, by injective pullback to the orientation double cover).
* `TauCeti.finrank_deRhamCohomology_eq_of_orientation`: on a compact oriented boundaryless
  manifold of dimension `k + l`, `finrank ℝ H^k_dR(M) = finrank ℝ H^l_dR(M)`.
* `TauCeti.poincarePairing_circleOrientation_circleAngularClosedForm_const_one` and
  `TauCeti.abs_poincarePairing_circleAngularClosedForm_const_one`: pairing the angular class `[dθ]`
  with `[1]` on `S¹` gives `2π` (and `±2π` for an arbitrary orientation).
* `TauCeti.poincarePairing_real_const_one_mk`: on `ℝ`, pairing `[1] ∈ H⁰_dR(ℝ)` with the compactly
  supported class of a `1`-form `ψ` evaluates the Lebesgue integral `∫ t, ψ t (fun _ ↦ 1)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 and Problems 18-6 to 18-8.
* Raoul Bott and Loring W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Chapter I, §5.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### Algebraic dual exactness and orientation helpers -/

section AlgebraicHelpers

private theorem exact_dualMap {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃] {f : V₁ →ₗ[K] V₂} {g : V₂ →ₗ[K] V₃}
    (h : Exact f g) : Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, Subspace.dualAnnihilator_inj, eq_comm,
    ← LinearMap.exact_iff]
  exact h

private theorem bijective_neg_one_pow_smul {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (m : ℕ) {f : V →ₗ[ℝ] W} (hf : Bijective f) :
    Bijective (((-1 : ℝ) ^ m • f : V →ₗ[ℝ] W)) := by
  have hsq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  refine ⟨fun x y hxy ↦ hf.1 ?_, fun w ↦ ?_⟩
  · have h := congrArg (((-1 : ℝ) ^ m) • ·) hxy
    simpa only [LinearMap.smul_apply, smul_smul, hsq, one_smul] using h
  · obtain ⟨v, hv⟩ := hf.2 ((-1 : ℝ) ^ m • w)
    refine ⟨v, ?_⟩
    rw [LinearMap.smul_apply, hv, smul_smul, hsq, one_smul]

end AlgebraicHelpers

section OrientationHelpers

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

private theorem orientation_reindex_trans {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Fintype ι₃] (e₁ : ι₁ ≃ ι₂) (e₂ : ι₂ ≃ ι₃) (o : Manifold.Orientation I M ι₁) :
    (o.reindex e₁).reindex e₂ = o.reindex (e₁.trans e₂) := by
  ext x
  rw [Manifold.Orientation.orientationAt_reindex, Manifold.Orientation.orientationAt_reindex,
    Manifold.Orientation.orientationAt_reindex]
  induction o.orientationAt x using Module.Ray.ind with | h v hv =>
    simp only [_root_.Orientation.reindex_apply]
    congr 1

private theorem orientation_reindex_refl {ι : Type*} [Fintype ι]
    (o : Manifold.Orientation I M ι) :
    o.reindex (Equiv.refl ι) = o := by
  ext x
  rw [Manifold.Orientation.orientationAt_reindex, _root_.Orientation.reindex_refl,
    Equiv.refl_apply]

private theorem orientation_reindex_finCongr {m n p : ℕ} (h₁ : m = n) (h₂ : n = p)
    (o : Manifold.Orientation I M (Fin m)) :
    (o.reindex (finCongr h₁)).reindex (finCongr h₂) = o.reindex (finCongr (h₁.trans h₂)) := by
  subst h₁
  subst h₂
  rw [finCongr_refl, orientation_reindex_refl]

private theorem isOrientationPreservingAt_reindex
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J 1 N] {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation J N ι} {f : M → N} {x : M}
    (h : o.IsOrientationPreservingAt o' f x) :
    (o.reindex e).IsOrientationPreservingAt (o'.reindex e) f x := by
  rw [Manifold.Orientation.isOrientationPreservingAt_iff] at h ⊢
  obtain ⟨D, hD, hmap⟩ := h
  refine ⟨D, hD, ?_⟩
  rw [Manifold.Orientation.orientationAt_reindex, Manifold.Orientation.orientationAt_reindex,
    ← hmap]
  induction o.orientationAt x using Module.Ray.ind with | h v hv =>
    simp only [_root_.Orientation.reindex_apply, _root_.Orientation.map_apply]
    rfl

private theorem orientation_restrict_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (o : Manifold.Orientation I M ι) (U : Opens M) :
    (o.restrict U).reindex e = (o.reindex e).restrict U :=
  Manifold.Orientation.eq_restrict_iff.mpr fun x ↦
    isOrientationPreservingAt_reindex e (o.isOrientationPreservingAt_restrict U x)

end OrientationHelpers

/-! ### Stokes compatibility with the Mayer–Vietoris connecting homomorphisms -/

section MayerVietorisStokes

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
private theorem smoothForm_cast_mem_compactlySupportedForms {m n : ℕ} (h : m = n)
    {φ : SmoothForm I M ℝ m} (hφ : φ ∈ compactlySupportedForms I M m) :
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h φ ∈
      compactlySupportedForms I M n := by
  subst h
  exact hφ

/-- Integration by parts for a smooth `j`-form `α` against a compactly supported `l`-form `γ` on
an oriented boundaryless manifold of dimension `(j + 1) + l`. -/
private theorem integralTopForm_mextDeriv_wedge_eq [SigmaCompactSpace M] {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (α : SmoothForm I M ℝ j) (γ : compactlySupportedForms I M l) :
    integralTopForm o (RoughForm.wedge (mextDerivₗ I j α).1 γ.1.1) =
      (-1 : ℝ) ^ (j + 1) * integralTopForm (o.reindex (finCongr hjl))
        (RoughForm.wedge α.1 (compactlySupportedForms.mextDerivₗ I M l γ).1.1) := by
  have h₁ : (j + 1) + l = j + l + 1 := by omega
  have h₂ : j + (l + 1) = j + l + 1 := by omega
  let o₁ : Manifold.Orientation I M (Fin (j + l + 1)) := o.reindex (finCongr h₁)
  let t₁ : SmoothForm I M ℝ (j + l + 1) :=
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h₁
      (SmoothForm.wedge (mextDerivₗ I j α) γ.1)
  let t₂ : SmoothForm I M ℝ (j + l + 1) :=
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h₂
      (SmoothForm.wedge α (compactlySupportedForms.mextDerivₗ I M l γ).1)
  have ht₁c : IsCompact (_root_.tsupport (α := E [⋀^Fin (j + l + 1)]→L[ℝ] ℝ) t₁.1) :=
    (mem_compactlySupportedForms I).mp (smoothForm_cast_mem_compactlySupportedForms h₁
      (SmoothForm.wedge_mem_compactlySupportedForms _ γ.2))
  have ht₂c : IsCompact (_root_.tsupport (α := E [⋀^Fin (j + l + 1)]→L[ℝ] ℝ)
      (((-1 : ℝ) ^ j • t₂).1)) :=
    (mem_compactlySupportedForms I).mp (Submodule.smul_mem _ _
      (smoothForm_cast_mem_compactlySupportedForms h₂
        (SmoothForm.wedge_mem_compactlySupportedForms α
          (compactlySupportedForms.mextDerivₗ I M l γ).2)))
  have hstokes : integralTopForm o₁ (t₁ + (-1 : ℝ) ^ j • t₂).1 = 0 := by
    have ht₂ : t₂ = LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) h₂
        (SmoothForm.wedge α (mextDerivₗ I l γ.1)) := by
      dsimp only [t₂]
      rw [compactlySupportedForms.coe_mextDerivₗ]
    rw [ht₂, ← SmoothForm.mextDerivₗ_wedge α γ.1, mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero o₁
      ((SmoothForm.wedge α γ.1).isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms α γ.2))
  rw [Submodule.coe_add, integralTopForm_add o₁ (t₁.isSmoothForm.of_le (by simp))
      (((-1 : ℝ) ^ j • t₂).isSmoothForm.of_le (by simp)) ht₁c ht₂c,
    Submodule.coe_smul, integralTopForm_smul] at hstokes
  have hc₁ : integralTopForm o₁ t₁.1 =
      integralTopForm o (RoughForm.wedge (mextDerivₗ I j α).1 γ.1.1) :=
    (integralTopForm_congr_cast h₁.symm o₁ t₁.1 (RoughForm.wedge (mextDerivₗ I j α).1 γ.1.1)
      fun x v ↦ by dsimp only [t₁]; rw [SmoothForm.cast_apply, SmoothForm.coe_wedge]).trans <| by
      dsimp only [o₁]
      rw [orientation_reindex_finCongr, finCongr_refl, orientation_reindex_refl]
  have hc₂ : integralTopForm o₁ t₂.1 =
      integralTopForm (o.reindex (finCongr hjl))
        (RoughForm.wedge α.1 (compactlySupportedForms.mextDerivₗ I M l γ).1.1) :=
    (integralTopForm_congr_cast h₂.symm o₁ t₂.1
      (RoughForm.wedge α.1 (compactlySupportedForms.mextDerivₗ I M l γ).1.1)
      fun x v ↦ by dsimp only [t₂]; rw [SmoothForm.cast_apply, SmoothForm.coe_wedge]).trans
      (by dsimp only [o₁]; rw [orientation_reindex_finCongr])
  rw [hc₁, hc₂] at hstokes
  rw [pow_succ, mul_neg, mul_one, neg_mul]
  linarith

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
/-- Extending a compactly supported form `η` along `U ≤ W` and wedging with `φ` on `W` agrees with
extending by zero the wedge `φ|_U ∧ η`. -/
private theorem roughForm_wedge_extendByZero_eq {U W : Opens M} {a b : ℕ} (h : U ≤ W)
    (φ : SmoothForm I W ℝ a) (η : compactlySupportedForms I U b) :
    RoughForm.wedge φ.1 (compactlySupportedForms.extendByZero h b η).1.1 =
      RoughForm.extendByZero W
        (RoughForm.wedge (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ).1
          η.1.1) := by
  funext z
  by_cases hz : (z : M) ∈ U
  · obtain ⟨u, rfl⟩ : ∃ u : U, Opens.inclusion h u = z := ⟨⟨z, hz⟩, rfl⟩
    rw [RoughForm.extendByZero_inclusion, SmoothForm.coe_mpullback,
      ← mpullback_inclusion_apply h (RoughForm.wedge φ.1 _), mpullback_wedge,
      compactlySupportedForms.coe_extendByZero, RoughForm.mpullback_inclusion_extendByZero]
  · rw [RoughForm.extendByZero_apply_of_notMem _ hz, RoughForm.wedge_def,
      RoughForm.wedgeWith_apply', compactlySupportedForms.coe_extendByZero,
      RoughForm.extendByZero_apply_of_notMem _ hz,
      ContinuousAlternatingMap.pairedWedge_zero_right]

omit [BoundarylessManifold I M] in
private theorem integralTopForm_wedge_extendByZero {U W : Opens M} {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) (h : U ≤ W)
    (φ : SmoothForm I W ℝ a) (η : compactlySupportedForms I U b) :
    integralTopForm (o.restrict W)
        (RoughForm.wedge φ.1 (compactlySupportedForms.extendByZero h b η).1.1) =
      integralTopForm (o.restrict U)
        (RoughForm.wedge (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ).1
          η.1.1) := by
  let φU := SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ
  have hsupp : IsCompact
      (_root_.tsupport (α := E [⋀^Fin (a + b)]→L[ℝ] ℝ) (RoughForm.wedge φU.1 η.1.1)) := by
    rw [← SmoothForm.coe_wedge]
    exact (mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φU η.2)
  rw [roughForm_wedge_extendByZero_eq h φ η]
  exact integralTopForm_extendByZero o h hsupp

omit [BoundarylessManifold I M] in
private def integralWedgeCompactlySupported {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b))) :
    SmoothForm I M ℝ a →ₗ[ℝ] compactlySupportedForms I M b →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun φ η ↦ integralTopForm o (SmoothForm.wedge φ η.1).1)
    (fun φ φ' η ↦ by
      rw [LinearMap.map_add₂, Submodule.coe_add]
      exact integralTopForm_add o
        ((SmoothForm.wedge φ η.1).isSmoothForm.of_le (by simp))
        ((SmoothForm.wedge φ' η.1).isSmoothForm.of_le (by simp))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ η.2))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ' η.2)))
    (fun c φ η ↦ by
      rw [LinearMap.map_smul₂, Submodule.coe_smul]
      exact integralTopForm_smul o c (SmoothForm.wedge φ η.1).1)
    (fun φ η η' ↦ by
      rw [Submodule.coe_add, map_add, Submodule.coe_add]
      exact integralTopForm_add o
        ((SmoothForm.wedge φ η.1).isSmoothForm.of_le (by simp))
        ((SmoothForm.wedge φ η'.1).isSmoothForm.of_le (by simp))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ η.2))
        ((mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms φ η'.2)))
    (fun c φ η ↦ by
      rw [Submodule.coe_smul, map_smul, Submodule.coe_smul]
      exact integralTopForm_smul o c (SmoothForm.wedge φ η.1).1)

omit [BoundarylessManifold I M] [T2Space M] in
private theorem integralWedgeCompactlySupported_apply {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b)))
    (φ : SmoothForm I M ℝ a) (η : compactlySupportedForms I M b) :
    integralWedgeCompactlySupported o φ η =
      integralTopForm o (RoughForm.wedge φ.1 η.1.1) := by
  rw [integralWedgeCompactlySupported, LinearMap.mk₂_apply, SmoothForm.coe_wedge]

omit [BoundarylessManifold I M] [T2Space M] in
private theorem integralWedgeCompactlySupported_neg {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b)))
    (φ : SmoothForm I M ℝ a) (η : compactlySupportedForms I M b) :
    integralWedgeCompactlySupported o φ (-η) = -integralWedgeCompactlySupported o φ η := by
  have h : -η = (-1 : ℝ) • η := Subtype.ext <| Subtype.ext <| by
    rw [Submodule.coe_neg, Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_smul,
      neg_smul, one_smul]
  rw [h, (integralWedgeCompactlySupported o φ).map_smul, smul_eq_mul, neg_one_mul]

omit [BoundarylessManifold I M] [T2Space M] in
private theorem integralWedgeCompactlySupported_sub {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b)))
    (φ₁ φ₂ : SmoothForm I M ℝ a) (η : compactlySupportedForms I M b) :
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
    integralWedgeCompactlySupported (o.restrict W) φ
        (compactlySupportedForms.extendByZero h b η) =
      integralWedgeCompactlySupported (o.restrict U)
        (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ) η := by
  rw [integralWedgeCompactlySupported_apply, integralWedgeCompactlySupported_apply]
  exact integralTopForm_wedge_extendByZero o h φ η

private theorem integralWedgeCompactlySupported_mextDeriv [SigmaCompactSpace M] {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (α : SmoothForm I M ℝ j) (γ : compactlySupportedForms I M l) :
    integralWedgeCompactlySupported o (mextDerivₗ I j α) γ =
      (-1 : ℝ) ^ (j + 1) *
        integralWedgeCompactlySupported (o.reindex (finCongr hjl)) α
          (compactlySupportedForms.mextDerivₗ I M l γ) := by
  rw [integralWedgeCompactlySupported_apply, integralWedgeCompactlySupported_apply]
  exact integralTopForm_mextDeriv_wedge_eq hjl o α γ

private theorem integralTopForm_mayerVietoris_step {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    (φ : SmoothForm I (U ⊓ V : Opens M) ℝ j)
    (α : SmoothForm I U ℝ j) (β : SmoothForm I V ℝ j)
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
    integralTopForm (o.restrict (U ⊔ V))
        (RoughForm.wedge σ.1
          (compactlySupportedForms.extendByZero (le_sup_left : U ≤ U ⊔ V) l γ +
            compactlySupportedForms.extendByZero (le_sup_right : V ≤ U ⊔ V) l δ).1.1) =
      (-1 : ℝ) ^ (j + 1) *
        integralTopForm ((o.reindex (finCongr hjl)).restrict (U ⊓ V))
          (RoughForm.wedge φ.1 τ.1.1) := by
  rw [← integralWedgeCompactlySupported_apply,
    (integralWedgeCompactlySupported (o.restrict (U ⊔ V)) σ).map_add,
    integralWedgeCompactlySupported_extendByZero o le_sup_left σ γ,
    integralWedgeCompactlySupported_extendByZero o le_sup_right σ δ,
    hσU, hσV,
    integralWedgeCompactlySupported_mextDeriv hjl (o.restrict U) α γ,
    integralWedgeCompactlySupported_mextDeriv hjl (o.restrict V) β δ,
    orientation_restrict_reindex, orientation_restrict_reindex]
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
    ← mul_add, ← sub_eq_add_neg, ← integralWedgeCompactlySupported_sub,
    hαβ, integralWedgeCompactlySupported_apply]

/-- **Compatibility of the Poincaré pairing with the Mayer–Vietoris connecting maps.** On open
subsets `U, V` of an oriented boundaryless Hausdorff σ-compact smooth manifold, the Poincaré
pairing on `U ⊔ V` intertwines `deRhamCohomology.mayerVietorisδ` with `(-1) ^ (j + 1)` times
`compactlySupportedDeRhamCohomology.mayerVietorisδ` on `U ⊓ V`. -/
theorem poincarePairing_mayerVietorisδ [SigmaCompactSpace M] {j l : ℕ}
    (hjl : (j + 1) + l = j + (l + 1)) (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (U V : Opens M) [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    (x : deRhamCohomology I (U ⊓ V : Opens M) j)
    (y : compactlySupportedDeRhamCohomology I (U ⊔ V : Opens M) l) :
    poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))
        (deRhamCohomology.mayerVietorisδ I U V j x) y =
      (-1 : ℝ) ^ (j + 1) *
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

/-! ### Binary-union Mayer–Vietoris step for Poincaré duality -/

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
private theorem bijective_prodPoincarePairing (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] {a b : ℕ}
    (o : Manifold.Orientation I M (Fin (a + b)))
    (hU : Bijective (poincarePairing I U (o.restrict U)))
    (hV : Bijective (poincarePairing I V (o.restrict V))) :
    Bijective (prodPoincarePairing U V o) :=
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
          (contMDiff_inclusion _) a)) := by
  refine LinearMap.ext fun c ↦ LinearMap.ext fun ⟨u, v⟩ ↦ ?_
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
          (contMDiff_inclusion _) a)) := by
  refine LinearMap.ext fun ⟨cU, cV⟩ ↦ LinearMap.ext fun z ↦ ?_
  simp [prodPoincarePairing, poincarePairing_extendByZero]

private theorem bijective_poincarePairing_sup_zero (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    {l : ℕ} (o : Manifold.Orientation I M (Fin (0 + l)))
    (hU : Bijective (poincarePairing I U (o.restrict U)))
    (hV : Bijective (poincarePairing I V (o.restrict V)))
    (hUV : Bijective (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))) :
    Bijective (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) := by
  have hl : Module.finrank ℝ E < l + 1 := by
    have hcard := o.card_eq
    rw [Fintype.card_fin] at hcard
    omega
  have : Subsingleton (compactlySupportedDeRhamCohomology I (U ⊓ V : Opens M) (l + 1)) :=
    subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt I (U ⊓ V : Opens M) hl
  have hsurj : Surjective
      ((compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (le_sup_left : U ≤ U ⊔ V) l).coprod
        (compactlySupportedDeRhamCohomology.extendByZero (I := I)
           (le_sup_right : V ≤ U ⊔ V) l)) := fun y ↦
    (compactlySupportedDeRhamCohomology.exact_mayerVietoris₃ U V l y).mp
      (Subsingleton.elim _ 0)
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact _ _ _ _
    (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V)))
    (prodPoincarePairing U V o)
    (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))
    (comm_poincarePairing_sup_prod U V o)
    (comm_poincarePairing_prod_inf U V o)
    (deRhamCohomology.exact_mayerVietoris₂ U V 0)
    (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₂ U V l))
    (bijective_prodPoincarePairing U V o hU hV)
    hUV.1
    (deRhamCohomology.injective_mayerVietoris_zero U V)
    (LinearMap.dualMap_injective_of_surjective hsurj)

private theorem bijective_poincarePairing_sup_succ (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V]
    [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]
    {j l : ℕ} (o : Manifold.Orientation I M (Fin ((j + 1) + l)))
    (hU₀ : Bijective (poincarePairing I U
      ((o.reindex (finCongr (by omega : (j + 1) + l = j + (l + 1)))).restrict U)))
    (hV₀ : Bijective (poincarePairing I V
      ((o.reindex (finCongr (by omega : (j + 1) + l = j + (l + 1)))).restrict V)))
    (hUV₀ : Bijective (poincarePairing I (U ⊓ V : Opens M)
      ((o.reindex (finCongr (by omega : (j + 1) + l = j + (l + 1)))).restrict (U ⊓ V))))
    (hU₁ : Bijective (poincarePairing I U (o.restrict U)))
    (hV₁ : Bijective (poincarePairing I V (o.restrict V)))
    (hUV₁ : Bijective (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))) :
    Bijective (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))) := by
  have hjl : (j + 1) + l = j + (l + 1) := by omega
  let o' := o.reindex (finCongr hjl)
  let s : ℝ := (-1 : ℝ) ^ (j + 1)
  have hc₁ : ((compactlySupportedDeRhamCohomology.extendByZero (I := I)
        (inf_le_left : U ⊓ V ≤ U) (l + 1)).prod
        (-compactlySupportedDeRhamCohomology.extendByZero (I := I)
          (inf_le_right : U ⊓ V ≤ V) (l + 1))).dualMap.comp
      (s • prodPoincarePairing U V o') =
      (s • poincarePairing I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V))).comp
        ((deRhamCohomology.map (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
            (contMDiff_inclusion _) j).coprod
          (-deRhamCohomology.map (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
            (contMDiff_inclusion _) j)) := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp, comm_poincarePairing_prod_inf U V o']
  have hc₂ : (compactlySupportedDeRhamCohomology.mayerVietorisδ I U V l).dualMap.comp
      (s • poincarePairing I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V))) =
      (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V))).comp
        (deRhamCohomology.mayerVietorisδ I U V j) := by
    refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.smul_apply,
      smul_eq_mul, s, o'] using (poincarePairing_mayerVietorisδ hjl o U V x y).symm
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    _ _ _ _ _ _ _ _
    (s • prodPoincarePairing U V o')
    (s • poincarePairing I (U ⊓ V : Opens M) (o'.restrict (U ⊓ V)))
    (poincarePairing I (U ⊔ V : Opens M) (o.restrict (U ⊔ V)))
    (prodPoincarePairing U V o)
    (poincarePairing I (U ⊓ V : Opens M) (o.restrict (U ⊓ V)))
    hc₁ hc₂
    (comm_poincarePairing_sup_prod U V o)
    (comm_poincarePairing_prod_inf U V o)
    (deRhamCohomology.exact_mayerVietoris₃ U V j)
    (deRhamCohomology.exact_mayerVietoris₁ U V j)
    (deRhamCohomology.exact_mayerVietoris₂ U V (j + 1))
    (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₁ U V l))
    (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₃ U V l))
    (exact_dualMap (compactlySupportedDeRhamCohomology.exact_mayerVietoris₂ U V l))
    (bijective_neg_one_pow_smul (j + 1) (bijective_prodPoincarePairing U V o' hU₀ hV₀)).2
    (bijective_neg_one_pow_smul (j + 1) hUV₀)
    (bijective_prodPoincarePairing U V o hU₁ hV₁)
    hUV₁.1

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
  cases a with
  | zero =>
    exact bijective_poincarePairing_sup_zero U V (o.reindex (finCongr hab.symm))
      (hU 0 b hab) (hV 0 b hab) (hUV 0 b hab)
  | succ j =>
    have hjb : j + (b + 1) = n := by omega
    have hre : (o.reindex (finCongr hab.symm)).reindex
        (finCongr (by omega : (j + 1) + b = j + (b + 1))) =
        o.reindex (finCongr hjb.symm) :=
      orientation_reindex_trans _ _ o
    exact bijective_poincarePairing_sup_succ U V (o.reindex (finCongr hab.symm))
      (hre.symm ▸ hU j (b + 1) hjb)
      (hre.symm ▸ hV j (b + 1) hjb)
      (hre.symm ▸ hUV j (b + 1) hjb)
      (hU (j + 1) b hab) (hV (j + 1) b hab) (hUV (j + 1) b hab)

end MayerVietorisStep

/-! ### Base cases: empty manifolds, diffeomorphisms, normed spaces, and open boxes -/

section BaseCases

private theorem bijective_poincarePairing_of_isEmpty
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] [IsEmpty M] {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    Bijective (poincarePairing I M o) := by
  have : Subsingleton (SmoothForm I M ℝ k) :=
    ⟨fun φ ψ ↦ Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  have : Subsingleton (deRhamCohomology I M k) :=
    (deRhamCohomology.mk_surjective I k).subsingleton
  have : Subsingleton (SmoothForm I M ℝ l) :=
    ⟨fun φ ψ ↦ Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  have : Subsingleton (compactlySupportedDeRhamCohomology I M l) :=
    (compactlySupportedDeRhamCohomology.mk_surjective I l).subsingleton
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private theorem bijective_poincarePairing_iff_of_isOrientationPreserving
    {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
    {k l : ℕ} (Φ : M ≃ₘ⟮I, J⟯ N) (o : Manifold.Orientation I M (Fin (k + l)))
    (o' : Manifold.Orientation J N (Fin (k + l)))
    (hpres : ∀ x : M, o.IsOrientationPreservingAt o' Φ x) :
    Bijective (poincarePairing I M o) ↔ Bijective (poincarePairing J N o') := by
  let e₁ := deRhamCohomology.equivOfDiffeomorph Φ k
  let e₂ := compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ l
  have hcomm : ∀ x, poincarePairing I M o x =
      e₂.symm.dualMap (poincarePairing J N o' (e₁.symm x)) := fun x ↦ LinearMap.ext fun y ↦ by
    simp only [LinearEquiv.dualMap_apply, e₁, e₂]
    have h := poincarePairing_map_diffeomorph o o' Φ hpres (e₁.symm x) (e₂.symm y)
    have hx : deRhamCohomology.map Φ Φ.contMDiff k (e₁.symm x) = x :=
      (deRhamCohomology.equivOfDiffeomorph_apply Φ k _).symm.trans (e₁.apply_symm_apply x)
    have hy : compactlySupportedDeRhamCohomology.map Φ Φ.contMDiff
        (by simpa only [Diffeomorph.coe_toHomeomorph] using Φ.toHomeomorph.isProperMap)
        l (e₂.symm y) = y :=
      (compactlySupportedDeRhamCohomology.equivOfDiffeomorph_apply Φ l _).symm.trans
        (e₂.apply_symm_apply y)
    rw [hx, hy] at h
    exact h
  have hfn : ⇑(poincarePairing I M o) = ⇑e₂.symm.dualMap ∘ ⇑(poincarePairing J N o') ∘ ⇑e₁.symm :=
    funext hcomm
  have hfn' : ⇑(poincarePairing J N o') = ⇑e₂.dualMap ∘ ⇑(poincarePairing I M o) ∘ ⇑e₁ :=
    funext fun z ↦ LinearMap.ext fun w ↦ by
      simp [hcomm (e₁ z)]
  exact ⟨fun hM ↦ hfn' ▸ e₂.dualMap.bijective.comp (hM.comp e₁.bijective),
    fun hN ↦ hfn ▸ e₂.symm.dualMap.bijective.comp (hN.comp e₁.symm.bijective)⟩

private theorem bijective_poincarePairing_of_diffeomorph
    {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
    {k l : ℕ} (Φ : M ≃ₘ⟮I, J⟯ N) (o : Manifold.Orientation I M (Fin (k + l)))
    (hN : ∀ o' : Manifold.Orientation J N (Fin (k + l)), Bijective (poincarePairing J N o')) :
    Bijective (poincarePairing I M o) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact bijective_poincarePairing_of_isEmpty o
  · obtain ⟨x₀⟩ := hM
    have hdim : Fintype.card (Fin (k + l)) = Module.finrank ℝ E' :=
      o.card_eq.trans (Φ.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv.finrank_eq
    let o' : Manifold.Orientation J N (Fin (k + l)) :=
      o.pullback (Φ.symm.contMDiff.of_le (by simp))
        (fun y ↦ Φ.symm.isInvertible_mfderiv (by simp)) hdim
    exact (bijective_poincarePairing_iff_of_isOrientationPreserving Φ.symm o' o
      (Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _)).mp (hN o')

/-- **Poincaré duality on a finite-dimensional real normed space.** -/
theorem bijective_poincarePairing_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k l : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin (k + l))) :
    Bijective (poincarePairing 𝓘(ℝ, E) E o) := by
  have hdim : k + l = Module.finrank ℝ E := by
    simpa only [Fintype.card_fin] using o.card_eq
  cases k with
  | zero =>
    have hconst_bij : Bijective (deRhamCohomology.const 𝓘(ℝ, E) E) :=
      ⟨deRhamCohomology.const_injective, fun c ↦ by
        obtain ⟨r, hr⟩ := deRhamCohomology.exists_eq_const c
        exact ⟨r, hr.symm⟩⟩
    let eC := LinearEquiv.ofBijective _ hconst_bij
    let eI := LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.bijective_integral (o.reindex (finCongr (zero_add l))))
    let eR : ℝ ≃ₗ[ℝ] Module.Dual ℝ ℝ := (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm
    have hcomm : (poincarePairing 𝓘(ℝ, E) E o).comp eC.toLinearMap =
        eI.dualMap.toLinearMap.comp eR.toLinearMap := by
      refine LinearMap.ext fun r ↦ LinearMap.ext fun y ↦ ?_
      simp [eC, eI, eR, poincarePairing_const_left, mul_comm]
    have hbij : Bijective (poincarePairing 𝓘(ℝ, E) E o ∘ eC) := by
      change Bijective ((poincarePairing 𝓘(ℝ, E) E o).comp eC.toLinearMap)
      rw [hcomm]
      exact eI.dualMap.bijective.comp eR.bijective
    exact (Bijective.of_comp_iff (poincarePairing 𝓘(ℝ, E) E o) eC.bijective).mp hbij
  | succ j =>
    have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) E (j + 1)) :=
      subsingleton_deRhamCohomology_normedSpace (E := E) j
    have : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E l) :=
      subsingleton_compactlySupportedDeRhamCohomology_normedSpace E (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private def openBox {d : ℕ} (a b : Fin d → ℝ) : Opens (EuclideanSpace ℝ (Fin d)) :=
  ⟨{x | ∀ i, EuclideanSpace.equiv (Fin d) ℝ x i ∈ Ioo (a i) (b i)}, by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioo.preimage ((continuous_apply i).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous)⟩

private theorem openBox_inf_openBox {d : ℕ} (a₁ b₁ a₂ b₂ : Fin d → ℝ) :
    openBox a₁ b₁ ⊓ openBox a₂ b₂ =
      openBox (fun i ↦ max (a₁ i) (a₂ i)) (fun i ↦ min (b₁ i) (b₂ i)) := by
  ext x
  change (∀ i, EuclideanSpace.equiv (Fin d) ℝ x i ∈ Ioo (a₁ i) (b₁ i)) ∧
      (∀ i, EuclideanSpace.equiv (Fin d) ℝ x i ∈ Ioo (a₂ i) (b₂ i)) ↔
    ∀ i, EuclideanSpace.equiv (Fin d) ℝ x i ∈ Ioo (max (a₁ i) (a₂ i)) (min (b₁ i) (b₂ i))
  simp only [← forall_and, ← mem_inter_iff, Ioo_inter_Ioo]

private theorem isBasis_openBoxes (d : ℕ) :
    Opens.IsBasis {U : Opens (EuclideanSpace ℝ (Fin d)) | ∃ a b, U = openBox a b} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  let L := EuclideanSpace.equiv (Fin d) ℝ
  have hopen : IsOpen (L.symm ⁻¹' (U : Set (EuclideanSpace ℝ (Fin d)))) :=
    U.isOpen.preimage L.symm.continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (L x) hx
  refine ⟨openBox (fun i ↦ L x i - r) (fun i ↦ L x i + r), ⟨_, _, rfl⟩,
    fun i ↦ ⟨sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩, fun y hy ↦ ?_⟩
  have hyb : L y ∈ Metric.ball (L x) r := by
    rw [ball_pi _ hr]
    intro i _
    dsimp only
    rw [Real.ball_eq_Ioo]
    exact hy i
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
  have hmem (v : EuclideanSpace ℝ (Fin d)) :
      L.symm (fun i ↦ e i (L v i)) ∈ openBox a b := fun i ↦ by
    change L (L.symm (fun j ↦ e j (L v j))) i ∈ Ioo (a i) (b i)
    rw [L.apply_symm_apply, ← htarget i]
    exact (e i).map_source (by simp [e])
  let equivBox : EuclideanSpace ℝ (Fin d) ≃ openBox a b :=
    { toFun := fun v ↦ ⟨L.symm (fun i ↦ e i (L v i)), hmem v⟩
      invFun := fun u ↦ L.symm (fun i ↦ (e i).symm (L u.1 i))
      left_inv := fun v ↦ L.injective <| funext fun i ↦ by
        simp only [L.apply_symm_apply]
        exact (e i).left_inv (by simp [e])
      right_inv := fun u ↦ Subtype.ext <| L.injective <| funext fun i ↦ by
        simp only [L.apply_symm_apply]
        exact (e i).right_inv (htarget i ▸ u.2 i) }
  refine
    { toEquiv := equivBox
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
      contMDiff_invFun := ?_ }
  · refine L.symm.contDiff.contMDiff.comp (contMDiff_pi_module_iff.mpr fun i ↦ ?_)
    exact OpenPartialHomeomorph.contDiff_univBall.contMDiff.comp
      (((ContinuousLinearMap.proj (R := ℝ) i).comp
        (L : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))).contMDiff)
  · refine L.symm.contDiff.contMDiff.comp (contMDiff_pi_module_iff.mpr fun i ↦ ?_)
    have hcd : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (e i).symm (Ioo (a i) (b i)) := by
      rw [← htarget i, OpenPartialHomeomorph.univBall_target _ (hr i)]
      exact (OpenPartialHomeomorph.contDiffOn_univBall_symm (n := (⊤ : ℕ∞))).contMDiffOn
    exact hcd.comp_contMDiff
      ((((ContinuousLinearMap.proj (R := ℝ) i).comp
        (L : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))).contMDiff).comp contMDiff_subtype_val)
      fun u ↦ u.2 i

private theorem bijective_poincarePairing_opens_euclideanSpace {d n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) (Fin n))
    (W : Opens (EuclideanSpace ℝ (Fin d))) [SigmaCompactSpace W] :
    ∀ (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) W
        ((o.reindex (finCongr hab.symm)).restrict W)) := by
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
  let P (U : Opens (EuclideanSpace ℝ (Fin d))) : Prop :=
    ∀ [SigmaCompactSpace U] (a b : ℕ) (hab : a + b = n),
      Bijective (poincarePairing J U ((o.reindex (finCongr hab.symm)).restrict U))
  have hPW : P W := mayerVietoris_induction P {U | ∃ a b, U = openBox a b} (isBasis_openBoxes d)
    (by rintro _ ⟨a₁, b₁, rfl⟩ _ ⟨a₂, b₂, rfl⟩; exact ⟨_, _, openBox_inf_openBox a₁ b₁ a₂ b₂⟩)
    (by
      intro _ a b hab
      have : IsEmpty (⊥ : Opens (EuclideanSpace ℝ (Fin d))) := isEmpty_coe_sort.mpr rfl
      exact bijective_poincarePairing_of_isEmpty _)
    (by
      rintro U ⟨p, q, rfl⟩ _ a b hab
      by_cases hpq : ∀ i, p i < q i
      · exact bijective_poincarePairing_of_diffeomorph (diffeomorphOpenBox hpq).symm _
          fun o' ↦ bijective_poincarePairing_normedSpace _ o'
      · push Not at hpq
        obtain ⟨i, hi⟩ := hpq
        have : IsEmpty (openBox p q) :=
          ⟨fun x ↦ (lt_irrefl _ ((x.2 i).1.trans_le ((x.2 i).2.le.trans hi))).elim⟩
        exact bijective_poincarePairing_of_isEmpty _)
    (by
      intro U V hU hV hUV _ a b hab
      have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
      have : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
      have : LocallyCompactSpace (U ⊓ V : Opens (EuclideanSpace ℝ (Fin d))) :=
        (U ⊓ V : Opens _).isOpen.locallyCompactSpace
      exact bijective_poincarePairing_sup o U V hU hV hUV a b hab)
    (by
      intro s hs hPs _ a b hab
      have (m : ℕ) : LocallyCompactSpace (s m) := (s m).isOpen.locallyCompactSpace
      exact bijective_poincarePairing_iSup (o.reindex (finCongr hab.symm)) hs
        fun m ↦ hPs m a b hab) W
  exact fun a b hab ↦ hPW a b hab

end BaseCases

/-! ### Global Poincaré duality on boundaryless Hausdorff σ-compact manifolds -/

section GlobalDuality

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- Restricting a chart diffeomorphism `Φ : U ≃ₘ ℝ^d` to an open subset `W ≤ U` transports
Poincaré duality from the image open subset of `ℝ^d` back to `W`. -/
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
  let equivWV : W ≃ V :=
    { toFun := fun w ↦ ⟨Φ ⟨w.1, hWU w.2⟩, by simp [V, Φ.symm_apply_apply]⟩
      invFun := fun v ↦ ⟨(Φ.symm v.1).1, v.2⟩
      left_inv := fun w ↦ Subtype.ext <| by
        dsimp only
        exact congrArg Subtype.val (Φ.symm_apply_apply ⟨w.1, hWU w.2⟩)
      right_inv := fun v ↦ Subtype.ext (Φ.apply_symm_apply v.1) }
  have hinv_cmd : ContMDiff J I ∞ (Subtype.val ∘ ⇑equivWV.symm) :=
    (contMDiff_subtype_val (I := I) (U := U)).comp (Φ.symm.contMDiff.comp contMDiff_subtype_val)
  let Ψ : W ≃ₘ⟮I, J⟯ V :=
    { toEquiv := equivWV
      contMDiff_toFun :=
        (ContMDiff.subtypeVal_comp_iff _ _).mp (Φ.contMDiff.comp (contMDiff_inclusion hWU))
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp hinv_cmd }
  let oE : Manifold.Orientation J (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (Fin (a + b)) :=
    (oM.restrict U).pullback (Φ.symm.contMDiff.of_le (by simp))
      (fun z ↦ Φ.symm.isInvertible_mfderiv (by simp))
      (oM.card_eq.trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := Module.finrank ℝ E)).symm)
  have hΨ_pres : ∀ w : W, (oM.restrict W).IsOrientationPreservingAt (oE.restrict V) Ψ w := by
    intro w
    have hcomp : ((Subtype.val : U → M) ∘ Φ.symm ∘ (Subtype.val : V → _)) ∘ Ψ =
        (Subtype.val : W → M) :=
      funext fun z ↦ congrArg Subtype.val (Φ.symm_apply_apply ⟨z.1, hWU z.2⟩)
    have h₁ : (oE.restrict V).IsOrientationPreservingAt oM
        ((Subtype.val : U → M) ∘ Φ.symm ∘ (Subtype.val : V → _)) (Ψ w) :=
      (oM.isOrientationPreservingAt_restrict U _).comp
        ((Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _ _).comp
          (oE.isOrientationPreservingAt_restrict V (Ψ w)))
    have h₂ : (oM.restrict W).IsOrientationPreservingAt oM
        (((Subtype.val : U → M) ∘ Φ.symm ∘ (Subtype.val : V → _)) ∘ Ψ) w :=
      hcomp.symm ▸ oM.isOrientationPreservingAt_restrict W w
    exact h₁.of_comp h₂ (Ψ.contMDiff.mdifferentiableAt (by simp))
  have hV_bij : Bijective (poincarePairing J V (oE.restrict V)) := by
    simpa only [finCongr_refl, orientation_reindex_refl] using
      bijective_poincarePairing_opens_euclideanSpace oE V a b rfl
  exact (bijective_poincarePairing_iff_of_isOrientationPreserving Ψ _ _ hΨ_pres).mpr hV_bij

/-- **De Rham Poincaré duality.** On an oriented boundaryless Hausdorff σ-compact finite-dimensional
smooth manifold `M` of dimension `k + l`, with no compactness hypothesis, the Poincaré pairing
`TauCeti.poincarePairing I M o` is a bijection from `H^k_dR(M)` onto the dual of `H^l_c(M)`. -/
theorem bijective_poincarePairing [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    Function.Bijective (poincarePairing I M o :
      deRhamCohomology I M k →
        Module.Dual ℝ (compactlySupportedDeRhamCohomology I M l)) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose U hxU hΦ using fun x : M ↦
    exists_opens_diffeomorph_euclideanSpace (n := ⊤)
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  have hB : Opens.IsBasis {W : Opens M | ∃ x : M, W ≤ U x} := by
    rw [Opens.isBasis_iff_nbhd]
    exact fun {W x} hxW ↦ ⟨W ⊓ U x, ⟨x, inf_le_right⟩, ⟨hxW, hxU x⟩, inf_le_left⟩
  let P (W : Opens M) : Prop :=
    ∀ [SigmaCompactSpace W] (a b : ℕ) (hab : a + b = k + l),
      Bijective (poincarePairing I W ((o.reindex (finCongr hab.symm)).restrict W))
  have htop : P ⊤ := mayerVietoris_induction P {W | ∃ x : M, W ≤ U x} hB
    (fun _ ⟨x, hx⟩ _ _ ↦ ⟨x, inf_le_left.trans hx⟩)
    (by
      intro _ a b hab
      have : IsEmpty (⊥ : Opens M) := isEmpty_coe_sort.mpr rfl
      exact bijective_poincarePairing_of_isEmpty _)
    (by
      rintro W ⟨x, hW⟩ _ a b hab
      exact bijective_poincarePairing_of_le_diffeomorph_euclideanSpace hW (hΦ x).some
        (o.reindex (finCongr hab.symm)))
    (by
      intro W₁ W₂ h₁ h₂ h₁₂ _ a b hab
      have : LocallyCompactSpace W₁ := W₁.isOpen.locallyCompactSpace
      have : LocallyCompactSpace W₂ := W₂.isOpen.locallyCompactSpace
      have : LocallyCompactSpace (W₁ ⊓ W₂ : Opens M) :=
        (W₁ ⊓ W₂ : Opens M).isOpen.locallyCompactSpace
      exact bijective_poincarePairing_sup o W₁ W₂ h₁ h₂ h₁₂ a b hab)
    (by
      intro s hs hPs _ a b hab
      have (m : ℕ) : LocallyCompactSpace (s m) := (s m).isOpen.locallyCompactSpace
      exact bijective_poincarePairing_iSup (o.reindex (finCongr hab.symm)) hs
        fun m ↦ hPs m a b hab) ⊤
  have : LocallyCompactSpace (⊤ : Opens M) := (⊤ : Opens M).isOpen.locallyCompactSpace
  have htop_kl : Bijective (poincarePairing I (⊤ : Opens M) (o.restrict ⊤)) := by
    simpa only [finCongr_refl, orientation_reindex_refl] using htop k l rfl
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  have hΦ_pres : ∀ z : (⊤ : Opens M), (o.restrict ⊤).IsOrientationPreservingAt o Φ z := fun z ↦ by
    rw [Diffeomorph.coe_ofTop]
    exact o.isOrientationPreservingAt_restrict ⊤ z
  exact (bijective_poincarePairing_iff_of_isOrientationPreserving Φ _ _ hΦ_pres).mp htop_kl

end GlobalDuality

/-! ### Bundled Poincaré duality equivalence and nondegeneracy -/

section BundledAPI

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] {k l : ℕ}

/-- **De Rham Poincaré duality** as a linear equivalence `H^k_dR(M) ≃ₗ[ℝ] (H^l_c(M))^*` on an
oriented boundaryless Hausdorff σ-compact finite-dimensional smooth manifold of dimension
`k + l`. -/
def poincareDuality (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k ≃ₗ[ℝ]
      Module.Dual ℝ (compactlySupportedDeRhamCohomology I M l) :=
  LinearEquiv.ofBijective (poincarePairing I M o) (bijective_poincarePairing o)

/-- `TauCeti.poincareDuality` evaluates as `TauCeti.poincarePairing`. -/
@[simp]
theorem poincareDuality_apply (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) (y : compactlySupportedDeRhamCohomology I M l) :
    poincareDuality o x y = poincarePairing I M o x y :=
  (rfl)

/-- The underlying linear map of `TauCeti.poincareDuality` is `TauCeti.poincarePairing`. -/
@[simp]
theorem poincareDuality_toLinearMap (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincareDuality o).toLinearMap = poincarePairing I M o :=
  (rfl)

/-- Reversing the orientation negates `TauCeti.poincareDuality`. -/
@[simp]
theorem poincareDuality_neg (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) :
    poincareDuality (-o) x = -poincareDuality o x := by
  ext y
  simp [poincareDuality_apply]

/-- The Poincaré pairing is left-separating: a class in `H^k_dR(M)` that pairs to zero with every
class in `H^l_c(M)` vanishes. -/
theorem poincarePairing_separatingLeft (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).SeparatingLeft :=
  LinearMap.separatingLeft_iff_ker_eq_bot.mpr
    (LinearMap.ker_eq_bot_of_injective (bijective_poincarePairing o).injective)

/-- The Poincaré pairing is right-separating: a class in `H^l_c(M)` on which every class in
`H^k_dR(M)` pairs to zero vanishes. -/
theorem poincarePairing_separatingRight (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).SeparatingRight := by
  intro y hy
  refine (Module.forall_dual_apply_eq_zero_iff ℝ y).mp fun φ ↦ ?_
  obtain ⟨x, rfl⟩ := (bijective_poincarePairing o).surjective φ
  exact hy x

/-- **Nondegeneracy of the Poincaré pairing** in both arguments. -/
theorem poincarePairing_nondegenerate (o : Manifold.Orientation I M (Fin (k + l))) :
    (poincarePairing I M o).Nondegenerate :=
  ⟨poincarePairing_separatingLeft o, poincarePairing_separatingRight o⟩

/-- If `x ∈ H^k_dR(M)` pairs to zero with every `y ∈ H^l_c(M)`, then `x = 0`. -/
theorem eq_zero_of_forall_poincarePairing_eq_zero_left
    (o : Manifold.Orientation I M (Fin (k + l))) {x : deRhamCohomology I M k}
    (hx : ∀ y, poincarePairing I M o x y = 0) : x = 0 :=
  poincarePairing_separatingLeft o x hx

/-- If every `x ∈ H^k_dR(M)` pairs to zero with `y ∈ H^l_c(M)`, then `y = 0`. -/
theorem eq_zero_of_forall_poincarePairing_eq_zero_right
    (o : Manifold.Orientation I M (Fin (k + l))) {y : compactlySupportedDeRhamCohomology I M l}
    (hy : ∀ x, poincarePairing I M o x y = 0) : y = 0 :=
  poincarePairing_separatingRight o y hy

end BundledAPI

/-! ### Corollaries on compact boundaryless manifolds -/

section CompactManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- On a compact oriented boundaryless manifold of dimension `k + l`, Poincaré duality identifies
`H^k_dR(M)` with the dual of `H^l_dR(M)`. -/
def poincareDualityCompact {k l : ℕ} (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k ≃ₗ[ℝ] Module.Dual ℝ (deRhamCohomology I M l) :=
  (poincareDuality o).trans
    (LinearEquiv.ofBijective _
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
    have hinf_l : Cardinal.aleph0 ≤ Module.rank ℝ (deRhamCohomology I M l) :=
      hinf.trans (h₁.le.trans_eq e₂.symm.rank_eq)
    have h₂ : Module.rank ℝ (deRhamCohomology I M l) <
        Module.rank ℝ (Module.Dual ℝ (deRhamCohomology I M l)) := by
      simpa only [Cardinal.lift_id'] using lift_rank_lt_rank_dual hinf_l
    exact lt_irrefl (Module.rank ℝ (deRhamCohomology I M k))
      ((h₁.trans_eq e₂.symm.rank_eq).trans (h₂.trans_eq e₁.symm.rank_eq))
  · push Not at hk
    have : Subsingleton (deRhamCohomology I M k) :=
      subsingleton_deRhamCohomology_of_finrank_lt I M hk
    infer_instance

/-- **Finite-dimensionality of de Rham cohomology on a compact boundaryless manifold.** No
orientability hypothesis is needed: pullback to the orientation double cover is injective on
de Rham cohomology, and the orientation double cover of a compact manifold is compact and
canonically oriented. -/
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
finite-dimensional in every degree. -/
instance finiteDimensional_compactlySupportedDeRhamCohomology (k : ℕ) :
    FiniteDimensional ℝ (compactlySupportedDeRhamCohomology I M k) :=
  FiniteDimensional.of_injective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k).injective

/-- **Betti-number symmetry on a compact oriented boundaryless manifold.** In complementary
degrees `k` and `l` on a compact oriented boundaryless manifold of dimension `k + l`,
`finrank ℝ H^k_dR(M) = finrank ℝ H^l_dR(M)`. -/
theorem finrank_deRhamCohomology_eq_of_orientation {k l : ℕ}
    (o : Manifold.Orientation I M (Fin (k + l))) :
    Module.finrank ℝ (deRhamCohomology I M k) = Module.finrank ℝ (deRhamCohomology I M l) :=
  (poincareDualityCompact o).finrank_eq.trans Subspace.dual_finrank_eq

variable (I M) in
/-- The compactly supported degree-zero cohomology class of a constant `r : ℝ` on a compact
manifold. -/
def compactlySupportedDeRhamCohomology.const :
    ℝ →ₗ[ℝ] compactlySupportedDeRhamCohomology I M 0 :=
  (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I
      (M := M) 0)).symm.toLinearMap.comp
    (deRhamCohomology.const I M)

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
/-- Forgetting compact support sends `compactlySupportedDeRhamCohomology.const` to
`deRhamCohomology.const`. -/
@[simp]
theorem compactlySupportedDeRhamCohomology.toDeRhamCohomology_const (r : ℝ) :
    compactlySupportedDeRhamCohomology.toDeRhamCohomology I M 0
        (compactlySupportedDeRhamCohomology.const I M r) =
      deRhamCohomology.const I M r :=
  (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I 0)).apply_symm_apply _

/-- Pairing `x ∈ H^k_dR(M)` with the compactly supported constant class `r` on a compact oriented
manifold multiplies the integral of `x` by `r`. -/
@[simp]
theorem poincarePairing_const_right {k : ℕ} (o : Manifold.Orientation I M (Fin (k + 0)))
    (x : deRhamCohomology I M k) (r : ℝ) :
    poincarePairing I M o x (compactlySupportedDeRhamCohomology.const I M r) =
      r * compactlySupportedDeRhamCohomology.integral (o.reindex (finCongr (Nat.add_zero k)))
        ((LinearEquiv.ofBijective _
          (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k)).symm x) := by
  set xc := (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k)).symm x
  have hxc : compactlySupportedDeRhamCohomology.toDeRhamCohomology I M k xc = x :=
    (LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I k)).apply_symm_apply x
  have hre : (o.reindex (finCongr (Nat.add_comm k 0))).reindex (finCongr (zero_add k)) =
      o.reindex (finCongr (Nat.add_zero k)) :=
    orientation_reindex_finCongr _ _ o
  rw [← hxc, poincarePairing_comm_toDeRhamCohomology,
    compactlySupportedDeRhamCohomology.toDeRhamCohomology_const, Nat.mul_zero, pow_zero, one_mul,
    poincarePairing_const_left, hre]

end CompactManifold

/-! ### Explicit evaluations on the circle and on the real line -/

section Examples

/-- On the counterclockwise circle `S¹`, the Poincaré pairing of the angular class `[dθ]` with the
constant class `[1]` is `2π`. -/
theorem poincarePairing_circleOrientation_circleAngularClosedForm_const_one :
    poincarePairing (𝓡 1) Circle (circleOrientation.reindex (finCongr (Nat.add_zero 1).symm))
        (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm)
        (compactlySupportedDeRhamCohomology.const (𝓡 1) Circle 1) =
      2 * Real.pi := by
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
  have hre : (circleOrientation.reindex (finCongr (Nat.add_zero 1).symm)).reindex
      (finCongr (Nat.add_zero 1)) = circleOrientation := by
    rw [orientation_reindex_finCongr, finCongr_refl, orientation_reindex_refl]
  rw [poincarePairing_const_right, one_mul, hmk, hre,
    compactlySupportedDeRhamCohomology.integral_mk]
  change integralTopForm circleOrientation
      ((circleAngularClosedForm : SmoothForm (𝓡 1) Circle ℝ 1) : RoughForm (𝓡 1) Circle ℝ 1) =
    2 * Real.pi
  rw [coe_circleAngularClosedForm]
  exact integralTopForm_circleOrientation_circleAngularForm

/-- For any orientation of `S¹`, the absolute value of the Poincaré pairing `⟨[dθ], [1]⟩` is
`2π`. -/
theorem abs_poincarePairing_circleAngularClosedForm_const_one
    (o : Manifold.Orientation (𝓡 1) Circle (Fin (1 + 0))) :
    |poincarePairing (𝓡 1) Circle o
        (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm)
        (compactlySupportedDeRhamCohomology.const (𝓡 1) Circle 1)| =
      2 * Real.pi := by
  let o₀ := circleOrientation.reindex (finCongr (Nat.add_zero 1).symm)
  rcases o.eq_or_eq_neg o₀ with rfl | rfl
  · rw [poincarePairing_circleOrientation_circleAngularClosedForm_const_one,
      abs_of_pos Real.two_pi_pos]
  · rw [poincarePairing_neg, LinearMap.neg_apply, LinearMap.neg_apply, abs_neg,
      poincarePairing_circleOrientation_circleAngularClosedForm_const_one,
      abs_of_pos Real.two_pi_pos]

/-- On the oriented real line `ℝ`, pairing `[1] ∈ H⁰_dR(ℝ)` with the compactly supported class of a
`1`-form `ψ` evaluates the Lebesgue integral `∫ t, ψ t (fun _ ↦ 1)`. -/
theorem poincarePairing_real_const_one_mk
    (ψ : compactlySupportedClosedForms 𝓘(ℝ, ℝ) ℝ 1) :
    poincarePairing 𝓘(ℝ, ℝ) ℝ
        (Manifold.Orientation.real.reindex (finCongr (zero_add 1).symm))
        (deRhamCohomology.const 𝓘(ℝ, ℝ) ℝ 1)
        (compactlySupportedDeRhamCohomology.mk 𝓘(ℝ, ℝ) 1 ψ) =
      ∫ t : ℝ, ψ.1.1 t (fun _ ↦ 1) := by
  have hψ := (mem_compactlySupportedClosedForms 𝓘(ℝ, ℝ)).mp ψ.2
  have hre : (Manifold.Orientation.real.reindex (finCongr (zero_add 1).symm)).reindex
      (finCongr (zero_add 1)) = Manifold.Orientation.real := by
    rw [orientation_reindex_finCongr, finCongr_refl, orientation_reindex_refl]
  rw [poincarePairing_const_one_left, hre, compactlySupportedDeRhamCohomology.integral_mk]
  exact integralTopForm_real_eq_integral (ψ.1.isSmoothForm.of_le (by simp))
    ((mem_compactlySupportedForms 𝓘(ℝ, ℝ)).mp hψ.1)

end Examples

end TauCeti
