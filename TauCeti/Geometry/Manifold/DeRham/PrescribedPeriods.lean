/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Cover
public import TauCeti.Geometry.Manifold.DeRham.LogDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph

/-!
# Closed one-forms with prescribed periods

On a connected manifold the periods of a closed `1`-form determine its de Rham class
(`TauCeti.deRhamCohomology.period_injective`). This file proves the converse half of the de Rham
theorem in degree one: on a path-connected σ-compact manifold `M`, every homomorphism
`P : π₁(M, x) → ℝ` is the period homomorphism of a closed smooth real `1`-form
(`TauCeti.exists_mem_closedForms_periodHom_eq`). Hence the periods identify the first de Rham
cohomology with the real homomorphisms of the fundamental group
(`TauCeti.deRhamCohomology.periodEquiv`) and of the first singular homology group
(`TauCeti.deRhamCohomology.homologyPeriodEquiv`):

`H¹_dR(M) ≃ Hom(π₁(M, x), ℝ) ≃ Hom(H₁(M; ℤ), ℝ)`.

For the group `C^∞(M, U(1))` of smooth circle-valued maps, the gauge group of a Hermitian line
bundle, every homomorphism `H₁(M; ℤ) → ℤ` is the period homomorphism of a gauge transformation
(`TauCeti.circlePeriodHom_surjective`). Together with the kernel computed in
`TauCeti.circlePeriodHom_eq_one_iff`, this identifies the group of components of the gauge group,
`C^∞(M, U(1))` modulo the maps `exp (i f)` with a smooth logarithm, with `Hom(H₁(M; ℤ), ℤ)`. The
gauge transformation is obtained from a closed real form `ψ` with periods `n` by applying
`exists_mlogDeriv_coe_eq` to `2πi ψ`, whose periods are `2πi n` because integration commutes with
coefficient maps (`TauCeti.homologyPeriodHom_mapCoeff`).

The form with periods `P` is built on the universal cover `UniversalCover x`, on which
`π₁(M, x)` acts by deck transformations. There is a smooth function `F` on the cover with
`F (g • p) = F p - P g` (`TauCeti.UniversalCover.exists_contMDiff_smul_eq_add` for `-P`, built
from a partition of unity and local sections of the projection). Its differential `dF` is
invariant under the deck transformations, so it is the pullback of a closed form `β` on `M`
(`IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff`). The integral of `β` along a loop `g`
is the change of `F` along the lift of the loop, from the constant-path point to its translate by
`g⁻¹` (`TauCeti.UniversalCover.apply_mk_eq_apply_mk_refl_add_pathClassIntegral`), which is `P g`.

## Main results

* `TauCeti.exists_mem_closedForms_periodHom_eq`: every real homomorphism of the fundamental group
  is the period homomorphism of a closed smooth `1`-form.
* `TauCeti.deRhamCohomology.period_surjective`,
  `TauCeti.deRhamCohomology.homologyPeriod_surjective`: the period maps on `H¹_dR(M)` are onto.
* `TauCeti.deRhamCohomology.periodEquiv`, `TauCeti.deRhamCohomology.homologyPeriodEquiv`: the
  periods identify `H¹_dR(M)` with `Hom(π₁(M, x), ℝ)` and with `Hom(H₁(M; ℤ), ℝ)`.
* `TauCeti.circlePeriodHom_surjective`: every integral homomorphism of `H₁(M; ℤ)` is the period
  homomorphism of a smooth circle-valued map.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (the de Rham theorem).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the components of the
  gauge group of a line bundle).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [PathConnectedSpace M]

/-- **Closed one-forms with prescribed periods.** On a path-connected σ-compact manifold, every
homomorphism `P` from the fundamental group at `x` to `ℝ` is the period homomorphism of a closed
smooth real `1`-form. -/
theorem exists_mem_closedForms_periodHom_eq (x : M) (P : Additive (FundamentalGroup M x) →+ ℝ) :
    ∃ φ ∈ closedForms I M 1, periodHom (φ : RoughForm I M ℝ 1) x = P := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  have hproj := UniversalCover.isLocalDiffeomorph_proj (I := I) (n := ∞) x
  -- A function on the universal cover changing by `-P g` under `g`; its differential descends.
  obtain ⟨F, hF, hFg⟩ := UniversalCover.exists_contMDiff_smul_eq_add (I := I) (x₀ := x) (-P)
  have hF0 : RoughForm.ofFunction I F ∈ smoothBundleForms I ℝ (Bundle.Trivial _ ℝ) 0 :=
    (isSmoothForm_ofFunction_iff.mpr hF).mem_smoothBundleForms
  obtain ⟨α, hα⟩ : ∃ α : SmoothForm I (UniversalCover x) ℝ 1,
      (α : RoughForm I (UniversalCover x) ℝ 1) = mextDeriv (RoughForm.ofFunction I F) :=
    ⟨⟨_, mextDeriv_mem_smoothBundleForms hF0⟩, rfl⟩
  have hσ (g : FundamentalGroup M x) : ContMDiff I I ∞ (g • · : UniversalCover x → _) :=
    UniversalCover.contMDiff_iff.mpr ⟨continuous_const_smul g, hproj.contMDiff⟩
  -- `dF` is invariant under the deck transformations, since `F ∘ (g • ·) = F - P g`.
  have hinv (g : FundamentalGroup M x) : SmoothForm.mpullback _ (hσ g) α = α := by
    apply Subtype.ext
    have hFσ : F ∘ (g • ·) = F + fun _ ↦ (-P) (Additive.ofMul g) := funext (hFg g)
    simp only [SmoothForm.coe_mpullback, hα]
    rw [mpullback_mextDeriv_ofFunction ((hσ g).mdifferentiable (by simp))
      (hF.mdifferentiable (by simp)), hFσ, mextDeriv_ofFunction_add (hF.mdifferentiable (by simp))
      mdifferentiable_const, add_eq_left]
    ext p v
    simp [mextDeriv_ofFunction, mvfderiv_const]
  obtain ⟨β, hβ⟩ := (hproj.exists_smoothForm_mpullback_eq_iff UniversalCover.proj_surjective hσ
    (fun g ↦ funext (UniversalCover.proj_smul g)) (fun p q hpq ↦
      .inr (UniversalCover.proj_eq_iff_mem_orbit.mp hpq.symm))).mpr hinv
  have hβ' : mextDeriv (RoughForm.ofFunction I F) =
      mpullback I I UniversalCover.proj (β : RoughForm I M ℝ 1) := by
    rw [← hα, ← hβ, SmoothForm.coe_mpullback]
  have hβc : mextDeriv (β : RoughForm I M ℝ 1) = 0 := by
    have hαc : α.IsClosed := by
      rw [SmoothForm.isClosed_def, hα]
      exact mextDeriv_mextDeriv_ofFunction (hF.of_le (by simp))
    rw [← hβ] at hαc
    exact (SmoothForm.isClosed_def β).mp
      ((hproj.isClosed_mpullback_iff UniversalCover.proj_surjective).mp hαc)
  refine ⟨β, (mem_closedForms I β).mpr hβc, AddMonoidHom.ext fun g ↦ ?_⟩
  -- Integrate `dF` along the lift of a loop `g`, which ends at `g⁻¹ • mk x refl`.
  have h := UniversalCover.apply_mk_eq_apply_mk_refl_add_pathClassIntegral
    (β.isSmoothForm.of_le (by simp)) hβc (hF.of_le (by simp)) hβ' (Additive.toMul g).toPath
  rw [← Path.Homotopic.Quotient.trans_refl (Additive.toMul g).toPath,
    ← UniversalCover.inv_smul_mk, hFg, Path.Homotopic.Quotient.trans_refl] at h
  rw [periodHom_apply]
  simp only [AddMonoidHom.neg_apply, ofMul_inv, ofMul_toMul, map_neg, neg_neg] at h
  linarith

namespace deRhamCohomology

/-- On a path-connected σ-compact manifold, every real homomorphism of the fundamental group at `x`
is the period homomorphism of a de Rham class. -/
theorem period_surjective (x : M) : Function.Surjective (period (I := I) x) := fun P ↦ by
  obtain ⟨φ, hφ, hP⟩ := exists_mem_closedForms_periodHom_eq (I := I) x P
  exact ⟨mk I 1 ⟨φ, hφ⟩, by rw [period_mk, hP]⟩

variable (I M) in
/-- **The de Rham theorem in degree one, for the fundamental group.** On a path-connected
σ-compact manifold, the periods identify the first de Rham cohomology with the real
homomorphisms of the fundamental group at `x`. -/
def periodEquiv (x : M) : deRhamCohomology I M 1 ≃ₗ[ℝ] (Additive (FundamentalGroup M x) →+ ℝ) :=
  LinearEquiv.ofBijective (period x) ⟨period_injective x, period_surjective x⟩

@[simp]
theorem periodEquiv_apply (x : M) (c : deRhamCohomology I M 1) :
    periodEquiv I M x c = period x c :=
  (rfl)

end deRhamCohomology

section Homology

open TauCeti.HurewiczOne TauCeti.TopCat

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [PathConnectedSpace M]

namespace deRhamCohomology

/-- On a path-connected σ-compact manifold, every homomorphism `H₁(M; ℤ) → ℝ` is the period
homomorphism of a de Rham class. -/
theorem homologyPeriod_surjective : Function.Surjective (homologyPeriod (I := I) (M := M)) := by
  intro h
  obtain ⟨x⟩ : Nonempty M := inferInstance
  -- The homomorphism of the fundamental group through the Hurewicz isomorphism.
  obtain ⟨c, hc⟩ := period_surjective (I := I) x (h.comp
    ((hurewiczHomologyAddEquiv (X := .of M) x (.refl ℤ)).toAddMonoidHom.comp
      (MonoidHom.toAdditive Group.Abelianization.of)))
  obtain ⟨φ, rfl⟩ := mk_surjective I 1 c
  refine ⟨mk I 1 φ,
    homology_one_addMonoidHom_ext_of_fundamentalGroup (X := .of M) x (.refl ℤ) fun g ↦ ?_⟩
  rw [homologyPeriod_mk, homologyPeriodHom_hurewiczHomologyAddEquiv, ← period_mk, hc]
  simp only [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    AddEquiv.coe_toAddMonoidHom]

variable (I M) in
/-- **The de Rham theorem in degree one.** On a path-connected σ-compact manifold, the periods on
the first singular homology group identify the first de Rham cohomology with
`Hom(H₁(M; ℤ), ℝ)`. -/
def homologyPeriodEquiv :
    deRhamCohomology I M 1 ≃ₗ[ℝ] (((singularChains ℤ).obj (.of M)).homology 1 →+ ℝ) :=
  LinearEquiv.ofBijective homologyPeriod ⟨homologyPeriod_injective, homologyPeriod_surjective⟩

@[simp]
theorem homologyPeriodEquiv_apply (c : deRhamCohomology I M 1) :
    homologyPeriodEquiv I M c = homologyPeriod c :=
  (rfl)

/-- The class `(homologyPeriodEquiv I M).symm h` has the periods `h`. -/
@[simp]
theorem homologyPeriod_homologyPeriodEquiv_symm_apply
    (h : ((singularChains ℤ).obj (.of M)).homology 1 →+ ℝ) :
    homologyPeriod ((homologyPeriodEquiv I M).symm h) = h :=
  (homologyPeriodEquiv I M).apply_symm_apply h

end deRhamCohomology

/-- **Every integral period homomorphism comes from a gauge transformation.** On a path-connected
σ-compact manifold, every homomorphism `n : H₁(M; ℤ) → ℤ` is the period homomorphism of a smooth
circle-valued map: `(2πi)⁻¹ ∫_c dlog u = n c` for every class `c`. Together with
`TauCeti.circlePeriodHom_eq_one_iff`, this identifies the group of components of `C^∞(M, U(1))`,
modulo the maps `exp (i f)` with a smooth logarithm, with `Hom(H₁(M; ℤ), ℤ)`. -/
theorem circlePeriodHom_surjective : Function.Surjective (circlePeriodHom I M) := by
  intro n
  -- A closed real form `ψ` whose periods are the integers `n c`.
  obtain ⟨c, hc⟩ := deRhamCohomology.homologyPeriod_surjective (I := I)
    ((Int.castAddHom ℝ).comp (Multiplicative.toAdd n))
  obtain ⟨ψ, rfl⟩ := deRhamCohomology.mk_surjective I 1 c
  rw [deRhamCohomology.homologyPeriod_mk] at hc
  have hψ := ψ.val.isSmoothForm
  have hψc : mextDeriv (ψ.val : RoughForm I M ℝ 1) = 0 := (mem_closedForms I _).mp ψ.property
  -- Its multiple by `2πi` is a closed imaginary form with periods `2πi n c`.
  set L : ℝ →L[ℝ] ℂ := (2 * Real.pi * Complex.I) • Complex.ofRealCLM
  have hL := homologyPeriodHom_mapCoeff L (hψ.of_le (by simp)) hψc
  refine mem_range_circlePeriodHom_iff.mpr ⟨RoughForm.mapCoeff L ψ.val, hψ.mapCoeff L,
    by rw [mextDeriv_mapCoeff L (hψ.of_le (by simp)), hψc, RoughForm.mapCoeff_zero],
    fun y v ↦ by simp [L], fun y ↦ ?_⟩
  simp only [hL, hc, AddMonoidHom.coe_comp, Int.coe_castAddHom, comp_apply,
    AddMonoidHom.coe_ofClass, smul_apply, Complex.ofRealCLM_apply, Complex.ofReal_intCast,
    smul_eq_mul, L]
  ring

end Homology

end TauCeti
