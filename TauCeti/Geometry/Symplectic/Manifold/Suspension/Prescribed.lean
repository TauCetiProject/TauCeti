/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Extension
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.SeamFamily
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Seam-compatible families with prescribed values on closed regions

Let `φ` be a diffeomorphism of a finite-dimensional manifold `M` with nondegenerate two-form `σ`,
let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and `X_φ = (ℝ / ℤ)_s × Y_φ`,
with covering map `q : (ℝ × ℝ) × M → X_φ`, `((s, t), x) ↦ ([s], [t, x])`
(`TauCeti.SmoothMappingTorus.suspensionCover`). A block almost complex structure on `X_φ` descends
from a *vertical family* `K_((s,t),x)` of complex structures on `T_x M` which is smooth, periodic in
`s` and satisfies the seam identity `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

This file builds such families relative to prescribed data, for families depending on a parameter
`λ` in a manifold `Λ`. The data are:

* a *background* family `K₀ λ`: jointly smooth in `(λ, ((s, t), x))`, periodic, seam-compatible
  and `σ`-compatible everywhere, for instance the families built from one compatible structure by
  `TauCeti.SmoothMappingTorus.seamFamily`;
* an open set `U ⊆ Λ × X_φ` and a *prescribed* family `K₁ λ` which is jointly smooth,
  `σ`-compatible, periodic and seam-compatible only over the preimage of `U` under
  `(λ, p) ↦ (λ, q p)`. Over that preimage the seam identity holds on an open set, so the prescribed
  data match across the seam to every order.

A closed region `A ⊆ U` of `Λ × X_φ` can be of the form `F × X_φ` for a closed face `F` of the
parameter space, of the form `Λ × C` for a closed region `C` of `X_φ`, or a union of such sets;
prescriptions on several regions which agree on the overlaps of their open neighbourhoods form one
prescribed family on the union of those neighbourhoods.

Given a smooth cutoff `ρ : Λ × X_φ → [0, 1]` with topological support in `U`, the family

`K λ p = cayleyInterp (K₀ λ p) (ρ (λ, q p)) (K₁ λ p)` over the preimage of `U`, `K₀ λ p` elsewhere,

interpolates in the compatible Cayley chart centred at the background structure
(`TauCeti.SymplecticForm.Compatible.cayleyInterp`), which keeps every value `σ`-compatible. It is
the cutoff interpolation `TauCeti.SmoothTwoForm.IsNondegenerate.cutoffInterp` along
`(λ, ((s, t), x)) ↦ x`, shared with the extension of compatible structures on `M`. It is
jointly smooth, because the Cayley interpolation is a rational expression in its endpoints
(`TauCeti.cayleyPathFormula`). It is periodic and seam-compatible, because the cutoff is pulled
back from the quotient and the Cayley interpolation commutes with conjugation by the linear
isomorphisms `dφ⁻¹`. It equals `K₁` where `ρ = 1` and `K₀` where `ρ = 0`, and it equals `K₀`
wherever `K₁` already does, since the Cayley coordinate of a structure relative to itself is zero
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_eq_of_cutoff`). On a Hausdorff second-countable
finite-dimensional parameter manifold, with `M` second-countable, a closed set `A ⊆ U` of
`Λ × X_φ` admits such a cutoff equal to one exactly on `A`
(`IsClosed.exists_contMDiff_tsupport_subset_eq_one_iff`), so the family equals `K₁` over `A` and
`K₀` outside `U`
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn`). Over the seam path background built from
a family `J₀ λ`, a prescription which is `J₀ λ` on part of the time-end collar `|t| ≤ 1/3` leaves
the family equal to `J₀ λ` there, so the collars stay fixed even inside `U`
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn_seamFamily`). Descending, the block
structures `J λ` on `X_φ` depend smoothly on `λ`, are compatible with `Ω = ds ∧ dt + σ_v` when `φ`
preserves `σ`, send `∂_s` to the suspension vector field everywhere, and have vertical part `K₁`
over `A` and `K₀` outside `U` and wherever `K₁` is `K₀`
(`TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_eqOn`).

No `φ`-invariant structure is needed, and the prescribed family need not extend smoothly beyond
`U`.

## Main results

* `TauCeti.SmoothMappingTorus.exists_verticalFamily_eq_of_cutoff`: a periodic, seam-compatible,
  `σ`-compatible smooth family equal to the prescribed one where a given cutoff is one and to the
  background where it vanishes.
* `TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn`: the same for a closed region of
  `Λ × X_φ`, constructing the cutoff.
* `TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn_seamFamily`: the same with background
  the seam path construction from a smooth family of compatible structures on `M`.
* `TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_eqOn`: the descended
  compatible block structures on `X_φ`, sending `∂_s` to the suspension vector field, with
  prescribed vertical part over a closed region.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Sections 2.5 and 4.1 (compatible Cayley charts and relative extension of compatible
  structures).
* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  symplectic mapping tori).
-/

public noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} (hσn : σ.IsNondegenerate)
  {Λ : Type*}

/-! ### The cutoff family -/

section Cutoff

variable {K₀ K₁ : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  {U : Set (Λ × (UnitAddCircle × SmoothMappingTorus φ))}
  (hK₀c : ∀ l p, (hσn.symplecticFormAt p.2).Compatible (K₀ l p))
  (hK₁c : ∀ l p, (l, suspensionCover φ p) ∈ U →
    (hσn.symplecticFormAt p.2).Compatible (K₁ l p))
  (ρ : Λ × (UnitAddCircle × SmoothMappingTorus φ) → ℝ) (hρ : ∀ y, ρ y ∈ Icc 0 1)

/-- The cutoff interpolation `TauCeti.SmoothTwoForm.IsNondegenerate.cutoffInterp` along
`(λ, ((s, t), x)) ↦ x`, over the preimage of `U` and with the cutoff pulled back along
`(λ, p) ↦ (λ, q p)`, curried in the parameter. -/
private def cutoffFamily (l : Λ) (p : (ℝ × ℝ) × M) :
    AlmostComplexStructure (TangentSpace I p.2) :=
  hσn.cutoffInterp (f := fun r : Λ × ((ℝ × ℝ) × M) ↦ r.2.2)
    (W := {r | (r.1, suspensionCover φ r.2) ∈ U}) (fun r ↦ hK₀c r.1 r.2)
    (fun r hr ↦ hK₁c r.1 r.2 hr) (fun r ↦ ρ (r.1, suspensionCover φ r.2)) (fun _ ↦ hρ _) (l, p)

private theorem cutoffFamily_of_mem {l : Λ} {p : (ℝ × ℝ) × M}
    (h : (l, suspensionCover φ p) ∈ U) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l p =
      (hK₀c l p).cayleyInterp (V := E) (hK₁c l p h) (hρ (l, suspensionCover φ p)) :=
  hσn.cutoffInterp_of_mem _ _ _ _ (n := (l, p)) h

private theorem cutoffFamily_of_notMem {l : Λ} {p : (ℝ × ℝ) × M}
    (h : (l, suspensionCover φ p) ∉ U) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l p = K₀ l p :=
  hσn.cutoffInterp_of_notMem _ _ _ _ (n := (l, p)) h

/-- The cutoff family is compatible everywhere. -/
private theorem compatible_cutoffFamily (l : Λ) (p : (ℝ × ℝ) × M) :
    (hσn.symplecticFormAt p.2).Compatible (cutoffFamily hσn hK₀c hK₁c ρ hρ l p) :=
  hσn.compatible_cutoffInterp (f := fun r : Λ × ((ℝ × ℝ) × M) ↦ r.2.2) _ _ _ _ (l, p)

/-- Where the cutoff is one, the cutoff family is the prescribed family. -/
private theorem cutoffFamily_of_eq_one [TopologicalSpace Λ] (hsupp : tsupport ρ ⊆ U) {l : Λ}
    {p : (ℝ × ℝ) × M} (h : ρ (l, suspensionCover φ p) = 1) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l p = K₁ l p :=
  hσn.cutoffInterp_of_eq_one _ _ _ _ (n := (l, p)) (hsupp (subset_tsupport ρ (by simp [h]))) h

/-- Where the cutoff vanishes, the cutoff family is the background family. -/
private theorem cutoffFamily_of_eq_zero {l : Λ} {p : (ℝ × ℝ) × M}
    (h : ρ (l, suspensionCover φ p) = 0) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l p = K₀ l p :=
  hσn.cutoffInterp_of_eq_zero _ _ _ _ (n := (l, p)) h

/-- Where the prescribed family is the background family, so is the cutoff family. -/
private theorem cutoffFamily_of_eq {l : Λ} {p : (ℝ × ℝ) × M} (h : K₁ l p = K₀ l p) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l p = K₀ l p :=
  hσn.cutoffInterp_of_eq _ _ _ _ (n := (l, p)) h

/-- Over the preimage of `U`, the cutoff family acts by the Cayley path expression in the
operators of `K₀` and `K₁`. -/
private theorem cutoffFamily_apply_of_mem {l : Λ} {p : (ℝ × ℝ) × M}
    (h : (l, suspensionCover φ p) ∈ U) (v : TangentSpace I p.2) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l p v =
      cayleyPathFormula (ρ (l, suspensionCover φ p))
        (LinearMap.toContinuousLinearMap (K₀ l p).toLinearMap)
        (LinearMap.toContinuousLinearMap (K₁ l p).toLinearMap) v := by
  unfold cutoffFamily
  exact DFunLike.congr_fun (hσn.toContinuousLinearMap_cutoffInterp _ _ _ _ (n := (l, p)) h) v

/-- The cutoff family is periodic in `s`. -/
private theorem cutoffFamily_add_fst
    (hs₀ : ∀ l (p : (ℝ × ℝ) × M), K₀ l (p.1 + (1, 0), p.2) = K₀ l p)
    (hs₁ : ∀ l (p : (ℝ × ℝ) × M), (l, suspensionCover φ p) ∈ U →
      K₁ l (p.1 + (1, 0), p.2) = K₁ l p)
    (l : Λ) (p : (ℝ × ℝ) × M) :
    cutoffFamily hσn hK₀c hK₁c ρ hρ l (p.1 + (1, 0), p.2) =
      cutoffFamily hσn hK₀c hK₁c ρ hρ l p := by
  by_cases h : (l, suspensionCover φ p) ∈ U
  · have h' : (l, suspensionCover φ (p.1 + (1, 0), p.2)) ∈ U := by
      rwa [suspensionCover_add_fst]
    rw [cutoffFamily_of_mem hσn hK₀c hK₁c ρ hρ h', cutoffFamily_of_mem hσn hK₀c hK₁c ρ hρ h]
    congr 1
    · exact hs₀ l p
    · exact hs₁ l p h
    · rw [suspensionCover_add_fst]
  · have h' : (l, suspensionCover φ (p.1 + (1, 0), p.2)) ∉ U := by
      rwa [suspensionCover_add_fst]
    rw [cutoffFamily_of_notMem hσn hK₀c hK₁c ρ hρ h', cutoffFamily_of_notMem hσn hK₀c hK₁c ρ hρ h,
      hs₀ l p]

/-- The cutoff family satisfies the seam identity. -/
private theorem mfderiv_symm_cutoffFamily
    (ht₀ : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K₀ l p v) =
        K₀ l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (ht₁ : ∀ l (p : (ℝ × ℝ) × M), (l, suspensionCover φ p) ∈ U →
      ∀ v : TangentSpace I p.2, mfderiv I I φ.symm p.2 (K₁ l p v) =
        K₁ l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (l : Λ) (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    mfderiv I I φ.symm p.2 (cutoffFamily hσn hK₀c hK₁c ρ hρ l p v) =
      cutoffFamily hσn hK₀c hK₁c ρ hρ l (p.1 + (0, 1), φ.symm p.2)
        (mfderiv I I φ.symm p.2 v) := by
  by_cases h : (l, suspensionCover φ p) ∈ U
  · have h' : (l, suspensionCover φ (p.1 + (0, 1), φ.symm p.2)) ∈ U := by
      rwa [suspensionCover_add_snd_symm]
    -- Both sides are Cayley path expressions, and `dφ⁻¹` intertwines their endpoints.
    let e := φ.symm.mfderivToContinuousLinearEquiv (by simp) p.2
    have he (w : TangentSpace I p.2) : e w = mfderiv I I φ.symm p.2 w :=
      congr($(φ.symm.mfderivToContinuousLinearEquiv_coe (x := p.2) (by simp)) w)
    rw [cutoffFamily_apply_of_mem hσn hK₀c hK₁c ρ hρ h,
      cutoffFamily_apply_of_mem hσn hK₀c hK₁c ρ hρ h', suspensionCover_add_snd_symm, ← he, ← he]
    exact e.apply_cayleyPathFormula_apply (V := E) (W := E) _
      (fun w ↦ (he _).trans ((ht₀ l p w).trans (congrArg _ (he w).symm)))
      (fun w ↦ (he _).trans ((ht₁ l p h w).trans (congrArg _ (he w).symm))) v
  · have h' : (l, suspensionCover φ (p.1 + (0, 1), φ.symm p.2)) ∉ U := by
      rwa [suspensionCover_add_snd_symm]
    rw [cutoffFamily_of_notMem hσn hK₀c hK₁c ρ hρ h', cutoffFamily_of_notMem hσn hK₀c hK₁c ρ hρ h]
    exact ht₀ l p v

variable [T2Space M] [LocallyCompactSpace M] {EΛ HΛ : Type*} [NormedAddCommGroup EΛ]
  [NormedSpace ℝ EΛ] [TopologicalSpace HΛ] {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ]
  [ChartedSpace HΛ Λ]

omit [FiniteDimensional ℝ E] in
/-- The parametrized covering map `(λ, p) ↦ (λ, q p)` is smooth. -/
private theorem contMDiff_prodMap_suspensionCover :
    ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I))) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ (r.1, suspensionCover φ r.2)) :=
  contMDiff_fst.prodMk ((isLocalDiffeomorph_suspensionCover φ).contMDiff.comp contMDiff_snd)

/-- The cutoff family is jointly smooth in the parameter and the point. -/
private theorem contMDiff_cutoffFamily (hU : IsOpen U)
    (hK₀ : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K₀ r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hK₁ : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K₁ r.1 r.2).toLinearMap.toContinuousLinearMap)
      {r | (r.1, suspensionCover φ r.2) ∈ U})
    (hsρ : ContMDiff (IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I))) 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (cutoffFamily hσn hK₀c hK₁c ρ hρ r.1 r.2).toLinearMap.toContinuousLinearMap) := by
  have hcov := contMDiff_prodMap_suspensionCover (Λ := Λ) (IΛ := IΛ) (φ := φ)
  exact hσn.contMDiff_cutoffInterp _ _ _ _ (contMDiff_snd.comp contMDiff_snd)
    (hU.preimage hcov.continuous) hK₀ hK₁ (hsρ.comp hcov)
    ((tsupport_comp_subset_preimage ρ hcov.continuous).trans fun _ hr ↦ hsupp hr)

end Cutoff

/-! ### Relative seam-compatible families -/

variable [T2Space M] [LocallyCompactSpace M] {EΛ HΛ : Type*} [NormedAddCommGroup EΛ]
  [NormedSpace ℝ EΛ] [TopologicalSpace HΛ] {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ]
  [ChartedSpace HΛ Λ]
  {K₀ K₁ : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  (hK₀ : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      r.2.2 (K₀ r.1 r.2).toLinearMap.toContinuousLinearMap))
  (hs₀ : ∀ l (p : (ℝ × ℝ) × M), K₀ l (p.1 + (1, 0), p.2) = K₀ l p)
  (ht₀ : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
    mfderiv I I φ.symm p.2 (K₀ l p v) =
      K₀ l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
  (hK₀c : ∀ l p, (hσn.symplecticFormAt p.2).Compatible (K₀ l p))
  {U : Set (Λ × (UnitAddCircle × SmoothMappingTorus φ))} (hU : IsOpen U)
  (hK₁ : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      r.2.2 (K₁ r.1 r.2).toLinearMap.toContinuousLinearMap)
    {r | (r.1, suspensionCover φ r.2) ∈ U})
  (hs₁ : ∀ l (p : (ℝ × ℝ) × M), (l, suspensionCover φ p) ∈ U →
    K₁ l (p.1 + (1, 0), p.2) = K₁ l p)
  (ht₁ : ∀ l (p : (ℝ × ℝ) × M), (l, suspensionCover φ p) ∈ U →
    ∀ v : TangentSpace I p.2, mfderiv I I φ.symm p.2 (K₁ l p v) =
      K₁ l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
  (hK₁c : ∀ l p, (l, suspensionCover φ p) ∈ U →
    (hσn.symplecticFormAt p.2).Compatible (K₁ l p))

include hK₀ hs₀ ht₀ hK₀c hU hK₁ hs₁ ht₁ hK₁c in
/-- **Relative seam-compatible families.** Let `K₀ λ` be a background family of vertical
structures, jointly smooth in `(λ, ((s, t), x))`, periodic in `s`, seam-compatible and
`σ`-compatible, and let `K₁ λ` be a prescribed family with these properties over the preimage of an
open set `U ⊆ Λ × X_φ`. For a smooth cutoff `ρ : Λ × X_φ → [0, 1]` with topological support in
`U`, there is a family `K λ` with all these properties everywhere, equal to `K₁` where the pulled
back cutoff is one, to `K₀` where it vanishes, and to `K₀` wherever `K₁` is. -/
theorem exists_verticalFamily_eq_of_cutoff (ρ : Λ × (UnitAddCircle × SmoothMappingTorus φ) → ℝ)
    (hρ : ∀ y, ρ y ∈ Icc 0 1) (hsρ : ContMDiff (IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I))) 𝓘(ℝ) ∞ ρ)
    (hsupp : tsupport ρ ⊆ U) :
    ∃ K : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l (p : (ℝ × ℝ) × M), K l (p.1 + (1, 0), p.2) = K l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K l p v) =
          K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K l p)) ∧
      (∀ l p, ρ (l, suspensionCover φ p) = 1 → K l p = K₁ l p) ∧
      (∀ l p, ρ (l, suspensionCover φ p) = 0 → K l p = K₀ l p) ∧
      (∀ l p, K₁ l p = K₀ l p → K l p = K₀ l p) :=
  ⟨cutoffFamily hσn hK₀c hK₁c ρ hρ,
    contMDiff_cutoffFamily hσn hK₀c hK₁c ρ hρ hU hK₀ hK₁ hsρ hsupp,
    cutoffFamily_add_fst hσn hK₀c hK₁c ρ hρ hs₀ hs₁,
    mfderiv_symm_cutoffFamily hσn hK₀c hK₁c ρ hρ ht₀ ht₁,
    compatible_cutoffFamily hσn hK₀c hK₁c ρ hρ,
    fun _ _ ↦ cutoffFamily_of_eq_one hσn hK₀c hK₁c ρ hρ hsupp,
    fun _ _ ↦ cutoffFamily_of_eq_zero hσn hK₀c hK₁c ρ hρ,
    fun _ _ ↦ cutoffFamily_of_eq hσn hK₀c hK₁c ρ hρ⟩

include hK₀ hs₀ ht₀ hK₀c hU hK₁ hs₁ ht₁ hK₁c in
/-- **Relative seam-compatible families on closed regions.** With the hypotheses of
`exists_verticalFamily_eq_of_cutoff`, on a Hausdorff second-countable finite-dimensional parameter
manifold and for a second-countable `M`, let `A ⊆ U` be a closed set of `Λ × X_φ`. There is a
jointly smooth, periodic, seam-compatible and `σ`-compatible family `K λ` equal to the prescribed
family `K₁` over `A`, to the background `K₀` outside `U`, and to `K₀` wherever `K₁` is. -/
theorem exists_verticalFamily_eqOn [IsManifold IΛ ∞ Λ] [FiniteDimensional ℝ EΛ] [T2Space Λ]
    [SecondCountableTopology Λ] [SecondCountableTopology M]
    {A : Set (Λ × (UnitAddCircle × SmoothMappingTorus φ))} (hA : IsClosed A) (hAU : A ⊆ U) :
    ∃ K : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l (p : (ℝ × ℝ) × M), K l (p.1 + (1, 0), p.2) = K l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K l p v) =
          K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K l p)) ∧
      (∀ l p, (l, suspensionCover φ p) ∈ A → K l p = K₁ l p) ∧
      (∀ l p, (l, suspensionCover φ p) ∉ U → K l p = K₀ l p) ∧
      (∀ l p, K₁ l p = K₀ l p → K l p = K₀ l p) := by
  have : LocallyCompactSpace HΛ := IΛ.locallyCompactSpace
  have : LocallyCompactSpace Λ := ChartedSpace.locallyCompactSpace HΛ Λ
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace (ModelProd ℝ H) := inferInstanceAs (LocallyCompactSpace (ℝ × H))
  have : LocallyCompactSpace (SmoothMappingTorus φ) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℝ H) _
  obtain ⟨ρ, hsρ, hρ, hsupp, hone⟩ :=
    hA.exists_contMDiff_tsupport_subset_eq_one_iff (I := IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I))) hU hAU
  obtain ⟨K, hK, hs, ht, hc, hloc, hbg, heq⟩ := exists_verticalFamily_eq_of_cutoff hσn hK₀ hs₀ ht₀
    hK₀c hU hK₁ hs₁ ht₁ hK₁c ρ hρ hsρ hsupp
  refine ⟨K, hK, hs, ht, hc, fun l p h ↦ hloc l p ((hone _).mp h), fun l p h ↦ hbg l p ?_, heq⟩
  exact Function.notMem_support.mp fun h' ↦ h (hsupp (subset_tsupport ρ h'))

include hU hK₁ hs₁ ht₁ hK₁c in
/-- **Relative seam-compatible families over the seam path construction.** With the hypotheses of
`exists_verticalFamily_eqOn` on the prescribed family `K₁`, take as background the
seam-compatible families built from a smooth family `J₀ λ` of `σ`-compatible structures on `M`
(`TauCeti.SmoothMappingTorus.seamFamily`), for a `σ` preserved by `φ`. There is a jointly smooth,
periodic, seam-compatible and `σ`-compatible family equal to `K₁` over `A` and, outside `U`, to the
Cayley path from `(φ ^ k)^* J₀ λ` to `(φ ^ (k + 1))^* J₀ λ` on each time interval `[k, k + 1]`; in
particular to `J₀ λ` there for `|t| ≤ 1/3`. On the collar `|t| ≤ 1/3` it is `J₀ λ` also inside `U`,
wherever the prescribed family is. -/
theorem exists_verticalFamily_eqOn_seamFamily [IsManifold IΛ ∞ Λ] [FiniteDimensional ℝ EΛ]
    [T2Space Λ] [SecondCountableTopology Λ] [SecondCountableTopology M]
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) {J₀ : Λ → SmoothAlmostComplexStructure I M}
    (hJ₀ : ∀ l, σ.Compatible (J₀ l))
    (hJ₀s : ContMDiff (IΛ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Λ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((J₀ q.1).toEndomorphism q.2)))
    {A : Set (Λ × (UnitAddCircle × SmoothMappingTorus φ))} (hA : IsClosed A) (hAU : A ⊆ U) :
    ∃ K : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l (p : (ℝ × ℝ) × M), K l (p.1 + (1, 0), p.2) = K l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K l p v) =
          K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K l p)) ∧
      (∀ l p, (l, suspensionCover φ p) ∈ A → K l p = K₁ l p) ∧
      (∀ l p, (l, suspensionCover φ p) ∉ U → K l p = seamFamily hσ (hJ₀ l) p) ∧
      (∀ l (s t : ℝ) (x : M), t ∈ Icc (-(1 / 3) : ℝ) (1 / 3) →
        K₁ l ((s, t), x) = (J₀ l).almostComplexStructureAt x →
        K l ((s, t), x) = (J₀ l).almostComplexStructureAt x) := by
  obtain ⟨K, hK, hs, ht, hc, hloc, hbg, heq⟩ := exists_verticalFamily_eqOn hσn
    (contMDiff_seamFamily_family hσ hJ₀ hJ₀s) (fun l ↦ seamFamily_add_fst hσ (hJ₀ l))
    (fun l ↦ mfderiv_symm_seamFamily hσ (hJ₀ l)) (fun l ↦ compatible_seamFamily hσ (hJ₀ l) hσn)
    hU hK₁ hs₁ ht₁ hK₁c hA hAU
  refine ⟨K, hK, hs, ht, hc, hloc, hbg, fun l s t x hct h ↦ ?_⟩
  rw [← seamFamily_eq_of_mem_Icc hσ (hJ₀ l) (s := s) hct] at h ⊢
  exact heq l _ h

include hK₀ hs₀ ht₀ hK₀c hU hK₁ hs₁ ht₁ hK₁c in
/-- **Compatible block structures with prescribed vertical part.** Let `φ` preserve `σ`. With the
hypotheses of `exists_verticalFamily_eqOn`, there is a family `J λ` of almost complex structures on
`X_φ = (ℝ / ℤ) × Y_φ`, jointly smooth in `(λ, y)` and each compatible with
`Ω = ds ∧ dt + σ_v`, which in the coordinates `(s, t, x)` sends `a ∂_s + b ∂_t + v` to
`-b ∂_s + a ∂_t + K₁ λ ((s, t), x) v` over the closed set `A`, and to
`-b ∂_s + a ∂_t + K₀ λ ((s, t), x) v` outside `U` and wherever `K₁` is `K₀`. Everywhere on `X_φ`,
`J λ` sends `∂_s` to the suspension vector field `T`. -/
theorem exists_suspensionAlmostComplexStructure_eqOn [IsManifold IΛ ∞ Λ] [FiniteDimensional ℝ EΛ]
    [T2Space Λ] [SecondCountableTopology Λ] [SecondCountableTopology M]
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    {A : Set (Λ × (UnitAddCircle × SmoothMappingTorus φ))} (hA : IsClosed A) (hAU : A ⊆ U) :
    ∃ J : Λ → SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
        (UnitAddCircle × SmoothMappingTorus φ),
      ContMDiff (IΛ.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I)))
        ((𝓘(ℝ).prod (𝓘(ℝ).prod I)).prod 𝓘(ℝ, (ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))) ∞
        (fun r : Λ × (UnitAddCircle × SmoothMappingTorus φ) ↦
          TotalSpace.mk' ((ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))
            (E := fun y : UnitAddCircle × SmoothMappingTorus φ ↦
              TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y →L[ℝ]
                TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y) r.2
            ((J r.1).toEndomorphism r.2)) ∧
      (∀ l, (suspensionForm φ σ hσ).Compatible (J l)) ∧
      (∀ l y, J l y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2)) ∧
      (∀ l (s t : ℝ) (x : M), (l, ((s : UnitAddCircle), mk φ t x)) ∈ A →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J l ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K₁ l ((s, t), x) v)))) ∧
      (∀ l (s t : ℝ) (x : M),
        (l, ((s : UnitAddCircle), mk φ t x)) ∉ U ∨ K₁ l ((s, t), x) = K₀ l ((s, t), x) →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J l ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K₀ l ((s, t), x) v)))) := by
  obtain ⟨K, hK, hs, ht, hc, hloc, hbg, heq⟩ := exists_verticalFamily_eqOn hσn hK₀ hs₀ ht₀ hK₀c hU
    hK₁ hs₁ ht₁ hK₁c hA hAU
  refine ⟨fun l ↦ suspensionAlmostComplexStructure φ
      (hK.comp (contMDiff_const.prodMk contMDiff_id)) (hs l) (ht l),
    contMDiff_suspensionAlmostComplexStructure_family φ hK hs ht,
    fun l ↦ compatible_suspensionAlmostComplexStructure φ _ _ _ hσn (hc l),
    fun l ↦ suspensionAlmostComplexStructure_apply_symm_one_zero φ _ _ _, ?_, ?_⟩
  · intro l s t x h a b v
    refine (suspensionAlmostComplexStructure_mk φ _ _ _ s t x a b v).trans ?_
    dsimp only [id]
    rw [hloc l ((s, t), x) (by rwa [suspensionCover_apply])]
  · intro l s t x h a b v
    refine (suspensionAlmostComplexStructure_mk φ _ _ _ s t x a b v).trans ?_
    dsimp only [id]
    rw [h.elim (fun h ↦ hbg l ((s, t), x) (by rwa [suspensionCover_apply])) (heq l _)]

end TauCeti.SmoothMappingTorus
