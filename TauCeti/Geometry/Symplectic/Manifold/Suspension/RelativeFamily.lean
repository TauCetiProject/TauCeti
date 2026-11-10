/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.AlmostComplex
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Seam-compatible vertical families with prescribed values on a closed region

Let `φ` be a diffeomorphism of a finite-dimensional manifold `M` with nondegenerate two-form `σ`,
let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ`, with covering map `q : (ℝ × ℝ) × M → X_φ`,
`((s, t), x) ↦ ([s], [t, x])` (`TauCeti.SmoothMappingTorus.suspensionCover`). A block almost
complex structure on `X_φ` descends from a *vertical family* `K_((s,t),x)` of almost complex
structures on the tangent spaces `T_x M` which is jointly smooth, periodic in `s` and satisfies
the seam identity `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

This file solves the relative problem. Let `A ⊆ X_φ` be closed and `U ⊇ A` open, and let `L` be a
vertical family that is prescribed only over `q⁻¹(U)`: smooth, `σ`-compatible, periodic in `s` and
seam-compatible there. These are exactly the vertical data over `U` pulled back to the covering
space, and the region `q⁻¹(U)` is invariant under the deck transformations. Given any smooth
seam-compatible `σ`-compatible background family `K₀`, such as
`TauCeti.SmoothMappingTorus.seamFamily`, there is a smooth seam-compatible `σ`-compatible vertical
family `K` that equals `L` over `A` and equals `K₀` outside `U`
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn`). Its descent is a block almost complex
structure on `X_φ`, compatible with `Ω = ds ∧ dt + σ_v`, whose vertical part over `A` is the
prescribed one (`TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_eqOn`).

The construction cuts `L` off in the Cayley chart of `K₀`, as in the extension of a single
compatible structure from a closed region
(`TauCeti.SmoothTwoForm.Compatible.exists_compatible_eq_of_cutoff`), with a cutoff function
pulled back from `X_φ` along `q`. Pulled back cutoffs are invariant under the deck
transformations, and the Cayley interpolation is a rational expression in its two endpoints, so it
commutes with conjugation by `dφ⁻¹`; this preserves the seam identity. Compatibility is preserved
because the compatible Cayley ball is convex. The prescribed family need not be extendable from
`q⁻¹(U)` in any sense: a cutoff whose topological support lies in `U` makes the result smooth
everywhere. Neither the closedness of `σ` nor `φ^* σ = σ` is needed for the construction of `K`;
the invariance of `σ` enters only through the form `Ω` in the descended statement. No compactness
of `M` or of `A` is needed; the versions for a closed set assume `M` second countable, so that
`X_φ` carries smooth cutoff functions.

## Main results

* `TauCeti.SmoothMappingTorus.exists_verticalFamily_eq_of_cutoff`: the relative vertical family
  built from a specified smooth cutoff on `X_φ` with topological support in `U`.
* `TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn`: the relative vertical family for a
  closed set `A ⊆ U`, for a second countable `M`.
* `TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_eqOn`: the descended
  `Ω`-compatible block structure on `X_φ` whose vertical part is prescribed over `A`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  `ℝ × Y_φ`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Sections 2.5 and 4.1 (compatible Cayley charts and relative extension).
-/

public noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} (hσn : σ.IsNondegenerate)
  {K₀ : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  (hK₀ : ∀ p, (hσn.symplecticFormAt p.2).Compatible (K₀ p))
  {U : Set (UnitAddCircle × SmoothMappingTorus φ)}
  (L : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
  (hL : ∀ p, suspensionCover φ p ∈ U → (hσn.symplecticFormAt p.2).Compatible (L p))
  (ρ : UnitAddCircle × SmoothMappingTorus φ → ℝ) (hρ : ∀ y, ρ y ∈ Icc 0 1)

/-! ### Deck invariance of the covering map -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The covering map is invariant under the translation `s ↦ s + 1`. -/
private theorem suspensionCover_add_fst (p : (ℝ × ℝ) × M) :
    suspensionCover φ (p.1 + (1, 0), p.2) = suspensionCover φ p := by
  simpa using suspensionCover_deck φ 1 0 p

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The covering map is invariant under the seam step `(t, x) ↦ (t + 1, φ⁻¹ x)`. -/
private theorem suspensionCover_add_snd (p : (ℝ × ℝ) × M) :
    suspensionCover φ (p.1 + (0, 1), φ.symm p.2) = suspensionCover φ p := by
  simpa using suspensionCover_deck φ 0 1 p

/-! ### The cut-off family -/

open Classical in
/-- The vertical family that interpolates, at `p`, from `K₀ p` towards `L p` with the weight
`ρ (q p)` in the Cayley chart of `K₀ p`, and equals `K₀ p` outside `q⁻¹(U)`. -/
private def cutoffFamily (p : (ℝ × ℝ) × M) : AlmostComplexStructure (TangentSpace I p.2) :=
  if hp : suspensionCover φ p ∈ U then
    (hK₀ p).cayleyInterp (V := E) (hL p hp) (hρ (suspensionCover φ p))
  else K₀ p

private theorem cutoffFamily_of_mem {p : (ℝ × ℝ) × M} (hp : suspensionCover φ p ∈ U) :
    cutoffFamily hσn hK₀ L hL ρ hρ p =
      (hK₀ p).cayleyInterp (V := E) (hL p hp) (hρ (suspensionCover φ p)) :=
  dite_eq_left hp

private theorem cutoffFamily_of_notMem {p : (ℝ × ℝ) × M} (hp : suspensionCover φ p ∉ U) :
    cutoffFamily hσn hK₀ L hL ρ hρ p = K₀ p :=
  dite_eq_right hp

private theorem compatible_cutoffFamily (p : (ℝ × ℝ) × M) :
    (hσn.symplecticFormAt p.2).Compatible (cutoffFamily hσn hK₀ L hL ρ hρ p) := by
  by_cases hp : suspensionCover φ p ∈ U
  · rw [cutoffFamily_of_mem hσn hK₀ L hL ρ hρ hp]
    exact (hK₀ p).compatible_cayleyInterp (V := E) (hL p hp) _
  · rw [cutoffFamily_of_notMem hσn hK₀ L hL ρ hρ hp]
    exact hK₀ p

private theorem cutoffFamily_eq_background {p : (ℝ × ℝ) × M} (hp : ρ (suspensionCover φ p) = 0) :
    cutoffFamily hσn hK₀ L hL ρ hρ p = K₀ p := by
  by_cases hpU : suspensionCover φ p ∈ U
  · rw [cutoffFamily_of_mem hσn hK₀ L hL ρ hρ hpU]
    simp only [hp]
    exact (hK₀ p).cayleyInterp_zero (V := E) (hL p hpU)
  · exact cutoffFamily_of_notMem hσn hK₀ L hL ρ hρ hpU

private theorem cutoffFamily_eq_local {p : (ℝ × ℝ) × M} (hpU : suspensionCover φ p ∈ U)
    (hp : ρ (suspensionCover φ p) = 1) :
    cutoffFamily hσn hK₀ L hL ρ hρ p = L p := by
  rw [cutoffFamily_of_mem hσn hK₀ L hL ρ hρ hpU]
  simp only [hp]
  exact (hK₀ p).cayleyInterp_one (V := E) (hL p hpU)

/-- Over `q⁻¹(U)`, the cut-off family is the Cayley path expression in `K₀` and `L`. -/
private theorem cutoffFamily_formula {p : (ℝ × ℝ) × M} (hp : suspensionCover φ p ∈ U) :
    LinearMap.toContinuousLinearMap (cutoffFamily hσn hK₀ L hL ρ hρ p).toLinearMap =
      cayleyPathFormula (ρ (suspensionCover φ p))
        (LinearMap.toContinuousLinearMap (K₀ p).toLinearMap)
        (LinearMap.toContinuousLinearMap (L p).toLinearMap) := by
  rw [cutoffFamily_of_mem hσn hK₀ L hL ρ hρ hp]
  exact (hK₀ p).toContinuousLinearMap_cayleyInterp (V := E) (hL p hp) _
    (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)

omit [IsManifold I ∞ M] in
/-- If `dφ⁻¹ ∘ K = K' ∘ dφ⁻¹`, then `K'` is the conjugate of `K` by the differential of `φ⁻¹`. -/
private theorem conj_eq_of_mfderiv_symm {x : M} {K : AlmostComplexStructure (TangentSpace I x)}
    {K' : AlmostComplexStructure (TangentSpace I (φ.symm x))}
    (h : ∀ v, mfderiv I I φ.symm x (K v) = K' (mfderiv I I φ.symm x v)) :
    (φ.symm.mfderivToContinuousLinearEquiv (by simp) x).conjContinuousAlgEquiv
        (LinearMap.toContinuousLinearMap K.toLinearMap) =
      LinearMap.toContinuousLinearMap K'.toLinearMap := by
  ext w
  set g := φ.symm.mfderivToContinuousLinearEquiv (by simp) x
  have hg : ∀ v, g v = mfderiv I I φ.symm x v := fun v ↦
    congrArg (· v) (φ.symm.mfderivToContinuousLinearEquiv_coe (x := x) (by simp))
  have h' := h (g.symm w)
  rw [← hg, ← hg, ContinuousLinearEquiv.apply_symm_apply] at h'
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
  -- An almost complex structure acts on vectors through its underlying linear map.
  exact h'

/-- The cut-off family is periodic in `s` when `K₀` and `L` are. -/
private theorem cutoffFamily_add_fst (hK₀s : ∀ p, K₀ (p.1 + (1, 0), p.2) = K₀ p)
    (hLs : ∀ p, suspensionCover φ p ∈ U → L (p.1 + (1, 0), p.2) = L p) (p : (ℝ × ℝ) × M) :
    cutoffFamily hσn hK₀ L hL ρ hρ (p.1 + (1, 0), p.2) = cutoffFamily hσn hK₀ L hL ρ hρ p := by
  by_cases hp : suspensionCover φ p ∈ U
  · have hp' : suspensionCover φ (p.1 + (1, 0), p.2) ∈ U := by
      rwa [suspensionCover_add_fst]
    -- Both values are the Cayley path expression in the same endpoints with the same weight.
    have h := cutoffFamily_formula hσn hK₀ L hL ρ hρ hp'
    rw [suspensionCover_add_fst, hK₀s, hLs p hp, ← cutoffFamily_formula hσn hK₀ L hL ρ hρ hp] at h
    exact AlmostComplexStructure.toLinearMap_injective (LinearMap.toContinuousLinearMap.injective h)
  · have hp' : suspensionCover φ (p.1 + (1, 0), p.2) ∉ U := by
      rwa [suspensionCover_add_fst]
    rw [cutoffFamily_of_notMem hσn hK₀ L hL ρ hρ hp, cutoffFamily_of_notMem hσn hK₀ L hL ρ hρ hp',
      hK₀s]

/-- The cut-off family satisfies the seam identity when `K₀` and `L` do. -/
private theorem mfderiv_symm_cutoffFamily
    (hK₀t : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K₀ p v) =
        K₀ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hLt : ∀ p : (ℝ × ℝ) × M, suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L p v) = L (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    mfderiv I I φ.symm p.2 (cutoffFamily hσn hK₀ L hL ρ hρ p v) =
      cutoffFamily hσn hK₀ L hL ρ hρ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v) := by
  by_cases hp : suspensionCover φ p ∈ U
  · have hp' : suspensionCover φ (p.1 + (0, 1), φ.symm p.2) ∈ U := by
      rwa [suspensionCover_add_snd]
    set g := φ.symm.mfderivToContinuousLinearEquiv (by simp) p.2
    have hg : ∀ v, g v = mfderiv I I φ.symm p.2 v := fun v ↦
      congrArg (· v) (φ.symm.mfderivToContinuousLinearEquiv_coe (x := p.2) (by simp))
    -- Conjugation by `dφ⁻¹` is an algebra isomorphism, so it commutes with the Cayley path
    -- expression, and it carries the endpoints at `p` to the endpoints at the seam image of `p`.
    have hconj : g.conjContinuousAlgEquiv
        (LinearMap.toContinuousLinearMap (cutoffFamily hσn hK₀ L hL ρ hρ p).toLinearMap) =
        LinearMap.toContinuousLinearMap
          (cutoffFamily hσn hK₀ L hL ρ hρ (p.1 + (0, 1), φ.symm p.2)).toLinearMap := by
      rw [cutoffFamily_formula hσn hK₀ L hL ρ hρ hp, cutoffFamily_formula hσn hK₀ L hL ρ hρ hp',
        map_cayleyPathFormula, conj_eq_of_mfderiv_symm (hK₀t p),
        conj_eq_of_mfderiv_symm (hLt p hp), suspensionCover_add_snd]
    have h := congrArg (· (g v)) hconj
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply, LinearMap.coe_toContinuousLinearMap'] at h
    rw [hg, hg] at h
    -- An almost complex structure acts on vectors through its underlying linear map.
    exact h
  · have hp' : suspensionCover φ (p.1 + (0, 1), φ.symm p.2) ∉ U := by
      rwa [suspensionCover_add_snd]
    rw [cutoffFamily_of_notMem hσn hK₀ L hL ρ hρ hp, cutoffFamily_of_notMem hσn hK₀ L hL ρ hρ hp']
    exact hK₀t p v

variable [T2Space M] [LocallyCompactSpace M]

/-- The cut-off family is smooth when `K₀` is smooth, `L` is smooth over `q⁻¹(U)`, and the
cutoff is smooth with topological support in `U`. -/
private theorem contMDiffAt_cutoffFamily
    (hK₀s : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K₀ p).toLinearMap.toContinuousLinearMap))
    (hU : IsOpen U)
    (hLs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (L p).toLinearMap.toContinuousLinearMap) (suspensionCover φ ⁻¹' U))
    (hsρ : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U)
    (p₀ : (ℝ × ℝ) × M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (cutoffFamily hσn hK₀ L hL ρ hρ p).toLinearMap.toContinuousLinearMap) p₀ := by
  have hq := (isLocalDiffeomorph_suspensionCover φ).contMDiff
  by_cases hp₀ : suspensionCover φ p₀ ∈ U
  · have hUp : suspensionCover φ ⁻¹' U ∈ 𝓝 p₀ :=
      hq.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hp₀)
    have hs := ContMDiffAt.cayleyPathFormula_hom_bundle contMDiffAt_snd
      ((hsρ.comp hq) p₀) (hK₀s p₀) ((hLs p₀ hp₀).contMDiffAt hUp)
      (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E) (hK₀ p₀).tames
        (hL p₀ hp₀).tames (LinearMap.coe_toContinuousLinearMap _)
        (LinearMap.coe_toContinuousLinearMap _))
      (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E) (hK₀ p₀)
        (hL p₀ hp₀).tames
        (by simpa only [Function.comp_apply, abs_of_nonneg (hρ (suspensionCover φ p₀)).1] using
          (hρ (suspensionCover φ p₀)).2)
        (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _))
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [hUp] with p hp
    exact congrArg (fun B : E →L[ℝ] E ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) p.2 B)
      (cutoffFamily_formula hσn hK₀ L hL ρ hρ hp)
  · have hz : ∀ᶠ p in 𝓝 p₀, ρ (suspensionCover φ p) = 0 :=
      hq.continuous.continuousAt.eventually
        (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hp₀ (hsupp h))
    refine (hK₀s p₀).congr_of_eventuallyEq ?_
    filter_upwards [hz] with p hp
    rw [cutoffFamily_eq_background hσn hK₀ L hL ρ hρ hp]

/-! ### Relative vertical families -/

include hK₀ hL hρ in
/-- **Relative seam-compatible vertical families, with a specified cutoff.** Let `K₀` be a smooth
`σ`-compatible vertical family on `(ℝ × ℝ) × M`, periodic in `s` and satisfying the seam identity,
and let `L` be a vertical family with these properties over the preimage `q⁻¹(U)` of an open set
`U ⊆ (ℝ / ℤ) × Y_φ`. For a smooth cutoff `ρ` on `(ℝ / ℤ) × Y_φ` with values in `[0, 1]` and
topological support in `U`, there is a smooth `σ`-compatible vertical family `K`, periodic in `s`
and satisfying the seam identity, which is `L` where `ρ ∘ q = 1` and `K₀` where `ρ ∘ q = 0`. -/
theorem exists_verticalFamily_eq_of_cutoff
    (hK₀s : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K₀ p).toLinearMap.toContinuousLinearMap))
    (hK₀p : ∀ p, K₀ (p.1 + (1, 0), p.2) = K₀ p)
    (hK₀t : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K₀ p v) =
        K₀ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hU : IsOpen U)
    (hLs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (L p).toLinearMap.toContinuousLinearMap) (suspensionCover φ ⁻¹' U))
    (hLp : ∀ p, suspensionCover φ p ∈ U → L (p.1 + (1, 0), p.2) = L p)
    (hLt : ∀ p : (ℝ × ℝ) × M, suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L p v) = L (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hsρ : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ∃ K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          p.2 (K p).toLinearMap.toContinuousLinearMap) ∧
      (∀ p, K (p.1 + (1, 0), p.2) = K p) ∧
      (∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K p v) =
          K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ p, (hσn.symplecticFormAt p.2).Compatible (K p)) ∧
      (∀ p, ρ (suspensionCover φ p) = 1 → K p = L p) ∧
      (∀ p, ρ (suspensionCover φ p) = 0 → K p = K₀ p) := by
  refine ⟨cutoffFamily hσn hK₀ L hL ρ hρ,
    contMDiffAt_cutoffFamily hσn hK₀ L hL ρ hρ hK₀s hU hLs hsρ hsupp,
    cutoffFamily_add_fst hσn hK₀ L hL ρ hρ hK₀p hLp,
    mfderiv_symm_cutoffFamily hσn hK₀ L hL ρ hρ hK₀t hLt,
    compatible_cutoffFamily hσn hK₀ L hL ρ hρ, fun p hp ↦ ?_,
    fun p hp ↦ cutoffFamily_eq_background hσn hK₀ L hL ρ hρ hp⟩
  have hpU : suspensionCover φ p ∈ U :=
    hsupp (subset_tsupport ρ (by simp [Function.mem_support, hp]))
  exact cutoffFamily_eq_local hσn hK₀ L hL ρ hρ hpU hp

include hK₀ hL in
/-- **Relative seam-compatible vertical families.** Let `M` be second countable, let `K₀` be a
smooth `σ`-compatible vertical family on `(ℝ × ℝ) × M`, periodic in `s` and satisfying the seam
identity, and let `L` be a vertical family with these properties over the preimage `q⁻¹(U)` of an
open set `U ⊆ (ℝ / ℤ) × Y_φ`. For every closed set `A ⊆ U`, there is a smooth `σ`-compatible
vertical family `K`, periodic in `s` and satisfying the seam identity, which equals `L` over `A`
and `K₀` outside `U`. -/
theorem exists_verticalFamily_eqOn [SecondCountableTopology M]
    (hK₀s : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K₀ p).toLinearMap.toContinuousLinearMap))
    (hK₀p : ∀ p, K₀ (p.1 + (1, 0), p.2) = K₀ p)
    (hK₀t : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K₀ p v) =
        K₀ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hU : IsOpen U) {A : Set (UnitAddCircle × SmoothMappingTorus φ)} (hA : IsClosed A)
    (hAU : A ⊆ U)
    (hLs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (L p).toLinearMap.toContinuousLinearMap) (suspensionCover φ ⁻¹' U))
    (hLp : ∀ p, suspensionCover φ p ∈ U → L (p.1 + (1, 0), p.2) = L p)
    (hLt : ∀ p : (ℝ × ℝ) × M, suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L p v) = L (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          p.2 (K p).toLinearMap.toContinuousLinearMap) ∧
      (∀ p, K (p.1 + (1, 0), p.2) = K p) ∧
      (∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K p v) =
          K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ p, (hσn.symplecticFormAt p.2).Compatible (K p)) ∧
      (∀ p, suspensionCover φ p ∈ A → K p = L p) ∧
      (∀ p, suspensionCover φ p ∉ U → K p = K₀ p) := by
  have := (𝓘(ℝ).prod (𝓘(ℝ).prod I)).locallyCompactSpace
  have : LocallyCompactSpace (UnitAddCircle × SmoothMappingTorus φ) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℝ (ModelProd ℝ H)) _
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨ρ, hsρ, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) hV hA hAV
  have hρ : ∀ y, ρ y ∈ Icc 0 1 := fun y ↦ hrange (mem_range_self y)
  have ht : tsupport ρ ⊆ U := by
    rw [tsupport, hsupp]
    exact hVU
  obtain ⟨K, hKs, hKp, hKt, hKc, hlocal, hbase⟩ :=
    exists_verticalFamily_eq_of_cutoff hσn hK₀ L hL ρ hρ hK₀s hK₀p hK₀t hU hLs hLp hLt hsρ ht
  refine ⟨K, hKs, hKp, hKt, hKc, fun p hp ↦ hlocal p ((hone _).mp hp), fun p hp ↦ hbase p ?_⟩
  exact Function.notMem_support.mp fun h ↦ hp (ht (subset_tsupport ρ h))

include hK₀ hL in
/-- **Compatible block structures on a symplectic suspension with prescribed vertical part.**
Let `φ` preserve `σ`, let `M` be second countable, and let `K₀` and `L` be as in
`TauCeti.SmoothMappingTorus.exists_verticalFamily_eqOn`, with `L` prescribed over the preimage of
an open set `U ⊆ (ℝ / ℤ) × Y_φ`. For every closed set `A ⊆ U`, there is a smooth almost complex
structure `J` on `(ℝ / ℤ) × Y_φ` compatible with `Ω = ds ∧ dt + σ_v`, sending `∂_s` to the
suspension vector field `T`, which in the coordinates `(s, t, x)` sends `a ∂_s + b ∂_t + v` to
`-b ∂_s + a ∂_t + L_((s, t), x) v` at the points `([s], [t, x])` of `A`, and to
`-b ∂_s + a ∂_t + (K₀)_((s, t), x) v` at the points outside `U`. -/
theorem exists_compatible_suspensionForm_eqOn [SecondCountableTopology M]
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    (hK₀s : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K₀ p).toLinearMap.toContinuousLinearMap))
    (hK₀p : ∀ p, K₀ (p.1 + (1, 0), p.2) = K₀ p)
    (hK₀t : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K₀ p v) =
        K₀ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hU : IsOpen U) {A : Set (UnitAddCircle × SmoothMappingTorus φ)} (hA : IsClosed A)
    (hAU : A ⊆ U)
    (hLs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (L p).toLinearMap.toContinuousLinearMap) (suspensionCover φ ⁻¹' U))
    (hLp : ∀ p, suspensionCover φ p ∈ U → L (p.1 + (1, 0), p.2) = L p)
    (hLt : ∀ p : (ℝ × ℝ) × M, suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L p v) = L (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
        (UnitAddCircle × SmoothMappingTorus φ),
      (suspensionForm φ σ hσ).Compatible J ∧
      (∀ y, J y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2)) ∧
      (∀ (s t : ℝ) (x : M), ((s : UnitAddCircle), mk φ t x) ∈ A →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, L ((s, t), x) v)))) ∧
      (∀ (s t : ℝ) (x : M), ((s : UnitAddCircle), mk φ t x) ∉ U →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K₀ ((s, t), x) v)))) := by
  obtain ⟨K, hKs, hKp, hKt, hKc, hlocal, hbase⟩ :=
    exists_verticalFamily_eqOn hσn hK₀ L hL hK₀s hK₀p hK₀t hU hA hAU hLs hLp hLt
  refine ⟨suspensionAlmostComplexStructure φ hKs hKp hKt,
    compatible_suspensionAlmostComplexStructure φ hKs hKp hKt hσn hKc,
    suspensionAlmostComplexStructure_apply_symm_one_zero φ hKs hKp hKt,
    fun s t x hx a b v ↦ ?_, fun s t x hx a b v ↦ ?_⟩
  · rw [suspensionAlmostComplexStructure_mk, hlocal ((s, t), x) (by rwa [suspensionCover_apply])]
  · rw [suspensionAlmostComplexStructure_mk, hbase ((s, t), x) (by rwa [suspensionCover_apply])]

end TauCeti.SmoothMappingTorus
