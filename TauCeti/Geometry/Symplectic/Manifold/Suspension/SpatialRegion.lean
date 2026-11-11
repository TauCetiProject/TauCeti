/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.SeamFamily
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Seam-compatible families with prescribed values on closed spatial regions

Let `φ` be a symplectomorphism of a finite-dimensional manifold `(M, σ)`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ` carry the form `Ω = ds ∧ dt + σ_v`. A block almost complex structure on
`X_φ` descends along the covering map `q : ((s, t), x) ↦ ([s], [t, x])`
(`TauCeti.SmoothMappingTorus.suspensionCover`) from a *vertical family* `K_((s,t),x)` of
`σ`-compatible structures on `T_x M`, smooth in `((s, t), x)`, periodic in `s` and satisfying the
seam identity `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

This file prescribes the vertical part on a closed region `A` of `X_φ`, for families of such data
over a parameter manifold `Λ`. A region `B` of the mapping torus `Y_φ` is the case
`A = (ℝ / ℤ) × B`. Let `K_l` be a background family of vertical families, jointly smooth in
`(l, ((s, t), x))`, each `σ`-compatible, periodic in `s` and seam-compatible, for instance the
families `TauCeti.SmoothMappingTorus.seamFamily` built from a smooth family of compatible
structures `K₀ l` on `M`. Let `L_l` be a second family, given only over an open neighbourhood `U`
of `A`: it is required to be smooth, compatible, periodic and seam-compatible only at the points
of `q⁻¹ U`. Since `q⁻¹ U` is invariant under the deck transformations, these requirements on `L`
are those of the vertical bundle over `U` read on the cover, and prescribing a single family over
all of `U` encodes the agreement of the data on overlaps. Then there is a family `K'_l` with all
these properties everywhere, equal to `L_l` over `A` and to `K_l` outside `U`
(`TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eq_of_suspensionCover_mem`). It also
equals `K_l` at every point where `L_l` already does; with the seam-family background, this keeps
the fixed time-end collar `|t| ≤ 1/3` wherever the prescription already has it.

The construction cuts `L` off against `K` in the Cayley chart of `K`, with weight `ρ(q p)` for a
smooth cutoff `ρ : X_φ → [0, 1]` equal to one on `A` and with topological support in `U`. The
weight is a function on `X_φ` pulled back along `q`, so it takes the same value at a point and at
its deck translates. In operator coordinates the interpolated structure is the rational
expression `TauCeti.cayleyPathFormula (ρ (q p)) (K_l p) (L_l p)`. Conjugation by the differential
of `φ⁻¹` is an algebra isomorphism, so it commutes with this expression
(`TauCeti.map_cayleyPathFormula`), and the seam identity of both endpoints gives that of the
interpolation. Compatibility comes from the convexity of the compatible Cayley ball
(`TauCeti.SymplecticForm.Compatible.compatible_cayleyInterp`), and joint smoothness from the
smoothness of the Cayley path expression in the tangent endomorphism bundle
(`ContMDiffAt.cayleyPathFormula_hom_bundle`). The smooth Urysohn function on `X_φ` exists because
`X_φ` is Hausdorff, and σ-compact when `M` is.

The descended block structures `J_l` on `X_φ` are jointly smooth in `(l, y)`, compatible with `Ω`,
send `∂_s` to the suspension vector field `T`, act through `L_l` over `A` and agree with the
structures `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure` built from `K₀ l` outside `U`
(`TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_family_eq_of_mem`). Neither
closedness of `σ` nor compactness of `M`, of `Λ` or of `A` is used.

## Main results

* `TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eq_of_spatialCutoff`: relative extension
  of parametrized seam-compatible vertical families, for a specified cutoff on `X_φ`.
* `TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eq_of_suspensionCover_mem`: relative
  extension from a closed region of `X_φ`.
* `TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_family_eq_of_mem`: the descended
  smooth family of `Ω`-compatible block structures on `X_φ`, with prescribed vertical part over
  the closed region, the seam structures outside its neighbourhood, and the collar structures
  wherever the prescription has them.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  `ℝ × Y_φ`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Sections 2.5 and 4.1 (compatible Cayley charts and relative extension).
-/

public noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} (hσn : σ.IsNondegenerate)
  {Λ : Type*} {K : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  (hK : ∀ l p, (hσn.symplecticFormAt p.2).Compatible (K l p))
  {U : Set (UnitAddCircle × SmoothMappingTorus φ)}
  (L : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
  (hL : ∀ l p, suspensionCover φ p ∈ U → (hσn.symplecticFormAt p.2).Compatible (L l p))
  (ρ : UnitAddCircle × SmoothMappingTorus φ → ℝ) (hρ : ∀ y, ρ y ∈ Icc 0 1)

/-! ### The cut-off family -/

open Classical in
/-- The family that, at a point `p` over `U`, interpolates from `K l p` towards `L l p` with the
weight `ρ (q p)` in the Cayley chart of `K l p`, and equals `K l p` at the points not over `U`. -/
private def spatialCutoff (l : Λ) (p : (ℝ × ℝ) × M) :
    AlmostComplexStructure (TangentSpace I p.2) :=
  if hp : suspensionCover φ p ∈ U then
    (hK l p).cayleyInterp (V := E) (hL l p hp) (hρ (suspensionCover φ p))
  else K l p

private theorem spatialCutoff_of_mem {l : Λ} {p : (ℝ × ℝ) × M} (hp : suspensionCover φ p ∈ U) :
    spatialCutoff hσn hK L hL ρ hρ l p =
      (hK l p).cayleyInterp (V := E) (hL l p hp) (hρ (suspensionCover φ p)) :=
  dite_eq_left hp

private theorem spatialCutoff_of_notMem {l : Λ} {p : (ℝ × ℝ) × M}
    (hp : suspensionCover φ p ∉ U) : spatialCutoff hσn hK L hL ρ hρ l p = K l p :=
  dite_eq_right hp

private theorem compatible_spatialCutoff (l : Λ) (p : (ℝ × ℝ) × M) :
    (hσn.symplecticFormAt p.2).Compatible (spatialCutoff hσn hK L hL ρ hρ l p) := by
  by_cases hp : suspensionCover φ p ∈ U
  · rw [spatialCutoff_of_mem hσn hK L hL ρ hρ hp]
    exact (hK l p).compatible_cayleyInterp (V := E) (hL l p hp) _
  · rw [spatialCutoff_of_notMem hσn hK L hL ρ hρ hp]
    exact hK l p

private theorem spatialCutoff_eq_background {l : Λ} {p : (ℝ × ℝ) × M}
    (hp : ρ (suspensionCover φ p) = 0) : spatialCutoff hσn hK L hL ρ hρ l p = K l p := by
  by_cases hpU : suspensionCover φ p ∈ U
  · rw [spatialCutoff_of_mem hσn hK L hL ρ hρ hpU]
    simp only [hp]
    exact (hK l p).cayleyInterp_zero (V := E) (hL l p hpU)
  · exact spatialCutoff_of_notMem hσn hK L hL ρ hρ hpU

private theorem spatialCutoff_eq_local {l : Λ} {p : (ℝ × ℝ) × M} (hpU : suspensionCover φ p ∈ U)
    (hp : ρ (suspensionCover φ p) = 1) : spatialCutoff hσn hK L hL ρ hρ l p = L l p := by
  rw [spatialCutoff_of_mem hσn hK L hL ρ hρ hpU]
  simp only [hp]
  exact (hK l p).cayleyInterp_one (V := E) (hL l p hpU)

/-- Where the prescribed structure equals the background one, the cut-off family does too: the
Cayley coordinate of a structure relative to itself is zero. -/
private theorem spatialCutoff_eq_of_eq {l : Λ} {p : (ℝ × ℝ) × M} (h : L l p = K l p) :
    spatialCutoff hσn hK L hL ρ hρ l p = K l p := by
  by_cases hp : suspensionCover φ p ∈ U
  · rw [spatialCutoff_of_mem hσn hK L hL ρ hρ hp]
    refine (hK l p).eq_of_cayley_eq
      ((hK l p).compatible_cayleyInterp (V := E) (hL l p hp) _).tames (hK l p).tames
      (((hK l p).cayley_cayleyInterp (V := E) (hL l p hp) _).trans ?_)
    rw [h]
    exact (congrArg (ρ (suspensionCover φ p) • ·)
      (AlmostComplexStructure.cayley_self (V := E) _)).trans
      ((smul_zero _).trans (AlmostComplexStructure.cayley_self _).symm)
  · exact spatialCutoff_of_notMem hσn hK L hL ρ hρ hp

/-- Over `U`, the cut-off family is the Cayley path expression in `K l p` and `L l p` with weight
`ρ (q p)`. -/
private theorem spatialCutoff_formula {l : Λ} {p : (ℝ × ℝ) × M} (hp : suspensionCover φ p ∈ U) :
    LinearMap.toContinuousLinearMap (spatialCutoff hσn hK L hL ρ hρ l p).toLinearMap =
      cayleyPathFormula (ρ (suspensionCover φ p))
        (LinearMap.toContinuousLinearMap (K l p).toLinearMap)
        (LinearMap.toContinuousLinearMap (L l p).toLinearMap) := by
  rw [spatialCutoff_of_mem hσn hK L hL ρ hρ hp]
  exact (hK l p).toContinuousLinearMap_cayleyInterp (V := E) (hL l p hp) _
    (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)

/-- The cut-off family is periodic in `s` when the background and the prescribed families are. -/
private theorem spatialCutoff_add_fst (hKs : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hLs : ∀ l p, suspensionCover φ p ∈ U → L l (p.1 + (1, 0), p.2) = L l p)
    (l : Λ) (p : (ℝ × ℝ) × M) :
    spatialCutoff hσn hK L hL ρ hρ l (p.1 + (1, 0), p.2) = spatialCutoff hσn hK L hL ρ hρ l p := by
  have hq := suspensionCover_add_one_zero φ p
  by_cases hp : suspensionCover φ p ∈ U
  · -- Both values are the Cayley path expression in the same endpoints with the same weight.
    have h := spatialCutoff_formula hσn hK L hL ρ hρ (l := l) (hq ▸ hp)
    rw [hKs, hLs l p hp, hq, ← spatialCutoff_formula hσn hK L hL ρ hρ hp] at h
    exact AlmostComplexStructure.toLinearMap_injective (LinearMap.toContinuousLinearMap.injective h)
  · rw [spatialCutoff_of_notMem hσn hK L hL ρ hρ (hq ▸ hp),
      spatialCutoff_of_notMem hσn hK L hL ρ hρ hp, hKs]

omit [IsManifold I ∞ M] in
/-- If `dφ⁻¹ ∘ J = J' ∘ dφ⁻¹` at `x`, then `J'` is the conjugate of `J` by the differential of
`φ⁻¹` at `x`. -/
private theorem conjContinuousAlgEquiv_eq_of_mfderiv_symm {x : M}
    {J : AlmostComplexStructure (TangentSpace I x)}
    {J' : AlmostComplexStructure (TangentSpace I (φ.symm x))}
    (h : ∀ v, mfderiv I I φ.symm x (J v) = J' (mfderiv I I φ.symm x v)) :
    (φ.symm.mfderivToContinuousLinearEquiv (by simp) x).conjContinuousAlgEquiv
        (LinearMap.toContinuousLinearMap J.toLinearMap) =
      LinearMap.toContinuousLinearMap J'.toLinearMap := by
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

/-- The cut-off family satisfies the seam identity when the background and the prescribed
families do. -/
private theorem mfderiv_symm_spatialCutoff
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hLt : ∀ l (p : (ℝ × ℝ) × M), suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (l : Λ) (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    mfderiv I I φ.symm p.2 (spatialCutoff hσn hK L hL ρ hρ l p v) =
      spatialCutoff hσn hK L hL ρ hρ l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v) := by
  have hq := suspensionCover_add_zero_one_symm φ p
  by_cases hp : suspensionCover φ p ∈ U
  · set g := φ.symm.mfderivToContinuousLinearEquiv (by simp) p.2
    have hg : ∀ v, g v = mfderiv I I φ.symm p.2 v := fun v ↦
      congrArg (· v) (φ.symm.mfderivToContinuousLinearEquiv_coe (x := p.2) (by simp))
    -- Conjugation by `dφ⁻¹` is an algebra isomorphism, so it commutes with the Cayley path
    -- expression, and it carries both endpoints at `p` to the endpoints at the seam image of `p`,
    -- where the weight is the same.
    have hconj : g.conjContinuousAlgEquiv
        (LinearMap.toContinuousLinearMap (spatialCutoff hσn hK L hL ρ hρ l p).toLinearMap) =
        LinearMap.toContinuousLinearMap
          (spatialCutoff hσn hK L hL ρ hρ l (p.1 + (0, 1), φ.symm p.2)).toLinearMap := by
      rw [spatialCutoff_formula hσn hK L hL ρ hρ hp,
        spatialCutoff_formula hσn hK L hL ρ hρ (hq ▸ hp), hq, map_cayleyPathFormula,
        conjContinuousAlgEquiv_eq_of_mfderiv_symm (hKt l p),
        conjContinuousAlgEquiv_eq_of_mfderiv_symm (hLt l p hp)]
    have h := congrArg (· (g v)) hconj
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply, LinearMap.coe_toContinuousLinearMap'] at h
    rw [hg, hg] at h
    -- An almost complex structure acts on vectors through its underlying linear map.
    exact h
  · rw [spatialCutoff_of_notMem hσn hK L hL ρ hρ hp,
      spatialCutoff_of_notMem hσn hK L hL ρ hρ (hq ▸ hp)]
    exact hKt l p v

variable [T2Space M] [LocallyCompactSpace M]
  {EΛ HΛ : Type*} [NormedAddCommGroup EΛ] [NormedSpace ℝ EΛ] [TopologicalSpace HΛ]
  {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ] [ChartedSpace HΛ Λ]

/-- The cut-off family is jointly smooth in the parameter and the point when the background family
is, the prescribed family is jointly smooth over `q⁻¹ U`, and the cutoff is smooth with
topological support in `U`. -/
private theorem contMDiff_spatialCutoff
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hU : IsOpen U)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (univ ×ˢ (suspensionCover φ ⁻¹' U)))
    (hsρ : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (spatialCutoff hσn hK L hL ρ hρ r.1 r.2).toLinearMap.toContinuousLinearMap) := by
  have hq := (isLocalDiffeomorph_suspensionCover φ).contMDiff
  rintro ⟨l₀, p₀⟩
  by_cases hp₀ : suspensionCover φ p₀ ∈ U
  · have hUr : univ ×ˢ (suspensionCover φ ⁻¹' U) ∈ 𝓝 (l₀, p₀) :=
      prod_mem_nhds Filter.univ_mem (hq.continuous.continuousAt.preimage_mem_nhds
        (hU.mem_nhds hp₀))
    have hs := ContMDiffAt.cayleyPathFormula_hom_bundle (contMDiffAt_snd.comp _ contMDiffAt_snd)
      ((hsρ.comp (hq.comp contMDiff_snd)) (l₀, p₀)) (hKs (l₀, p₀))
      ((hLs (l₀, p₀) ⟨mem_univ _, hp₀⟩).contMDiffAt hUr)
      (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E) (hK l₀ p₀).tames
        (hL l₀ p₀ hp₀).tames (LinearMap.coe_toContinuousLinearMap _)
        (LinearMap.coe_toContinuousLinearMap _))
      (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E) (hK l₀ p₀)
        (hL l₀ p₀ hp₀).tames
        (by simpa only [Function.comp_apply, abs_of_nonneg (hρ _).1] using
          (hρ (suspensionCover φ p₀)).2)
        (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _))
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [hUr] with r hr
    exact congrArg (fun B : E →L[ℝ] E ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) r.2.2 B)
      (spatialCutoff_formula hσn hK L hL ρ hρ hr.2)
  · -- Near a point not over `U` the cutoff vanishes, so the family is the background family.
    have hz : ∀ᶠ r : Λ × ((ℝ × ℝ) × M) in 𝓝 (l₀, p₀), ρ (suspensionCover φ r.2) = 0 :=
      (hq.continuous.comp continuous_snd).continuousAt.eventually
        (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hp₀ (hsupp h))
    refine (hKs (l₀, p₀)).congr_of_eventuallyEq ?_
    filter_upwards [hz] with r hr
    rw [spatialCutoff_eq_background hσn hK L hL ρ hρ hr]

/-! ### Relative parametrized vertical families -/

include hK hL hρ in
/-- **Parametrized seam-compatible vertical families with a prescribed spatial cutoff.** Let
`K l` be a family, over a manifold `Λ`, of `σ`-compatible vertical families on `(ℝ × ℝ) × M`,
jointly smooth in `(l, ((s, t), x))`, periodic in `s` and satisfying the seam identity, and let
`L l` be a family with these properties at the points `p` with `q p` in an open set `U` of
`(ℝ / ℤ) × Y_φ`, where `q` is the covering map. For a smooth cutoff `ρ : (ℝ / ℤ) × Y_φ → [0, 1]`
with topological support in `U`, there is a family `K' l` with these properties everywhere, which
is `L l` where `ρ ∘ q = 1`, is `K l` where `ρ ∘ q = 0`, and agrees with `K l` at every point where
`L l` does. -/
theorem exists_verticalFamily_family_eq_of_spatialCutoff
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hKp : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hU : IsOpen U)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (univ ×ˢ (suspensionCover φ ⁻¹' U)))
    (hLp : ∀ l p, suspensionCover φ p ∈ U → L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l (p : (ℝ × ℝ) × M), suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hsρ : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ∃ K' : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K' r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l p, K' l (p.1 + (1, 0), p.2) = K' l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K' l p v) =
          K' l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K' l p)) ∧
      (∀ l p, ρ (suspensionCover φ p) = 1 → K' l p = L l p) ∧
      (∀ l p, ρ (suspensionCover φ p) = 0 → K' l p = K l p) ∧
      (∀ l p, L l p = K l p → K' l p = K l p) := by
  refine ⟨spatialCutoff hσn hK L hL ρ hρ,
    contMDiff_spatialCutoff hσn hK L hL ρ hρ hKs hU hLs hsρ hsupp,
    spatialCutoff_add_fst hσn hK L hL ρ hρ hKp hLp,
    mfderiv_symm_spatialCutoff hσn hK L hL ρ hρ hKt hLt,
    compatible_spatialCutoff hσn hK L hL ρ hρ, fun l p hp ↦ ?_,
    fun l p hp ↦ spatialCutoff_eq_background hσn hK L hL ρ hρ hp,
    fun l p h ↦ spatialCutoff_eq_of_eq hσn hK L hL ρ hρ h⟩
  have hpU : suspensionCover φ p ∈ U := hsupp (subset_tsupport ρ (by simp [mem_support, hp]))
  exact spatialCutoff_eq_local hσn hK L hL ρ hρ hpU hp

omit hρ

variable [SigmaCompactSpace M]

include hK hL in
/-- **Parametrized seam-compatible vertical families with values prescribed on a closed region.**
Let `K l` be a family, over a manifold `Λ`, of `σ`-compatible vertical families on
`(ℝ × ℝ) × M`, jointly smooth in `(l, ((s, t), x))`, periodic in `s` and satisfying the seam
identity, and let `L l` be a family with these properties at the points `p` with `q p` in an open
set `U` of `(ℝ / ℤ) × Y_φ`, where `q` is the covering map. For every closed set `A ⊆ U` there is
a family `K' l` with these properties everywhere, which is `L l` over `A`, is `K l` outside `U`,
and agrees with `K l` at every point where `L l` does. -/
theorem exists_verticalFamily_family_eq_of_suspensionCover_mem
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hKp : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hU : IsOpen U) {A : Set (UnitAddCircle × SmoothMappingTorus φ)} (hA : IsClosed A)
    (hAU : A ⊆ U)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (univ ×ˢ (suspensionCover φ ⁻¹' U)))
    (hLp : ∀ l p, suspensionCover φ p ∈ U → L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l (p : (ℝ × ℝ) × M), suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    ∃ K' : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2),
      ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          r.2.2 (K' r.1 r.2).toLinearMap.toContinuousLinearMap) ∧
      (∀ l p, K' l (p.1 + (1, 0), p.2) = K' l p) ∧
      (∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K' l p v) =
          K' l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) ∧
      (∀ l p, (hσn.symplecticFormAt p.2).Compatible (K' l p)) ∧
      (∀ l p, suspensionCover φ p ∈ A → K' l p = L l p) ∧
      (∀ l p, suspensionCover φ p ∉ U → K' l p = K l p) ∧
      (∀ l p, L l p = K l p → K' l p = K l p) := by
  have : LocallyCompactSpace (ModelProd ℝ (ModelProd ℝ H)) :=
    (𝓘(ℝ).prod (𝓘(ℝ).prod I)).locallyCompactSpace
  have : LocallyCompactSpace (UnitAddCircle × SmoothMappingTorus φ) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℝ (ModelProd ℝ H)) _
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨ρ, hsρ, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) hV hA hAV
  have hρ : ∀ y, ρ y ∈ Icc 0 1 := fun y ↦ hrange (mem_range_self y)
  have ht : tsupport ρ ⊆ U := by
    rw [tsupport, hsupp]
    exact hVU
  obtain ⟨K', hK's, hK'p, hK't, hK'c, hlocal, hbase, hagree⟩ :=
    exists_verticalFamily_family_eq_of_spatialCutoff hσn hK L hL ρ hρ hKs hKp hKt hU hLs hLp hLt
      hsρ ht
  refine ⟨K', hK's, hK'p, hK't, hK'c, fun l p hp ↦ hlocal l p ((hone _).mp hp),
    fun l p hp ↦ hbase l p ?_, hagree⟩
  exact notMem_support.mp fun h ↦ hp (ht (subset_tsupport ρ h))

/-! ### Descended families of block structures -/

omit hK

include hL in
/-- **Families of compatible block structures on a symplectic suspension with values prescribed on
a closed region.** Let `φ` preserve the nondegenerate form `σ`, and let `K₀ l` be a smooth family
of `σ`-compatible almost complex structures on `M`, over a manifold `Λ`. Let `U` be an open set
of `(ℝ / ℤ) × Y_φ`, and let `L l` be a family of vertical families on `(ℝ × ℝ) × M` which, at the
points over `U`, is jointly smooth, `σ`-compatible, periodic in `s` and satisfies the seam
identity. For every closed set `A ⊆ U` there is a family `J l` of almost complex structures on
`(ℝ / ℤ) × Y_φ`, jointly smooth in `(l, y)`, such that:

* each `J l` is compatible with `Ω = ds ∧ dt + σ_v` and sends `∂_s` to the suspension vector field
  `T`;
* at the points `([s], [t, x])` of `A`, in the coordinates `(s, t, x)`, `J l` sends
  `a ∂_s + b ∂_t + v` to `-b ∂_s + a ∂_t + L_l((s, t), x) v`;
* outside `U`, `J l` is the seam structure built from `K₀ l`;
* on the collar `|t| ≤ 1/3`, wherever `L l` is `K₀ l`, `J l` sends `a ∂_s + b ∂_t + v` to
  `-b ∂_s + a ∂_t + K₀ l v`. -/
theorem exists_compatible_suspensionForm_family_eq_of_mem
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    {K₀ : Λ → SmoothAlmostComplexStructure I M} (hK₀ : ∀ l, σ.Compatible (K₀ l))
    (hK₀s : ContMDiff (IΛ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Λ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hU : IsOpen U) {A : Set (UnitAddCircle × SmoothMappingTorus φ)} (hA : IsClosed A)
    (hAU : A ⊆ U)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (univ ×ˢ (suspensionCover φ ⁻¹' U)))
    (hLp : ∀ l p, suspensionCover φ p ∈ U → L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l (p : (ℝ × ℝ) × M), suspensionCover φ p ∈ U → ∀ v : TangentSpace I p.2,
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
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
      (∀ l (s t : ℝ) (x : M), ((s : UnitAddCircle), mk φ t x) ∈ A →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J l ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, L l ((s, t), x) v)))) ∧
      (∀ l, ∀ y ∉ U, (J l).almostComplexStructureAt y =
        (seamAlmostComplexStructure hσ (hK₀ l)).almostComplexStructureAt y) ∧
      (∀ l (s t : ℝ) (x : M), t ∈ Icc (-(1 / 3) : ℝ) (1 / 3) →
        L l ((s, t), x) = (K₀ l).almostComplexStructureAt x →
        ∀ (a b : ℝ) (v : TangentSpace I x),
          J l ((s : UnitAddCircle), mk φ t x)
              ((Manifold.tangentSpaceProdEquiv _).symm
                (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                  ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
            (Manifold.tangentSpaceProdEquiv _).symm
              (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K₀ l x v)))) := by
  -- The background is the family of seam families built from `K₀ l`.
  obtain ⟨K', hK's, hK'p, hK't, hK'c, hlocal, hbase, hagree⟩ :=
    exists_verticalFamily_family_eq_of_suspensionCover_mem hσn
      (K := fun l ↦ seamFamily hσ (hK₀ l)) (fun l ↦ compatible_seamFamily hσ (hK₀ l) hσn) L hL
      (contMDiff_seamFamily_family hσ hK₀ hK₀s) (fun l ↦ seamFamily_add_fst hσ (hK₀ l))
      (fun l ↦ mfderiv_symm_seamFamily hσ (hK₀ l)) hU hA hAU hLs hLp hLt
  refine ⟨fun l ↦ suspensionAlmostComplexStructure φ
      (hK's.comp (contMDiff_const.prodMk contMDiff_id)) (hK'p l) (hK't l),
    contMDiff_suspensionAlmostComplexStructure_family φ hK's hK'p hK't,
    fun l ↦ compatible_suspensionAlmostComplexStructure φ _ _ _ hσn (hK'c l),
    fun l ↦ suspensionAlmostComplexStructure_apply_symm_one_zero φ _ _ _,
    fun l s t x hx a b v ↦ ?_, fun l y hy ↦ ?_, fun l s t x ht hLK a b v ↦ ?_⟩
  · -- `dsimp` evaluates the slice `p ↦ (l, p)` of the parametrized vertical family at `l`.
    rw [suspensionAlmostComplexStructure_mk]
    dsimp only [id]
    rw [hlocal l ((s, t), x) (by rwa [suspensionCover_apply])]
  · -- Outside `U` both structures act through the seam family of `K₀ l` in the coordinates
    -- `(s, t, x)`, which reach every tangent vector.
    obtain ⟨⟨⟨s, t⟩, x⟩, rfl⟩ := suspensionCover_surjective φ y
    have hK' : K' l ((s, t), x) = seamFamily hσ (hK₀ l) ((s, t), x) := hbase l _ hy
    have key (a b : ℝ) (v : TangentSpace I x) :
        suspensionAlmostComplexStructure φ (hK's.comp (contMDiff_const.prodMk contMDiff_id))
            (hK'p l) (hK't l) ((s : UnitAddCircle), mk φ t x)
            ((Manifold.tangentSpaceProdEquiv _).symm
              (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
          seamAlmostComplexStructure hσ (hK₀ l) ((s : UnitAddCircle), mk φ t x)
            ((Manifold.tangentSpaceProdEquiv _).symm
              (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) := by
      rw [suspensionAlmostComplexStructure_mk, seamAlmostComplexStructure_mk_apply]
      dsimp only [id]
      rw [hK']
    apply AlmostComplexStructure.toLinearMap_injective
    rw [suspensionCover_apply, SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    ext w
    obtain ⟨a, b, v, rfl⟩ : ∃ (a b : ℝ) (v : TangentSpace I x),
        w = (Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) := by
      obtain ⟨b, v, hw⟩ := exists_mfderiv_uncurry_mk_eq φ t x
        (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) _ w).2
      exact ⟨(Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) _ w).1, b, v,
        by rw [hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]⟩
    exact key a b v
  · have hK : L l ((s, t), x) = seamFamily hσ (hK₀ l) ((s, t), x) := by
      rw [hLK, seamFamily_eq_of_mem_Icc hσ (hK₀ l) ht]
    rw [suspensionAlmostComplexStructure_mk]
    dsimp only [id]
    rw [hagree l _ hK, seamFamily_eq_of_mem_Icc hσ (hK₀ l) ht,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

end TauCeti.SmoothMappingTorus
