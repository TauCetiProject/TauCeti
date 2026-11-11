/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.SeamFamily
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Seam-compatible families with prescribed values on closed parameter faces

Let `φ` be a symplectomorphism of a finite-dimensional manifold `(M, σ)`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ` carry the form `Ω = ds ∧ dt + σ_v`. A block almost complex structure on
`X_φ` descends from a *vertical family* `K_((s,t),x)` of `σ`-compatible structures on `T_x M`,
smooth in `((s, t), x)`, periodic in `s` and satisfying the seam identity
`dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

This file treats families of such data over a parameter manifold `Λ`, for instance a compact
manifold with corners, with values prescribed on a closed set `F ⊆ Λ`, such as a union of closed
faces. Let `K_l` be a background family of vertical families, jointly smooth in
`(l, ((s, t), x))`, each `σ`-compatible, periodic in `s` and seam-compatible; the vertical
families `TauCeti.SmoothMappingTorus.seamFamily` built from a smooth family of compatible
structures `K₀ l` on `M` are an example (`TauCeti.SmoothMappingTorus.contMDiff_seamFamily_family`).
Let `L_l` be a second family with the same properties, but given only for parameters `l` in an
open neighbourhood `W` of `F`. Prescribing a single family on a neighbourhood of all of `F`
encodes the agreement of the data on overlaps and face intersections. Then there is a family
`K'_l` with all these properties for every `l ∈ Λ`, equal to `L_l` for `l ∈ F` and to `K_l` for
`l ∉ W` (`TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eqOn`). It also equals `K_l` at
every point where `L_l` already does. With the seam-family background this is the compatibility
with the fixed time-end collars: where the prescribed data restrict to `K₀ l` on the collar
`|t| ≤ 1/3`, so does the result.

The construction cuts `L` off against `K` in the Cayley chart of `K`, with weight `ρ(l)` for a
smooth cutoff `ρ : Λ → [0, 1]` equal to one on `F` and with topological support in `W`. In
operator coordinates the interpolated structure is the rational expression
`TauCeti.cayleyPathFormula (ρ l) (K_l) (L_l)`. Since the weight depends only on the parameter,
it is the same at a point and at its deck translates. Conjugation by the differential of `φ⁻¹` is
an algebra isomorphism, so it commutes with this expression (`TauCeti.map_cayleyPathFormula`);
hence the seam identity of both endpoints gives that of the interpolation. Compatibility comes
from the convexity of the compatible Cayley ball
(`TauCeti.SymplecticForm.Compatible.compatible_cayleyInterp`), and joint smoothness from the
smoothness of the Cayley path expression in the tangent endomorphism bundle
(`ContMDiffAt.cayleyPathFormula_hom_bundle`). This cutoff argument, including the passage from a
specified cutoff to a closed set, adapts the relative extension of a single compatible structure
`TauCeti.SmoothTwoForm.Compatible.exists_compatible_eq_of_cutoff` and
`TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn` (`AlmostComplex/Extension.lean`) to
parametrized seam-compatible vertical families.

The descended block structures `J_l` on `X_φ` are then jointly smooth in `(l, y)`, compatible
with `Ω`, send `∂_s` to the suspension vector field `T`, act through `L_l` for `l ∈ F` and are the
structures `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure` built from `K₀ l` for `l ∉ W`
(`TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_family_eqOn`). Neither closedness of
`σ` nor compactness of `M` or of `Λ` is used. The symplectomorphism `φ` is the same for every
parameter.

## Main results

* `TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eq_of_cutoff`: relative extension of
  parametrized seam-compatible vertical families, for a specified cutoff on the parameter
  manifold.
* `TauCeti.SmoothMappingTorus.exists_verticalFamily_family_eqOn`: relative extension from a
  closed set of parameters.
* `TauCeti.SmoothMappingTorus.exists_compatible_suspensionForm_family_eqOn`: the descended
  smooth family of `Ω`-compatible block structures on `X_φ`, with prescribed vertical part over
  the closed set of parameters, the seam structures away from its neighbourhood, and the collar
  structures wherever the prescription has them.

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
  {W : Set Λ} (L : Λ → ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
  (hL : ∀ l ∈ W, ∀ p, (hσn.symplecticFormAt p.2).Compatible (L l p))
  (ρ : Λ → ℝ) (hρ : ∀ l, ρ l ∈ Icc 0 1)

/-! ### The cut-off family -/

open Classical in
/-- The family that, at the parameter `l ∈ W`, interpolates from `K l p` towards `L l p` with the
weight `ρ l` in the Cayley chart of `K l p`, and equals `K l p` for `l ∉ W`. -/
private def faceCutoff (l : Λ) (p : (ℝ × ℝ) × M) : AlmostComplexStructure (TangentSpace I p.2) :=
  if hl : l ∈ W then (hK l p).cayleyInterp (V := E) (hL l hl p) (hρ l) else K l p

private theorem faceCutoff_of_mem {l : Λ} (hl : l ∈ W) (p : (ℝ × ℝ) × M) :
    faceCutoff hσn hK L hL ρ hρ l p = (hK l p).cayleyInterp (V := E) (hL l hl p) (hρ l) :=
  dite_eq_left hl

private theorem faceCutoff_of_notMem {l : Λ} (hl : l ∉ W) (p : (ℝ × ℝ) × M) :
    faceCutoff hσn hK L hL ρ hρ l p = K l p :=
  dite_eq_right hl

private theorem compatible_faceCutoff (l : Λ) (p : (ℝ × ℝ) × M) :
    (hσn.symplecticFormAt p.2).Compatible (faceCutoff hσn hK L hL ρ hρ l p) := by
  by_cases hl : l ∈ W
  · rw [faceCutoff_of_mem hσn hK L hL ρ hρ hl]
    exact (hK l p).compatible_cayleyInterp (V := E) (hL l hl p) (hρ l)
  · rw [faceCutoff_of_notMem hσn hK L hL ρ hρ hl]
    exact hK l p

private theorem faceCutoff_eq_background {l : Λ} (hl : ρ l = 0) (p : (ℝ × ℝ) × M) :
    faceCutoff hσn hK L hL ρ hρ l p = K l p := by
  by_cases hlW : l ∈ W
  · rw [faceCutoff_of_mem hσn hK L hL ρ hρ hlW]
    simp only [hl]
    exact (hK l p).cayleyInterp_zero (V := E) (hL l hlW p)
  · exact faceCutoff_of_notMem hσn hK L hL ρ hρ hlW p

private theorem faceCutoff_eq_local {l : Λ} (hlW : l ∈ W) (hl : ρ l = 1) (p : (ℝ × ℝ) × M) :
    faceCutoff hσn hK L hL ρ hρ l p = L l p := by
  rw [faceCutoff_of_mem hσn hK L hL ρ hρ hlW]
  simp only [hl]
  exact (hK l p).cayleyInterp_one (V := E) (hL l hlW p)

/-- Where the prescribed structure equals the background one, the cut-off family does too: the
Cayley coordinate of a structure relative to itself is zero. -/
private theorem faceCutoff_eq_of_eq {l : Λ} {p : (ℝ × ℝ) × M} (h : L l p = K l p) :
    faceCutoff hσn hK L hL ρ hρ l p = K l p := by
  by_cases hl : l ∈ W
  · rw [faceCutoff_of_mem hσn hK L hL ρ hρ hl]
    refine (hK l p).eq_of_cayley_eq
      ((hK l p).compatible_cayleyInterp (V := E) (hL l hl p) (hρ l)).tames (hK l p).tames
      (((hK l p).cayley_cayleyInterp (V := E) (hL l hl p) (hρ l)).trans ?_)
    rw [h]
    exact (congrArg (ρ l • ·) (AlmostComplexStructure.cayley_self (V := E) _)).trans
      ((smul_zero _).trans (AlmostComplexStructure.cayley_self _).symm)
  · exact faceCutoff_of_notMem hσn hK L hL ρ hρ hl p

/-- For `l ∈ W`, the cut-off family is the Cayley path expression in `K l p` and `L l p` with
weight `ρ l`. -/
private theorem faceCutoff_formula {l : Λ} (hl : l ∈ W) (p : (ℝ × ℝ) × M) :
    LinearMap.toContinuousLinearMap (faceCutoff hσn hK L hL ρ hρ l p).toLinearMap =
      cayleyPathFormula (ρ l) (LinearMap.toContinuousLinearMap (K l p).toLinearMap)
        (LinearMap.toContinuousLinearMap (L l p).toLinearMap) := by
  rw [faceCutoff_of_mem hσn hK L hL ρ hρ hl]
  exact (hK l p).toContinuousLinearMap_cayleyInterp (V := E) (hL l hl p) (hρ l)
    (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)

/-- The cut-off family is periodic in `s` when the background and the prescribed families are. -/
private theorem faceCutoff_add_fst (hKs : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hLs : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p) (l : Λ) (p : (ℝ × ℝ) × M) :
    faceCutoff hσn hK L hL ρ hρ l (p.1 + (1, 0), p.2) = faceCutoff hσn hK L hL ρ hρ l p := by
  by_cases hl : l ∈ W
  · -- Both values are the Cayley path expression in the same endpoints with the same weight.
    have h := faceCutoff_formula hσn hK L hL ρ hρ hl (p.1 + (1, 0), p.2)
    rw [hKs, hLs l hl, ← faceCutoff_formula hσn hK L hL ρ hρ hl p] at h
    exact AlmostComplexStructure.toLinearMap_injective (LinearMap.toContinuousLinearMap.injective h)
  · rw [faceCutoff_of_notMem hσn hK L hL ρ hρ hl, faceCutoff_of_notMem hσn hK L hL ρ hρ hl, hKs]

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
  refine (ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_eq_iff_semiconj _ _ _).2 fun v ↦ ?_
  have hg : ∀ w, φ.symm.mfderivToContinuousLinearEquiv (by simp) x w = mfderiv I I φ.symm x w :=
    fun w ↦ congrArg (· w) (φ.symm.mfderivToContinuousLinearEquiv_coe (x := x) (by simp))
  rw [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap', hg, hg]
  -- An almost complex structure acts on vectors through its underlying linear map.
  exact h v

/-- The cut-off family satisfies the seam identity when the background and the prescribed
families do. -/
private theorem mfderiv_symm_faceCutoff
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (l : Λ) (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    mfderiv I I φ.symm p.2 (faceCutoff hσn hK L hL ρ hρ l p v) =
      faceCutoff hσn hK L hL ρ hρ l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v) := by
  by_cases hl : l ∈ W
  · set g := φ.symm.mfderivToContinuousLinearEquiv (by simp) p.2
    have hg : ∀ v, g v = mfderiv I I φ.symm p.2 v := fun v ↦
      congrArg (· v) (φ.symm.mfderivToContinuousLinearEquiv_coe (x := p.2) (by simp))
    -- Conjugation by `dφ⁻¹` is an algebra isomorphism, so it commutes with the Cayley path
    -- expression, and it carries both endpoints at `p` to the endpoints at the seam image of `p`.
    have hconj : g.conjContinuousAlgEquiv
        (LinearMap.toContinuousLinearMap (faceCutoff hσn hK L hL ρ hρ l p).toLinearMap) =
        LinearMap.toContinuousLinearMap
          (faceCutoff hσn hK L hL ρ hρ l (p.1 + (0, 1), φ.symm p.2)).toLinearMap := by
      rw [faceCutoff_formula hσn hK L hL ρ hρ hl, faceCutoff_formula hσn hK L hL ρ hρ hl,
        map_cayleyPathFormula, conjContinuousAlgEquiv_eq_of_mfderiv_symm (hKt l p),
        conjContinuousAlgEquiv_eq_of_mfderiv_symm (hLt l hl p)]
    have h := congrArg (· (g v)) hconj
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply, LinearMap.coe_toContinuousLinearMap'] at h
    rw [hg, hg] at h
    -- An almost complex structure acts on vectors through its underlying linear map.
    exact h
  · rw [faceCutoff_of_notMem hσn hK L hL ρ hρ hl, faceCutoff_of_notMem hσn hK L hL ρ hρ hl]
    exact hKt l p v

variable {EΛ HΛ : Type*} [NormedAddCommGroup EΛ] [NormedSpace ℝ EΛ] [TopologicalSpace HΛ]
  {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ] [ChartedSpace HΛ Λ]

/-- The cut-off family is jointly smooth in the parameter and the point when the background family
is, the prescribed family is jointly smooth over `W`, and the cutoff is smooth with topological
support in `W`. -/
private theorem contMDiff_faceCutoff
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hW : IsOpen W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hsρ : ContMDiff IΛ 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ W) :
    ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (faceCutoff hσn hK L hL ρ hρ r.1 r.2).toLinearMap.toContinuousLinearMap) := by
  rintro ⟨l₀, p₀⟩
  by_cases hl₀ : l₀ ∈ W
  · have hWr : W ×ˢ (univ : Set ((ℝ × ℝ) × M)) ∈ 𝓝 (l₀, p₀) :=
      prod_mem_nhds (hW.mem_nhds hl₀) Filter.univ_mem
    have hs := ContMDiffAt.cayleyPathFormula_hom_bundle (contMDiffAt_snd.comp _ contMDiffAt_snd)
      ((hsρ l₀).comp _ contMDiffAt_fst) (hKs (l₀, p₀))
      ((hLs (l₀, p₀) ⟨hl₀, mem_univ _⟩).contMDiffAt hWr)
      (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E) (hK l₀ p₀).tames
        (hL l₀ hl₀ p₀).tames (LinearMap.coe_toContinuousLinearMap _)
        (LinearMap.coe_toContinuousLinearMap _))
      (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E) (hK l₀ p₀)
        (hL l₀ hl₀ p₀).tames
        (by simpa only [Function.comp_apply, abs_of_nonneg (hρ l₀).1] using (hρ l₀).2)
        (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _))
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [hWr] with r hr
    exact congrArg (fun B : E →L[ℝ] E ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) r.2.2 B)
      (faceCutoff_formula hσn hK L hL ρ hρ hr.1 r.2)
  · -- Near a parameter outside `W` the cutoff vanishes, so the family is the background family.
    have hz : ∀ᶠ r : Λ × ((ℝ × ℝ) × M) in 𝓝 (l₀, p₀), ρ r.1 = 0 :=
      continuous_fst.continuousAt.eventually
        (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hl₀ (hsupp h))
    refine (hKs (l₀, p₀)).congr_of_eventuallyEq ?_
    filter_upwards [hz] with r hr
    rw [faceCutoff_eq_background hσn hK L hL ρ hρ hr]

/-! ### Relative parametrized vertical families -/

include hK hL hρ in
/-- **Parametrized seam-compatible vertical families with a prescribed cutoff.** Let `K l` be a
family, over a manifold `Λ`, of `σ`-compatible vertical families on `(ℝ × ℝ) × M`, jointly smooth
in `(l, ((s, t), x))`, periodic in `s` and satisfying the seam identity, and let `L l` be a family
with these properties for the parameters `l` in an open set `W`. For a smooth cutoff
`ρ : Λ → [0, 1]` with topological support in `W`, there is a family `K' l` with these properties
for every `l`, which is `L l` where `ρ l = 1`, is `K l` where `ρ l = 0`, and agrees with `K l` at
every point where `L l` does. -/
theorem exists_verticalFamily_family_eq_of_cutoff
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hKp : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hW : IsOpen W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (L l p v) =
        L l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hsρ : ContMDiff IΛ 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ W) :
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
      (∀ l, ρ l = 1 → K' l = L l) ∧
      (∀ l, ρ l = 0 → K' l = K l) ∧
      (∀ l p, L l p = K l p → K' l p = K l p) := by
  refine ⟨faceCutoff hσn hK L hL ρ hρ,
    contMDiff_faceCutoff hσn hK L hL ρ hρ hKs hW hLs hsρ hsupp,
    faceCutoff_add_fst hσn hK L hL ρ hρ hKp hLp,
    mfderiv_symm_faceCutoff hσn hK L hL ρ hρ hKt hLt,
    compatible_faceCutoff hσn hK L hL ρ hρ, fun l hl ↦ ?_,
    fun l hl ↦ funext (faceCutoff_eq_background hσn hK L hL ρ hρ hl),
    fun l p h ↦ faceCutoff_eq_of_eq hσn hK L hL ρ hρ h⟩
  have hlW : l ∈ W := hsupp (subset_tsupport ρ (by simp [Function.mem_support, hl]))
  exact funext (faceCutoff_eq_local hσn hK L hL ρ hρ hlW hl)

omit hρ

variable [IsManifold IΛ ∞ Λ] [FiniteDimensional ℝ EΛ] [T2Space Λ] [SigmaCompactSpace Λ]

include hK hL in
/-- **Parametrized seam-compatible vertical families with values prescribed on a closed set of
parameters.** Let `K l` be a family, over a Hausdorff σ-compact finite-dimensional manifold `Λ`,
of `σ`-compatible vertical families on `(ℝ × ℝ) × M`, jointly smooth in `(l, ((s, t), x))`,
periodic in `s` and satisfying the seam identity, and let `L l` be a family with these properties
for the parameters `l` in an open set `W`. For every closed set `F ⊆ W`, for instance a union of
closed faces of `Λ`, there is a family `K' l` with these properties for every `l`, which is `L l`
for `l ∈ F`, is `K l` for `l ∉ W`, and agrees with `K l` at every point where `L l` does. -/
theorem exists_verticalFamily_family_eqOn
    (hKs : ContMDiff (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap))
    (hKp : ∀ l p, K l (p.1 + (1, 0), p.2) = K l p)
    (hKt : ∀ l (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K l p v) =
        K l (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (hW : IsOpen W) {F : Set Λ} (hF : IsClosed F) (hFW : F ⊆ W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
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
      (∀ l ∈ F, K' l = L l) ∧
      (∀ l ∉ W, K' l = K l) ∧
      (∀ l p, L l p = K l p → K' l p = K l p) := by
  have : LocallyCompactSpace HΛ := IΛ.locallyCompactSpace
  have : LocallyCompactSpace Λ := ChartedSpace.locallyCompactSpace HΛ Λ
  obtain ⟨V, hV, hFV, hVW⟩ := normal_exists_closure_subset hF hW hFW
  obtain ⟨ρ, hsρ, hrange, hsupp, hone⟩ := exists_contMDiff_support_eq_eq_one_iff IΛ hV hF hFV
  have hρ : ∀ l, ρ l ∈ Icc 0 1 := fun l ↦ hrange (mem_range_self l)
  have ht : tsupport ρ ⊆ W := by
    rw [tsupport, hsupp]
    exact hVW
  obtain ⟨K', hK's, hK'p, hK't, hK'c, hlocal, hbase, hagree⟩ :=
    exists_verticalFamily_family_eq_of_cutoff hσn hK L hL ρ hρ hKs hKp hKt hW hLs hLp hLt hsρ ht
  refine ⟨K', hK's, hK'p, hK't, hK'c, fun l hl ↦ hlocal l ((hone l).mp hl),
    fun l hl ↦ hbase l ?_, hagree⟩
  exact Function.notMem_support.mp fun h ↦ hl (ht (subset_tsupport ρ h))

/-! ### Descended families of block structures -/

omit hK

include hL in
/-- **Families of compatible block structures on a symplectic suspension with values prescribed on
a closed set of parameters.** Let `φ` preserve the nondegenerate form `σ`, and let `K₀ l` be a
smooth family of `σ`-compatible almost complex structures on `M`, over a Hausdorff σ-compact
finite-dimensional manifold `Λ`. Let `L l` be a family of vertical families on `(ℝ × ℝ) × M` given
for the parameters `l` in an open set `W`, jointly smooth there, `σ`-compatible, periodic in `s`
and satisfying the seam identity. For every closed set `F ⊆ W` there is a family `J l` of almost
complex structures on `(ℝ / ℤ) × Y_φ`, jointly smooth in `(l, y)`, such that:

* each `J l` is compatible with `Ω = ds ∧ dt + σ_v` and sends `∂_s` to the suspension vector field
  `T`;
* for `l ∈ F`, in the coordinates `(s, t, x)`, `J l` sends `a ∂_s + b ∂_t + v` to
  `-b ∂_s + a ∂_t + L_l((s, t), x) v`;
* for `l ∉ W`, `J l` is the seam structure built from `K₀ l`;
* on the collar `|t| ≤ 1/3`, wherever `L l` is `K₀ l`, `J l` sends `a ∂_s + b ∂_t + v` to
  `-b ∂_s + a ∂_t + K₀ l v`. -/
theorem exists_compatible_suspensionForm_family_eqOn [T2Space M] [LocallyCompactSpace M]
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    {K₀ : Λ → SmoothAlmostComplexStructure I M} (hK₀ : ∀ l, σ.Compatible (K₀ l))
    (hK₀s : ContMDiff (IΛ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Λ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hW : IsOpen W) {F : Set Λ} (hF : IsClosed F) (hFW : F ⊆ W)
    (hLs : ContMDiffOn (IΛ.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r : Λ × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        r.2.2 (L r.1 r.2).toLinearMap.toContinuousLinearMap) (W ×ˢ univ))
    (hLp : ∀ l ∈ W, ∀ p, L l (p.1 + (1, 0), p.2) = L l p)
    (hLt : ∀ l ∈ W, ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
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
      (∀ l ∈ F, ∀ (s t : ℝ) (x : M) (a b : ℝ) (v : TangentSpace I x),
        J l ((s : UnitAddCircle), mk φ t x)
            ((Manifold.tangentSpaceProdEquiv _).symm
              (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
          (Manifold.tangentSpaceProdEquiv _).symm
            (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
              ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, L l ((s, t), x) v)))) ∧
      (∀ l ∉ W, J l = seamAlmostComplexStructure hσ (hK₀ l)) ∧
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
    exists_verticalFamily_family_eqOn hσn (K := fun l ↦ seamFamily hσ (hK₀ l))
      (fun l ↦ compatible_seamFamily hσ (hK₀ l) hσn) L hL
      (contMDiff_seamFamily_family hσ hK₀ hK₀s) (fun l ↦ seamFamily_add_fst hσ (hK₀ l))
      (fun l ↦ mfderiv_symm_seamFamily hσ (hK₀ l)) hW hF hFW hLs hLp hLt
  refine ⟨fun l ↦ suspensionAlmostComplexStructure φ
      (hK's.comp (contMDiff_const.prodMk contMDiff_id)) (hK'p l) (hK't l),
    contMDiff_suspensionAlmostComplexStructure_family φ hK's hK'p hK't,
    fun l ↦ compatible_suspensionAlmostComplexStructure φ _ _ _ hσn (hK'c l),
    fun l ↦ suspensionAlmostComplexStructure_apply_symm_one_zero φ _ _ _,
    fun l hl s t x a b v ↦ ?_, fun l hl ↦ ?_, fun l s t x ht hLK a b v ↦ ?_⟩
  · -- `dsimp` evaluates the slice `p ↦ (l, p)` of the parametrized vertical family at `l`.
    rw [suspensionAlmostComplexStructure_mk]
    dsimp only [id]
    rw [hlocal l hl]
  · -- Off `W` the vertical family is the seam family of `K₀ l`, which descends to the seam
    -- structure.
    rw [seamAlmostComplexStructure_def]
    dsimp only
    congr 1
    exact hbase l hl
  · have hK : L l ((s, t), x) = seamFamily hσ (hK₀ l) ((s, t), x) := by
      rw [hLK, seamFamily_eq_of_mem_Icc hσ (hK₀ l) ht]
    rw [suspensionAlmostComplexStructure_mk]
    dsimp only [id]
    rw [hagree l _ hK, seamFamily_eq_of_mem_Icc hσ (hK₀ l) ht,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

end TauCeti.SmoothMappingTorus
