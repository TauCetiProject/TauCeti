/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Smooth Cayley paths of almost complex structures

Let `σ` be a smooth two-form on a finite-dimensional manifold `M`, let `J₀` be a smooth almost
complex structure compatible with `σ` and let `J₁` be a smooth almost complex structure tamed by
`σ`. At each point `x`, the Cayley chart based at the compatible structure `J₀ x` identifies the
`σ_x`-tame complex structures on `T_x M` with a balanced convex ball containing `0`, and its
`σ_x`-compatible structures with a convex subset. `TauCeti.SymplecticForm.Compatible.cayleyPath`
joins `J₀ x` to `J₁ x` by scaling the Cayley coordinate of `J₁ x` with `smoothTransition t`. This
file assembles these pointwise paths into the family of smooth almost complex structures

`J_t = TauCeti.SmoothTwoForm.Compatible.cayleyPath h₀ h₁ t`

on `M`, where `h₀ : σ.Compatible J₀` and `h₁ : σ.Tames J₁`. Each `J_t` is tamed by `σ`, and is
compatible with `σ` when `J₁` is. Further `J_t = J₀` for `t ≤ 0` and `J_t = J₁` for `t ≥ 1`, and
the family is jointly smooth on `ℝ × M` as a section of the endomorphism bundle of the tangent
bundle along `(t, x) ↦ x`. So the path is smooth across both endpoints and constant in `t`
outside `(0, 1)`. Tameness and compatibility of `J₁` are kept as distinct hypotheses.

Read with the time reversed, `(t, J) ↦ J_{1 - t}` deforms every tame structure onto `J₀` through
tame structures, keeps compatible structures compatible and fixes `J₀`. This is the bundlewise
assembly of the linear contraction `TauCeti.SymplecticForm.Compatible.cayleyContraction` of the
tame complex structures on a symplectic vector space.

Smoothness is checked in the trivializations of the tangent bundle. The value of `J_t` at `x` is
the rational expression `J₀ (1 + β C) (1 - β C)⁻¹` in `J₀ x` and `J₁ x`, where
`C = -(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` is the Cayley coordinate of `J₁ x` and `β = smoothTransition t`.
Both inverses exist because `J₀ x` is compatible and `J₁ x` is tame. Reading a fibre
endomorphism in a trivialization is conjugation by a continuous linear equivalence, an algebra
isomorphism, so it commutes with this expression; and inversion is smooth at invertible
operators. No compactness of `M` and no closedness of `σ` is used.

Such collar-constant families are the input for extending prescribed almost complex structures
across collars, for instance for building a structure on a mapping torus out of `J₀` and its
pullback by the monodromy. Since the path is a rational expression in `J₀` and `J₁`, it depends
only on the two endpoints and is natural: pulling it back along a diffeomorphism gives the path
between the pulled-back structures, for the pulled-back form.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.cayleyPath h₀ h₁ t`: the smooth almost complex structure
  that is the linear Cayley path from `J₀` to `J₁` at time `t` at every point.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cayleyPath`: at each point, `J_t`
  is the linear Cayley path from `J₀ x` to `J₁ x`.
* `TauCeti.SmoothTwoForm.Compatible.cayley_almostComplexStructureAt_cayleyPath` and
  `TauCeti.SmoothTwoForm.Compatible.eq_cayleyPath_of_cayley_eq`: the Cayley coordinate of `J_t`
  relative to `J₀` at each point, which characterizes the path.
* `TauCeti.SmoothTwoForm.Compatible.tames_cayleyPath`: every `J_t` is tamed by `σ`.
* `TauCeti.SmoothTwoForm.Compatible.compatible_cayleyPath`: for compatible `J₁`, every `J_t` is
  compatible with `σ`.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_one_le`: the path is `J₀` for `t ≤ 0` and `J₁`
  for `1 ≤ t`.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_self`: the path from `J₀` to itself is constant.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPath`: the family is jointly smooth in
  `(t, x)`.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPath_family`: for endpoints and a time
  depending smoothly on a parameter, the paths depend smoothly on the parameter and the point.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_congr`: the path depends only on its endpoints.
* `TauCeti.SmoothTwoForm.Compatible.pullback_cayleyPath`: naturality under diffeomorphisms.
* `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_of_cayley_eq_sum`: a family of tame structures
  whose Cayley coordinates relative to `J₀` are weighted sums of the Cayley coordinates of smooth
  tame families, with smooth weights, is smooth. Domain-dependent structures interpolating
  between prescribed structures, such as those on the ends of punctured Riemann surfaces, are
  built this way.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Proposition 2.5.13 and Sections 2.5 and 4.1 (the Cayley chart on tame
  and compatible complex structures, and the contractibility of the spaces of tame and of
  compatible almost complex structures on a symplectic manifold).
-/

public section

open Bundle Real
open scoped Manifold ContDiff

noncomputable section

open TauCeti in
/-- The Cayley path formula applied to two tangent endomorphism sections along a smooth base
map is smooth at a point whenever both inverse denominators are units there. Only pointwise
smoothness and invertibility are needed; no compatibility assumptions away from the point are
required. -/
theorem ContMDiffAt.cayleyPathFormula_hom_bundle
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    {f : P → M} {b : P → ℝ}
    {A B : (q : P) → TangentSpace I (f q) →L[ℝ] TangentSpace I (f q)} {q₀ : P}
    (hf : ContMDiffAt IP I ∞ f q₀) (hb : ContMDiffAt IP 𝓘(ℝ) ∞ b q₀)
    (hA : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (A q)) q₀)
    (hB : ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) (B q)) q₀)
    (hu₁ : IsUnit (1 - A q₀ * B q₀))
    (hu₂ : IsUnit (1 - b q₀ • cayleyFormula (A q₀) (B q₀))) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q)
        (cayleyPathFormula (b q) (A q) (B q))) q₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf, ?_⟩
  let e := trivializationAt E (TangentSpace I) (f q₀)
  let coord : (x : M) → (TangentSpace I x →L[ℝ] TangentSpace I x) → E →L[ℝ] E :=
    fun x C ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
      (f q₀) x (f q₀) x C
  have hconj {x : M} (hx : x ∈ e.baseSet) (C : TangentSpace I x →L[ℝ] TangentSpace I x) :
      coord x C = (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv C :=
    ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hx C
  have hx₀ : f q₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (f q₀)
  have hinner : ContMDiffAt IP 𝓘(ℝ, ℝ × (E →L[ℝ] E) × (E →L[ℝ] E)) ∞
      (fun q ↦ (b q, coord (f q) (A q), coord (f q) (B q))) q₀ :=
    hb.prodMk_space (((contMDiffAt_hom_bundle _).1 hA).2.prodMk_space
      ((contMDiffAt_hom_bundle _).1 hB).2)
  let φ := (e.continuousLinearEquivAt ℝ (f q₀) hx₀).conjContinuousAlgEquiv
  have hu₁' : IsUnit (1 - coord (f q₀) (A q₀) * coord (f q₀) (B q₀)) := by
    rw [hconj hx₀, hconj hx₀, ← map_mul, ← map_one φ, ← map_sub]
    exact hu₁.map φ
  have hu₂' : IsUnit (1 - b q₀ •
      cayleyFormula (coord (f q₀) (A q₀)) (coord (f q₀) (B q₀))) := by
    rw [hconj hx₀, hconj hx₀, ← map_cayleyFormula, ← map_smul, ← map_one φ, ← map_sub]
    exact hu₂.map φ
  refine ((contDiffAt_cayleyPathFormula hu₁' hu₂').comp_contMDiffAt
    (f := fun q ↦ (b q, coord (f q) (A q), coord (f q) (B q)))
    hinner).congr_of_eventuallyEq ?_
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx₀)] with q hq
  rw [Function.comp_apply, hconj hq, hconj hq]
  exact (hconj hq _).trans (map_cayleyPathFormula _ _ _ _)

namespace TauCeti

/-! ### The Cayley path of smooth almost complex structures -/

namespace SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ J₁ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (h₁ : σ.Tames J₁)

include h₀ in
/-- Read in the tangent trivialization at `x₀`, the Cayley denominator `1 - J₀ L` of a tame
structure `L` is invertible at `x₀`. -/
private theorem isUnit_one_sub_inCoordinates_mul {L : SmoothAlmostComplexStructure I M}
    (hL : σ.Tames L) (x₀ : M) :
    IsUnit (1 - ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x₀ x₀ x₀
        (J₀.toEndomorphism x₀) *
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x₀ x₀ x₀
        (L.toEndomorphism x₀)) := by
  let : NormedAddCommGroup (TangentSpace I x₀) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x₀) := inferInstanceAs (NormedSpace ℝ E)
  let e := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  let φ₀ := (e.continuousLinearEquivAt ℝ x₀ hx₀).conjContinuousAlgEquiv
  -- Reading in coordinates at `x₀` is conjugation by an algebra isomorphism.
  rw [ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hx₀,
    ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hx₀, ← map_mul, ← map_one φ₀,
    ← map_sub]
  exact ((h₀.compatibleAt x₀).tames.isUnit_one_sub_mul_of_toLinearMap
    (h₀.isNondegenerate.tames_iff.mp hL x₀) (J₀.almostComplexStructureAt_toLinearMap x₀).symm
    (L.almostComplexStructureAt_toLinearMap x₀).symm).map φ₀

section Family

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]

/-- For a compatible endpoint family `K₀ p`, a tame endpoint family `K₁ p`, both depending
smoothly on a parameter `p`, and a smooth time `τ p`, the Cayley path expressions in `K₀ p x`
and `K₁ p x` form a jointly smooth family of tangent endomorphisms over `P × M`. -/
private theorem contMDiff_cayleyPathFormula_family
    {K₀ K₁ : P → SmoothAlmostComplexStructure I M}
    (hc₀ : ∀ p, σ.Compatible (K₀ p)) (hc₁ : ∀ p, σ.Tames (K₁ p))
    (hs₀ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hs₁ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₁ q.1).toEndomorphism q.2)))
    {τ : P → ℝ} (hτ : ContMDiff IP 𝓘(ℝ) ∞ τ) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (cayleyPathFormula (smoothTransition (τ q.1)) ((K₀ q.1).toEndomorphism q.2)
          ((K₁ q.1).toEndomorphism q.2))) := by
  intro q₀
  have ht : (hc₀ q₀.1).isNondegenerate.symplecticFormAt q₀.2 |>.Tames
      ((K₁ q₀.1).almostComplexStructureAt q₀.2) :=
    (hc₀ q₀.1).isNondegenerate.tames_iff.mp (hc₁ q₀.1) q₀.2
  exact ContMDiffAt.cayleyPathFormula_hom_bundle contMDiffAt_snd
    (smoothTransition.contDiff.contMDiff.comp (hτ.comp contMDiff_fst)).contMDiffAt
    (hs₀ q₀) (hs₁ q₀)
    (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E)
      ((hc₀ q₀.1).compatibleAt q₀.2).tames ht
      ((K₀ q₀.1).almostComplexStructureAt_toLinearMap q₀.2).symm
      ((K₁ q₀.1).almostComplexStructureAt_toLinearMap q₀.2).symm)
    (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E)
      ((hc₀ q₀.1).compatibleAt q₀.2) ht (smoothTransition.abs_le_one _)
      ((K₀ q₀.1).almostComplexStructureAt_toLinearMap q₀.2).symm
      ((K₁ q₀.1).almostComplexStructureAt_toLinearMap q₀.2).symm)

end Family

include h₀ h₁ in
/-- The Cayley path expressions in `J₀ x` and `J₁ x` at all times and points form a jointly
smooth family of tangent endomorphisms over `ℝ × M`. -/
private theorem contMDiff_cayleyPathFormula :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) p.2
        (cayleyPathFormula (smoothTransition p.1) (J₀.toEndomorphism p.2)
          (J₁.toEndomorphism p.2))) :=
  -- This is the case of constant endpoint families, with the time as parameter.
  contMDiff_cayleyPathFormula_family (K₀ := fun _ : ℝ ↦ J₀) (K₁ := fun _ : ℝ ↦ J₁)
    (fun _ ↦ h₀) (fun _ ↦ h₁) (J₀.toEndomorphism.contMDiff.comp contMDiff_snd)
    (J₁.toEndomorphism.contMDiff.comp contMDiff_snd) contMDiff_id

/-- The pointwise linear Cayley path at `x`. It is formed on the model space `E = T_x M`, which
carries the norm required by the linear Cayley chart. -/
private def cayleyPathAt (t : ℝ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x)
    (h₀.isNondegenerate.tames_iff.mp h₁ x) t

/-- In operator-norm coordinates the pointwise path is the Cayley path expression in the fibre
values of `J₀` and `J₁`. -/
private theorem toContinuousLinearMap_cayleyPathAt (t : ℝ) (x : M) :
    LinearMap.toContinuousLinearMap (cayleyPathAt h₀ h₁ t x).toLinearMap =
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) :=
  SymplecticForm.Compatible.toContinuousLinearMap_cayleyPath (V := E) _ _ t
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    (J₁.almostComplexStructureAt_toLinearMap x).symm

/-- The Cayley path from the compatible structure `J₀` to the tame structure `J₁` at time `t`, as
a smooth almost complex structure on `M`: at each point `x` it is the tame structure whose Cayley
coordinate relative to `J₀ x` is `smoothTransition t` times that of `J₁ x`. It is `J₀` for `t ≤ 0`
and `J₁` for `1 ≤ t`. -/
def cayleyPath (t : ℝ) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨fun x ↦
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x),
    (contMDiff_cayleyPathFormula h₀ h₁).comp (contMDiff_const.prodMk contMDiff_id)⟩
  square_neg x := by
    ext v
    -- The value at `x` is the continuous version of the pointwise structure.
    change cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x)
      (cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) v) = -v
    rw [← toContinuousLinearMap_cayleyPathAt h₀ h₁]
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of `T_x M` underlying the path is the Cayley path expression in the fibre
values of `J₀` and `J₁`. -/
theorem cayleyPath_toEndomorphism (t : ℝ) (x : M) :
    (h₀.cayleyPath h₁ t).toEndomorphism x =
      cayleyPathFormula (smoothTransition t) (J₀.toEndomorphism x) (J₁.toEndomorphism x) :=
  (rfl)

/-- At each point, the path is the pointwise linear Cayley path. -/
-- This is not a `simp` lemma: its right-hand side is a structure on the model space `E`, so
-- rewriting with it turns `TangentSpace I x` terms into `E` terms that later `simp` lemmas, such
-- as `cayley_almostComplexStructureAt_cayleyPath`, no longer match.
theorem almostComplexStructureAt_cayleyPath (t : ℝ) (x : M) :
    (h₀.cayleyPath h₁ t).almostComplexStructureAt x =
      SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x)
        (h₀.isNondegenerate.tames_iff.mp h₁ x) t :=
  AlmostComplexStructure.toLinearMap_injective <| by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      cayleyPath_toEndomorphism, ← toContinuousLinearMap_cayleyPathAt h₀ h₁]
    exact LinearMap.coe_toContinuousLinearMap _

/-- At each point, applying the path to a tangent vector applies the pointwise linear Cayley
path. -/
-- This is not a `simp` lemma, for the same reason as `almostComplexStructureAt_cayleyPath`.
theorem cayleyPath_apply (t : ℝ) (x : M) (v : TangentSpace I x) :
    h₀.cayleyPath h₁ t x v =
      SymplecticForm.Compatible.cayleyPath (V := E) (h₀.compatibleAt x)
        (h₀.isNondegenerate.tames_iff.mp h₁ x) t v := by
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_cayleyPath]
  rfl

/-- At every point, the Cayley coordinate of `J_t` relative to `J₀` is the Cayley coordinate of
`J₁` scaled by `smoothTransition t`. Since tame structures are determined by their Cayley
coordinate relative to a compatible structure, this characterizes the path. -/
@[simp]
theorem cayley_almostComplexStructureAt_cayleyPath (t : ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley ((h₀.cayleyPath h₁ t).almostComplexStructureAt x) =
      smoothTransition t •
        (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_cayleyPath]
  exact SymplecticForm.Compatible.cayley_cayleyPath (V := E) _ _ t

/-- Every structure on the path is tamed by `σ`. -/
theorem tames_cayleyPath (t : ℝ) : σ.Tames (h₀.cayleyPath h₁ t) :=
  h₀.isNondegenerate.tames_iff.2 fun x ↦ by
    rw [almostComplexStructureAt_cayleyPath]
    exact SymplecticForm.Compatible.tames_cayleyPath (V := E) _ _ t

/-- A tame smooth almost complex structure with the prescribed Cayley coordinate at every point
is the path at time `t`. -/
theorem eq_cayleyPath_of_cayley_eq {t : ℝ} {J : SmoothAlmostComplexStructure I M}
    (hJ : σ.Tames J)
    (h : ∀ x, (J₀.almostComplexStructureAt x).cayley (J.almostComplexStructureAt x) =
      smoothTransition t •
        (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x)) :
    J = h₀.cayleyPath h₁ t :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x ↦
    SymplecticForm.Compatible.eq_of_cayley_eq (h₀.compatibleAt x)
      (h₀.isNondegenerate.tames_iff.mp hJ x) (h₀.isNondegenerate.tames_iff.mp
        (h₀.tames_cayleyPath h₁ t) x)
      ((h x).trans (cayley_almostComplexStructureAt_cayleyPath h₀ h₁ t x).symm)

/-- For a compatible endpoint, every structure on the path is compatible with `σ`. -/
theorem compatible_cayleyPath (h₁ : σ.Compatible J₁) (t : ℝ) :
    σ.Compatible (h₀.cayleyPath h₁.tames t) :=
  h₀.isNondegenerate.compatible_iff.2 fun x ↦ by
    rw [almostComplexStructureAt_cayleyPath]
    exact SymplecticForm.Compatible.compatible_cayleyPath (V := E) (h₀.compatibleAt x)
      (h₁.compatibleAt x) t

/-- The path agrees with `J₀` on the whole incoming collar `t ≤ 0`. -/
@[simp]
theorem cayleyPath_of_nonpos {t : ℝ} (ht : t ≤ 0) : h₀.cayleyPath h₁ t = J₀ :=
  (h₀.eq_cayleyPath_of_cayley_eq h₁ h₀.tames fun x ↦ by
    rw [smoothTransition.zero_of_nonpos ht, zero_smul, AlmostComplexStructure.cayley_self]).symm

/-- The path agrees with `J₁` on the whole outgoing collar `1 ≤ t`. -/
@[simp]
theorem cayleyPath_of_one_le {t : ℝ} (ht : 1 ≤ t) : h₀.cayleyPath h₁ t = J₁ :=
  (h₀.eq_cayleyPath_of_cayley_eq h₁ h₁ fun x ↦ by
    rw [smoothTransition.one_of_one_le ht, one_smul]).symm

/-- The Cayley path from a compatible structure to itself is constant. -/
@[simp]
theorem cayleyPath_self (t : ℝ) : h₀.cayleyPath h₀.tames t = J₀ :=
  (h₀.eq_cayleyPath_of_cayley_eq h₀.tames h₀.tames fun x ↦ by
    rw [AlmostComplexStructure.cayley_self, smul_zero]).symm

/-- The Cayley path is jointly smooth in time and space: `(t, x) ↦ J_t x` is a smooth section of
the tangent endomorphism bundle along the projection `ℝ × M → M`. -/
theorem contMDiff_cayleyPath :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((h₀.cayleyPath h₁ p.1).toEndomorphism p.2)) :=
  contMDiff_cayleyPathFormula h₀ h₁

/-- For a compatible endpoint family `K₀ p` and a tame endpoint family `K₁ p` depending smoothly
on a parameter `p` in a manifold `P`, and a smooth time `τ p`, the Cayley paths
`(p, x) ↦ cayleyPath (K₀ p) (K₁ p) (τ p) x` form a smooth section of the tangent endomorphism
bundle along the projection `P × M → M`. -/
theorem contMDiff_cayleyPath_family {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    {K₀ K₁ : P → SmoothAlmostComplexStructure I M}
    (hc₀ : ∀ p, σ.Compatible (K₀ p)) (hc₁ : ∀ p, σ.Tames (K₁ p))
    (hs₀ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₀ q.1).toEndomorphism q.2)))
    (hs₁ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((K₁ q.1).toEndomorphism q.2)))
    {τ : P → ℝ} (hτ : ContMDiff IP 𝓘(ℝ) ∞ τ) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (((hc₀ q.1).cayleyPath (hc₁ q.1) (τ q.1)).toEndomorphism q.2)) :=
  contMDiff_cayleyPathFormula_family hc₀ hc₁ hs₀ hs₁ hτ

/-- The Cayley path depends only on its endpoints, not on the form they are compatible with or
tamed by. -/
theorem cayleyPath_congr {σ' : SmoothTwoForm I M} {J₀' J₁' : SmoothAlmostComplexStructure I M}
    (h₀' : σ'.Compatible J₀') (h₁' : σ'.Tames J₁') (hJ₀ : J₀ = J₀') (hJ₁ : J₁ = J₁')
    (t : ℝ) : h₀.cayleyPath h₁ t = h₀'.cayleyPath h₁' t := by
  subst hJ₀ hJ₁
  apply SmoothAlmostComplexStructure.toEndomorphism_injective
  ext x : 1
  rw [cayleyPath_toEndomorphism, cayleyPath_toEndomorphism]

/-- Pulling the Cayley path back along a diffeomorphism gives the Cayley path between the
pulled-back structures, for the pulled-back form. -/
theorem pullback_cayleyPath {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] {σ' : SmoothTwoForm I' M'}
    {J₀' J₁' : SmoothAlmostComplexStructure I' M'} (h₀' : σ'.Compatible J₀')
    (h₁' : σ'.Tames J₁') (h : M ≃ₘ⟮I, I'⟯ M') (t : ℝ) :
    (h₀'.cayleyPath h₁' t).pullback h = (h₀'.pullback h).cayleyPath (h₁'.pullback h) t := by
  apply SmoothAlmostComplexStructure.toEndomorphism_injective
  ext x : 1
  -- Both sides are the Cayley path expression, and pulling back is a conjugation.
  rw [SmoothAlmostComplexStructure.pullback_toEndomorphism, cayleyPath_toEndomorphism,
    cayleyPath_toEndomorphism, map_cayleyPathFormula,
    SmoothAlmostComplexStructure.pullback_toEndomorphism,
    SmoothAlmostComplexStructure.pullback_toEndomorphism]

/-! ### Smoothness from weighted sums of Cayley coordinates -/

/-- A tame structure on a tangent space whose Cayley coordinate at `J₀` is a weighted sum of the
Cayley coordinates of smooth tame structures is the inverse Cayley expression of the weighted sum
of their Cayley formulas, as continuous endomorphisms. -/
private theorem toContinuousLinearMap_eq_of_cayley_eq_sum {ι : Type*} [Fintype ι] (x : M)
    {K : AlmostComplexStructure (TangentSpace I x)}
    (hK : (h₀.isNondegenerate.symplecticFormAt x).Tames K)
    {L : ι → SmoothAlmostComplexStructure I M} (hL : ∀ i, σ.Tames (L i)) {a : ι → ℝ}
    (hKL : (J₀.almostComplexStructureAt x).cayley K =
      ∑ i, a i • (J₀.almostComplexStructureAt x).cayley ((L i).almostComplexStructureAt x)) :
    LinearMap.toContinuousLinearMap K.toLinearMap =
        J₀.toEndomorphism x *
          (1 + ∑ i, a i • cayleyFormula (J₀.toEndomorphism x) ((L i).toEndomorphism x)) *
          Ring.inverse
            (1 - ∑ i, a i • cayleyFormula (J₀.toEndomorphism x) ((L i).toEndomorphism x)) ∧
      IsUnit (1 - ∑ i, a i • cayleyFormula (J₀.toEndomorphism x) ((L i).toEndomorphism x)) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  -- The weighted sum is the Cayley coordinate of `K`, read as a continuous endomorphism.
  have hCK : LinearMap.toContinuousLinearMap ((J₀.almostComplexStructureAt x).cayley K) =
      ∑ i, a i • cayleyFormula (J₀.toEndomorphism x) ((L i).toEndomorphism x) := by
    rw [hKL, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    exact congrArg (a i • ·) ((h₀.compatibleAt x).tames.toContinuousLinearMap_cayley
      (h₀.isNondegenerate.tames_iff.mp (hL i) x)
      (J₀.almostComplexStructureAt_toLinearMap x).symm
      ((L i).almostComplexStructureAt_toLinearMap x).symm)
  have hc : (LinearMap.toContinuousLinearMap
      ((J₀.almostComplexStructureAt x).cayley K)).toLinearMap ∈
      (h₀.isNondegenerate.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x) := by
    simpa only [LinearMap.coe_toContinuousLinearMap] using
      (h₀.compatibleAt x).cayley_mem_cayleyBall hK
  rw [← hCK]
  refine ⟨?_, SymplecticForm.isUnit_one_sub_of_toLinearMap_mem_cayleyBall hc⟩
  have heq : ((h₀.compatibleAt x).cayleyEquiv.symm ⟨_, hc⟩).val = K := by
    rw [(h₀.compatibleAt x).cayleyEquiv.symm_apply_eq.mpr (Subtype.ext (by simp) :
      ⟨_, hc⟩ = (h₀.compatibleAt x).cayleyEquiv ⟨K, hK⟩)]
  have hbase : LinearMap.toContinuousLinearMap (J₀.almostComplexStructureAt x).toLinearMap =
      J₀.toEndomorphism x :=
    ContinuousLinearMap.coe_injective (J₀.almostComplexStructureAt_toLinearMap x)
  have h := (h₀.compatibleAt x).cayleyEquiv_symm_apply_toContinuousLinearMap _ hc
  rw [heq] at h
  exact h.trans (congrArg (fun B : TangentSpace I x →L[ℝ] TangentSpace I x =>
    B * (1 + LinearMap.toContinuousLinearMap ((J₀.almostComplexStructureAt x).cayley K)) *
      Ring.inverse (1 - LinearMap.toContinuousLinearMap
        ((J₀.almostComplexStructureAt x).cayley K))) hbase)

/-- **Smoothness from Cayley coordinates.** Let `K y` be tame structures on the tangent spaces at
the points `b y` of a `C^n` family, for `y` in a manifold `N`. If the Cayley coordinate of each
`K y` relative to `J₀` is a weighted sum `∑ i, a i y • cayley (L i y)` of the Cayley coordinates of
smooth tame structures `L i y`, with weights and sections `y ↦ L i y (b y)` that are `C^n` at `y₀`,
then `y ↦ K y` is a `C^n` section of the tangent endomorphism bundle along `b` at `y₀`. -/
theorem contMDiffAt_of_cayley_eq_sum {ι : Type*} [Fintype ι]
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {IN : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : WithTop ℕ∞} [ENat.LEInfty n] {b : N → M}
    {K : (y : N) → AlmostComplexStructure (TangentSpace I (b y))}
    {L : ι → N → SmoothAlmostComplexStructure I M} {a : ι → N → ℝ} {y₀ : N}
    (hK : ∀ y, (h₀.isNondegenerate.symplecticFormAt (b y)).Tames (K y))
    (hL : ∀ i y, σ.Tames (L i y))
    (hKL : ∀ y, (J₀.almostComplexStructureAt (b y)).cayley (K y) =
      ∑ i, a i y • (J₀.almostComplexStructureAt (b y)).cayley
        ((L i y).almostComplexStructureAt (b y)))
    (hb : ContMDiffAt IN I n b y₀) (ha : ∀ i, ContMDiffAt IN 𝓘(ℝ) n (a i) y₀)
    (hLs : ∀ i, ContMDiffAt IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((L i y).toEndomorphism (b y))) y₀) :
    ContMDiffAt IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) (LinearMap.toContinuousLinearMap (K y).toLinearMap)) y₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hb, ?_⟩
  set x₀ := b y₀
  let e := trivializationAt E (TangentSpace I) x₀
  let coord := fun (x : M) (A : TangentSpace I x →L[ℝ] TangentSpace I x) =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x A
  -- On the base set, reading in coordinates is conjugation by an algebra isomorphism.
  have hconj {x : M} (hx : x ∈ e.baseSet) (A : TangentSpace I x →L[ℝ] TangentSpace I x) :
      coord x A = (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv A :=
    ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hx A
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  -- The base structure and the families `L i`, in coordinates.
  let A := fun y => coord (b y) (J₀.toEndomorphism (b y))
  let B := fun i y => coord (b y) ((L i y).toEndomorphism (b y))
  have hA : ContMDiffAt IN 𝓘(ℝ, E →L[ℝ] E) n A y₀ :=
    ((contMDiffAt_hom_bundle _).mp
      (((J₀.toEndomorphism.contMDiff (b y₀)).of_le ENat.LEInfty.out).comp y₀ hb)).2
  have hB (i : ι) : ContMDiffAt IN 𝓘(ℝ, E →L[ℝ] E) n (B i) y₀ :=
    ((contMDiffAt_hom_bundle _).mp (hLs i)).2
  -- In coordinates, the Cayley denominators of the `L i` are units at `y₀`.
  let φ₀ := (e.continuousLinearEquivAt ℝ x₀ hx₀).conjContinuousAlgEquiv
  have hu (i : ι) : IsUnit (1 - A y₀ * B i y₀) := isUnit_one_sub_inCoordinates_mul h₀ (hL i y₀) x₀
  let C := fun y => ∑ i, a i y • cayleyFormula (A y) (B i y)
  have hC : ContMDiffAt IN 𝓘(ℝ, E →L[ℝ] E) n C y₀ :=
    contMDiffAt_finsetSum fun i _ =>
      (ha i).smul (SymplecticForm.contMDiffAt_cayleyFormula_of_isUnit hA (hB i) (hu i))
  -- On the base set, the coordinates of the weighted sum of Cayley formulas are `C`.
  have hcoordC {y : N} (hy : b y ∈ e.baseSet) :
      coord (b y) (∑ i, a i y •
        cayleyFormula (J₀.toEndomorphism (b y)) ((L i y).toEndomorphism (b y))) = C y := by
    simp only [hconj hy, map_sum, map_smul, map_cayleyFormula, C, A, B]
  have hfib (y : N) := toContinuousLinearMap_eq_of_cayley_eq_sum h₀ (b y) (hK y)
    (fun i => hL i y) (hKL y)
  have hCu : IsUnit (1 - C y₀) := by
    rw [← hcoordC hx₀, hconj hx₀, ← map_one φ₀, ← map_sub]
    exact (hfib y₀).2.map φ₀
  refine (SymplecticForm.contMDiffAt_mul_one_add_ringInverse hA hC hCu).congr_of_eventuallyEq ?_
  filter_upwards [hb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx₀)] with y hy
  -- The hom-bundle smoothness criterion reads the fiber value in the fixed trivialization.
  change coord (b y) _ = _
  rw [(hfib y).1, hconj hy, map_mul, map_mul, map_add, map_one, map_ringInverse, map_sub,
    map_one, ← hconj hy, ← hconj hy, hcoordC hy]

end SmoothTwoForm.Compatible

end TauCeti
