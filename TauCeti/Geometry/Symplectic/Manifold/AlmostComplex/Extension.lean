/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Extending compatible almost complex structures from a closed region

A compatible almost complex structure prescribed smoothly on an open neighbourhood of a
closed set extends to the whole manifold, agreeing with a chosen background structure outside
that neighbourhood. The local field is a total function, but its regularity and compatibility
are required only on the given open set; its values elsewhere have no effect.

The construction cuts off the local field in the Cayley chart of the background structure,
not by averaging almost complex structures. The convexity of the compatible Cayley ball
preserves compatibility. A cutoff whose topological support lies in the open set makes the
result smooth even where the prescribed field is not defined smoothly.
The coordinate smoothness argument uses the pointwise tangent-bundle Cayley formula lemma in
`TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath`, requiring regularity only
on the open region where the local field is used.

The cut-off itself is stated for families along an arbitrary map `f : P → M`, so that it also
serves parametrized families and families on covering spaces.

## Main results

* `TauCeti.cayleyCutoff`: the cut-off of a family `L` against a background family `K` along a
  map `f : P → M`, with `TauCeti.contMDiff_cayleyCutoff` for its smoothness.
* `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eq_of_cutoff`: extend using a specified
  smooth cutoff with topological support in the prescribed open set.
* `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`: extend from an arbitrary closed
  set in a Hausdorff sigma-compact manifold, constructing the cutoff automatically.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Sections 2.5 and 4.1 (compatible Cayley charts and relative extension).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Cutting off a family against a background in the Cayley chart -/

section CayleyCutoff

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : P → M}
  {K : ∀ p, AlmostComplexStructure (TangentSpace I (f p))}
  (hK : ∀ p, (hσ.symplecticFormAt (f p)).Compatible (K p)) {U : Set P}
  (L : ∀ p, AlmostComplexStructure (TangentSpace I (f p)))
  (hL : ∀ p ∈ U, (hσ.symplecticFormAt (f p)).Compatible (L p))
  (ρ : P → ℝ) (hρ : ∀ p, ρ p ∈ Icc 0 1)

open Classical in
/-- Given families `K` and `L` of structures on the tangent spaces `T_(f p) M` along a map
`f : P → M`, with `K p` compatible everywhere and `L p` compatible on `U`, the family that at
`p ∈ U` moves from `K p` towards `L p` with weight `ρ p` in the Cayley chart of `K p`, and equals
`K p` off `U`. -/
def cayleyCutoff (p : P) : AlmostComplexStructure (TangentSpace I (f p)) :=
  if hp : p ∈ U then (hK p).cayleyInterp (V := E) (hL p hp) (hρ p) else K p

/-- On `U`, the cut-off family is the Cayley interpolation from `K p` towards `L p`. -/
theorem cayleyCutoff_of_mem {p : P} (hp : p ∈ U) :
    cayleyCutoff hK L hL ρ hρ p = (hK p).cayleyInterp (V := E) (hL p hp) (hρ p) :=
  dite_eq_left hp

/-- Off `U`, the cut-off family is the background family. -/
theorem cayleyCutoff_of_notMem {p : P} (hp : p ∉ U) : cayleyCutoff hK L hL ρ hρ p = K p :=
  dite_eq_right hp

/-- The cut-off family is compatible: the compatible Cayley ball is convex. -/
theorem compatible_cayleyCutoff (p : P) :
    (hσ.symplecticFormAt (f p)).Compatible (cayleyCutoff hK L hL ρ hρ p) := by
  by_cases hp : p ∈ U
  · rw [cayleyCutoff_of_mem hK L hL ρ hρ hp]
    exact (hK p).compatible_cayleyInterp (V := E) (hL p hp) (hρ p)
  · rw [cayleyCutoff_of_notMem hK L hL ρ hρ hp]
    exact hK p

/-- Where the weight vanishes, the cut-off family is the background family. -/
theorem cayleyCutoff_of_eq_zero {p : P} (hp : ρ p = 0) : cayleyCutoff hK L hL ρ hρ p = K p := by
  by_cases hpU : p ∈ U
  · rw [cayleyCutoff_of_mem hK L hL ρ hρ hpU]
    simp only [hp]
    exact (hK p).cayleyInterp_zero (V := E) (hL p hpU)
  · exact cayleyCutoff_of_notMem hK L hL ρ hρ hpU

/-- Where the weight is one on `U`, the cut-off family is the prescribed family. -/
theorem cayleyCutoff_of_eq_one {p : P} (hpU : p ∈ U) (hp : ρ p = 1) :
    cayleyCutoff hK L hL ρ hρ p = L p := by
  rw [cayleyCutoff_of_mem hK L hL ρ hρ hpU]
  simp only [hp]
  exact (hK p).cayleyInterp_one (V := E) (hL p hpU)

/-- Where the prescribed structure equals the background one, the cut-off family does too: the
Cayley coordinate of a structure relative to itself is zero. -/
theorem cayleyCutoff_of_eq {p : P} (h : L p = K p) : cayleyCutoff hK L hL ρ hρ p = K p := by
  by_cases hp : p ∈ U
  · rw [cayleyCutoff_of_mem hK L hL ρ hρ hp]
    refine (hK p).eq_of_cayley_eq
      ((hK p).compatible_cayleyInterp (V := E) (hL p hp) _).tames (hK p).tames
      (((hK p).cayley_cayleyInterp (V := E) (hL p hp) _).trans ?_)
    rw [h]
    exact (congrArg (ρ p • ·) (AlmostComplexStructure.cayley_self (V := E) _)).trans
      ((smul_zero _).trans (AlmostComplexStructure.cayley_self _).symm)
  · exact cayleyCutoff_of_notMem hK L hL ρ hρ hp

/-- On `U`, the cut-off family is the Cayley path expression in `K p` and `L p` with weight
`ρ p`. -/
theorem toContinuousLinearMap_cayleyCutoff {p : P} (hp : p ∈ U) :
    LinearMap.toContinuousLinearMap (cayleyCutoff hK L hL ρ hρ p).toLinearMap =
      cayleyPathFormula (ρ p) (LinearMap.toContinuousLinearMap (K p).toLinearMap)
        (LinearMap.toContinuousLinearMap (L p).toLinearMap) := by
  rw [cayleyCutoff_of_mem hK L hL ρ hρ hp]
  exact (hK p).toContinuousLinearMap_cayleyInterp (V := E) (hL p hp) (hρ p)
    (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)

/-- The cut-off family is smooth along a smooth map `f` when the background family is, the
prescribed family is smooth on the open set `U`, and the weight is smooth with topological
support in `U`. -/
theorem contMDiff_cayleyCutoff {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P]
    [ChartedSpace HP P] (hf : ContMDiff IP I ∞ f)
    (hKs : ContMDiff IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f p) (LinearMap.toContinuousLinearMap (K p).toLinearMap)))
    (hU : IsOpen U)
    (hLs : ContMDiffOn IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f p) (LinearMap.toContinuousLinearMap (L p).toLinearMap)) U)
    (hsρ : ContMDiff IP 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ContMDiff IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f p) (LinearMap.toContinuousLinearMap (cayleyCutoff hK L hL ρ hρ p).toLinearMap)) := by
  intro p₀
  by_cases hp₀ : p₀ ∈ U
  · have hs := ContMDiffAt.cayleyPathFormula_hom_bundle (hf p₀) (hsρ p₀) (hKs p₀)
      ((hLs p₀ hp₀).contMDiffAt (hU.mem_nhds hp₀))
      (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E) (hK p₀).tames
        (hL p₀ hp₀).tames (LinearMap.coe_toContinuousLinearMap _)
        (LinearMap.coe_toContinuousLinearMap _))
      (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E) (hK p₀)
        (hL p₀ hp₀).tames (by simpa only [abs_of_nonneg (hρ p₀).1] using (hρ p₀).2)
        (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _))
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hp₀] with p hp
    exact congrArg (fun B : E →L[ℝ] E ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f p) B)
      (toContinuousLinearMap_cayleyCutoff hK L hL ρ hρ hp)
  · -- Near a point outside `U` the weight vanishes, so the family is the background family.
    have hz : ∀ᶠ p in 𝓝 p₀, ρ p = 0 :=
      notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hp₀ (hsupp h)
    refine (hKs p₀).congr_of_eventuallyEq ?_
    filter_upwards [hz] with p hp
    rw [cayleyCutoff_of_eq_zero hK L hL ρ hρ hp]

end CayleyCutoff

/-! ### Extension from a closed region -/

namespace SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) {U : Set M} (K : M → AlmostComplexStructure E)
  (hK : ∀ x ∈ U, (h₀.isNondegenerate.symplecticFormAt x).Compatible (K x))
  (ρ : M → ℝ) (hρ : ∀ x, ρ x ∈ Icc 0 1)

include h₀ hK hρ in
/-- A smooth cutoff supported inside the region where a local field is smooth and compatible
extends it to a global compatible structure. Where the cutoff is one the local field is
unchanged; where it is zero the background structure is unchanged. -/
theorem exists_compatible_eq_of_cutoff (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U)
    (hsρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ U) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      (∀ x, ρ x = 1 → J.almostComplexStructureAt x = K x) ∧
      (∀ x, ρ x = 0 → J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) := by
  -- The background family is `J₀`, read along the identity map of `M`.
  have hJ₀ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (id x) (LinearMap.toContinuousLinearMap (J₀.almostComplexStructureAt x).toLinearMap)) :=
    J₀.toEndomorphism.contMDiff.congr fun x ↦ by
      rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
      -- Converting a continuous linear map to a linear map and back is definitionally the
      -- original map; here it is read on `TangentSpace I x = E`.
      rfl
  let J₁ := cayleyCutoff (f := id) h₀.compatibleAt K hK ρ hρ
  let J : SmoothAlmostComplexStructure I M :=
    { toEndomorphism := ⟨fun x ↦ LinearMap.toContinuousLinearMap (J₁ x).toLinearMap,
        contMDiff_cayleyCutoff h₀.compatibleAt K hK ρ hρ contMDiff_id hJ₀ hU hs hsρ hsupp⟩
      square_neg := fun x ↦ by
        ext v
        exact (J₁ x).apply_apply v }
  have hJ (x : M) : J.almostComplexStructureAt x = J₁ x := by
    apply AlmostComplexStructure.toLinearMap_injective
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    exact LinearMap.coe_toContinuousLinearMap _
  refine ⟨J, h₀.isNondegenerate.compatible_iff.mpr (fun x ↦ ?_), ?_, ?_⟩
  · rw [hJ]
    exact compatible_cayleyCutoff h₀.compatibleAt K hK ρ hρ x
  · intro x hx
    have hxU : x ∈ U := hsupp (subset_tsupport ρ (by simp [Function.mem_support, hx]))
    rw [hJ]
    exact cayleyCutoff_of_eq_one h₀.compatibleAt K hK ρ hρ hxU hx
  · intro x hx
    rw [hJ]
    exact cayleyCutoff_of_eq_zero h₀.compatibleAt K hK ρ hρ hx

include h₀ hK in
/-- Extend a compatible field prescribed smoothly near a closed set, retaining a chosen
background compatible structure outside that neighbourhood. No closedness of the two-form or
compactness of the prescribed set is required. The local field is tested for smoothness as a
section of the tangent endomorphism bundle, not in a global trivialization. -/
theorem exists_compatible_eqOn [T2Space M] [SigmaCompactSpace M]
    (hU : IsOpen U) {A : Set M} (hA : IsClosed A) (hAU : A ⊆ U)
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (LinearMap.toContinuousLinearMap (K x).toLinearMap)) U) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      (∀ x ∈ A, J.almostComplexStructureAt x = K x) ∧
      (∀ x ∉ U, J.almostComplexStructureAt x = J₀.almostComplexStructureAt x) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨ρ, hsρ, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff I hV hA hAV
  have hρ : ∀ x, ρ x ∈ Icc 0 1 := fun x ↦ hrange (mem_range_self x)
  have ht : tsupport ρ ⊆ U := by
    rw [tsupport, hsupp]
    exact hVU
  obtain ⟨J, hJ, hlocal, hbase⟩ := h₀.exists_compatible_eq_of_cutoff K hK ρ hρ hU hs hsρ ht
  refine ⟨J, hJ, fun x hx ↦ hlocal x ((hone x).mp hx), fun x hx ↦ hbase x ?_⟩
  exact Function.notMem_support.mp (fun h ↦ hx (ht (subset_tsupport ρ h)))

end SmoothTwoForm.Compatible
end TauCeti
