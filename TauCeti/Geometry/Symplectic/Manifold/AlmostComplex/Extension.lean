/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath
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

The cutoff is built for families of structures along a smooth map `f : P → M`: a background
family `K₀ q` and a prescribed family `K q` of `σ`-compatible structures on `T_(f q) M`, the
latter only on an open set `W ⊆ P`, are combined with a weight `ρ q ∈ [0, 1]` into
`TauCeti.SmoothTwoForm.IsNondegenerate.cayleyCutoff`, whose Cayley coordinate relative to `K₀ q`
is `ρ q` times that of `K q`. Taking `f = id` gives structures on `M` itself; families over
other parameter spaces, such as the vertical families over `(ℝ × ℝ) × M` that descend to a
mapping torus, are cut off in the same way. The cutoff is a rational expression in `K₀ q` and
`K q`, so it commutes with every linear isomorphism of tangent spaces intertwining the two
families (`TauCeti.SmoothTwoForm.IsNondegenerate.apply_cayleyCutoff_apply`). This is what makes
it preserve invariance under deck transformations.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.cayleyCutoff`: the Cayley cutoff of a family of compatible
  structures along a map against a background family.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.compatible_cayleyCutoff`: the cutoff is compatible.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cayleyCutoff_of_eq_one`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.cayleyCutoff_of_eq_zero`: it is the prescribed family
  where the weight is one and the background where the weight is zero.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_cayleyCutoff`: it is smooth when the weight is
  smooth with topological support in the region where the prescribed family is smooth.
* `TauCeti.SmoothTwoForm.IsNondegenerate.apply_cayleyCutoff_apply`: it commutes with linear
  isomorphisms intertwining the background and prescribed families.
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

/-! ### The Cayley cutoff of a family along a map -/

namespace SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {P : Type*}
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : P → M}
  {K₀ K : ∀ q : P, AlmostComplexStructure (TangentSpace I (f q))}
  (hK₀ : ∀ q, (hσ.symplecticFormAt (f q)).Compatible (K₀ q)) {W : Set P}
  (hK : ∀ q ∈ W, (hσ.symplecticFormAt (f q)).Compatible (K q))
  {ρ : P → ℝ} (hρ : ∀ q, ρ q ∈ Icc 0 1)

open Classical in
/-- The Cayley cutoff of a family `K` of `σ`-compatible structures along `f : P → M`, prescribed on
`W ⊆ P`, against a background family `K₀` with weight `ρ`. On `W` its Cayley coordinate relative to
`K₀ q` is `ρ q` times the Cayley coordinate of `K q`; off `W` it is `K₀ q`. -/
def cayleyCutoff (q : P) : AlmostComplexStructure (TangentSpace I (f q)) :=
  if hq : q ∈ W then (hK₀ q).cayleyInterp (V := E) (hK q hq) (hρ q) else K₀ q

/-- On the prescribed region the cutoff is the Cayley interpolation with weight `ρ q`. -/
theorem cayleyCutoff_of_mem {q : P} (hq : q ∈ W) :
    hσ.cayleyCutoff hK₀ hK hρ q = (hK₀ q).cayleyInterp (V := E) (hK q hq) (hρ q) :=
  dite_eq_left hq

/-- Off the prescribed region the cutoff is the background family. -/
theorem cayleyCutoff_of_notMem {q : P} (hq : q ∉ W) : hσ.cayleyCutoff hK₀ hK hρ q = K₀ q :=
  dite_eq_right hq

/-- Every member of the cutoff family is compatible with `σ`. -/
theorem compatible_cayleyCutoff (q : P) :
    (hσ.symplecticFormAt (f q)).Compatible (hσ.cayleyCutoff hK₀ hK hρ q) := by
  by_cases hq : q ∈ W
  · rw [cayleyCutoff_of_mem hσ hK₀ hK hρ hq]
    exact (hK₀ q).compatible_cayleyInterp (V := E) (hK q hq) (hρ q)
  · rw [cayleyCutoff_of_notMem hσ hK₀ hK hρ hq]
    exact hK₀ q

/-- Where the weight vanishes the cutoff is the background family. -/
theorem cayleyCutoff_of_eq_zero {q : P} (hq : ρ q = 0) : hσ.cayleyCutoff hK₀ hK hρ q = K₀ q := by
  by_cases hqW : q ∈ W
  · rw [cayleyCutoff_of_mem hσ hK₀ hK hρ hqW]
    have h0 {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hb0 : b = 0) :
        (hK₀ q).cayleyInterp (V := E) (hK q hqW) hb = K₀ q := by
      subst hb0
      exact (hK₀ q).cayleyInterp_zero (V := E) (hK q hqW)
    exact h0 (hρ q) hq
  · exact cayleyCutoff_of_notMem hσ hK₀ hK hρ hqW

/-- On the prescribed region, where the weight is one the cutoff is the prescribed family. -/
theorem cayleyCutoff_of_eq_one {q : P} (hqW : q ∈ W) (hq : ρ q = 1) :
    hσ.cayleyCutoff hK₀ hK hρ q = K q := by
  rw [cayleyCutoff_of_mem hσ hK₀ hK hρ hqW]
  have h1 {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hb1 : b = 1) :
      (hK₀ q).cayleyInterp (V := E) (hK q hqW) hb = K q := by
    subst hb1
    exact (hK₀ q).cayleyInterp_one (V := E) (hK q hqW)
  exact h1 (hρ q) hq

/-- On the prescribed region the cutoff is the rational expression `cayleyPathFormula` in the two
families, as continuous endomorphisms. -/
theorem toContinuousLinearMap_cayleyCutoff {q : P} (hq : q ∈ W) :
    LinearMap.toContinuousLinearMap (hσ.cayleyCutoff hK₀ hK hρ q).toLinearMap =
      cayleyPathFormula (ρ q) (LinearMap.toContinuousLinearMap (K₀ q).toLinearMap)
        (LinearMap.toContinuousLinearMap (K q).toLinearMap) := by
  rw [cayleyCutoff_of_mem hσ hK₀ hK hρ hq]
  exact (hK₀ q).toContinuousLinearMap_cayleyInterp (V := E) (hK q hq) (hρ q)
    (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)

/-- The cutoff commutes with every linear isomorphism `L : T_(f q) M → T_(f q') M` intertwining the
background families and, on the prescribed region, the prescribed families, between two parameters
with the same weight and both or neither in the prescribed region. -/
theorem apply_cayleyCutoff_apply {q q' : P}
    (L : TangentSpace I (f q) ≃L[ℝ] TangentSpace I (f q'))
    (h₀ : ∀ v, L (K₀ q v) = K₀ q' (L v)) (h : q ∈ W → ∀ v, L (K q v) = K q' (L v))
    (hW : q' ∈ W ↔ q ∈ W) (hρq : ρ q' = ρ q) (v : TangentSpace I (f q)) :
    L (hσ.cayleyCutoff hK₀ hK hρ q v) = hσ.cayleyCutoff hK₀ hK hρ q' (L v) := by
  by_cases hq : q ∈ W
  · -- Conjugation by `L` is an algebra isomorphism, so it commutes with the rational expression.
    have hconj (J : AlmostComplexStructure (TangentSpace I (f q)))
        (J' : AlmostComplexStructure (TangentSpace I (f q'))) (hJ : ∀ v, L (J v) = J' (L v)) :
        LinearMap.toContinuousLinearMap J'.toLinearMap =
          L.conjContinuousAlgEquiv (LinearMap.toContinuousLinearMap J.toLinearMap) := by
      ext w
      simp [hJ]
    have key : LinearMap.toContinuousLinearMap (hσ.cayleyCutoff hK₀ hK hρ q').toLinearMap =
        L.conjContinuousAlgEquiv
          (LinearMap.toContinuousLinearMap (hσ.cayleyCutoff hK₀ hK hρ q).toLinearMap) := by
      rw [toContinuousLinearMap_cayleyCutoff hσ hK₀ hK hρ (hW.2 hq), hρq, hconj _ _ h₀,
        hconj _ _ (h hq), ← map_cayleyPathFormula,
        toContinuousLinearMap_cayleyCutoff hσ hK₀ hK hρ hq]
    simpa using (DFunLike.congr_fun key (L v)).symm
  · rw [cayleyCutoff_of_notMem hσ hK₀ hK hρ hq,
      cayleyCutoff_of_notMem hσ hK₀ hK hρ (mt hW.1 hq), h₀]

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]

/-- The cutoff is smooth near each point of the prescribed region where the background family and
the prescribed family are smooth. -/
private theorem contMDiffAt_cayleyCutoff_of_mem (hf : ContMDiff IP I ∞ f) (hW : IsOpen W)
    (hK₀s : ContMDiff IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f q) (LinearMap.toContinuousLinearMap (K₀ q).toLinearMap)))
    (hKs : ContMDiffOn IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f q) (LinearMap.toContinuousLinearMap (K q).toLinearMap)) W)
    (hρs : ContMDiff IP 𝓘(ℝ) ∞ ρ) {q₀ : P} (hq₀ : q₀ ∈ W) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f q) (LinearMap.toContinuousLinearMap (hσ.cayleyCutoff hK₀ hK hρ q).toLinearMap)) q₀ := by
  have hs := ContMDiffAt.cayleyPathFormula_hom_bundle (hf q₀) (hρs q₀) (hK₀s q₀)
    ((hKs q₀ hq₀).contMDiffAt (hW.mem_nhds hq₀))
    (SymplecticForm.Tames.isUnit_one_sub_mul_of_toLinearMap (V := E) (hK₀ q₀).tames
      (hK q₀ hq₀).tames (LinearMap.coe_toContinuousLinearMap _)
      (LinearMap.coe_toContinuousLinearMap _))
    (SymplecticForm.Compatible.isUnit_one_sub_smul_cayleyFormula (V := E) (hK₀ q₀)
      (hK q₀ hq₀).tames (by simpa only [abs_of_nonneg (hρ q₀).1] using (hρ q₀).2)
      (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _))
  refine hs.congr_of_eventuallyEq ?_
  filter_upwards [hW.mem_nhds hq₀] with q hq
  exact congrArg (fun L : E →L[ℝ] E ↦ TotalSpace.mk'
    (E →L[ℝ] E) (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (f q) L)
    (toContinuousLinearMap_cayleyCutoff hσ hK₀ hK hρ hq)

/-- The cutoff family is smooth, as a section of the tangent endomorphism bundle along `f`, when
`f`, the background family and the weight are smooth, the prescribed family is smooth on the open
prescribed region, and the weight has topological support in that region. -/
theorem contMDiff_cayleyCutoff (hf : ContMDiff IP I ∞ f) (hW : IsOpen W)
    (hK₀s : ContMDiff IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f q) (LinearMap.toContinuousLinearMap (K₀ q).toLinearMap)))
    (hKs : ContMDiffOn IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f q) (LinearMap.toContinuousLinearMap (K q).toLinearMap)) W)
    (hρs : ContMDiff IP 𝓘(ℝ) ∞ ρ) (hsupp : tsupport ρ ⊆ W) :
    ContMDiff IP (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (f q) (LinearMap.toContinuousLinearMap (hσ.cayleyCutoff hK₀ hK hρ q).toLinearMap)) := by
  intro q₀
  by_cases hq₀ : q₀ ∈ W
  · exact contMDiffAt_cayleyCutoff_of_mem hσ hK₀ hK hρ hf hW hK₀s hKs hρs hq₀
  · -- Away from the prescribed region the weight vanishes nearby, so the cutoff is the background.
    have hz : ∀ᶠ q in 𝓝 q₀, ρ q = 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hq₀ (hsupp h))
    refine (hK₀s q₀).congr_of_eventuallyEq ?_
    filter_upwards [hz] with q hq
    rw [cayleyCutoff_of_eq_zero hσ hK₀ hK hρ hq]

end SmoothTwoForm.IsNondegenerate

/-! ### Extending compatible structures on a manifold -/

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
  -- The cutoff of `K` against `J₀` along the identity of `M`.
  have hσ := h₀.isNondegenerate
  have hJ₀ : ∀ x : M, (hσ.symplecticFormAt (id x)).Compatible (J₀.almostComplexStructureAt x) :=
    h₀.compatibleAt
  have hK₀s : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        (id x) (LinearMap.toContinuousLinearMap (J₀.almostComplexStructureAt x).toLinearMap)) :=
    -- The fibrewise structure of `J₀` is its bundled endomorphism section.
    J₀.toEndomorphism.contMDiff.congr fun x ↦ congrArg (TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x)
      ((LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2
        (J₀.almostComplexStructureAt_toLinearMap x))
  let C := hσ.cayleyCutoff (f := id) hJ₀ hK hρ
  have hC := hσ.contMDiff_cayleyCutoff hJ₀ hK hρ contMDiff_id hU hK₀s hs hsρ hsupp
  let J : SmoothAlmostComplexStructure I M :=
    { toEndomorphism := ⟨fun x ↦ LinearMap.toContinuousLinearMap (C x).toLinearMap, hC⟩
      square_neg := fun x ↦ by
        ext v
        exact (C x).apply_apply v }
  have hJ (x : M) : J.almostComplexStructureAt x = C x := by
    apply AlmostComplexStructure.toLinearMap_injective
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    exact LinearMap.coe_toContinuousLinearMap _
  refine ⟨J, hσ.compatible_iff.mpr (fun x ↦ ?_), fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hJ]
    exact hσ.compatible_cayleyCutoff hJ₀ hK hρ x
  · have hxU : x ∈ U := hsupp (subset_tsupport ρ (by simp [Function.mem_support, hx]))
    rw [hJ]
    exact hσ.cayleyCutoff_of_eq_one hJ₀ hK hρ hxU hx
  · rw [hJ]
    exact hσ.cayleyCutoff_of_eq_zero hJ₀ hK hρ hx

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
