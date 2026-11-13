/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Chart
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Locality
import TauCeti.Topology.ContinuousOn.NhdsWithin

/-!
# Weak pseudoholomorphic maps from a Riemann surface

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, with its almost complex structure
`j = TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ X`. Let `M` be a manifold modelled
on a boundaryless model `I` with model vector space `E`, `J` a domain-dependent almost complex
structure on `M` of class `C^ℓ` and `ν` an inhomogeneous term for `(j, J)`. A map `u : X → M` is
*weakly pseudoholomorphic* on `s ⊆ X` for `(J, ν)` and an exponent `p`
(`TauCeti.IsWeakPseudoholomorphicOn J ν p u s`) when it lies in the local Sobolev class
`W^{1,p}_loc` on `s` and the equation `du + J(z, u) ∘ du ∘ j = 2ν(z, u)` holds almost everywhere
in every pair of charts. In a holomorphic chart `φ` of `X` and a chart `ψ` of `M`, read in `E` as
`ψ̂ = ψ.extendTrans I (Homeomorph.refl E)` (whose coordinates are `ψ.extend I`), the equation is
read on the coordinate vector `∂ₛ` as the planar weak equation `TauCeti.IsWeakCauchyRiemannOn`
for `ψ̂ ∘ u ∘ φ⁻¹`, with the structure `J_φψ(z, v) = dψ̂ ∘ J(φ⁻¹ z, ψ̂⁻¹ v) ∘ dψ̂⁻¹`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.chartField`) and the term
`η_φψ(z, v) = 2 dψ̂ (ν(φ⁻¹ z, ψ̂⁻¹ v)(dφ⁻¹ 1))` (`TauCeti.InhomogeneousTerm.chartTerm`). Testing
on `∂ₛ` alone suffices: the value of the equation on `∂ₜ = j ∂ₛ` is `-J(z, u)` applied to its
value on `∂ₛ`, since `ν` is complex antilinear. Allowing any boundaryless model on `M` covers
product targets such as `X × M`, on which graphs of solutions live.

## Main results

* `TauCeti.IsWeakPseudoholomorphicOn`, `TauCeti.IsWeakPseudoholomorphic`: the predicate on a set
  and on the whole surface, with their unfolding, reading-off and monotonicity lemmas and
  `TauCeti.isWeakPseudoholomorphicOn_univ`.
* `TauCeti.isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn`,
  `TauCeti.isWeakPseudoholomorphic_iff_continuous_isWeakCauchyRiemannOn`: continuity together with
  the coordinate equations already gives the Sobolev class.
* `TauCeti.isWeakPseudoholomorphicOn_ofLE`, `TauCeti.isWeakPseudoholomorphic_ofLE`: the predicate
  does not change when `J` and `ν` are regarded as being of lower regularity.
* `TauCeti.isWeakPseudoholomorphicOn_iff_locally`, `TauCeti.isWeakPseudoholomorphic_iff_locally`,
  `TauCeti.isWeakPseudoholomorphicOn_iSup_iff`: it is a sheaf condition on `X`.
* `TauCeti.isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn`,
  `TauCeti.isWeakPseudoholomorphic_iff_isPseudoholomorphic`: **Comparison.** For `ν = 0`, `J`
  independent of the domain point and smooth, and `u` of class `C¹` on an open set, the predicate
  is Tau Ceti's `IsPseudoholomorphicOn` for `j` and `J`. In particular holomorphic maps into a
  complex manifold solve the equation for its structure
  (`MDifferentiableOn.isWeakPseudoholomorphicOn`, `MDifferentiable.isWeakPseudoholomorphic`),
  and so does the identity of `X` (`TauCeti.isWeakPseudoholomorphicOn_id`,
  `TauCeti.isWeakPseudoholomorphic_id`).
* `TauCeti.isWeakPseudoholomorphicOn_const`, `TauCeti.isWeakPseudoholomorphic_const`: constant
  maps solve the homogeneous equation for every `J`.
* Check on `X = M = ℂ`: conjugation does not solve the equation for the structure `i`
  (`TauCeti.not_isWeakPseudoholomorphicOn_conj`).
* Check on `X = ℂ`, for any `M`: a constant map with value `u₀` solves the inhomogeneous equation
  on an open set exactly when `ν(z, u₀)` vanishes on `∂ₛ` for almost every `z`
  (`TauCeti.isWeakPseudoholomorphicOn_const_iff_complex`).

## Implementation notes

As for `TauCeti.MemWkpLocMapOn`, the charts tested are those of the maximal atlases, so the
predicate does not depend on chosen atlases, and it is intended for open sets `s`. The class is
meant for `p > 2`, where Sobolev maps are continuous; the definition is stated for every `p`.
No dimension hypothesis on `E` is needed; the theorems assume it complete, as weak derivatives
require.
That the equation in one atlas of each implies it in all charts, its invariance under
biholomorphisms of `X` and diffeomorphisms of `M`, and boundary conditions are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.1, 3.1 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology ComplexConjugate TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

/-! ### The predicate -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}

variable (J) in
/-- **Weak pseudoholomorphic maps.** For a domain-dependent almost complex structure `J` on `M`,
an inhomogeneous term `ν` for `J` and the structure `j` of the Riemann surface `X`, and an exponent
`p`, a map `u : X → M` is weakly pseudoholomorphic on `s` when it is in `W^{1,p}_loc` on `s` and,
for every holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`, read in the model vector
space as `ψ̂ = ψ.extendTrans I (Homeomorph.refl E)`, the coordinate expression `ψ̂ ∘ u ∘ φ⁻¹` is
a weak solution of `∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)` on the part of the target of `φ` over `s`
where `u` maps into the source of `ψ`. Here `J_φψ` is
`ContMDiffAlmostComplexStructureFamily.chartField` and `η_φψ` is `InhomogeneousTerm.chartTerm`
for `φ` and `ψ̂`: the equation `du + J(z, u) ∘ du ∘ j = 2ν(z, u)` evaluated on `∂ₛ`. The
definition is intended for open `s` and `p > 2`. -/
def IsWeakPseudoholomorphicOn
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (p : ENNReal) (u : X → M) (s : Set X) : Prop :=
  MemWkpLocMapOn I p 1 u s ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm)

variable (J) in
/-- **Weak pseudoholomorphic maps on the whole surface.** A map `u : X → M` is weakly
pseudoholomorphic for `J`, `ν` and `p` when it is in `W^{1,p}_loc` and, for every holomorphic
chart `φ` of `X` and every smooth chart `ψ` of `M` read in the model vector space as
`ψ̂ = ψ.extendTrans I (Homeomorph.refl E)`, the coordinate expression `ψ̂ ∘ u ∘ φ⁻¹` is a weak
solution of the coordinate equation `∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)` on the part of the
target of `φ` where `u` maps into the source of `ψ`. -/
def IsWeakPseudoholomorphic
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (p : ENNReal) (u : X → M) : Prop :=
  MemWkpLocMap I p 1 u ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm)

variable
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p q : ENNReal} {u : X → M} {s t : Set X}

/-- Unfolding the definition of weak pseudoholomorphic maps on a set. -/
theorem isWeakPseudoholomorphicOn_iff : IsWeakPseudoholomorphicOn J ν p u s ↔
    MemWkpLocMapOn I p 1 u s ∧
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  Iff.rfl

/-- Unfolding the definition of weak pseudoholomorphic maps. -/
theorem isWeakPseudoholomorphic_iff : IsWeakPseudoholomorphic J ν p u ↔
    MemWkpLocMap I p 1 u ∧
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  Iff.rfl

/-- On the whole surface, the predicate on a set is the predicate for maps from the surface. -/
@[simp]
theorem isWeakPseudoholomorphicOn_univ :
    IsWeakPseudoholomorphicOn J ν p u univ ↔ IsWeakPseudoholomorphic J ν p u := by
  simp only [isWeakPseudoholomorphicOn_iff, isWeakPseudoholomorphic_iff,
    memWkpLocMapOnGroupoid_univ, univ_inter]

namespace IsWeakPseudoholomorphicOn

/-- A weak pseudoholomorphic map on `s` is a local Sobolev map on `s`. -/
theorem memWkpLocMapOn (h : IsWeakPseudoholomorphicOn J ν p u s) : MemWkpLocMapOn I p 1 u s :=
  h.1

/-- A weak pseudoholomorphic map on `s` is continuous on `s`. -/
theorem continuousOn (h : IsWeakPseudoholomorphicOn J ν p u s) : ContinuousOn u s :=
  h.1.continuousOn

/-- **Reading off the coordinate equation.** In a holomorphic chart `φ` and a smooth chart `ψ`,
a weak pseudoholomorphic map solves the planar weak equation with the structure and term read in
the charts. -/
theorem isWeakCauchyRiemannOn_chart (h : IsWeakPseudoholomorphicOn J ν p u s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  h.2 φ hφ ψ hψ

/-- Restriction to a smaller set, in particular to an open subset, preserves weak solutions. -/
theorem mono (h : IsWeakPseudoholomorphicOn J ν p u s) (hts : t ⊆ s) :
    IsWeakPseudoholomorphicOn J ν p u t :=
  ⟨h.1.mono hts, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts)))⟩

/-- Decreasing the exponent preserves weak solutions. -/
theorem mono_exponent (h : IsWeakPseudoholomorphicOn J ν p u s) (hqp : q ≤ p) :
    IsWeakPseudoholomorphicOn J ν q u s :=
  ⟨h.1.mono_exponent hqp, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).mono_exponent hqp⟩

end IsWeakPseudoholomorphicOn

namespace IsWeakPseudoholomorphic

/-- A weak pseudoholomorphic map is a local Sobolev map. -/
theorem memWkpLocMap (h : IsWeakPseudoholomorphic J ν p u) : MemWkpLocMap I p 1 u :=
  h.1

/-- A weak pseudoholomorphic map is continuous. -/
theorem continuous (h : IsWeakPseudoholomorphic J ν p u) : Continuous u :=
  h.1.continuous

/-- A weak pseudoholomorphic map is weakly pseudoholomorphic on every set. -/
theorem isWeakPseudoholomorphicOn (h : IsWeakPseudoholomorphic J ν p u) :
    IsWeakPseudoholomorphicOn J ν p u s :=
  (isWeakPseudoholomorphicOn_univ.2 h).mono (subset_univ s)

/-- **Reading off the coordinate equation.** In a holomorphic chart `φ` and a smooth chart `ψ`,
a weak pseudoholomorphic map solves the planar weak equation with the structure and term read in
the charts. -/
theorem isWeakCauchyRiemannOn_chart (h : IsWeakPseudoholomorphic J ν p u)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
      (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  h.2 φ hφ ψ hψ

/-- Decreasing the exponent preserves weak solutions. -/
theorem mono_exponent (h : IsWeakPseudoholomorphic J ν p u) (hqp : q ≤ p) :
    IsWeakPseudoholomorphic J ν q u :=
  isWeakPseudoholomorphicOn_univ.1 ((isWeakPseudoholomorphicOn_univ.2 h).mono_exponent hqp)

end IsWeakPseudoholomorphic

/-- **Continuity suffices for the Sobolev class.** A map is weakly pseudoholomorphic on `s`
exactly when it is continuous on `s` and solves the coordinate equation in every pair of charts:
each coordinate solution is already in `W^{1,p}_loc`. -/
theorem isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, h.2⟩, fun h ↦ ⟨memWkpLocMapOn_iff.2 ⟨h.1, fun φ hφ ψ hψ ↦ ?_⟩,
    h.2⟩⟩
  rw [← ψ.coe_extendTrans_refl I]
  exact (h.2 φ hφ ψ hψ).memWkpLoc_one

/-- **Continuity suffices for the Sobolev class.** A map is weakly pseudoholomorphic exactly when
it is continuous and solves the coordinate equation in every pair of charts. -/
theorem isWeakPseudoholomorphic_iff_continuous_isWeakCauchyRiemannOn :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
          (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
          (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  simp only [← isWeakPseudoholomorphicOn_univ,
    isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn, continuousOn_univ,
    univ_inter]

/-- **Regularity downgrade.** Regarding a `C^ℓ` structure `J` and an inhomogeneous term `ν` for
it as `C^m`, for `m ≤ ℓ`, does not change which maps are weakly pseudoholomorphic on `s`. -/
@[simp]
theorem isWeakPseudoholomorphicOn_ofLE {m : ℕ∞} (hmℓ : m ≤ ℓ) :
    IsWeakPseudoholomorphicOn (J.ofLE hmℓ)
        ((ν.ofLE hmℓ).ofEq (SmoothAlmostComplexStructure.toContMDiff_ofLE _ hmℓ) rfl) p u s ↔
      IsWeakPseudoholomorphicOn J ν p u s := by
  simp only [isWeakPseudoholomorphicOn_iff, ContMDiffAlmostComplexStructureFamily.chartField_ofLE,
    InhomogeneousTerm.chartTerm_ofEq, InhomogeneousTerm.chartTerm_ofLE]

/-- **Regularity downgrade.** Regarding a `C^ℓ` structure `J` and an inhomogeneous term `ν` for
it as `C^m`, for `m ≤ ℓ`, does not change which maps are weakly pseudoholomorphic. -/
@[simp]
theorem isWeakPseudoholomorphic_ofLE {m : ℕ∞} (hmℓ : m ≤ ℓ) :
    IsWeakPseudoholomorphic (J.ofLE hmℓ)
        ((ν.ofLE hmℓ).ofEq (SmoothAlmostComplexStructure.toContMDiff_ofLE _ hmℓ) rfl) p u ↔
      IsWeakPseudoholomorphic J ν p u := by
  simp only [← isWeakPseudoholomorphicOn_univ, isWeakPseudoholomorphicOn_ofLE]

/-! ### Locality -/

section Locality

variable [CompleteSpace E]

/-- **Locality.** A map is weakly pseudoholomorphic on `s` exactly when every point of `s` has a
neighbourhood within `s` on which it is. -/
theorem isWeakPseudoholomorphicOn_iff_locally :
    IsWeakPseudoholomorphicOn J ν p u s ↔
      ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, IsWeakPseudoholomorphicOn J ν p u t := by
  refine ⟨fun h _ _ ↦ ⟨s, self_mem_nhdsWithin, h⟩, fun h ↦ ⟨?_, fun φ hφ ψ hψ ↦ ?_⟩⟩
  · exact memWkpLocMapOnGroupoid_iff_locally.2 fun x hx ↦
      (h x hx).imp fun _ ht ↦ ⟨ht.1, ht.2.memWkpLocMapOn⟩
  · refine isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨t, ht, hut⟩ := h _ hz.2.1
    exact ⟨_, (φ.continuousOn_symm z hz.1).inter_preimage_inter_mem_nhdsWithin ht,
      hut.isWeakCauchyRiemannOn_chart hφ hψ⟩

/-- **Locality on the whole surface.** A map is weakly pseudoholomorphic exactly when every
point has a neighbourhood on which it is. -/
theorem isWeakPseudoholomorphic_iff_locally :
    IsWeakPseudoholomorphic J ν p u ↔ ∀ x, ∃ t ∈ 𝓝 x, IsWeakPseudoholomorphicOn J ν p u t := by
  simp [← isWeakPseudoholomorphicOn_univ, isWeakPseudoholomorphicOn_iff_locally (s := univ)]

/-- **The sheaf property.** A map is weakly pseudoholomorphic on a union of open sets exactly when
it is on each of them. -/
theorem isWeakPseudoholomorphicOn_iSup_iff {ι : Type*} (W : ι → Opens X) :
    IsWeakPseudoholomorphicOn J ν p u (⨆ i, W i : Opens X) ↔
      ∀ i, IsWeakPseudoholomorphicOn J ν p u (W i) := by
  refine ⟨fun h i ↦ h.mono (SetLike.coe_subset_coe.2 (le_iSup W i)), fun h ↦ ?_⟩
  refine isWeakPseudoholomorphicOn_iff_locally.2 fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := mem_iUnion.1 (by simpa only [Opens.coe_iSup] using hx)
  exact ⟨W i, mem_nhdsWithin_of_mem_nhds ((W i).isOpen.mem_nhds hi), h i⟩

end Locality

/-! ### Comparison with pseudoholomorphic maps -/

section Comparison

variable [CompleteSpace E]

/-- **The comparison in one pair of charts.** For the zero inhomogeneous term, a smooth structure
`J₀` independent of the domain point and a map `u` of class `C¹` on an open set `s`, the weak
equation in a holomorphic chart `φ` and a smooth chart `ψ` says that the derivative of `u ∘ φ⁻¹`
intertwines multiplication by `i` with `J₀` at every point of the coordinate domain. -/
private theorem isWeakCauchyRiemannOn_chart_iff (J₀ : SmoothAlmostComplexStructure I M)
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        ((ContMDiffAlmostComplexStructureFamily.const (IP := 𝓘(ℝ, ℂ)) (P := X)
          (J₀.toContMDiff ℓ)).chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        ((0 : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff
          ℓ) (ContMDiffAlmostComplexStructureFamily.const (J₀.toContMDiff ℓ))).chartTerm φ
            (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) ↔
      ∀ z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source), ∀ w : ℂ,
        mfderiv 𝓘(ℝ, ℂ) I (u ∘ φ.symm) z (Complex.I * w) =
          J₀ (u (φ.symm z)) (mfderiv 𝓘(ℝ, ℂ) I (u ∘ φ.symm) z w) := by
  set ψ' := ψ.extendTrans I (Homeomorph.refl E)
  have hΨ : ContDiff ℝ ∞ (Homeomorph.refl E) := contDiff_id
  have hΨs : ContDiff ℝ ∞ (Homeomorph.refl E).symm := contDiff_id
  have hD : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    φ.isOpen_inter_preimage_symm (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) I 1 (u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ)).mono inter_subset_left)
      fun _ hz ↦ hz.2.1
  have hf : ContDiffOn ℝ 1 (ψ' ∘ u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    contMDiffOn_iff_contDiffOn.mp
      (((ψ.contMDiffOn_extendTrans hψ hΨ).of_le (by exact_mod_cast le_top)).comp hg
        fun _ hz ↦ by simpa [ψ'] using hz.2.2)
  have hJ : ContinuousOn (fun z ↦ (J₀.toContMDiff ℓ).chartPushforward ψ' ((ψ' ∘ u ∘ φ.symm) z))
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    ((J₀.toContMDiff ℓ).contDiffOn_chartPushforward (ψ.contMDiffOn_extendTrans hψ hΨ)
      (ψ.contMDiffOn_extendTrans_symm hψ hΨs) le_top).continuousOn.comp
        hf.continuousOn fun _ hz ↦ ψ'.map_source (by simpa [ψ'] using hz.2.2)
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const, InhomogeneousTerm.chartTerm_zero]
  -- For `C¹` maps the weak equation is the pointwise one, which the chart reading translates.
  refine (isWeakCauchyRiemannOn_iff_of_contDiffOn (Ω := ⟨_, hD⟩) hf hJ
    continuousOn_const).trans (forall₂_congr fun z hz ↦ ?_)
  have hgz : MDifferentiableAt 𝓘(ℝ, ℂ) I (u ∘ φ.symm) z :=
    (hg.contMDiffAt (hD.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hy : (u ∘ φ.symm) z ∈ ψ'.source := by simpa [ψ'] using hz.2.2
  simpa only [SmoothAlmostComplexStructure.toContMDiff_apply, Function.comp_apply] using
    (J₀.toContMDiff ℓ).fderiv_chart_comp_add_eq_zero_iff hgz hy
      ((ψ.contMDiffAt_extendTrans hψ hΨ hz.2.2).mdifferentiableAt (by simp))
      ((ψ.contMDiffAt_extendTrans_symm hψ hΨs (ψ'.map_source hy)).mdifferentiableAt (by simp))

/-- **Comparison with `IsPseudoholomorphicOn`.** For the zero inhomogeneous term, a smooth almost
complex structure `J₀` on `M` regarded as a domain-independent family, and a map `u` of class `C¹`
on an open set `s`, the weak pseudoholomorphic equation for any exponent is pseudoholomorphy of
`u` on `s` for the structure `j` of `X` and `J₀`. -/
theorem isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn
    (J₀ : SmoothAlmostComplexStructure I M) (hs : IsOpen s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const (J₀.toContMDiff ℓ)) 0
        p u s ↔
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) J₀ u s := by
  -- Holomorphic charts of `X` intertwine `j` with multiplication by `i`, so in each pair of
  -- charts both conditions are `isWeakCauchyRiemannOn_chart_iff`.
  constructor
  · -- Read the equation in the charts at `x` and `u x`, and transport it back along `φ`.
    refine fun h ↦ isPseudoholomorphicOn_iff.2 fun x hx ↦ ?_
    set φ := chartAt ℂ x
    set ψ := chartAt H (u x)
    have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X := IsManifold.chart_mem_maximalAtlas x
    have hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
    have hxφ : x ∈ φ.source := mem_chart_source ℂ x
    have hz : φ x ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := by
      refine ⟨φ.map_source hxφ, ?_⟩
      rw [mem_preimage, φ.left_inv hxφ]
      exact ⟨hx, mem_chart_source H (u x)⟩
    have hcr := (isWeakCauchyRiemannOn_chart_iff J₀ hs hu hφ hψ).1
      (h.isWeakCauchyRiemannOn_chart hφ hψ) _ hz
    have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) I (u ∘ φ.symm) (φ x) := by
      refine ((hu.contMDiffAt (hs.mem_nhds ?_)).comp (φ x)
        (contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ) hz.1)).mdifferentiableAt
        one_ne_zero
      rw [φ.left_inv hxφ]
      exact hx
    have hg : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J₀
        (u ∘ φ.symm) (φ x) := by
      refine isPseudoholomorphicAt_iff_mfderiv.2 ⟨hgd, fun (w : ℂ) ↦ ?_⟩
      rw [SmoothAlmostComplexStructure.ofComplexManifold_apply, smul_eq_mul]
      exact hcr w
    have hφx : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ X)
        (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) φ x :=
      isPseudoholomorphicAt_ofComplexManifold_iff.2 (mdifferentiableAt_of_mem_maximalAtlas hφ hxφ)
    refine ((hg.comp hφx).congr_of_eventuallyEq ?_).isPseudoholomorphicWithinAt
    filter_upwards [φ.open_source.mem_nhds hxφ] with y hy
    simp only [Function.comp_apply, φ.left_inv hy]
  · -- Compose with the holomorphic inverse chart and read the derivative condition in charts.
    intro h
    refine ⟨hu.memWkpLocMapOn le_rfl hs, fun φ hφ ψ hψ ↦
      (isWeakCauchyRiemannOn_chart_iff J₀ hs hu hφ hψ).2 fun z hz w ↦ ?_⟩
    have hx : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) J₀ u
        (φ.symm z) :=
      (isPseudoholomorphicOn_iff.1 h _ hz.2.1).isPseudoholomorphicAt_of_mem_nhds
        (hs.mem_nhds hz.2.1)
    have hφs : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)
        (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) φ.symm z :=
      isPseudoholomorphicAt_ofComplexManifold_iff.2
        (mdifferentiableAt_symm_of_mem_maximalAtlas hφ hz.1)
    have := (hx.comp hφs).mfderiv_apply_commute w
    rwa [SmoothAlmostComplexStructure.ofComplexManifold_apply, smul_eq_mul] at this

/-- **Comparison with `IsPseudoholomorphic`.** For the zero inhomogeneous term, a smooth almost
complex structure `J₀` on `M` regarded as a domain-independent family, and a map `u` of class
`C¹`, the weak pseudoholomorphic equation for any exponent is pseudoholomorphy of `u` for the
structure `j` of `X` and `J₀`. -/
theorem isWeakPseudoholomorphic_iff_isPseudoholomorphic
    (J₀ : SmoothAlmostComplexStructure I M) (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) :
    IsWeakPseudoholomorphic (ContMDiffAlmostComplexStructureFamily.const (J₀.toContMDiff ℓ)) 0
        p u ↔
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) J₀ u := by
  rw [← isWeakPseudoholomorphicOn_univ, ← isPseudoholomorphicOn_univ]
  exact isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn J₀ isOpen_univ hu.contMDiffOn

/-- **Holomorphic maps.** A map from a Riemann surface into a complex manifold `N`, holomorphic
on an open set, is weakly pseudoholomorphic there for the almost complex structure of `N` and
`ν = 0`, for every exponent. -/
theorem _root_.MDifferentiableOn.isWeakPseudoholomorphicOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℂ, F) ∞ N] {f : X → N} (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, F) f s)
    (hs : IsOpen s) :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold F N).toContMDiff ℓ)) 0 p f s := by
  have hf' := (hf.contMDiffOn (n := 1) hs).restrictScalars ℝ
  rw [modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at hf'
  exact (isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn _ hs hf').2
    (isPseudoholomorphicOn_ofComplexManifold_iff.2 hf)

/-- **Holomorphic maps on the whole surface.** A holomorphic map from a Riemann surface into a
complex manifold `N` is weakly pseudoholomorphic for the almost complex structure of `N` and
`ν = 0`, for every exponent. -/
theorem _root_.MDifferentiable.isWeakPseudoholomorphic {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℂ, F) ∞ N] {f : X → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, F) f) :
    IsWeakPseudoholomorphic (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold F N).toContMDiff ℓ)) 0 p f :=
  isWeakPseudoholomorphicOn_univ.1 (hf.mdifferentiableOn.isWeakPseudoholomorphicOn isOpen_univ)

/-- **The identity is a solution.** The identity of a Riemann surface is weakly pseudoholomorphic
on every set for its own structure and `ν = 0`, for every exponent. -/
@[simp]
theorem isWeakPseudoholomorphicOn_id (s : Set X) :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ)) 0 p id s :=
  (mdifferentiableOn_id.isWeakPseudoholomorphicOn isOpen_univ).mono (subset_univ s)

/-- **The identity is a solution.** The identity of a Riemann surface is weakly pseudoholomorphic
for its own structure and `ν = 0`, for every exponent. -/
@[simp]
theorem isWeakPseudoholomorphic_id :
    IsWeakPseudoholomorphic (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ)) 0 p (id : X → X) :=
  isWeakPseudoholomorphicOn_univ.1 (isWeakPseudoholomorphicOn_id univ)

end Comparison

/-! ### Constant maps -/

section Constant

variable [CompleteSpace E]

/-- **Constant maps solve the homogeneous equation** on every set, for every domain-dependent
structure. -/
@[simp]
theorem isWeakPseudoholomorphicOn_const (y : M) :
    IsWeakPseudoholomorphicOn J 0 p (fun _ ↦ y) s := by
  refine ⟨(contMDiff_const.memWkpLocMap (n := 1) le_rfl).memWkpLocMapOnGroupoid, fun φ _ ψ _ ↦ ?_⟩
  rw [InhomogeneousTerm.chartTerm_zero]
  exact isWeakCauchyRiemannOn_const (ψ.extendTrans I (Homeomorph.refl E) y)

/-- **Constant maps solve the homogeneous equation** for every domain-dependent structure. -/
@[simp]
theorem isWeakPseudoholomorphic_const (y : M) : IsWeakPseudoholomorphic J 0 p (fun _ ↦ y) :=
  isWeakPseudoholomorphicOn_univ.1 (isWeakPseudoholomorphicOn_const y)

end Constant

/-! ### Checks on the plane -/

section Plane

/-- **Conjugation does not solve the equation** on `X = M = ℂ` for the structure `i` and `ν = 0`,
on any nonempty open set. -/
theorem not_isWeakPseudoholomorphicOn_conj {s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty) :
    ¬IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
        conj s := by
  intro h
  -- Read the equation in the identity charts, where it is the planar weak equation.
  have h' := h.isWeakCauchyRiemannOn_chart (StructureGroupoid.id_mem_maximalAtlas _)
    (StructureGroupoid.id_mem_maximalAtlas _)
  have hD : (OpenPartialHomeomorph.refl ℂ).target ∩ (OpenPartialHomeomorph.refl ℂ).symm ⁻¹'
      (s ∩ conj ⁻¹' (OpenPartialHomeomorph.refl ℂ).source) = s := by
    simp
  have hJ : (fun (_ : ℂ) (v : ℂ) ↦
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ).toEndomorphism v) =
        fun _ _ ↦ Complex.I • ContinuousLinearMap.id ℝ ℂ := by
    funext _ v
    rw [SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
      SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  rw [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl,
    ContMDiffAlmostComplexStructureFamily.chartField_const,
    ContMDiffAlmostComplexStructure.chartPushforward_refl, InhomogeneousTerm.chartTerm_zero, hD,
    hJ] at h'
  exact not_isWeakCauchyRiemannOn_conj (Ω := ⟨s, hs⟩) hne h'

variable [CompleteSpace E]

/-- **Constant maps and the inhomogeneous equation.** On `X = ℂ`, a constant map with value `y`
is weakly pseudoholomorphic on an open set `s` exactly when the inhomogeneous term at `(z, y)`
vanishes on `∂ₛ` for almost every `z ∈ s`. -/
theorem isWeakPseudoholomorphicOn_const_iff_complex
    {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) ℂ ℓ}
    {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) J}
    {s : Set ℂ} (hs : IsOpen s) (y : M) :
    IsWeakPseudoholomorphicOn J ν p (fun _ ↦ y) s ↔
      ∀ᵐ z ∂volume.restrict s, ν.val.tangentHom (z, y) (1 : ℂ) = 0 := by
  have hΨ : ContDiff ℝ ∞ (Homeomorph.refl E) := contDiff_id
  have hΨs : ContDiff ℝ ∞ (Homeomorph.refl E).symm := contDiff_id
  -- A smooth chart `ψ` of `M`, read in `E`, is differentiable at `y` with inverse differentiable
  -- at the image of `y`, so the term read in charts vanishes there exactly when `ν` does on `∂ₛ`.
  have hzero : ∀ {ψ : OpenPartialHomeomorph M H}, ψ ∈ IsManifold.maximalAtlas I ∞ M →
      y ∈ ψ.source → ∀ (φ : OpenPartialHomeomorph ℂ ℂ) (z : ℂ),
        ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)) z
            (ψ.extendTrans I (Homeomorph.refl E) y) = 0 ↔
          ν.val.tangentHom (φ.symm z, y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ)) = 0 :=
    fun {ψ} hψ hy φ z ↦ by
      have hy' : y ∈ (ψ.extendTrans I (Homeomorph.refl E)).source := by simpa using hy
      exact InhomogeneousTerm.chartTerm_apply_eq_zero_iff ν φ hy'
        ((ψ.contMDiffAt_extendTrans hψ hΨ hy).mdifferentiableAt (by simp))
        ((ψ.contMDiffAt_extendTrans_symm hψ hΨs
          ((ψ.extendTrans I _).map_source hy')).mdifferentiableAt (by simp)) z
  constructor
  · intro h
    have hψ : chartAt H y ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas y
    have hy : y ∈ (chartAt H y).source := mem_chart_source H y
    have h' := (isWeakCauchyRiemannOn_const_iff
      ((chartAt H y).extendTrans I (Homeomorph.refl E) y)).1
        (h.isWeakCauchyRiemannOn_chart (StructureGroupoid.id_mem_maximalAtlas _) hψ)
    have hD : (OpenPartialHomeomorph.refl ℂ).target ∩ (OpenPartialHomeomorph.refl ℂ).symm ⁻¹'
        (s ∩ (fun _ : ℂ ↦ y) ⁻¹' (chartAt H y).source) = s := by
      simp [hy]
    rw [hD, hs.interior_eq] at h'
    filter_upwards [h'] with z hz
    have := ((hzero hψ hy _ z).1 hz)
    rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
      mfderiv_id] at this
    -- The identity of the tangent space at `z` sends `1` to `1`.
    exact this
  · intro hae
    refine ⟨(contMDiff_const.memWkpLocMap (n := 1) le_rfl).memWkpLocMapOnGroupoid,
      fun φ hφ ψ hψ ↦ ?_⟩
    have hD : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ (fun _ : ℂ ↦ y) ⁻¹' ψ.source)) :=
      φ.isOpen_inter_preimage_symm (continuousOn_const.isOpen_inter_preimage hs ψ.open_source)
    refine (isWeakCauchyRiemannOn_const_iff (ψ.extendTrans I (Homeomorph.refl E) y)).2 ?_
    rw [hD.interior_eq]
    -- In a holomorphic chart `φ` the term is read at `φ⁻¹ z`; the exceptional points form the
    -- image under `φ` of a null set, which is null.
    have hN : volume {x | x ∈ s ∧ ν.val.tangentHom (x, y) (1 : ℂ) ≠ 0} = 0 := by
      refine measure_mono_null (fun x hx ↦ ?_)
        (ae_iff.1 ((ae_restrict_iff' hs.measurableSet).1 hae))
      exact fun h ↦ hx.2 (h hx.1)
    have hφd : DifferentiableOn ℝ φ φ.source :=
      ((contMDiffOn_iff_contDiffOn.1 (contMDiffOn_of_mem_maximalAtlas hφ)).differentiableOn
        one_ne_zero).restrictScalars ℝ
    have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hφd.mono inter_subset_right) (measure_mono_null inter_subset_left hN)
    refine (ae_restrict_iff' hD.measurableSet).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 himg] with z hz hzD
    refine (hzero hψ hzD.2.2 φ z).2
      (DFunLike.congr_fun ((ν.tangentHom_eq_zero_iff_apply_one_eq_zero _).2 ?_) _)
    by_contra hne
    exact hz ⟨φ.symm z, ⟨⟨hzD.2.1, hne⟩, φ.map_target hzD.1⟩, φ.right_inv hzD.1⟩

end Plane

end TauCeti
