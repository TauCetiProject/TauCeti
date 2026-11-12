/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Locality
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Weak pseudoholomorphic maps from a Riemann surface

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, with its almost complex structure
`j = TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ X`. Let `M` be a manifold modelled
on a real normed space `E`, `J` a domain-dependent almost complex structure on
`M` of class `C^ℓ` and `ν` an inhomogeneous term for `(j, J)`. A map `u : X → M` is *weakly
pseudoholomorphic* on `s ⊆ X` for `(J, ν)` and an exponent `p`
(`TauCeti.IsWeakPseudoholomorphicOn J ν p u s`) when it lies in the local Sobolev class
`W^{1,p}_loc` on `s` and the equation `du + J(z, u) ∘ du ∘ j = 2ν(z, u)` holds almost everywhere
in every pair of charts. In a holomorphic chart `φ` of `X` and a chart `ψ` of `M` the equation is
read on the coordinate vector `∂ₛ` as the planar weak equation
`TauCeti.IsWeakCauchyRiemannOn` for `ψ ∘ u ∘ φ⁻¹`, with the structure
`J_φψ(z, v) = dψ ∘ J(φ⁻¹ z, ψ⁻¹ v) ∘ dψ⁻¹`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.chartField`) and the term
`η_φψ(z, v) = 2 dψ (ν(φ⁻¹ z, ψ⁻¹ v)(dφ⁻¹ 1))` (`TauCeti.InhomogeneousTerm.chartTerm`). Testing
on `∂ₛ` alone suffices: the value of the equation on `∂ₜ = j ∂ₛ` is `-J(z, u)` applied to its
value on `∂ₛ`, since `ν` is complex antilinear.

## Main results

* `TauCeti.IsWeakPseudoholomorphicOn`: the predicate, with its unfolding, reading-off and
  monotonicity lemmas.
* `TauCeti.isWeakPseudoholomorphicOn_iff_locally`, `TauCeti.isWeakPseudoholomorphicOn_iSup_iff`:
  it is a sheaf condition on `X`.
* `TauCeti.isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn`: **Comparison.** For `ν = 0`, `J`
  independent of the domain point and smooth, and `u` of class `C¹` on an open set, the predicate
  is Tau Ceti's `IsPseudoholomorphicOn` for `j` and `J`. In particular holomorphic maps into a
  complex manifold solve the equation for its structure
  (`MDifferentiableOn.isWeakPseudoholomorphicOn`).
* `TauCeti.isWeakPseudoholomorphicOn_const`: constant maps solve the homogeneous equation for
  every `J`.
* Checks on `X = M = ℂ`: the identity is a solution for the structure `i`
  (`TauCeti.isWeakPseudoholomorphicOn_id_complex`) and conjugation is not
  (`TauCeti.not_isWeakPseudoholomorphicOn_conj`).
* Check on `X = ℂ`, for any `M`: a constant map with value `u₀` solves the inhomogeneous equation
  exactly when `ν(z, u₀)` vanishes on `∂ₛ` for almost every `z`
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

open Set Filter TopologicalSpace MeasureTheory Complex
open scoped Manifold ContDiff Topology ComplexConjugate TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

/-! ### The predicate -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {ℓ : ℕ∞}

/-- A domain-dependent structure read in a chart `φ` of `X` and a chart `ψ` of `M`: at
`(z, v)`, the structure `J(φ⁻¹ z, ψ⁻¹ v)` pushed forward along `ψ`, that is
`dψ ∘ J(φ⁻¹ z, ψ⁻¹ v) ∘ dψ⁻¹`. -/
def ContMDiffAlmostComplexStructureFamily.chartField
    (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, E) M 𝓘(ℝ, ℂ) X ℓ)
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M E) (z : ℂ) (v : E) :
    E →L[ℝ] E :=
  (J.freeze (φ.symm z)).chartPushforward ψ v

/-- Evaluate a structure read in charts. -/
theorem ContMDiffAlmostComplexStructureFamily.chartField_apply
    (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, E) M 𝓘(ℝ, ℂ) X ℓ)
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M E) (z : ℂ) (v : E) :
    J.chartField φ ψ z v = (J.freeze (φ.symm z)).chartPushforward ψ v :=
  (rfl)

/-- A structure independent of the domain point reads in charts as its pushforward along the
chart of `M`. -/
@[simp]
theorem ContMDiffAlmostComplexStructureFamily.chartField_const
    (J : ContMDiffAlmostComplexStructure 𝓘(ℝ, E) ℓ M) (φ : OpenPartialHomeomorph X ℂ)
    (ψ : OpenPartialHomeomorph M E) :
    (ContMDiffAlmostComplexStructureFamily.const (IP := 𝓘(ℝ, ℂ)) (P := X) J).chartField φ ψ =
      fun _ v ↦ J.chartPushforward ψ v := by
  funext z v
  rw [chartField_apply, freeze_const]

variable [IsManifold 𝓘(ℂ) ∞ X] {j : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) ℓ X}
  {J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, E) M 𝓘(ℝ, ℂ) X ℓ}

/-- An inhomogeneous term read in a chart `φ` of `X` and a chart `ψ` of `M`: at `(z, v)`, twice
the value of `ν(φ⁻¹ z, ψ⁻¹ v)` on the coordinate vector `∂ₛ = dφ⁻¹ 1`, pushed forward along `ψ`.
This is the right-hand side `η` of the coordinate equation `∂ₛu + J(z, u) ∂ₜu = η(z, u)`. -/
def InhomogeneousTerm.chartTerm (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph X ℂ)
    (ψ : OpenPartialHomeomorph M E) (z : ℂ) (v : E) : E :=
  (2 : ℝ) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (ψ.symm v)
    (ν.val.tangentHom (φ.symm z, ψ.symm v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ)))

/-- Evaluate an inhomogeneous term read in charts. -/
theorem InhomogeneousTerm.chartTerm_apply (ν : InhomogeneousTerm j J)
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M E) (z : ℂ) (v : E) :
    ν.chartTerm φ ψ z v = (2 : ℝ) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (ψ.symm v)
      (ν.val.tangentHom (φ.symm z, ψ.symm v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ))) :=
  (rfl)

/-- The zero inhomogeneous term reads as zero in all charts. -/
@[simp]
theorem InhomogeneousTerm.chartTerm_zero (φ : OpenPartialHomeomorph X ℂ)
    (ψ : OpenPartialHomeomorph M E) :
    (0 : InhomogeneousTerm j J).chartTerm φ ψ = fun _ _ ↦ 0 := by
  funext z v
  rw [chartTerm_apply, DomainDependentHomSection.tangentHom_apply, ZeroMemClass.coe_zero,
    ContMDiffSection.coe_zero, Pi.zero_apply]
  -- The zero map sends `∂ₛ` to zero, which is pushed forward to zero.
  exact (congrArg ((2 : ℝ) • ·) (map_zero _)).trans (smul_zero _)

/-- An inhomogeneous term read in charts vanishes at the value `ψ y` exactly when the term at
`(φ⁻¹ z, y)` vanishes on `∂ₛ`. -/
theorem InhomogeneousTerm.chartTerm_apply_eq_zero_iff (ν : InhomogeneousTerm j J)
    (φ : OpenPartialHomeomorph X ℂ) {ψ : OpenPartialHomeomorph M E}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : M} (hy : y ∈ ψ.source) (z : ℂ) :
    ν.chartTerm φ ψ z (ψ y) = 0 ↔
      ν.val.tangentHom (φ.symm z, y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ)) = 0 := by
  -- The chart derivative is injective, with left inverse the derivative of `ψ.symm`.
  have hψ1 : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hψ
  have hinv := ψ.mfderiv_symm_apply_mfderiv_apply hy
    (mdifferentiableAt_of_mem_maximalAtlas hψ1 hy)
    (mdifferentiableAt_symm_of_mem_maximalAtlas hψ1 (ψ.map_source hy))
  rw [chartTerm_apply, ψ.left_inv hy]
  set c : ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ)
  set v : E := ν.val.tangentHom (φ.symm z, y) c
  -- The tangent space `TangentSpace 𝓘(ℝ, E) (ψ y)` is `E` by definition; state the goal in `E`.
  change (2 : ℝ) • (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ y v : E) = 0 ↔ v = 0
  rw [smul_eq_zero, or_iff_right two_ne_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; exact map_zero _⟩
  rw [← hinv v, h]
  exact map_zero _

/-- On a Riemann surface, an inhomogeneous term vanishes at a point exactly when it vanishes on
`∂ₛ = 1` there. -/
theorem InhomogeneousTerm.tangentHom_eq_zero_iff_apply_one_eq_zero
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (q : X × M) : ν.val.tangentHom q = 0 ↔ ν.val.tangentHom q (1 : ℂ) = 0 := by
  -- The tangent space of `X` at `q.1` is `ℂ`, where `1` and `i` span over `ℝ`.
  have key : ∀ L : ℂ →L[ℝ] E, L 1 = 0 → L I = 0 → L = 0 := fun L h1 hI ↦ by
    ext a
    have ha : a = a.re • (1 : ℂ) + a.im • I := by simp
    rw [zero_apply, ha, map_add, map_smul, map_smul, h1, hI, smul_zero, smul_zero, add_zero]
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ key _ h ?_⟩
  -- By complex antilinearity, the value on `∂ₜ = j ∂ₛ = i` is `-J` applied to the value on `1`.
  have hj1 : ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) q.1 (1 : ℂ) =
      I := by
    simp [SmoothAlmostComplexStructure.ofComplexManifold_apply]
    -- The two sides are `I` in `TangentSpace 𝓘(ℝ, ℂ) q.1` and in `ℂ`, equal by definition.
    rfl
  have hI := ν.tangentHom_apply_j q (1 : ℂ)
  rw [hj1, h, map_zero, neg_zero] at hI
  exact hI

variable (J) in
/-- **Weak pseudoholomorphic maps.** For a domain-dependent almost complex structure `J` on `M`,
an inhomogeneous term `ν` for `J` and the structure `j` of the Riemann surface `X`, and an exponent
`p`, a map `u : X → M` is weakly pseudoholomorphic on `s` when it is in `W^{1,p}_loc` on `s` and,
for every holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`, the coordinate
expression `ψ ∘ u ∘ φ⁻¹` is a weak solution of `∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)` on the part of
the target of `φ` over `s` where `u` maps into the source of `ψ`. Here `J_φψ` is
`ContMDiffAlmostComplexStructureFamily.chartField` and `η_φψ` is `InhomogeneousTerm.chartTerm`:
the equation `du + J(z, u) ∘ du ∘ j = 2ν(z, u)` evaluated on `∂ₛ`. The definition is intended for
open `s` and `p > 2`. -/
def IsWeakPseudoholomorphicOn
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (p : ENNReal) (u : X → M) (s : Set X) : Prop :=
  MemWkpLocMapOn 𝓘(ℝ, E) p 1 u s ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (J.chartField φ ψ)
        (ν.chartTerm φ ψ) (ψ ∘ u ∘ φ.symm)

variable
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p q : ENNReal} {u : X → M} {s t : Set X}

/-- Unfolding the definition of weak pseudoholomorphic maps. -/
theorem isWeakPseudoholomorphicOn_iff : IsWeakPseudoholomorphicOn J ν p u s ↔
    MemWkpLocMapOn 𝓘(ℝ, E) p 1 u s ∧
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M,
        IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (J.chartField φ ψ)
          (ν.chartTerm φ ψ) (ψ ∘ u ∘ φ.symm) :=
  Iff.rfl

namespace IsWeakPseudoholomorphicOn

/-- A weak pseudoholomorphic map on `s` is a local Sobolev map on `s`. -/
theorem memWkpLocMapOn (h : IsWeakPseudoholomorphicOn J ν p u s) :
    MemWkpLocMapOn 𝓘(ℝ, E) p 1 u s :=
  h.1

/-- A weak pseudoholomorphic map on `s` is continuous on `s`. -/
theorem continuousOn (h : IsWeakPseudoholomorphicOn J ν p u s) : ContinuousOn u s :=
  h.1.continuousOn

/-- **Reading off the coordinate equation.** In a holomorphic chart `φ` and a smooth chart `ψ`,
a weak pseudoholomorphic map solves the planar weak equation with the structure and term read in
the charts. -/
theorem isWeakCauchyRiemannOn_chart (h : IsWeakPseudoholomorphicOn J ν p u s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M E} (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (J.chartField φ ψ)
      (ν.chartTerm φ ψ) (ψ ∘ u ∘ φ.symm) :=
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

/-! ### Locality -/

section Locality

variable [CompleteSpace E]

/-- **Locality.** A map is weakly pseudoholomorphic on `s` exactly when every point of `s` has a
neighbourhood within `s` on which it is. -/
theorem isWeakPseudoholomorphicOn_iff_locally :
    IsWeakPseudoholomorphicOn J ν p u s ↔
      ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, IsWeakPseudoholomorphicOn J ν p u t := by
  refine ⟨fun h _ _ ↦ ⟨s, self_mem_nhdsWithin, h⟩, fun h ↦ ⟨?_, fun φ hφ ψ hψ ↦ ?_⟩⟩
  · exact memWkpLocMapOn_iff_locally.2 fun x hx ↦
      (h x hx).imp fun _ ht ↦ ⟨ht.1, ht.2.memWkpLocMapOn⟩
  · refine isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨t, ht, hut⟩ := h _ hz.2.1
    exact ⟨_, φ.target_inter_preimage_symm_mem_nhdsWithin hz ht,
      hut.isWeakCauchyRiemannOn_chart hφ hψ⟩

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

/-- **The equation at a point, read in a chart of `M`.** For a map `g` from the plane into `M`,
differentiable at `z` with `g z` in the source of a chart `ψ`, the coordinate equation
`∂ₛ(ψ ∘ g) + ψ_* J ∂ₜ(ψ ∘ g) = 0` at `z` says that the derivative of `g` at `z` intertwines
multiplication by `i` with `J`. -/
private theorem fderiv_chart_comp_add_eq_zero_iff
    (J₀ : ContMDiffAlmostComplexStructure 𝓘(ℝ, E) ℓ M) {ψ : OpenPartialHomeomorph M E}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {g : ℂ → M}
    {z : ℂ} (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z) (hgz : g z ∈ ψ.source) :
    fderiv ℝ (ψ ∘ g) z 1 + J₀.chartPushforward ψ ((ψ ∘ g) z) (fderiv ℝ (ψ ∘ g) z I) = 0 ↔
      ∀ w : ℂ, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z (I * w) =
        J₀ (g z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z w) := by
  have hψ1 : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hψ
  have hψd := mdifferentiableAt_of_mem_maximalAtlas hψ1 hgz
  have hψsd := mdifferentiableAt_symm_of_mem_maximalAtlas hψ1 (ψ.map_source hgz)
  have hD : ∀ w, fderiv ℝ (ψ ∘ g) z w =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (g z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z w) := fun w ↦ by
    have h := mfderiv_comp z hψd hg
    rw [mfderiv_eq_fderiv] at h
    exact congr($h w)
  have hA := J₀.chartPushforward_apply_chartPushforward_apply ψ (ψ.map_source hgz)
    (by rwa [ψ.left_inv hgz]) hψsd
  have hinv := ψ.mfderiv_symm_apply_mfderiv_apply hgz hψd hψsd
  refine (LinearMap.forall_apply_I_mul_eq_iff (fderiv ℝ (ψ ∘ g) z : ℂ →ₗ[ℝ] E)
    (A := (J₀.chartPushforward ψ (ψ (g z))).toLinearMap) hA).symm.trans
    (forall_congr' fun w ↦ ?_)
  have hJ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (g z) (J₀ (g z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z w)) =
      J₀.chartPushforward ψ (ψ (g z))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (g z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z w)) :=
    DFunLike.congr_fun (J₀.mfderiv_comp_toEndomorphism ψ hgz hψd hψsd) _
  simp only [ContinuousLinearMap.coe_coe]
  rw [hD, hD, ← hJ]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← hinv (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) g z (I * w)), h, hinv]

omit [IsManifold 𝓘(ℂ) ∞ X] in
/-- The inverse of a holomorphic chart is real `C¹` on its target. -/
private theorem contMDiffOn_symm_of_mem_maximalAtlas_complex {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 φ.symm φ.target :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero _ one_ne_zero hφ)

variable [CompleteSpace E]

/-- **The comparison in one pair of charts.** For the zero inhomogeneous term, a smooth structure
`J₀` independent of the domain point and a map `u` of class `C¹` on an open set `s`, the weak
equation in a holomorphic chart `φ` and a smooth chart `ψ` says that the derivative of `u ∘ φ⁻¹`
intertwines multiplication by `i` with `J₀` at every point of the coordinate domain. -/
private theorem isWeakCauchyRiemannOn_chart_iff (J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, E) M)
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 u s) {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {ψ : OpenPartialHomeomorph M E}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        ((ContMDiffAlmostComplexStructureFamily.const (J₀.toContMDiff ℓ)).chartField φ ψ)
        ((0 : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff
          ℓ) (ContMDiffAlmostComplexStructureFamily.const (J₀.toContMDiff ℓ))).chartTerm φ ψ)
        (ψ ∘ u ∘ φ.symm) ↔
      ∀ z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source), ∀ w : ℂ,
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ φ.symm) z (I * w) =
          J₀ (u (φ.symm z)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ φ.symm) z w) := by
  have hD : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    φ.isOpen_inter_preimage_symm (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (u ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas_complex hφ).mono inter_subset_left)
      fun _ hz ↦ hz.2.1
  have hf : ContDiffOn ℝ 1 (ψ ∘ u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    contMDiffOn_iff_contDiffOn.mp
      (((contMDiffOn_of_mem_maximalAtlas hψ).of_le (by exact_mod_cast le_top)).comp hg
        fun _ hz ↦ hz.2.2)
  have hJ : ContinuousOn (fun z ↦ (J₀.toContMDiff ℓ).chartPushforward ψ ((ψ ∘ u ∘ φ.symm) z))
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    ((J₀.toContMDiff ℓ).contDiffOn_chartPushforward hψ).continuousOn.comp hf.continuousOn
      fun _ hz ↦ ψ.map_source hz.2.2
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const, InhomogeneousTerm.chartTerm_zero]
  -- For `C¹` maps the weak equation is the pointwise one, which the chart reading translates.
  refine (isWeakCauchyRiemannOn_iff_of_contDiffOn (Ω := ⟨_, hD⟩) hf hJ
    continuousOn_const).trans (forall₂_congr fun z hz ↦ ?_)
  have hgz : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ φ.symm) z :=
    (hg.contMDiffAt (hD.mem_nhds hz)).mdifferentiableAt one_ne_zero
  simpa only [SmoothAlmostComplexStructure.toContMDiff_apply, Function.comp_apply] using
    fderiv_chart_comp_add_eq_zero_iff (J₀.toContMDiff ℓ) hψ hgz hz.2.2

/-- **Comparison with `IsPseudoholomorphicOn`.** For the zero inhomogeneous term, a smooth almost
complex structure `J₀` on `M` regarded as a domain-independent family, and a map `u` of class `C¹`
on an open set `s`, the weak pseudoholomorphic equation for any exponent is pseudoholomorphy of
`u` on `s` for the structure `j` of `X` and `J₀`. -/
theorem isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn
    (J₀ : SmoothAlmostComplexStructure 𝓘(ℝ, E) M) (hs : IsOpen s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 u s) :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const (J₀.toContMDiff ℓ)) 0
        p u s ↔
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ X) J₀ u s := by
  -- Holomorphic charts of `X` intertwine `j` with multiplication by `i`, so in each pair of
  -- charts both conditions are `isWeakCauchyRiemannOn_chart_iff`.
  constructor
  · -- Read the equation in the charts at `x` and `u x`, and transport it back along `φ`.
    refine fun h ↦ isPseudoholomorphicOn_iff.2 fun x hx ↦ ?_
    set φ := chartAt ℂ x
    set ψ := chartAt E (u x)
    have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X := IsManifold.chart_mem_maximalAtlas x
    have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas _
    have hxφ : x ∈ φ.source := mem_chart_source ℂ x
    have hz : φ x ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := by
      refine ⟨φ.map_source hxφ, ?_⟩
      rw [mem_preimage, φ.left_inv hxφ]
      exact ⟨hx, mem_chart_source E (u x)⟩
    have hcr := (isWeakCauchyRiemannOn_chart_iff J₀ hs hu hφ hψ).1
      (h.isWeakCauchyRiemannOn_chart hφ hψ) _ hz
    have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ φ.symm) (φ x) := by
      refine ((hu.contMDiffAt (hs.mem_nhds ?_)).comp (φ x)
        ((contMDiffOn_symm_of_mem_maximalAtlas_complex hφ).contMDiffAt
          (φ.open_target.mem_nhds hz.1))).mdifferentiableAt one_ne_zero
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

end Comparison

/-! ### Constant maps -/

section Constant

variable [CompleteSpace E]

/-- **Constant maps solve the homogeneous equation** for every domain-dependent structure. -/
theorem isWeakPseudoholomorphicOn_const (hs : IsOpen s) (y : M) :
    IsWeakPseudoholomorphicOn J 0 p (fun _ ↦ y) s := by
  refine ⟨contMDiffOn_const.memWkpLocMapOn (n := 1) le_rfl hs, fun φ _ ψ _ ↦ ?_⟩
  rw [InhomogeneousTerm.chartTerm_zero]
  exact isWeakCauchyRiemannOn_const (ψ y)

end Constant

/-! ### Checks on the plane -/

section Plane

/-- **The identity solves the equation** on `X = M = ℂ` for the structure `i` and `ν = 0`. -/
theorem isWeakPseudoholomorphicOn_id_complex {s : Set ℂ} (hs : IsOpen s) :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p id s :=
  (isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn _ hs contMDiffOn_id).2
    (isPseudoholomorphicOn_id _ s)

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
        fun _ _ ↦ I • ContinuousLinearMap.id ℝ ℂ := by
    funext _ v
    rw [SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
      SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const,
    ContMDiffAlmostComplexStructure.chartPushforward_refl, InhomogeneousTerm.chartTerm_zero, hD,
    hJ] at h'
  exact not_isWeakCauchyRiemannOn_conj (Ω := ⟨s, hs⟩) hne h'

variable [CompleteSpace E]

/-- **Constant maps and the inhomogeneous equation.** On `X = ℂ`, a constant map with value `y`
is weakly pseudoholomorphic on an open set `s` exactly when the inhomogeneous term at `(z, y)`
vanishes on `∂ₛ` for almost every `z ∈ s`. -/
theorem isWeakPseudoholomorphicOn_const_iff_complex
    {J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, E) M 𝓘(ℝ, ℂ) ℂ ℓ}
    {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) J}
    {s : Set ℂ} (hs : IsOpen s) (y : M) :
    IsWeakPseudoholomorphicOn J ν p (fun _ ↦ y) s ↔
      ∀ᵐ z ∂volume.restrict s, ν.val.tangentHom (z, y) (1 : ℂ) = 0 := by
  constructor
  · intro h
    have hψ : chartAt E y ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
      IsManifold.chart_mem_maximalAtlas y
    have hy : y ∈ (chartAt E y).source := mem_chart_source E y
    have h' := (isWeakCauchyRiemannOn_const_iff (chartAt E y y)).1
      (h.isWeakCauchyRiemannOn_chart (StructureGroupoid.id_mem_maximalAtlas _) hψ)
    have hD : (OpenPartialHomeomorph.refl ℂ).target ∩ (OpenPartialHomeomorph.refl ℂ).symm ⁻¹'
        (s ∩ (fun _ : ℂ ↦ y) ⁻¹' (chartAt E y).source) = s := by
      simp [hy]
    rw [hD, hs.interior_eq] at h'
    filter_upwards [h'] with z hz
    have := (InhomogeneousTerm.chartTerm_apply_eq_zero_iff ν _ hψ hy z).1 hz
    rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
      mfderiv_id] at this
    -- The identity of the tangent space at `z` sends `1` to `1`.
    exact this
  · intro hae
    refine ⟨contMDiffOn_const.memWkpLocMapOn (n := 1) le_rfl hs, fun φ hφ ψ hψ ↦ ?_⟩
    have hD : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ (fun _ : ℂ ↦ y) ⁻¹' ψ.source)) :=
      φ.isOpen_inter_preimage_symm (continuousOn_const.isOpen_inter_preimage hs ψ.open_source)
    refine (isWeakCauchyRiemannOn_const_iff (ψ y)).2 ?_
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
    refine (InhomogeneousTerm.chartTerm_apply_eq_zero_iff ν φ hψ hzD.2.2 z).2
      (DFunLike.congr_fun ((ν.tangentHom_eq_zero_iff_apply_one_eq_zero _).2 ?_) _)
    by_contra hne
    exact hz ⟨φ.symm z, ⟨⟨hzD.2.1, hne⟩, φ.map_target hzD.1⟩, φ.right_inv hzD.1⟩

end Plane

end TauCeti
