/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Local Sobolev maps from a Riemann surface into a manifold

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, and let `M` be a smooth manifold modelled on a real normed space
`F`. A map `u : X → M` lies in the local Sobolev class `W^{k,p}_loc(X, M)`
(`TauCeti.MemWkpLocMap F p k u`) when it is continuous and every coordinate expression
`ψ ∘ u ∘ φ.symm` belongs to the planar local Sobolev class `TauCeti.MemWkpLoc p _ k` on the open
part of the target of `φ` where `u` maps into the source of `ψ`. Here `φ` runs over all
holomorphic charts of `X`, the charts of the maximal atlas of `𝓘(ℂ)`, and `ψ` over all charts of
the maximal smooth atlas of `M`. The holomorphic charts serve as the isothermal charts of `X`;
for a surface given instead by a smooth almost complex structure `j`, the comparison of its
isothermal charts with a holomorphic atlas (for which `j` is
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`) transfers the definition.

The relative version `TauCeti.MemWkpLocMapOn F p k u s` asks for continuity on `s` and tests the
coordinate expressions on the part of each chart target lying over `s`; it is intended for open
sets `s`, where it is the class of the open subsurface `s`.

The class is meant for `k ≥ 1` and `k p > 2`. Then continuity of a Sobolev map is automatic
(Morrey), so requiring it does not change the class, and it makes the domains of the coordinate
expressions open. The definition is stated for all parameters; for `k p ≤ 2` it is the smaller
class of continuous maps with Sobolev coordinate expressions.

## Main declarations

* `TauCeti.MemWkpLocMapOn`, `TauCeti.MemWkpLocMap`: local Sobolev maps on a subset and on the
  whole surface.
* `TauCeti.MemWkpLocMapOn.mono`: restriction to a smaller set, in particular to an open subset.
* `TauCeti.MemWkpLocMapOn.of_le`, `TauCeti.MemWkpLocMapOn.mono_exponent`: decreasing the
  derivative order or the integrability exponent.
* `ContMDiffOn.memWkpLocMapOn`, `ContMDiff.memWkpLocMap`: `C^k` maps belong to the class of
  order `k`, for every exponent.
* `TauCeti.memWkpLocMap_id_complex`, `Differentiable.memWkpLocMap`,
  `DifferentiableOn.memWkpLocMapOn`: for `X = M = ℂ`, the identity and every holomorphic function
  belong to the class for every `k` and `p`.

## Implementation notes

The charts tested are those of the maximal atlases, so the definition does not depend on the
chosen atlases. That it suffices to test one atlas of each, composition with `C^ℓ` maps of `M`
and the weak differential of a Sobolev map need the change-of-variables and chain rules for
planar local Sobolev classes, and are not part of this file. Charts reaching the boundary of a
bordered surface are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
  {p q : ENNReal} {k l : ℕ} {u : X → M} {s t : Set X}

variable (F) in
/-- A map `u : X → M` from a Riemann surface is in the local Sobolev class `W^{k,p}_loc` on
`s ⊆ X` if it is continuous on `s` and, for every holomorphic chart `φ` of `X` and every smooth
chart `ψ` of `M`, the coordinate expression `ψ ∘ u ∘ φ.symm` is in the planar class
`MemWkpLoc p _ k` on the part of the target of `φ` over `s` where `u` maps into the source
of `ψ`. The definition is intended for open `s`. -/
def MemWkpLocMapOn (p : ENNReal) (k : ℕ) (u : X → M) (s : Set X) : Prop :=
  ContinuousOn u s ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ ∘ u ∘ φ.symm)

variable (F) in
/-- A map `u : X → M` from a Riemann surface is in the local Sobolev class `W^{k,p}_loc(X, M)`
if it is continuous and, for every holomorphic chart `φ` of `X` and every smooth chart `ψ` of
`M`, the coordinate expression `ψ ∘ u ∘ φ.symm` is in the planar class `MemWkpLoc p _ k` on the
open part of the target of `φ` where `u` maps into the source of `ψ`. -/
def MemWkpLocMap (p : ENNReal) (k : ℕ) (u : X → M) : Prop :=
  Continuous u ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ ∘ u ∘ φ.symm)

/-- On the whole surface, the relative class is the class of maps from the surface. -/
@[simp]
theorem memWkpLocMapOn_univ : MemWkpLocMapOn F p k u univ ↔ MemWkpLocMap F p k u := by
  simp only [MemWkpLocMapOn, MemWkpLocMap, continuousOn_univ, univ_inter]

/-- A local Sobolev map is a local Sobolev map on every subset. -/
theorem MemWkpLocMap.memWkpLocMapOn (hu : MemWkpLocMap F p k u) :
    MemWkpLocMapOn F p k u s := by
  rw [← memWkpLocMapOn_univ] at hu
  exact ⟨hu.1.mono (subset_univ s), fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ (subset_univ s))))⟩

/-- A local Sobolev map on `s` is continuous on `s`. -/
theorem MemWkpLocMapOn.continuousOn (hu : MemWkpLocMapOn F p k u s) : ContinuousOn u s := hu.1

/-- A local Sobolev map is continuous. -/
theorem MemWkpLocMap.continuous (hu : MemWkpLocMap F p k u) : Continuous u := hu.1

/-- Restriction to a smaller set, in particular to an open subset, preserves the class. -/
theorem MemWkpLocMapOn.mono (hu : MemWkpLocMapOn F p k u s) (hts : t ⊆ s) :
    MemWkpLocMapOn F p k u t :=
  ⟨hu.1.mono hts, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts)))⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLocMapOn.of_le (hu : MemWkpLocMapOn F p k u s) (hlk : l ≤ k) :
    MemWkpLocMapOn F p l u s :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).of_le hlk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLocMap.of_le (hu : MemWkpLocMap F p k u) (hlk : l ≤ k) : MemWkpLocMap F p l u :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).of_le hlk⟩

/-- Decreasing the integrability exponent preserves the class. -/
theorem MemWkpLocMapOn.mono_exponent (hu : MemWkpLocMapOn F p k u s) (hqp : q ≤ p) :
    MemWkpLocMapOn F q k u s :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono_exponent hqp⟩

/-- Decreasing the integrability exponent preserves the class. -/
theorem MemWkpLocMap.mono_exponent (hu : MemWkpLocMap F p k u) (hqp : q ≤ p) :
    MemWkpLocMap F q k u :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono_exponent hqp⟩

/-- A map that is `C^k` on an open set, for the real manifold structure underlying the Riemann
surface, is a local Sobolev map of order `k` on that set for every exponent. -/
theorem _root_.ContMDiffOn.memWkpLocMapOn [IsManifold 𝓘(ℂ) 1 X] [CompleteSpace F]
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) k u s) (hs : IsOpen s) :
    MemWkpLocMapOn F p k u s := by
  have : IsManifold 𝓘(ℝ, ℂ) k X := IsManifold.restrictScalars_of_ne_zero k one_ne_zero ‹_›
  refine ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  have hV : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    φ.isOpen_inter_preimage_symm (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have hφ' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) k φ.symm φ.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero _ one_ne_zero hφ)
  have hψ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) k ψ ψ.source :=
    (contMDiffOn_of_mem_maximalAtlas hψ).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) k (ψ ∘ u ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    hψ'.comp (hu.comp (hφ'.mono inter_subset_left) fun _ hz ↦ hz.2.1) fun _ hz ↦ hz.2.2
  exact (contMDiffOn_iff_contDiffOn.mp hcomp).memWkpLoc (Ω := ⟨_, hV⟩) subset_rfl

/-- A `C^k` map, for the real manifold structure underlying the Riemann surface, is a local
Sobolev map of order `k` for every exponent. -/
theorem _root_.ContMDiff.memWkpLocMap [IsManifold 𝓘(ℂ) 1 X] [CompleteSpace F]
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, F) k u) : MemWkpLocMap F p k u :=
  memWkpLocMapOn_univ.mp (hu.contMDiffOn.memWkpLocMapOn isOpen_univ)

/-! ### Checks on the plane -/

/-- For `X = M = ℂ`, the identity is a local Sobolev map for every order and exponent. -/
theorem memWkpLocMap_id_complex : MemWkpLocMap ℂ p k (id : ℂ → ℂ) :=
  contMDiff_id.memWkpLocMap

/-- For `X = M = ℂ`, every entire function is a local Sobolev map for every order and
exponent. -/
theorem _root_.Differentiable.memWkpLocMap {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    MemWkpLocMap ℂ p k f :=
  ((hf.contDiff (n := k)).restrict_scalars ℝ).contMDiff.memWkpLocMap

/-- For `X = M = ℂ`, a function holomorphic on an open set is a local Sobolev map on that set for
every order and exponent. -/
theorem _root_.DifferentiableOn.memWkpLocMapOn {f : ℂ → ℂ} {s : Set ℂ}
    (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) : MemWkpLocMapOn ℂ p k f s :=
  (contMDiffOn_iff_contDiffOn.mpr
    ((hf.contDiffOn (n := k) hs).restrict_scalars ℝ)).memWkpLocMapOn hs

end TauCeti
