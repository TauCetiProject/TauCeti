/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Local Sobolev maps from a Riemann surface into a manifold

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, and let `M` be a smooth manifold modelled on
`I : ModelWithCorners ℝ F H`, where `F` is a real Banach space. A map `u : X → M` lies in the
local Sobolev class `W^{k,p}_loc(X, M)` (`TauCeti.MemWkpLocMap I p k u`) when it is continuous and
every coordinate expression `ψ.extend I ∘ u ∘ φ.symm` belongs to the planar local Sobolev class
`TauCeti.MemWkpLoc p _ k` on the open part of the target of `φ` where `u` maps into the source of
`ψ`. Here `φ` runs over all holomorphic charts of `X`, the charts of the maximal atlas of `𝓘(ℂ)`,
and `ψ` over all charts of the maximal smooth atlas of `M`. The holomorphic charts serve as the
isothermal charts of `X`; for a surface given instead by a smooth almost complex structure `j`,
the comparison of its isothermal charts with a holomorphic atlas (for which `j` is
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`) transfers the definition.

The relative version `TauCeti.MemWkpLocMapOn I p k u s` asks for continuity on `s` and tests the
coordinate expressions on the part of each chart target lying over `s`; it is intended for open
sets `s`, where it is the class of the open subsurface `s`.

Both are instances of `TauCeti.MemWkpLocMapOnGroupoid G J I p k u s` and
`TauCeti.MemWkpLocMapGroupoid G J I p k u`, which test the charts of the maximal atlas of a
structure groupoid `G` on a model space `H'`, read in `ℂ` through a model
`J : ModelWithCorners ℝ ℂ H'`. Riemann surfaces without boundary use the holomorphic groupoid and
`J = 𝓘(ℝ, ℂ)`; Riemann surfaces with boundary use the bordered holomorphic groupoid and the closed
upper half-plane (`TauCeti.MemWkpLocMapOnBordered`).

The class is meant for `k ≥ 1` and `k p > 2`. Then continuity of a Sobolev map is automatic
(Morrey), so requiring it does not change the class, and it makes the domains of the coordinate
expressions open. The definition is stated for all parameters; for `k p ≤ 2` it is the smaller
class of continuous maps with Sobolev coordinate expressions.

## Main declarations

* `TauCeti.MemWkpLocMapOnGroupoid`, `TauCeti.MemWkpLocMapGroupoid`: local Sobolev maps on a
  subset and on the whole surface, tested in the charts of a structure groupoid.
* `TauCeti.MemWkpLocMapOn`, `TauCeti.MemWkpLocMap`: local Sobolev maps from a Riemann surface on a
  subset and on the whole surface.
* `TauCeti.MemWkpLocMapOnGroupoid.mono`: restriction to a smaller set, in particular to an open
  subset.
* `TauCeti.MemWkpLocMapOnGroupoid.of_le`, `TauCeti.MemWkpLocMapOnGroupoid.mono_exponent`:
  decreasing the derivative order or the integrability exponent.
* `ContMDiffOn.memWkpLocMapOn`, `ContMDiff.memWkpLocMap`: `C^n` maps belong to the class of
  every order `k ≤ n`, for every exponent.
* `TauCeti.memWkpLocMapOn_iff`, `TauCeti.memWkpLocMap_iff`,
  `TauCeti.MemWkpLocMapOn.memWkpLoc_chart`, `TauCeti.MemWkpLocMap.memWkpLoc_chart`: unfolding the
  definitions and reading off the coordinate expressions in the charts of `X`.
* `MDifferentiableOn.memWkpLocMapOn`, `MDifferentiable.memWkpLocMap`: holomorphic maps from a
  Riemann surface into a complex manifold modelled on a complex Banach space belong to the class
  for every `k` and `p`.
* `TauCeti.memWkpLocMap_id_complex`: for `X = M = ℂ`, the identity belongs to the class for every
  `k` and `p`.
* `Differentiable.memWkpLocMap`, `DifferentiableOn.memWkpLocMapOn`: for `X = ℂ` and `M` a complex
  Banach space, every holomorphic function belongs to the class for every `k` and `p`.

## Implementation notes

The charts tested are those of the maximal atlases, so the definition does not depend on the
chosen atlases. As for `ContMDiff`, the definitions carry no manifold hypotheses: they are meant
for `IsManifold 𝓘(ℂ) 1 X` and `IsManifold I ∞ M`, under which the maximal atlases contain the
given charts and so cover `X` and `M`. For charted spaces with incompatible charts they need not
cover, and the coordinate tests can be vacuous. Likewise the definitions do not assume
`CompleteSpace F`, but at positive orders the class inherits it from the weak derivatives of
`TauCeti.MemWkpLoc` (`TauCeti.MemWkpLoc.completeSpace`), so for incomplete `F` it contains no map
from a nonempty surface. That it suffices to test one atlas of each,
composition with `C^ℓ` maps of `M` and the weak differential of a Sobolev map need the
change-of-variables and chain rules for planar local Sobolev classes, and are not part of this
file. Charts reaching the boundary of a bordered surface are treated in
`TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

/-! ### Local Sobolev maps tested in the charts of a structure groupoid -/

section Groupoid

variable {H' : Type*} [TopologicalSpace H'] {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p q : ENNReal} {k l : ℕ} {u : X → M} {s t : Set X}

variable (G J I) in
/-- A map `u : X → M` from a surface modelled on `H'`, read in `ℂ` through the model `J`, is in
the local Sobolev class `W^{k,p}_loc` on `s ⊆ X` for the structure groupoid `G` if it is
continuous on `s` and, for every chart `φ` of the maximal atlas of `G` and every smooth chart `ψ`
of `M`, the coordinate expression `ψ.extend I ∘ u ∘ (φ.extend J).symm` is in the planar class
`MemWkpLoc p _ k` on the part of the extended target of `φ` over `s` where `u` maps into the
source of `ψ`. The definition is intended for open `s`. -/
def MemWkpLocMapOnGroupoid (p : ENNReal) (k : ℕ) (u : X → M) (s : Set X) : Prop :=
  ContinuousOn u s ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend J).symm)

variable (G J I) in
/-- A map `u : X → M` from a surface modelled on `H'`, read in `ℂ` through the model `J`, is in
the local Sobolev class `W^{k,p}_loc(X, M)` for the structure groupoid `G` if it is continuous
and, for every chart `φ` of the maximal atlas of `G` and every smooth chart `ψ` of `M`, the
coordinate expression `ψ.extend I ∘ u ∘ (φ.extend J).symm` is in the planar class
`MemWkpLoc p _ k` on the part of the extended target of `φ` where `u` maps into the source
of `ψ`. -/
def MemWkpLocMapGroupoid (p : ENNReal) (k : ℕ) (u : X → M) : Prop :=
  Continuous u ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend J).symm)

/-- Unfolding the definition of the relative local Sobolev class for a structure groupoid. -/
theorem memWkpLocMapOnGroupoid_iff : MemWkpLocMapOnGroupoid G J I p k u s ↔ ContinuousOn u s ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) :=
  Iff.rfl

/-- Unfolding the definition of the local Sobolev class for a structure groupoid. -/
theorem memWkpLocMapGroupoid_iff : MemWkpLocMapGroupoid G J I p k u ↔ Continuous u ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) :=
  Iff.rfl

/-- The coordinate expression of a local Sobolev map on `s` in a chart `φ` of the maximal atlas of
`G` and a smooth chart `ψ` is in the planar class on the part of the extended target of `φ` over
`s` where `u` maps into the source of `ψ`. -/
theorem MemWkpLocMapOnGroupoid.memWkpLoc_chart (hu : MemWkpLocMapOnGroupoid G J I p k u s)
    {φ : OpenPartialHomeomorph X H'} (hφ : φ ∈ G.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemWkpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) :=
  hu.2 φ hφ ψ hψ

/-- The coordinate expression of a local Sobolev map in a chart `φ` of the maximal atlas of `G`
and a smooth chart `ψ` is in the planar class on the part of the extended target of `φ` where `u`
maps into the source of `ψ`. -/
theorem MemWkpLocMapGroupoid.memWkpLoc_chart (hu : MemWkpLocMapGroupoid G J I p k u)
    {φ : OpenPartialHomeomorph X H'} (hφ : φ ∈ G.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemWkpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)) k
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) :=
  hu.2 φ hφ ψ hψ

/-- On the whole surface, the relative class is the class of maps from the surface. -/
@[simp]
theorem memWkpLocMapOnGroupoid_univ :
    MemWkpLocMapOnGroupoid G J I p k u univ ↔ MemWkpLocMapGroupoid G J I p k u := by
  simp only [MemWkpLocMapOnGroupoid, MemWkpLocMapGroupoid, continuousOn_univ, univ_inter]

/-- A local Sobolev map on `s` is continuous on `s`. -/
theorem MemWkpLocMapOnGroupoid.continuousOn (hu : MemWkpLocMapOnGroupoid G J I p k u s) :
    ContinuousOn u s :=
  hu.1

/-- A local Sobolev map is continuous. -/
theorem MemWkpLocMapGroupoid.continuous (hu : MemWkpLocMapGroupoid G J I p k u) : Continuous u :=
  hu.1

/-- Restriction to a smaller set, in particular to an open subset, preserves the class. -/
theorem MemWkpLocMapOnGroupoid.mono (hu : MemWkpLocMapOnGroupoid G J I p k u s) (hts : t ⊆ s) :
    MemWkpLocMapOnGroupoid G J I p k u t :=
  ⟨hu.1.mono hts, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts)))⟩

/-- A local Sobolev map is a local Sobolev map on every subset. -/
theorem MemWkpLocMapGroupoid.memWkpLocMapOnGroupoid (hu : MemWkpLocMapGroupoid G J I p k u) :
    MemWkpLocMapOnGroupoid G J I p k u s :=
  (memWkpLocMapOnGroupoid_univ.mpr hu).mono (subset_univ s)

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLocMapOnGroupoid.of_le (hu : MemWkpLocMapOnGroupoid G J I p k u s) (hlk : l ≤ k) :
    MemWkpLocMapOnGroupoid G J I p l u s :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).of_le hlk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLocMapGroupoid.of_le (hu : MemWkpLocMapGroupoid G J I p k u) (hlk : l ≤ k) :
    MemWkpLocMapGroupoid G J I p l u :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).of_le hlk⟩

/-- Decreasing the integrability exponent preserves the class. -/
theorem MemWkpLocMapOnGroupoid.mono_exponent (hu : MemWkpLocMapOnGroupoid G J I p k u s)
    (hqp : q ≤ p) : MemWkpLocMapOnGroupoid G J I q k u s :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono_exponent hqp⟩

/-- Decreasing the integrability exponent preserves the class. -/
theorem MemWkpLocMapGroupoid.mono_exponent (hu : MemWkpLocMapGroupoid G J I p k u)
    (hqp : q ≤ p) : MemWkpLocMapGroupoid G J I q k u :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono_exponent hqp⟩

end Groupoid

/-! ### Riemann surfaces without boundary -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

variable (I) in
/-- A map `u : X → M` from a Riemann surface is in the local Sobolev class `W^{k,p}_loc` on
`s ⊆ X` if it is continuous on `s` and, for every holomorphic chart `φ` of `X` and every smooth
chart `ψ` of `M`, the coordinate expression `ψ.extend I ∘ u ∘ φ.symm` is in the planar class
`MemWkpLoc p _ k` on the part of the target of `φ` over `s` where `u` maps into the source
of `ψ` (`TauCeti.memWkpLocMapOn_iff`). It is the class `TauCeti.MemWkpLocMapOnGroupoid` for the
holomorphic groupoid, with charts read in `ℂ` through `𝓘(ℝ, ℂ)`. The definition is intended for
open `s`. -/
abbrev MemWkpLocMapOn (p : ENNReal) (k : ℕ) (u : X → M) (s : Set X) : Prop :=
  MemWkpLocMapOnGroupoid (contDiffGroupoid 1 𝓘(ℂ)) 𝓘(ℝ, ℂ) I p k u s

variable (I) in
/-- A map `u : X → M` from a Riemann surface is in the local Sobolev class `W^{k,p}_loc(X, M)`
if it is continuous and, for every holomorphic chart `φ` of `X` and every smooth chart `ψ` of
`M`, the coordinate expression `ψ.extend I ∘ u ∘ φ.symm` is in the planar class `MemWkpLoc p _ k`
on the open part of the target of `φ` where `u` maps into the source of `ψ`
(`TauCeti.memWkpLocMap_iff`). It is the class `TauCeti.MemWkpLocMapGroupoid` for the holomorphic
groupoid, with charts read in `ℂ` through `𝓘(ℝ, ℂ)`. -/
abbrev MemWkpLocMap (p : ENNReal) (k : ℕ) (u : X → M) : Prop :=
  MemWkpLocMapGroupoid (contDiffGroupoid 1 𝓘(ℂ)) 𝓘(ℝ, ℂ) I p k u

/-- Unfolding the definition of the relative local Sobolev class. -/
theorem memWkpLocMapOn_iff : MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  simp only [memWkpLocMapOnGroupoid_iff, IsManifold.maximalAtlas, mfld_simps]

/-- Unfolding the definition of the local Sobolev class. -/
theorem memWkpLocMap_iff : MemWkpLocMap I p k u ↔ Continuous u ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  simp only [memWkpLocMapGroupoid_iff, IsManifold.maximalAtlas, mfld_simps]

/-- The coordinate expression of a local Sobolev map on `s` in a holomorphic chart `φ` and a
smooth chart `ψ` is in the planar class on the part of the target of `φ` over `s` where `u` maps
into the source of `ψ`. -/
theorem MemWkpLocMapOn.memWkpLoc_chart (hu : MemWkpLocMapOn I p k u s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  (memWkpLocMapOn_iff.1 hu).2 φ hφ ψ hψ

/-- The coordinate expression of a local Sobolev map in a holomorphic chart `φ` and a smooth
chart `ψ` is in the planar class on the part of the target of `φ` where `u` maps into the source
of `ψ`. -/
theorem MemWkpLocMap.memWkpLoc_chart (hu : MemWkpLocMap I p k u) {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  (memWkpLocMap_iff.1 hu).2 φ hφ ψ hψ

/-- A map that is `C^n` on an open set, for the real manifold structure underlying the Riemann
surface and a manifold `M` modelled on a real Banach space, is a local Sobolev map on that set of
every order `k ≤ n` and every exponent. -/
theorem _root_.ContMDiffOn.memWkpLocMapOn [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s) (hk : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) :
    MemWkpLocMapOn I p k u s := by
  refine memWkpLocMapOn_iff.2 ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  have hV : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    φ.isOpen_inter_preimage_symm (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have hφ' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) k φ.symm φ.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero _ one_ne_zero hφ)
  have hψ' : ContMDiffOn I 𝓘(ℝ, F) k (ψ.extend I) ψ.source :=
    (ψ.contMDiffOn_extend hψ).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) k (ψ.extend I ∘ u ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    hψ'.comp ((hu.of_le hk).comp (hφ'.mono inter_subset_left) fun _ hz ↦ hz.2.1)
      fun _ hz ↦ hz.2.2
  exact (contMDiffOn_iff_contDiffOn.mp hcomp).memWkpLoc (Ω := ⟨_, hV⟩) subset_rfl

/-- A `C^n` map, for the real manifold structure underlying the Riemann surface and a manifold
`M` modelled on a real Banach space, is a local Sobolev map of every order `k ≤ n` and every
exponent. -/
theorem _root_.ContMDiff.memWkpLocMap [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I n u) (hk : (k : ℕ∞ω) ≤ n) : MemWkpLocMap I p k u :=
  memWkpLocMapOnGroupoid_univ.mp (hu.contMDiffOn.memWkpLocMapOn hk isOpen_univ)

/-! ### Holomorphic maps -/

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ E H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold 𝓘(ℂ) 1 X]
  [IsManifold I' 1 M'] {f : X → M'}

/-- A map from a Riemann surface into a complex manifold modelled on a complex Banach space which
is holomorphic on an open set is, for the underlying real model, a local Sobolev map on that set
for every order and exponent. -/
theorem _root_.MDifferentiableOn.memWkpLocMapOn (hf : MDifferentiableOn 𝓘(ℂ) I' f s)
    (hs : IsOpen s) : MemWkpLocMapOn (I'.restrictScalars ℝ) p k f s := by
  have hf' := (hf.contMDiffOn (n := k) hs).restrictScalars ℝ
  rw [modelWithCornersSelf_restrictScalars] at hf'
  exact hf'.memWkpLocMapOn le_rfl hs

/-- A holomorphic map from a Riemann surface into a complex manifold modelled on a complex Banach
space is, for the underlying real model, a local Sobolev map for every order and exponent. -/
theorem _root_.MDifferentiable.memWkpLocMap (hf : MDifferentiable 𝓘(ℂ) I' f) :
    MemWkpLocMap (I'.restrictScalars ℝ) p k f :=
  memWkpLocMapOnGroupoid_univ.mp (hf.mdifferentiableOn.memWkpLocMapOn isOpen_univ)

end Holomorphic

/-! ### Checks on the plane -/

/-- For `X = M = ℂ`, the identity is a local Sobolev map for every order and exponent. -/
theorem memWkpLocMap_id_complex : MemWkpLocMap 𝓘(ℝ, ℂ) p k (id : ℂ → ℂ) :=
  contMDiff_id.memWkpLocMap le_top

/-- For `X = ℂ` and `M` a complex Banach space, a function holomorphic on an open set is a local
Sobolev map on that set for every order and exponent. -/
theorem _root_.DifferentiableOn.memWkpLocMapOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {s : Set ℂ} (hf : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : MemWkpLocMapOn 𝓘(ℝ, E) p k f s := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    MDifferentiableOn.memWkpLocMapOn (p := p) (k := k) hf.mdifferentiableOn hs

/-- For `X = ℂ` and `M` a complex Banach space, every entire function is a local Sobolev map
for every order and exponent. -/
theorem _root_.Differentiable.memWkpLocMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) : MemWkpLocMap 𝓘(ℝ, E) p k f :=
  memWkpLocMapOnGroupoid_univ.mp (hf.differentiableOn.memWkpLocMapOn isOpen_univ)

end TauCeti
