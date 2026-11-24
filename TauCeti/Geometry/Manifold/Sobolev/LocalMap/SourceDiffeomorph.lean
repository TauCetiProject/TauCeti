/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import TauCeti.Geometry.Manifold.Diffeomorph.MaximalAtlas

/-!
# Local Sobolev maps under structomorphisms of the source

Let `G` be a structure groupoid on a model `H'` read in `ℂ` through a model `J`, such as the
holomorphic groupoid of Riemann surfaces or the bordered holomorphic groupoid of Riemann surfaces
with boundary, and let `e : X' → X` be a `G`-structomorphism. A map `u : X → M` is in the local
Sobolev class `W^{k,p}_loc` on `s ⊆ X` for `G` exactly when `u ∘ e` is in it on `e ⁻¹' s`, for
every order `k` and exponent `p` (`Structomorph.memWkpLocMapOnGroupoid_comp_iff`). For Riemann
surfaces without boundary the same holds for a biholomorphism given as a `C^n` diffeomorphism for
the models `𝓘(ℂ)` with `1 ≤ n` (`Diffeomorph.memWkpLocMapOn_comp_diffeomorph_iff`).

No change of variables is involved: the class tests every chart of the maximal atlas, and the
charts of the maximal atlas of `X'` are exactly the charts `e ≫ φ` for charts `φ` of the maximal
atlas of `X`. In such a pair of charts the coordinate expressions of `u` and of `u ∘ e` are the same
map on the same set (`TauCeti.MemWkpLocMapOnGroupoid.comp_of_forall_mem_maximalAtlas`).
Composition on the target side is `Diffeomorph.memWkpLocMapOnGroupoid_diffeomorph_comp_iff`.

## Main results

* `TauCeti.MemWkpLocMapOnGroupoid.comp_of_forall_mem_maximalAtlas`: precomposition with a map
  matching the charts of the two maximal atlases preserves the class.
* `TauCeti.MemWkpLocMapOnGroupoid.comp_structomorph`,
  `TauCeti.MemWkpLocMapGroupoid.comp_structomorph`,
  `Structomorph.memWkpLocMapOnGroupoid_comp_iff`, `Structomorph.memWkpLocMapGroupoid_comp_iff`:
  invariance under structomorphisms of the source.
* `TauCeti.MemWkpLocMapOn.comp_diffeomorph`, `TauCeti.MemWkpLocMap.comp_diffeomorph`,
  `Diffeomorph.memWkpLocMapOn_comp_diffeomorph_iff`,
  `Diffeomorph.memWkpLocMap_comp_diffeomorph_iff`: invariance under biholomorphisms of Riemann
  surfaces without boundary.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

section Groupoid

variable {H' : Type*} [TopologicalSpace H'] {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace H' X']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-- **Chart reindexing.** Let `g : X' → X` be continuous and such that every chart `φ'` of the
maximal `G`-atlas of `X'` has a chart `φ` of the maximal `G`-atlas of `X` with the same target and
with `φ⁻¹ = g ∘ φ'⁻¹`. If `u` is a local Sobolev map on `s`, then `u ∘ g` is one on `g ⁻¹' s`, of
the same order and exponent: in `φ'` it reads as `u` reads in `φ`. -/
theorem MemWkpLocMapOnGroupoid.comp_of_forall_mem_maximalAtlas
    (hu : MemWkpLocMapOnGroupoid G J I p k u s) {g : X' → X} (hg : Continuous g)
    (hchart : ∀ φ' ∈ G.maximalAtlas X', ∃ φ ∈ G.maximalAtlas X,
      φ.target = φ'.target ∧ φ.symm = g ∘ φ'.symm) :
    MemWkpLocMapOnGroupoid G J I p k (u ∘ g) (g ⁻¹' s) := by
  refine memWkpLocMapOnGroupoid_iff.2
    ⟨hu.continuousOn.comp hg.continuousOn (mapsTo_preimage _ _), fun φ' hφ' ψ hψ ↦ ?_⟩
  obtain ⟨φ, hφ, htarget, hsymm⟩ := hchart φ' hφ'
  have ht : (φ.extend J).target = (φ'.extend J).target := by
    rw [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.extend_target, htarget]
  have hs : ⇑(φ.extend J).symm = g ∘ (φ'.extend J).symm := by
    rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe_symm, hsymm]
    rfl
  have h := hu.memWkpLoc_chart hφ hψ
  rw [ht, hs] at h
  exact h

/-- **Precomposition with a structomorphism.** If `u` is a local Sobolev map on `s` for `G` and
`e : X' → X` is a `G`-structomorphism, then `u ∘ e` is one on `e ⁻¹' s`, of the same order and
exponent. -/
theorem MemWkpLocMapOnGroupoid.comp_structomorph (hu : MemWkpLocMapOnGroupoid G J I p k u s)
    (e : Structomorph G X' X) :
    MemWkpLocMapOnGroupoid G J I p k (u ∘ e.toHomeomorph) (e.toHomeomorph ⁻¹' s) :=
  hu.comp_of_forall_mem_maximalAtlas e.toHomeomorph.continuous fun _ hφ' ↦
    e.exists_mem_maximalAtlas_symm_eq_comp hφ'

/-- **Precomposition with a structomorphism.** If `u` is a local Sobolev map for `G` and
`e : X' → X` is a `G`-structomorphism, then `u ∘ e` is one, of the same order and exponent. -/
theorem MemWkpLocMapGroupoid.comp_structomorph {u : X → M}
    (hu : MemWkpLocMapGroupoid G J I p k u) (e : Structomorph G X' X) :
    MemWkpLocMapGroupoid G J I p k (u ∘ e.toHomeomorph) := by
  simpa only [preimage_univ, memWkpLocMapOnGroupoid_univ] using
    (memWkpLocMapOnGroupoid_univ.2 hu).comp_structomorph e

end Groupoid

end TauCeti

namespace Structomorph

open TauCeti

variable {H' : Type*} [TopologicalSpace H'] {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace H' X']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-- **Invariance under structomorphisms of the source.** For a `G`-structomorphism `e : X' → X`, a
map `u : X → M` is a local Sobolev map on `s` for `G` exactly when `u ∘ e` is one on `e ⁻¹' s`, for
every order `k` and exponent `p`. -/
theorem memWkpLocMapOnGroupoid_comp_iff (e : Structomorph G X' X) :
    MemWkpLocMapOnGroupoid G J I p k (u ∘ e.toHomeomorph) (e.toHomeomorph ⁻¹' s) ↔
      MemWkpLocMapOnGroupoid G J I p k u s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_structomorph e⟩
  have h' := h.comp_structomorph e.symm
  have hu : (u ∘ e.toHomeomorph) ∘ e.symm.toHomeomorph = u :=
    funext fun x ↦ by simp
  have hs : e.symm.toHomeomorph ⁻¹' (e.toHomeomorph ⁻¹' s) = s :=
    ext fun x ↦ by simp
  rwa [hu, hs] at h'

/-- **Invariance under structomorphisms of the source.** For a `G`-structomorphism `e : X' → X`, a
map `u : X → M` is a local Sobolev map for `G` exactly when `u ∘ e` is one, for every order `k` and
exponent `p`. -/
theorem memWkpLocMapGroupoid_comp_iff (e : Structomorph G X' X) :
    MemWkpLocMapGroupoid G J I p k (u ∘ e.toHomeomorph) ↔ MemWkpLocMapGroupoid G J I p k u := by
  simpa only [preimage_univ, memWkpLocMapOnGroupoid_univ] using
    e.memWkpLocMapOnGroupoid_comp_iff (J := J) (I := I) (p := p) (k := k) (u := u) (s := univ)

end Structomorph

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace ℂ X']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X} {n : WithTop ℕ∞}

/-- **Precomposition with a biholomorphism.** If `u` is a local Sobolev map on `s` and
`f : X' → X` is a biholomorphism, then `u ∘ f` is a local Sobolev map on `f ⁻¹' s`, of the same
order and exponent. -/
theorem MemWkpLocMapOn.comp_diffeomorph (hu : MemWkpLocMapOn I p k u s)
    (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) : MemWkpLocMapOn I p k (u ∘ f) (f ⁻¹' s) :=
  hu.comp_of_forall_mem_maximalAtlas f.continuous fun _ hφ' ↦
    f.exists_mem_maximalAtlas_symm_eq_comp hn hφ'

/-- **Precomposition with a biholomorphism.** If `u` is a local Sobolev map and `f : X' → X` is a
biholomorphism, then `u ∘ f` is a local Sobolev map of the same order and exponent. -/
theorem MemWkpLocMap.comp_diffeomorph (hu : MemWkpLocMap I p k u)
    (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) : MemWkpLocMap I p k (u ∘ f) := by
  have h : MemWkpLocMapOn I p k u univ := memWkpLocMapOnGroupoid_univ.2 hu
  simpa only [preimage_univ, memWkpLocMapOnGroupoid_univ] using h.comp_diffeomorph f hn

end TauCeti

namespace Diffeomorph

open TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) 1 X']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X} {n : WithTop ℕ∞}

/-- **Invariance under biholomorphisms of the source.** For a biholomorphism `f : X' → X`, a map
`u : X → M` is a local Sobolev map on `s` exactly when `u ∘ f` is one on `f ⁻¹' s`, for every
order `k` and exponent `p`. -/
theorem memWkpLocMapOn_comp_diffeomorph_iff (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    MemWkpLocMapOn I p k (u ∘ f) (f ⁻¹' s) ↔ MemWkpLocMapOn I p k u s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_diffeomorph f hn⟩
  simpa [Function.comp_def, preimage_preimage] using h.comp_diffeomorph f.symm hn

/-- **Invariance under biholomorphisms of the source.** For a biholomorphism `f : X' → X`, a map
`u : X → M` is a local Sobolev map exactly when `u ∘ f` is one, for every order `k` and exponent
`p`. -/
theorem memWkpLocMap_comp_diffeomorph_iff (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    MemWkpLocMap I p k (u ∘ f) ↔ MemWkpLocMap I p k u := by
  simpa only [preimage_univ, memWkpLocMapOnGroupoid_univ] using
    f.memWkpLocMapOn_comp_diffeomorph_iff (I := I) (p := p) (k := k) (u := u) (s := univ) hn

end Diffeomorph
