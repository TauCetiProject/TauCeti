/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Cones
public import TauCeti.Algebra.Module.FiltrationLevel

/-!
# Spectral invariants of filtered complexes

A real filtration of a complex of modules `C` is a functor `F : ℝ ⥤ HomologicalComplex` with a
cocone `s` whose point is `C`: the stage `F a` maps to `C`, compatibly with the transition maps
`F a ⟶ F b` for `a ≤ b`. For a Floer complex, `F a` is the subcomplex spanned by the periodic
orbits of action at most `a`. The **homology filtration** of `Hᵢ(C)`
(`TauCeti.homologyFiltration`) is the increasing family of submodules

`a ↦ im (Hᵢ(F a) → Hᵢ(C))`,

and the **spectral invariant** of a class `σ ∈ Hᵢ(C)` is its filtration level
`ρ(σ) = TauCeti.filtrationLevel (homologyFiltration s i) σ`: the infimum of the levels `a` at which
`σ` comes from the homology of `F a`.

This file proves the properties of spectral invariants that only involve the filtered complexes:

* **Filtered maps.** A chain map `φ : C ⟶ D` which is induced on each stage by maps
  `F a ⟶ G (a + δ)` raises spectral invariants by at most `δ`
  (`TauCeti.filtrationLevel_homologyFiltration_homologyMap_le_add`), and does not raise them when
  it preserves the stages (`TauCeti.filtrationLevel_homologyFiltration_homologyMap_le`). For
  continuation maps of Floer complexes, these give the Lipschitz continuity of spectral invariants
  in the Hamiltonian and their monotonicity along monotone homotopies.
* **Spectrality.** If the transition maps `F a ⟶ F b` are quasi-isomorphisms whenever `[a, b]`
  does not meet a closed set `S`, the homology of some stage vanishes and some stage computes the
  homology of `C`, then the spectral invariant of every nonzero class is a real number in `S`
  (`TauCeti.exists_mem_filtrationLevel_homologyFiltration_eq`). If `S` is moreover discrete and
  the transitions are quasi-isomorphisms as soon as `(a, b]` does not meet `S`, as for sublevels of
  the action of finitely many orbits, the class comes from the stage at its spectral invariant
  (`TauCeti.mem_homologyFiltration_of_filtrationLevel_eq`).

## Main definitions

* `TauCeti.homologyFiltration s i`: the images of the homology of the stages of a filtered
  complex in its homology.

## References

* M. Usher, *Spectral numbers in Floer theories*, Compositio Math. 144 (2008), 1581–1592.
* M. Schwarz, *On the action spectrum for closed symplectically aspherical manifolds*,
  Pacific J. Math. 193 (2000), 419–461.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1.
-/

public section

open CategoryTheory Limits Filter Set

namespace TauCeti

universe v u w

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {F G : ℝ ⥤ HomologicalComplex (ModuleCat.{v} R) c} (s : Cocone F) (t : Cocone G) (i : ι)

/-- The homology filtration of a filtered complex: the image in `Hᵢ` of the point of the cocone
`s` of the homology of the stage `F a`. -/
noncomputable def homologyFiltration (a : ℝ) : Submodule R (s.pt.homology i) :=
  LinearMap.range (HomologicalComplex.homologyMap (s.ι.app a) i).hom

variable {s t i}

theorem mem_homologyFiltration_iff {a : ℝ} {σ : s.pt.homology i} :
    σ ∈ homologyFiltration s i a ↔
      ∃ τ, (HomologicalComplex.homologyMap (s.ι.app a) i).hom τ = σ :=
  LinearMap.mem_range

theorem homologyMap_mem_homologyFiltration (a : ℝ) (τ : (F.obj a).homology i) :
    (HomologicalComplex.homologyMap (s.ι.app a) i).hom τ ∈ homologyFiltration s i a :=
  LinearMap.mem_range_self _ τ

variable (s i) in
theorem homologyFiltration_mono : Monotone (homologyFiltration s i) := by
  intro a b hab σ hσ
  obtain ⟨τ, rfl⟩ := mem_homologyFiltration_iff.mp hσ
  refine mem_homologyFiltration_iff.mpr
    ⟨(HomologicalComplex.homologyMap (F.map (homOfLE hab)) i).hom τ, ?_⟩
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    s.w]

/-- Where the transition map `F a ⟶ F b` is a quasi-isomorphism, the homology filtration does not
grow between `a` and `b`. -/
theorem homologyFiltration_le_of_quasiIsoAt {a b : ℝ} (hab : a ≤ b)
    (h : QuasiIsoAt (F.map (homOfLE hab)) i) :
    homologyFiltration s i b ≤ homologyFiltration s i a := by
  intro σ hσ
  obtain ⟨τ, rfl⟩ := mem_homologyFiltration_iff.mp hσ
  have := (quasiIsoAt_iff_isIso_homologyMap _ _).mp h
  obtain ⟨τ', rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (F.map (homOfLE hab)) i)).2 τ
  refine mem_homologyFiltration_iff.mpr ⟨τ', ?_⟩
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    s.w]

/-- A stage which computes the homology of the complex contains every class. -/
theorem homologyFiltration_eq_top_of_quasiIsoAt {a : ℝ} (h : QuasiIsoAt (s.ι.app a) i) :
    homologyFiltration s i a = ⊤ := by
  have := (quasiIsoAt_iff_isIso_homologyMap _ _).mp h
  exact LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (s.ι.app a) i)).2

/-- A stage with vanishing homology contributes no class. -/
theorem homologyFiltration_eq_bot_of_isZero {a : ℝ} (h : IsZero ((F.obj a).homology i)) :
    homologyFiltration s i a = ⊥ := by
  have := ModuleCat.subsingleton_of_isZero h
  exact LinearMap.range_eq_bot.mpr (LinearMap.ext fun τ ↦ by simp [Subsingleton.elim τ 0])

/-- A chain map which is induced on each stage by maps `F a ⟶ G (e a)` sends the stage `a` of the
homology filtration into the stage `e a`. -/
theorem map_homologyFiltration_le {φ : s.pt ⟶ t.pt} {e : ℝ → ℝ}
    (ψ : ∀ a, F.obj a ⟶ G.obj (e a)) (hψ : ∀ a, ψ a ≫ t.ι.app (e a) = s.ι.app a ≫ φ)
    (a : ℝ) :
    (homologyFiltration s i a).map (HomologicalComplex.homologyMap φ i).hom ≤
      homologyFiltration t i (e a) := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, rfl⟩ := mem_homologyFiltration_iff.mp hσ
  refine mem_homologyFiltration_iff.mpr ⟨(HomologicalComplex.homologyMap (ψ a) i).hom τ, ?_⟩
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    hψ]

/-- **Filtered maps with shift `δ`.** A chain map which is induced on each stage by maps
`F a ⟶ G (a + δ)` raises spectral invariants by at most `δ`. -/
theorem filtrationLevel_homologyFiltration_homologyMap_le_add {φ : s.pt ⟶ t.pt} (δ : ℝ)
    (ψ : ∀ a, F.obj a ⟶ G.obj (a + δ)) (hψ : ∀ a, ψ a ≫ t.ι.app (a + δ) = s.ι.app a ≫ φ)
    (σ : s.pt.homology i) :
    filtrationLevel (homologyFiltration t i) ((HomologicalComplex.homologyMap φ i).hom σ) ≤
      filtrationLevel (homologyFiltration s i) σ + δ :=
  filtrationLevel_map_le_add _ δ (map_homologyFiltration_le (e := (· + δ)) ψ hψ) σ

/-- **Filtered maps.** A chain map which is induced on each stage by maps `F a ⟶ G a` does not
raise spectral invariants. -/
theorem filtrationLevel_homologyFiltration_homologyMap_le {φ : s.pt ⟶ t.pt}
    (ψ : ∀ a, F.obj a ⟶ G.obj a) (hψ : ∀ a, ψ a ≫ t.ι.app a = s.ι.app a ≫ φ)
    (σ : s.pt.homology i) :
    filtrationLevel (homologyFiltration t i) ((HomologicalComplex.homologyMap φ i).hom σ) ≤
      filtrationLevel (homologyFiltration s i) σ :=
  filtrationLevel_map_le _ (map_homologyFiltration_le (e := fun a ↦ a) ψ hψ) σ

/-- **Spectrality.** Suppose that the transition maps `F a ⟶ F b` are quasi-isomorphisms in
degree `i` whenever `[a, b]` does not meet the closed set `S`, that some stage has vanishing
homology and that some stage computes the homology of the complex. Then the spectral invariant
of a nonzero class is a real number in `S`. -/
theorem exists_mem_filtrationLevel_homologyFiltration_eq {S : Set ℝ} (hS : IsClosed S)
    (hFS : ∀ a b (hab : a ≤ b), Disjoint S (Icc a b) → QuasiIsoAt (F.map (homOfLE hab)) i)
    {a b : ℝ} (ha : IsZero ((F.obj a).homology i)) (hb : QuasiIsoAt (s.ι.app b) i)
    {σ : s.pt.homology i} (hσ : σ ≠ 0) :
    ∃ r ∈ S, filtrationLevel (homologyFiltration s i) σ = r :=
  exists_mem_filtrationLevel_eq (homologyFiltration_mono s i) hS
    (fun _ _ hab hdisj ↦ homologyFiltration_le_of_quasiIsoAt hab (hFS _ _ hab hdisj))
    (homologyFiltration_eq_bot_of_isZero ha)
    (homologyFiltration_eq_top_of_quasiIsoAt hb ▸ Submodule.mem_top) hσ

/-- If the transition maps `F a ⟶ F b` are quasi-isomorphisms in degree `i` whenever `(a, b]`
does not meet the closed discrete set `S`, then a class with finite spectral invariant `r` comes
from the homology of the stage `F r`. -/
theorem mem_homologyFiltration_of_filtrationLevel_eq {S : Set ℝ} (hS : Sᶜ ∈ codiscrete ℝ)
    (hFS : ∀ a b (hab : a ≤ b), Disjoint S (Ioc a b) → QuasiIsoAt (F.map (homOfLE hab)) i)
    {σ : s.pt.homology i} {r : ℝ} (hr : filtrationLevel (homologyFiltration s i) σ = r) :
    σ ∈ homologyFiltration s i r :=
  mem_of_filtrationLevel_eq hS
    (fun _ _ hab hdisj ↦ homologyFiltration_le_of_quasiIsoAt hab (hFS _ _ hab hdisj)) hr

end TauCeti
