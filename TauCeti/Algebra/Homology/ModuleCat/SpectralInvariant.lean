/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Cones
public import TauCeti.Algebra.Homology.SpectralInvariant

/-!
# Spectral invariants of filtered complexes

A filtration of a complex of modules `C`, indexed by a preorder `α`, is a functor
`F : α ⥤ HomologicalComplex` with a cocone `s` whose point is `C`: the stage `F a` maps to `C`,
compatibly with the transition maps `F a ⟶ F b` for `a ≤ b`. For a Floer complex, `α = ℝ` and
`F a` is the subcomplex spanned by the periodic orbits of action at most `a`; the stages need not
be subcomplexes of `C`, as for Floer complexes with DG coefficients. The **homology filtration** of
`Hᵢ(C)` (`CategoryTheory.Limits.Cocone.homologyFiltration`) is the increasing family of submodules

`a ↦ im (Hᵢ(F a) → Hᵢ(C))`,

and for `α = ℝ` the **spectral invariant** of a class `σ ∈ Hᵢ(C)` is
`ρ(σ) = TauCeti.spectralInvariant (s.homologyFiltration i) σ`: the infimum of the levels `a` at
which `σ` comes from the homology of `F a`.

This file proves the properties of spectral invariants that only involve the filtered complexes:

* **Filtered maps.** A chain map `φ : C ⟶ D` which is induced in homology by maps
  `F a ⟶ G (a + δ)` raises spectral invariants by at most `δ`
  (`TauCeti.spectralInvariant_homologyFiltration_homologyMap_le_add`), and does not raise them
  when it preserves the stages (`TauCeti.spectralInvariant_homologyFiltration_homologyMap_le`).
  Only the commutation of the squares in homology is assumed, so the squares may commute up to
  chain homotopy. For continuation maps of Floer complexes, these give the Lipschitz continuity of
  spectral invariants in the Hamiltonian and their monotonicity along monotone homotopies.
* **Spectrality.** If the transition maps `F a ⟶ F b` are surjective in homology whenever
  `[a, b]` does not meet a closed set `S`, then every finite spectral invariant lies in `S`
  (`TauCeti.mem_of_spectralInvariant_homologyFiltration_eq_coe_of_isClosed`); in particular so
  does the spectral invariant of a class which comes from some stage and not from another
  (`TauCeti.exists_mem_spectralInvariant_homologyFiltration_eq`). If `S` is moreover discrete and
  the transitions are surjective in homology as soon as `(a, b]` does not meet `S`, as for
  sublevels of the action of finitely many orbits, the class comes from the stage at its spectral
  invariant (`TauCeti.mem_homologyFiltration_of_spectralInvariant_eq_coe`).

## Main definitions

* `CategoryTheory.Limits.Cocone.homologyFiltration s i`: the images of the homology of the stages
  of a filtered complex in its homology.

## References

* M. Usher, *Spectral numbers in Floer theories*, Compositio Math. 144 (2008), 1581–1592.
* M. Schwarz, *On the action spectrum for closed symplectically aspherical manifolds*,
  Pacific J. Math. 193 (2000), 419–461.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1.
-/

public section

open CategoryTheory Limits Filter Set

universe v u w

namespace CategoryTheory.Limits.Cocone

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {α β : Type*} [Preorder α] [Preorder β]
  {F : α ⥤ HomologicalComplex (ModuleCat.{v} R) c} {G : β ⥤ HomologicalComplex (ModuleCat.{v} R) c}
  (s : Cocone F) (t : Cocone G) (i : ι)

/-- The homology filtration of a filtered complex: the image in `Hᵢ` of the point of the cocone
`s` of the homology of the stage `F a`. -/
noncomputable def homologyFiltration (a : α) : Submodule R (s.pt.homology i) :=
  LinearMap.range (HomologicalComplex.homologyMap (s.ι.app a) i).hom

/-- The compatibility `Cocone.w_apply` of a cocone, in homology: mapping a class of `Hᵢ(F a)`
to `Hᵢ(F b)` and then to the homology of the point is mapping it to the point directly. -/
@[simp]
theorem homologyMap_w_apply {a b : α} (f : a ⟶ b) (τ : (F.obj a).homology i) :
    (HomologicalComplex.homologyMap (L := s.pt) (s.ι.app b) i).hom
        ((HomologicalComplex.homologyMap (F.map f) i).hom τ) =
      (HomologicalComplex.homologyMap (s.ι.app a) i).hom τ := by
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    s.w]

variable {s t i}

theorem homologyFiltration_def {a : α} :
    s.homologyFiltration i a =
      LinearMap.range (HomologicalComplex.homologyMap (s.ι.app a) i).hom := by
  rw [homologyFiltration]

@[simp]
theorem mem_homologyFiltration_iff {a : α} {σ : s.pt.homology i} :
    σ ∈ s.homologyFiltration i a ↔
      ∃ τ, (HomologicalComplex.homologyMap (s.ι.app a) i).hom τ = σ := by
  rw [homologyFiltration_def, LinearMap.mem_range]

theorem homologyMap_mem_homologyFiltration (a : α) (τ : (F.obj a).homology i) :
    (HomologicalComplex.homologyMap (s.ι.app a) i).hom τ ∈ s.homologyFiltration i a :=
  mem_homologyFiltration_iff.mpr ⟨τ, rfl⟩

variable (s i) in
theorem homologyFiltration_mono : Monotone (s.homologyFiltration i) := by
  intro a b hab σ hσ
  obtain ⟨τ, rfl⟩ := mem_homologyFiltration_iff.mp hσ
  exact mem_homologyFiltration_iff.mpr ⟨_, s.homologyMap_w_apply i (homOfLE hab) τ⟩

/-- Where the transition map `F a ⟶ F b` is surjective in homology, the homology filtration does
not grow between `a` and `b`. -/
theorem homologyFiltration_le_of_epi {a b : α} (hab : a ≤ b)
    (h : Epi (HomologicalComplex.homologyMap (F.map (homOfLE hab)) i)) :
    s.homologyFiltration i b ≤ s.homologyFiltration i a := by
  intro σ hσ
  obtain ⟨τ, rfl⟩ := mem_homologyFiltration_iff.mp hσ
  obtain ⟨τ', rfl⟩ := (ModuleCat.epi_iff_surjective _).mp h τ
  exact mem_homologyFiltration_iff.mpr ⟨τ', (s.homologyMap_w_apply i (homOfLE hab) τ').symm⟩

/-- A stage contains every class exactly when its homology surjects onto that of the complex. -/
theorem homologyFiltration_eq_top_iff {a : α} :
    s.homologyFiltration i a = ⊤ ↔ Epi (HomologicalComplex.homologyMap (s.ι.app a) i) := by
  rw [homologyFiltration_def, ModuleCat.epi_iff_range_eq_top]

/-- A stage with vanishing homology contributes no class. -/
theorem homologyFiltration_eq_bot_of_isZero {a : α} (h : IsZero ((F.obj a).homology i)) :
    s.homologyFiltration i a = ⊥ := by
  have := ModuleCat.subsingleton_of_isZero h
  rw [homologyFiltration_def]
  exact LinearMap.range_eq_bot.mpr (LinearMap.ext fun τ ↦ by simp [Subsingleton.elim τ 0])

/-- A chain map which is induced in homology by maps `F a ⟶ G (e a)` sends the stage `a` of the
homology filtration into the stage `e a`. -/
theorem map_homologyFiltration_le {φ : s.pt ⟶ t.pt} {e : α → β}
    (ψ : ∀ a, F.obj a ⟶ G.obj (e a))
    (hψ : ∀ a, HomologicalComplex.homologyMap (ψ a) i ≫
        HomologicalComplex.homologyMap (t.ι.app (e a)) i =
      HomologicalComplex.homologyMap (s.ι.app a) i ≫ HomologicalComplex.homologyMap φ i)
    (a : α) :
    (s.homologyFiltration i a).map (HomologicalComplex.homologyMap φ i).hom ≤
      t.homologyFiltration i (e a) := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, rfl⟩ := mem_homologyFiltration_iff.mp hσ
  refine mem_homologyFiltration_iff.mpr ⟨(HomologicalComplex.homologyMap (ψ a) i).hom τ, ?_⟩
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hψ]

end CategoryTheory.Limits.Cocone

namespace TauCeti

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}

variable {F G : ℝ ⥤ HomologicalComplex (ModuleCat.{v} R) c} {s : Cocone F} {t : Cocone G} {i : ι}

/-- **Filtered maps with shift `δ`.** A chain map which is induced in homology by maps
`F a ⟶ G (a + δ)` raises spectral invariants by at most `δ`. -/
theorem spectralInvariant_homologyFiltration_homologyMap_le_add {φ : s.pt ⟶ t.pt} (δ : ℝ)
    (ψ : ∀ a, F.obj a ⟶ G.obj (a + δ))
    (hψ : ∀ a, HomologicalComplex.homologyMap (ψ a) i ≫
        HomologicalComplex.homologyMap (t.ι.app (a + δ)) i =
      HomologicalComplex.homologyMap (s.ι.app a) i ≫ HomologicalComplex.homologyMap φ i)
    (σ : s.pt.homology i) :
    spectralInvariant (t.homologyFiltration i) ((HomologicalComplex.homologyMap φ i).hom σ) ≤
      spectralInvariant (s.homologyFiltration i) σ + δ :=
  spectralInvariant_map_le _ (Cocone.map_homologyFiltration_le (e := (· + δ)) ψ hψ) σ

/-- **Filtered maps.** A chain map which is induced in homology by maps `F a ⟶ G a` does not
raise spectral invariants. -/
theorem spectralInvariant_homologyFiltration_homologyMap_le {φ : s.pt ⟶ t.pt}
    (ψ : ∀ a, F.obj a ⟶ G.obj a)
    (hψ : ∀ a, HomologicalComplex.homologyMap (ψ a) i ≫
        HomologicalComplex.homologyMap (t.ι.app a) i =
      HomologicalComplex.homologyMap (s.ι.app a) i ≫ HomologicalComplex.homologyMap φ i)
    (σ : s.pt.homology i) :
    spectralInvariant (t.homologyFiltration i) ((HomologicalComplex.homologyMap φ i).hom σ) ≤
      spectralInvariant (s.homologyFiltration i) σ :=
  spectralInvariant_le_of_imp fun a ha ↦
    Cocone.map_homologyFiltration_le (e := fun a ↦ a) ψ hψ a (Submodule.mem_map_of_mem ha)

/-- **Spectrality.** If the transition maps `F a ⟶ F b` are surjective in homology in degree `i`
whenever `[a, b]` does not meet the closed set `S`, then a finite spectral invariant lies in
`S`. -/
theorem mem_of_spectralInvariant_homologyFiltration_eq_coe_of_isClosed {S : Set ℝ}
    (hS : IsClosed S)
    (hFS : ∀ a b (hab : a ≤ b), Disjoint S (Icc a b) →
      Epi (HomologicalComplex.homologyMap (F.map (homOfLE hab)) i))
    {σ : s.pt.homology i} {r : ℝ} (hr : spectralInvariant (s.homologyFiltration i) σ = r) :
    r ∈ S :=
  mem_of_spectralInvariant_eq_coe_of_isClosed hS
    (fun _ _ hab hdisj ↦ Cocone.homologyFiltration_le_of_epi hab (hFS _ _ hab hdisj)) hr

/-- **Spectrality.** Suppose that the transition maps `F a ⟶ F b` are surjective in homology in
degree `i` whenever `[a, b]` does not meet the closed set `S`. Then the spectral invariant of a
class which does not come from the stage `a` but comes from the stage `b` is a real number in
`S`. -/
theorem exists_mem_spectralInvariant_homologyFiltration_eq {S : Set ℝ} (hS : IsClosed S)
    (hFS : ∀ a b (hab : a ≤ b), Disjoint S (Icc a b) →
      Epi (HomologicalComplex.homologyMap (F.map (homOfLE hab)) i))
    {a b : ℝ} {σ : s.pt.homology i} (hσa : σ ∉ s.homologyFiltration i a)
    (hσb : σ ∈ s.homologyFiltration i b) :
    ∃ r ∈ S, spectralInvariant (s.homologyFiltration i) σ = r :=
  exists_mem_spectralInvariant_eq (s.homologyFiltration_mono i) hS
    (fun _ _ hab hdisj ↦ Cocone.homologyFiltration_le_of_epi hab (hFS _ _ hab hdisj)) hσa hσb

/-- If the transition maps `F a ⟶ F b` are surjective in homology in degree `i` whenever `(a, b]`
does not meet the closed discrete set `S`, then a class with finite spectral invariant `r` comes
from the homology of the stage `F r`. -/
theorem mem_homologyFiltration_of_spectralInvariant_eq_coe {S : Set ℝ}
    (hS : Sᶜ ∈ codiscrete ℝ)
    (hFS : ∀ a b (hab : a ≤ b), Disjoint S (Ioc a b) →
      Epi (HomologicalComplex.homologyMap (F.map (homOfLE hab)) i))
    {σ : s.pt.homology i} {r : ℝ} (hr : spectralInvariant (s.homologyFiltration i) σ = r) :
    σ ∈ s.homologyFiltration i r :=
  mem_apply_of_spectralInvariant_eq_coe hS
    (fun _ _ hab hdisj ↦ Cocone.homologyFiltration_le_of_epi hab (hFS _ _ hab hdisj)) hr

end TauCeti
