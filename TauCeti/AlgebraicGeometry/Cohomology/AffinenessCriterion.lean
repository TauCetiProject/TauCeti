/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Modules.LinearCombination
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Serre's criterion for affineness

A quasi-compact scheme `X` on which every quasi-coherent `𝒪_X`-module has vanishing first
cohomology is affine (Stacks, Lemma 30.3.1 (01XF), (2) implies (1)). This file proves it in two
steps.

* Every closed point `x` of `X` lies in an affine basic open `X_f` of a global function `f`
  (`AlgebraicGeometry.Scheme.exists_isAffineOpen_basicOpen_mem_of_isClosed`); this step only uses
  the vanishing of `H¹(X, I)` for quasi-coherent ideal sheaves `I`. Choose an affine open
  `U ∋ x`, and let `Z = (X ∖ U) ∪ {x}`, a closed subset in which `{x}` is open and closed. With
  `I` the vanishing ideal of `Z`, the sequence `0 ⟶ I ⟶ 𝒪_X ⟶ i_* 𝒪_Z ⟶ 0` and `H¹(X, I) = 0`
  lift the global function on `Z` that is `1` at `x` and `0` on `X ∖ U` to a global function `f`
  on `X`. Then `x ∈ X_f ⊆ U`, so `X_f` is a basic open of the affine open `U`.
* Since `X` is quasi-compact, finitely many such `X_{fᵢ}` cover `X` (every point specializes to a
  closed point). Then `(gᵢ) ↦ Σ fᵢ gᵢ` is an epimorphism `𝒪_X^n ⟶ 𝒪_X` with quasi-coherent
  kernel, so the vanishing of the first cohomology of the kernel lifts `1` to global functions
  `gᵢ` with `Σ fᵢ gᵢ = 1`. A scheme covered by affine basic opens of global functions generating
  the unit ideal is affine (`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`).

## Main results

* `AlgebraicGeometry.Scheme.exists_isAffineOpen_basicOpen_mem_of_isClosed`: if `H¹(X, I) = 0` for
  every ideal sheaf `I`, every closed point lies in an affine basic open of a global function.
* `AlgebraicGeometry.Scheme.isAffine_of_subsingleton_cohomology_one`: **Serre's criterion**, a
  quasi-compact scheme with `H¹(X, F) = 0` for every quasi-coherent `F` is affine. The converse is
  `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`.

## References

* The Stacks Project, Lemma 30.3.1 (01XF).
* R. Hartshorne, *Algebraic Geometry*, Theorem III.3.7.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Scheme.Modules

variable {X : Scheme.{u}}

/-- If the first cohomology of every ideal sheaf on `X` vanishes, every closed point `x` of `X`
lies in the basic open `X_f` of a global function `f` with `X_f` affine. Stacks, proof of
Lemma 30.3.1 (01XF). -/
theorem exists_isAffineOpen_basicOpen_mem_of_isClosed
    (h : ∀ I : X.IdealSheafData, Subsingleton (Cohomology I.sheaf 1)) {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  -- The closed subscheme `Z = (X ∖ U) ∪ {x}`, in which `{x}` is open and closed.
  let I := IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ ∪ {x}, U.isOpen.isClosed_compl.union hx⟩
  have hrange : Set.range I.subschemeι = (U : Set X)ᶜ ∪ {x} := by
    simp [I, IdealSheafData.range_subschemeι]
  let B : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩
  have hUB : IsCompl (I.subschemeι ⁻¹ᵁ U) (I.subschemeι ⁻¹ᵁ B) := by
    constructor
    · rw [disjoint_iff]
      ext y
      simp only [Opens.coe_inf, Hom.coe_preimage, Set.mem_inter_iff, Set.mem_preimage,
        SetLike.mem_coe, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
      intro hyU hyB
      have : I.subschemeι y ∈ Set.range I.subschemeι := ⟨y, rfl⟩
      rw [hrange] at this
      exact this.elim (· hyU) hyB
    · rw [codisjoint_iff]
      ext y
      simp only [Opens.coe_sup, Opens.coe_top, Set.mem_univ, iff_true]
      by_cases hy : I.subschemeι y = x
      · exact Or.inl (show I.subschemeι y ∈ U from hy ▸ hxU)
      · exact Or.inr (show I.subschemeι y ∈ B from hy)
  -- The function on `Z` that is `1` at `x` and `0` on `X ∖ U` lifts to `X`, as `H¹(X, I) = 0`.
  obtain ⟨e, he⟩ := exists_basicOpen_eq_of_isCompl hUB
  obtain ⟨g, hg⟩ : ∃ g : Γ(X, ⊤), I.subschemeι.app ⊤ g = e :=
    sections_surjective I.shortExact_toPushforwardSubscheme (h I) e
  have hpre : I.subschemeι ⁻¹ᵁ X.basicOpen g = I.subschemeι ⁻¹ᵁ U := by
    rw [preimage_basicOpen]
    exact (congrArg I.subscheme.basicOpen hg).trans he
  have hle : X.basicOpen g ≤ U := by
    intro z hz
    by_contra hzU
    obtain ⟨y, rfl⟩ : z ∈ Set.range I.subschemeι := hrange ▸ Or.inl hzU
    exact hzU (show y ∈ I.subschemeι ⁻¹ᵁ U from hpre ▸ hz)
  obtain ⟨y, hy⟩ : x ∈ Set.range I.subschemeι := hrange ▸ Or.inr rfl
  have hyU : y ∈ I.subschemeι ⁻¹ᵁ U := show I.subschemeι y ∈ U from hy ▸ hxU
  refine ⟨g, hy ▸ (show y ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g from hpre ▸ hyU), ?_⟩
  have := hU.basicOpen (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op g)
  rwa [basicOpen_res, inf_eq_right.mpr hle] at this

/-- **Serre's criterion for affineness.** A quasi-compact scheme on which the first cohomology of
every quasi-coherent `𝒪_X`-module vanishes is affine. Stacks, Lemma 30.3.1 (01XF). -/
theorem isAffine_of_subsingleton_cohomology_one [CompactSpace X]
    (h : ∀ (F : X.Modules) [F.IsQuasicoherent], Subsingleton (Cohomology F 1)) :
    IsAffine X := by
  -- Every point specializes to a closed point, which lies in an affine basic open.
  have hpt (y : X) : ∃ f : Γ(X, ⊤), y ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
    obtain ⟨x, hxy, hx⟩ := isClosed_closure.exists_closed_singleton
      (⟨y, subset_closure rfl⟩ : (closure ({y} : Set X)).Nonempty)
    obtain ⟨f, hxf, hf⟩ := exists_isAffineOpen_basicOpen_mem_of_isClosed (fun I ↦ h I.sheaf) hx
    exact ⟨f, (specializes_iff_mem_closure.mpr hxy).mem_open (X.basicOpen f).isOpen hxf, hf⟩
  choose f hmem haff using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (X.basicOpen (f y) : Set X))
    (fun y ↦ (X.basicOpen (f y)).isOpen) fun y _ ↦ Set.mem_iUnion.mpr ⟨y, hmem y⟩
  let F : t → Γ(X, ⊤) := fun y ↦ f y
  have hcover : ⨆ i, X.basicOpen (F i) = ⊤ := by
    refine top_le_iff.mp fun z _ ↦ ?_
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hz⟩
  -- The kernel of the surjection `𝒪_X^t ⟶ 𝒪_X`, `(gᵢ) ↦ Σ fᵢ gᵢ`, is quasi-coherent, so `1` lifts.
  have := epi_linearCombination F hcover
  have : (SheafOfModules.free (R := X.ringCatSheaf) t : X.Modules).IsQuasicoherent :=
    inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) t).IsQuasicoherent
  have : (kernel (C := X.Modules) (linearCombination F)).IsQuasicoherent :=
    isQuasicoherent_kernel (M := SheafOfModules.free (R := X.ringCatSheaf) t)
      (N := SheafOfModules.unit X.ringCatSheaf) _
  obtain ⟨c, hc⟩ := sections_surjective (TauCeti.kernelSequence_shortExact
    (C := X.Modules) (linearCombination F)) (h (kernel (C := X.Modules) _)) (1 : Γ(X, ⊤))
  obtain ⟨a, ha⟩ := exists_linearCombination_app_eq F ⊤ c
  have hspan : Ideal.span (Set.range F) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    have h1 := ha.symm.trans hc
    simp only [show (Opens.leTop ⊤ : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
      X.presheaf.map_id, ConcreteCategory.id_apply] at h1
    exact h1
  exact isAffine_of_isAffineOpen_basicOpen _ hspan fun _ ⟨i, hi⟩ ↦ hi ▸ haff i

end AlgebraicGeometry.Scheme
