/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Modules.LinearCombination
import Mathlib.Algebra.Category.Grp.Zero
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.AlgebraicGeometry.VectorBundle.Free.Basic
import TauCeti.Topology.Sets.Opens

/-!
# Serre's criterion for affineness

A quasi-compact scheme `X` on which every quasi-coherent ideal sheaf has vanishing first
cohomology is affine: Stacks, Lemma 30.3.1 (01XF), (2) implies (1). The proof has three steps.

* Every closed point `x` of `X` lies in an affine basic open `X_f` of a global function `f`
  (`AlgebraicGeometry.Scheme.exists_isAffineOpen_basicOpen_mem_of_isClosed`). Choose an affine
  open `U ∋ x`, and let `Z = (X ∖ U) ∪ {x}`, a closed subset in which `{x}` is open and closed.
  With `I` the vanishing ideal of `Z`, the sequence `0 ⟶ I ⟶ 𝒪_X ⟶ i_* 𝒪_Z ⟶ 0` and
  `H¹(X, I) = 0` lift the global function on `Z` that is `1` at `x` and `0` on `X ∖ U` to a global
  function `f` on `X`. Then `x ∈ X_f ⊆ U`, so `X_f` is a basic open of the affine open `U`.
* A quasi-coherent submodule `M` of a finite free module `𝒪_X^n` has `H¹(X, M) = 0`
  (`AlgebraicGeometry.Scheme.subsingleton_cohomology_one_of_comp_eq_zero_imp`, stated for `M`
  with finitely many jointly injective morphisms to `𝒪_X`). By induction on `n`: the image of `M`
  under the last coordinate is a quasi-coherent ideal sheaf `I`, the kernel of `M ⟶ I` is a
  submodule of `𝒪_X^{n-1}`, and the long exact sequence concludes.
* Since `X` is quasi-compact, finitely many such `X_{fᵢ}` cover `X` (every point specializes to a
  closed point). Then `(gᵢ) ↦ Σ fᵢ gᵢ` is an epimorphism `⨁ᵢ 𝒪_X ⟶ 𝒪_X` whose kernel is a
  quasi-coherent submodule of `⨁ᵢ 𝒪_X`, so the vanishing of its first cohomology lifts `1` to
  global functions `gᵢ` with `Σ fᵢ gᵢ = 1`. A scheme covered by affine basic opens of global
  functions generating the unit ideal is affine
  (`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`).

## Main results

* `AlgebraicGeometry.Scheme.exists_isAffineOpen_basicOpen_mem_of_isClosed`: if `H¹(X, I) = 0` for
  every ideal sheaf `I`, every closed point lies in an affine basic open of a global function.
* `AlgebraicGeometry.Scheme.isAffine_of_subsingleton_cohomology_one_idealSheaf`: **Serre's
  criterion**, a quasi-compact scheme with `H¹(X, I) = 0` for every quasi-coherent ideal sheaf `I`
  is affine.
* `AlgebraicGeometry.Scheme.isAffine_of_subsingleton_cohomology_one`: the same with `H¹(X, F) = 0`
  for every quasi-coherent `F`. The converse is
  `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`.
* `AlgebraicGeometry.Scheme.isAffine_tfae`: the three conditions (affine, `H¹` of quasi-coherent
  ideal sheaves vanishes, higher cohomology of quasi-coherent modules vanishes) are equivalent.

## References

* The Stacks Project, Lemma 30.3.1 (01XF).
* R. Hartshorne, *Algebraic Geometry*, Theorem III.3.7.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- If the first cohomology of every ideal sheaf on `X` vanishes, every closed point `x` of `X`
lies in the basic open `X_f` of a global function `f` with `X_f` affine. Stacks, proof of
Lemma 30.3.1 (01XF). -/
theorem exists_isAffineOpen_basicOpen_mem_of_isClosed (X : Scheme.{u})
    (h : ∀ I : X.IdealSheafData, Subsingleton (Cohomology I.sheaf 1)) {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  -- The closed subscheme `Z = (X ∖ U) ∪ {x}`, in which `{x}` is open and closed.
  let I := IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ ∪ {x}, U.isOpen.isClosed_compl.union hx⟩
  have hrange : Set.range I.subschemeι = (U : Set X)ᶜ ∪ {x} := by
    simp [I, IdealSheafData.range_subschemeι]
  have hUB : IsCompl (I.subschemeι ⁻¹ᵁ U) (I.subschemeι ⁻¹ᵁ ⟨{x}ᶜ, hx.isOpen_compl⟩) :=
    (Opens.isCompl_comap_iff _ _).mpr <| hrange ▸
      ⟨fun y hy ↦ hy.elim (fun hyU ↦ .inr (ne_of_mem_of_not_mem hxU hyU).symm) (.inl <| · ▸ hxU),
        Set.disjoint_left.mpr fun y hy hyUx ↦ hy.elim (· hyUx.1) (hyUx.2 ·)⟩
  -- The function on `Z` that is `1` at `x` and `0` on `X ∖ U` lifts to `X`, as `H¹(X, I) = 0`.
  obtain ⟨e, he⟩ := I.subscheme.exists_basicOpen_eq_of_isCompl hUB
  obtain ⟨g, hg⟩ : ∃ g : Γ(X, ⊤), I.subschemeι.app ⊤ g = e := by
    obtain ⟨g, hg⟩ := sections_surjective I.shortExact_toPushforwardSubscheme (h I) e
    exact ⟨g, (I.toPushforwardSubscheme_app g).symm.trans hg⟩
  have hpre : I.subschemeι ⁻¹ᵁ X.basicOpen g = I.subschemeι ⁻¹ᵁ U := by
    rw [preimage_basicOpen]
    exact (congrArg I.subscheme.basicOpen hg).trans he
  have hle : X.basicOpen g ≤ U := by
    intro z hz
    by_contra hzU
    obtain ⟨y, rfl⟩ : z ∈ Set.range I.subschemeι := hrange ▸ Or.inl hzU
    exact hzU (I.subschemeι.mem_preimage.mp (hpre ▸ I.subschemeι.mem_preimage.mpr hz))
  obtain ⟨y, hy⟩ : x ∈ Set.range I.subschemeι := hrange ▸ Or.inr rfl
  have hyU : y ∈ I.subschemeι ⁻¹ᵁ U := I.subschemeι.mem_preimage.mpr (hy ▸ hxU)
  refine ⟨g, hy ▸ I.subschemeι.mem_preimage.mp (hpre ▸ hyU), ?_⟩
  have := hU.basicOpen (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op g)
  rwa [basicOpen_res, inf_eq_right.mpr hle] at this

/-- If the first cohomology of every quasi-coherent ideal sheaf on `X` vanishes, so does that of
every quasi-coherent `𝒪_X`-module `M` with finitely many jointly injective morphisms
`φ i : M ⟶ 𝒪_X`, that is, of every quasi-coherent submodule of a finite free module. Stacks,
proof of Lemma 30.3.1 (01XF). -/
theorem subsingleton_cohomology_one_of_comp_eq_zero_imp
    (h : ∀ I : X.IdealSheafData, Subsingleton (Cohomology I.sheaf 1)) {ι : Type u} [Finite ι]
    (M : X.Modules) [M.IsQuasicoherent] (φ : ι → (M ⟶ Scheme.Modules.unit X))
    (hφ : ∀ ⦃Z : X.Modules⦄ (g : Z ⟶ M), (∀ i, g ≫ φ i = 0) → g = 0) :
    Subsingleton (Cohomology M 1) := by
  refine Finite.induction_empty_option (P := fun ι ↦ ∀ (M : X.Modules) [M.IsQuasicoherent]
      (φ : ι → (M ⟶ Scheme.Modules.unit X)),
      (∀ ⦃Z : X.Modules⦄ (g : Z ⟶ M), (∀ i, g ≫ φ i = 0) → g = 0) →
        Subsingleton (Cohomology M 1)) ?_ ?_ ?_ ι M φ hφ
  · intro α β e ih M _ φ hφ
    exact ih M (fun i ↦ φ (e i)) fun Z g hg ↦ hφ g fun i ↦ by simpa using hg (e.symm i)
  · intro M _ φ hφ
    have hM : IsZero M := by
      rw [IsZero.iff_id_eq_zero]
      exact hφ (𝟙 M) fun i ↦ isEmptyElim i
    exact (AddCommGrpCat.isZero_iff_subsingleton).mp ((cohomologyFunctor X 1).map_isZero hM)
  · intro α _ ih M _ φ hφ
    have : (kernel (φ none).toImageIdealSheaf).IsQuasicoherent :=
      isQuasicoherent_kernel (φ none).toImageIdealSheaf
    refine subsingleton_cohomology_X₂
      (TauCeti.kernelSequence_shortExact (C := X.Modules) (φ none).toImageIdealSheaf) 1
      (ih (kernel (φ none).toImageIdealSheaf)
        (fun i ↦ kernel.ι (φ none).toImageIdealSheaf ≫ φ (some i)) fun Z g hg ↦ ?_) (h _)
    -- `φ none` factors through `M ⟶ I` followed by the inclusion of `I`.
    have hnone : kernel.ι (φ none).toImageIdealSheaf ≫ φ none = 0 := by
      have h0 := kernel.condition_assoc (φ none).toImageIdealSheaf (φ none).imageIdealSheaf.sheafι
      rw [Hom.toImageIdealSheaf_ι] at h0
      exact h0.trans zero_comp
    have hg' : g ≫ kernel.ι (φ none).toImageIdealSheaf = 0 := hφ _ fun
      | none => by rw [Category.assoc, hnone, Limits.comp_zero]
      | some i => by rw [Category.assoc]; exact hg i
    exact zero_of_comp_mono _ hg'

/-- **Serre's criterion for affineness.** A quasi-compact scheme on which the first cohomology of
every quasi-coherent ideal sheaf vanishes is affine. Stacks, Lemma 30.3.1 (01XF). -/
theorem isAffine_of_subsingleton_cohomology_one_idealSheaf (X : Scheme.{u}) [CompactSpace X]
    (h : ∀ I : X.IdealSheafData, Subsingleton (Cohomology I.sheaf 1)) :
    IsAffine X := by
  -- Every point specializes to a closed point, which lies in an affine basic open.
  have hpt (y : X) : ∃ f : Γ(X, ⊤), y ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
    obtain ⟨x, hxy, hx⟩ := isClosed_closure.exists_closed_singleton
      (⟨y, subset_closure rfl⟩ : (closure ({y} : Set X)).Nonempty)
    obtain ⟨f, hxf, hf⟩ := X.exists_isAffineOpen_basicOpen_mem_of_isClosed h hx
    exact ⟨f, (specializes_iff_mem_closure.mpr hxy).mem_open (X.basicOpen f).isOpen hxf, hf⟩
  choose f hmem haff using hpt
  obtain ⟨t, ht⟩ := ((Opens.isCompactElement_iff ⊤).mpr isCompact_univ).exists_finset_of_le_iSup
    (fun y ↦ X.basicOpen (f y)) fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hmem y⟩
  let F : t → Γ(X, ⊤) := fun y ↦ f y
  have hcover : ⨆ i, X.basicOpen (F i) = ⊤ := top_le_iff.mp (ht.trans_eq (iSup_subtype' ..))
  -- The kernel of the surjection `𝒪_X^t ⟶ 𝒪_X`, `(gᵢ) ↦ Σ fᵢ gᵢ`, is a quasi-coherent submodule
  -- of `𝒪_X^t`, so its first cohomology vanishes and `1` lifts.
  have := epi_linearCombination F hcover
  have : (SheafOfModules.free (R := X.ringCatSheaf) t : X.Modules).IsQuasicoherent :=
    inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) t).IsQuasicoherent
  have : (kernel (C := X.Modules) (linearCombination F)).IsQuasicoherent :=
    isQuasicoherent_kernel (M := SheafOfModules.free (R := X.ringCatSheaf) t)
      (N := SheafOfModules.unit X.ringCatSheaf) _
  -- The coordinate projections of the biproduct `𝒪_X^t` are jointly injective.
  have hK := subsingleton_cohomology_one_of_comp_eq_zero_imp h
    (kernel (C := X.Modules) (linearCombination F))
    (fun i ↦ kernel.ι (C := X.Modules) _ ≫ (FiniteLocallyFreeSheaf.freeBicone X t).π i)
    fun Z g hg ↦ by
      have : Mono (kernel.ι (C := X.Modules) (linearCombination F)) := equalizer.ι_mono
      refine (cancel_mono (kernel.ι (C := X.Modules) (linearCombination F))).mp ?_
      refine (FiniteLocallyFreeSheaf.isBilimitFreeBicone X t).isLimit.hom_ext fun ⟨j⟩ ↦ ?_
      exact ((Category.assoc _ _ _).trans (hg j)).trans
        (zero_comp.symm.trans (Category.assoc _ _ _).symm)
  obtain ⟨c, hc⟩ := sections_surjective (TauCeti.kernelSequence_shortExact
    (C := X.Modules) (linearCombination F)) hK (1 : Γ(X, ⊤))
  obtain ⟨a, ha⟩ := exists_coefficients_linearCombination_app_eq_sum F ⊤ c
  have hspan : Ideal.span (Set.range F) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    have h1 := ha.symm.trans hc
    simp only [TopCat.Presheaf.map_apply_eq_self] at h1
    exact h1
  exact isAffine_of_isAffineOpen_basicOpen _ hspan fun _ ⟨i, hi⟩ ↦ hi ▸ haff i

/-- **Serre's criterion for affineness**, for all quasi-coherent modules. A quasi-compact scheme on
which the first cohomology of every quasi-coherent `𝒪_X`-module vanishes is affine. Stacks,
Lemma 30.3.1 (01XF). -/
theorem isAffine_of_subsingleton_cohomology_one (X : Scheme.{u}) [CompactSpace X]
    (h : ∀ (F : X.Modules) [F.IsQuasicoherent], Subsingleton (Cohomology F 1)) :
    IsAffine X :=
  isAffine_of_subsingleton_cohomology_one_idealSheaf X fun I ↦ h I.sheaf

/-- **Serre's criterion for affineness**, as equivalent conditions on a quasi-compact scheme `X`:
`X` is affine; the first cohomology of every quasi-coherent ideal sheaf vanishes; all higher
cohomology of every quasi-coherent `𝒪_X`-module vanishes. Stacks, Lemmas 30.3.1 (01XF) and 30.2.2
(01XB). -/
theorem isAffine_tfae (X : Scheme.{u}) [CompactSpace X] :
    List.TFAE [IsAffine X,
      ∀ I : X.IdealSheafData, Subsingleton (Cohomology I.sheaf 1),
      ∀ (F : X.Modules) [F.IsQuasicoherent] (n : ℕ), Subsingleton (Cohomology F (n + 1))] := by
  tfae_have 1 → 3 := fun _ _ _ _ ↦ inferInstance
  tfae_have 3 → 2 := fun h I ↦ h I.sheaf 0
  tfae_have 2 → 1 := isAffine_of_subsingleton_cohomology_one_idealSheaf X
  tfae_finish

end AlgebraicGeometry.Scheme
