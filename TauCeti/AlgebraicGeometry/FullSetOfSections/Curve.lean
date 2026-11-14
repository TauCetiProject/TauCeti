/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.FullSetOfSections.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.IncidenceLocus
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.RingTheory.Ideal.Maps
import TauCeti.RingTheory.LocalRing.SemilocalPrincipal
import TauCeti.RingTheory.Norm.FullSetOfSections.SectionKernel
import TauCeti.RingTheory.Norm.Quotient

/-!
# Full sets of sections on smooth curves and sums of section divisors

Let `f : X ⟶ S` be a separated smooth morphism of relative dimension one, `Z ⊆ X` a closed
subscheme finite locally free over `S`, and `s₁, …, s_r` sections of `Z ⟶ S` inducing sections
`xᵢ = sᵢ ≫ i : S ⟶ X` of `f` with relative effective Cartier divisors `xᵢ.ker`. Following
Katz–Mazur, Theorem 1.8.3, `s₁, …, s_r` form a **full set of sections** of `Z ⟶ S` if and only if
`Z` equals `[x₁] + ⋯ + [x_r]` (`∏ k, xₖ.ker`) as a closed subscheme of `X`
(`isFullSetOfSections_subschemeι_comp_iff`, `isFullSetOfSections_iff_ker_eq_prod_ker`), with no
properness assumption on `f` and no reducedness assumption on `S`.

## Proof outline

Both directions reduce to `S = Spec R` for a local ring `R`, where every closed subscheme finite
over `S` has semilocal coordinate ring (`Scheme.Hom.finite_maximalSpectrum_appTop`):
* **Divisor sum `⇒` full set** (`isFullSetOfSections_prod_ker`): inducting on `ι` via
  `Fintype.induction_empty_option`, stalkwise principal kernels and annihilators
  (`IsEffectiveCartier.exists_map_ker_inclusion_appTop_eq_span_singleton_and_annihilator`) patch to
  a global generator `u`
  (`Ideal.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum`), so
  `IsFullSetOfSections.optionElim_of_ker_span_singleton` extends the full set of sections.
* **Full set `⇒` divisor sum** (`eq_prod_ker_of_isFullSetOfSections`): pulling back along
  `φ : Spec R ⟶ X` and its graph section `δ` yields `δ.ker.comap I.subschemeι = (u)`
  (`exists_eq_ofIdealTop_span_singleton_of_stalkIdeal`), Cayley–Hamilton gives `∏ k, xₖ.ker ≤ I`
  (`AlgHom.algebraMap_norm_eq_zero_of_map_eq_zero`), and matching fiber ranks `Fintype.card ι`
  (`IsFullSetOfSections.finrank_eq_card`, `finrank_prod_ker`) upgrades containment to equality.

## Main results

* `TauCeti.AlgebraicGeometry.isFullSetOfSections_prod_ker` and
  `TauCeti.AlgebraicGeometry.eq_prod_ker_of_isFullSetOfSections`: the two implications of
  Katz–Mazur Theorem 1.8.3.
* `TauCeti.AlgebraicGeometry.isFullSetOfSections_subschemeι_comp_iff`,
  `TauCeti.AlgebraicGeometry.isFullSetOfSections_iff_ker_eq_prod_ker`, and
  `TauCeti.AlgebraicGeometry.eq_of_isFullSetOfSections`: **Katz–Mazur, Theorem 1.8.3** and
  uniqueness of a finite locally free closed subscheme admitting a full set of sections.
* `TauCeti.AlgebraicGeometry.fullSetLocus_subschemeι_comp_eq_equalityLocus` and
  `TauCeti.AlgebraicGeometry.fullSetLocus_eq_equalityLocus`: equality of `fullSetLocus` and
  `equalityLocus` on `S`.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Theorem 1.8.3 and §§1.8–1.9.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.IdealSheafData

/-! ### Divisor sum implies full set of sections -/

private lemma exists_ker_span_singleton_and_annihilator_of_finite_maximalSpectrum
    {R : Type u} [CommRing R] [Finite (MaximalSpectrum R)] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {I₁ D' : X.IdealSheafData} (hCartier : I₁.IsEffectiveCartier)
    (hI₁ : I₁ * D' ≤ I₁) (hD' : I₁ * D' ≤ D') [IsFinite ((I₁ * D').subschemeι ≫ f)] :
    ∃ u : Γ((I₁ * D').subscheme, ⊤),
      RingHom.ker (inclusion hI₁).appTop.hom = Ideal.span {u} ∧
        RingHom.ker (inclusion hD').appTop.hom = (Ideal.span {u}).annihilator := by
  let g := (I₁ * D').subschemeι ≫ f
  have : IsAffine (I₁ * D').subscheme := isAffine_of_isAffineHom g
  have := g.finite_maximalSpectrum_appTop
  refine Ideal.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum _ _ fun M _ ↦ ?_
  obtain ⟨a, ha₁, ha₂⟩ :=
    IsEffectiveCartier.exists_map_ker_inclusion_appTop_eq_span_singleton_and_annihilator hCartier
      hI₁ hD' ((isAffineOpen_top (I₁ * D').subscheme).fromSpec ⟨M, inferInstance⟩)
  exact IsAffineOpen.exists_map_atPrime_eq_span_singleton_and_annihilator M ha₁ ha₂

private lemma isFullSetOfSections_option_of_ker_span_singleton {Y Z Z' : Scheme.{u}} [IsAffine Y]
    (g : Z ⟶ Y) [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    (g' : Z' ⟶ Y) [IsFinite g'] [Flat g'] [LocallyOfFinitePresentation g']
    (hloc : IsLocalRing Γ(Y, ⊤)) (ι_map : Z' ⟶ Z) [IsClosedImmersion ι_map] (hιg : ι_map ≫ g = g')
    {ι : Type*} [Fintype ι] {s : Option ι → (Y ⟶ Z)} (hs : ∀ k, s k ≫ g = 𝟙 Y)
    {s' : ι → (Y ⟶ Z')} (hs' : ∀ j, s' j ≫ g' = 𝟙 Y) (hcomp : ∀ j : ι, s' j ≫ ι_map = s (some j))
    {u : Γ(Z, ⊤)} (hker_s0 : RingHom.ker (s none).appTop.hom = Ideal.span {u})
    (hann : RingHom.ker ι_map.appTop.hom = (Ideal.span {u}).annihilator)
    (ih : IsFullSetOfSections g' s' hs') : IsFullSetOfSections g s hs := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let : Algebra Γ(Y, U) Γ(Z, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(Z', g' ⁻¹ᵁ U) := (g'.app U).hom.toAlgebra
  have : IsLocalRing Γ(Y, U) := hloc
  have : Module.Finite Γ(Y, U) Γ(Z', g' ⁻¹ᵁ U) := g'.finite_app U U.2
  have := g'.projective_app U
  have : Module.Free Γ(Y, U) Γ(Z', g' ⁻¹ᵁ U) := Module.free_of_flat_of_isLocalRing
  let eZ : Γ(Z, ⊤) ≃+* Γ(Z, g ⁻¹ᵁ ⊤) :=
    (Z.presheaf.mapIso (eqToIso g.preimage_top).op).commRingCatIsoToRingEquiv
  let eZ' : Γ(Z', ⊤) ≃+* Γ(Z', g' ⁻¹ᵁ ⊤) :=
    (Z'.presheaf.mapIso (eqToIso g'.preimage_top).op).commRingCatIsoToRingEquiv
  let π_hom : Γ(Z, g ⁻¹ᵁ ⊤) ⟶ Γ(Z', g' ⁻¹ᵁ ⊤) :=
    Z.presheaf.map (eqToHom g.preimage_top.symm).op ≫ ι_map.appTop ≫
      Z'.presheaf.map (eqToHom g'.preimage_top).op
  let π : Γ(Z, g ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Γ(Z', g' ⁻¹ᵁ U) :=
    { π_hom.hom with
      commutes' r := by
        have hcomm : g.app ⊤ ≫ π_hom = g'.app ⊤ := by
          simp only [π_hom, app_top_comp_map_preimage_top_assoc]
          rw [← Scheme.Hom.comp_appTop_assoc, hιg, appTop_comp_map_preimage_top]
        exact congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(Z', g' ⁻¹ᵁ ⊤) ↦ φ.hom r) hcomm }
  have hπ : Function.Surjective π :=
    (eZ'.surjective.comp (ι_map.app_surjective ⊤ (isAffineOpen_top Z))).comp eZ.symm.surjective
  have hker_σ0 : RingHom.ker (sectionAlgHom g (hs none) ⊤) = Ideal.span {eZ u} := by
    rw [ker_sectionAlgHom_top g (hs none), hker_s0, Ideal.map_span, Set.image_singleton]; rfl
  have hann' : RingHom.ker π = (Ideal.span {eZ u}).annihilator := by
    ext b
    have hb : b ∈ RingHom.ker π ↔ eZ.symm b ∈ RingHom.ker ι_map.appTop.hom := by
      rw [RingHom.mem_ker, show π b = eZ' (ι_map.appTop.hom (eZ.symm b)) from rfl,
        map_eq_zero_iff eZ' eZ'.injective, RingHom.mem_ker]
    rw [hb, hann, Submodule.mem_annihilator_span_singleton,
      Submodule.mem_annihilator_span_singleton, smul_eq_mul, smul_eq_mul,
      ← map_eq_zero_iff eZ eZ.injective, map_mul, eZ.apply_symm_apply]
  have hopt := ((isFullSetOfSections_iff_of_isAffine g' s' hs').1 ih)
    |>.optionElim_of_ker_span_singleton hπ hker_σ0 hann'
  rw [isFullSetOfSections_iff_of_isAffine]
  refine (Iff.of_eq (congrArg TauCeti.IsFullSetOfSections (funext fun o ↦ AlgHom.ext fun b ↦ ?_))).1
    hopt
  cases o with
  | none => rfl
  | some j =>
    rw [Option.elim_some, AlgHom.comp_apply,
      show π b = Z'.presheaf.map (eqToHom g'.preimage_top).op
        (ι_map.appTop (Z.presheaf.map (eqToHom g.preimage_top.symm).op b)) from rfl,
      sectionAlgHom_top_map_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcomp j,
      sectionAlgHom_top_apply]

private lemma isFullSetOfSections_option_prodKerSection_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] {ι : Type*} [Fintype ι]
    {x : Option ι → (Spec (.of R) ⟶ X)} (hx : ∀ k, x k ≫ f = 𝟙 _)
    (ih : IsFullSetOfSections ((∏ j : ι, (x (some j)).ker).subschemeι ≫ f)
      (prodKerSection fun j ↦ x (some j)) (prodKerSection_comp fun j ↦ hx (some j))) :
    IsFullSetOfSections ((∏ k : Option ι, (x k).ker).subschemeι ≫ f)
      (prodKerSection x) (prodKerSection_comp hx) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  let I₁ := (x none).ker; let D' := ∏ j : ι, (x (some j)).ker; let M := I₁ * D'
  have hopt : ∏ k : Option ι, (x k).ker = M := Fintype.prod_option _
  have hI₁ : M ≤ I₁ := mul_le_of_le_one_right bot_le le_top
  have hD' : M ≤ D' := mul_le_of_le_one_left bot_le le_top
  have := isFinite_prod_ker fun j ↦ hx (some j); have := flat_prod_ker fun j ↦ hx (some j)
  have := locallyOfFinitePresentation_prod_ker fun j ↦ hx (some j)
  have : IsFinite (M.subschemeι ≫ f) := hopt ▸ isFinite_prod_ker hx
  have : Flat (M.subschemeι ≫ f) := hopt ▸ flat_prod_ker hx
  have : LocallyOfFinitePresentation (M.subschemeι ≫ f) :=
    hopt ▸ locallyOfFinitePresentation_prod_ker hx
  have : IsAffine M.subscheme := isAffine_of_isAffineHom (M.subschemeι ≫ f)
  obtain ⟨u, hu₁, hu₂⟩ := exists_ker_span_singleton_and_annihilator_of_finite_maximalSpectrum f
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
      (x none) (hx none)).isEffectiveCartier hI₁ hD'
  let sM (k : Option ι) : Spec (.of R) ⟶ M.subscheme := prodKerSection x k ≫ inclusion hopt.ge
  have hsM (k : Option ι) : sM k ≫ (M.subschemeι ≫ f) = 𝟙 _ := by
    simp [sM, inclusion_subschemeι_assoc, hx]
  have hker_s0 : RingHom.ker (sM none).appTop.hom = Ideal.span {u} := by
    have hs0 : (sM none).ker = (inclusion hI₁).ker := by
      rw [← Scheme.Hom.comap_ker_comp_of_isClosedImmersion _ M.subschemeι]
      simp [sM, inclusion_subschemeι, prodKerSection_subschemeι, I₁]
    have htop := congrArg (fun K : M.subscheme.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top _⟩) hs0
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at htop; exact htop.trans hu₁
  have hM := isFullSetOfSections_option_of_ker_span_singleton (M.subschemeι ≫ f) (D'.subschemeι ≫ f)
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.isLocalRing (inclusion hD')
    (inclusion_subschemeι_assoc hD' f) hsM (prodKerSection_comp fun j ↦ hx (some j))
    (fun j ↦ by simp [← cancel_mono M.subschemeι, sM, D', inclusion_subschemeι]) hker_s0 hu₂ ih
  have : IsIso (inclusion hopt.ge) := IsClosedImmersion.isIso_of_ker_eq _ M.subschemeι
    (inclusion hopt.ge) (inclusion_subschemeι hopt.ge) (by simp [hopt])
  exact (isFullSetOfSections_iff_of_iso (M.subschemeι ≫ f) sM hsM (asIso (inclusion hopt.ge))
    (inclusion_subschemeι_assoc hopt.ge f) (prodKerSection_comp hx) fun _ ↦ rfl).2 hM

private lemma isFullSetOfSections_prodKerSection_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] {ι : Type*} [Fintype ι]
    (x : ι → (Spec (.of R) ⟶ X)) (hx : ∀ i, x i ≫ f = 𝟙 _) :
    IsFullSetOfSections ((∏ k, (x k).ker).subschemeι ≫ f)
      (prodKerSection x) (prodKerSection_comp hx) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  refine Fintype.induction_empty_option
    (P := fun α _ ↦ ∀ (x : α → (Spec (.of R) ⟶ X)) (hx : ∀ i, x i ≫ f = 𝟙 _),
      IsFullSetOfSections ((∏ k, (x k).ker).subschemeι ≫ f)
        (prodKerSection x) (prodKerSection_comp hx)) ?_ ?_ ?_ ι x hx
  · intro α β _ e hα x hx
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    let x' : α → (Spec (.of R) ⟶ X) := x ∘ e
    have hx' (j : α) : x' j ≫ f = 𝟙 _ := hx (e j)
    have hpeq : ∏ j, (x' j).ker = ∏ i, (x i).ker := Fintype.prod_equiv e _ _ fun _ ↦ rfl
    have := isFinite_prod_ker hx; have := flat_prod_ker hx
    have := locallyOfFinitePresentation_prod_ker hx
    have : IsIso (inclusion hpeq.ge) := IsClosedImmersion.isIso_of_ker_eq _ _ (inclusion hpeq.ge)
      (inclusion_subschemeι hpeq.ge) (by simp [hpeq])
    have h1 := (isFullSetOfSections_iff_of_iso ((∏ i, (x i).ker).subschemeι ≫ f)
      (fun j ↦ prodKerSection x (e j)) (fun j ↦ prodKerSection_comp hx (e j))
      (asIso (inclusion hpeq.ge)) (inclusion_subschemeι_assoc hpeq.ge f) (prodKerSection_comp hx')
      fun j ↦ by
        rw [← cancel_mono (∏ i, (x i).ker).subschemeι, asIso_hom, Category.assoc,
          inclusion_subschemeι, prodKerSection_subschemeι, prodKerSection_subschemeι]; rfl).1
      (hα x' hx')
    exact (isFullSetOfSections_iff_of_equiv ((∏ i, (x i).ker).subschemeι ≫ f) (prodKerSection x)
      (prodKerSection_comp hx) (fun j ↦ prodKerSection_comp hx (e j)) e fun _ ↦ rfl).1 h1
  · intro x hx
    let D₀ := ∏ k : PEmpty, (x k).ker
    have := isFinite_prod_ker hx; have := flat_prod_ker hx
    have := locallyOfFinitePresentation_prod_ker hx
    have hD₀ : D₀ = ⊤ := Finset.prod_empty.trans one_eq_top
    have : IsEmpty D₀.subscheme := hD₀ ▸ inferInstance
    have hbot : (D₀.subschemeι ≫ f) ⁻¹ᵁ ⊤ = ⊥ := by ext z; exact isEmptyElim z
    have : Subsingleton Γ(D₀.subscheme, (D₀.subschemeι ≫ f) ⁻¹ᵁ ⊤) := hbot ▸ inferInstance
    rw [isFullSetOfSections_iff_of_isAffine]
    let := ((D₀.subschemeι ≫ f).app ⊤).hom.toAlgebra
    exact TauCeti.isFullSetOfSections_of_subsingleton _
  · exact fun _ _ ih _ hx ↦
      isFullSetOfSections_option_prodKerSection_of_isLocalRing hx (ih _ fun j ↦ hx (some j))

/-- **Sections of a smooth separated curve form a full set of sections of their divisor sum**
(Katz–Mazur, Theorem 1.8.3, `(⇐)`). -/
theorem isFullSetOfSections_prod_ker {X S : Scheme.{u}} {f : X ⟶ S} [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] {ι : Type*} [Fintype ι] {x : ι → (S ⟶ X)}
    (hx : ∀ i, x i ≫ f = 𝟙 S) :
    IsFullSetOfSections ((∏ k, (x k).ker).subschemeι ≫ f)
      (prodKerSection x) (prodKerSection_comp hx) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  let D := ∏ k, (x k).ker
  have := isFinite_prod_ker hx; have := flat_prod_ker hx
  have := locallyOfFinitePresentation_prod_ker hx
  rw [isFullSetOfSections_iff_fullSetLocus_eq_bot (D.subschemeι ≫ f)]
  refine eq_bot_of_le_ker_Spec_isLocalRing fun R _ _ t ↦ ?_
  let f' := Limits.pullback.fst t f; let pX := Limits.pullback.snd t f
  have := SmoothOfRelativeDimension.smooth 1 f'
  let x' : ι → (Spec (.of R) ⟶ Limits.pullback t f) :=
    fun i ↦ baseChangeSection f (x i) (hx i) (Over.mk t)
  have hx' (i : ι) : x' i ≫ f' = 𝟙 _ := baseChangeSection_fst f (x i) (hx i) (Over.mk t)
  have hker (i : ι) : (x' i).ker = (x i).ker.comap pX := by
    have := Scheme.Hom.isClosedImmersion_of_comp_eq_id (x i) (hx i)
    exact Scheme.Hom.ker_eq_comap_of_isPullback_section (IsPullback.of_hasPullback t f).flip
      (hx i) (hx' i) (baseChangeSection_snd f (x i) (hx i) (Over.mk t))
  let D' := ∏ k, (x' k).ker
  have hD' : D' = D.comap pX := by rw [comap_prod]; exact Finset.prod_congr rfl fun i _ ↦ hker i
  have H_D := isPullback_subschemeMap_of_eq hD' (IsPullback.of_hasPullback t f).flip
  have := isFinite_prod_ker hx'; have := flat_prod_ker hx'
  have := locallyOfFinitePresentation_prod_ker hx'
  have hs' (i : ι) :
      prodKerSection x' i ≫ subschemeMap D' D pX (hD' ▸ D.le_map_comap pX) =
        t ≫ prodKerSection x i := by
    rw [← cancel_mono D.subschemeι, Category.assoc, subschemeMap_subschemeι,
      prodKerSection_subschemeι_assoc, Category.assoc, prodKerSection_subschemeι]
    exact baseChangeSection_snd f (x i) (hx i) (Over.mk t)
  rw [fullSetLocus_le_ker_iff_of_isPullback (D.subschemeι ≫ f) (prodKerSection x)
    (prodKerSection_comp hx) H_D (prodKerSection_comp hx') hs']
  exact isFullSetOfSections_prodKerSection_of_isLocalRing x' hx'

/-! ### Full set of sections implies divisor sum -/

private lemma prod_comap_ofIdealTop_span_le_ker
    {Y Z W : Scheme.{u}} [IsAffine Y] (g : Z ⟶ Y) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (hloc : IsLocalRing Γ(Y, ⊤)) {ι : Type*} [Fintype ι]
    {s : ι → (Y ⟶ Z)} (hs : ∀ i, s i ≫ g = 𝟙 Y) (hfull : IsFullSetOfSections g s hs) (u : Γ(Z, ⊤))
    {ℓ : W ⟶ Z} {w : W ⟶ Y} (hℓg : ℓ ≫ g = w) (hu : ofIdealTop (Ideal.span {u}) ≤ ℓ.ker) :
    ∏ i, (ofIdealTop (Ideal.span {u})).comap (s i) ≤ w.ker := by
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let : Algebra Γ(Y, U) Γ(Z, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(W, ⊤) := w.appTop.hom.toAlgebra
  have : IsLocalRing Γ(Y, U) := hloc
  have : Module.Finite Γ(Y, U) Γ(Z, g ⁻¹ᵁ U) := g.finite_app U U.2
  have := g.projective_app U
  have : Module.Free Γ(Y, U) Γ(Z, g ⁻¹ᵁ U) := Module.free_of_flat_of_isLocalRing
  let u' : Γ(Z, g ⁻¹ᵁ ⊤) := Z.presheaf.map (eqToHom g.preimage_top).op u
  rw [prod_comap_ofIdealTop_span_singleton g hs Finset.univ u,
    ← ((isFullSetOfSections_iff g s hs).1 hfull U).norm_eq_prod u', ofIdealTop_le_ker_iff,
    Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  have hℓu : ℓ.appTop.hom u = 0 :=
    (ofIdealTop_le_ker_iff ℓ (Ideal.span {u})).mp hu (Ideal.mem_span_singleton_self u)
  let τ : Γ(Z, g ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Γ(W, ⊤) :=
    { (Z.presheaf.map (eqToHom g.preimage_top.symm).op ≫ ℓ.appTop).hom with
      commutes' r := by
        have hcomm : g.app ⊤ ≫ Z.presheaf.map (eqToHom g.preimage_top.symm).op ≫ ℓ.appTop =
            w.appTop := by
          rw [app_top_comp_map_preimage_top_assoc, ← Scheme.Hom.comp_appTop, hℓg]
        exact congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(W, ⊤) ↦ φ.hom r) hcomm }
  refine τ.algebraMap_norm_eq_zero_of_map_eq_zero ?_
  rw [show τ u' = ℓ.appTop (Z.presheaf.map (eqToHom g.preimage_top.symm).op u') from rfl,
    ← CommRingCat.comp_apply (Z.presheaf.map _) (Z.presheaf.map _), ← Functor.map_comp, eqToHom_op,
    eqToHom_op, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  exact hℓu

private lemma comap_prod_ker_le_comap_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] {ι : Type*} [Fintype ι]
    {s : ι → (Spec (.of R) ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 _)
    (hfull : IsFullSetOfSections (I.subschemeι ≫ f) s hs) {δ : Spec (.of R) ⟶ X}
    (hδ : δ ≫ f = 𝟙 _) : (∏ i, (s i ≫ I.subschemeι).ker).comap δ ≤ I.comap δ := by
  have hCartier : δ.ker.IsEffectiveCartier :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension δ hδ).isEffectiveCartier
  obtain ⟨u, hu⟩ := exists_eq_ofIdealTop_span_singleton_of_stalkIdeal (I.subschemeι ≫ f)
    (δ.ker.comap I.subschemeι) fun z ↦ by
      obtain ⟨V, hzV, α, -, hα⟩ := (isEffectiveCartier_iff δ.ker).mp hCartier (I.subschemeι z)
      refine ⟨(I.subschemeι.stalkMap z).hom ((X.presheaf.germ V.1 _ hzV).hom α), ?_⟩
      rw [δ.ker.stalkIdeal_comap, δ.ker.stalkIdeal_eq_map V _ hzV, hα, Ideal.map_span,
        Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hcomm (i : ι) : (s i ≫ I.subschemeι).ker.comap δ =
      (ofIdealTop (Ideal.span {u})).comap (s i) := by
    have hx₀ : (s i ≫ I.subschemeι) ≫ f = 𝟙 _ := by rw [Category.assoc, hs i]
    have := Scheme.Hom.isClosedImmersion_of_comp_eq_id δ hδ
    have := Scheme.Hom.isClosedImmersion_of_comp_eq_id (s i ≫ I.subschemeι) hx₀
    rw [Scheme.Hom.ker_comap_section_comm hδ hx₀, comap_comp, hu]
  rw [comap_prod]; simp_rw [hcomm]
  let K := I.comap δ; let ℓ : K.subscheme ⟶ I.subscheme := subschemeMap K I δ (I.le_map_comap δ)
  have hℓg : ℓ ≫ (I.subschemeι ≫ f) = K.subschemeι := by
    rw [← Category.assoc, subschemeMap_subschemeι, Category.assoc, hδ, Category.comp_id]
  have hle : ofIdealTop (Ideal.span {u}) ≤ ℓ.ker := by
    rw [← hu, ← le_map_iff_comap_le, map_ker, subschemeMap_subschemeι]
    exact Scheme.Hom.le_ker_comp K.subschemeι δ
  rw [← (I.comap δ).ker_subschemeι]
  exact prod_comap_ofIdealTop_span_le_ker (I.subschemeι ≫ f)
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.isLocalRing hs hfull u hℓg hle

section MainTheorem

variable {X S : Scheme.{u}} {f : X ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {ι : Type*} [Fintype ι]

/-- If `s` is a full set of sections of a finite locally free closed subscheme `V(I) ⊆ X` of a
separated smooth curve `X ⟶ S`, then `∏ i, (s i ≫ I.subschemeι).ker ≤ I`. -/
theorem prod_ker_le_of_isFullSetOfSections {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    {s : ι → (S ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S)
    (hfull : IsFullSetOfSections (I.subschemeι ≫ f) s hs) :
    ∏ i, (s i ≫ I.subschemeι).ker ≤ I := by
  refine le_of_comap_Spec_isLocalRing fun R _ _ φ ↦ ?_
  let t := φ ≫ f; let f' := Limits.pullback.fst t f; let pX := Limits.pullback.snd t f
  have H : IsPullback pX f' f t := (IsPullback.of_hasPullback t f).flip
  have H_I := I.isPullback_subschemeMap_comap f H
  let _ : IsFinite ((I.comap pX).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback H_I inferInstance
  let _ : Flat ((I.comap pX).subschemeι ≫ f') := MorphismProperty.of_isPullback H_I inferInstance
  let _ : LocallyOfFinitePresentation ((I.comap pX).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback H_I inferInstance
  have hfull' : IsFullSetOfSections ((I.comap pX).subschemeι ≫ f')
      (pullbackSubschemeSection H I s hs) (pullbackSubschemeSection_comp H I s hs) := by
    rw [← fullSetLocus_le_ker_iff_of_isPullback (I.subschemeι ≫ f) s hs H_I
      (pullbackSubschemeSection_comp H I s hs) (pullbackSubschemeSection_subschemeMap H I s hs),
      (isFullSetOfSections_iff_fullSetLocus_eq_bot _ _ _).1 hfull]; exact bot_le
  have hδφ : graphSection (T := Over.mk t) (Over.homMk φ rfl) ≫ pX = φ :=
    graphSection_snd (T := Over.mk t) (Over.homMk φ rfl)
  rw [← hδφ, comap_comp, comap_comp, ← prod_ker_pullbackSubschemeSection H I s hs]
  exact comap_prod_ker_le_comap_of_isLocalRing (pullbackSubschemeSection_comp H I s hs) hfull'
    (graphSection_fst (T := Over.mk t) (Over.homMk φ rfl))

/-- **Full set of sections implies divisor sum** (Katz–Mazur, Theorem 1.8.3, `(⇒)`): if `s` is a
full set of sections of a finite locally free closed subscheme `V(I) ⊆ X` of a separated smooth
curve `X ⟶ S`, then `I = ∏ i, (s i ≫ I.subschemeι).ker`. -/
theorem eq_prod_ker_of_isFullSetOfSections {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    {s : ι → (S ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S)
    (hfull : IsFullSetOfSections (I.subschemeι ≫ f) s hs) :
    I = ∏ i, (s i ≫ I.subschemeι).ker := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (i : ι) : (s i ≫ I.subschemeι) ≫ f = 𝟙 S := by rw [Category.assoc, hs i]
  have := isFinite_prod_ker hx; have := flat_prod_ker hx
  refine (eq_of_le_of_finrank_eq (prod_ker_le_of_isFullSetOfSections hs hfull) f ?_).symm
  ext p; rw [finrank_prod_ker hx p, hfull.finrank_eq_card p]

/-- **Katz–Mazur, Theorem 1.8.3** (ideal-sheaf form). For a separated smooth curve `f : X ⟶ S` and
an ideal sheaf `I` with `V(I) ⟶ S` finite locally free, sections `s : ι → (S ⟶ I.subscheme)` form a
full set of sections iff `I = ∏ i, (s i ≫ I.subschemeι).ker`. -/
theorem isFullSetOfSections_subschemeι_comp_iff {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    {s : ι → (S ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S) :
    IsFullSetOfSections (I.subschemeι ≫ f) s hs ↔ I = ∏ i, (s i ≫ I.subschemeι).ker := by
  refine ⟨eq_prod_ker_of_isFullSetOfSections hs, fun hI ↦ ?_⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (i : ι) : (s i ≫ I.subschemeι) ≫ f = 𝟙 S := by rw [Category.assoc, hs i]
  let D := ∏ i, (s i ≫ I.subschemeι).ker
  have := isFinite_prod_ker hx; have := flat_prod_ker hx
  have := locallyOfFinitePresentation_prod_ker hx
  have : IsIso (inclusion hI.ge) := IsClosedImmersion.isIso_of_ker_eq I.subschemeι D.subschemeι
    (inclusion hI.ge) (inclusion_subschemeι hI.ge) (by simp [hI, D])
  exact (isFullSetOfSections_iff_of_iso (D.subschemeι ≫ f) (prodKerSection _)
    (prodKerSection_comp hx) (asIso (inclusion hI.ge)) (inclusion_subschemeι_assoc hI.ge f) hs
    fun i ↦ by
      rw [← cancel_mono D.subschemeι, asIso_hom, Category.assoc, inclusion_subschemeι,
        prodKerSection_subschemeι]).2 (isFullSetOfSections_prod_ker hx)

/-- **Katz–Mazur, Theorem 1.8.3** (closed-immersion form). For a separated smooth curve `f : X ⟶ S`
and a closed immersion `i : Z ⟶ X` with `i ≫ f` finite locally free, sections `s : ι → (S ⟶ Z)`
form a full set of sections iff `i.ker = ∏ k, (s k ≫ i).ker`. -/
theorem isFullSetOfSections_iff_ker_eq_prod_ker {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    {s : ι → (S ⟶ Z)} (hs : ∀ k, s k ≫ (i ≫ f) = 𝟙 S) :
    IsFullSetOfSections (i ≫ f) s hs ↔ i.ker = ∏ k, (s k ≫ i).ker := by
  let e : Z ≅ i.ker.subscheme := asIso i.toImage
  have heg : e.hom ≫ (i.ker.subschemeι ≫ f) = i ≫ f := i.toImage_imageι_assoc f
  have hs' (k : ι) : (s k ≫ e.hom) ≫ (i.ker.subschemeι ≫ f) = 𝟙 S := by
    rw [Category.assoc, heg, hs k]
  have hker (k : ι) : (s k ≫ e.hom) ≫ i.ker.subschemeι = s k ≫ i := by
    rw [Category.assoc]; exact congrArg (s k ≫ ·) i.toImage_imageι
  rw [isFullSetOfSections_iff_of_iso (i.ker.subschemeι ≫ f) (fun k ↦ s k ≫ e.hom) hs' e heg hs
    (fun _ ↦ rfl), isFullSetOfSections_subschemeι_comp_iff hs']
  simp_rw [hker]

/-- **Uniqueness of the closed subscheme admitting a full set of sections**: on a separated smooth
curve `X ⟶ S`, at most one finite locally free closed subscheme can admit a given family of
sections of `X ⟶ S` as a full set of sections. -/
theorem eq_of_isFullSetOfSections {I₁ I₂ : X.IdealSheafData}
    [IsFinite (I₁.subschemeι ≫ f)] [Flat (I₁.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I₁.subschemeι ≫ f)]
    [IsFinite (I₂.subschemeι ≫ f)] [Flat (I₂.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I₂.subschemeι ≫ f)]
    {s₁ : ι → (S ⟶ I₁.subscheme)} {s₂ : ι → (S ⟶ I₂.subscheme)}
    (hs₁ : ∀ i, s₁ i ≫ (I₁.subschemeι ≫ f) = 𝟙 S) (hs₂ : ∀ i, s₂ i ≫ (I₂.subschemeι ≫ f) = 𝟙 S)
    (h₁ : IsFullSetOfSections (I₁.subschemeι ≫ f) s₁ hs₁)
    (h₂ : IsFullSetOfSections (I₂.subschemeι ≫ f) s₂ hs₂)
    (hcomp : ∀ i, s₁ i ≫ I₁.subschemeι = s₂ i ≫ I₂.subschemeι) : I₁ = I₂ := by
  rw [eq_prod_ker_of_isFullSetOfSections hs₁ h₁, eq_prod_ker_of_isFullSetOfSections hs₂ h₂]
  simp_rw [hcomp]

/-- **On a separated smooth curve, the full-set locus equals the divisor equality locus**
(ideal-sheaf form). -/
theorem fullSetLocus_subschemeι_comp_eq_equalityLocus {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    {s : ι → (S ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S) :
    letI : IsFinite ((∏ i, (s i ≫ I.subschemeι).ker).subschemeι ≫ f) :=
      have := SmoothOfRelativeDimension.smooth 1 f
      isFinite_prod_ker fun i ↦ by rw [Category.assoc, hs i]
    letI := flat_prod_ker (f := f) (x := fun i ↦ s i ≫ I.subschemeι)
      fun i ↦ by rw [Category.assoc, hs i]
    letI := locallyOfFinitePresentation_prod_ker (f := f) (x := fun i ↦ s i ≫ I.subschemeι)
      fun i ↦ by rw [Category.assoc, hs i]
    fullSetLocus (I.subschemeι ≫ f) s hs = equalityLocus f I (∏ i, (s i ≫ I.subschemeι).ker) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (i : ι) : (s i ≫ I.subschemeι) ≫ f = 𝟙 S := by rw [Category.assoc, hs i]
  let _ := isFinite_prod_ker hx; let _ := flat_prod_ker hx
  let _ := locallyOfFinitePresentation_prod_ker hx
  let D := ∏ i, (s i ≫ I.subschemeι).ker
  refine eq_of_forall_le_ker_iff fun r ↦ ?_
  let f' := Limits.pullback.fst r f; let pX := Limits.pullback.snd r f
  have H : IsPullback pX f' f r := (IsPullback.of_hasPullback r f).flip
  have H_I := I.isPullback_subschemeMap_comap f H
  let _ : IsFinite ((I.comap pX).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback H_I inferInstance
  let _ : Flat ((I.comap pX).subschemeι ≫ f') := MorphismProperty.of_isPullback H_I inferInstance
  let _ : LocallyOfFinitePresentation ((I.comap pX).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback H_I inferInstance
  rw [fullSetLocus_le_ker_iff_of_isPullback (I.subschemeι ≫ f) s hs H_I
    (pullbackSubschemeSection_comp H I s hs) (pullbackSubschemeSection_subschemeMap H I s hs),
    isFullSetOfSections_subschemeι_comp_iff, prod_ker_pullbackSubschemeSection H I s hs,
    equalityLocus_le_ker_iff_of_isPullback I D H]

/-- **On a separated smooth curve, the full-set locus equals the divisor equality locus**
(closed-immersion form). -/
theorem fullSetLocus_eq_equalityLocus {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    {s : ι → (S ⟶ Z)} (hs : ∀ k, s k ≫ (i ≫ f) = 𝟙 S) :
    letI : IsFinite ((∏ k, (s k ≫ i).ker).subschemeι ≫ f) :=
      have := SmoothOfRelativeDimension.smooth 1 f
      isFinite_prod_ker fun k ↦ by rw [Category.assoc, hs k]
    letI := flat_prod_ker (f := f) (x := fun k ↦ s k ≫ i) fun k ↦ by rw [Category.assoc, hs k]
    letI := locallyOfFinitePresentation_prod_ker (f := f) (x := fun k ↦ s k ≫ i)
      fun k ↦ by rw [Category.assoc, hs k]
    fullSetLocus (i ≫ f) s hs = equalityLocus f i.ker (∏ k, (s k ≫ i).ker) := by
  let e : Z ≅ i.ker.subscheme := asIso i.toImage
  have heg : e.hom ≫ (i.ker.subschemeι ≫ f) = i ≫ f := i.toImage_imageι_assoc f
  have hs' (k : ι) : (s k ≫ e.hom) ≫ (i.ker.subschemeι ≫ f) = 𝟙 S := by
    rw [Category.assoc, heg, hs k]
  have hker (k : ι) : (s k ≫ e.hom) ≫ i.ker.subschemeι = s k ≫ i := by
    rw [Category.assoc]; exact congrArg (s k ≫ ·) i.toImage_imageι
  rw [fullSetLocus_eq_of_iso (i.ker.subschemeι ≫ f) (fun k ↦ s k ≫ e.hom) hs' e heg hs
    (fun _ ↦ rfl), fullSetLocus_subschemeι_comp_eq_equalityLocus hs']
  congr 1; simp_rw [hker]

end MainTheorem

end TauCeti.AlgebraicGeometry
