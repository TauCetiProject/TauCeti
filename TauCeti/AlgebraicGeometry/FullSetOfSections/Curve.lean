/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.FullSetOfSections.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.IncidenceLocus
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.RingTheory.LocalProperties.Semilocal
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

This equivalence bridges the coordinate-ring norm condition (`IsFullSetOfSections`, `fullSetLocus`)
on finite locally free `S`-schemes to relative effective Cartier divisor sums and schematic divisor
equality (`equalityLocus`) on smooth separated curves over arbitrary bases. Consequently, at most
one finite locally free closed subscheme of `X` can admit a given family of sections of `f` as a
full set of sections (`eq_of_isFullSetOfSections`), and the full-set locus of sections of `Z ⟶ S`
coincides as a closed subscheme of `S` with the locus where `Z` equals the sum of the corresponding
section divisors (`fullSetLocus_subschemeι_comp_eq_equalityLocus`, `fullSetLocus_eq_equalityLocus`).

## Main results

* `TauCeti.AlgebraicGeometry.isFullSetOfSections_prod_ker`,
  `TauCeti.AlgebraicGeometry.eq_prod_ker_of_isFullSetOfSections`,
  `TauCeti.AlgebraicGeometry.isFullSetOfSections_subschemeι_comp_iff`, and
  `TauCeti.AlgebraicGeometry.isFullSetOfSections_iff_ker_eq_prod_ker`: **Katz–Mazur 1.8.3**.
* `TauCeti.AlgebraicGeometry.eq_of_isFullSetOfSections`,
  `TauCeti.AlgebraicGeometry.fullSetLocus_subschemeι_comp_eq_equalityLocus`, and
  `TauCeti.AlgebraicGeometry.fullSetLocus_eq_equalityLocus`: closed-subscheme uniqueness and
  identification of `fullSetLocus` with `equalityLocus`.

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

private lemma isFullSetOfSections_option_of_ker_span_singleton {Y Z Z' : Scheme.{u}} [IsAffine Y]
    (g : Z ⟶ Y) [IsAffineHom g] (g' : Z' ⟶ Y) [IsFinite g'] [Flat g']
    (hloc : IsLocalRing Γ(Y, ⊤)) (ι_map : Z' ⟶ Z) [IsClosedImmersion ι_map] (hιg : ι_map ≫ g = g')
    {ι : Type*} [Fintype ι] {s : Option ι → (Y ⟶ Z)} (hs : ∀ k, s k ≫ g = 𝟙 Y)
    {s' : ι → (Y ⟶ Z')} (hs' : ∀ j, s' j ≫ g' = 𝟙 Y) (hcomp : ∀ j : ι, s' j ≫ ι_map = s (some j))
    {u : Γ(Z, ⊤)} (hker_s0 : RingHom.ker (s none).appTop.hom = Ideal.span {u})
    (hann : RingHom.ker ι_map.appTop.hom = (Ideal.span {u}).annihilator)
    (ih : IsFullSetOfSections g' s' hs') : IsFullSetOfSections g s hs := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  let : Algebra Γ(Y, ⊤) Γ(Z, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(Z', ⊤) := g'.appTop.hom.toAlgebra
  have : Module.Finite Γ(Y, ⊤) Γ(Z', ⊤) := g'.finite_appTop; have := g'.free_appTop
  let π := ι_map.appTopAlgHom hιg
  have hπ : Function.Surjective π :=
    ι_map.coe_appTopAlgHom hιg ▸ (IsClosedImmersion.isAffine_surjective_of_isAffine ι_map).2
  have hker_σ0 : RingHom.ker (sectionTopAlgHom g (hs none)) = Ideal.span {u} := by
    rw [AlgHom.ker_coe, toRingHom_sectionTopAlgHom, hker_s0]
  have hann' : RingHom.ker π = (Ideal.span {u}).annihilator := by
    rw [AlgHom.ker_coe, ι_map.toRingHom_appTopAlgHom hιg, hann]
  have hopt := ((isFullSetOfSections_iff_sectionTopAlgHom_of_isAffine g' s' hs').1 ih)
    |>.optionElim_of_ker_span_singleton hπ hker_σ0 hann'
  rw [isFullSetOfSections_iff_sectionTopAlgHom_of_isAffine]
  refine (Iff.of_eq (congrArg TauCeti.IsFullSetOfSections (funext fun o ↦ AlgHom.ext fun b ↦ ?_))).1
    hopt
  rcases o with _ | j <;> simp [π, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcomp]

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
  have : IsFinite (M.subschemeι ≫ f) := hopt ▸ isFinite_prod_ker hx
  have : IsAffine M.subscheme := isAffine_of_isAffineHom (M.subschemeι ≫ f)
  have := (M.subschemeι ≫ f).finite_maximalSpectrum_appTop
  have hCart := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
    (x none) (hx none)).isEffectiveCartier
  obtain ⟨u, hu₁, hu₂⟩ := Ideal.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum
    _ _ fun P _ ↦
      let ⟨a, ha₁, ha₂⟩ := hCart.exists_map_ker_inclusion_appTop_eq_span_singleton_and_annihilator
        hI₁ hD' ((isAffineOpen_top M.subscheme).fromSpec ⟨P, inferInstance⟩)
      M.subscheme.exists_map_atPrime_eq_span_singleton_and_annihilator P ha₁ ha₂
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
  exact (isFullSetOfSections_subschemeι_comp_iff_of_eq hopt (prodKerSection_comp hx) hsM
    fun k ↦ by simp [sM, inclusion_subschemeι]).2 hM

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
  · intro α β _ e hα x hx; let _ : Fintype α := Fintype.ofEquiv β e.symm
    have hx' (j : α) : x (e j) ≫ f = 𝟙 _ := hx (e j)
    have hpeq : ∏ j, (x (e j)).ker = ∏ i, (x i).ker := Fintype.prod_equiv e _ _ fun _ ↦ rfl
    have h1 := (isFullSetOfSections_subschemeι_comp_iff_of_eq hpeq (prodKerSection_comp hx')
      (fun j ↦ prodKerSection_comp hx (e j)) fun j ↦ by simp [prodKerSection_subschemeι]).1
      (hα (fun j ↦ x (e j)) hx')
    exact (isFullSetOfSections_iff_of_equiv ((∏ i, (x i).ker).subschemeι ≫ f) (prodKerSection x)
      (prodKerSection_comp hx) (fun j ↦ prodKerSection_comp hx (e j)) e fun _ ↦ rfl).1 h1
  · intro x hx; let D₀ := ∏ k : PEmpty, (x k).ker; have := isFinite_prod_ker hx
    have hD₀ : D₀ = ⊤ := Finset.prod_empty.trans one_eq_top
    have : IsEmpty D₀.subscheme := hD₀ ▸ inferInstance
    rw [isFullSetOfSections_iff_sectionTopAlgHom_of_isAffine]
    let : Algebra Γ(Spec (.of R), ⊤) Γ(D₀.subscheme, ⊤) := (D₀.subschemeι ≫ f).appTop.hom.toAlgebra
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
  have := SmoothOfRelativeDimension.smooth 1 f; let D := ∏ k, (x k).ker
  have := isFinite_prod_ker hx; have := flat_prod_ker hx
  have := locallyOfFinitePresentation_prod_ker hx
  rw [isFullSetOfSections_iff_fullSetLocus_eq_bot (D.subschemeι ≫ f)]
  refine eq_bot_of_le_ker_Spec_isLocalRing fun R _ _ t ↦ ?_
  let f' := Limits.pullback.fst t f; let pX := Limits.pullback.snd t f
  have := SmoothOfRelativeDimension.smooth 1 f'
  let x' (i : ι) := baseChangeSection f (x i) (hx i) (Over.mk t)
  have hx' (i : ι) : x' i ≫ f' = 𝟙 _ := baseChangeSection_fst f (x i) (hx i) (Over.mk t)
  have hker (i : ι) : (x' i).ker = (x i).ker.comap pX := by
    have := Scheme.Hom.isClosedImmersion_of_comp_eq_id (x i) (hx i)
    exact (IsPullback.of_hasPullback t f).flip.ker_eq_comap_of_comp_eq_id (hx i) (hx' i)
      (baseChangeSection_snd f (x i) (hx i) (Over.mk t))
  let D' := ∏ k, (x' k).ker; have hD' : D' = D.comap pX := by
    rw [comap_prod]; exact Finset.prod_congr rfl fun i _ ↦ hker i
  have H_D := isPullback_subschemeMap_of_eq hD' (IsPullback.of_hasPullback t f).flip
  have := isFinite_prod_ker hx'; have := flat_prod_ker hx'
  have := locallyOfFinitePresentation_prod_ker hx'
  have hs' (i : ι) : prodKerSection x' i ≫ subschemeMap D' D pX (hD' ▸ D.le_map_comap pX) =
      t ≫ prodKerSection x i := by
    rw [← cancel_mono D.subschemeι, Category.assoc, subschemeMap_subschemeι,
      prodKerSection_subschemeι_assoc, Category.assoc, prodKerSection_subschemeι]
    exact baseChangeSection_snd f (x i) (hx i) (Over.mk t)
  exact (fullSetLocus_le_ker_iff_of_isPullback (D.subschemeι ≫ f) (prodKerSection x)
    (prodKerSection_comp hx) H_D (prodKerSection_comp hx') hs').2
    (isFullSetOfSections_prodKerSection_of_isLocalRing x' hx')

/-! ### Full set of sections implies divisor sum -/

private lemma prod_comap_ofIdealTop_span_le_ker {Y Z W : Scheme.{u}} [IsAffine Y] (g : Z ⟶ Y)
    [IsFinite g] [Flat g] (hloc : IsLocalRing Γ(Y, ⊤)) {ι : Type*} [Fintype ι]
    {s : ι → (Y ⟶ Z)} (hs : ∀ i, s i ≫ g = 𝟙 Y) (hfull : IsFullSetOfSections g s hs) (u : Γ(Z, ⊤))
    {ℓ : W ⟶ Z} {w : W ⟶ Y} (hℓg : ℓ ≫ g = w) (hu : ofIdealTop (Ideal.span {u}) ≤ ℓ.ker) :
    ∏ i, (ofIdealTop (Ideal.span {u})).comap (s i) ≤ w.ker := by
  let : Algebra Γ(Y, ⊤) Γ(Z, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(W, ⊤) := w.appTop.hom.toAlgebra
  have : Module.Finite Γ(Y, ⊤) Γ(Z, ⊤) := g.finite_appTop; have := g.free_appTop
  have htop := (isFullSetOfSections_iff_sectionTopAlgHom_of_isAffine g s hs).1 hfull
  have hprod : (∏ i, (s i).appTop u) = ∏ i, sectionTopAlgHom g (hs i) u :=
    Finset.prod_congr rfl fun i _ ↦ (sectionTopAlgHom_apply g (hs i) u).symm
  rw [prod_comap_ofIdealTop_span_singleton s Finset.univ u, hprod, ← htop.norm_eq_prod u,
    ofIdealTop_le_ker_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  refine (ℓ.appTopAlgHom hℓg).algebraMap_norm_eq_zero_of_map_eq_zero ?_
  rw [ℓ.appTopAlgHom_apply hℓg]
  exact (ofIdealTop_le_ker_iff ℓ (Ideal.span {u})).mp hu (Ideal.mem_span_singleton_self u)

private lemma comap_prod_ker_le_comap_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)] {ι : Type*} [Fintype ι]
    {s : ι → (Spec (.of R) ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 _)
    (hfull : IsFullSetOfSections (I.subschemeι ≫ f) s hs) {δ : Spec (.of R) ⟶ X}
    (hδ : δ ≫ f = 𝟙 _) : (∏ i, (s i ≫ I.subschemeι).ker).comap δ ≤ I.comap δ := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ f)
  have := (I.subschemeι ≫ f).finite_maximalSpectrum_appTop
  have hCartier :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension δ hδ).isEffectiveCartier
  obtain ⟨u, hu⟩ := (δ.ker.comap I.subschemeι).exists_eq_ofIdealTop_span_singleton_of_stalkIdeal
    fun z ↦ by
      obtain ⟨V, hzV, α, -, hα⟩ := (isEffectiveCartier_iff δ.ker).mp hCartier (I.subschemeι z)
      refine ⟨(I.subschemeι.stalkMap z).hom ((X.presheaf.germ V.1 _ hzV).hom α), ?_⟩
      rw [δ.ker.stalkIdeal_comap, δ.ker.stalkIdeal_eq_map V _ hzV, hα, Ideal.map_span,
        Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hcomm (i : ι) :
      (s i ≫ I.subschemeι).ker.comap δ = (ofIdealTop (Ideal.span {u})).comap (s i) := by
    have hx₀ : (s i ≫ I.subschemeι) ≫ f = 𝟙 _ := by rw [Category.assoc, hs i]
    have := Scheme.Hom.isClosedImmersion_of_comp_eq_id δ hδ
    have := Scheme.Hom.isClosedImmersion_of_comp_eq_id (s i ≫ I.subschemeι) hx₀
    rw [(s i ≫ I.subschemeι).comap_ker_comm_of_comp_eq_id δ hx₀ hδ, comap_comp, hu]
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

/-- If `s` is a full set of sections of a finite locally free `V(I) ⊆ X` on a separated smooth curve
`X ⟶ S`, then `∏ i, (s i ≫ I.subschemeι).ker ≤ I`. -/
theorem prod_ker_le_of_isFullSetOfSections {I : X.IdealSheafData} [IsFinite (I.subschemeι ≫ f)]
    [Flat (I.subschemeι ≫ f)] [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    {s : ι → (S ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S)
    (hfull : IsFullSetOfSections (I.subschemeι ≫ f) s hs) :
    ∏ i, (s i ≫ I.subschemeι).ker ≤ I := by
  refine le_of_comap_Spec_isLocalRing fun R _ _ φ ↦ ?_
  let t := φ ≫ f; let f' := Limits.pullback.fst t f; let pX := Limits.pullback.snd t f
  have H : IsPullback pX f' f t := (IsPullback.of_hasPullback t f).flip
  have H_I := I.isPullback_subschemeMap_comap f H
  let _ : IsFinite ((I.comap pX).subschemeι ≫ f') := MorphismProperty.of_isPullback H_I ‹_›
  let _ : Flat ((I.comap pX).subschemeι ≫ f') := MorphismProperty.of_isPullback H_I ‹_›
  let _ : LocallyOfFinitePresentation ((I.comap pX).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback H_I ‹_›
  have hfull' := (fullSetLocus_le_ker_iff_of_isPullback (I.subschemeι ≫ f) s hs H_I
    (I.pullbackSubschemeSection_comp H s hs) (I.pullbackSubschemeSection_subschemeMap H s hs)).1
    (((isFullSetOfSections_iff_fullSetLocus_eq_bot _ _ _).1 hfull).symm ▸ bot_le)
  have hδφ : graphSection (T := Over.mk t) (Over.homMk φ rfl) ≫ pX = φ :=
    graphSection_snd (T := Over.mk t) (Over.homMk φ rfl)
  rw [← hδφ, comap_comp, comap_comp, ← I.prod_ker_pullbackSubschemeSection H s hs]
  exact comap_prod_ker_le_comap_of_isLocalRing (I.pullbackSubschemeSection_comp H s hs) hfull'
    (graphSection_fst (T := Over.mk t) (Over.homMk φ rfl))

/-- **Full set of sections implies divisor sum** (Katz–Mazur, Theorem 1.8.3, `(⇒)`). -/
theorem eq_prod_ker_of_isFullSetOfSections {I : X.IdealSheafData} [IsFinite (I.subschemeι ≫ f)]
    [Flat (I.subschemeι ≫ f)] [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    {s : ι → (S ⟶ I.subscheme)} (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S)
    (hfull : IsFullSetOfSections (I.subschemeι ≫ f) s hs) :
    I = ∏ i, (s i ≫ I.subschemeι).ker := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (i : ι) : (s i ≫ I.subschemeι) ≫ f = 𝟙 S := by rw [Category.assoc, hs i]
  have := isFinite_prod_ker hx; have := flat_prod_ker hx
  refine (eq_of_le_of_finrank_eq (prod_ker_le_of_isFullSetOfSections hs hfull) f ?_).symm
  ext p; rw [finrank_prod_ker hx p, hfull.finrank_eq_card p]

/-- **Katz–Mazur, Theorem 1.8.3** (ideal-sheaf form): on a separated smooth curve `f : X ⟶ S`,
sections `s` of a finite locally free `V(I) ⟶ S` form a full set iff
`I = ∏ i, (s i ≫ I.subschemeι).ker`. -/
theorem isFullSetOfSections_subschemeι_comp_iff {I : X.IdealSheafData}
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] {s : ι → (S ⟶ I.subscheme)}
    (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S) :
    IsFullSetOfSections (I.subschemeι ≫ f) s hs ↔ I = ∏ i, (s i ≫ I.subschemeι).ker := by
  refine ⟨eq_prod_ker_of_isFullSetOfSections hs, fun hI ↦ ?_⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (i : ι) : (s i ≫ I.subschemeι) ≫ f = 𝟙 S := by rw [Category.assoc, hs i]
  exact (isFullSetOfSections_subschemeι_comp_iff_of_eq hI hs (prodKerSection_comp hx)
    fun i ↦ (prodKerSection_subschemeι (fun k ↦ s k ≫ I.subschemeι) i).symm).2
      (isFullSetOfSections_prod_ker hx)

/-- **Uniqueness of the closed subscheme admitting a full set of sections** on a separated smooth
curve `X ⟶ S`. -/
theorem eq_of_isFullSetOfSections {I₁ I₂ : X.IdealSheafData} [IsFinite (I₁.subschemeι ≫ f)]
    [Flat (I₁.subschemeι ≫ f)] [LocallyOfFinitePresentation (I₁.subschemeι ≫ f)]
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
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] {s : ι → (S ⟶ I.subscheme)}
    (hs : ∀ i, s i ≫ (I.subschemeι ≫ f) = 𝟙 S) :
    letI : IsFinite ((∏ i, (s i ≫ I.subschemeι).ker).subschemeι ≫ f) :=
      have := SmoothOfRelativeDimension.smooth 1 f; isFinite_prod_ker fun i ↦ by simp [hs i]
    letI := flat_prod_ker (f := f) (x := fun i ↦ s i ≫ I.subschemeι) fun i ↦ by simp [hs i]
    letI := locallyOfFinitePresentation_prod_ker (f := f) (x := fun i ↦ s i ≫ I.subschemeι)
      fun i ↦ by simp [hs i]
    fullSetLocus (I.subschemeι ≫ f) s hs = equalityLocus f I (∏ i, (s i ≫ I.subschemeι).ker) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (i : ι) : (s i ≫ I.subschemeι) ≫ f = 𝟙 S := by rw [Category.assoc, hs i]
  let _ := isFinite_prod_ker hx; let _ := flat_prod_ker hx
  let _ := locallyOfFinitePresentation_prod_ker hx; let D := ∏ i, (s i ≫ I.subschemeι).ker
  refine eq_of_forall_le_ker_iff fun r ↦ ?_
  let f' := Limits.pullback.fst r f; let pX := Limits.pullback.snd r f
  have H : IsPullback pX f' f r := (IsPullback.of_hasPullback r f).flip
  have H_I := I.isPullback_subschemeMap_comap f H
  let _ : IsFinite ((I.comap pX).subschemeι ≫ f') := MorphismProperty.of_isPullback H_I ‹_›
  let _ : Flat ((I.comap pX).subschemeι ≫ f') := MorphismProperty.of_isPullback H_I ‹_›
  let _ : LocallyOfFinitePresentation ((I.comap pX).subschemeι ≫ f') :=
    MorphismProperty.of_isPullback H_I ‹_›
  rw [fullSetLocus_le_ker_iff_of_isPullback (I.subschemeι ≫ f) s hs H_I
    (I.pullbackSubschemeSection_comp H s hs) (I.pullbackSubschemeSection_subschemeMap H s hs),
    isFullSetOfSections_subschemeι_comp_iff, I.prod_ker_pullbackSubschemeSection H s hs,
    equalityLocus_le_ker_iff_of_isPullback I D H]

/-- **On a separated smooth curve, the full-set locus equals the divisor equality locus**
(closed-immersion form). -/
theorem fullSetLocus_eq_equalityLocus {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)] {s : ι → (S ⟶ Z)}
    (hs : ∀ k, s k ≫ (i ≫ f) = 𝟙 S) :
    letI : IsFinite ((∏ k, (s k ≫ i).ker).subschemeι ≫ f) :=
      have := SmoothOfRelativeDimension.smooth 1 f; isFinite_prod_ker fun k ↦ by simp [hs k]
    letI := flat_prod_ker (f := f) (x := fun k ↦ s k ≫ i) fun k ↦ by simp [hs k]
    letI := locallyOfFinitePresentation_prod_ker (f := f) (x := fun k ↦ s k ≫ i)
      fun k ↦ by simp [hs k]
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

/-- **Katz–Mazur, Theorem 1.8.3** (closed-immersion form): on a separated smooth curve `f : X ⟶ S`,
sections `s` of `i : Z ⟶ X` (`i ≫ f` finite locally free) form a full set iff
`i.ker = ∏ k, (s k ≫ i).ker`. -/
theorem isFullSetOfSections_iff_ker_eq_prod_ker {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)] {s : ι → (S ⟶ Z)}
    (hs : ∀ k, s k ≫ (i ≫ f) = 𝟙 S) :
    IsFullSetOfSections (i ≫ f) s hs ↔ i.ker = ∏ k, (s k ≫ i).ker := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have hx (k : ι) : (s k ≫ i) ≫ f = 𝟙 S := by rw [Category.assoc, hs k]
  let _ := isFinite_prod_ker hx; let _ := flat_prod_ker hx
  let _ := locallyOfFinitePresentation_prod_ker hx
  rw [isFullSetOfSections_iff_fullSetLocus_eq_bot, fullSetLocus_eq_equalityLocus i hs,
    equalityLocus_eq_bot_iff]

end MainTheorem

end TauCeti.AlgebraicGeometry
