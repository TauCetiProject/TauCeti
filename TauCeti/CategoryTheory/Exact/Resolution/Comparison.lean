/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.CategoryTheory.Exact.Projective
public import TauCeti.CategoryTheory.Exact.Resolution.ChainComplex

/-!
# The comparison theorem for finite projective resolutions

Let `r` be a finite resolution of `X` in an exact category whose resolving terms are relatively
projective, and let `r'` be any finite resolution of `Y`. Every morphism `f : X ⟶ Y` lifts to a
chain map between the complexes of the two resolutions compatible with the augmentations, and any
two such lifts are chain homotopic. The lift is built one conflation at a time: a projective term
`Qₙ` lifts along the deflation `Q'ₙ ↠ K'ₙ`, and the induced map on the kernels `Kₙ₊₁ ⟶ K'ₙ₊₁` is
the input to the next step. The homotopy is built the same way, after subtracting the part of the
chain map already accounted for.

Consequently any two finite projective resolutions of the same object are homotopy equivalent,
and the resolution is unique up to chain homotopy. This is the relative version of Mathlib's
`CategoryTheory.ProjectiveResolution.lift`, `liftHomotopyZero` and `homotopyEquiv` for abelian
categories: the ambient category need not have kernels or cokernels, and exactness is the
exact-structure datum rather than Mathlib's `ShortComplex.Exact`.

The uniqueness also makes the comparison map functorial: the image of a lift under a
conflation-exact functor is again a lift, so it is homotopic to the lift between the image
resolutions. Applied to the grading shift of a graded exact category, this is the graded
comparison theorem.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.lift`: the chain map lifting `f : X ⟶ Y` from a finite
  projective resolution of `X` to a finite resolution of `Y`.
* `TauCeti.ExactStructure.FiniteResolution.liftHomotopyZero`: a chain map from a finite projective
  resolution to a finite resolution which vanishes against the augmentation is null-homotopic.
* `TauCeti.ExactStructure.FiniteResolution.liftHomotopy`: two lifts of the same morphism are
  homotopic.
* `TauCeti.ExactStructure.FiniteResolution.liftIdHomotopy` and
  `TauCeti.ExactStructure.FiniteResolution.liftCompHomotopy`: the lift of an identity is
  homotopic to the identity, and the lift of a composite to the composite of the lifts.
* `TauCeti.ExactStructure.FiniteResolution.homotopyEquiv`: two finite projective resolutions of
  the same object are homotopy equivalent.
* `TauCeti.ExactStructure.FiniteResolution.liftMapHomotopy`: the comparison map is functorial
  up to homotopy along conflation-exact functors preserving the projective terms.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.lift_f_zero_comp_aug`: the lift is compatible with
  the augmentations, `(lift f).f 0 ≫ aug' = aug ≫ f`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 12,
  for the comparison theorem for projective resolutions in a Quillen exact category.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994),
  Theorem 2.2.6, the comparison theorem, and Section 2.2 for its proof by induction along the
  resolution.
* `Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean`, whose `lift`, `liftHomotopyZero`,
  `liftHomotopy`, `liftIdHomotopy`, `liftCompHomotopy` and `homotopyEquiv` API for projective
  resolutions in abelian categories is followed here.
* `Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean`, whose
  `CategoryTheory.Functor.mapProjectiveResolution` is the abelian counterpart of the image of a
  resolution under a functor used in `liftMapHomotopy`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {P P' P'' : ObjectProperty C}

namespace FiniteResolution

section Lift

/-- The components of the lift of `f : X ⟶ Y` along two resolutions, with the compatibility with
the augmentations and the differentials. The recursion is on the projective resolution of `X`:
its first term lifts along the augmentation of the resolution of `Y`, and the induced map on the
kernels is lifted recursively. -/
private noncomputable def liftAux (hP : P ≤ E.isProjective) :
    ∀ {X Y : C} (r : FiniteResolution E P X) (r' : FiniteResolution E P' Y) (f : X ⟶ Y),
      { g : ∀ n, r.term n ⟶ r'.term n //
        g 0 ≫ r'.aug = r.aug ≫ f ∧ ∀ n, g (n + 1) ≫ r'.d n = r.d n ≫ g n }
  | _, _, .base hX, r', f =>
      ⟨fun n => match n with
        | 0 => (hP _ hX).factorThru r'.isDeflation_aug f
        | _ + 1 => 0,
       by simp, fun n => by simp⟩
  | _, _, .step hQ i p zero hp r, .base hY, f =>
      ⟨fun n => match n with
        | 0 => p ≫ f
        | _ + 1 => 0,
       by simp, fun n => match n with
        | 0 => by simp [reassoc_of% zero]
        | _ + 1 => by simp⟩
  | _, _, .step hQ i p zero hp r, .step hQ' i' p' zero' hp' r', f =>
      let g₀ := (hP _ hQ).factorThru (E.isDeflation_g hp') (p ≫ f)
      have hg₀ : g₀ ≫ p' = p ≫ f := (hP _ hQ).factorThru_comp _ _
      let u := (E.isKernelCokernelPair _ hp').lift (i ≫ g₀)
        (by rw [Category.assoc, hg₀, ← Category.assoc, zero, zero_comp])
      have hu : u ≫ i' = i ≫ g₀ := (E.isKernelCokernelPair _ hp').lift_f _ _
      let g := liftAux hP r r' u
      ⟨fun n => match n with
        | 0 => g₀
        | n + 1 => g.1 n,
       by simpa using hg₀, fun n => match n with
        | 0 => by simp [reassoc_of% g.2.1, hu]
        | n + 1 => by simpa using g.2.2 n⟩

/-- **The comparison map.** The chain map lifting `f : X ⟶ Y` from a finite resolution `r` of
`X` by relative projectives to any finite resolution `r'` of `Y`, compatible with the two
augmentations. -/
noncomputable def lift (hP : P ≤ E.isProjective) {X Y : C} (f : X ⟶ Y) (r : FiniteResolution E P X)
    (r' : FiniteResolution E P' Y) : r.toChainComplex ⟶ r'.toChainComplex :=
  ChainComplex.ofHom (liftAux hP r r' f).1 fun n => by simpa using (liftAux hP r r' f).2.2 n

/-- The lift is compatible with the augmentations. -/
@[reassoc (attr := simp)]
theorem lift_f_zero_comp_aug (hP : P ≤ E.isProjective) {X Y : C} (f : X ⟶ Y)
    (r : FiniteResolution E P X)
    (r' : FiniteResolution E P' Y) : (lift hP f r r').f 0 ≫ r'.aug = r.aug ≫ f :=
  (liftAux hP r r' f).2.1

end Lift

section Homotopy

/-- The components of a null-homotopy of a family of maps between the complexes of two
resolutions which commutes with the differentials and vanishes against the augmentation. The
recursion is on the projective resolution: the degree-zero component is lifted along the
augmentation of the second resolution, and the family corrected by it is null-homotoped
recursively one degree down. -/
private noncomputable def liftHomotopyZeroAux (hP : P ≤ E.isProjective) :
    ∀ {X Y : C} (r : FiniteResolution E P X) (r' : FiniteResolution E P' Y)
      (φ : ∀ n, r.term n ⟶ r'.term n), (∀ n, φ (n + 1) ≫ r'.d n = r.d n ≫ φ n) →
      φ 0 ≫ r'.aug = 0 →
      { h : ∀ n, r.term n ⟶ r'.term (n + 1) //
        φ 0 = h 0 ≫ r'.d 0 ∧ ∀ n, φ (n + 1) = r.d n ≫ h n + h (n + 1) ≫ r'.d (n + 1) }
  | _, _, _, .base _, φ, _, hφ =>
      ⟨fun _ => 0, by simpa using hφ, fun n => (isZero_zero C).eq_of_tgt _ _⟩
  | _, _, .base hX, .step hQ' i' p' zero' hp' r', φ, _, hφ =>
      let u := (E.isKernelCokernelPair _ hp').lift (φ 0) (by simpa using hφ)
      have hu : u ≫ i' = φ 0 := (E.isKernelCokernelPair _ hp').lift_f _ _
      ⟨fun n => match n with
        | 0 => (hP _ hX).factorThru r'.isDeflation_aug u
        | _ + 1 => 0,
       by simp [hu], fun n => (isZero_zero C).eq_of_src _ _⟩
  | _, _, .step hQ i p zero hp r, .step hQ' i' p' zero' hp' r', φ, hcomm, hφ =>
      let u := (E.isKernelCokernelPair _ hp').lift (φ 0) (by simpa using hφ)
      have hu : u ≫ i' = φ 0 := (E.isKernelCokernelPair _ hp').lift_f _ _
      let h₀ := (hP _ hQ).factorThru r'.isDeflation_aug u
      have hh₀ : h₀ ≫ r'.aug = u := (hP _ hQ).factorThru_comp _ _
      -- the family one degree down, corrected by the degree-zero component of the homotopy
      let φ' : ∀ n, r.term n ⟶ r'.term n := fun n => match n with
        | 0 => φ 1 - (r.aug ≫ i) ≫ h₀
        | n + 1 => φ (n + 2)
      have hcomm' : ∀ n, φ' (n + 1) ≫ r'.d n = r.d n ≫ φ' n := fun n => match n with
        | 0 => by
            have := hcomm 1
            simp only [d_step_succ] at this
            simp [φ', Preadditive.comp_sub, this]
        | n + 1 => by simpa [φ'] using hcomm (n + 2)
      have hφ' : φ' 0 ≫ r'.aug = 0 := by
        have := (E.isKernelCokernelPair _ hp').mono_f
        have h₁ := hcomm 0
        simp only [d_step_zero, Category.assoc] at h₁
        rw [← cancel_mono i', zero_comp, Category.assoc]
        simp [φ', Preadditive.sub_comp, reassoc_of% hh₀, hu, h₁]
      let H := liftHomotopyZeroAux hP r r' φ' hcomm' hφ'
      ⟨fun n => match n with
        | 0 => h₀
        | n + 1 => H.1 n,
       by simp [reassoc_of% hh₀, hu], fun n => match n with
        | 0 => by
            have := H.2.1
            simp only [φ'] at this
            rw [sub_eq_iff_eq_add'] at this
            simpa using this
        | n + 1 => by simpa [φ'] using H.2.2 n⟩

/-- A chain map from the complex of a finite projective resolution to the complex of a finite
resolution which vanishes against the augmentation is null-homotopic. -/
noncomputable def liftHomotopyZero (hP : P ≤ E.isProjective) {X Y : C} {r : FiniteResolution E P X}
    {r' : FiniteResolution E P' Y} (φ : r.toChainComplex ⟶ r'.toChainComplex)
    (hφ : φ.f 0 ≫ r'.aug = 0) : Homotopy φ 0 :=
  let H := liftHomotopyZeroAux hP r r' (fun n => φ.f n)
    (fun n => by simpa using φ.comm (n + 1) n) hφ
  Homotopy.mkChainComplex φ H.1 (by rw [toChainComplex_d]; exact H.2.1) fun n => by
    rw [toChainComplex_d, toChainComplex_d]
    exact H.2.2 n

/-- Two lifts of the same morphism are homotopic. -/
noncomputable def liftHomotopy (hP : P ≤ E.isProjective) {X Y : C} (f : X ⟶ Y)
    {r : FiniteResolution E P X}
    {r' : FiniteResolution E P' Y} (φ ψ : r.toChainComplex ⟶ r'.toChainComplex)
    (hφ : φ.f 0 ≫ r'.aug = r.aug ≫ f) (hψ : ψ.f 0 ≫ r'.aug = r.aug ≫ f) : Homotopy φ ψ :=
  Homotopy.equivSubZero.symm (liftHomotopyZero hP (φ - ψ) (by simp [Preadditive.sub_comp, hφ, hψ]))

/-- The lift of the identity is homotopic to the identity chain map. -/
noncomputable def liftIdHomotopy (hP : P ≤ E.isProjective) {X : C} (r : FiniteResolution E P X) :
    Homotopy (lift hP (𝟙 X) r r) (𝟙 r.toChainComplex) :=
  liftHomotopy hP (𝟙 X) _ _ (by simp) (by simp)

/-- The lift of a composite is homotopic to the composite of the lifts. -/
noncomputable def liftCompHomotopy (hP : P ≤ E.isProjective) (hP' : P' ≤ E.isProjective)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r : FiniteResolution E P X) (r' : FiniteResolution E P' Y)
    (r'' : FiniteResolution E P'' Z) :
    Homotopy (lift hP (f ≫ g) r r'') (lift hP f r r' ≫ lift hP' g r' r'') :=
  liftHomotopy hP (f ≫ g) _ _ (by simp) (by simp)

/-- **Uniqueness of finite projective resolutions up to homotopy.** Two finite resolutions of
the same object by relative projectives have homotopy equivalent complexes. -/
noncomputable def homotopyEquiv (hP : P ≤ E.isProjective) (hP' : P' ≤ E.isProjective) {X : C}
    (r : FiniteResolution E P X) (r' : FiniteResolution E P' X) :
    HomotopyEquiv r.toChainComplex r'.toChainComplex where
  hom := lift hP (𝟙 X) r r'
  inv := lift hP' (𝟙 X) r' r
  homotopyHomInvId := (liftCompHomotopy hP hP' (𝟙 X) (𝟙 X) r r' r).symm.trans
    (by simpa using liftIdHomotopy hP r)
  homotopyInvHomId := (liftCompHomotopy hP' hP (𝟙 X) (𝟙 X) r' r r').symm.trans
    (by simpa using liftIdHomotopy hP' r')

@[reassoc (attr := simp)]
theorem homotopyEquiv_hom_f_zero_comp_aug (hP : P ≤ E.isProjective) (hP' : P' ≤ E.isProjective)
    {X : C} (r : FiniteResolution E P X) (r' : FiniteResolution E P' X) :
    (homotopyEquiv hP hP' r r').hom.f 0 ≫ r'.aug = r.aug := by
  simp [homotopyEquiv]

@[reassoc (attr := simp)]
theorem homotopyEquiv_inv_f_zero_comp_aug (hP : P ≤ E.isProjective) (hP' : P' ≤ E.isProjective)
    {X : C} (r : FiniteResolution E P X) (r' : FiniteResolution E P' X) :
    (homotopyEquiv hP hP' r r').inv.f 0 ≫ r.aug = r'.aug := by
  simp [homotopyEquiv]

end Homotopy

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E' : ExactStructure D} {Q Q' : ObjectProperty D} {F : C ⥤ D} [F.Additive]

/-- **Functoriality of the comparison map.** Let `F` be a conflation-exact functor carrying the
relative projectives of `P` into relative projectives of `Q`. The lift of `F f` between the images
of two resolutions is homotopic to the image of the lift of `f`, transported along the
identifications `TauCeti.ExactStructure.FiniteResolution.toChainComplexMapIso` of the complexes
of the image resolutions with the images of the complexes. -/
noncomputable def liftMapHomotopy (hP : P ≤ E.isProjective) (hQ : Q ≤ E'.isProjective)
    (hF : E.IsConflationExact E' F) (hPQ : P ≤ Q.inverseImage F) (hP'Q' : P' ≤ Q'.inverseImage F)
    {X Y : C} (f : X ⟶ Y) (r : FiniteResolution E P X) (r' : FiniteResolution E P' Y) :
    Homotopy (lift hQ (F.map f) (r.map hF hPQ) (r'.map hF hP'Q'))
      ((toChainComplexMapIso hF hPQ r).hom ≫ (F.mapHomologicalComplex _).map (lift hP f r r') ≫
        (toChainComplexMapIso hF hP'Q' r').inv) :=
  liftHomotopy hQ (F.map f) _ _ (lift_f_zero_comp_aug ..) (by
    simp only [HomologicalComplex.comp_f, toChainComplexMapIso_hom_f,
      Functor.mapHomologicalComplex_map_f, toChainComplexMapIso_inv_f, Category.assoc,
      Iso.inv_hom_id_assoc, aug_map]
    rw [← F.map_comp, ← F.map_comp, lift_f_zero_comp_aug])

end Map

end FiniteResolution

end ExactStructure

end TauCeti
