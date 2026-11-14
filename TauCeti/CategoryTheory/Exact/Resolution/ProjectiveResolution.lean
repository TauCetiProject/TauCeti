/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.ChainComplex.Exact
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Resolution.ChainComplex
public import TauCeti.CategoryTheory.Exact.Resolution.HasFiniteResolution
public import TauCeti.CategoryTheory.Exact.Resolution.OfChainComplex
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import TauCeti.CategoryTheory.Abelian.LeftDerived

/-!
# Finite resolutions in abelian categories are projective resolutions

For the canonical exact structure of an abelian category, the conflations of a finite resolution

```text
K₁ ↪ Q₀ ↠ X,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁
```

are short exact sequences, so the spliced complex `0 ⟶ Kₙ ⟶ Qₙ₋₁ ⟶ ⋯ ⟶ Q₀` is exact in positive
degrees and its augmentation `Q₀ ⟶ X` is an epimorphism with kernel the image of `Q₁ ⟶ Q₀`.
When the resolving terms are projective, this is a projective resolution of `X` in Mathlib's
sense, bounded by the length of the resolution. This makes the recursive data produced by
dimension shifting usable with Mathlib's comparison theory of projective resolutions, which only
sees chain complexes.

Conversely, a projective resolution in Mathlib's sense whose term in degree `n + 1` vanishes is,
by `TauCeti.ExactStructure.FiniteResolution.ofChainComplex`, a finite resolution by projective
objects of length `n`, so the Euler-class and resolution-theorem API of finite resolutions applies
to it. In particular, in an abelian category with enough projectives, an object has projective
dimension at most `n` if and only if it admits a projective resolution vanishing above degree `n`.
Consequently, a right-exact additive functor preserving projective objects does not increase the
projective dimension of an `F`-acyclic object, and along an adjunction `F ⊣ G` with `G` fully
faithful and epimorphism-preserving (such as restriction of scalars along a surjective ring
homomorphism) `F`-acyclicity of `G(Y)` bounds the projective dimension of `Y` by that of `G(Y)`.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution`: a finite resolution by
  projective objects in an abelian category, as a `CategoryTheory.ProjectiveResolution`.
* `CategoryTheory.ProjectiveResolution.toFiniteResolution`: a projective resolution whose term in
  degree `n + 1` vanishes, as a finite resolution by projectives of length `n`.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.exact_d_zero_aug` and
  `TauCeti.ExactStructure.FiniteResolution.exact_d_succ_d`: the augmented complex of a finite
  resolution in an abelian category is exact.
* `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution_complex_d` and
  `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution_π_f_zero`: the projective
  resolution has the differentials and augmentation of the finite resolution, through the
  identifications `TauCeti.ExactStructure.FiniteResolution.toProjectiveResolutionXIso` of its
  terms with those of the finite resolution.
* `CategoryTheory.ProjectiveResolution.length_toFiniteResolution` and
  `CategoryTheory.ProjectiveResolution.foldAlternating_toFiniteResolution`: that finite resolution
  has length `n`, and alternating folds along it are alternating sums over the terms of degree at
  most `n`.
* `CategoryTheory.ProjectiveResolution.hasProjectiveDimensionLE` and
  `CategoryTheory.exists_projectiveResolution_of_hasProjectiveDimensionLE`: projective resolutions
  vanishing above degree `n` characterize `HasProjectiveDimensionLE X n`.
* `CategoryTheory.Functor.hasProjectiveDimensionLE_obj_of_isZero_leftDerived` and
  `CategoryTheory.Adjunction.hasProjectiveDimensionLE_of_isZero_leftDerived`: projective dimension
  bounds along right-exact projective-preserving functors and reflective adjunctions on acyclic
  objects.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti.ExactStructure.FiniteResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}

/-- The augmentation of a finite resolution in an abelian category is an epimorphism. -/
instance epi_aug {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X) : Epi r.aug := by
  cases r with
  | base hX => simpa using (inferInstance : Epi (𝟙 X))
  | step hQ i p zero hp r => simpa using ((abelian_conflation _).mp hp).epi_g

/-- The augmented complex of a finite resolution in an abelian category is exact at its
degree-zero term: the kernel of the augmentation is the image of the first differential. -/
theorem exact_d_zero_aug {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X) :
    (ShortComplex.mk (r.d 0) r.aug r.d_comp_aug).Exact := by
  cases r with
  | base hX =>
    exact (ShortComplex.exact_iff_mono _ (d_base hX 0)).2
      (by simpa using (inferInstance : Mono (𝟙 X)))
  | step hQ i p zero hp r =>
    -- Precomposing the inflation `i` with the epimorphism `r.aug` does not change its image.
    have h := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (r.aug ≫ i) p (by simp [zero]))
      (S₂ := ShortComplex.mk i p zero)
      { τ₁ := r.aug, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 ((abelian_conflation _).mp hp).exact
    simpa using h

/-- The complex of a finite resolution in an abelian category is exact in every positive
degree. -/
theorem exact_d_succ_d {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X) (n : ℕ) :
    (ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n)).Exact := by
  induction r generalizing n with
  | base hX => exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
  | step hQ i p zero hp r ih =>
    cases n with
    | zero =>
      -- Postcomposing `r.aug` with the monomorphism `i` does not change its kernel.
      have : Mono i := ((abelian_conflation _).mp hp).mono_f
      have h := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk (r.d 0) r.aug r.d_comp_aug)
        (S₂ := ShortComplex.mk (r.d 0) (r.aug ≫ i) (by simp))
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := i }).1 r.exact_d_zero_aug
      simpa using h
    | succ n => simpa using ih n

/-- The complex of a finite resolution in an abelian category is exact in every positive
degree, in the vocabulary of homological complexes. -/
theorem exactAt_toChainComplex_succ {X : C} (r : (ExactStructure.abelian C).FiniteResolution P X)
    (n : ℕ) : r.toChainComplex.ExactAt (n + 1) :=
  ChainComplex.of_exactAt_succ r.term r.d r.d_comp_d n (r.exact_d_succ_d n)

/-- The augmentation kills the first differential of the complex of a finite resolution. -/
private theorem toChainComplex_d_one_zero_comp_aug {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) : r.toChainComplex.d 1 0 ≫ r.aug = 0 := by
  rw [toChainComplex_d, d_comp_aug]

variable (hP : P ≤ isProjective C)

/-- A finite resolution by projective objects in an abelian category is a projective resolution
in Mathlib's sense: its complex is the spliced complex of the resolution, which vanishes beyond
the length, and the quasi-isomorphism to `X` is the augmentation.

The proof that the augmentation is a quasi-isomorphism follows that of Mathlib's
`CategoryTheory.ProjectiveResolution.of` in `Mathlib/CategoryTheory/Abelian/Projective/Resolution`
(by Markus Himmel, Kim Morrison, Jakob von Raumer and Joël Riou). -/
noncomputable def toProjectiveResolution {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) : ProjectiveResolution X :=
  r.toChainComplex.toProjectiveResolution r.aug r.toChainComplex_d_one_zero_comp_aug
    (fun n => by
      by_cases hn : n ≤ r.length
      · exact hP _ (r.prop_term_of_le_length hn)
      · exact (r.isZero_term_of_length_lt (not_le.mp hn)).projective)
    (ChainComplex.of_exact_d_one_zero r.term r.d r.d_comp_d r.aug r.d_comp_aug
      r.exact_d_zero_aug)
    r.exactAt_toChainComplex_succ

/-- The terms of the projective resolution are the terms of the finite resolution. -/
noncomputable def toProjectiveResolutionXIso {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) (n : ℕ) :
    (r.toProjectiveResolution hP).complex.X n ≅ r.term n :=
  Iso.refl _

/-- The projective resolution vanishes above the length of the finite resolution. -/
theorem isZero_toProjectiveResolution_X_of_length_lt {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) {n : ℕ} (hn : r.length < n) :
    IsZero ((r.toProjectiveResolution hP).complex.X n) :=
  (r.isZero_term_of_length_lt hn).of_iso (r.toProjectiveResolutionXIso hP n)

/-- The differentials of the projective resolution are those of the finite resolution, through
the identifications of the terms. -/
@[simp]
theorem toProjectiveResolution_complex_d {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) (n : ℕ) :
    (r.toProjectiveResolution hP).complex.d (n + 1) n =
      (r.toProjectiveResolutionXIso hP (n + 1)).hom ≫ r.d n ≫
        (r.toProjectiveResolutionXIso hP n).inv := by
  -- Reduction identifies the endpoints of the identity term isomorphisms before simp can
  -- apply category laws; rewriting just the complex projection leaves an ill-typed simp goal.
  simp [toProjectiveResolutionXIso, toProjectiveResolution, ChainComplex.toProjectiveResolution]

/-- The augmentation of the projective resolution is that of the finite resolution, through the
identification of the degree-zero terms. -/
@[simp]
theorem toProjectiveResolution_π_f_zero {X : C}
    (r : (ExactStructure.abelian C).FiniteResolution P X) :
    (r.toProjectiveResolution hP).π.f 0 = (r.toProjectiveResolutionXIso hP 0).hom ≫ r.aug := by
  -- As above, the identity's endpoints need reduction before the augmentation lemma applies.
  simpa [toProjectiveResolutionXIso, toProjectiveResolution,
    ChainComplex.toProjectiveResolution] using
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := r.toChainComplex) r.aug
      r.toChainComplex_d_one_zero_comp_aug

end TauCeti.ExactStructure.FiniteResolution

namespace CategoryTheory.ProjectiveResolution

open TauCeti TauCeti.ExactStructure

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- The augmentation of a projective resolution, as a morphism to `X`, is an epimorphism. -/
private instance epi_toSingle₀Equiv (R : ProjectiveResolution X) :
    Epi (ChainComplex.toSingle₀Equiv _ X R.π).1 :=
  inferInstanceAs (Epi (R.π.f 0))

/-- A projective resolution whose term in degree `n + 1` vanishes, as a finite resolution of
length `n` by projective objects for the canonical exact structure. Only that single term needs
to vanish: the terms above `n + 1` are not constrained. -/
noncomputable def toFiniteResolution (R : ProjectiveResolution X) {n : ℕ}
    (hn : IsZero (R.complex.X (n + 1))) :
    (ExactStructure.abelian C).FiniteResolution (isProjective C) X :=
  FiniteResolution.ofChainComplex (hε := (ChainComplex.toSingle₀Equiv _ X R.π).2) R.exact₀
    (fun i _ => R.exact_succ i) hn (fun i _ => R.projective i)

/-- The finite resolution of a projective resolution with vanishing term in degree `n + 1` has
length `n`. -/
@[simp]
theorem length_toFiniteResolution (R : ProjectiveResolution X) {n : ℕ}
    (hn : IsZero (R.complex.X (n + 1))) : (R.toFiniteResolution hn).length = n :=
  FiniteResolution.length_ofChainComplex _ _ _ _

/-- Alternating sums along the finite resolution of a projective resolution with vanishing term in
degree `n + 1` are the alternating sums over its terms of degree at most `n`. -/
theorem foldAlternating_toFiniteResolution (R : ProjectiveResolution X) {n : ℕ}
    (hn : IsZero (R.complex.X (n + 1))) {A : Type*} [AddCommGroup A]
    (f : ∀ Z : C, isProjective C Z → A)
    (hf : ∀ {Y Z : C} (_ : Y ≅ Z) (hY : isProjective C Y) (hZ : isProjective C Z),
      f Y hY = f Z hZ) :
    (R.toFiniteResolution hn).foldAlternating f =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (R.complex.X i) (R.projective i) :=
  FiniteResolution.foldAlternating_ofChainComplex _ _ _ _ f hf

/-- A projective resolution whose term in degree `n + 1` vanishes witnesses that the resolved
object has projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE (R : ProjectiveResolution X) {n : ℕ}
    (hn : IsZero (R.complex.X (n + 1))) : HasProjectiveDimensionLE X n :=
  (R.length_toFiniteResolution hn ▸
    (R.toFiniteResolution hn).hasFiniteResolutionOfLength).hasProjectiveDimensionLE

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory

open TauCeti.ExactStructure

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]

/-- In an abelian category with enough projectives, an object of projective dimension at most `n`
admits a projective resolution whose terms vanish above degree `n`. -/
theorem exists_projectiveResolution_of_hasProjectiveDimensionLE {X : C} {n : ℕ}
    (hX : HasProjectiveDimensionLE X n) :
    ∃ P : ProjectiveResolution X, ∀ i, n < i → IsZero (P.complex.X i) := by
  obtain ⟨r, rfl⟩ := exists_finiteResolution_isProjective_length_eq_iff.mpr hX
  exact ⟨r.toProjectiveResolution le_rfl,
    fun _ hi ↦ r.isZero_toProjectiveResolution_X_of_length_lt le_rfl hi⟩

/-- In an abelian category with enough projectives, an object has projective dimension at most `n`
if and only if it admits a projective resolution vanishing above degree `n`. -/
theorem exists_projectiveResolution_isZero_X_iff_hasProjectiveDimensionLE {X : C} {n : ℕ} :
    (∃ P : ProjectiveResolution X, ∀ i, n < i → IsZero (P.complex.X i)) ↔
      HasProjectiveDimensionLE X n :=
  ⟨fun ⟨P, hP⟩ ↦ P.hasProjectiveDimensionLE (hP (n + 1) (Nat.lt_succ_self n)),
    exists_projectiveResolution_of_hasProjectiveDimensionLE⟩

section LeftDerived

omit [EnoughProjectives C]
variable [HasProjectiveResolutions C] {D : Type*} [Category* D] [Abelian D]

/-- A right-exact additive functor `F` preserving projective objects does not increase the
projective dimension of an `F`-acyclic object. -/
theorem Functor.hasProjectiveDimensionLE_obj_of_isZero_leftDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] {X : C}
    (h : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X)) {m : ℕ}
    (hX : HasProjectiveDimensionLE X m) :
    HasProjectiveDimensionLE (F.obj X) m := by
  have : EnoughProjectives C :=
    ⟨fun Z ↦ ⟨{ p := (projectiveResolution Z).complex.X 0
                projective := (projectiveResolution Z).projective 0
                f := (projectiveResolution Z).π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 Z).hom
                epi := inferInstance }⟩⟩
  obtain ⟨P, hP⟩ := exists_projectiveResolution_of_hasProjectiveDimensionLE hX
  exact (P.mapOfIsZeroLeftDerived F h).hasProjectiveDimensionLE
    (F.map_isZero (hP (m + 1) (Nat.lt_succ_self m)))

/-- Strict projective-dimension bound for a right-exact additive functor preserving projective
objects on an `F`-acyclic object. -/
theorem Functor.hasProjectiveDimensionLT_obj_of_isZero_leftDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] {X : C}
    (h : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X)) {n : ℕ}
    (hX : HasProjectiveDimensionLT X n) :
    HasProjectiveDimensionLT (F.obj X) n := by
  cases n with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero] at hX ⊢
    exact F.map_isZero hX
  | succ m => exact F.hasProjectiveDimensionLE_obj_of_isZero_leftDerived h hX

/-- A right-exact additive functor preserving projective objects satisfies
`projectiveDimension (F.obj X) ≤ projectiveDimension X` when `Lₙ₊₁F(X) = 0` for all `n`. -/
theorem Functor.projectiveDimension_le_obj_of_isZero_leftDerived (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] {X : C}
    (h : ∀ n, IsZero ((F.leftDerived (n + 1)).obj X)) :
    projectiveDimension (F.obj X) ≤ projectiveDimension X :=
  sInf_le_sInf_of_subset_insert_top fun n hn ↦ by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    exact fun i hi ↦ F.hasProjectiveDimensionLT_obj_of_isZero_leftDerived h (hn i hi)

/-- Given an adjunction `F ⊣ G` with `G` fully faithful and preserving epimorphisms, if `G(Y)` is
`F`-acyclic (`Lₙ₊₁F(G(Y)) = 0` for all `n`) and has projective dimension at most `m`, then `Y` has
projective dimension at most `m`. -/
theorem Adjunction.hasProjectiveDimensionLE_of_isZero_leftDerived {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [G.Full] [G.Faithful] [G.PreservesEpimorphisms] {Y : D}
    (h : ∀ n, IsZero ((F.leftDerived (n + 1)).obj (G.obj Y))) {m : ℕ}
    (hY : HasProjectiveDimensionLE (G.obj Y) m) :
    HasProjectiveDimensionLE Y m := by
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  have := Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms adj
  have : HasProjectiveDimensionLT ((G ⋙ F).obj Y) (m + 1) :=
    F.hasProjectiveDimensionLE_obj_of_isZero_leftDerived h hY
  exact hasProjectiveDimensionLT_of_iso (asIso (adj.counit.app Y)) (m + 1)

/-- Strict projective-dimension bound along an adjunction `F ⊣ G` with `G` fully faithful and
epimorphism-preserving on an object `Y` whose image `G(Y)` is `F`-acyclic. -/
theorem Adjunction.hasProjectiveDimensionLT_of_isZero_leftDerived {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [G.Full] [G.Faithful] [G.PreservesEpimorphisms] {Y : D}
    (h : ∀ n, IsZero ((F.leftDerived (n + 1)).obj (G.obj Y))) {n : ℕ}
    (hY : HasProjectiveDimensionLT (G.obj Y) n) :
    HasProjectiveDimensionLT Y n := by
  cases n with
  | zero =>
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    rw [hasProjectiveDimensionLT_zero_iff_isZero] at hY ⊢
    exact (F.map_isZero hY).of_iso (asIso (adj.counit.app Y)).symm
  | succ m => exact adj.hasProjectiveDimensionLE_of_isZero_leftDerived h hY

/-- Given an adjunction `F ⊣ G` with `G` fully faithful and epimorphism-preserving, if
`Lₙ₊₁F(G(Y)) = 0` for all `n`, then `projectiveDimension Y ≤ projectiveDimension (G.obj Y)`. -/
theorem Adjunction.projectiveDimension_le_of_isZero_leftDerived {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [G.Full] [G.Faithful] [G.PreservesEpimorphisms] {Y : D}
    (h : ∀ n, IsZero ((F.leftDerived (n + 1)).obj (G.obj Y))) :
    projectiveDimension Y ≤ projectiveDimension (G.obj Y) :=
  sInf_le_sInf_of_subset_insert_top fun n hn ↦ by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    exact fun i hi ↦ adj.hasProjectiveDimensionLT_of_isZero_leftDerived h (hn i hi)

end LeftDerived

end CategoryTheory
