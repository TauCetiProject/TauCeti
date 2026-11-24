/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# The horseshoe lemma for injective resolutions

Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence `S` in an abelian category, and let `I₁` and
`I₃` be injective resolutions of `A` and `C`. The horseshoe lemma builds an injective resolution
`I₁.horseshoe I₃ hS` of `B` whose term in degree `n` is the biproduct `I₁ⁿ ⊞ I₃ⁿ`, together with
chain maps `I₁ ⟶ I₂ ⟶ I₃` (the inclusion of and the projection to the biproduct factors in each
degree) that are compatible with the augmentations and form a split short exact sequence in every
degree. No supply of injective objects is needed: the construction only lifts into the given
injective terms of `I₁`.

The differential of the middle resolution is `(u, v) ↦ (d u + t v, d v)`, for twisting maps
`tⁿ : I₃ⁿ ⟶ I₁ⁿ⁺¹` (`CategoryTheory.InjectiveResolution.horseshoeTwist`), and its augmentation is
`b ↦ (e b, ε₃ (g b))`, where `ε₃ : C ⟶ I₃⁰` is the augmentation of `I₃` and `e : B ⟶ I₁⁰` extends
the augmentation of `I₁` along `A ⟶ B`
(`CategoryTheory.InjectiveResolution.horseshoeExtension`). The twisting maps are chosen by
induction, using that the terms of `I₁` are injective and that `I₃` is exact: `t⁰` is chosen so that
the augmentation is a chain map (`S.g ≫ ε₃ ≫ t⁰ = -(e ≫ d)`), and `tⁿ⁺¹` so that the differential
squares to zero (`d ≫ tⁿ⁺¹ = -(tⁿ ≫ d)`). The augmentation is a quasi-isomorphism because the
outer ones are and the two rows `A[0] ⟶ B[0] ⟶ C[0]` and `I₁ ⟶ I₂ ⟶ I₃` are short exact
(`HomologicalComplex.HomologySequence.quasiIso_τ₂`).

Tau Ceti's projective horseshoe lemmas for exact categories
(`TauCeti.ExactStructure.ProjectiveResolution.horseshoe` and its finite and complete variants)
work with the resolutions of an exact structure; this file works directly with Mathlib's
`CategoryTheory.InjectiveResolution`, the carrier of injective resolutions in an abelian category
and of right derived functors.

Horseshoe resolutions are the step from injective resolutions of objects to the Cartan–Eilenberg
resolutions of complexes, which resolve the short exact sequences relating the cycles, boundaries
and cohomology of a complex compatibly.

## Main definitions and results

* `CategoryTheory.InjectiveResolution.horseshoe`: the horseshoe resolution of the middle term.
* `CategoryTheory.InjectiveResolution.horseshoeShortComplex`: the sequence `I₁ ⟶ I₂ ⟶ I₃`, which is
  short exact (`CategoryTheory.InjectiveResolution.horseshoeShortComplex_shortExact`) and split in
  every degree (`CategoryTheory.InjectiveResolution.horseshoeSplitting`).
* `CategoryTheory.ShortComplex.ShortExact.exists_injectiveResolution_horseshoe`: the horseshoe
  lemma as an existence statement.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Horseshoe Lemma 2.2.8 and its dual.
* The Stacks Project, Derived Categories, Lemma 18.9 (tag 013T).
-/

public section

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory.InjectiveResolution

open CochainComplex HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}
  (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃) (hS : S.ShortExact)

/-- An extension `S.X₂ ⟶ I₁⁰` of the augmentation `S.X₁ ⟶ I₁⁰` along the monomorphism `S.f`. It is
the first component of the augmentation of the horseshoe resolution. -/
def horseshoeExtension : S.X₂ ⟶ I₁.cocomplex.X 0 :=
  have := hS.mono_f
  Injective.factorThru I₁.ι₀ S.f

/-- `I₁.horseshoeExtension hS` extends the augmentation of `I₁` along `S.f`. -/
@[reassoc (attr := simp)]
lemma comp_horseshoeExtension : S.f ≫ I₁.horseshoeExtension hS = I₁.ι₀ :=
  have := hS.mono_f
  Injective.comp_factorThru _ _

/-- The first twisting map `I₃⁰ ⟶ I₁¹`, which makes the augmentation of the horseshoe
resolution a chain map. -/
private def horseshoeTwistZero : I₃.cocomplex.X 0 ⟶ I₁.cocomplex.X 1 :=
  have := hS.epi_g
  Injective.factorThru
    (hS.exact.desc (-(I₁.horseshoeExtension hS ≫ I₁.cocomplex.d 0 1)) (by simp)) I₃.ι₀

private lemma comp_horseshoeTwistZero :
    S.g ≫ I₃.ι₀ ≫ horseshoeTwistZero I₁ I₃ hS =
      -(I₁.horseshoeExtension hS ≫ I₁.cocomplex.d 0 1) := by
  have := hS.epi_g
  simp [horseshoeTwistZero]

/-- The second twisting map `I₃¹ ⟶ I₁²`, which starts the induction. -/
private def horseshoeTwistOne : I₃.cocomplex.X 1 ⟶ I₁.cocomplex.X 2 :=
  I₃.exact_ι₀.descToInjective (-(horseshoeTwistZero I₁ I₃ hS ≫ I₁.cocomplex.d 1 2)) (by
    have := hS.epi_g
    rw [← cancel_epi S.g]
    simp [reassoc_of% comp_horseshoeTwistZero])

/-- The pairs of consecutive twisting maps `(tⁿ, tⁿ⁺¹)` with `d ≫ tⁿ⁺¹ = -(tⁿ ≫ d)`, constructed
by induction on `n`. -/
private def horseshoeTwistAux : (n : ℕ) →
    Σ' (a : I₃.cocomplex.X n ⟶ I₁.cocomplex.X (n + 1))
      (b : I₃.cocomplex.X (n + 1) ⟶ I₁.cocomplex.X (n + 2)),
      I₃.cocomplex.d n (n + 1) ≫ b = -(a ≫ I₁.cocomplex.d (n + 1) (n + 2))
  | 0 => ⟨horseshoeTwistZero I₁ I₃ hS, horseshoeTwistOne I₁ I₃ hS,
      I₃.exact_ι₀.comp_descToInjective _ _⟩
  | n + 1 =>
      let p := horseshoeTwistAux n
      ⟨p.2.1, (I₃.exact_succ n).descToInjective (-(p.2.1 ≫ I₁.cocomplex.d (n + 2) (n + 3)))
          (by
            dsimp
            rw [Preadditive.comp_neg, ← Category.assoc, p.2.2]
            simp),
        (I₃.exact_succ n).comp_descToInjective _ _⟩

/-- The twisting maps `tⁿ : I₃ⁿ ⟶ I₁ⁿ⁺¹` of the horseshoe resolution, whose differential is
`(u, v) ↦ (d u + t v, d v)` on `I₁ⁿ ⊞ I₃ⁿ`. They are one choice, made through the
injectivity of the terms of `I₁`, among many maps satisfying
`CategoryTheory.InjectiveResolution.comp_horseshoeTwist_zero` and
`CategoryTheory.InjectiveResolution.d_comp_horseshoeTwist`. -/
def horseshoeTwist (n : ℕ) : I₃.cocomplex.X n ⟶ I₁.cocomplex.X (n + 1) :=
  (horseshoeTwistAux I₁ I₃ hS n).1

/-- The first twisting map makes the augmentation `b ↦ (e b, ε₃ (g b))` a chain map. -/
@[reassoc]
lemma comp_horseshoeTwist_zero :
    S.g ≫ I₃.ι₀ ≫ I₁.horseshoeTwist I₃ hS 0 =
      -(I₁.horseshoeExtension hS ≫ I₁.cocomplex.d 0 1) :=
  comp_horseshoeTwistZero I₁ I₃ hS

/-- The twisting maps make the differential of the horseshoe resolution square to zero. -/
@[reassoc]
lemma d_comp_horseshoeTwist (n : ℕ) :
    I₃.cocomplex.d n (n + 1) ≫ I₁.horseshoeTwist I₃ hS (n + 1) =
      -(I₁.horseshoeTwist I₃ hS n ≫ I₁.cocomplex.d (n + 1) (n + 2)) :=
  -- the second component of the pair at `n` is by construction the first component at `n + 1`
  (horseshoeTwistAux I₁ I₃ hS n).2.2

/-- The complex of the horseshoe resolution: its term in degree `n` is `I₁ⁿ ⊞ I₃ⁿ`, and its
differential is `(u, v) ↦ (d u + t v, d v)` for the twisting maps
`t = I₁.horseshoeTwist I₃ hS`.

This is an abbreviation, as is `CochainComplex.of`, so that its terms are reducibly the
biproducts: the statements of `CategoryTheory.InjectiveResolution.horseshoeInl_f` and its
companions use this, and the biproduct lemmas apply to its terms. -/
abbrev horseshoeCocomplex : CochainComplex C ℕ :=
  CochainComplex.of (fun n ↦ I₁.cocomplex.X n ⊞ I₃.cocomplex.X n)
    (fun n ↦ biprod.lift
      (biprod.fst ≫ I₁.cocomplex.d n (n + 1) + biprod.snd ≫ I₁.horseshoeTwist I₃ hS n)
      (biprod.snd ≫ I₃.cocomplex.d n (n + 1)))
    (fun n ↦ by
      -- on `I₃ⁿ`, the first component of `d ∘ d` is `t ∘ d + d ∘ t`; the index `n + 1 + 1` is the
      -- one produced by `CochainComplex.of`
      have h : I₃.cocomplex.d n (n + 1) ≫ I₁.horseshoeTwist I₃ hS (n + 1) =
          -(I₁.horseshoeTwist I₃ hS n ≫ I₁.cocomplex.d (n + 1) (n + 1 + 1)) :=
        I₁.d_comp_horseshoeTwist I₃ hS n
      ext <;> simp [h])

/-- The differential of the horseshoe complex is `(u, v) ↦ (d u + t v, d v)`. -/
lemma horseshoeCocomplex_d (n : ℕ) :
    (I₁.horseshoeCocomplex I₃ hS).d n (n + 1) =
      biprod.lift
        (biprod.fst ≫ I₁.cocomplex.d n (n + 1) + biprod.snd ≫ I₁.horseshoeTwist I₃ hS n)
        (biprod.snd ≫ I₃.cocomplex.d n (n + 1)) := by
  simp

/-- The inclusion `I₁ ⟶ I₂` of the first factor of the horseshoe complex. -/
def horseshoeInl : I₁.cocomplex ⟶ I₁.horseshoeCocomplex I₃ hS :=
  CochainComplex.ofHom (fun _ ↦ biprod.inl) (fun n ↦ by ext <;> simp)

/-- The projection `I₂ ⟶ I₃` to the second factor of the horseshoe complex. -/
def horseshoeSnd : I₁.horseshoeCocomplex I₃ hS ⟶ I₃.cocomplex :=
  CochainComplex.ofHom (fun _ ↦ biprod.snd) (fun n ↦ by simp)

@[simp]
lemma horseshoeInl_f (n : ℕ) : (I₁.horseshoeInl I₃ hS).f n = biprod.inl :=
  (rfl)

@[simp]
lemma horseshoeSnd_f (n : ℕ) : (I₁.horseshoeSnd I₃ hS).f n = biprod.snd :=
  (rfl)

@[reassoc (attr := simp)]
lemma horseshoeInl_comp_horseshoeSnd :
    I₁.horseshoeInl I₃ hS ≫ I₁.horseshoeSnd I₃ hS = 0 := by
  ext n : 1
  simp

/-- The sequence `I₁ ⟶ I₂ ⟶ I₃` of the inclusion and the projection of the horseshoe complex.

The body is exposed so that its terms and maps are definitionally those of the horseshoe complex,
as its `simps` lemmas require. -/
@[expose, simps X₁ X₂ X₃ f g]
def horseshoeShortComplex : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (I₁.horseshoeInl I₃ hS) (I₁.horseshoeSnd I₃ hS)
    (I₁.horseshoeInl_comp_horseshoeSnd I₃ hS)

/-- In each degree, `I₁ ⟶ I₂ ⟶ I₃` is the split short exact sequence `I₁ⁿ ⟶ I₁ⁿ ⊞ I₃ⁿ ⟶ I₃ⁿ`, whose
retraction and section are `biprod.fst` and `biprod.inr`
(`CategoryTheory.InjectiveResolution.horseshoeSplitting_r` and
`CategoryTheory.InjectiveResolution.horseshoeSplitting_s`). -/
def horseshoeSplitting (n : ℕ) :
    ((I₁.horseshoeShortComplex I₃ hS).map (HomologicalComplex.eval C _ n)).Splitting :=
  -- the maps in degree `n` are the biproduct maps by `horseshoeInl_f` and `horseshoeSnd_f`, which
  -- hold by definition
  ShortComplex.Splitting.ofHasBinaryBiproduct _ _

/-- The retraction of the degreewise splitting of `I₁ ⟶ I₂ ⟶ I₃` is the first projection. -/
@[simp]
lemma horseshoeSplitting_r (n : ℕ) :
    (I₁.horseshoeSplitting I₃ hS n).r = biprod.fst := by
  -- the body is not exposed, so the projection of `ofHasBinaryBiproduct` is reached by unfolding
  unfold horseshoeSplitting
  rfl

/-- The section of the degreewise splitting of `I₁ ⟶ I₂ ⟶ I₃` is the second inclusion. -/
@[simp]
lemma horseshoeSplitting_s (n : ℕ) :
    (I₁.horseshoeSplitting I₃ hS n).s = biprod.inr := by
  -- the body is not exposed, so the projection of `ofHasBinaryBiproduct` is reached by unfolding
  unfold horseshoeSplitting
  rfl

/-- The sequence `I₁ ⟶ I₂ ⟶ I₃` of horseshoe complexes is short exact. -/
lemma horseshoeShortComplex_shortExact : (I₁.horseshoeShortComplex I₃ hS).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n ↦ (I₁.horseshoeSplitting I₃ hS n).shortExact

/-- The augmentation `S.X₂ ⟶ I₁⁰ ⊞ I₃⁰` of the horseshoe resolution, `b ↦ (e b, ε₃ (g b))`. -/
def horseshoeι : (single₀ C).obj S.X₂ ⟶ I₁.horseshoeCocomplex I₃ hS :=
  (fromSingle₀Equiv _ _).symm ⟨biprod.lift (I₁.horseshoeExtension hS) (S.g ≫ I₃.ι₀), by
    -- `rw` unifies the index `0 + 1` of `horseshoeCocomplex_d` with the `1` of `fromSingle₀Equiv`
    rw [I₁.horseshoeCocomplex_d I₃ hS 0]
    ext <;> simp [comp_horseshoeTwist_zero]⟩

@[simp]
lemma horseshoeι_f_zero :
    (I₁.horseshoeι I₃ hS).f 0 = biprod.lift (I₁.horseshoeExtension hS) (S.g ≫ I₃.ι₀) :=
  fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentations of `I₁` and of the horseshoe complex are compatible with `S.f`. -/
@[reassoc (attr := simp)]
lemma ι_comp_horseshoeInl :
    I₁.ι ≫ I₁.horseshoeInl I₃ hS = (single₀ C).map S.f ≫ I₁.horseshoeι I₃ hS := by
  ext : 1
  simp only [comp_f, ι_f_zero, horseshoeInl_f, single₀_map_f_zero, horseshoeι_f_zero]
  ext <;> simp

/-- The augmentations of the horseshoe complex and of `I₃` are compatible with `S.g`. -/
@[reassoc (attr := simp)]
lemma horseshoeι_comp_horseshoeSnd :
    I₁.horseshoeι I₃ hS ≫ I₁.horseshoeSnd I₃ hS = (single₀ C).map S.g ≫ I₃.ι := by
  ext : 1
  simp [ι_f_zero]

/-- The augmentations form a morphism from `S` placed in degree `0` to `I₁ ⟶ I₂ ⟶ I₃`. -/
private def horseshoeAugmentation :
    S.map (single₀ C) ⟶ I₁.horseshoeShortComplex I₃ hS where
  τ₁ := I₁.ι
  τ₂ := I₁.horseshoeι I₃ hS
  τ₃ := I₃.ι
  comm₁₂ := I₁.ι_comp_horseshoeInl I₃ hS
  comm₂₃ := I₁.horseshoeι_comp_horseshoeSnd I₃ hS

/-- The augmentation of the horseshoe complex is a quasi-isomorphism, by the five lemma applied to
the short exact sequences `S.X₁[0] ⟶ S.X₂[0] ⟶ S.X₃[0]` and `I₁ ⟶ I₂ ⟶ I₃`. -/
instance : QuasiIso (I₁.horseshoeι I₃ hS) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₂ (horseshoeAugmentation I₁ I₃ hS)
    (hS.map_of_exact (single₀ C)) (I₁.horseshoeShortComplex_shortExact I₃ hS)
    I₁.quasiIso I₃.quasiIso

/-- **The horseshoe resolution.** For a short exact sequence `S` and injective resolutions `I₁` of
`S.X₁` and `I₃` of `S.X₃`, the injective resolution of `S.X₂` with terms `I₁ⁿ ⊞ I₃ⁿ`,
differential `(u, v) ↦ (d u + t v, d v)` and augmentation `b ↦ (e b, ε₃ (g b))`.

This is an abbreviation so that its complex is reducibly `I₁.horseshoeCocomplex I₃ hS`, whose
terms are reducibly the biproducts: the statements relating it to `I₁` and `I₃` use this, and the
biproduct lemmas apply to its terms. -/
abbrev horseshoe : InjectiveResolution S.X₂ where
  cocomplex := I₁.horseshoeCocomplex I₃ hS
  injective _ := inferInstance
  ι := I₁.horseshoeι I₃ hS

/-- The augmentation `S.X₂ ⟶ I₁⁰ ⊞ I₃⁰` of the horseshoe resolution is `b ↦ (e b, ε₃ (g b))`. -/
@[simp]
lemma horseshoe_ι₀ :
    (I₁.horseshoe I₃ hS).ι₀ = biprod.lift (I₁.horseshoeExtension hS) (S.g ≫ I₃.ι₀) := by
  rw [← ι_f_zero, horseshoeι_f_zero]

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.ShortComplex.ShortExact

open InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}

/-- **The horseshoe lemma for injective resolutions.** In an abelian category, for a short exact
sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` and injective resolutions `I₁` of `A` and `I₃` of `C`, there are an
injective resolution `I₂` of `B` and chain maps `I₁ ⟶ I₂ ⟶ I₃`, compatible with the augmentations,
that form a split short exact sequence in every degree. -/
theorem exists_injectiveResolution_horseshoe (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ (I₂ : InjectiveResolution S.X₂) (i : I₁.cocomplex ⟶ I₂.cocomplex)
      (p : I₂.cocomplex ⟶ I₃.cocomplex),
      I₁.ι ≫ i = (CochainComplex.single₀ C).map S.f ≫ I₂.ι ∧
      I₂.ι ≫ p = (CochainComplex.single₀ C).map S.g ≫ I₃.ι ∧
      ∀ n : ℕ, ∃ w : i.f n ≫ p.f n = 0,
        Nonempty (ShortComplex.mk (i.f n) (p.f n) w).Splitting :=
  ⟨I₁.horseshoe I₃ hS, I₁.horseshoeInl I₃ hS, I₁.horseshoeSnd I₃ hS,
    I₁.ι_comp_horseshoeInl I₃ hS, I₁.horseshoeι_comp_horseshoeSnd I₃ hS,
    fun n ↦ ⟨_, ⟨I₁.horseshoeSplitting I₃ hS n⟩⟩⟩

end CategoryTheory.ShortComplex.ShortExact
