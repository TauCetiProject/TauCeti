/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.Refinements
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# The horseshoe lemma for injective resolutions

Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in an abelian category, and let `I₁`
and `I₃` be injective resolutions of `X₁` and `X₃`. The horseshoe lemma constructs an injective
resolution `InjectiveResolution.horseshoe hS I₁ I₃` of `X₂` whose term in degree `n` is
`I₁ⁿ ⊞ I₃ⁿ`, together with chain maps `I₁ ⟶ horseshoe hS I₁ I₃ ⟶ I₃` given in each degree by
`biprod.inl` and `biprod.snd` (`InjectiveResolution.horseshoeInl`,
`InjectiveResolution.horseshoeSnd`), which lift `S.f` and `S.g`
(`InjectiveResolution.ι₀_comp_horseshoeInl_f_zero`,
`InjectiveResolution.horseshoe_ι₀_comp_horseshoeSnd_f_zero`) and form a degreewise split short
exact sequence of cochain complexes (`InjectiveResolution.horseshoeShortComplex_shortExact`).

A morphism `φ : S ⟶ S'` of short exact sequences, with chain maps `α₁ : I₁ ⟶ I₁'` and
`α₃ : I₃ ⟶ I₃'` lifting `φ.τ₁` and `φ.τ₃`, lifts to a chain map between the horseshoe resolutions
(`InjectiveResolution.horseshoeMap`), given in each degree by an upper triangular matrix
`[[α₁, θ], [0, α₃]]` and hence commuting with the chain maps of the horseshoes
(`InjectiveResolution.horseshoeInl_comp_horseshoeMap`,
`InjectiveResolution.horseshoeMap_comp_horseshoeSnd`); the maps `θ n : I₃ⁿ ⟶ I₁'ⁿ` are again
chosen inductively (`InjectiveResolution.horseshoeMapθ`).

The augmentation of an injective resolution `I` of `Z` is used in the form
`InjectiveResolution.ι₀ I : Z ⟶ I⁰`, whose source is `Z` itself rather than the degree `0` object
of the single complex on `Z`, so that it composes with `S.f` and `S.g` without unfolding.

The differential of the middle complex is the upper triangular matrix `[[d, σ], [0, d]]`, where
the maps `σ n : I₃ⁿ ⟶ I₁ⁿ⁺¹` are chosen inductively by extending morphisms to the injective
objects `I₁ⁿ⁺¹` (`InjectiveResolution.horseshoeσ`).

The horseshoe lemma is the inductive step in the construction of Cartan–Eilenberg resolutions,
and hence of the Grothendieck and Leray spectral sequences.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8 (dual form).
* [Stacks, Lemma 13.18.9 (013T)](https://stacks.math.columbia.edu/tag/013T)
-/

-- Bodies are exposed so that, for consumers, the terms of the horseshoe complex unfold to the
-- biproducts `I₁ⁿ ⊞ I₃ⁿ` and the complex of `horseshoe` to `horseshoeCocomplex`.
@[expose] public section

open CategoryTheory Category Limits Preadditive

universe v u

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C} (hS : S.ShortExact)
  (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)

/-- The pairs of consecutive off-diagonal components of the differential of the horseshoe
resolution, with the relation which makes it square to zero. -/
structure HorseshoeStep (n : ℕ) where
  /-- The off-diagonal component in degree `n`. -/
  σ : I₃.cocomplex.X n ⟶ I₁.cocomplex.X (n + 1)
  /-- The off-diagonal component in degree `n + 1`. -/
  σ' : I₃.cocomplex.X (n + 1) ⟶ I₁.cocomplex.X (n + 2)
  /-- The relation `σ ≫ d + d ≫ σ' = 0`, which makes the differential square to zero. -/
  comm : σ ≫ I₁.cocomplex.d (n + 1) (n + 2) + I₃.cocomplex.d n (n + 1) ≫ σ' = 0

include hS

/-- The first component `X₂ ⟶ I₁⁰` of the augmentation of the horseshoe resolution: an
extension of the augmentation of `I₁` along the monomorphism `S.f`. -/
noncomputable def horseshoeι₀Fst : S.X₂ ⟶ I₁.cocomplex.X 0 :=
  haveI := hS.mono_f
  Injective.factorThru I₁.ι₀ S.f

@[reassoc (attr := simp)]
lemma f_comp_horseshoeι₀Fst : S.f ≫ horseshoeι₀Fst hS I₁ = I₁.ι₀ := by
  have := hS.mono_f
  exact Injective.comp_factorThru _ _

/-- The morphism `X₃ ⟶ I₁¹` induced by `-(horseshoeι₀Fst ≫ d)`, which vanishes on `X₁`. -/
noncomputable def horseshoeτ : S.X₃ ⟶ I₁.cocomplex.X 1 :=
  hS.exact.descToInjective (-(horseshoeι₀Fst hS I₁ ≫ I₁.cocomplex.d 0 1)) (by
    rw [comp_neg, f_comp_horseshoeι₀Fst_assoc, ι₀_comp_d, neg_zero])

@[reassoc (attr := simp)]
lemma g_comp_horseshoeτ :
    S.g ≫ horseshoeτ hS I₁ = -(horseshoeι₀Fst hS I₁ ≫ I₁.cocomplex.d 0 1) :=
  hS.exact.comp_descToInjective _ _

@[reassoc (attr := simp)]
lemma horseshoeτ_comp_d : horseshoeτ hS I₁ ≫ I₁.cocomplex.d 1 2 = 0 := by
  have := hS.epi_g
  rw [← cancel_epi S.g, g_comp_horseshoeτ_assoc, comp_zero, neg_comp, assoc,
    HomologicalComplex.d_comp_d, comp_zero, neg_zero]

/-- The off-diagonal component `I₃⁰ ⟶ I₁¹` of the horseshoe differential in degree `0`. -/
noncomputable def horseshoeσ₀ : I₃.cocomplex.X 0 ⟶ I₁.cocomplex.X 1 :=
  Injective.factorThru (horseshoeτ hS I₁) I₃.ι₀

@[reassoc (attr := simp)]
lemma ι₀_comp_horseshoeσ₀ : I₃.ι₀ ≫ horseshoeσ₀ hS I₁ I₃ = horseshoeτ hS I₁ :=
  Injective.comp_factorThru _ _

/-- The first pair of off-diagonal components of the horseshoe differential. -/
noncomputable def horseshoeStepZero : HorseshoeStep I₁ I₃ 0 where
  σ := horseshoeσ₀ hS I₁ I₃
  σ' := I₃.exact_ι₀.descToInjective (-(horseshoeσ₀ hS I₁ I₃ ≫ I₁.cocomplex.d 1 2)) (by
    dsimp
    rw [comp_neg, ι₀_comp_horseshoeσ₀_assoc, horseshoeτ_comp_d, neg_zero])
  comm := by
    rw [I₃.exact_ι₀.comp_descToInjective, add_neg_cancel]

/-- The next pair of off-diagonal components of the horseshoe differential. -/
noncomputable def HorseshoeStep.next {n : ℕ} (s : HorseshoeStep I₁ I₃ n) :
    HorseshoeStep I₁ I₃ (n + 1) where
  σ := s.σ'
  σ' := (I₃.exact_succ n).descToInjective (-(s.σ' ≫ I₁.cocomplex.d (n + 2) (n + 3))) (by
    dsimp
    rw [comp_neg, ← assoc, eq_neg_of_add_eq_zero_right s.comm, neg_comp, assoc,
      HomologicalComplex.d_comp_d, comp_zero, neg_zero, neg_zero])
  comm := by
    rw [(I₃.exact_succ n).comp_descToInjective, add_neg_cancel]

/-- The pairs of consecutive off-diagonal components of the horseshoe differential, defined by
induction. -/
noncomputable def horseshoeStep : (n : ℕ) → HorseshoeStep I₁ I₃ n
  | 0 => horseshoeStepZero hS I₁ I₃
  | n + 1 => (horseshoeStep n).next

/-- The off-diagonal component `I₃ⁿ ⟶ I₁ⁿ⁺¹` of the differential of the horseshoe resolution. -/
noncomputable def horseshoeσ (n : ℕ) : I₃.cocomplex.X n ⟶ I₁.cocomplex.X (n + 1) :=
  (horseshoeStep hS I₁ I₃ n).σ

lemma horseshoeσ_zero : horseshoeσ hS I₁ I₃ 0 = horseshoeσ₀ hS I₁ I₃ := rfl

@[reassoc]
lemma horseshoeσ_comm (n : ℕ) :
    horseshoeσ hS I₁ I₃ n ≫ I₁.cocomplex.d (n + 1) (n + 2) +
      I₃.cocomplex.d n (n + 1) ≫ horseshoeσ hS I₁ I₃ (n + 1) = 0 :=
  (horseshoeStep hS I₁ I₃ n).comm

@[reassoc (attr := simp)]
lemma g_comp_ι₀_comp_horseshoeσ_zero :
    S.g ≫ I₃.ι₀ ≫ horseshoeσ hS I₁ I₃ 0 = -(horseshoeι₀Fst hS I₁ ≫ I₁.cocomplex.d 0 1) := by
  rw [horseshoeσ_zero, ι₀_comp_horseshoeσ₀, g_comp_horseshoeτ]

/-- The differential `I₁ⁿ ⊞ I₃ⁿ ⟶ I₁ⁿ⁺¹ ⊞ I₃ⁿ⁺¹` of the horseshoe resolution, the upper
triangular matrix `[[d, σ n], [0, d]]`. -/
noncomputable def horseshoeD (n : ℕ) :
    I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶ I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1) :=
  biprod.map (I₁.cocomplex.d n (n + 1)) (I₃.cocomplex.d n (n + 1)) +
    biprod.snd ≫ horseshoeσ hS I₁ I₃ n ≫ biprod.inl

@[reassoc (attr := simp)]
lemma inl_horseshoeD (n : ℕ) :
    biprod.inl ≫ horseshoeD hS I₁ I₃ n = I₁.cocomplex.d n (n + 1) ≫ biprod.inl := by
  simp [horseshoeD]

@[reassoc (attr := simp)]
lemma horseshoeD_snd (n : ℕ) :
    horseshoeD hS I₁ I₃ n ≫ biprod.snd = biprod.snd ≫ I₃.cocomplex.d n (n + 1) := by
  simp [horseshoeD]

@[reassoc (attr := simp)]
lemma horseshoeD_fst (n : ℕ) :
    horseshoeD hS I₁ I₃ n ≫ biprod.fst =
      biprod.fst ≫ I₁.cocomplex.d n (n + 1) + biprod.snd ≫ horseshoeσ hS I₁ I₃ n := by
  simp [horseshoeD]

@[reassoc (attr := simp)]
lemma horseshoeD_comp_horseshoeD (n : ℕ) :
    horseshoeD hS I₁ I₃ n ≫ horseshoeD hS I₁ I₃ (n + 1) = 0 := by
  have h : horseshoeσ hS I₁ I₃ n ≫ I₁.cocomplex.d (n + 1) (n + 1 + 1) +
      I₃.cocomplex.d n (n + 1) ≫ horseshoeσ hS I₁ I₃ (n + 1) = 0 :=
    horseshoeσ_comm hS I₁ I₃ n
  ext <;> simp [horseshoeD, h]

/-- The cochain complex of the horseshoe resolution, with `I₁ⁿ ⊞ I₃ⁿ` in degree `n`. -/
noncomputable def horseshoeCocomplex : CochainComplex C ℕ :=
  CochainComplex.of (fun n ↦ I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) (horseshoeD hS I₁ I₃)
    (horseshoeD_comp_horseshoeD hS I₁ I₃)

@[simp]
lemma horseshoeCocomplex_X (n : ℕ) :
    (horseshoeCocomplex hS I₁ I₃).X n = (I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) := rfl

@[simp]
lemma horseshoeCocomplex_d (n : ℕ) :
    (horseshoeCocomplex hS I₁ I₃).d n (n + 1) = horseshoeD hS I₁ I₃ n := by
  dsimp only [horseshoeCocomplex]
  exact CochainComplex.of_d _ _ n

/-- The augmentation `X₂ ⟶ I₁⁰ ⊞ I₃⁰` of the horseshoe resolution. -/
noncomputable def horseshoeι₀ : S.X₂ ⟶ I₁.cocomplex.X 0 ⊞ I₃.cocomplex.X 0 :=
  biprod.lift (horseshoeι₀Fst hS I₁) (S.g ≫ I₃.ι₀)

@[reassoc (attr := simp)]
lemma horseshoeι₀_fst : horseshoeι₀ hS I₁ I₃ ≫ biprod.fst = horseshoeι₀Fst hS I₁ := by
  simp [horseshoeι₀]

@[reassoc (attr := simp)]
lemma horseshoeι₀_snd : horseshoeι₀ hS I₁ I₃ ≫ biprod.snd = S.g ≫ I₃.ι₀ := by
  simp [horseshoeι₀]

@[reassoc (attr := simp)]
lemma f_comp_horseshoeι₀ : S.f ≫ horseshoeι₀ hS I₁ I₃ = I₁.ι₀ ≫ biprod.inl := by
  ext <;> simp

@[reassoc (attr := simp)]
lemma horseshoeι₀_comp_horseshoeD : horseshoeι₀ hS I₁ I₃ ≫ horseshoeD hS I₁ I₃ 0 = 0 := by
  ext
  · simp
  · simp

/-- The chain map `I₁ ⟶ horseshoeCocomplex`, given by `biprod.inl` in each degree. -/
@[simps]
noncomputable def horseshoeInl : I₁.cocomplex ⟶ horseshoeCocomplex hS I₁ I₃ where
  f _ := biprod.inl
  comm' := by
    rintro i _ rfl
    simp

/-- The chain map `horseshoeCocomplex ⟶ I₃`, given by `biprod.snd` in each degree. -/
@[simps]
noncomputable def horseshoeSnd : horseshoeCocomplex hS I₁ I₃ ⟶ I₃.cocomplex where
  f _ := biprod.snd
  comm' := by
    rintro i _ rfl
    simp

/-- The short complex of cochain complexes `I₁ ⟶ horseshoeCocomplex ⟶ I₃`. -/
@[simps]
noncomputable def horseshoeShortComplex : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (horseshoeInl hS I₁ I₃) (horseshoeSnd hS I₁ I₃) (by
    ext n
    simp only [HomologicalComplex.comp_f, horseshoeInl_f, horseshoeSnd_f, HomologicalComplex.zero_f]
    exact biprod.inl_snd)

/-- The short complex `I₁ ⟶ horseshoeCocomplex ⟶ I₃` is short exact, being degreewise split. -/
lemma horseshoeShortComplex_shortExact : (horseshoeShortComplex hS I₁ I₃).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (ShortComplex.Splitting.ofHasBinaryBiproduct (I₁.cocomplex.X n) (I₃.cocomplex.X n)).shortExact

/-- The augmentation `X₂ ⟶ I₁⁰ ⊞ I₃⁰` is a monomorphism. -/
lemma mono_horseshoeι₀ : Mono (horseshoeι₀ hS I₁ I₃) := by
  have := hS.mono_f
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx ↦ ?_
  have hg : x ≫ S.g = 0 := by
    rw [← cancel_mono I₃.ι₀, zero_comp]
    simpa using hx =≫ biprod.snd
  obtain ⟨y, rfl⟩ : ∃ y, y ≫ S.f = x := ⟨hS.exact.lift x hg, hS.exact.lift_f x hg⟩
  have hy : y = 0 := by
    rw [← cancel_mono I₁.ι₀, zero_comp]
    simpa using hx =≫ biprod.fst
  simp [hy]

/-- The sequence `X₂ ⟶ I₁⁰ ⊞ I₃⁰ ⟶ I₁¹ ⊞ I₃¹` is exact. -/
lemma horseshoe_exact₀ :
    (ShortComplex.mk _ _ (horseshoeι₀_comp_horseshoeD hS I₁ I₃)).Exact := by
  have := hS.epi_g
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨T₁, π₁, _, y, hy⟩ := I₃.exact_ι₀.exact_up_to_refinements (x₂ ≫ biprod.snd) (by
    simpa using hx₂ =≫ biprod.snd)
  dsimp at hy
  obtain ⟨T₂, π₂, _, z, hz⟩ := surjective_up_to_refinements_of_epi S.g y
  set w := π₂ ≫ π₁ ≫ x₂ - z ≫ horseshoeι₀ hS I₁ I₃ with hw
  have hw_snd : w ≫ biprod.snd = 0 := by
    rw [hw, sub_comp, assoc, assoc, hy, reassoc_of% hz, assoc, horseshoeι₀_snd, sub_self]
  have hw_eq : w = (w ≫ biprod.fst) ≫ biprod.inl := by
    ext <;> simp [hw_snd]
  have hw_d : (w ≫ biprod.fst) ≫ I₁.cocomplex.d 0 1 = 0 := by
    have h : w ≫ horseshoeD hS I₁ I₃ 0 = 0 := by
      rw [hw, sub_comp, assoc, assoc, hx₂, comp_zero, comp_zero, assoc,
        horseshoeι₀_comp_horseshoeD, comp_zero, sub_self]
    rw [hw_eq, assoc, inl_horseshoeD] at h
    simpa using h =≫ biprod.fst
  obtain ⟨T₃, π₃, _, v, hv⟩ := I₁.exact_ι₀.exact_up_to_refinements (w ≫ biprod.fst) hw_d
  dsimp at hv
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance, π₃ ≫ z + v ≫ S.f, ?_⟩
  have h : π₂ ≫ π₁ ≫ x₂ = w + z ≫ horseshoeι₀ hS I₁ I₃ := by
    rw [hw, sub_add_cancel]
  dsimp
  rw [assoc, assoc, h]
  ext
  · simpa [add_comm] using hv
  · simp [hw_snd]

lemma horseshoeι₀_comp_horseshoeCocomplex_d :
    horseshoeι₀ hS I₁ I₃ ≫ (horseshoeCocomplex hS I₁ I₃).d 0 1 = 0 := by
  have := horseshoeCocomplex_d hS I₁ I₃ 0
  dsimp at this
  rw [this]
  exact horseshoeι₀_comp_horseshoeD hS I₁ I₃

/-- **The horseshoe lemma**: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` and injective
resolutions `I₁`, `I₃` of `X₁`, `X₃`, an injective resolution of `X₂` with `I₁ⁿ ⊞ I₃ⁿ` in
degree `n`. -/
noncomputable def horseshoe : InjectiveResolution S.X₂ where
  cocomplex := horseshoeCocomplex hS I₁ I₃
  injective n := by dsimp; infer_instance
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨horseshoeι₀ hS I₁ I₃, horseshoeι₀_comp_horseshoeCocomplex_d hS I₁ I₃⟩
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨horseshoe_exact₀ hS I₁ I₃, mono_horseshoeι₀ hS I₁ I₃⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp)
        simp only [Iso.refl_hom]
        -- `S.X₂` is the degree `0` object of the single complex only up to unfolding `single₀`,
        -- so `simp` can neither cancel the identities nor rewrite the component
        exact (id_comp _).trans ((comp_id _).trans
          (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero (C := horseshoeCocomplex hS I₁ I₃) _
            (horseshoeι₀_comp_horseshoeCocomplex_d hS I₁ I₃))).symm
      -- the differentials into and out of degree `0` of the single complex, and into degree `0`
      -- of the horseshoe complex, vanish by unfolding `single₀` and `CochainComplex.of`
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
      exact (horseshoeShortComplex_shortExact hS I₁ I₃).exactAt_X₂ (n + 1)
        (I₁.cocomplex_exactAt_succ n) (I₃.cocomplex_exactAt_succ n)⟩

@[simp]
lemma horseshoe_cocomplex : (horseshoe hS I₁ I₃).cocomplex = horseshoeCocomplex hS I₁ I₃ := rfl

@[simp]
lemma horseshoe_ι₀ : (horseshoe hS I₁ I₃).ι₀ = horseshoeι₀ hS I₁ I₃ :=
  congrArg Subtype.val ((fromSingle₀Equiv_ι (horseshoe hS I₁ I₃)).symm.trans
    ((CochainComplex.fromSingle₀Equiv _ _).apply_symm_apply _))

/-- The chain map `horseshoeInl` lifts `S.f`. -/
@[reassoc]
lemma ι₀_comp_horseshoeInl_f_zero :
    I₁.ι₀ ≫ (horseshoeInl hS I₁ I₃).f 0 = S.f ≫ (horseshoe hS I₁ I₃).ι₀ := by
  simp

/-- The chain map `horseshoeSnd` lifts `S.g`. -/
@[reassoc]
lemma horseshoe_ι₀_comp_horseshoeSnd_f_zero :
    (horseshoe hS I₁ I₃).ι₀ ≫ (horseshoeSnd hS I₁ I₃).f 0 = S.g ≫ I₃.ι₀ := by
  simp

end CategoryTheory.InjectiveResolution

/-! ### Morphisms of horseshoe resolutions -/

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S')
  {I₁ : InjectiveResolution S.X₁} {I₃ : InjectiveResolution S.X₃}
  {I₁' : InjectiveResolution S'.X₁} {I₃' : InjectiveResolution S'.X₃}
  (α₁ : I₁.cocomplex ⟶ I₁'.cocomplex) (α₃ : I₃.cocomplex ⟶ I₃'.cocomplex)

/-- The pairs of consecutive off-diagonal components of a morphism of horseshoe resolutions, with
the relation which makes it commute with the differentials. -/
structure HorseshoeMapStep (n : ℕ) where
  /-- The off-diagonal component in degree `n`. -/
  θ : I₃.cocomplex.X n ⟶ I₁'.cocomplex.X n
  /-- The off-diagonal component in degree `n + 1`. -/
  θ' : I₃.cocomplex.X (n + 1) ⟶ I₁'.cocomplex.X (n + 1)
  /-- The relation which makes the morphism commute with the differentials. -/
  comm : I₃.cocomplex.d n (n + 1) ≫ θ' = θ ≫ I₁'.cocomplex.d n (n + 1) +
    α₃.f n ≫ horseshoeσ hS' I₁' I₃' n - horseshoeσ hS I₁ I₃ n ≫ α₁.f (n + 1)

variable (h₁ : I₁.ι₀ ≫ α₁.f 0 = φ.τ₁ ≫ I₁'.ι₀) (h₃ : I₃.ι₀ ≫ α₃.f 0 = φ.τ₃ ≫ I₃'.ι₀)

/-- The morphism `X₃ ⟶ I₁'⁰` induced by the difference of the two ways of mapping `X₂` to `I₁'⁰`,
which vanishes on `X₁`. -/
noncomputable def horseshoeMapτ : S.X₃ ⟶ I₁'.cocomplex.X 0 :=
  hS.exact.descToInjective (φ.τ₂ ≫ horseshoeι₀Fst hS' I₁' - horseshoeι₀Fst hS I₁ ≫ α₁.f 0) (by
    rw [comp_sub, ← φ.comm₁₂_assoc, f_comp_horseshoeι₀Fst, f_comp_horseshoeι₀Fst_assoc, h₁,
      sub_self])

@[reassoc (attr := simp)]
lemma g_comp_horseshoeMapτ :
    S.g ≫ horseshoeMapτ hS hS' φ α₁ h₁ =
      φ.τ₂ ≫ horseshoeι₀Fst hS' I₁' - horseshoeι₀Fst hS I₁ ≫ α₁.f 0 :=
  hS.exact.comp_descToInjective _ _

/-- The off-diagonal component `I₃⁰ ⟶ I₁'⁰` of a morphism of horseshoe resolutions in degree
`0`. -/
noncomputable def horseshoeMapθ₀ : I₃.cocomplex.X 0 ⟶ I₁'.cocomplex.X 0 :=
  Injective.factorThru (horseshoeMapτ hS hS' φ α₁ h₁) I₃.ι₀

@[reassoc (attr := simp)]
lemma ι₀_comp_horseshoeMapθ₀ :
    I₃.ι₀ ≫ horseshoeMapθ₀ hS hS' φ α₁ h₁ = horseshoeMapτ hS hS' φ α₁ h₁ :=
  Injective.comp_factorThru _ _

/-- The first pair of off-diagonal components of a morphism of horseshoe resolutions. -/
noncomputable def horseshoeMapStepZero : HorseshoeMapStep hS hS' α₁ α₃ 0 where
  θ := horseshoeMapθ₀ hS hS' φ α₁ h₁
  θ' := I₃.exact_ι₀.descToInjective (horseshoeMapθ₀ hS hS' φ α₁ h₁ ≫ I₁'.cocomplex.d 0 1 +
      α₃.f 0 ≫ horseshoeσ hS' I₁' I₃' 0 - horseshoeσ hS I₁ I₃ 0 ≫ α₁.f 1) (by
    have := hS.epi_g
    dsimp
    rw [← cancel_epi S.g, comp_zero]
    simp only [comp_add, comp_sub, ι₀_comp_horseshoeMapθ₀_assoc, g_comp_horseshoeMapτ_assoc,
      reassoc_of% h₃, ← φ.comm₂₃_assoc, g_comp_ι₀_comp_horseshoeσ_zero,
      g_comp_ι₀_comp_horseshoeσ_zero_assoc, sub_comp, assoc, neg_comp, comp_neg, α₁.comm]
    abel)
  comm := I₃.exact_ι₀.comp_descToInjective _ _

variable {hS hS' α₁ α₃} in
/-- The next pair of off-diagonal components of a morphism of horseshoe resolutions. -/
noncomputable def HorseshoeMapStep.next {n : ℕ} (s : HorseshoeMapStep hS hS' α₁ α₃ n) :
    HorseshoeMapStep hS hS' α₁ α₃ (n + 1) where
  θ := s.θ'
  θ' := (I₃.exact_succ n).descToInjective (s.θ' ≫ I₁'.cocomplex.d (n + 1) (n + 2) +
      α₃.f (n + 1) ≫ horseshoeσ hS' I₁' I₃' (n + 1) -
        horseshoeσ hS I₁ I₃ (n + 1) ≫ α₁.f (n + 2)) (by
    have h := horseshoeσ_comm hS I₁ I₃ n
    have h' := horseshoeσ_comm hS' I₁' I₃' n
    have h₂ : I₃.cocomplex.d n (n + 1) ≫ horseshoeσ hS I₁ I₃ (n + 1) ≫ α₁.f (n + 2) =
        -(horseshoeσ hS I₁ I₃ n ≫ I₁.cocomplex.d (n + 1) (n + 2) ≫ α₁.f (n + 2)) := by
      rw [← assoc, eq_neg_of_add_eq_zero_right h, neg_comp, assoc]
    dsimp
    rw [comp_sub, comp_add, reassoc_of% s.comm, ← α₃.comm_assoc,
      eq_neg_of_add_eq_zero_right h', h₂]
    simp only [add_comp, sub_comp, assoc, HomologicalComplex.d_comp_d, comp_zero, comp_neg,
      HomologicalComplex.Hom.comm]
    abel)
  comm := (I₃.exact_succ n).comp_descToInjective _ _

/-- The pairs of consecutive off-diagonal components of a morphism of horseshoe resolutions,
defined by induction. -/
noncomputable def horseshoeMapStep : (n : ℕ) → HorseshoeMapStep hS hS' α₁ α₃ n
  | 0 => horseshoeMapStepZero hS hS' φ α₁ α₃ h₁ h₃
  | n + 1 => (horseshoeMapStep n).next

/-- The off-diagonal component `I₃ⁿ ⟶ I₁'ⁿ` of a morphism of horseshoe resolutions. -/
noncomputable def horseshoeMapθ (n : ℕ) : I₃.cocomplex.X n ⟶ I₁'.cocomplex.X n :=
  (horseshoeMapStep hS hS' φ α₁ α₃ h₁ h₃ n).θ

lemma horseshoeMapθ_zero :
    horseshoeMapθ hS hS' φ α₁ α₃ h₁ h₃ 0 = horseshoeMapθ₀ hS hS' φ α₁ h₁ := rfl

lemma horseshoeMapθ_comm (n : ℕ) :
    I₃.cocomplex.d n (n + 1) ≫ horseshoeMapθ hS hS' φ α₁ α₃ h₁ h₃ (n + 1) =
      horseshoeMapθ hS hS' φ α₁ α₃ h₁ h₃ n ≫ I₁'.cocomplex.d n (n + 1) +
        α₃.f n ≫ horseshoeσ hS' I₁' I₃' n - horseshoeσ hS I₁ I₃ n ≫ α₁.f (n + 1) :=
  (horseshoeMapStep hS hS' φ α₁ α₃ h₁ h₃ n).comm

/-- The component `I₁ⁿ ⊞ I₃ⁿ ⟶ I₁'ⁿ ⊞ I₃'ⁿ` of a morphism of horseshoe resolutions, the upper
triangular matrix `[[α₁, θ n], [0, α₃]]`. -/
noncomputable def horseshoeMapF (n : ℕ) :
    I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶ I₁'.cocomplex.X n ⊞ I₃'.cocomplex.X n :=
  biprod.map (α₁.f n) (α₃.f n) + biprod.snd ≫ horseshoeMapθ hS hS' φ α₁ α₃ h₁ h₃ n ≫ biprod.inl

/-- **The horseshoe lemma for morphisms**: a morphism `φ` of short exact sequences, with chain
maps `α₁`, `α₃` between injective resolutions of the outer terms lifting `φ.τ₁` and `φ.τ₃`,
lifts to a chain map between the horseshoe resolutions of the middle terms, given in each degree
by an upper triangular matrix `[[α₁, θ], [0, α₃]]`. -/
noncomputable def horseshoeMap :
    horseshoeCocomplex hS I₁ I₃ ⟶ horseshoeCocomplex hS' I₁' I₃' :=
  CochainComplex.ofHom (horseshoeMapF hS hS' φ α₁ α₃ h₁ h₃) fun n ↦ by
    have h := horseshoeMapθ_comm hS hS' φ α₁ α₃ h₁ h₃ n
    rw [horseshoeCocomplex_d, horseshoeCocomplex_d]
    refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
      simp [horseshoeMapF, horseshoeD, h]

lemma horseshoeMap_f (n : ℕ) :
    (horseshoeMap hS hS' φ α₁ α₃ h₁ h₃).f n = horseshoeMapF hS hS' φ α₁ α₃ h₁ h₃ n := rfl

@[reassoc (attr := simp)]
lemma horseshoeInl_comp_horseshoeMap :
    horseshoeInl hS I₁ I₃ ≫ horseshoeMap hS hS' φ α₁ α₃ h₁ h₃ = α₁ ≫ horseshoeInl hS' I₁' I₃' := by
  ext n : 2
  simp [horseshoeMap_f, horseshoeMapF]

@[reassoc (attr := simp)]
lemma horseshoeMap_comp_horseshoeSnd :
    horseshoeMap hS hS' φ α₁ α₃ h₁ h₃ ≫ horseshoeSnd hS' I₁' I₃' = horseshoeSnd hS I₁ I₃ ≫ α₃ := by
  ext n : 2
  simp [horseshoeMap_f, horseshoeMapF]

/-- The morphism of horseshoe resolutions lifts `φ.τ₂`. -/
@[reassoc]
lemma horseshoe_ι₀_comp_horseshoeMap_f_zero :
    (horseshoe hS I₁ I₃).ι₀ ≫ (horseshoeMap hS hS' φ α₁ α₃ h₁ h₃).f 0 =
      φ.τ₂ ≫ (horseshoe hS' I₁' I₃').ι₀ := by
  rw [horseshoe_ι₀, horseshoe_ι₀, horseshoeMap_f]
  refine biprod.hom_ext _ _ ?_ ?_
  · simp [horseshoeMapF, horseshoeMapθ_zero]
  · simp [horseshoeMapF, φ.comm₂₃_assoc, h₃]

end CategoryTheory.InjectiveResolution
