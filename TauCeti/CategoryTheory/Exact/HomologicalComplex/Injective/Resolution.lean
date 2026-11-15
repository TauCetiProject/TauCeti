/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Acyclic
public import TauCeti.CategoryTheory.Exact.Injective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Injective resolutions of bounded below complexes

Let `E` be an exact structure with enough injectives. Every bounded below complex `X` has an
injective resolution: a map `X ⟶ I` to a bounded below complex of `E`-injective objects whose
mapping cone is `E`-acyclic. This is the dual of Bühler's Theorem 12.7, due to Keller.

For `X` strictly bounded below at `0`, the construction is recursive. Put `B⁰ = X⁰` and
`q⁰ = d : B⁰ ⟶ X¹`. Given `qᵏ : Bᵏ ⟶ Xᵏ⁺¹` with `qᵏ ≫ d = 0`, choose an inflation `jᵏ : Bᵏ ↣ Iᵏ`
into an injective, and let `Bᵏ⁺¹` be the pushout of `jᵏ` and `qᵏ`; the map `qᵏ⁺¹ : Bᵏ⁺¹ ⟶ Xᵏ⁺²`
is `0` on `Iᵏ` and `d` on `Xᵏ⁺¹`. The complex `I` has differential `Iᵏ ⟶ Bᵏ⁺¹ ↣ Iᵏ⁺¹`, and the
resolution is `Xᵏ ⟶ Bᵏ ↣ Iᵏ`. The pushout squares make its cone acyclic, by
`TauCeti.ExactStructure.acyclic_mappingCone_of_isPushout`. No idempotent completeness is needed.

## Main results

* `TauCeti.ExactStructure.EnoughInjectives.exists_injectiveResolution`: a complex strictly bounded
  below at `n` has a map to a complex of injectives, strictly bounded below at `n`, with acyclic
  mapping cone.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Theorem 12.7, of which this is the dual.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Math. **67** (1990),
  379--417, Section 4.1, Lemma b).
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace EnoughInjectives

variable (hE : E.EnoughInjectives) (X : CochainComplex C ℤ)

/-- A stage of the recursion: an object `Bᵏ` with a map `qᵏ : Bᵏ ⟶ Xᵏ⁺¹` killed by `d`. -/
private structure Stage (k : ℕ) where
  /-- The object `Bᵏ`. -/
  B : C
  /-- The map `qᵏ : Bᵏ ⟶ Xᵏ⁺¹`. -/
  q : B ⟶ X.X (k + 1 : ℕ)
  hq : q ≫ X.d (k + 1 : ℕ) (k + 1 + 1 : ℕ) = 0

/-- The pushout of an inflation exists. -/
private theorem hasPushout_i {Y T : C} (P : E.InjectivePresentation Y) (q : Y ⟶ T) :
    HasPushout P.i q :=
  E.hasPushouts_inflations.hasPushout q (E.isInflation_f P.conflation)

/-- The stages of the recursion. -/
private noncomputable def stage : ∀ k : ℕ, Stage X k
  | 0 => ⟨X.X 0, X.d 0 (0 + 1 : ℕ), X.d_comp_d _ _ _⟩
  | k + 1 =>
    have := hasPushout_i (hE.injectivePresentation (stage k).B) (stage k).q
    { B := pushout (hE.injectivePresentation (stage k).B).i (stage k).q
      q := pushout.desc 0 (X.d (k + 1 : ℕ) (k + 1 + 1 : ℕ)) (by rw [comp_zero, (stage k).hq])
      hq := by apply pushout.hom_ext <;> simp }

/-- The chosen injective presentation `jᵏ : Bᵏ ↣ Iᵏ`. -/
private noncomputable abbrev pres (k : ℕ) : E.InjectivePresentation (stage hE X k).B :=
  hE.injectivePresentation (stage hE X k).B

/-! The data of the resolution in all degrees: zero in negative degrees. -/

/-- The objects `Bᵐ`. -/
private noncomputable def objB : ℤ → C
  | Int.ofNat k => (stage hE X k).B
  | Int.negSucc _ => 0

/-- The terms `Iᵐ` of the resolution. -/
private noncomputable def objI : ℤ → C
  | Int.ofNat k => (pres hE X k).I
  | Int.negSucc _ => 0

/-- The inflations `jᵐ : Bᵐ ↣ Iᵐ`. -/
private noncomputable def j : ∀ m, objB hE X m ⟶ objI hE X m
  | Int.ofNat k => (pres hE X k).i
  | Int.negSucc _ => 𝟙 0

/-- The maps `qᵐ : Bᵐ ⟶ Xᵐ⁺¹`. -/
private noncomputable def q : ∀ m, objB hE X m ⟶ X.X (m + 1)
  | Int.ofNat k => (stage hE X k).q
  | Int.negSucc _ => 0

/-- The maps `uᵐ : Iᵐ ⟶ Bᵐ⁺¹`. -/
private noncomputable def u : ∀ m, objI hE X m ⟶ objB hE X (m + 1)
  | Int.ofNat k =>
    have := hasPushout_i (pres hE X k) (stage hE X k).q
    (pushout.inl _ _ : _ ⟶ (stage hE X (k + 1)).B)
  | Int.negSucc _ => 0

/-- The maps `vᵐ : Xᵐ ⟶ Bᵐ`. -/
private noncomputable def v : ∀ m, X.X m ⟶ objB hE X m
  | Int.ofNat 0 => 𝟙 _
  | Int.ofNat (k + 1) =>
    have := hasPushout_i (pres hE X k) (stage hE X k).q
    (pushout.inr _ _ : _ ⟶ (stage hE X (k + 1)).B)
  | Int.negSucc _ => 0

private theorem isInflation_j (m : ℤ) : E.IsInflation (j hE X m) :=
  match m with
  | Int.ofNat k => E.isInflation_f (pres hE X k).conflation
  | Int.negSucc _ => E.isInflation_id 0

private theorem isInjective_objI (m : ℤ) : E.isInjective (objI hE X m) :=
  match m with
  | Int.ofNat k => (pres hE X k).isInjective
  | Int.negSucc _ => E.isInjective.prop_of_isZero (isZero_zero C)

private theorem u_q (m : ℤ) : u hE X m ≫ q hE X (m + 1) = 0 :=
  match m with
  | Int.ofNat k =>
    have := hasPushout_i (pres hE X k) (stage hE X k).q
    pushout.inl_desc (f := (pres hE X k).i) (g := (stage hE X k).q) _ _ _
  | Int.negSucc _ => zero_comp

variable [X.IsStrictlyGE 0]

private theorem v_q (m : ℤ) : v hE X m ≫ q hE X m = X.d m (m + 1) :=
  match m with
  | Int.ofNat 0 => Category.id_comp _
  | Int.ofNat (k + 1) =>
    have := hasPushout_i (pres hE X k) (stage hE X k).q
    pushout.inr_desc (f := (pres hE X k).i) (g := (stage hE X k).q) _ _ _
  | Int.negSucc k => (X.isZero_of_isStrictlyGE 0 (Int.negSucc k) (by lia)).eq_of_src _ _

private theorem isPushout (m : ℤ) :
    IsPushout (j hE X m) (q hE X m) (u hE X m) (v hE X (m + 1)) :=
  match m with
  | Int.ofNat k =>
    have := hasPushout_i (pres hE X k) (stage hE X k).q
    IsPushout.of_hasPushout (pres hE X k).i (stage hE X k).q
  | Int.negSucc 0 => by
    have : IsIso (j hE X (Int.negSucc 0)) := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (v hE X (Int.negSucc 0 + 1)) := inferInstanceAs (IsIso (𝟙 _))
    exact IsPushout.of_horiz_isIso ⟨by simp [u, q]⟩
  | Int.negSucc (k + 1) => by
    have : IsIso (j hE X (Int.negSucc (k + 1))) := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (v hE X (Int.negSucc (k + 1) + 1)) :=
      isIso_of_source_target_iso_zero _
        (X.isZero_of_isStrictlyGE 0 (Int.negSucc k) (by lia)).isoZero (Iso.refl 0)
    exact IsPushout.of_horiz_isIso ⟨by simp [u, q]⟩
/-- The complex of injectives, with differential `Iᵐ ⟶ Bᵐ⁺¹ ↣ Iᵐ⁺¹`. -/
private noncomputable def complex : CochainComplex C ℤ :=
  CochainComplex.of (objI hE X) (fun m ↦ u hE X m ≫ j hE X (m + 1)) fun m ↦ by
    simp only [Category.assoc]
    rw [reassoc_of% (isPushout hE X (m + 1)).w, reassoc_of% (u_q hE X m), zero_comp]

/-- The resolution `Xᵐ ⟶ Bᵐ ↣ Iᵐ`. -/
private noncomputable def hom : X ⟶ complex hE X where
  f m := v hE X m ≫ j hE X m
  comm' := by
    rintro m _ rfl
    dsimp only [complex]
    rw [CochainComplex.of_d, Category.assoc, reassoc_of% (isPushout hE X m).w,
      ← Category.assoc, v_q]

private theorem acyclic_mappingCone_hom : E.acyclic (CochainComplex.mappingCone (hom hE X)) :=
  E.acyclic_mappingCone_of_isPushout (hom hE X) (objB hE X) (j hE X) (q hE X) (u hE X) (v hE X)
    (isInflation_j hE X) (isPushout hE X) (fun m ↦ by simp [complex]) (fun _ ↦ rfl) (v_q hE X)
    (u_q hE X)

private instance : (complex hE X).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
  exact isZero_zero C

omit [X.IsStrictlyGE 0] in
include hE in
/-- **Injective resolutions of complexes bounded below at `0`.** -/
private theorem exists_injectiveResolution_zero [X.IsStrictlyGE 0] :
    ∃ (I : CochainComplex C ℤ) (α : X ⟶ I), I.IsStrictlyGE 0 ∧ (∀ k, E.isInjective (I.X k)) ∧
      E.acyclic (CochainComplex.mappingCone α) :=
  ⟨complex hE X, hom hE X, inferInstance, isInjective_objI hE X, acyclic_mappingCone_hom hE X⟩

omit [X.IsStrictlyGE 0] in
include hE in
/-- **Injective resolutions of bounded below complexes** (dual of Bühler, Theorem 12.7): for an
exact structure with enough injectives, a complex strictly bounded below at `n` has a map to a
complex of injectives, strictly bounded below at `n`, with acyclic mapping cone. The case `n = 0`
is the recursive construction; the general case follows by shifting. -/
theorem exists_injectiveResolution (n : ℤ) [X.IsStrictlyGE n] :
    ∃ (I : CochainComplex C ℤ) (α : X ⟶ I), I.IsStrictlyGE n ∧ (∀ k, E.isInjective (I.X k)) ∧
      E.acyclic (CochainComplex.mappingCone α) := by
  have : (X⟦n⟧).IsStrictlyGE 0 := X.isStrictlyGE_shift n n 0 (by simp)
  obtain ⟨I, α, _, hI, hα⟩ := exists_injectiveResolution_zero hE (X⟦n⟧)
  let e := (shiftFunctorCompIsoId (CochainComplex C ℤ) n (-n) (add_neg_cancel n)).app X
  refine ⟨I⟦-n⟧, e.inv ≫ α⟦-n⟧', I.isStrictlyGE_shift 0 (-n) n (by simp),
    fun k ↦ hI (k + -n), ?_⟩
  obtain ⟨hα⟩ := (E.acyclic_iff _).1 hα
  refine E.acyclic_mappingCone_of_iso e.symm (Iso.refl _) (by simp)
    (E.acyclic.prop_of_iso (CochainComplex.mappingCone.shiftIso α (-n)) (hα.shift (-n)).acyclic)

end EnoughInjectives

end TauCeti.ExactStructure
