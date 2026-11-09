/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.YonedaExt.Basic

/-!
# The Baer sum on the Yoneda `Ext¹` of an exact category

The *Baer sum* of two classes `ξ₁, ξ₂ ∈ Ext¹_E(Z, X)` is the base change along the diagonal
`Z ⟶ Z ⊞ Z` of the cobase change along the codiagonal `X ⊞ X ⟶ X` of their direct sum. This file
shows that it makes `Ext¹_E(Z, X)` an abelian group, with the class of the split conflation as
zero, and that base and cobase change are additive in both of their arguments. Over a semiring
`R` for which the exact category is `R`-linear, `Ext¹_E(Z, X)` is an `R`-module, with `r • ξ` the
cobase change of `ξ` along `r • 𝟙 X` (equivalently, its base change along `r • 𝟙 Z`), and base and
cobase change are `R`-linear. These are the structures through which `Ext¹` is compared with
duals of `Hom` modules in Auslander-Reiten theory.

## Main definitions

* `TauCeti.ExactStructure.Extension.biprod` and `TauCeti.ExactStructure.Ext1.biprod`: the direct
  sum of two extensions and of two classes.
* The `AddCommGroup` instance on `TauCeti.ExactStructure.Ext1 E Z X` is the Baer sum.
* The `Module R` instance on `TauCeti.ExactStructure.Ext1 E Z X`, for `R`-linear categories.
* `TauCeti.ExactStructure.Ext1.pushoutLinearMap` and
  `TauCeti.ExactStructure.Ext1.pullbackLinearMap`: cobase and base change as `R`-linear maps.

## Main results

* `TauCeti.ExactStructure.Ext1.add_def`: the formula for the Baer sum.
* `TauCeti.ExactStructure.Ext1.pushout_add`, `TauCeti.ExactStructure.Ext1.add_pushout`,
  `TauCeti.ExactStructure.Ext1.pullback_add` and `TauCeti.ExactStructure.Ext1.add_pullback`:
  biadditivity of base and cobase change.
* `TauCeti.ExactStructure.Ext1.neg_eq_pushout` and `TauCeti.ExactStructure.Ext1.neg_eq_pullback`:
  the negative of a class is its cobase change along `-𝟙 X`, and its base change along `-𝟙 Z`.

## Implementation notes

No associativity or symmetry constraint on direct sums of conflations is needed. A morphism of
extensions covering `a` on the first terms and `c` on the third terms identifies the cobase change
along `a` with the base change along `c` (`TauCeti.ExactStructure.Ext1.pushout_mk_eq_pullback_mk`).
Applied to the diagonal of a middle term this gives
`ξ.pushout (a + b) = ξ.pushout a + ξ.pushout b`, and applied to the projections of a direct sum it
shows that any two classes are cobase changes of one class along the two projections of a
biproduct. The group laws of `Ext¹_E(Z, X)` are thereby inherited from those of morphisms.

## References

* Saunders Mac Lane, *Homology*, Grundlehren **114**, Springer (1963), Chapter III, §§1–2, for the
  Baer sum of extensions of modules and the congruence attached to a morphism of extensions.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Proposition 2.9, for direct sums of conflations.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {X X' X'' X₁ X₂ Z Z' Z'' Z₁ Z₂ : C}

namespace Extension

/-- The **direct sum** `X₁ ⊞ X₂ ⟶ e₁.obj ⊞ e₂.obj ⟶ Z₁ ⊞ Z₂` of two extensions. The body is exposed
because the statements about its inflation and deflation need its middle term. -/
@[expose, simps]
noncomputable def biprod (e₁ : E.Extension Z₁ X₁) (e₂ : E.Extension Z₂ X₂) :
    E.Extension (Z₁ ⊞ Z₂) (X₁ ⊞ X₂) where
  obj := e₁.obj ⊞ e₂.obj
  f := Limits.biprod.map e₁.f e₂.f
  g := Limits.biprod.map e₁.g e₂.g
  zero := (e₁.shortComplex.biprod e₂.shortComplex).zero
  conflation := E.conflation_biprod e₁.conflation e₂.conflation

/-- The direct sum of extensions respects Yoneda equivalence. -/
theorem Rel.biprod {e₁ e₁' : E.Extension Z₁ X₁} {e₂ e₂' : E.Extension Z₂ X₂}
    (h₁ : e₁.Rel e₁') (h₂ : e₂.Rel e₂') : (e₁.biprod e₂).Rel (e₁'.biprod e₂') := by
  obtain ⟨φ₁, hf₁, hg₁⟩ := (rel_def _ _).mp h₁
  obtain ⟨φ₂, hf₂, hg₂⟩ := (rel_def _ _).mp h₂
  have hf : Limits.biprod.map e₁.f e₂.f ≫ Limits.biprod.map φ₁ φ₂ =
      Limits.biprod.map e₁'.f e₂'.f := by
    apply Limits.biprod.hom_ext <;> simp [hf₁, hf₂]
  have hg : Limits.biprod.map φ₁ φ₂ ≫ Limits.biprod.map e₁'.g e₂'.g =
      Limits.biprod.map e₁.g e₂.g := by
    apply Limits.biprod.hom_ext <;> simp [hg₁, hg₂]
  exact (rel_def _ _).mpr ⟨Limits.biprod.map φ₁ φ₂, hf, hg⟩

end Extension

namespace Ext1

/-- The **direct sum** of two classes, in `Ext¹_E(Z₁ ⊞ Z₂, X₁ ⊞ X₂)`. -/
noncomputable def biprod (ξ₁ : E.Ext1 Z₁ X₁) (ξ₂ : E.Ext1 Z₂ X₂) : E.Ext1 (Z₁ ⊞ Z₂) (X₁ ⊞ X₂) :=
  lift (fun e₁ ↦ lift (fun e₂ ↦ mk (e₁.biprod e₂))
      (fun _ _ h ↦ (mk_eq_mk_iff _ _).mpr ((Extension.Rel.refl e₁).biprod h)) ξ₂)
    (fun e₁ e₁' h ↦ by
      induction ξ₂ using induction with
      | h e₂ =>
        simpa only [lift_mk] using (mk_eq_mk_iff _ _).mpr (h.biprod (Extension.Rel.refl e₂))) ξ₁

/-- The direct sum of two classes is the class of the direct sum of two representatives. -/
@[simp]
theorem biprod_mk (e₁ : E.Extension Z₁ X₁) (e₂ : E.Extension Z₂ X₂) :
    (mk e₁).biprod (mk e₂) = mk (e₁.biprod e₂) := by
  simp only [biprod, lift_mk]

/-- Cobase change along a morphism into a biproduct is the base change along the diagonal of the
direct sum of the cobase changes along the two components. -/
theorem pushout_biprod_lift (ξ : E.Ext1 Z X) (a : X ⟶ X₁) (b : X ⟶ X₂) :
    ξ.pushout (Limits.biprod.lift a b) =
      ((ξ.pushout a).biprod (ξ.pushout b)).pullback (Limits.biprod.lift (𝟙 Z) (𝟙 Z)) := by
  induction ξ using induction with
  | h e =>
    simp only [pushout_mk (e := e) (v := a), pushout_mk (e := e) (v := b), biprod_mk]
    have h₁ : e.f ≫ Limits.biprod.lift (e.pushoutInl a) (e.pushoutInl b) =
        Limits.biprod.lift a b ≫ Limits.biprod.map (e.pushout a).f (e.pushout b).f := by
      apply Limits.biprod.hom_ext <;> simp [Extension.f_pushoutInl]
    have h₂ : Limits.biprod.lift (e.pushoutInl a) (e.pushoutInl b) ≫
        Limits.biprod.map (e.pushout a).g (e.pushout b).g =
          e.g ≫ Limits.biprod.lift (𝟙 Z) (𝟙 Z) := by
      apply Limits.biprod.hom_ext <;> simp
    exact pushout_mk_eq_pullback_mk (e' := (e.pushout a).biprod (e.pushout b)) _ h₁ h₂

/-- Base change along a morphism out of a biproduct is the cobase change along the codiagonal of
the direct sum of the base changes along the two components. -/
theorem pullback_biprod_desc (ξ : E.Ext1 Z X) (c : Z₁ ⟶ Z) (d : Z₂ ⟶ Z) :
    ξ.pullback (Limits.biprod.desc c d) =
      ((ξ.pullback c).biprod (ξ.pullback d)).pushout (Limits.biprod.desc (𝟙 X) (𝟙 X)) := by
  induction ξ using induction with
  | h e =>
    simp only [pullback_mk (e := e) (u := c), pullback_mk (e := e) (u := d), biprod_mk]
    have h₁ : Limits.biprod.map (e.pullback c).f (e.pullback d).f ≫
        Limits.biprod.desc (e.pullbackFst c) (e.pullbackFst d) =
          Limits.biprod.desc (𝟙 X) (𝟙 X) ≫ e.f := by
      apply Limits.biprod.hom_ext' <;> simp
    have h₂ : Limits.biprod.desc (e.pullbackFst c) (e.pullbackFst d) ≫ e.g =
        Limits.biprod.map (e.pullback c).g (e.pullback d).g ≫ Limits.biprod.desc c d := by
      apply Limits.biprod.hom_ext' <;> simp [Extension.pullbackFst_g]
    exact (pushout_mk_eq_pullback_mk (e := (e.pullback c).biprod (e.pullback d)) _ h₁ h₂).symm

/-- The cobase change of a direct sum along the first projection is a base change of the first
summand. -/
@[simp]
theorem biprod_pushout_fst (ξ₁ : E.Ext1 Z₁ X₁) (ξ₂ : E.Ext1 Z₂ X₂) :
    (ξ₁.biprod ξ₂).pushout Limits.biprod.fst = ξ₁.pullback Limits.biprod.fst := by
  induction ξ₁ using induction with
  | h e₁ =>
    induction ξ₂ using induction with
    | h e₂ =>
      rw [biprod_mk]
      exact pushout_mk_eq_pullback_mk (e := e₁.biprod e₂) Limits.biprod.fst
        (Limits.biprod.map_fst _ _) (Limits.biprod.map_fst _ _).symm

/-- The cobase change of a direct sum along the second projection is a base change of the second
summand. -/
@[simp]
theorem biprod_pushout_snd (ξ₁ : E.Ext1 Z₁ X₁) (ξ₂ : E.Ext1 Z₂ X₂) :
    (ξ₁.biprod ξ₂).pushout Limits.biprod.snd = ξ₂.pullback Limits.biprod.snd := by
  induction ξ₁ using induction with
  | h e₁ =>
    induction ξ₂ using induction with
    | h e₂ =>
      rw [biprod_mk]
      exact pushout_mk_eq_pullback_mk (e := e₁.biprod e₂) Limits.biprod.snd
        (Limits.biprod.map_snd _ _) (Limits.biprod.map_snd _ _).symm

/-- The base change of a direct sum along the first inclusion is a cobase change of the first
summand. -/
@[simp]
theorem biprod_pullback_inl (ξ₁ : E.Ext1 Z₁ X₁) (ξ₂ : E.Ext1 Z₂ X₂) :
    (ξ₁.biprod ξ₂).pullback Limits.biprod.inl = ξ₁.pushout Limits.biprod.inl := by
  induction ξ₁ using induction with
  | h e₁ =>
    induction ξ₂ using induction with
    | h e₂ =>
      rw [biprod_mk]
      exact (pushout_mk_eq_pullback_mk (e' := e₁.biprod e₂) Limits.biprod.inl
        (Limits.biprod.inl_map _ _).symm (Limits.biprod.inl_map _ _)).symm

/-- The base change of a direct sum along the second inclusion is a cobase change of the second
summand. -/
@[simp]
theorem biprod_pullback_inr (ξ₁ : E.Ext1 Z₁ X₁) (ξ₂ : E.Ext1 Z₂ X₂) :
    (ξ₁.biprod ξ₂).pullback Limits.biprod.inr = ξ₂.pushout Limits.biprod.inr := by
  induction ξ₁ using induction with
  | h e₁ =>
    induction ξ₂ using induction with
    | h e₂ =>
      rw [biprod_mk]
      exact (pushout_mk_eq_pullback_mk (e' := e₁.biprod e₂) Limits.biprod.inr
        (Limits.biprod.inr_map _ _).symm (Limits.biprod.inr_map _ _)).symm

/-! ### The Baer sum -/

/-- The **Baer sum** on `Ext¹_E(Z, X)`: the base change along the diagonal of the cobase change
along the codiagonal of the direct sum. -/
noncomputable instance : Add (E.Ext1 Z X) where
  add ξ₁ ξ₂ := ((ξ₁.biprod ξ₂).pushout (Limits.biprod.desc (𝟙 X) (𝟙 X))).pullback
    (Limits.biprod.lift (𝟙 Z) (𝟙 Z))

/-- The formula for the **Baer sum**. -/
theorem add_def (ξ₁ ξ₂ : E.Ext1 Z X) :
    ξ₁ + ξ₂ = ((ξ₁.biprod ξ₂).pushout (Limits.biprod.desc (𝟙 X) (𝟙 X))).pullback
      (Limits.biprod.lift (𝟙 Z) (𝟙 Z)) := (rfl)

/-- Cobase change is additive in the morphism. -/
@[simp]
theorem pushout_add (ξ : E.Ext1 Z X) (a b : X ⟶ X') :
    ξ.pushout (a + b) = ξ.pushout a + ξ.pushout b := by
  rw [add_def, pushout_pullback, ← pushout_biprod_lift, pushout_pushout, Limits.biprod.lift_desc]
  simp

/-- Base change is additive in the morphism. -/
@[simp]
theorem pullback_add (ξ : E.Ext1 Z X) (c d : Z' ⟶ Z) :
    ξ.pullback (c + d) = ξ.pullback c + ξ.pullback d := by
  rw [add_def, ← pullback_biprod_desc, pullback_pullback, Limits.biprod.lift_desc]
  simp

/-- Any two classes with the same third term are cobase changes of one class along the two
projections of the biproduct of their first terms. -/
private theorem exists_pushout_fst_eq_and_pushout_snd_eq (ξ₁ : E.Ext1 Z X₁) (ξ₂ : E.Ext1 Z X₂) :
    ∃ θ : E.Ext1 Z (X₁ ⊞ X₂), θ.pushout Limits.biprod.fst = ξ₁ ∧
      θ.pushout Limits.biprod.snd = ξ₂ := by
  refine ⟨(ξ₁.biprod ξ₂).pullback (Limits.biprod.lift (𝟙 Z) (𝟙 Z)), ?_, ?_⟩
  · simp [← pushout_pullback]
  · simp [← pushout_pullback]

/-- Cobase change is additive in the class. -/
@[simp]
theorem add_pushout (ξ₁ ξ₂ : E.Ext1 Z X) (v : X ⟶ X') :
    (ξ₁ + ξ₂).pushout v = ξ₁.pushout v + ξ₂.pushout v := by
  obtain ⟨θ, rfl, rfl⟩ := exists_pushout_fst_eq_and_pushout_snd_eq ξ₁ ξ₂
  simp only [← pushout_add, pushout_pushout, Preadditive.add_comp]

/-- Base change is additive in the class. -/
@[simp]
theorem add_pullback (ξ₁ ξ₂ : E.Ext1 Z X) (u : Z' ⟶ Z) :
    (ξ₁ + ξ₂).pullback u = ξ₁.pullback u + ξ₂.pullback u := by
  obtain ⟨θ, rfl, rfl⟩ := exists_pushout_fst_eq_and_pushout_snd_eq ξ₁ ξ₂
  simp only [← pushout_add, pushout_pullback]

/-- The **negative** of a class is its cobase change along `-𝟙 X`. -/
noncomputable instance : Neg (E.Ext1 Z X) where
  neg ξ := ξ.pushout (-𝟙 X)

/-- The negative of a class is its cobase change along `-𝟙 X`. -/
theorem neg_eq_pushout (ξ : E.Ext1 Z X) : -ξ = ξ.pushout (-𝟙 X) := (rfl)

/-- The negative of a class is its base change along `-𝟙 Z`. -/
theorem neg_eq_pullback (ξ : E.Ext1 Z X) : -ξ = ξ.pullback (-𝟙 Z) := by
  induction ξ using induction with
  | h e => exact pushout_mk_eq_pullback_mk (-𝟙 e.obj) (by simp) (by simp)

/-- The cobase change along the zero multiple of `𝟙 X` is zero. -/
private theorem pushout_zero_smul (S : Type*) [Semiring S] [Module S (X ⟶ X)] (ξ : E.Ext1 Z X) :
    ξ.pushout ((0 : S) • 𝟙 X) = 0 := by
  rw [zero_smul, pushout_zero]

/-- The cobase change along a successor multiple of `𝟙 X` adds the class to the cobase change along
the preceding multiple. -/
private theorem pushout_add_one_smul {S : Type*} [Semiring S] [Module S (X ⟶ X)]
    (n : S) (ξ : E.Ext1 Z X) :
    ξ.pushout ((n + 1) • 𝟙 X) = ξ.pushout (n • 𝟙 X) + ξ := by
  rw [add_smul, one_smul, pushout_add, pushout_id]

/-- The successor law for integer multiples, in the form required of `zsmul`. -/
private theorem pushout_ofNat_succ_smul (n : ℕ) (ξ : E.Ext1 Z X) :
    ξ.pushout (Int.ofNat n.succ • 𝟙 X) = ξ.pushout (Int.ofNat n • 𝟙 X) + ξ := by
  simpa only [Int.ofNat_eq_natCast, Nat.cast_succ] using pushout_add_one_smul (n : ℤ) ξ

/-- The negation law for integer multiples, in the form required of `zsmul`. -/
private theorem pushout_negSucc_smul (n : ℕ) (ξ : E.Ext1 Z X) :
    ξ.pushout (Int.negSucc n • 𝟙 X) = -ξ.pushout ((n.succ : ℤ) • 𝟙 X) := by
  rw [neg_eq_pushout, pushout_pushout, Preadditive.comp_neg, Category.comp_id, Int.negSucc_eq,
    Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_smul]

/-- **The Baer sum makes `Ext¹_E(Z, X)` an abelian group**, with the class of the split conflation
as zero. The multiples of a class are its cobase changes along the multiples of `𝟙 X`, so that the
`ℕ`- and `ℤ`-module structures agree definitionally with those of an `R`-linear category. -/
noncomputable instance : AddCommGroup (E.Ext1 Z X) where
  -- The `by` blocks keep the private lemmas out of the exposed instance body.
  add_assoc ξ₁ ξ₂ ξ₃ := by
    obtain ⟨θ, rfl, rfl⟩ := exists_pushout_fst_eq_and_pushout_snd_eq ξ₁ ξ₂
    obtain ⟨θ', rfl, rfl⟩ := exists_pushout_fst_eq_and_pushout_snd_eq θ ξ₃
    simp only [pushout_pushout, ← pushout_add, add_assoc]
  zero_add ξ := by simpa using (pushout_add ξ 0 (𝟙 X)).symm
  add_zero ξ := by simpa using (pushout_add ξ (𝟙 X) 0).symm
  nsmul n ξ := ξ.pushout (n • 𝟙 X)
  nsmul_zero ξ := by exact pushout_zero_smul ℕ ξ
  nsmul_succ n ξ := by exact pushout_add_one_smul n ξ
  zsmul n ξ := ξ.pushout (n • 𝟙 X)
  zsmul_zero' ξ := by exact pushout_zero_smul ℤ ξ
  zsmul_succ' n ξ := by exact pushout_ofNat_succ_smul n ξ
  zsmul_neg' n ξ := by exact pushout_negSucc_smul n ξ
  neg_add_cancel ξ := by
    rw [neg_eq_pushout]
    simpa using (pushout_add ξ (-𝟙 X) (𝟙 X)).symm
  add_comm ξ₁ ξ₂ := by
    obtain ⟨θ, rfl, rfl⟩ := exists_pushout_fst_eq_and_pushout_snd_eq ξ₁ ξ₂
    simp only [← pushout_add, add_comm]

/-- Cobase change along a negated morphism is the negative of the cobase change. -/
@[simp]
theorem pushout_neg (ξ : E.Ext1 Z X) (v : X ⟶ X') : ξ.pushout (-v) = -ξ.pushout v := by
  rw [neg_eq_pushout, pushout_pushout, Preadditive.comp_neg, Category.comp_id]

/-- Cobase change of a negated class is the negative of the cobase change. -/
@[simp]
theorem neg_pushout (ξ : E.Ext1 Z X) (v : X ⟶ X') : (-ξ).pushout v = -ξ.pushout v := by
  rw [neg_eq_pushout, pushout_pushout, Preadditive.neg_comp, Category.id_comp, pushout_neg]

/-- Base change along a negated morphism is the negative of the base change. -/
@[simp]
theorem pullback_neg (ξ : E.Ext1 Z X) (u : Z' ⟶ Z) : ξ.pullback (-u) = -ξ.pullback u := by
  rw [neg_eq_pullback, pullback_pullback, Preadditive.neg_comp, Category.id_comp]

/-- Base change of a negated class is the negative of the base change. -/
@[simp]
theorem neg_pullback (ξ : E.Ext1 Z X) (u : Z' ⟶ Z) : (-ξ).pullback u = -ξ.pullback u := by
  rw [neg_eq_pullback, pullback_pullback, Preadditive.comp_neg, Category.comp_id, pullback_neg]

/-! ### The module structure -/

section Linear

variable (R : Type*) [Semiring R] [Linear R C]

/-- The scalar action on `Ext¹_E(Z, X)` of an `R`-linear category: `r • ξ` is the cobase change of
`ξ` along `r • 𝟙 X`. -/
noncomputable instance : SMul R (E.Ext1 Z X) where
  smul r ξ := ξ.pushout (r • 𝟙 X)

variable {R} in
/-- The scalar action on `Ext¹_E(Z, X)` is cobase change along a multiple of `𝟙 X`. -/
theorem smul_eq_pushout (r : R) (ξ : E.Ext1 Z X) : r • ξ = ξ.pushout (r • 𝟙 X) := (rfl)

/-- `Ext¹_E(Z, X)` is an **`R`-module** when the exact category is `R`-linear. -/
noncomputable instance : Module R (E.Ext1 Z X) where
  one_smul ξ := by rw [smul_eq_pushout, one_smul, pushout_id]
  mul_smul r s ξ := by
    rw [smul_eq_pushout, smul_eq_pushout s, smul_eq_pushout r, pushout_pushout, Linear.comp_smul,
      Category.comp_id, mul_smul]
  smul_zero r := zero_pushout _
  smul_add r ξ₁ ξ₂ := add_pushout _ _ _
  add_smul r s ξ := by
    rw [smul_eq_pushout, smul_eq_pushout r, smul_eq_pushout s, add_smul, pushout_add]
  zero_smul ξ := by rw [smul_eq_pushout, zero_smul, pushout_zero]

variable {R}

/-- The scalar action on `Ext¹_E(Z, X)` is base change along a multiple of `𝟙 Z`. -/
theorem smul_eq_pullback (r : R) (ξ : E.Ext1 Z X) : r • ξ = ξ.pullback (r • 𝟙 Z) := by
  induction ξ using induction with
  | h e => exact pushout_mk_eq_pullback_mk (r • 𝟙 e.obj) (by simp) (by simp)

/-- Cobase change is `R`-linear in the morphism. -/
@[simp]
theorem pushout_smul (r : R) (ξ : E.Ext1 Z X) (v : X ⟶ X') :
    ξ.pushout (r • v) = r • ξ.pushout v := by
  rw [smul_eq_pushout, pushout_pushout, Linear.comp_smul, Category.comp_id]

/-- Cobase change is `R`-linear in the class. -/
@[simp]
theorem smul_pushout (r : R) (ξ : E.Ext1 Z X) (v : X ⟶ X') :
    (r • ξ).pushout v = r • ξ.pushout v := by
  rw [smul_eq_pushout, pushout_pushout, Linear.smul_comp, Category.id_comp, pushout_smul]

/-- Base change is `R`-linear in the morphism. -/
@[simp]
theorem pullback_smul (r : R) (ξ : E.Ext1 Z X) (u : Z' ⟶ Z) :
    ξ.pullback (r • u) = r • ξ.pullback u := by
  rw [smul_eq_pullback r (ξ.pullback u), pullback_pullback, Linear.smul_comp, Category.id_comp]

/-- Base change is `R`-linear in the class. -/
@[simp]
theorem smul_pullback (r : R) (ξ : E.Ext1 Z X) (u : Z' ⟶ Z) :
    (r • ξ).pullback u = r • ξ.pullback u := by
  rw [smul_eq_pullback r ξ, pullback_pullback, Linear.comp_smul, Category.comp_id, pullback_smul]

variable (R)

/-- **Cobase change** along `v : X ⟶ X'`, as an `R`-linear map `Ext¹_E(Z, X) → Ext¹_E(Z, X')`. -/
noncomputable def pushoutLinearMap (v : X ⟶ X') : E.Ext1 Z X →ₗ[R] E.Ext1 Z X' where
  toFun ξ := ξ.pushout v
  map_add' ξ₁ ξ₂ := add_pushout ξ₁ ξ₂ v
  map_smul' r ξ := smul_pushout r ξ v

@[simp]
theorem pushoutLinearMap_apply (v : X ⟶ X') (ξ : E.Ext1 Z X) :
    pushoutLinearMap R v ξ = ξ.pushout v := (rfl)

/-- **Base change** along `u : Z' ⟶ Z`, as an `R`-linear map `Ext¹_E(Z, X) → Ext¹_E(Z', X)`. -/
noncomputable def pullbackLinearMap (u : Z' ⟶ Z) : E.Ext1 Z X →ₗ[R] E.Ext1 Z' X where
  toFun ξ := ξ.pullback u
  map_add' ξ₁ ξ₂ := add_pullback ξ₁ ξ₂ u
  map_smul' r ξ := smul_pullback r ξ u

@[simp]
theorem pullbackLinearMap_apply (u : Z' ⟶ Z) (ξ : E.Ext1 Z X) :
    pullbackLinearMap R u ξ = ξ.pullback u := (rfl)

end Linear

end Ext1

end ExactStructure

end TauCeti
