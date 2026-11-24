/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.Analysis.CStarAlgebra.Idempotent

/-!
# Idempotents and their range projections in C*-categories

An idempotent arrow `e : X ⟶ X` of a C*-category need not be self-adjoint. Its range projection
`TauCeti.CStarCategory.idempotentRangeProjection e` is the range projection of `e` in the
C*-algebra `End X`: the unique self-adjoint idempotent `p` with `p ≫ e = p` and `e ≫ p = e`, that
is, with the range of `e` (in operator notation `e p = p` and `p e = e`). The idempotent `e` is
similar to `p` through an automorphism of `X`.

Splittings of `e` and of `p` through a given object `Y` correspond. A *unitary splitting* of a
self-adjoint idempotent `p` through `Y` is an isometry `v : Y ⟶ X`, that is
`v ≫ dagger v = 𝟙 Y`, whose range projection `dagger v ≫ v` is `p`. If `v` is one for the range
projection of `e`, then `v` and `e ≫ dagger v` split `e`. Conversely, if `i : Y ⟶ X` and
`r : X ⟶ Y` split `e`, then `a = i ≫ dagger i` is invertible in `End Y`
(`CategoryTheory.End.isStrictlyPositive_self_comp_dagger_iff`), and `a ^ (-1/2) ≫ i` is a unitary
splitting of the range projection. Unitary splittings of one projection through two objects differ
by a unique unitary (`TauCeti.isUnitary_comp_dagger_of_dagger_comp_eq`); this conjugacy holds for
unitary splittings of self-adjoint projections only, not for arbitrary splittings of idempotents.

Hence a C*-category is idempotent complete in Mathlib's sense, the property characterizing
categories equivalent to their `Karoubi` envelope, exactly when every self-adjoint idempotent has a
unitary splitting.

## Main declarations

* `TauCeti.CStarCategory.idempotentRangeProjection`: the range projection of an endomorphism.
* `TauCeti.CStarCategory.eq_idempotentRangeProjection_iff`: its characterization as the
  self-adjoint arrow `q` with `q ≫ e = q` and `e ≫ q = e`.
* `TauCeti.CStarCategory.exists_iso_inv_comp_idempotentRangeProjection_comp_hom_eq`: an idempotent
  is similar to its range projection.
* `CategoryTheory.End.isStrictlyPositive_self_comp_dagger_iff`: `f ≫ dagger f` is invertible
  exactly when `f` is a split monomorphism.
* `TauCeti.CStarCategory.exists_split_iff`: an idempotent splits through `Y` exactly when its
  range projection has a unitary splitting through `Y`.
* `TauCeti.CStarCategory.isIdempotentComplete_iff`: a C*-category is idempotent complete exactly
  when all self-adjoint idempotents have unitary splittings.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Proposition 4.6.2.
* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C]

/-- An idempotent arrow is an idempotent element of the endomorphism monoid. -/
private theorem isIdempotentElem_of {X : C} {e : X ⟶ X} (he : e ≫ e = e) :
    IsIdempotentElem (End.of e) :=
  End.ext he

section Dagger

variable [Preadditive C] [DaggerCategory C] [DaggerPreadditive C] {X : C} {e q : X ⟶ X}

/-- The **range projection** of an arrow `e : X ⟶ X`: the range projection
`TauCeti.idempotentRangeProjection` of `e` in the star ring `End X`. For an idempotent `e` of a
C*-category it is the unique self-adjoint idempotent with the range of `e`
(`TauCeti.CStarCategory.eq_idempotentRangeProjection_iff`); for other arrows it carries no
meaning. -/
def idempotentRangeProjection (e : X ⟶ X) : X ⟶ X :=
  (TauCeti.idempotentRangeProjection (End.of e)).asHom

/-- As an endomorphism, the range projection of `e` is that of `End.of e` in `End X`. -/
@[simp] theorem of_idempotentRangeProjection (e : X ⟶ X) :
    End.of (idempotentRangeProjection e) = TauCeti.idempotentRangeProjection (End.of e) := (rfl)

/-- The range projection `p` of an idempotent `e` lies in the range of `e`: `p ≫ e = p`. -/
@[simp, reassoc] theorem idempotentRangeProjection_comp (he : e ≫ e = e) :
    idempotentRangeProjection e ≫ e = idempotentRangeProjection e :=
  congrArg End.asHom (isIdempotentElem_of he).mul_idempotentRangeProjection

/-- A self-adjoint idempotent is its own range projection. -/
@[simp] theorem idempotentRangeProjection_eq (hq : dagger q = q) (hqq : q ≫ q = q) :
    idempotentRangeProjection q = q :=
  congrArg End.asHom
    (IsStarProjection.idempotentRangeProjection_eq ⟨isIdempotentElem_of hqq, End.ext hq⟩)

end Dagger

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {X Y : C} {e q : X ⟶ X}

/-- The range projection of an idempotent is self-adjoint. -/
@[simp] theorem dagger_idempotentRangeProjection (he : e ≫ e = e) :
    dagger (idempotentRangeProjection e) = idempotentRangeProjection e :=
  congrArg End.asHom
    (isIdempotentElem_of he).isStarProjection_idempotentRangeProjection.isSelfAdjoint

/-- The range projection of an idempotent is idempotent. -/
@[simp, reassoc] theorem idempotentRangeProjection_comp_self (he : e ≫ e = e) :
    idempotentRangeProjection e ≫ idempotentRangeProjection e = idempotentRangeProjection e :=
  congrArg End.asHom
    (isIdempotentElem_of he).isStarProjection_idempotentRangeProjection.isIdempotentElem

/-- The range of an idempotent `e` lies in that of its range projection `p`: `e ≫ p = e`. -/
@[simp, reassoc] theorem comp_idempotentRangeProjection (he : e ≫ e = e) :
    e ≫ idempotentRangeProjection e = e :=
  congrArg End.asHom (isIdempotentElem_of he).idempotentRangeProjection_mul

/-- The range projection of an idempotent `e` is the only self-adjoint arrow `q` with
`q ≫ e = q` and `e ≫ q = e`. -/
theorem eq_idempotentRangeProjection_iff (he : e ≫ e = e) (hq : dagger q = q) :
    q = idempotentRangeProjection e ↔ q ≫ e = q ∧ e ≫ q = e := by
  have := (isIdempotentElem_of he).eq_idempotentRangeProjection_iff (q := End.of q) (End.ext hq)
  simpa only [End.ext_iff, End.mul_asHom, idempotentRangeProjection] using this

/-- An idempotent `e` is similar to its range projection `p`: `e = u⁻¹ p u` for an automorphism
`u` of `X`, written `u.inv ≫ p ≫ u.hom = e` in categorical composition order. -/
theorem exists_iso_inv_comp_idempotentRangeProjection_comp_hom_eq (he : e ≫ e = e) :
    ∃ u : X ≅ X, u.inv ≫ idempotentRangeProjection e ≫ u.hom = e := by
  obtain ⟨c, hc⟩ := (isIdempotentElem_of he).isConj_idempotentRangeProjection
  have hc' : idempotentRangeProjection e ≫ c.val.asHom = c.val.asHom ≫ e := congrArg End.asHom hc
  have hci : c.inv.asHom ≫ c.val.asHom = 𝟙 X := congrArg End.asHom c.val_inv
  refine ⟨⟨c.val.asHom, c.inv.asHom, congrArg End.asHom c.inv_val, hci⟩, ?_⟩
  dsimp only
  rw [hc', reassoc_of% hci]

end TauCeti.CStarCategory

namespace CategoryTheory.End

open TauCeti TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {X Y : C}

/-- For an arrow `f : Y ⟶ X` of a C*-category, the positive endomorphism `f†f`, that is
`f ≫ dagger f`, is strictly positive, equivalently invertible in `End Y`, exactly when `f` is a
split monomorphism. -/
theorem isStrictlyPositive_self_comp_dagger_iff (f : Y ⟶ X) :
    IsStrictlyPositive (End.of (f ≫ dagger f)) ↔ IsSplitMono f := by
  refine ⟨fun ha => ?_, fun _ => ?_⟩
  · obtain ⟨u, hu⟩ := ha.isUnit
    refine .mk' ⟨dagger f ≫ u.inv.asHom, ?_⟩
    have hu' : (u : End Y).asHom = f ≫ dagger f := by rw [hu]
    rw [← Category.assoc, ← hu', ← End.mul_asHom, u.inv_val, End.one_asHom]
  -- With `r` a retraction of `f`, `e = r ≫ f` is idempotent with range projection `p`, and
  -- `f ≫ dagger f` has inverse `dagger r ≫ p ≫ r`.
  obtain ⟨r, hfr⟩ : ∃ r : X ⟶ Y, f ≫ r = 𝟙 Y := ⟨retraction f, IsSplitMono.id f⟩
  obtain ⟨e, hre⟩ : ∃ e : X ⟶ X, r ≫ f = e := ⟨_, rfl⟩
  have he : e ≫ e = e := by rw [← hre, Category.assoc, reassoc_of% hfr]
  have hfe : f ≫ e = f := by rw [← hre, reassoc_of% hfr]
  have hfp : f ≫ idempotentRangeProjection e = f := by
    rw [← hfe, Category.assoc, comp_idempotentRangeProjection he]
  have hpf : idempotentRangeProjection e ≫ dagger f = dagger f := by
    rw [← dagger_idempotentRangeProjection he, ← dagger_comp, hfp]
  have hep : dagger e ≫ idempotentRangeProjection e = idempotentRangeProjection e := by
    simpa only [dagger_comp, dagger_idempotentRangeProjection he] using
      congrArg dagger (idempotentRangeProjection_comp he)
  have hdf : dagger f ≫ dagger r = dagger e := by rw [← dagger_comp, hre]
  refine IsUnit.isStrictlyPositive
    ⟨⟨_, .of (dagger r ≫ idempotentRangeProjection e ≫ r), ?_, ?_⟩, rfl⟩
    (self_comp_dagger_nonneg f)
  · ext
    simp only [End.mul_asHom, End.one_asHom, Category.assoc]
    rw [reassoc_of% hre, idempotentRangeProjection_comp_assoc he, hpf, ← dagger_comp, hfr,
      dagger_id]
  · ext
    simp only [End.mul_asHom, End.one_asHom, Category.assoc]
    rw [reassoc_of% hdf, reassoc_of% hep, reassoc_of% hfp, hfr]

end CategoryTheory.End

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {X Y : C} {e : X ⟶ X}

/-- A splitting of an idempotent `e` gives a unitary splitting of its range projection through the
same object: if `i ≫ r = 𝟙 Y` and `r ≫ i = e`, then the polar part `a ^ (-1/2) ≫ i` of `i`, for
the invertible positive endomorphism `a = i ≫ dagger i` of `Y`, is an isometry with range
projection `idempotentRangeProjection e`. -/
theorem exists_isometry_of_split {i : Y ⟶ X} {r : X ⟶ Y} (hir : i ≫ r = 𝟙 Y) (hri : r ≫ i = e) :
    ∃ v : Y ⟶ X, v ≫ dagger v = 𝟙 Y ∧ dagger v ≫ v = idempotentRangeProjection e := by
  have he : e ≫ e = e := by rw [← hri, Category.assoc, reassoc_of% hir]
  have hie : i ≫ e = i := by rw [← hri, reassoc_of% hir]
  have ha : IsStrictlyPositive (End.of (i ≫ dagger i)) :=
    (End.isStrictlyPositive_self_comp_dagger_iff i).2 (.mk' ⟨r, hir⟩)
  -- The isometry is `v = s ≫ i` for `s = a ^ (-1/2)` with `a = i ≫ dagger i`; `s` is
  -- self-adjoint and invertible.
  obtain ⟨s, hs_def⟩ : ∃ s : End Y, s = End.of (i ≫ dagger i) ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  have hss : dagger s.asHom = s.asHom := by
    rw [hs_def]
    exact congrArg End.asHom (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hsas : s * End.of (i ≫ dagger i) * s = 1 := hs_def ▸ CFC.conjugate_rpow_neg_one_half _
  obtain ⟨t, ht⟩ := ha.isUnit.cfcRpow (-(1 / 2) : ℝ) ha.nonneg
  rw [← hs_def] at ht
  have hts : t.inv.asHom ≫ s.asHom = 𝟙 Y := by
    rw [← End.mul_asHom, ← ht, t.val_inv, End.one_asHom]
  have hv : s.asHom ≫ i ≫ dagger (s.asHom ≫ i) = 𝟙 Y := by
    rw [dagger_comp, hss]
    simpa only [End.mul_asHom, End.one_asHom, Category.assoc] using congrArg End.asHom hsas
  refine ⟨s.asHom ≫ i, by simpa only [Category.assoc] using hv, ?_⟩
  refine (eq_idempotentRangeProjection_iff (q := dagger (s.asHom ≫ i) ≫ s.asHom ≫ i) he
    (by simp)).2 ⟨?_, ?_⟩
  · simp only [Category.assoc, hie]
  · -- `e = r ≫ i` and `i = t⁻¹ ≫ s ≫ i` factors through the isometry `s ≫ i`.
    have hvv : (s.asHom ≫ i) ≫ dagger (s.asHom ≫ i) ≫ s.asHom ≫ i = s.asHom ≫ i := by
      rw [Category.assoc, reassoc_of% hv]
    calc e ≫ dagger (s.asHom ≫ i) ≫ s.asHom ≫ i
        = r ≫ t.inv.asHom ≫ (s.asHom ≫ i) ≫ dagger (s.asHom ≫ i) ≫ s.asHom ≫ i := by
          rw [← hri, ← Category.assoc t.inv.asHom, reassoc_of% hts, Category.assoc]
      _ = e := by rw [hvv, reassoc_of% hts, hri]

/-- An idempotent `e` splits through `Y` exactly when its range projection has a unitary splitting
through `Y`: an isometry `v : Y ⟶ X`, with `v ≫ dagger v = 𝟙 Y`, whose range projection
`dagger v ≫ v` is `idempotentRangeProjection e`. -/
theorem exists_split_iff (he : e ≫ e = e) (Y : C) :
    (∃ (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e) ↔
      ∃ v : Y ⟶ X, v ≫ dagger v = 𝟙 Y ∧ dagger v ≫ v = idempotentRangeProjection e := by
  refine ⟨fun ⟨i, r, hir, hri⟩ => exists_isometry_of_split hir hri, fun ⟨v, hv, hvp⟩ => ?_⟩
  -- `v` lies in the range of `e`, so `v` and `e ≫ dagger v` split `e`.
  have hve : v ≫ e = v :=
    calc v ≫ e = v ≫ (dagger v ≫ v) ≫ e := by rw [Category.assoc, reassoc_of% hv]
      _ = v := by rw [hvp, idempotentRangeProjection_comp he, ← hvp, reassoc_of% hv]
  exact ⟨v, e ≫ dagger v, by rw [reassoc_of% hve, hv], by
    rw [Category.assoc, hvp, comp_idempotentRangeProjection he]⟩

/-- A C*-category is idempotent complete exactly when every self-adjoint idempotent `p : X ⟶ X`
has a unitary splitting: an isometry `v : Y ⟶ X`, with `v ≫ dagger v = 𝟙 Y`, such that
`dagger v ≫ v = p`. -/
theorem isIdempotentComplete_iff : IsIdempotentComplete C ↔
    ∀ (X : C) (p : X ⟶ X), dagger p = p → p ≫ p = p →
      ∃ (Y : C) (v : Y ⟶ X), v ≫ dagger v = 𝟙 Y ∧ dagger v ≫ v = p := by
  refine ⟨fun h X p hp hpp => ?_, fun h => ⟨fun X e he => ?_⟩⟩
  · obtain ⟨Y, i, r, hir, hri⟩ := h.idempotents_split X p hpp
    obtain ⟨v, hv, hvp⟩ := exists_isometry_of_split hir hri
    exact ⟨Y, v, hv, hvp.trans (idempotentRangeProjection_eq hp hpp)⟩
  · obtain ⟨Y, v, hv, hvp⟩ := h X (idempotentRangeProjection e)
      (dagger_idempotentRangeProjection he) (idempotentRangeProjection_comp_self he)
    exact ⟨Y, (exists_split_iff he Y).2 ⟨v, hv, hvp⟩⟩

end TauCeti.CStarCategory
