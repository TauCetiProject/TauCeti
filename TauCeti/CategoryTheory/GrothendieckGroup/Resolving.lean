/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolving
public import TauCeti.CategoryTheory.GrothendieckGroup.Resolution
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The resolution theorem for a resolving subcategory

Let `E` be an exact structure on an additive category `C` and let `P` be a resolving property:
it contains a zero object, is closed under binary direct sums and extensions, is closed under
kernels of deflations between its objects, and every object of `C` admits a finite
`P`-resolution. This file proves Weibel's **resolution theorem** in this generality: the
inclusion of the full subcategory on `P`, with its induced exact structure, induces an isomorphism

```text
K₀(P) ≃ K₀(C)
```

whose inverse sends the class of an object `X` to the alternating class
`[Q₀] - [Q₁] + ⋯ + (-1)ⁿ [Kₙ]` of any finite `P`-resolution of `X`, computed in `K₀(P)`.

Unlike the projective case of `TauCeti/CategoryTheory/GrothendieckGroup/ProjectiveResolution.lean`,
conflations with a resolving quotient need not split, so neither Schanuel's lemma nor the horseshoe
lemma is available. Both are replaced by pullbacks of deflations and the Noether conflation
`TauCeti.ExactStructure.exists_conflation_comp'`: two first steps `K ↪ Q ↠ X` and `K' ↪ Q' ↠ X`
are compared through a single object `Q''` of `P` covering their pullback, and the dimension
shifting of `TauCeti.ExactStructure.IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₂`
keeps the inductions on lengths well founded.

## Main results

* `TauCeti.ExactStructure.IsResolving.eulerClassFullSubcategory_eq_eulerClassFullSubcategory`:
  **the alternating class of a finite `P`-resolution in `K₀(P)` depends only on the resolved
  object**.
* `TauCeti.ExactStructure.IsResolving.eulerClassOf_eq_add_of_conflation`: the Euler class is
  additive on the conflations of `C`.
* `TauCeti.ExactStructure.IsResolving.resolutionEquiv`,
  `TauCeti.ExactStructure.IsResolving.resolutionEquiv_of` and
  `TauCeti.ExactStructure.IsResolving.resolutionEquiv_symm_of`: **the resolution theorem**.

## Implementation notes

The Euler class of an object is `TauCeti.ExactStructure.eulerClassOf`, with values in the exact
`K₀` of `TauCeti.ExactStructure.fullSubcategory`; the exact structure
`TauCeti.ExactStructure.resolvingSubcategory` is by definition that induced structure, which is
how the two are identified in the statement of the resolution theorem.

Well-definedness is proved by induction on the length of one of the two resolutions, and
additivity by induction on the length of a resolution of the quotient term; both are stated as
`private` auxiliaries over an explicit bound.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Theorem 7.6 and Lemma 7.6.1: the resolution theorem and the independence of the Euler class.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  Proposition 2.12 and Lemma 3.5, for base change of conflations and the Noether conflation.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C} {P : ObjectProperty C} [E.IsResolving P]

namespace ExactStructure

namespace IsResolving

open FiniteResolution

/-- The extension closure of a resolving property, which defines its induced exact structure. -/
local notation "hP" => (IsResolving.isExtensionClosed (E := E) (P := P))

section EulerClass

variable [LocallySmall.{w} C] [ObjectProperty.EssentiallySmall.{w} P]

/-- An object satisfying `P` is its own resolution, and every other resolution of it has the same
alternating class: the kernel of the first step is again in `P`, by closure under kernels. -/
private theorem eulerClassFullSubcategory_base_eq {X : C} (hX : P X)
    (s : E.FiniteResolution P X) :
    (base (E := E) hX).eulerClassFullSubcategory hP = s.eulerClassFullSubcategory hP := by
  induction s with
  | base _ => rfl
  | @step K Q X hQ i p zero hp s ih =>
      have hK : P K := IsResolving.prop_X₁ (S := ShortComplex.mk i p zero) hp hQ hX
      have key : (ExactK0.of ⟨Q, hQ⟩ : ExactK0 (E.fullSubcategory P hP)) =
          ExactK0.of ⟨K, hK⟩ + ExactK0.of ⟨X, hX⟩ :=
        ExactK0.of_conflation_fullSubcategory hP (S := ShortComplex.mk i p zero) hp hK hX
      rw [eulerClassFullSubcategory_step, ← ih hK, eulerClassFullSubcategory_base,
        eulerClassFullSubcategory_base, key]
      abel

/-- The inductive core of
`TauCeti.ExactStructure.IsResolving.eulerClassFullSubcategory_eq_eulerClassFullSubcategory`, on
the length of the first resolution.

For two first steps `K ↪ Q ↠ X` and `K' ↪ Q' ↠ X`, cover the pullback `Y` of `Q ↠ X` and
`Q' ↠ X` by an object `Q''` of `P`, with kernel `K''`. The kernels `L` of `Q'' ↠ Q'` and `L'` of
`Q'' ↠ Q` lie in `P`, and `K'' ↪ L ↠ K`, `K'' ↪ L' ↠ K'` are conflations. The induction hypothesis
compares the given resolutions of `K` and `K'` with the ones through `L` and `L'`; dimension
shifting makes the resolution of `K'` short enough for this. -/
private theorem eulerClassFullSubcategory_eq_aux (n : ℕ) :
    ∀ {X : C} (r s : E.FiniteResolution P X), r.length ≤ n →
      r.eulerClassFullSubcategory hP = s.eulerClassFullSubcategory hP := by
  induction n with
  | zero =>
      intro X r s h
      cases r with
      | base hX => exact eulerClassFullSubcategory_base_eq hX s
      | step => simp at h
  | succ n ih =>
      intro X r s h
      cases r with
      | base hX => exact eulerClassFullSubcategory_base_eq hX s
      | @step K Q X hQ i p zero hp r =>
          cases s with
          | base hX => exact (eulerClassFullSubcategory_base_eq hX _).symm
          | @step K' Q' X hQ' i' p' zero' hp' s =>
              have hr : r.length ≤ n := by simpa using h
              have : HasPullback p p' :=
                E.hasPullbacks_deflations.hasPullback p' (E.isDeflation_g hp)
              have sq : IsPullback (pullback.fst p p') (pullback.snd p p') p p' :=
                IsPullback.of_hasPullback _ _
              have hY₁ := E.conflation_baseChange hp sq
              rw [baseChange_def] at hY₁
              have hY₂ := E.conflation_baseChange hp' sq.flip
              rw [baseChange_def] at hY₂
              obtain ⟨K'', Q'', i'', p'', h'', hQ'', hc'', hK''⟩ :=
                IsResolving.exists_conflation_prop_X₂_admitsFiniteResolution_X₁
                  (E := E) (P := P) (pullback p p')
              let t := ((E.admitsFiniteResolution_iff P).mp hK'').some
              obtain ⟨L, c, α, β, hc, hβ, hLc, hKL, -, -⟩ := E.exists_conflation_comp' hY₁ hc''
              obtain ⟨L', c', α', β', hc', hβ', hLc', hKL', -, -⟩ :=
                E.exists_conflation_comp' hY₂ hc''
              have hL : P L := IsResolving.prop_X₁ (S := ShortComplex.mk _ _ hc) hLc hQ'' hQ'
              have hL' : P L' := IsResolving.prop_X₁ (S := ShortComplex.mk _ _ hc') hLc' hQ'' hQ
              obtain ⟨u, hu⟩ := IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₂
                (S := ShortComplex.mk i' p' zero') hp' hQ' ⟨.step hQ i p zero hp r, by simpa⟩
              have e₁ := ih r (.step hL β α hβ hKL t) hr
              have e₂ := ih u s hu
              have e₃ := ih u (.step hL' β' α' hβ' hKL' t) hu
              have k₁ : (ExactK0.of ⟨Q'', hQ''⟩ : ExactK0 (E.fullSubcategory P hP)) =
                  ExactK0.of ⟨L, hL⟩ + ExactK0.of ⟨Q', hQ'⟩ :=
                ExactK0.of_conflation_fullSubcategory hP (S := ShortComplex.mk _ _ hc) hLc hL hQ'
              have k₂ : (ExactK0.of ⟨Q'', hQ''⟩ : ExactK0 (E.fullSubcategory P hP)) =
                  ExactK0.of ⟨L', hL'⟩ + ExactK0.of ⟨Q, hQ⟩ :=
                ExactK0.of_conflation_fullSubcategory hP (S := ShortComplex.mk _ _ hc') hLc' hL' hQ
              rw [eulerClassFullSubcategory_step, eulerClassFullSubcategory_step, e₁, ← e₂, e₃,
                eulerClassFullSubcategory_step, eulerClassFullSubcategory_step]
              linear_combination (norm := module) k₁ - k₂

/-- **The Euler class in the `K₀` of a resolving subcategory depends only on the resolved
object.** Any two finite `P`-resolutions of the same object have the same alternating class in the
exact `K₀` of the structure induced on `P`, whatever their lengths. -/
theorem eulerClassFullSubcategory_eq_eulerClassFullSubcategory {X : C}
    (r s : E.FiniteResolution P X) :
    r.eulerClassFullSubcategory hP = s.eulerClassFullSubcategory hP :=
  eulerClassFullSubcategory_eq_aux _ r s le_rfl

/-- Every finite `P`-resolution of `X` computes `TauCeti.ExactStructure.eulerClassOf`. -/
theorem eulerClassOf_eq {X : C} (hX : E.admitsFiniteResolution P X)
    (r : E.FiniteResolution P X) :
    E.eulerClassOf hP hX = r.eulerClassFullSubcategory hP :=
  ExactStructure.eulerClassOf_eq_of_forall_eulerClassFullSubcategory_eq hP hX r fun s =>
    eulerClassFullSubcategory_eq_eulerClassFullSubcategory s r

/-- On an object satisfying `P` the Euler class is the class of that object. -/
@[simp]
theorem eulerClassOf_of_prop {X : C} (hX : P X) (h : E.admitsFiniteResolution P X) :
    E.eulerClassOf hP h = ExactK0.of (⟨X, hX⟩ : P.FullSubcategory) := by
  rw [eulerClassOf_eq h (.base hX), eulerClassFullSubcategory_base]

/-- **The Euler class drops by one step along a conflation with resolving middle term**:
`χ(X) = [Q] - χ(K)` for a conflation `K ↪ Q ↠ X` with `P Q`. -/
theorem eulerClassOf_eq_sub_of_conflation {K Q X : C} (hQ : P Q) {i : K ⟶ Q} {p : Q ⟶ X}
    {zero : i ≫ p = 0} (hp : E.Conflation (ShortComplex.mk i p zero))
    (hK : E.admitsFiniteResolution P K) (hX : E.admitsFiniteResolution P X) :
    E.eulerClassOf hP hX = ExactK0.of (⟨Q, hQ⟩ : P.FullSubcategory) - E.eulerClassOf hP hK := by
  rw [eulerClassOf_eq hX (.step hQ i p zero hp ((E.admitsFiniteResolution_iff P).mp hK).some),
    eulerClassFullSubcategory_step, eulerClassOf_eq hK]

/-- The Euler class is invariant under isomorphism of the resolved object. -/
theorem eulerClassOf_congr {X Y : C} (e : X ≅ Y) (hX : E.admitsFiniteResolution P X)
    (hY : E.admitsFiniteResolution P Y) : E.eulerClassOf hP hX = E.eulerClassOf hP hY := by
  have := ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P
  rw [eulerClassOf_eq hY (((E.admitsFiniteResolution_iff P).mp hX).some.ofIso e),
    eulerClassFullSubcategory_ofIso]
  exact eulerClassOf_eq hX _

/-- Additivity of the Euler class on a conflation whose quotient term satisfies `P`. Cover the
middle term by `Q ↠ X₂` with kernel `K`; the kernel `M` of `Q ↠ X₂ ↠ X₃` lies in `P`, and
`K ↪ M ↠ X₁` computes the Euler class of `X₁`. -/
private theorem eulerClassOf_eq_add_of_prop_X₃ {S : ShortComplex C} (hS : E.Conflation S)
    (h₃ : P S.X₃) (a₁ : E.admitsFiniteResolution P S.X₁)
    (a₂ : E.admitsFiniteResolution P S.X₂) (a₃ : E.admitsFiniteResolution P S.X₃) :
    E.eulerClassOf hP a₂ = E.eulerClassOf hP a₁ + E.eulerClassOf hP a₃ := by
  obtain ⟨K, Q, i, a, hia, hQ, hc, hK⟩ :=
    IsResolving.exists_conflation_prop_X₂_admitsFiniteResolution_X₁ (E := E) (P := P) S.X₂
  obtain ⟨M, c, α, β, hc', hβ, hMc, hKM, -, -⟩ := E.exists_conflation_comp' hS hc
  have hM : P M := IsResolving.prop_X₁ (S := ShortComplex.mk _ _ hc') hMc hQ h₃
  have key : (ExactK0.of ⟨Q, hQ⟩ : ExactK0 (E.fullSubcategory P hP)) =
      ExactK0.of ⟨M, hM⟩ + ExactK0.of ⟨S.X₃, h₃⟩ :=
    ExactK0.of_conflation_fullSubcategory hP (S := ShortComplex.mk _ _ hc') hMc hM h₃
  rw [eulerClassOf_eq_sub_of_conflation hQ hc hK a₂,
    eulerClassOf_eq_sub_of_conflation hM hKM hK a₁, eulerClassOf_of_prop h₃, key]
  abel

/-- The inductive core of `TauCeti.ExactStructure.IsResolving.eulerClassOf_eq_add_of_conflation`,
on the length of a resolution of the quotient term.

For `X₁ ↪ X₂ ↠ X₃` and a first step `K ↪ Q ↠ X₃`, the pullback `Y` of `X₂ ↠ X₃` along `Q ↠ X₃`
is an extension `X₁ ↪ Y ↠ Q`, handled by the case of a resolving quotient, and an extension
`K ↪ Y ↠ X₂`. Covering `Y` by `Q' ↠ Y` with kernel `K'`, the kernel `M` of `Q' ↠ Y ↠ X₂` is an
extension `K' ↪ M ↠ K` whose quotient has a shorter resolution. -/
private theorem eulerClassOf_add_aux (n : ℕ) :
    ∀ {S : ShortComplex C}, E.Conflation S →
      (∃ t : E.FiniteResolution P S.X₃, t.length ≤ n) →
      ∀ (a₁ : E.admitsFiniteResolution P S.X₁) (a₂ : E.admitsFiniteResolution P S.X₂)
        (a₃ : E.admitsFiniteResolution P S.X₃),
        E.eulerClassOf hP a₂ = E.eulerClassOf hP a₁ + E.eulerClassOf hP a₃ := by
  have := ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P
  induction n with
  | zero =>
      rintro S hS ⟨t, ht⟩ a₁ a₂ a₃
      exact eulerClassOf_eq_add_of_prop_X₃ hS (by simpa using t.prop_syzygy ht) a₁ a₂ a₃
  | succ n ih =>
      intro S hS ht a₁ a₂ a₃
      obtain ⟨KZ, QZ, iZ, pZ, hZ, hQZ, hcZ, hKZ⟩ :=
        E.exists_conflation_of_exists_finiteResolution_length_le_succ ht
      have : HasPullback S.g pZ :=
        E.hasPullbacks_deflations.hasPullback pZ (E.isDeflation_g hS)
      have sq : IsPullback (pullback.fst S.g pZ) (pullback.snd S.g pZ) S.g pZ :=
        IsPullback.of_hasPullback _ _
      have hY₁ := E.conflation_baseChange hS sq
      rw [baseChange_def] at hY₁
      have hY₂ := E.conflation_baseChange hcZ sq.flip
      rw [baseChange_def] at hY₂
      obtain ⟨K', Q', i', p', h', hQ', hc', hK'⟩ :=
        IsResolving.exists_conflation_prop_X₂_admitsFiniteResolution_X₁
          (E := E) (P := P) (pullback S.g pZ)
      obtain ⟨M, c, α, β, hMc', hβ, hMc, hK'M, -, -⟩ := E.exists_conflation_comp' hY₂ hc'
      have aY := IsResolving.finiteResolution (E := E) (P := P) (pullback S.g pZ)
      have aKZ := IsResolving.finiteResolution (E := E) (P := P) KZ
      have aM := IsResolving.finiteResolution (E := E) (P := P) M
      have eY : E.eulerClassOf hP aY =
          E.eulerClassOf hP a₁ + ExactK0.of (⟨QZ, hQZ⟩ : P.FullSubcategory) := by
        rw [eulerClassOf_eq_add_of_prop_X₃ hY₁ hQZ a₁ aY
          (IsResolving.finiteResolution _), eulerClassOf_of_prop hQZ]
      have eM := ih (S := ShortComplex.mk β α hβ) hK'M hKZ hK' aM aKZ
      rw [eulerClassOf_eq_sub_of_conflation hQ' hc' hK' aY] at eY
      rw [eulerClassOf_eq_sub_of_conflation hQ' hMc aM a₂,
        eulerClassOf_eq_sub_of_conflation hQZ hcZ aKZ a₃, eM]
      linear_combination (norm := module) eY

/-- **The Euler class is additive on conflations.** Together with
`TauCeti.ExactStructure.IsResolving.eulerClassOf_eq` it makes the alternating class of a finite
`P`-resolution a conflation-additive invariant of the objects of `C`. -/
theorem eulerClassOf_eq_add_of_conflation {S : ShortComplex C} (hS : E.Conflation S)
    (a₁ : E.admitsFiniteResolution P S.X₁) (a₂ : E.admitsFiniteResolution P S.X₂)
    (a₃ : E.admitsFiniteResolution P S.X₃) :
    E.eulerClassOf hP a₂ = E.eulerClassOf hP a₁ + E.eulerClassOf hP a₃ :=
  eulerClassOf_add_aux _ hS ⟨((E.admitsFiniteResolution_iff P).mp a₃).some, le_rfl⟩ a₁ a₂ a₃

end EulerClass

section ResolutionTheorem

variable [EssentiallySmall.{w} C]

/-- A property of an essentially small category is essentially small. -/
local instance : ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le (Q := ⊤) le_top

/-- **The alternating class of a finite `P`-resolution of `X`, pushed forward along the inclusion,
is the class of `X`.** This is the telescoping computation
`TauCeti.ExactStructure.FiniteResolution.eulerClass_eq_of`, carried out through the inclusion of
the resolving subcategory. -/
@[simp]
theorem map_eulerClassFullSubcategory_eq_of {X : C}
    (r : E.FiniteResolution P X) :
    ExactK0.map P.ι (IsResolving.isConflationExact_ι E P) (r.eulerClassFullSubcategory hP) =
      ExactK0.of X := by
  induction r with
  | base hX => rw [eulerClassFullSubcategory_base, ExactK0.map_of]; rfl
  | @step K Q X hQ i p zero hp r ih =>
      rw [eulerClassFullSubcategory_step, map_sub, ExactK0.map_of, ih,
        ExactK0.of_eq_sub_of_conflation (S := ShortComplex.mk i p zero) hp]
      exact sub_sub_cancel _ _

variable (E P)

/-- The Euler class as a conflation-additive invariant of the objects of `C`. -/
private noncomputable def eulerInvariant :
    ExactK0.AdditiveInvariant E (ExactK0 (E.resolvingSubcategory P)) where
  obj X := E.eulerClassOf hP (IsResolving.finiteResolution X)
  map_iso _ _ e := eulerClassOf_congr e _ _
  map_conflation _ hS := eulerClassOf_eq_add_of_conflation hS _ _ _

/-- **The inverse of the comparison map of the resolution theorem**: the homomorphism sending the
class of an object to the alternating class of any of its finite `P`-resolutions. -/
noncomputable def eulerHom : ExactK0 E →+ ExactK0 (E.resolvingSubcategory P) :=
  ExactK0.lift (eulerInvariant E P)

@[simp] theorem eulerHom_of (X : C) :
    eulerHom E P (ExactK0.of X) = E.eulerClassOf hP (IsResolving.finiteResolution X) :=
  ExactK0.lift_of _ _

/-- **The resolution theorem.** For a resolving property `P` of an exact category, the inclusion
of the full subcategory on `P` induces an isomorphism of exact Grothendieck groups. Its inverse
sends the class of an object to the alternating class of any finite `P`-resolution of it, by
`TauCeti.ExactStructure.IsResolving.resolutionEquiv_symm_of`. -/
noncomputable def resolutionEquiv : ExactK0 (E.resolvingSubcategory P) ≃+ ExactK0 E where
  toFun := ExactK0.map P.ι (IsResolving.isConflationExact_ι E P)
  invFun := eulerHom E P
  map_add' _ _ := map_add _ _ _
  left_inv x := by
    refine DFunLike.congr_fun (ExactK0.hom_ext (f := (eulerHom E P).comp
      (ExactK0.map P.ι (IsResolving.isConflationExact_ι E P))) (g := AddMonoidHom.id _)
      fun Y => ?_) x
    rw [AddMonoidHom.coe_comp, Function.comp_apply, ExactK0.map_of, eulerHom_of,
      AddMonoidHom.id_apply]
    exact eulerClassOf_of_prop Y.property _
  right_inv x := by
    refine DFunLike.congr_fun (ExactK0.hom_ext (f := (ExactK0.map P.ι
      (IsResolving.isConflationExact_ι E P)).comp (eulerHom E P)) (g := AddMonoidHom.id _)
      fun X => ?_) x
    rw [AddMonoidHom.coe_comp, Function.comp_apply, eulerHom_of, AddMonoidHom.id_apply,
      eulerClassOf_eq _ ((E.admitsFiniteResolution_iff P).mp
        (IsResolving.finiteResolution X)).some]
    exact map_eulerClassFullSubcategory_eq_of _

/-- The forward map of the resolution theorem sends a `P`-object to its class in `K₀(C)`. -/
@[simp] theorem resolutionEquiv_of (X : P.FullSubcategory) :
    resolutionEquiv E P (ExactK0.of X) = ExactK0.of X.obj :=
  ExactK0.map_of _ _ _

/-- The inverse map of the resolution theorem sends an object class to its Euler class. -/
@[simp] theorem resolutionEquiv_symm_of (X : C) :
    (resolutionEquiv E P).symm (ExactK0.of X) =
      E.eulerClassOf hP (IsResolving.finiteResolution X) :=
  eulerHom_of E P X

end ResolutionTheorem

end IsResolving

end ExactStructure

end TauCeti
