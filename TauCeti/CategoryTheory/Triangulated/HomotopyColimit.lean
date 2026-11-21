/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Preadditive.Compact
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference

import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import TauCeti.Algebra.Category.Grp.ZModuleEquivalence
import TauCeti.Algebra.Category.ModuleCat.Colimits
import TauCeti.Algebra.Category.ModuleCat.Products

/-!
# Sequential homotopy colimits and the Milnor exact sequence

In a pretriangulated category `T` with countable coproducts, a sequential *Milnor homotopy
colimit* of `X : ℕ ⥤ T` (`X₀ → X₁ → ⋯`) is the cone `M` of `X.sequenceDifference`
(`CategoryTheory.Functor.sequenceDifference`), fitting into a distinguished triangle
`∐ X.obj ──1 - s──▶ ∐ X.obj ──ψ──▶ M ──δ──▶ (∐ X.obj)⟦1⟧`.

We establish:
1. **Mapping out of a compact object:** for `A` compact (`TauCeti.IsCompactForCoproducts A`),
   morphisms `A ⟶ M` factor through some `X.obj N` (`exists_factor_of_milnorTriangle`),
   vanish in `M` iff killed by some transition (`comp_milnorTriangle_eq_zero_iff`), and
   `Hom(A, M)` is the colimit of `Hom(A, X.obj n)` (`isColimitMapCoconeOfMilnorTriangle`).
2. **The generic Milnor exact sequence:** for `F : Tᵒᵖ ⥤ ModuleCat.{v} R` homological taking
   countable coproducts to products, `0 ⟶ lim¹ F((Xₙ)⟦1⟧) ⟶ F(M) ⟶ lim F(Xₙ) ⟶ 0` is a
   natural short exact sequence, with `TauCeti.exists_lift_of_milnorTriangle` for
   `AddCommGrpCat`-valued functors.

## Main definitions

* `TauCeti.coconeOfMilnorTriangle`, `CategoryTheory.Functor.milnorObjToLim`,
  `CategoryTheory.Functor.milnorLimOneToObj`

## Main results

* `TauCeti.surjective_comp_of_milnorTriangle`, `TauCeti.exists_factor_of_milnorTriangle`,
  `TauCeti.comp_milnorTriangle_eq_zero_iff`, `TauCeti.isColimitMapCoconeOfMilnorTriangle`,
  `TauCeti.exists_lift_of_milnorTriangle`
* `CategoryTheory.Functor.milnorLimOneToObj_injective`,
  `CategoryTheory.Functor.exact_milnorLimOneToObj_milnorObjToLim`,
  `CategoryTheory.Functor.milnorObjToLim_surjective`,
  `CategoryTheory.Functor.milnorObjToLim_bijective_of_subsingleton_limOne`,
  `CategoryTheory.Functor.milnorObjToLim_naturality`,
  `CategoryTheory.Functor.milnorLimOneToObj_naturality`

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. **12** (1962), 337–341.
* A. Neeman, *Triangulated categories*, Princeton Univ. Press (2001), Section 1.6–1.7.
* S. Schwede, *Symmetric spectra*, Chapter II, Def. 5.4 and Lemma 5.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped DirectSum

universe uR w v u

namespace TauCeti

section CompactMapping

variable {T : Type u} [Category.{v} T] [Preadditive T]

private def coyonedaToHom (A : T) (X : ℕ ⥤ T) (k : ℕ) :
    ↑((X ⋙ preadditiveCoyonedaObj A).obj k) ≃+ (A ⟶ X.obj k) :=
  { toFun := id, invFun := id, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
    map_add' := fun _ _ ↦ rfl }

/-- Additive equivalence identifying `⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)` with
`⨁ n, (A ⟶ X.obj n)`. -/
private def seqDirectSumEquiv (A : T) (X : ℕ ⥤ T) :
    (⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) ≃+ (⨁ n, (A ⟶ X.obj n)) :=
  DFinsupp.mapRange.addEquiv (coyonedaToHom A X)

private theorem seqDirectSumEquiv_of (A : T) (X : ℕ ⥤ T) (n : ℕ)
    (g : ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    seqDirectSumEquiv A X
        (DirectSum.of (fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)) n g) =
      DirectSum.of (fun k ↦ A ⟶ X.obj k) n (coyonedaToHom A X n g) :=
  DFinsupp.mapRange_single (f := fun k ↦ coyonedaToHom A X k) (hf := fun _ ↦ rfl) (i := n)

/-- Under `coprodComparisonAddHom` and `seqDirectSumEquiv`, postcomposition with
`X.sequenceDifference` agrees with `ModuleCat.telescopeDiff` on `X ⋙ preadditiveCoyonedaObj A`. -/
private theorem coprodComparisonAddHom_telescopeDiff (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    (a : ⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    coprodComparisonAddHom A X.obj
        (seqDirectSumEquiv A X (ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A) a)) =
      coprodComparisonAddHom A X.obj (seqDirectSumEquiv A X a) ≫ X.sequenceDifference := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n g =>
    rw [← DirectSum.lof_eq_of (End A)ᵐᵒᵖ, ModuleCat.telescopeDiff_lof, map_sub, map_sub,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, seqDirectSumEquiv_of, seqDirectSumEquiv_of,
      coprodComparisonAddHom_of, coprodComparisonAddHom_of, Category.assoc,
      X.ι_sequenceDifference, Preadditive.comp_sub]
    exact congrArg (coyonedaToHom A X n g ≫ Sigma.ι X.obj n - ·)
      (Category.assoc (coyonedaToHom A X n g) (X.map (homOfLE (n.le_add_right 1)))
        (Sigma.ι X.obj (n + 1)))
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, map_add, Preadditive.add_comp, ha, hb]

/-- For a compact object `A`, postcomposition with the sequence–difference map
`X.sequenceDifference : (∐ X.obj) ⟶ (∐ X.obj)` is injective on `A ⟶ ∐ X.obj`. -/
theorem injective_comp_sequenceDifference {A : T} (hA : IsCompactForCoproducts A) (X : ℕ ⥤ T)
    [HasCoproduct X.obj] :
    Function.Injective (fun g : A ⟶ ∐ X.obj ↦ g ≫ X.sequenceDifference) := fun g₁ g₂ hg ↦ by
  dsimp only at hg
  obtain ⟨a₁', rfl⟩ := (hA.bijective_coprodComparisonAddHom X.obj).2 g₁
  obtain ⟨a₂', rfl⟩ := (hA.bijective_coprodComparisonAddHom X.obj).2 g₂
  obtain ⟨a₁, rfl⟩ := (seqDirectSumEquiv A X).surjective a₁'
  obtain ⟨a₂, rfl⟩ := (seqDirectSumEquiv A X).surjective a₂'
  rw [← coprodComparisonAddHom_telescopeDiff, ← coprodComparisonAddHom_telescopeDiff] at hg
  exact congrArg (fun z ↦ coprodComparisonAddHom A X.obj (seqDirectSumEquiv A X z)) <|
    ModuleCat.telescopeDiff_injective (X ⋙ preadditiveCoyonedaObj A)
      ((seqDirectSumEquiv A X).injective ((hA.bijective_coprodComparisonAddHom X.obj).1 hg))

/-- Evaluate a morphism `A ⟶ ∐ X.obj` out of a compact object `A` against the legs of a cocone
over `X ⋙ preadditiveCoyoneda.obj (op A)`. -/
private def evalCoconeOfCompact {X : ℕ ⥤ T} [HasCoproduct X.obj] {A : T}
    (hA : IsCompactForCoproducts A) (s : Cocone (X ⋙ preadditiveCoyoneda.obj (op A))) :
    (A ⟶ ∐ X.obj) →+ s.pt :=
  (DirectSum.toAddMonoid fun k ↦
    ({ toFun := fun f ↦ (s.ι.app k).hom f, map_zero' := map_zero (s.ι.app k).hom,
       map_add' := map_add (s.ι.app k).hom } : (A ⟶ X.obj k) →+ s.pt)).comp
    (hA.homCoprodEquiv X.obj).symm.toAddMonoidHom

private theorem evalCoconeOfCompact_comp_ι {X : ℕ ⥤ T} [HasCoproduct X.obj] {A : T}
    (hA : IsCompactForCoproducts A) (s : Cocone (X ⋙ preadditiveCoyoneda.obj (op A)))
    (n : ℕ) (h : A ⟶ X.obj n) :
    evalCoconeOfCompact hA s (h ≫ Sigma.ι X.obj n) = (s.ι.app n).hom h := by
  dsimp only [evalCoconeOfCompact]
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hA.homCoprodEquiv_symm_comp_ι,
    DirectSum.toAddMonoid_of]
  rfl

private theorem evalCoconeOfCompact_comp_sequenceDifference {X : ℕ ⥤ T} [HasCoproduct X.obj]
    {A : T} (hA : IsCompactForCoproducts A) (s : Cocone (X ⋙ preadditiveCoyoneda.obj (op A)))
    (v : A ⟶ ∐ X.obj) :
    evalCoconeOfCompact hA s (v ≫ X.sequenceDifference) = 0 := by
  obtain ⟨a, rfl⟩ := (hA.bijective_coprodComparisonAddHom X.obj).2 v
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n h =>
    rw [coprodComparisonAddHom_of, Category.assoc, X.ι_sequenceDifference, Preadditive.comp_sub,
      ← Category.assoc, map_sub, evalCoconeOfCompact_comp_ι, evalCoconeOfCompact_comp_ι]
    have hw := congrArg (fun φ : (preadditiveCoyoneda.obj (op A)).obj (X.obj n) ⟶ s.pt ↦ φ h)
      (s.w (homOfLE (n.le_add_right 1)))
    exact sub_eq_zero.2 hw.symm
  | add a b ha hb => simp [Preadditive.add_comp, ha, hb]

section Shift

variable [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]

/-- For a compact object `A`, postcomposition with the shifted sequence–difference map
`(X.sequenceDifference)⟦(1 : ℤ)⟧` is injective on `A ⟶ (∐ X.obj)⟦(1 : ℤ)⟧`. -/
theorem injective_comp_shift_sequenceDifference {A : T} (hA : IsCompactForCoproducts A)
    (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    Function.Injective (fun g : A ⟶ (∐ X.obj)⟦(1 : ℤ)⟧ ↦
      g ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧') := fun g₁ g₂ hg ↦ by
  dsimp only at hg
  let ε := (shiftFunctorCompIsoId T (1 : ℤ) (-1 : ℤ) (add_neg_cancel 1)).hom
  have hnat : ((X.sequenceDifference)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) =
      ε.app (∐ X.obj) ≫ X.sequenceDifference := ε.naturality _
  have h1 : (g₁⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ X.sequenceDifference =
      (g₂⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ X.sequenceDifference := by
    rw [Category.assoc, ← hnat, ← Functor.map_comp_assoc, hg, Functor.map_comp_assoc, hnat,
      ← Category.assoc]
  exact (shiftFunctor T (-1 : ℤ)).map_injective
    ((cancel_mono (ε.app (∐ X.obj))).1 (injective_comp_sequenceDifference (hA.shift (-1 : ℤ)) X h1))

end Shift

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

/-- The canonical cocone over `X` with point `M` attached to a Milnor homotopy colimit triangle
`∐ X.obj ⟶ ∐ X.obj ⟶ M ⟶ (∐ X.obj)⟦1⟧`. -/
abbrev coconeOfMilnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
    {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) : Cocone X :=
  X.coconeOfSequenceDifference ψ (comp_distTriang_mor_zero₁₂ _ ht)

/-- Every morphism from a compact object `A` into a Milnor homotopy colimit `M` factors through
the structural map `ψ : ∐ X.obj ⟶ M`. -/
theorem surjective_comp_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) :
    Function.Surjective (fun g : A ⟶ ∐ X.obj ↦ g ≫ ψ) := fun f ↦ by
  have hfδ : f ≫ δ = 0 := injective_comp_shift_sequenceDifference hA X <| by
    have hδ : δ ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ ht
    dsimp only; rw [Category.assoc, hδ, comp_zero, zero_comp]
  exact ((ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (op A)).map_distinguished_exact _ (rot_of_distTriang _ ht))) f hfδ

/-- **Factoring out of a compact object into a Milnor homotopy colimit:** every morphism from a
compact object `A` into a Milnor homotopy colimit `M` of `X` factors through some finite stage
`X.obj N`. -/
theorem exists_factor_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) (g : A ⟶ M) :
    ∃ (N : ℕ) (h : A ⟶ X.obj N), g = h ≫ Sigma.ι X.obj N ≫ ψ := by
  obtain ⟨u, rfl⟩ := surjective_comp_of_milnorTriangle ht hA g
  obtain ⟨s, h, rfl⟩ := hA.exists_finset_sum_comp_ι X.obj u
  have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
  refine ⟨s.sup id, ∑ n ∈ s.attach, h n.1 ≫ X.map (homOfLE (Finset.le_sup (f := id) n.2)), ?_⟩
  dsimp only
  rw [Preadditive.sum_comp, Preadditive.sum_comp, ← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Category.assoc, Category.assoc, X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ]

/-- **Kernel criterion for morphisms out of a compact object into a Milnor homotopy colimit:**
a morphism `h : A ⟶ X.obj n` from a compact object `A` vanishes in the Milnor homotopy colimit `M`
if and only if it is annihilated by some transition map `X.obj n ⟶ X.obj m` (`n ≤ m`). -/
theorem comp_milnorTriangle_eq_zero_iff {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) {n : ℕ} (h : A ⟶ X.obj n) :
    h ≫ Sigma.ι X.obj n ≫ ψ = 0 ↔ ∃ (m : ℕ) (hnm : n ≤ m), h ≫ X.map (homOfLE hnm) = 0 := by
  classical
  have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
  refine ⟨fun hzero ↦ ?_, fun ⟨m, hnm, hm⟩ ↦ by
    rw [← X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ hnm,
      ← Category.assoc, hm, zero_comp]⟩
  have hex :=
    (ShortComplex.ab_exact_iff _).1 ((preadditiveCoyoneda.obj (op A)).map_distinguished_exact _ ht)
  obtain ⟨(v : A ⟶ ∐ X.obj), hv⟩ :=
    hex (h ≫ Sigma.ι X.obj n) ((Category.assoc h (Sigma.ι X.obj n) ψ).trans hzero)
  let β : ℕ → Type v := fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)
  let a : ⨁ k, β k := (seqDirectSumEquiv A X).symm ((hA.homCoprodEquiv X.obj).symm v)
  let h' : β n := h
  have hdiff : ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A) a =
      DirectSum.lof (End A)ᵐᵒᵖ ℕ β n h' := by
    rw [DirectSum.lof_eq_of]
    apply (seqDirectSumEquiv A X).injective
    apply (hA.bijective_coprodComparisonAddHom X.obj).1
    have ha_eq : coprodComparisonAddHom A X.obj (seqDirectSumEquiv A X a) = v := by
      dsimp only [a]
      rw [AddEquiv.apply_symm_apply, ← hA.homCoprodEquiv_apply, AddEquiv.apply_symm_apply]
    rw [coprodComparisonAddHom_telescopeDiff, seqDirectSumEquiv_of,
      coprodComparisonAddHom_of, ha_eq]
    exact hv
  exact ModuleCat.exists_map_homOfLE_eq_zero_of_telescopeDiff_eq_lof hdiff

/-- For a compact object `A`, `Hom(A, -)` sends any Milnor homotopy colimit triangle to a colimit
cocone in `AddCommGrpCat`. -/
def isColimitMapCoconeOfMilnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) :
    IsColimit ((preadditiveCoyoneda.obj (op A)).mapCocone (coconeOfMilnorTriangle ht)) := by
  let F := preadditiveCoyoneda.obj (op A)
  have hsurj := surjective_comp_of_milnorTriangle ht hA
  let lift (g : A ⟶ M) : A ⟶ ∐ X.obj := (hsurj g).choose
  have hlift (g : A ⟶ M) : lift g ≫ ψ = g := (hsurj g).choose_spec
  have hex := (ShortComplex.ab_exact_iff _).1 (F.map_distinguished_exact _ ht)
  have heval_wd (s : Cocone (X ⋙ F)) {u₁ u₂ : A ⟶ ∐ X.obj} (h : u₁ ≫ ψ = u₂ ≫ ψ) :
      evalCoconeOfCompact hA s u₁ = evalCoconeOfCompact hA s u₂ := by
    obtain ⟨(v : A ⟶ ∐ X.obj), hv⟩ :=
      hex (u₁ - u₂) ((Preadditive.sub_comp u₁ u₂ ψ).trans (sub_eq_zero.2 h))
    have hv' : v ≫ X.sequenceDifference = u₁ - u₂ := hv
    exact sub_eq_zero.1 <| by rw [← map_sub, ← hv', evalCoconeOfCompact_comp_sequenceDifference]
  have hfac (s : Cocone (X ⋙ F)) (n : ℕ) (h : A ⟶ X.obj n) :
      evalCoconeOfCompact hA s (lift (h ≫ Sigma.ι X.obj n ≫ ψ)) = (s.ι.app n).hom h :=
    (heval_wd s (u₂ := h ≫ Sigma.ι X.obj n)
      ((hlift _).trans (Category.assoc h (Sigma.ι X.obj n) ψ).symm)).trans
        (evalCoconeOfCompact_comp_ι hA s n h)
  let descHom (s : Cocone (X ⋙ F)) : (A ⟶ M) →+ s.pt :=
    { toFun := fun g ↦ evalCoconeOfCompact hA s (lift g)
      map_zero' := (heval_wd s (u₂ := 0) ((hlift 0).trans zero_comp.symm)).trans (map_zero _)
      map_add' := fun g₁ g₂ ↦
        (heval_wd s (u₂ := lift g₁ + lift g₂) <| by
          rw [hlift, Preadditive.add_comp, hlift, hlift]).trans (map_add _ _ _) }
  exact
    { desc := fun s ↦ AddCommGrpCat.ofHom (descHom s)
      fac := fun s n ↦ by ext (h : A ⟶ X.obj n); exact hfac s n h
      uniq := fun s m hm ↦ by
        ext (g : A ⟶ M)
        obtain ⟨N, h, rfl⟩ := exists_factor_of_milnorTriangle ht hA g
        exact (congrArg (fun φ : F.obj (X.obj N) ⟶ s.pt ↦ φ h) (hm N)).trans (hfac s N h).symm }

end CompactMapping

end TauCeti

section MilnorSequence

namespace CategoryTheory.Functor

open TauCeti

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- The shifted coproduct cofan for `X ⋙ shiftFunctor T (1 : ℤ)` with vertex `(∐ X.obj)⟦1⟧` and
inclusions `(Sigma.ι X.obj n)⟦1⟧'`. -/
private abbrev shiftedCoproductCofan (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    Cofan (X ⋙ shiftFunctor T (1 : ℤ)).obj :=
  Cofan.mk ((∐ X.obj)⟦(1 : ℤ)⟧) fun n ↦ (Sigma.ι X.obj n)⟦(1 : ℤ)⟧'

private def isColimit_shiftedCoproductCofan (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    IsColimit (shiftedCoproductCofan X) :=
  (isColimitMapCoconeCofanMkEquiv (shiftFunctor T (1 : ℤ)) X.obj (Sigma.ι X.obj)).1
    (isColimitOfPreserves (shiftFunctor T (1 : ℤ)) (coproductIsCoproduct X.obj))

section ModuleValued

variable {R : Type uR} [Ring R] (F : Tᵒᵖ ⥤ ModuleCat.{v} R)
variable {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
  {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor exact sequence for a contravariant
functor `F : Tᵒᵖ ⥤ ModuleCat R`. -/
def milnorObjToLim (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    F.obj (op M) →ₗ[R] ModuleTower.lim (X.op ⋙ F) :=
  ModuleTower.limLift (X.op ⋙ F) (fun n ↦ (F.map (Sigma.ι X.obj n ≫ ψ).op).hom) fun n ↦ by
    have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
    rw [ModuleTower.transition_def, ← ModuleCat.hom_comp, Functor.comp_map, Functor.op_map,
      Quiver.Hom.unop_op, ← F.map_comp, ← op_comp,
      X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ]

@[simp]
theorem coe_milnorObjToLim_apply (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (u : F.obj (op M)) (n : ℕ) :
    (F.milnorObjToLim ht u : ModuleTower.Product (X.op ⋙ F)) n =
      F.map (Sigma.ι X.obj n ≫ ψ).op u :=
  ModuleTower.coe_limLift_apply (X.op ⋙ F) _ _ u n

/-- Naturality of the restriction map `F(M) →ₗ[R] lim F(Xₙ)` with respect to any morphism of
Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorObjToLim_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T) (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    F.milnorObjToLim htX ∘ₗ (F.map φ.hom₃.op).hom =
      ModuleTower.limMap (Functor.whiskerRight (NatTrans.op α) F) ∘ₗ F.milnorObjToLim htY := by
  ext n u
  have hcomm : ψ ≫ φ.hom₃ = φ.hom₂ ≫ ψ' := φ.comm₂
  simp only [LinearMap.comp_apply, ModuleTower.limπ_apply, coe_milnorObjToLim_apply,
    ModuleTower.coe_limMap_apply, ModuleTower.productMap_apply, Functor.whiskerRight_app,
    NatTrans.op_app, ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp, Category.assoc]
  rw [hcomm, hφ₂, Sigma.ι_map_assoc]

variable [F.IsHomological] [PreservesLimitsOfShape (Discrete ℕ) F]

private theorem cofanOpToPiLinearEquiv_map_sequenceDifference (X : ℕ ⥤ T) [HasCoproduct X.obj]
    (x : F.obj (op (∐ X.obj))) :
    (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F (F.map X.sequenceDifference.op x) =
      ModuleTower.shift (X.op ⋙ F)
        ((coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F x) := by
  funext n
  simp only [IsColimit.cofanOpToPiLinearEquiv_apply, ModuleTower.shift_apply,
    ModuleTower.transition_def, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, Cofan.inj,
    Cofan.mk_ι_app, ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp, X.ι_sequenceDifference,
    op_sub, F.map_sub]
  rfl

private theorem cofanOpToPiLinearEquiv_map_shift_sequenceDifference (X : ℕ ⥤ T)
    [HasCoproduct X.obj] (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    (isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv F
        (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op y) =
      ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)
        ((isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv F y) := by
  funext n
  simp only [IsColimit.cofanOpToPiLinearEquiv_apply, ModuleTower.shift_apply,
    ModuleTower.transition_def, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
    shiftedCoproductCofan, Cofan.inj, Cofan.mk_ι_app, ← CategoryTheory.comp_apply, ← F.map_comp,
    ← op_comp]
  rw [← (shiftFunctor T (1 : ℤ)).map_comp, X.ι_sequenceDifference,
    (shiftFunctor T (1 : ℤ)).map_sub, (shiftFunctor T (1 : ℤ)).map_comp, op_sub, F.map_sub]
  rfl

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor sequence is surjective. -/
theorem milnorObjToLim_surjective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Surjective (F.milnorObjToLim ht) := fun ⟨x, hx⟩ ↦ by
  let e := (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F
  have hzero : F.map X.sequenceDifference.op (e.symm x) = 0 := e.injective <| by
    rw [cofanOpToPiLinearEquiv_map_sequenceDifference, LinearEquiv.apply_symm_apply, map_zero]
    exact LinearMap.mem_ker.1 (ModuleTower.lim_eq_ker (X.op ⋙ F) ▸ hx)
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (F.map_distinguished_op_exact _ ht)
  dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle] at hex
  obtain ⟨u, hu⟩ := hex (e.symm x) hzero
  have hu' : F.map ψ.op u = e.symm x := hu
  refine ⟨u, Subtype.ext <| funext fun n ↦ ?_⟩
  rw [coe_milnorObjToLim_apply, op_comp, F.map_comp, CategoryTheory.comp_apply, hu']
  exact (coproductIsCoproduct X.obj).map_inj_cofanOpToPiLinearEquiv_symm F x n

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor exact sequence, induced
by `F.map δ.op : F((∐ Xₙ)⟦1⟧) → F(M)`. -/
def milnorLimOneToObj (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) →ₗ[R] F.obj (op M) :=
  let e₁ := (isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  Submodule.liftQ (LinearMap.range (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)))
    ((F.map δ.op).hom ∘ₗ e₁.symm.toLinearMap) <| by
    rintro _ ⟨y, rfl⟩
    have hshift : e₁.symm (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) y) =
        F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op (e₁.symm y) := e₁.injective <| by
      rw [LinearEquiv.apply_symm_apply, cofanOpToPiLinearEquiv_map_shift_sequenceDifference,
        LinearEquiv.apply_symm_apply]
    have hδ : δ ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ ht
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hshift,
      ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp, hδ, op_zero, F.map_zero]; rfl

@[simp]
theorem milnorLimOneToObj_mk_map (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    F.milnorLimOneToObj ht
        (Submodule.Quotient.mk fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) =
      F.map δ.op y := by
  let e₁ := (isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  have he₁ : (fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) = e₁ y :=
    funext fun n ↦ ((isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv_apply F y n).symm
  rw [he₁]
  exact congrArg (F.map δ.op) (e₁.symm_apply_apply y)

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor sequence is
injective. -/
theorem milnorLimOneToObj_injective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Injective (F.milnorLimOneToObj ht) := by
  let e₁ := (isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hex2 := (ShortComplex.moduleCat_exact_iff _).1
    (F.map_distinguished_op_exact _ (rot_of_distTriang _ (rot_of_distTriang _ ht)))
  dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle,
    Triangle.rotate] at hex2
  obtain ⟨w, hw⟩ := hex2 (e₁.symm x) hz
  have hw0 : F.map (-(X.sequenceDifference)⟦(1 : ℤ)⟧').op w = e₁.symm x := hw
  have hw' : F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op (-w) = e₁.symm x := by
    simpa [op_neg, F.map_neg] using hw0
  refine ⟨-e₁ w, ?_⟩
  rw [_root_.map_neg, ← cofanOpToPiLinearEquiv_map_shift_sequenceDifference, ← _root_.map_neg e₁,
    ← _root_.map_neg (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op).hom, hw',
    LinearEquiv.apply_symm_apply]

/-- Exactness at the middle term of the Milnor sequence
`0 → lim¹ F((Xₙ)⟦1⟧) → F(M) → lim F(Xₙ) → 0`. -/
theorem exact_milnorLimOneToObj_milnorObjToLim
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Exact (F.milnorLimOneToObj ht) (F.milnorObjToLim ht) := fun u ↦ by
  let e := (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F
  let e₁ := (isColimit_shiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  refine ⟨fun hu ↦ ?_, ?_⟩
  · have hψ : F.map ψ.op u = 0 := e.injective <| by
      rw [map_zero]; funext n
      have hcoord := congrArg
        (fun v : ModuleTower.lim (X.op ⋙ F) ↦ (v : ModuleTower.Product (X.op ⋙ F)) n) hu
      rw [coe_milnorObjToLim_apply, op_comp, F.map_comp, CategoryTheory.comp_apply] at hcoord
      dsimp only [e]; rw [IsColimit.cofanOpToPiLinearEquiv_apply]; exact hcoord
    have hex := (ShortComplex.moduleCat_exact_iff _).1
      (F.map_distinguished_op_exact _ (rot_of_distTriang _ ht))
    dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle,
      Triangle.rotate] at hex
    obtain ⟨y, hy⟩ := hex u hψ
    exact ⟨Submodule.Quotient.mk (e₁ y), (congrArg (F.map δ.op) (e₁.symm_apply_apply y)).trans hy⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hψδ : ψ ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ ht
    ext n
    simp only [ModuleTower.limπ_apply, coe_milnorObjToLim_apply, milnorLimOneToObj,
      Submodule.liftQ_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp, Category.assoc, hψδ, comp_zero,
      op_zero, F.map_zero]
    rfl

/-- When `lim¹ F((Xₙ)⟦1⟧)` vanishes, the Milnor restriction map `F(M) →ₗ[R] lim F(Xₙ)`
is bijective. -/
theorem milnorObjToLim_bijective_of_subsingleton_limOne
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [Subsingleton (ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F))] :
    Function.Bijective (F.milnorObjToLim ht) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu ↦ ?_, F.milnorObjToLim_surjective ht⟩
  obtain ⟨z, rfl⟩ := (F.exact_milnorLimOneToObj_milnorObjToLim ht u).1 hu
  rw [Subsingleton.elim z 0, map_zero]

/-- Naturality of the connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` with respect to any morphism
of Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorLimOneToObj_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T) (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.map φ.hom₃.op).hom ∘ₗ F.milnorLimOneToObj htY = F.milnorLimOneToObj htX ∘ₗ
      ModuleTower.limOneMap (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) := by
  let eY := (isColimit_shiftedCoproductCofan Y).cofanOpToPiLinearEquiv F
  ext x
  obtain ⟨y, rfl⟩ := eY.surjective x
  have hprod :
      ModuleTower.productMap (Functor.whiskerRight
          (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) (eY y) =
        fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op (F.map (φ.hom₁⟦(1 : ℤ)⟧').op y) := by
    funext n
    simp only [eY, ModuleTower.productMap_apply, Functor.whiskerRight_app, NatTrans.op_app,
      IsColimit.cofanOpToPiLinearEquiv_apply, shiftedCoproductCofan, Cofan.inj, Cofan.mk_ι_app,
      ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp,
      ← (shiftFunctor T (1 : ℤ)).map_comp, hφ₁, Sigma.ι_map]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, ModuleTower.limOneMap_mk, hprod,
    milnorLimOneToObj_mk_map]
  have hL : F.milnorLimOneToObj htY (Submodule.Quotient.mk (eY y)) = F.map δ'.op y :=
    congrArg (F.map δ'.op) (eY.symm_apply_apply y)
  have hcomm : δ ≫ φ.hom₁⟦(1 : ℤ)⟧' = φ.hom₃ ≫ δ' := φ.comm₃
  rw [hL, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← F.map_comp,
    ← F.map_comp, ← op_comp, ← op_comp, hcomm]

end ModuleValued

end CategoryTheory.Functor

namespace TauCeti

section AddCommGrpValued

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- **Milnor lifting for `AddCommGrpCat`-valued cohomological functors:** for a contravariant
homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` preserving countable products and any Milnor
homotopy colimit triangle of `X : ℕ ⥤ T`, every compatible family
`x : ∀ n, E.obj (op (X.obj n))` lifts to an element `u : E.obj (op M)` restricting to `x n`
along each `Sigma.ι X.obj n ≫ ψ`. -/
theorem exists_lift_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological] [PreservesLimitsOfShape (Discrete ℕ) E]
    (x : ∀ n, E.obj (op (X.obj n)))
    (hx : ∀ n, E.map (X.map (homOfLE (Nat.le_add_right n 1))).op (x (n + 1)) = x n) :
    ∃ u : E.obj (op M), ∀ n, E.map (Sigma.ι X.obj n ≫ ψ).op u = x n := by
  have := comp_preservesLimitsOfShape (J := Discrete ℕ) E AddCommGrpCat.toIntModule
  have : (E ⋙ AddCommGrpCat.toIntModule).IsHomological :=
    { map_zero := fun _ _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ by
        simp [AddCommGrpCat.toIntModule_map]; rfl
      exact := fun s hs ↦ (ShortComplex.moduleCat_exact_iff _).2 <|
        (ShortComplex.ab_exact_iff _).1 (E.map_distinguished_exact s hs) }
  obtain ⟨u, hu⟩ := (E ⋙ AddCommGrpCat.toIntModule).milnorObjToLim_surjective ht
    ⟨x, (ModuleTower.mem_lim (X.op ⋙ E ⋙ AddCommGrpCat.toIntModule)).2 fun n ↦ by
      rw [ModuleTower.transition_def]; exact hx n⟩
  exact ⟨u, fun n ↦
    (CategoryTheory.Functor.coe_milnorObjToLim_apply _ ht u n).symm.trans <|
      congrArg (fun v : ModuleTower.lim (X.op ⋙ (E ⋙ AddCommGrpCat.toIntModule)) ↦ v.1 n) hu⟩

end AddCommGrpValued

end TauCeti

end MilnorSequence
