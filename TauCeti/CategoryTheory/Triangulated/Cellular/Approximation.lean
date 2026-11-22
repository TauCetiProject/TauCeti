/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Triangulated.Cellular.Closure
public import TauCeti.CategoryTheory.Triangulated.HomotopyColimit

import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import TauCeti.Algebra.Category.Grp.Products

/-!
# Cellular approximation in pretriangulated categories with coproducts

For a `Type v`-indexed family `G : I → T` of objects compact for coproducts
(`TauCeti.IsCompactForCoproducts`) and a contravariant homological functor
`E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` sending `Type v`-indexed coproducts to products, we construct a
cellular approximation `R` in `TauCeti.InCellClosure G` with a cohomology class `x : E.obj (op R)`
inducing bijections `(G i ⟶ R) ≃ E.obj (op (G i))` (`TauCeti.cellularApproximation`).
Specializing to `preadditiveYoneda.obj Y` yields `TauCeti.cellularApproximation_obj`, without
requiring `IsTriangulated T`.

## Main results

* `TauCeti.cellularApproximation`, `TauCeti.cellularApproximation_obj`,
  `TauCeti.cellularApproximation_of_subsingleton`

## References

* A. Neeman, *Triangulated categories*, Princeton Univ. Press (2001), Lemma 4.2.4, Section 8.2.
* S. Schwede, *Symmetric spectra*, Chapter II, Def. 5.4, Lemma 5.6, and Prop. 5.14.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

universe v u

namespace TauCeti

section CellularApproximation

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{v} T]
  {I : Type v}

/-- One stage in the inductive construction of a cellular approximation. -/
private structure ApproxStage (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj : T
  cell : InCellClosure G obj
  pt : E.obj (op obj)

/-- The initial cellular stage: a coproduct of copies of `G i` indexed by all pairs `(i, y)` with
`y : E.obj (op (G i))`, together with the universal element matching every `y` on its summand. -/
private def approxStageZero (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E) : ApproxStage G E :=
  let J₀ := Σ i : I, E.obj (op (G i))
  let f₀ : J₀ → T := fun p ↦ G p.1
  have : PreservesLimitsOfShape (Discrete J₀) E := hE J₀
  { obj := ∐ f₀
    cell := InCellClosure.coproduct f₀ fun p ↦ InCellClosure.generator G p.1
    pt := ((coproductIsCoproduct f₀).cofanOpToPiAddEquiv E).symm fun p ↦ p.2 }

private lemma approxStageZero_map_ι (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E)
    (i : I) (y : E.obj (op (G i))) :
    E.map (Sigma.ι (fun p : Σ i : I, E.obj (op (G i)) ↦ G p.1) ⟨i, y⟩).op
        (approxStageZero G E hE).pt = y := by
  let J₀ := Σ i : I, E.obj (op (G i))
  let f₀ : J₀ → T := fun p ↦ G p.1
  have : PreservesLimitsOfShape (Discrete J₀) E := hE J₀
  exact IsColimit.map_inj_cofanOpToPiAddEquiv_symm (coproductIsCoproduct f₀) E
    (fun p : J₀ ↦ p.2) ⟨i, y⟩

/-- One inductive step attaching cells along all morphisms from `G i` that annihilate the current
cohomology class `s.pt`. -/
private structure ApproxStep (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (s : ApproxStage G E) where
  next : ApproxStage G E
  mor : s.obj ⟶ next.obj
  map_pt : E.map mor.op next.pt = s.pt
  kill : ∀ (i : I) (f : G i ⟶ s.obj), E.map f.op s.pt = 0 → f ≫ mor = 0

private def approxStep (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological]
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E)
    (s : ApproxStage G E) : ApproxStep G E s := by
  let K := Σ i : I, { f : G i ⟶ s.obj // E.map f.op s.pt = 0 }
  let g : K → T := fun p ↦ G p.1
  let k : (∐ g) ⟶ s.obj := Sigma.desc fun p ↦ p.2.val
  have htri := distinguished_cocone_triangle k
  let nextObj : T := htri.choose
  let j : s.obj ⟶ nextObj := htri.choose_spec.choose
  let δ : nextObj ⟶ (∐ g)⟦(1 : ℤ)⟧ := htri.choose_spec.choose_spec.choose
  have ht : Triangle.mk k j δ ∈ distTriang T := htri.choose_spec.choose_spec.choose_spec
  have hcell : InCellClosure G nextObj :=
    InCellClosure.of_distTriang ht
      (InCellClosure.coproduct g fun p ↦ InCellClosure.generator G p.1) s.cell
  have hk0 : E.map k.op s.pt = 0 := by
    have := hE K
    apply ((coproductIsCoproduct g).cofanOpToPiAddEquiv E).injective
    rw [map_zero]; funext p; rw [IsColimit.cofanOpToPiAddEquiv_apply]
    dsimp only [Cofan.inj, Cofan.mk_ι_app]
    rw [← CategoryTheory.Functor.map_op_comp_apply, Sigma.ι_comp_desc]
    exact p.2.property
  have hlift : ∃ u : E.obj (op nextObj), E.map j.op u = s.pt := by
    have hex := (ShortComplex.ab_exact_iff _).1 (E.map_distinguished_op_exact _ ht)
    dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle] at hex
    exact hex s.pt hk0
  exact
    { next := ⟨nextObj, hcell, hlift.choose⟩
      mor := j
      map_pt := hlift.choose_spec
      kill := fun i f hf ↦ by
        have hfk : f = Sigma.ι g ⟨i, ⟨f, hf⟩⟩ ≫ k :=
          (Sigma.ι_comp_desc (fun p : K ↦ p.2.val) ⟨i, ⟨f, hf⟩⟩).symm
        have hkj : k ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ ht
        rw [hfk, Category.assoc, hkj, comp_zero] }

/-- **Cellular approximation in a pretriangulated category with coproducts** (Schwede, *Symmetric
spectra*, Chapter II, Proposition 5.14): for any small family `G : I → T` of compact objects and
any contravariant homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` sending `Type v`-indexed
coproducts to products, there exist `R` in the cellular closure of `G` and `x : E.obj (op R)` such
that evaluation `f ↦ E.map f.op x` is bijective on `G i ⟶ R` for every `i`. -/
theorem cellularApproximation (G : I → T) (hG : ∀ i, IsCompactForCoproducts (G i))
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological]
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E) :
    ∃ R : T, InCellClosure G R ∧ ∃ x : E.obj (op R),
      ∀ i, Function.Bijective (fun f : G i ⟶ R ↦ E.map f.op x) := by
  let stage : ℕ → ApproxStage G E :=
    Nat.rec (approxStageZero G E hE) fun _ s ↦ (approxStep G E hE s).next
  let X : ℕ ⥤ T := Functor.ofSequence fun n ↦ (approxStep G E hE (stage n)).mor
  have : HasCoproductsOfShape ℕ T :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{v})
  have : PreservesLimitsOfShape (Discrete ℕ) E :=
    have := hE (ULift.{v} ℕ)
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{v}) E
  obtain ⟨R, ψ, δ, ht⟩ := distinguished_cocone_triangle X.sequenceDifference
  have hcell : InCellClosure G R := InCellClosure.of_milnorTriangle ht fun n ↦ (stage n).cell
  obtain ⟨x, hx⟩ := exists_lift_of_milnorTriangle ht E (fun n ↦ (stage n).pt) fun n ↦ by
    rw [Functor.ofSequence_map_homOfLE_succ]; exact (approxStep G E hE (stage n)).map_pt
  refine ⟨R, hcell, x, fun i ↦ ⟨fun f₁ f₂ hfeq ↦ sub_eq_zero.1 ?_, fun y ↦ ?_⟩⟩
  · have : PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op (G i))) :=
      (hG i).preservesColimitsOfShape ℕ
    have hf : E.map (f₁ - f₂).op x = 0 := by
      dsimp only at hfeq; simpa [op_sub, E.map_sub] using sub_eq_zero.2 hfeq
    obtain ⟨N, h, hfac⟩ := exists_factor_of_milnorTriangle ht (f₁ - f₂)
    rw [hfac] at hf ⊢
    have hh : E.map h.op (stage N).pt = 0 := by
      rw [← hx N, ← CategoryTheory.Functor.map_op_comp_apply]; exact hf
    have hkill : h ≫ X.map (homOfLE (Nat.le_add_right N 1)) = 0 := by
      rw [Functor.ofSequence_map_homOfLE_succ]; exact (approxStep G E hE (stage N)).kill i h hh
    have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
    rw [← X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ (Nat.le_add_right N 1),
      ← Category.assoc, hkill, zero_comp]
  · let ι₀ : G i ⟶ X.obj 0 := Sigma.ι (fun p : Σ i : I, E.obj (op (G i)) ↦ G p.1) ⟨i, y⟩
    refine ⟨ι₀ ≫ Sigma.ι X.obj 0 ≫ ψ, ?_⟩
    dsimp only; rw [CategoryTheory.Functor.map_op_comp_apply, hx 0]
    exact approxStageZero_map_ι G E hE i y

/-- **Cellular approximation of an object:** for a small family `G` of compact objects and any
object `Y : T`, there exist an object `R` in `InCellClosure G` and a morphism `u : R ⟶ Y` inducing
bijections `(G i ⟶ R) → (G i ⟶ Y)` by postcomposition for every `i`. -/
theorem cellularApproximation_obj (G : I → T) (hG : ∀ i, IsCompactForCoproducts (G i)) (Y : T) :
    ∃ R : T, InCellClosure G R ∧ ∃ u : R ⟶ Y,
      ∀ i, Function.Bijective (fun f : G i ⟶ R ↦ f ≫ u) :=
  cellularApproximation G hG (preadditiveYoneda.obj Y) fun _ ↦ inferInstance

/-- For a subsingleton (for instance zero) contravariant functor, the zero object and its zero
class provide a cellular approximation directly without compactness or exactness hypotheses. -/
theorem cellularApproximation_of_subsingleton (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [∀ X, Subsingleton (E.obj X)] :
    InCellClosure G (0 : T) ∧
      ∀ i, Function.Bijective (fun f : G i ⟶ (0 : T) ↦ E.map f.op (0 : E.obj (op 0))) := by
  refine ⟨InCellClosure.zero G, fun i ↦ ?_⟩
  have : Subsingleton (G i ⟶ (0 : T)) := ⟨fun f g ↦ (isZero_zero T).eq_of_tgt f g⟩
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

end CellularApproximation

end TauCeti
