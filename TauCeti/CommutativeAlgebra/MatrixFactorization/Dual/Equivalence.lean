/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Dual.Homotopy
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

-- Biduality compares the component formulas of the signed dual functors, and the final
-- descent uses the existing presentation of the homotopy dual as a quotient lift.
import all TauCeti.CommutativeAlgebra.MatrixFactorization.Dual.Basic
import all TauCeti.CommutativeAlgebra.MatrixFactorization.Dual.Homotopy
import all TauCeti.Algebra.Homology.Curved.Dual

/-!
# Duality is an equivalence of matrix-factorization categories

The signed transpose duality gives an additive equivalence
`(MatrixFactorization S w)ᵒᵖ ≌ MatrixFactorization S (-w)` over any commutative ring.
Finite projectivity, rather than freeness or a regularity hypothesis on the ring, is what
makes evaluation into the double dual invertible.

The inverse uses the same crossed transposes, with the potential rewritten from `-(-w)`
to `w`. Both double-dual comparisons have negative evaluation on the even component and
positive evaluation on the odd component. In particular, the equivalence uses the existing
signed dual functor, not a different convention for the position of the minus sign.

Duality also reflects null-homotopic maps. Consequently the already constructed additive
functor on homotopy classes is an equivalence `HMF(S,w)ᵒᵖ ≌ HMF(S,-w)`. Its object and
representative-map formulas remain those of `homotopyDualFunctor`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
* `TauCeti.CommutativeAlgebra.MatrixFactorization.Dual.Basic` supplies the signed transpose
  construction; `FGModuleCat.dualEvalIso` supplies finite-projective biduality.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Opposite

variable {S : Type u} [CommRing S] {w : S}

-- Rebuild only the curvature proofs: this avoids transporting all component maps across
-- the equality of potentials -(-w) = w.
private abbrev inverseDual (X : MatrixFactorization S (-w)) : MatrixFactorization S w :=
  ofCurvedDuplex
    { X₀ := (dual X).obj.X₀
      X₁ := (dual X).obj.X₁
      d₀ := (dual X).obj.d₀
      d₁ := (dual X).obj.d₁
      d₀_comp_d₁ := by simpa using (dual X).obj.d₀_comp_d₁
      d₁_comp_d₀ := by simpa using (dual X).obj.d₁_comp_d₀ }
    inferInstance inferInstance

private def inverseDualMap {X Y : MatrixFactorization S (-w)} (f : X ⟶ Y) :
    inverseDual Y ⟶ inverseDual X :=
  InducedCategory.homMk
    { f₀ := (dualMap f).hom.f₀
      f₁ := (dualMap f).hom.f₁
      comm₀ := (dualMap f).hom.comm₀
      comm₁ := (dualMap f).hom.comm₁ }

private def inverseDualFunctor : MatrixFactorization S (-w) ⥤ (MatrixFactorization S w)ᵒᵖ where
  obj X := op (inverseDual X)
  map f := (inverseDualMap f).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    apply CurvedDuplex.hom_ext <;> simp [inverseDualMap, InducedCategory.homMk]
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    apply CurvedDuplex.hom_ext <;> simp [inverseDualMap, InducedCategory.homMk]

private noncomputable def unitComponent (X : MatrixFactorization S w) :
    inverseDual (dual X) ≅ X :=
  ObjectProperty.isoMk (P := isProjective S w)
    (X := inverseDual (dual X)) (Y := doubleDual X)
    (CurvedDuplex.isoMk (Iso.refl _) (Iso.refl _)
      (by
        dsimp [inverseDual, dual, CurvedDuplex.dual, ofCurvedDuplex]
        simp)
      (by simp)) ≪≫ X.doubleDualIso

private noncomputable def counitComponent (X : MatrixFactorization S (-w)) :
    dual (inverseDual X) ≅ X :=
  ObjectProperty.isoMk (P := isProjective S (-w))
    (X := dual (inverseDual X)) (Y := doubleDual X)
    (CurvedDuplex.isoMk (Iso.refl _) (Iso.refl _)
      (by
        dsimp [inverseDual, dual, CurvedDuplex.dual, ofCurvedDuplex]
        simp)
      (by simp)) ≪≫ X.doubleDualIso

private noncomputable def dualUnitIso :
    𝟭 (MatrixFactorization S w)ᵒᵖ ≅ dualFunctor ⋙ inverseDualFunctor := by
  unfold dualFunctor
  exact NatIso.ofComponents (fun X ↦ (unitComponent X.unop).op) (by
    intro X Y f
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    -- Normalize the rebuilt curvature proofs and projectivity instances before applying
    -- the componentwise evaluation naturality lemma.
    dsimp [inverseDualFunctor, inverseDualMap, unitComponent, InducedCategory.homMk,
      ObjectProperty.isoMk, CurvedDuplex.isoMk, dualMap, CurvedDuplex.dualMap,
      inverseDual, dual, CurvedDuplex.dual, ofCurvedDuplex, ObjectProperty.homMk,
      doubleDual, CurvedDuplex.doubleDual, Iso.trans]
    apply CurvedDuplex.hom_ext <;>
      simp [CurvedDuplex.homMk, Preadditive.neg_comp, Preadditive.comp_neg,
        FGModuleCat.dualEvalIso_hom_naturality])

private noncomputable def dualCounitIso :
    inverseDualFunctor ⋙ dualFunctor ≅ 𝟭 (MatrixFactorization S (-w)) := by
  unfold dualFunctor
  exact NatIso.ofComponents counitComponent (by
    intro X Y f
    apply InducedCategory.hom_ext
    -- As for the unit, normalize the component types before using evaluation naturality.
    dsimp [inverseDualFunctor, inverseDualMap, counitComponent, InducedCategory.homMk,
      ObjectProperty.isoMk, CurvedDuplex.isoMk, dualMap, CurvedDuplex.dualMap,
      inverseDual, dual, CurvedDuplex.dual, ofCurvedDuplex, ObjectProperty.homMk,
      doubleDual, CurvedDuplex.doubleDual, Iso.trans]
    apply CurvedDuplex.hom_ext <;>
      simp [CurvedDuplex.homMk, Preadditive.neg_comp, Preadditive.comp_neg,
        FGModuleCat.dualEvalIso_hom_naturality])

/-- Signed transpose duality is an additive equivalence from the opposite category of
finite-projective factorizations of `w` to factorizations of `-w`. -/
noncomputable def dualEquivalence :
    (MatrixFactorization S w)ᵒᵖ ≌ MatrixFactorization S (-w) :=
  CategoryTheory.Equivalence.mk dualFunctor inverseDualFunctor dualUnitIso dualCounitIso

/-- The forward functor of the duality equivalence is the signed transpose functor. -/
@[simp]
theorem dualEquivalence_functor :
    (dualEquivalence (S := S) (w := w)).functor = dualFunctor := (rfl)

instance : (dualEquivalence (S := S) (w := w)).functor.Additive := by
  rw [dualEquivalence_functor]
  infer_instance

instance : (dualFunctor (S := S) (w := w)).IsEquivalence :=
  (dualEquivalence (S := S) (w := w)).isEquivalence_functor

/-- The even component of the inverse duality is the module dual. -/
@[simp]
theorem dualEquivalence_inverse_obj_X₀ (X : MatrixFactorization S (-w)) :
    ((dualEquivalence (S := S) (w := w)).inverse.obj X).unop.obj.X₀ =
      FGModuleCat.dual S X.obj.X₀ := (rfl)

/-- The odd component of the inverse duality is the module dual. -/
@[simp]
theorem dualEquivalence_inverse_obj_X₁ (X : MatrixFactorization S (-w)) :
    ((dualEquivalence (S := S) (w := w)).inverse.obj X).unop.obj.X₁ =
      FGModuleCat.dual S X.obj.X₁ := (rfl)

/-- The inverse duality uses the transpose of the odd differential in even degree. -/
@[simp]
theorem dualEquivalence_inverse_obj_d₀ (X : MatrixFactorization S (-w)) :
    ((dualEquivalence (S := S) (w := w)).inverse.obj X).unop.obj.d₀ =
      eqToHom (dualEquivalence_inverse_obj_X₀ X) ≫ FGModuleCat.dualMap X.obj.d₁ ≫
        eqToHom (dualEquivalence_inverse_obj_X₁ X).symm := (rfl)

/-- The inverse duality uses the negative transpose of the even differential in odd degree. -/
@[simp]
theorem dualEquivalence_inverse_obj_d₁ (X : MatrixFactorization S (-w)) :
    ((dualEquivalence (S := S) (w := w)).inverse.obj X).unop.obj.d₁ =
      eqToHom (dualEquivalence_inverse_obj_X₁ X) ≫ (-FGModuleCat.dualMap X.obj.d₀) ≫
        eqToHom (dualEquivalence_inverse_obj_X₀ X).symm := (rfl)

/-- In even degree, inverse duality acts by transposing the component map. -/
@[simp]
theorem dualEquivalence_inverse_map_f₀ {X Y : MatrixFactorization S (-w)} (f : X ⟶ Y) :
    ((dualEquivalence (S := S) (w := w)).inverse.map f).unop.hom.f₀ =
      eqToHom (dualEquivalence_inverse_obj_X₀ Y) ≫ FGModuleCat.dualMap f.hom.f₀ ≫
        eqToHom (dualEquivalence_inverse_obj_X₀ X).symm := (rfl)

/-- In odd degree, inverse duality acts by transposing the component map. -/
@[simp]
theorem dualEquivalence_inverse_map_f₁ {X Y : MatrixFactorization S (-w)} (f : X ⟶ Y) :
    ((dualEquivalence (S := S) (w := w)).inverse.map f).unop.hom.f₁ =
      eqToHom (dualEquivalence_inverse_obj_X₁ Y) ≫ FGModuleCat.dualMap f.hom.f₁ ≫
        eqToHom (dualEquivalence_inverse_obj_X₁ X).symm := (rfl)

private theorem inverseDualMap_mem_nullHomotopic
    {X Y : MatrixFactorization S (-w)} (f : X ⟶ Y)
    (hf : f ∈ (nullHomotopic (S := S) (w := -w)).hom X Y) :
    inverseDualMap f ∈ (nullHomotopic (S := S) (w := w)).hom _ _ := by
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff f).mp hf
  apply (mem_nullHomotopic_iff _).mpr
  refine ⟨-FGModuleCat.dualMap h₁, FGModuleCat.dualMap h₀, ?_⟩
  apply CurvedDuplex.hom_ext <;>
    simp [inverseDualMap, InducedCategory.homMk, ← hh,
      CurvedDuplex.dualMap_nullHomotopicMap]

/-- A map of finite-projective matrix factorizations is null-homotopic if and only if
its signed transpose is null-homotopic. -/
-- Reflect before the generic membership rule expands null homotopies into witnesses.
@[simp↓]
theorem dualMap_mem_nullHomotopic_iff {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    dualMap f ∈ (nullHomotopic (S := S) (w := -w)).hom _ _ ↔
      f ∈ (nullHomotopic (S := S) (w := w)).hom X Y := by
  refine ⟨fun hf ↦ ?_, dualMap_mem_nullHomotopic f⟩
  have hd := inverseDualMap_mem_nullHomotopic (dualMap f) hf
  have hn : (unitComponent X).hom ≫ f =
      inverseDualMap (dualMap f) ≫ (unitComponent Y).hom := by
    simpa [dualUnitIso, dualFunctor, inverseDualFunctor, NatIso.ofComponents] using
      congrArg Quiver.Hom.unop ((dualUnitIso (S := S) (w := w)).hom.naturality f.op)
  have hm := (nullHomotopic (S := S) (w := w)).comp_mem_left
    (unitComponent X).inv
    ((nullHomotopic (S := S) (w := w)).comp_mem_right (unitComponent Y).hom hd)
  rw [← hn] at hm
  simpa using hm

instance : (homotopyDualFunctor (S := S) (w := w)).IsEquivalence := by
  have hker :
      (dualFunctor ⋙ (nullHomotopic (S := S) (w := -w)).quotientFunctor).rightOp.kerIdeal ≤
        nullHomotopic (S := S) (w := w) := by
    intro X Y f hf
    apply (dualMap_mem_nullHomotopic_iff f).mp
    rw [Functor.mem_kerIdeal_hom] at hf
    have hz := congrArg Quiver.Hom.unop hf
    simp only [Functor.rightOp_map_unop, Functor.comp_map, Limits.unop_zero] at hz
    have hm := (MorphismIdeal.quotientFunctor_map_eq_zero_iff
      (nullHomotopic (S := S) (w := -w))).mp hz
    -- Reduce the functor in the hom-group instances as well as in the displayed morphism.
    dsimp [dualFunctor] at hm
    exact hm
  let liftIsEquivalence
      (hF : nullHomotopic (S := S) (w := w) ≤
        (dualFunctor ⋙ (nullHomotopic (S := S) (w := -w)).quotientFunctor).rightOp.kerIdeal) :
      ((nullHomotopic (S := S) (w := w)).lift
        (dualFunctor ⋙ (nullHomotopic (S := S) (w := -w)).quotientFunctor).rightOp
        hF).IsEquivalence :=
    (nullHomotopic (S := S) (w := w)).isEquivalence_lift _ hF hker
  unfold homotopyDualFunctor
  infer_instance

/-- Signed transpose duality on homotopy classes is an additive equivalence between the
opposite of `HMF(S,w)` and `HMF(S,-w)`. -/
noncomputable def homotopyDualEquivalence :
    (HomotopyCategory (S := S) (w := w))ᵒᵖ ≌ HomotopyCategory (S := S) (w := -w) :=
  (homotopyDualFunctor (S := S) (w := w)).asEquivalence

/-- The homotopy duality equivalence uses the existing functor on homotopy classes. -/
@[simp]
theorem homotopyDualEquivalence_functor :
    (homotopyDualEquivalence (S := S) (w := w)).functor = homotopyDualFunctor := (rfl)

instance : (homotopyDualEquivalence (S := S) (w := w)).functor.Additive := by
  rw [homotopyDualEquivalence_functor]
  infer_instance

end TauCeti.MatrixFactorization
