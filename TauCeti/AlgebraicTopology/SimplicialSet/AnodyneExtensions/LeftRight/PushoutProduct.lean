/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing

/-!
# Left and right anodyne extensions and pushout-products

This file proves Joyal's theorem that the pushout-product of a monomorphism and a left (resp.
right) anodyne extension of simplicial sets is a left (resp. right) anodyne extension
(`SSet.leftAnodyneExtensions_pushoutObjObjι`, `SSet.rightAnodyneExtensions_pushoutObjObjι`).
Dually, if `i : X₁ ⟶ Y₁` is a monomorphism and `p : E ⟶ B` is a left (resp. right) fibration,
then the map from `Y₁ ⟶[SSet] E` to the pullback of `X₁ ⟶[SSet] E` and `Y₁ ⟶[SSet] B` over
`X₁ ⟶[SSet] B` is a left (resp. right) fibration (`SSet.leftFibration_pullbackObjObjπ`,
`SSet.rightFibration_pullbackObjObjπ`). In particular, postcomposition with a left (resp. right)
fibration `p` gives a left (resp. right) fibration `(ihom X).map p` of functor simplicial sets.

The generating case is the inclusion of `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])` into
`Δ[m + 1] ⊗ Δ[n]`. Mathlib constructs a regular pairing for it, in the sense of Moss, to show
that it is an (inner) anodyne extension. For `k < m + 1` the pairing never attaches a horn
along its last face, and for `0 < k` never along its first face, so the inclusion is a left,
resp. right, anodyne extension (`SSet.prodStdSimplex.leftAnodyneExtensions_unionProd_ι`,
`SSet.prodStdSimplex.rightAnodyneExtensions_unionProd_ι`). The argument otherwise follows the
inner case in `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean`.

## References

* J. Lurie, *Higher Topos Theory*, Section 2.1.2, in particular Corollary 2.1.2.7.
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
* J. McKoen, *A Formalization of Functor Quasi-Categories in Lean 4*, for the inner case in
  Mathlib.
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Limits

open scoped Simplicial

namespace SSet

namespace prodStdSimplex

/-- The inclusion `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ Δ[m + 1] ⊗ Δ[n]` is a left
anodyne extension when `k < m + 1`. -/
lemma leftAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (hk : k < Fin.last (m + 1))
    (n : ℕ) :
    leftAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hk)
  refine (pairingCore k n).pairing.leftAnodyneExtensions fun x d hd ↦ ?_
  obtain ⟨s, rfl⟩ := (pairingCore k n).equivII.surjective x
  subst hd
  rw [Subcomplex.PairingCore.index_pairing_equivII]
  exact (Fin.castSucc_lt_last s.index).ne

/-- The inclusion `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ Δ[m + 1] ⊗ Δ[n]` is a right
anodyne extension when `0 < k`. -/
lemma rightAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (hk : 0 < k) (n : ℕ) :
    rightAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  by_cases hk' : k = Fin.last (m + 1)
  · -- For the last horn, Mathlib's `prodStdSimplex.pairing` is the opposite of the pairing for
    -- the first horn, transported along the isomorphism reversing the vertices of
    -- `Δ[m + 1] ⊗ Δ[n]`. We restate it, as its `dite` does not reduce under the binders below.
    -- The opposite reverses the face indices, which avoid the last face before reversal.
    subst hk'
    let e : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) ≅ opFunctor.obj (Δ[m + 1] ⊗ Δ[n]) :=
      ((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
        Functor.Monoidal.μIso opFunctor _ _
    have hA : (Subcomplex.unionProd.{u} Λ[m + 1, (0 : Fin (m + 1)).castSucc] ∂Δ[n]).op.preimage
        e.hom =
        Subcomplex.unionProd.{u} Λ[m + 1, Fin.last (m + 1)] ∂Δ[n] := by
      dsimp [e]
      rw [Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd,
        Subcomplex.preimage_unionProd, op_boundary, op_horn, Fin.rev_zero]
    refine ((pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso e hA).rightAnodyneExtensions ?_
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (Subcomplex.N.orderIsoOfIso e hA).symm.surjective b
    simp only [Subcomplex.Pairing.ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    rw [Subcomplex.Pairing.ofIso_index _ e hA ⟨a, hb⟩ hd]
    obtain ⟨c, rfl⟩ := Subcomplex.N.opEquiv.symm.surjective a
    rw [Subcomplex.Pairing.index_op _ ⟨c, hb⟩ hd hd, Fin.rev_ne_iff, Fin.rev_zero]
    obtain ⟨s, hs⟩ := (pairingCore (0 : Fin (m + 1)) n).equivII.surjective ⟨c, hb⟩
    simp only [Subtype.ext_iff] at hs
    subst hs hd
    exact ne_of_eq_of_ne ((pairingCore _ n).index_pairing_equivII s)
      (Fin.castSucc_lt_last s.index).ne
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk'
    obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.castSucc_pos_iff.mp hk).ne'
    exact (pairing k.castSucc.succ n).rightAnodyneExtensions
      fun x _ hd ↦ Subcomplex.Pairing.IsInner.ne_zero x hd

end prodStdSimplex

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}} {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

/-- If `i` is a monomorphism and `p` has the right lifting property with respect to
`(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ Δ[m + 1] ⊗ Δ[n]` for all `n`, then the
pullback-hom of `i` and `p` has the right lifting property with respect to `Λ[m + 1, k] ⟶ Δ[m + 1]`.
-/
lemma hasLiftingProperty_horn_ι_pullbackObjObjπ [Mono i] {m : ℕ} (k : Fin (m + 2))
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p)
    (h : ∀ n, HasLiftingProperty (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι p) :
    HasLiftingProperty Λ[m + 1, k].ι sq₁₃.π := by
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[m + 1, k].ι
  have e : Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι := Arrow.isoMk (Iso.refl _) (β_ _ _)
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂,
    HasLiftingProperty.iff_of_arrow_iso_left e]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[m + 1, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} _ _), Subcomplex.unionProd.pushoutObjObj_ι]
  exact h n

/-- If `i` is a monomorphism and `p` is a left fibration, the pullback-hom of `i` and `p` is a
left fibration. -/
lemma leftFibration_pullbackObjObjπ [Mono i] [LeftFibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    LeftFibration sq₁₃.π := by
  rw [leftFibration_iff, leftFibrations_eq_rlp]
  rintro _ _ _ ⟨k, hk⟩
  exact hasLiftingProperty_horn_ι_pullbackObjObjπ k sq₁₃ fun n ↦
    (prodStdSimplex.leftAnodyneExtensions_unionProd_ι k hk n).hasLiftingProperty p

/-- If `i` is a monomorphism and `p` is a right fibration, the pullback-hom of `i` and `p` is a
right fibration. -/
lemma rightFibration_pullbackObjObjπ [Mono i] [RightFibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    RightFibration sq₁₃.π := by
  rw [rightFibration_iff, rightFibrations_eq_rlp]
  rintro _ _ _ ⟨k, hk⟩
  exact hasLiftingProperty_horn_ι_pullbackObjObjπ k sq₁₃ fun n ↦
    (prodStdSimplex.rightAnodyneExtensions_unionProd_ι k hk n).hasLiftingProperty p

/-- The pushout-product of a monomorphism and a left anodyne extension is a left anodyne
extension. -/
lemma leftAnodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : leftAnodyneExtensions j) :
    leftAnodyneExtensions sq₁₂.ι := by
  rw [leftAnodyneExtensions_eq_llp] at hj ⊢
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  have : LeftFibration p := ⟨hp⟩
  exact hj _ (leftFibration_pullbackObjObjπ sq₁₃).mem

/-- The pushout-product of a monomorphism and a right anodyne extension is a right anodyne
extension. -/
lemma rightAnodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : rightAnodyneExtensions j) :
    rightAnodyneExtensions sq₁₂.ι := by
  rw [rightAnodyneExtensions_eq_llp] at hj ⊢
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  have : RightFibration p := ⟨hp⟩
  exact hj _ (rightFibration_pullbackObjObjπ sq₁₃).mem

/-- The pushout-product of a left anodyne extension and a monomorphism is a left anodyne
extension. -/
lemma leftAnodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono j] (hi : leftAnodyneExtensions i) :
    leftAnodyneExtensions sq₁₂.ι := by
  refine (leftAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (leftAnodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

/-- The pushout-product of a right anodyne extension and a monomorphism is a right anodyne
extension. -/
lemma rightAnodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono j] (hi : rightAnodyneExtensions i) :
    rightAnodyneExtensions sq₁₂.ι := by
  refine (rightAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (rightAnodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

lemma leftAnodyneExtensions_unionProd_ι {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : leftAnodyneExtensions B.ι) :
    leftAnodyneExtensions (A.unionProd B).ι :=
  leftAnodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

lemma rightAnodyneExtensions_unionProd_ι {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : rightAnodyneExtensions B.ι) :
    rightAnodyneExtensions (A.unionProd B).ι :=
  rightAnodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

lemma leftAnodyneExtensions_unionProd_ι' {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : leftAnodyneExtensions A.ι) :
    leftAnodyneExtensions (A.unionProd B).ι :=
  leftAnodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

lemma rightAnodyneExtensions_unionProd_ι' {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : rightAnodyneExtensions A.ι) :
    rightAnodyneExtensions (A.unionProd B).ι :=
  rightAnodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

lemma leftAnodyneExtensions.whiskerRight {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : leftAnodyneExtensions f) (Z : SSet.{u}) :
    leftAnodyneExtensions (f ▷ Z) :=
  leftAnodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

lemma rightAnodyneExtensions.whiskerRight {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : rightAnodyneExtensions f) (Z : SSet.{u}) :
    rightAnodyneExtensions (f ▷ Z) :=
  rightAnodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

lemma leftAnodyneExtensions.whiskerLeft {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : leftAnodyneExtensions f) (Z : SSet.{u}) :
    leftAnodyneExtensions (Z ◁ f) :=
  leftAnodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

lemma rightAnodyneExtensions.whiskerLeft {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : rightAnodyneExtensions f) (Z : SSet.{u}) :
    rightAnodyneExtensions (Z ◁ f) :=
  rightAnodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

/-- Postcomposition with a left fibration is a left fibration of functor simplicial sets. -/
instance {E B X : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    LeftFibration ((ihom X).map p) :=
  leftFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

/-- Postcomposition with a right fibration is a right fibration of functor simplicial sets. -/
instance {E B X : SSet.{u}} (p : E ⟶ B) [RightFibration p] :
    RightFibration ((ihom X).map p) :=
  rightFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

end SSet
