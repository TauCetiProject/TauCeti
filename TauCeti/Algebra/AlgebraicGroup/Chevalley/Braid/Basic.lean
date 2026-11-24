/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.Lie.Presentation.Serre
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Transporting Weyl word relations to Chevalley data, and the single-bond braid relation

A relation between two words in the rational Weyl units of the represented simple root
generators gives the same relation between the pinned simple Weyl representatives over every
commutative ring (`TauCeti.DynkinType.ChevalleyDatum.weylElement_prod_eq_of_weylUnit_prod_eq`).
The rational relation is first restricted to the datum's integral Kostant-stable lattice and
then extended to the value ring. This avoids imposing any restriction on weight multiplicities
or choosing a signed permutation weight basis.

Applied to the rational Serre-operator braid relation, it shows that pinned simple Weyl
representatives at a single bond satisfy the length-three braid relation over every
commutative ring. The equality holds in the actual point group, including in bad
characteristic and over nonreduced rings, not just in a Weyl quotient.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

open scoped _root_.Matrix in
/-- The represented pinned Chevalley generators form a Serre system for the transposed pinned
Cartan matrix, as the pinned generators themselves do
(`TauCeti.DynkinType.isSerreSystem_lieBasis`). The bond corollaries apply the rational
Serre-operator braid relations to this system. -/
theorem isSerreSystem_representation :
    IsSerreSystem ℚ t.cartanMatrixᵀ
      (fun k => D.representation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).h k)))
      (fun k => D.representation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e k)))
      (fun k => D.representation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).f k))) := by
  simpa only [Function.comp_def, LieHom.comp_apply, AlgHom.toLieHom_apply] using
    (t.isSerreSystem_lieBasis ht).map
      (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))

/-- **Transport of word relations to the points.** If two words in the rational Weyl units of
the represented simple root generators have equal products, then the same two words in the pinned
simple Weyl representatives `nₖ(1)` have equal products over every commutative value ring. The
rational relation is restricted to the Kostant-stable lattice and then extended to `A`, so no
division takes place in `A`. -/
theorem weylElement_prod_eq_of_weylUnit_prod_eq (w₁ w₂ : List (Fin t.rank))
    (h : ∀ (hE : ∀ k, IsNilpotent
        (D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e k))))
      (hF : ∀ k, IsNilpotent
        (D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).f k)))),
      (w₁.map fun k => weylUnit (hE k) (hF k)).prod = (w₂.map fun k => weylUnit (hE k) (hF k)).prod)
    (A : Type*) [CommRing A] :
    (w₁.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod =
      (w₂.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod := by
  let u := fun k => weylUnit (D.isNilpotent_representation_rootGenerator (.inl k))
    (D.isNilpotent_representation_rootGenerator (.inr k))
  have hu : (w₁.map u).prod = (w₂.map u).prod := by
    simpa only [u, LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
      h (fun k => by
          simpa only [LieAlgebra.Basis.rootGenerator_inl] using
            D.isNilpotent_representation_rootGenerator (.inl k))
        (fun k => by
          simpa only [LieAlgebra.Basis.rootGenerator_inr] using
            D.isNilpotent_representation_rootGenerator (.inr k))
  let n := fun k => kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    D.representation D.lattice D.representation_mem_lattice
    (D.isNilpotent_representation_rootGenerator (.inl k))
    (D.isNilpotent_representation_rootGenerator (.inr k))
  -- On the lattice, each word acts by the corresponding word in the rational Weyl units.
  have hres (w : List (Fin t.rank)) (v : D.lattice) :
      (((w.map n).prod v : D.lattice) : D.carrier) =
        ((w.map u).prod : Module.End ℚ D.carrier) v := by
    induction w generalizing v with
    | nil => rfl
    | cons k w ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, Units.val_mul, n, u,
        coe_kostantWeylRestrict_apply, Module.End.smul_def, ← ih]
  have hn : (w₁.map n).prod = (w₂.map n).prod := by
    ext v
    rw [hres, hres, hu]
  -- Scalar extension followed by the matrix realization is multiplicative.
  let f := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  let g : (D.lattice ≃ₗ[ℤ] D.lattice) →* Matrix.GeneralLinearGroup (Fin D.dim) A :=
    { toFun e := f (LinearMap.GeneralLinearGroup.ofLinearEquiv (e.baseChange ℤ A))
      map_one' := by rw [LinearEquiv.baseChange_one]; exact map_one f
      map_mul' e₁ e₂ := by
        rw [LinearEquiv.baseChange_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul, map_mul] }
  have hg (k : Fin t.rank) :
      (D.weylElement (t.simpleIndex ht k) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) =
        g (n k) := by
    rw [D.coe_weylElement_simpleIndex_one k A]
    -- `coe_weylElement_simpleIndex_one` is stated over `CommAlgCat.of ℤ A`, whose carrier is `A`
    -- by definition, and with the `MulEquiv` form of the matrix realization; up to these
    -- unfoldings both sides are `f` applied to a general linear group element.
    change f _ = f _
    congr 1
    apply Units.ext
    rw [kostantWeylGL_val, kostantWeylPoints_toLinearMap]
    -- The underlying linear map of `LinearMap.GeneralLinearGroup.ofLinearEquiv e` is `e` by
    -- definition, and `LinearEquiv.coe_baseChange` identifies that of `(n k).baseChange ℤ A`.
    exact (LinearEquiv.coe_baseChange _ _ _ _ _).symm
  have hw (w : List (Fin t.rank)) :
      (((w.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod :
        D.points A) : Matrix.GeneralLinearGroup (Fin D.dim) A) = g (w.map n).prod := by
    rw [map_list_prod, ← (D.points A).subtype_apply, map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun k _ => hg k)
  apply Subtype.ext
  rw [hw, hw, hn]

/-- Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative value ring. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_one (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 := by
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    using D.weylElement_prod_eq_of_weylUnit_prod_eq [i, j, i] [j, i, j]
    (fun hE hF => by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
        using D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_one
          (i := i) (j := j) (by simp) (by simp) hji hij (hE i) (hF i) (hE j) (hF j)) A

end TauCeti.DynkinType.ChevalleyDatum
