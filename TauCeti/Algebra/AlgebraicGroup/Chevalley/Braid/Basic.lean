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
# Word transfer and the single-bond braid relation in Chevalley data

Any equality of words in the pinned rational `weylUnit` operators of `D.representation` restricts
to the datum's Kostant-stable `ℤ`-lattice and extends scalars to every commutative ring `A`,
giving the same word equality in `D.points A`
(`prod_map_weylElement_eq_of_prod_map_weylUnit_eq`). Specializing to the single-bond Serre
identity proves that pinned simple Weyl representatives at a single bond satisfy the length-three
braid relation in `D.points A` over every commutative ring `A`, including in bad characteristic
and over nonreduced rings, without any restriction on weight multiplicities.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open Matrix TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The pinned Chevalley generators in `D.representation` form a Serre system over `ℚ` for the
transposed Cartan matrix `t.cartanMatrixᵀ`. -/
theorem isSerreSystem_representation :
    IsSerreSystem ℚ t.cartanMatrixᵀ
      (fun k => D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).h k)))
      (fun k => D.representation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator (.inl k))))
      (fun k => D.representation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator (.inr k)))) := by
  simpa only [Function.comp_def, LieHom.comp_apply, AlgHom.toLieHom_apply,
    LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr] using
    (t.isSerreSystem_lieBasis ht).map
      (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))

/-- **Transfer of rational `weylUnit` word identities to `D.points A`.** Any equality of products
of words in the pinned rational Weyl units on `D.carrier` restricts to `D.lattice`, extends
scalars to `A`, and gives the corresponding equality of words in the pinned simple Weyl elements
`D.weylElement (t.simpleIndex ht k) A 1` inside `D.points A` over every commutative ring `A`. -/
theorem prod_map_weylElement_eq_of_prod_map_weylUnit_eq {l₁ l₂ : List (Fin t.rank)}
    (h : (l₁.map fun k => weylUnit (D.isNilpotent_representation_rootGenerator (.inl k))
            (D.isNilpotent_representation_rootGenerator (.inr k))).prod =
          (l₂.map fun k => weylUnit (D.isNilpotent_representation_rootGenerator (.inl k))
            (D.isNilpotent_representation_rootGenerator (.inr k))).prod)
    (A : Type*) [CommRing A] :
    (l₁.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod =
      (l₂.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod := by
  let u (k : Fin t.rank) : (Module.End ℚ D.carrier)ˣ :=
    weylUnit (D.isNilpotent_representation_rootGenerator (.inl k))
      (D.isNilpotent_representation_rootGenerator (.inr k))
  let nR (k : Fin t.rank) : D.lattice ≃ₗ[ℤ] D.lattice :=
    kostantWeylRestrict (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl k))
      (D.isNilpotent_representation_rootGenerator (.inr k))
  have hnR_apply (l : List (Fin t.rank)) (v : D.lattice) :
      ((((l.map nR).prod : D.lattice ≃ₗ[ℤ] D.lattice) v : D.lattice) : D.carrier) =
        (((l.map u).prod : (Module.End ℚ D.carrier)ˣ) : Module.End ℚ D.carrier) v := by
    induction l with
    | nil => rfl
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, Units.val_mul,
        nR, coe_kostantWeylRestrict_apply, Module.End.smul_def, u, ih]
  have hnR : (l₁.map nR).prod = (l₂.map nR).prod := by
    ext v
    exact (hnR_apply l₁ v).trans
      ((congrArg (fun x : (Module.End ℚ D.carrier)ˣ => (x : Module.End ℚ D.carrier) v) h).trans
        (hnR_apply l₂ v).symm)
  let nGL (k : Fin t.rank) :=
    kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl k))
      (D.isNilpotent_representation_rootGenerator (.inr k)) A
  have hnGL_tmul (l : List (Fin t.rank)) (r : A) (v : D.lattice) :
      (((l.map nGL).prod : _) : Module.End A (A ⊗[ℤ] D.lattice)) (r ⊗ₜ[ℤ] v) =
        r ⊗ₜ[ℤ] ((l.map nR).prod v) := by
    induction l with
    | nil => rfl
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, mul_apply_eq_comp, ih,
        nGL, nR, kostantWeylGL_val, LinearEquiv.coe_coe, kostantWeylPoints_apply_tmul]
  have hnGL : (l₁.map nGL).prod = (l₂.map nGL).prod := by
    apply Units.ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r v => rw [hnGL_tmul, hnR, ← hnGL_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  let f := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  have hf (k : Fin t.rank) :
      (D.weylElement (t.simpleIndex ht k) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) =
        f (nGL k) := D.coe_weylElement_simpleIndex_one k A
  have hcoe (l : List (Fin t.rank)) :
      (((l.map fun k => D.weylElement (t.simpleIndex ht k) A 1).prod : D.points A) :
        Matrix.GeneralLinearGroup (Fin D.dim) A) = f (l.map nGL).prod := by
    induction l with
    | nil => simp
    | cons k l ih => simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, map_mul, hf, ih]
  exact Subtype.ext ((hcoe l₁).trans ((congrArg f hnGL).trans (hcoe l₂).symm))

/-- Pinned simple Weyl representatives at a single bond satisfy the length-three braid
relation over every commutative value ring. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_one (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)
    (A : Type*) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 := by
  simpa [mul_assoc] using D.prod_map_weylElement_eq_of_prod_map_weylUnit_eq
    (l₁ := [i, j, i]) (l₂ := [j, i, j]) (by
      simpa [mul_assoc] using D.isSerreSystem_representation.weylUnit_braid_of_cartan_eq_neg_one
        (i := i) (j := j) (by simp) (by simp) hji hij
        (D.isNilpotent_representation_rootGenerator (.inl i))
        (D.isNilpotent_representation_rootGenerator (.inr i))
        (D.isNilpotent_representation_rootGenerator (.inl j))
        (D.isNilpotent_representation_rootGenerator (.inr j))) A

end TauCeti.DynkinType.ChevalleyDatum
