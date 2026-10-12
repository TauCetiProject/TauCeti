/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.TensorDifferential
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Chains

/-!
# The cubical cross product as a chain map

The cross product of normalized cubical chains
(`TauCeti.NormalizedCubicalChain.crossProduct`) is bilinear and satisfies the Leibniz rule, so it
assembles into a chain map out of the tensor product of the normalized cubical chain complexes,
`N(X) ⊗ N(Y) ⟶ N(X × Y)`, natural in both spaces.

The tensor product of chain complexes is Mathlib's, with the differential
`d (a ⊗ b) = d a ⊗ b + (-1) ^ p • (a ⊗ d b)` on a summand of bidegree `(p, q)`.  The cross product
is a map on each summand, followed by the reindexing `p + q = n`.

## Main definitions and results

* `TauCeti.crossProductComplex R X Y`: the cross product as a chain map
  `N(X) ⊗ N(Y) ⟶ N(X ⊗ Y)`.
* `TauCeti.ι_crossProductComplex_f_apply`: its value on a summand of bidegree `(p, q)`.
* `TauCeti.crossProductComplex_naturality`: naturality in both spaces.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits

universe u

namespace TauCeti

variable (R : Type u) [CommRing R] (X Y : TopCat.{u})

/-- The cross product of normalized chains of degrees `p` and `q`, as a map out of the tensor
product of modules to the chains of degree `n = p + q` of the product space. -/
def crossProductSummand (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of R (NormalizedCubicalChain X R p) ⊗ ModuleCat.of R (NormalizedCubicalChain Y R q) ⟶
      ModuleCat.of R (NormalizedCubicalChain (X × Y) R n) :=
  ModuleCat.ofHom (TensorProduct.lift
    (LinearMap.compr₂ (NormalizedCubicalChain.crossProduct X Y R p q)
      (NormalizedCubicalChain.cast R h)))

@[simp]
theorem crossProductSummand_apply (p q n : ℕ) (h : p + q = n) (a : NormalizedCubicalChain X R p)
    (b : NormalizedCubicalChain Y R q) :
    (crossProductSummand R X Y p q n h).hom (a ⊗ₜ b) =
      NormalizedCubicalChain.cast R h (NormalizedCubicalChain.crossProduct X Y R p q a b) := by
  rw [crossProductSummand, ModuleCat.hom_ofHom]
  exact TensorProduct.lift.tmul a b

variable {R X Y}

/-- The degree-`n` component of the cross product chain map: the cross product on each summand
of bidegree `(p, q)` with `p + q = n`. -/
def crossProductX (n : ℕ) :
    ((normalizedCubicalChainComplex R).obj X ⊗ (normalizedCubicalChainComplex R).obj Y).X n ⟶
      ((normalizedCubicalChainComplex R).obj (X ⊗ Y)).X n :=
  mapBifunctorDesc fun p q h ↦ crossProductSummand R X Y p q n h

/-- The cross product chain map restricted to a summand is the cross product of that bidegree. -/
@[reassoc]
theorem ι_crossProductX {p q n : ℕ} (h : p + q = n) :
    ιTensorObj ((normalizedCubicalChainComplex R).obj X)
        ((normalizedCubicalChainComplex R).obj Y) p q n h ≫ crossProductX n =
      crossProductSummand R X Y p q n h := by
  exact ι_mapBifunctorDesc _ _ _ _

/-- Application of a composite of morphisms of modules. -/
private theorem comp_hom_apply' {M N P : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g).hom x = g.hom (f.hom x) :=
  (rfl)

/-- The differential of the normalized cubical chain complex is the boundary. -/
private theorem d_hom_apply (Z : TopCat.{u}) (n : ℕ) (x : NormalizedCubicalChain Z R (n + 1)) :
    (((normalizedCubicalChainComplex R).obj Z).d (n + 1) n).hom x =
      NormalizedCubicalChain.boundary Z R n x :=
  normalizedCubicalChainComplex_obj_d_apply Z n x

/-- Whiskering the differential of the first factor with a chain of the second. -/
private theorem whiskerRight_d_apply (r s : ℕ) (a : NormalizedCubicalChain X R (r + 1))
    (b : NormalizedCubicalChain Y R s) :
    (((normalizedCubicalChainComplex R).obj X).d (r + 1) r ▷
        ((normalizedCubicalChainComplex R).obj Y).X s).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.boundary X R r a ⊗ₜ[R] b := by
  change ((((normalizedCubicalChainComplex R).obj X).d (r + 1) r).hom a) ⊗ₜ[R] b = _
  rw [d_hom_apply]
  rfl

/-- Whiskering a chain of the first factor with the differential of the second. -/
private theorem whiskerLeft_d_apply (r s : ℕ) (a : NormalizedCubicalChain X R r)
    (b : NormalizedCubicalChain Y R (s + 1)) :
    (((normalizedCubicalChainComplex R).obj X).X r ◁
        ((normalizedCubicalChainComplex R).obj Y).d (s + 1) s).hom (a ⊗ₜ[R] b) =
      a ⊗ₜ[R] NormalizedCubicalChain.boundary Y R s b := by
  change a ⊗ₜ[R] ((((normalizedCubicalChainComplex R).obj Y).d (s + 1) s).hom b) = _
  rw [d_hom_apply]
  rfl

/-- The cross product of a summand, followed by the differential. -/
private theorem summand_d_apply (p q n : ℕ) (h : p + q = n + 1)
    (a : NormalizedCubicalChain X R p) (b : NormalizedCubicalChain Y R q) :
    (crossProductSummand R X Y p q (n + 1) h ≫
        ((normalizedCubicalChainComplex R).obj (X ⊗ Y)).d (n + 1) n).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.boundary (X × Y) R n
        (NormalizedCubicalChain.cast R h (NormalizedCubicalChain.crossProduct X Y R p q a b)) :=
  (d_hom_apply (X ⊗ Y) n _).trans (congrArg _ (crossProductSummand_apply R X Y p q (n + 1) h a b))

/-- The first part of the differential of the tensor product, then the cross product. -/
private theorem whiskerRight_summand_apply (r s n : ℕ) (h : r + s = n)
    (a : NormalizedCubicalChain X R (r + 1)) (b : NormalizedCubicalChain Y R s) :
    (((normalizedCubicalChainComplex R).obj X).d (r + 1) r ▷
          ((normalizedCubicalChainComplex R).obj Y).X s ≫ crossProductSummand R X Y r s n h).hom
        (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.cast R h
        (NormalizedCubicalChain.crossProduct X Y R r s (NormalizedCubicalChain.boundary X R r a)
          b) :=
  (congrArg (crossProductSummand R X Y r s n h).hom (whiskerRight_d_apply r s a b)).trans
    (crossProductSummand_apply R X Y r s n h _ b)

/-- The second part of the differential of the tensor product, then the cross product. -/
private theorem whiskerLeft_summand_apply (r s n : ℕ) (h : r + s = n)
    (a : NormalizedCubicalChain X R r) (b : NormalizedCubicalChain Y R (s + 1)) :
    (((normalizedCubicalChainComplex R).obj X).X r ◁
          ((normalizedCubicalChainComplex R).obj Y).d (s + 1) s ≫
            crossProductSummand R X Y r s n h).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.cast R h
        (NormalizedCubicalChain.crossProduct X Y R r s a
          (NormalizedCubicalChain.boundary Y R s b)) :=
  (congrArg (crossProductSummand R X Y r s n h).hom (whiskerLeft_d_apply r s a b)).trans
    (crossProductSummand_apply R X Y r s n h a _)

/-- The cross product is compatible with the differentials on every summand. -/
private theorem comm_summand (n p q : ℕ) (h : p + q = n + 1) :
    ιTensorObj ((normalizedCubicalChainComplex R).obj X)
        ((normalizedCubicalChainComplex R).obj Y) p q (n + 1) h ≫ crossProductX (n + 1) ≫
          ((normalizedCubicalChainComplex R).obj (X ⊗ Y)).d (n + 1) n =
      ιTensorObj ((normalizedCubicalChainComplex R).obj X)
          ((normalizedCubicalChainComplex R).obj Y) p q (n + 1) h ≫
        ((normalizedCubicalChainComplex R).obj X ⊗
          (normalizedCubicalChainComplex R).obj Y).d (n + 1) n ≫ crossProductX n := by
  have hd : ((normalizedCubicalChainComplex R).obj X ⊗
        (normalizedCubicalChainComplex R).obj Y).d (n + 1) n =
      mapBifunctor.D₁ _ _ (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ _ _ (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [ι_crossProductX_assoc, hd, Preadditive.add_comp, Preadditive.comp_add]
  rcases p with _ | r <;> rcases q with _ | s
  · omega
  · obtain rfl : n = s := by omega
    rw [ChainComplex.ιTensorObj_D₁_zero_assoc, zero_comp, zero_add,
      ChainComplex.ιTensorObj_D₂_succ_assoc]
    simp only [Category.assoc, ι_crossProductX, pow_zero, one_smul]
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    exact (summand_d_apply 0 (n + 1) n h a b).trans
      ((NormalizedCubicalChain.boundary_crossProduct_zero_left R a b).trans
        (whiskerLeft_summand_apply 0 n n (zero_add n) a b).symm)
  · obtain rfl : n = r := by omega
    rw [ChainComplex.ιTensorObj_D₂_zero_assoc, zero_comp, add_zero,
      ChainComplex.ιTensorObj_D₁_succ_assoc]
    simp only [ι_crossProductX]
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    exact (summand_d_apply (n + 1) 0 n h a b).trans
      (((congrArg (NormalizedCubicalChain.boundary (X × Y) R n)
          (NormalizedCubicalChain.cast_rfl R _)).trans
        (NormalizedCubicalChain.boundary_crossProduct_zero_right R a b)).trans
        ((NormalizedCubicalChain.cast_rfl R _).symm.trans
          (whiskerRight_summand_apply n 0 n rfl a b).symm))
  · obtain rfl : n = r + s + 1 := by omega
    rw [ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc]
    simp only [Category.assoc, Preadditive.zsmul_comp, ι_crossProductX]
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
    refine (summand_d_apply (r + 1) (s + 1) (r + s + 1) h a b).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· + ·)
      (whiskerRight_summand_apply r (s + 1) (r + s + 1) (by omega) a b).symm
      (congrArg (((-1 : ℤ) ^ (r + 1)) • ·)
        (whiskerLeft_summand_apply (r + 1) s (r + s + 1) (by omega) a b).symm))
    rw [NormalizedCubicalChain.boundary_crossProduct R a b]
    refine congrArg₂ (· + ·) (NormalizedCubicalChain.cast_rfl R _).symm ?_
    norm_cast

variable (R X Y) in
/-- **The cross product of normalized cubical chains as a chain map**
`N(X) ⊗ N(Y) ⟶ N(X ⊗ Y)`, with the Koszul sign on the tensor product of complexes: it sends
`a ⊗ b` of bidegree `(p, q)` to `a × b`, and the Leibniz rule says it commutes with the
differentials. -/
def crossProductComplex :
    (normalizedCubicalChainComplex R).obj X ⊗ (normalizedCubicalChainComplex R).obj Y ⟶
      (normalizedCubicalChainComplex R).obj (X ⊗ Y) where
  f := crossProductX
  comm' := by
    rintro _ n rfl
    exact mapBifunctor.hom_ext fun p q h ↦ by
      simpa only [Category.assoc] using comm_summand n p q h

/-- On a summand of bidegree `(p, q)`, the cross product chain map is the cross product of
normalized chains followed by the reindexing `p + q = n`. -/
theorem ι_crossProductComplex_f_apply {p q n : ℕ} (h : p + q = n)
    (a : NormalizedCubicalChain X R p) (b : NormalizedCubicalChain Y R q) :
    (ιTensorObj ((normalizedCubicalChainComplex R).obj X)
        ((normalizedCubicalChainComplex R).obj Y) p q n h ≫
          (crossProductComplex R X Y).f n).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.cast R h (NormalizedCubicalChain.crossProduct X Y R p q a b) := by
  rw [crossProductComplex, ι_crossProductX]
  exact crossProductSummand_apply R X Y p q n h a b

/-- **Naturality** of the cross product chain map in both spaces. -/
theorem crossProductComplex_naturality {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    HomologicalComplex.tensorHom ((normalizedCubicalChainComplex R).map f)
        ((normalizedCubicalChainComplex R).map g) ≫ crossProductComplex R X' Y' =
      crossProductComplex R X Y ≫ (normalizedCubicalChainComplex R).map (f ⊗ₘ g) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_tensorHom_assoc]
  simp only [crossProductComplex, ι_crossProductX_assoc, ι_crossProductX]
  refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
  refine (crossProductSummand_apply R X' Y' p q n h
    (NormalizedCubicalChain.map R f.hom p a) (NormalizedCubicalChain.map R g.hom q b)).trans ?_
  refine Eq.trans ?_ (congrArg (NormalizedCubicalChain.map R (f ⊗ₘ g).hom n)
    (crossProductSummand_apply R X Y p q n h a b)).symm
  erw [NormalizedCubicalChain.map_cast, ← NormalizedCubicalChain.map_crossProduct]
  rfl

end TauCeti

end

end
