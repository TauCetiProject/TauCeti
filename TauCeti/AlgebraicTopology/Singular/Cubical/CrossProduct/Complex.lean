/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
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

* `TauCeti.cubicalCrossProduct R X Y`: the cross product as a chain map
  `N(X) ⊗ N(Y) ⟶ N(X ⊗ Y)`.
* `TauCeti.cubicalCrossProduct_naturality`: naturality in both spaces.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits

universe u

namespace TauCeti

variable (R : Type u) [CommRing R] (X Y : TopCat.{u})

/-- The cross product of normalized chains of degrees `p` and `q`, as a map out of the tensor
product of modules to the chains of degree `n = p + q` of the product space. -/
def cubicalCrossProductSummand (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of R (NormalizedCubicalChain X R p) ⊗ ModuleCat.of R (NormalizedCubicalChain Y R q) ⟶
      ModuleCat.of R (NormalizedCubicalChain (X × Y) R n) :=
  ModuleCat.ofHom (TensorProduct.lift
    (LinearMap.compr₂ (NormalizedCubicalChain.crossProduct X Y R p q)
      (NormalizedCubicalChain.cast R h)))

/-- The cross product map of a summand, evaluated on a pure tensor `a ⊗ b` of normalized chains of
degrees `p` and `q`, is their cross product reindexed along `p + q = n`. -/
@[simp]
theorem cubicalCrossProductSummand_apply (p q n : ℕ) (h : p + q = n)
    (a : NormalizedCubicalChain X R p) (b : NormalizedCubicalChain Y R q) :
    (cubicalCrossProductSummand R X Y p q n h).hom (a ⊗ₜ b) =
      NormalizedCubicalChain.cast R h (NormalizedCubicalChain.crossProduct X Y R p q a b) := by
  rw [cubicalCrossProductSummand, ModuleCat.hom_ofHom]
  exact TensorProduct.lift.tmul a b

variable {R X Y}

/-- The degree-`n` component of the cross product chain map: the cross product on each summand
of bidegree `(p, q)` with `p + q = n`. -/
private def cubicalCrossProductX (n : ℕ) :
    ((normalizedCubicalChainComplex R).obj X ⊗ (normalizedCubicalChainComplex R).obj Y).X n ⟶
      ((normalizedCubicalChainComplex R).obj (X ⊗ Y)).X n :=
  mapBifunctorDesc fun p q h ↦ cubicalCrossProductSummand R X Y p q n h

/-- The component of the cross product chain map restricted to a summand is the cross product of
that bidegree. -/
@[reassoc]
private theorem ι_cubicalCrossProductX {p q n : ℕ} (h : p + q = n) :
    ιTensorObj ((normalizedCubicalChainComplex R).obj X)
        ((normalizedCubicalChainComplex R).obj Y) p q n h ≫ cubicalCrossProductX n =
      cubicalCrossProductSummand R X Y p q n h :=
  ι_mapBifunctorDesc _ _ _ _

/-- Whiskering the differential of the first factor with a chain of the second. -/
private theorem whiskerRight_d_apply (r s : ℕ) (a : NormalizedCubicalChain X R (r + 1))
    (b : NormalizedCubicalChain Y R s) :
    (((normalizedCubicalChainComplex R).obj X).d (r + 1) r ▷
        ((normalizedCubicalChainComplex R).obj Y).X s).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.boundary X R r a ⊗ₜ[R] b := by
  have h := ModuleCat.MonoidalCategory.whiskerRight_apply
    (((normalizedCubicalChainComplex R).obj X).d (r + 1) r)
    (((normalizedCubicalChainComplex R).obj Y).X s) a b
  rw [normalizedCubicalChainComplex_obj_d_apply] at h
  exact h

/-- Whiskering a chain of the first factor with the differential of the second. -/
private theorem whiskerLeft_d_apply (r s : ℕ) (a : NormalizedCubicalChain X R r)
    (b : NormalizedCubicalChain Y R (s + 1)) :
    (((normalizedCubicalChainComplex R).obj X).X r ◁
        ((normalizedCubicalChainComplex R).obj Y).d (s + 1) s).hom (a ⊗ₜ[R] b) =
      a ⊗ₜ[R] NormalizedCubicalChain.boundary Y R s b := by
  have h := ModuleCat.MonoidalCategory.whiskerLeft_apply
    (((normalizedCubicalChainComplex R).obj X).X r)
    (((normalizedCubicalChainComplex R).obj Y).d (s + 1) s) a b
  rw [normalizedCubicalChainComplex_obj_d_apply] at h
  exact h

/-- The cross product of a summand, followed by the differential. -/
private theorem summand_d_apply (p q n : ℕ) (h : p + q = n + 1)
    (a : NormalizedCubicalChain X R p) (b : NormalizedCubicalChain Y R q) :
    (cubicalCrossProductSummand R X Y p q (n + 1) h ≫
        ((normalizedCubicalChainComplex R).obj (X ⊗ Y)).d (n + 1) n).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.boundary (X × Y) R n
        (NormalizedCubicalChain.cast R h (NormalizedCubicalChain.crossProduct X Y R p q a b)) :=
  (normalizedCubicalChainComplex_obj_d_apply (X ⊗ Y) n _).trans
    (congrArg _ (cubicalCrossProductSummand_apply R X Y p q (n + 1) h a b))

/-- The first part of the differential of the tensor product, then the cross product. -/
private theorem whiskerRight_summand_apply (r s n : ℕ) (h : r + s = n)
    (a : NormalizedCubicalChain X R (r + 1)) (b : NormalizedCubicalChain Y R s) :
    (((normalizedCubicalChainComplex R).obj X).d (r + 1) r ▷
          ((normalizedCubicalChainComplex R).obj Y).X s ≫
            cubicalCrossProductSummand R X Y r s n h).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.cast R h
        (NormalizedCubicalChain.crossProduct X Y R r s (NormalizedCubicalChain.boundary X R r a)
          b) :=
  (congrArg (cubicalCrossProductSummand R X Y r s n h).hom (whiskerRight_d_apply r s a b)).trans
    (cubicalCrossProductSummand_apply R X Y r s n h _ b)

/-- The second part of the differential of the tensor product, then the cross product. -/
private theorem whiskerLeft_summand_apply (r s n : ℕ) (h : r + s = n)
    (a : NormalizedCubicalChain X R r) (b : NormalizedCubicalChain Y R (s + 1)) :
    (((normalizedCubicalChainComplex R).obj X).X r ◁
          ((normalizedCubicalChainComplex R).obj Y).d (s + 1) s ≫
            cubicalCrossProductSummand R X Y r s n h).hom (a ⊗ₜ[R] b) =
      NormalizedCubicalChain.cast R h
        (NormalizedCubicalChain.crossProduct X Y R r s a
          (NormalizedCubicalChain.boundary Y R s b)) :=
  (congrArg (cubicalCrossProductSummand R X Y r s n h).hom (whiskerLeft_d_apply r s a b)).trans
    (cubicalCrossProductSummand_apply R X Y r s n h a _)

/-- The cross product is compatible with the differentials on every summand.  The differential of
the tensor product is `D₁ + D₂`, the differential of the first factor and the signed differential
of the second, each vanishing when the factor it differentiates has degree `0`.  The four cases of
bidegree `(p, q)` are then the Leibniz rules `boundary_crossProduct_zero_left`,
`boundary_crossProduct_zero_right` and `boundary_crossProduct`; the case `(0, 0)` is impossible in
positive total degree. -/
private theorem comm_summand (n p q : ℕ) (h : p + q = n + 1) :
    ιTensorObj ((normalizedCubicalChainComplex R).obj X)
        ((normalizedCubicalChainComplex R).obj Y) p q (n + 1) h ≫ cubicalCrossProductX (n + 1) ≫
          ((normalizedCubicalChainComplex R).obj (X ⊗ Y)).d (n + 1) n =
      ιTensorObj ((normalizedCubicalChainComplex R).obj X)
          ((normalizedCubicalChainComplex R).obj Y) p q (n + 1) h ≫
        ((normalizedCubicalChainComplex R).obj X ⊗
          (normalizedCubicalChainComplex R).obj Y).d (n + 1) n ≫ cubicalCrossProductX n := by
  have hd : ((normalizedCubicalChainComplex R).obj X ⊗
        (normalizedCubicalChainComplex R).obj Y).d (n + 1) n =
      mapBifunctor.D₁ _ _ (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ _ _ (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [ι_cubicalCrossProductX_assoc, hd, Preadditive.add_comp, Preadditive.comp_add]
  rcases p with _ | r <;> rcases q with _ | s
  · omega -- bidegree `(0, 0)` has total degree `0`, not `n + 1`
  · -- bidegree `(0, s + 1)`: only `D₂` contributes, by `boundary_crossProduct_zero_left`
    obtain rfl : n = s := by omega
    rw [ChainComplex.ιTensorObj_D₁_zero_assoc, zero_comp, zero_add,
      ChainComplex.ιTensorObj_D₂_succ_assoc]
    simp only [Category.assoc, ι_cubicalCrossProductX, pow_zero, one_smul]
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    exact (summand_d_apply 0 (n + 1) n h a b).trans
      ((NormalizedCubicalChain.boundary_crossProduct_zero_left R a b).trans
        (whiskerLeft_summand_apply 0 n n (zero_add n) a b).symm)
  · -- bidegree `(r + 1, 0)`: only `D₁` contributes, by `boundary_crossProduct_zero_right`;
    -- `cast_rfl` removes the reindexing `r + 0 = r` on both sides
    obtain rfl : n = r := by omega
    rw [ChainComplex.ιTensorObj_D₂_zero_assoc, zero_comp, add_zero,
      ChainComplex.ιTensorObj_D₁_succ_assoc]
    simp only [ι_cubicalCrossProductX]
    refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
    exact (summand_d_apply (n + 1) 0 n h a b).trans
      (((congrArg (NormalizedCubicalChain.boundary (X × Y) R n)
          (NormalizedCubicalChain.cast_rfl R _)).trans
        (NormalizedCubicalChain.boundary_crossProduct_zero_right R a b)).trans
        ((NormalizedCubicalChain.cast_rfl R _).symm.trans
          (whiskerRight_summand_apply n 0 n rfl a b).symm))
  · -- bidegree `(r + 1, s + 1)`: both parts contribute, by `boundary_crossProduct`; the final
    -- `norm_cast` identifies the integer sign `(-1) ^ (r + 1)` of the tensor product with the
    -- sign in the ring `R`
    obtain rfl : n = r + s + 1 := by omega
    rw [ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc]
    simp only [Category.assoc, Preadditive.zsmul_comp, ι_cubicalCrossProductX]
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
differentials.  It is the cubical counterpart of the shuffle map `TopCat.shuffle`. -/
def cubicalCrossProduct :
    (normalizedCubicalChainComplex R).obj X ⊗ (normalizedCubicalChainComplex R).obj Y ⟶
      (normalizedCubicalChainComplex R).obj (X ⊗ Y) where
  f := cubicalCrossProductX
  comm' := by
    rintro _ n rfl
    exact mapBifunctor.hom_ext fun p q h ↦ by
      simpa only [Category.assoc] using comm_summand n p q h

/-- On a summand of bidegree `(p, q)`, the cross product chain map is the cross product of
normalized chains followed by the reindexing `p + q = n`. -/
@[reassoc (attr := simp)]
theorem ι_cubicalCrossProduct_f {p q n : ℕ} (h : p + q = n) :
    ιTensorObj ((normalizedCubicalChainComplex R).obj X)
        ((normalizedCubicalChainComplex R).obj Y) p q n h ≫ (cubicalCrossProduct R X Y).f n =
      cubicalCrossProductSummand R X Y p q n h :=
  ι_cubicalCrossProductX h

/-- **Naturality** of the cross product chain map in both spaces. -/
@[reassoc]
theorem cubicalCrossProduct_naturality {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((normalizedCubicalChainComplex R).map f ⊗ₘ (normalizedCubicalChainComplex R).map g) ≫
        cubicalCrossProduct R X' Y' =
      cubicalCrossProduct R X Y ≫ (normalizedCubicalChainComplex R).map (f ⊗ₘ g) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.tensorHom_eq_mapBifunctorMap, HomologicalComplex.ι_tensorHom_assoc,
    ι_cubicalCrossProduct_f, ι_cubicalCrossProduct_f_assoc]
  refine ModuleCat.hom_ext (TensorProduct.ext' fun a b ↦ ?_)
  have h₁ := cubicalCrossProductSummand_apply R X' Y' p q n h
    (((normalizedCubicalChainComplex R).map f).f p a)
    (((normalizedCubicalChainComplex R).map g).f q b)
  have hf : (((normalizedCubicalChainComplex R).map f).f p) a =
      NormalizedCubicalChain.map R f.hom p a := normalizedCubicalChainComplex_map_f_apply f p a
  have hg : (((normalizedCubicalChainComplex R).map g).f q) b =
      NormalizedCubicalChain.map R g.hom q b := normalizedCubicalChainComplex_map_f_apply g q b
  rw [hf, hg] at h₁
  have h₂ : (((normalizedCubicalChainComplex R).map (f ⊗ₘ g)).f n)
      ((cubicalCrossProductSummand R X Y p q n h).hom (a ⊗ₜ[R] b)) =
      NormalizedCubicalChain.map R (f ⊗ₘ g).hom n
        ((cubicalCrossProductSummand R X Y p q n h).hom (a ⊗ₜ[R] b)) :=
    normalizedCubicalChainComplex_map_f_apply (f ⊗ₘ g) n _
  -- the map underlying `f ⊗ₘ g` is the product map (`TopCat.tensor_apply`)
  have hprod : (f ⊗ₘ g).hom = f.hom.prodMap g.hom :=
    ContinuousMap.ext fun p ↦ TopCat.tensor_apply f g p
  rw [hprod] at h₂
  exact h₁.trans ((congrArg (NormalizedCubicalChain.cast R h)
    (NormalizedCubicalChain.map_crossProduct (R := R) f.hom g.hom a b).symm).trans
    ((NormalizedCubicalChain.map_cast (R := R) (f.hom.prodMap g.hom) h _).symm.trans
      ((congrArg (NormalizedCubicalChain.map R (f.hom.prodMap g.hom) n)
        (cubicalCrossProductSummand_apply R X Y p q n h a b)).symm.trans h₂.symm)))

end TauCeti

end

end
