/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.Kunneth

/-!
# The Leray–Hirsch theorem for a product over a field

Let `k` be a field, or more generally a commutative semisimple ring, and let `F` be a space whose
homology `Hₚ(F; k)` is finitely generated in degrees `p ≤ n`, for instance a space of finite CW
type. Suppose that for every degree `p` the family `b p : ι p → Hᵖ(F; k)` is a basis of `Hᵖ(F; k)`,
so that together these form a homogeneous basis of the graded cohomology of `F`. For any space
`X`, the **Leray–Hirsch map of the product** `X × F` in degree `n`,

`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, `(a_{p,i}) ↦ ∑ pr₁^* a_{p,i} ⌣ pr₂^* b_{p,i}`,

(`TopCat.lerayHirschProd`) is bijective (`TopCat.lerayHirschProd_bijective`). This is the
parameterized trivial-fibre case of the Leray–Hirsch theorem: the cohomology of `X × F` is a free
module over the cohomology of `X` on the pullbacks of the fibre basis. A summand indexed by
`p + q = n` and `i : ι p` carries the base degree `q`, so `q = n - p` is the base degree `n - dᵢ`
of the usual statement.

The proof is the cohomology Künneth theorem `TopCat.singularCohomologyKunnethIso` for `F × X`,
whose finitely generated factor is the first one. The basis identifies
`Hᵖ(F; k) ⊗ H^q(X; k)` with `⨁_{i : ι p} H^q(X; k)`; the cross product `b × a` on `F × X` is
`pr₁^* b ⌣ pr₂^* a`, pulling back along the swap `X × F ⟶ F × X` exchanges the two projections,
and graded commutativity of the cup product contributes the sign `(-1)^(p q)`, a unit. Finally the
Künneth theorem computes cohomology from chains with coefficients in `k ⊗ k`, which the unitor
`k ≅ k ⊗ k` identifies with the chains with coefficients in `k`.

## Main definitions and results

* `TopCat.lerayHirschProd`: the Leray–Hirsch map of `X × F` in degree `n`, characterized on
  summands by `TopCat.lerayHirschProd_lof`.
* `TopCat.lerayHirschProd_bijective`, `TopCat.lerayHirschProdEquiv`: the Leray–Hirsch theorem for
  the product `X × F`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch) and Theorem 3.15 (Künneth).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomologicalComplex
  AlgebraicTopology
open scoped DirectSum

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

section Coefficients

/-- The isomorphism `Hⁿ(Y; k ⊗ k, k) ≅ Hⁿ(Y; k, k)` induced by the chain coefficient isomorphism
`λ⁻¹ : k ≅ k ⊗ k`. -/
private def tensorUnitCoeffIso (Y : TopCat.{w}) (n : ℕ) :
    Y.singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n ≅
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  (homologyFunctor _ _ n).mapIso
    ((TauCeti.ChainComplex.linearYonedaFunctor k (𝟙_ (ModuleCat.{w} k))).mapIso
      (((SSet.chainComplexFunctor (ModuleCat.{w} k)).mapIso
        (λ_ (𝟙_ (ModuleCat.{w} k))).symm).app (toSSet.obj Y)).op)

/-- The cup product with chain coefficients `k`, along the unitor `k ≅ k ⊗ k`, is the cup product
with chain coefficients `k ⊗ k` followed by the coefficient isomorphism. -/
private lemma singularCup_tensorUnit_eq (Y : TopCat.{w}) {p q n : ℕ} (h : p + q = n)
    (a : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    Y.singularCup k (λ_ _).inv (λ_ _).hom p q n h a b =
      (tensorUnitCoeffIso Y n).hom (Y.singularCup k (𝟙 _) (λ_ _).hom p q n h a b) := by
  have h₁ := TauCeti.alexanderWhitneyDiagonal_def (X := Y) (λ_ (𝟙_ (ModuleCat.{w} k))).inv
  have h₂ := TauCeti.alexanderWhitneyDiagonal_def (X := Y)
    (𝟙 (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)))
  rw [(SSet.chainComplexFunctor (ModuleCat.{w} k)).map_id, NatTrans.id_app,
    Category.id_comp] at h₂
  rw [TauCeti.singularCup_def, TauCeti.singularCup_def, h₁, h₂,
    TauCeti.ChainComplex.cup_precomp]
  rfl

end Coefficients

variable (X F : TopCat.{w}) (n : ℕ) {ι : ℕ → Type w} [∀ p, DecidableEq (ι p)]
  (b : ∀ p, Module.Basis (ι p) k
    (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p))

/-- **The Leray–Hirsch map of the product** `X × F` in degree `n`,
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, sending `a` in the summand indexed by
`p + q = n` and `i : ι p` to `pr₁^* a ⌣ pr₂^* (b p i)`. -/
def lerayHirschProd :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) →ₗ[k]
      (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  DirectSum.toModule k _ _ fun j ↦
    ((X ⊗ F).singularCup k (λ_ _).inv (λ_ _).hom j.1.1.2 j.1.1.1 n
        (by rw [add_comm]; exact j.1.2)).flip
      (TopCat.singularCohomologyMap (snd X F) j.1.1.1 (b j.1.1.1 j.2)) ∘ₗ
      (TopCat.singularCohomologyMap (fst X F) j.1.1.2).hom

/-- The Leray–Hirsch map of `X × F` sends `a` in the summand indexed by `p + q = n` and `i : ι p`
to `pr₁^* a ⌣ pr₂^* (b p i)`. -/
@[simp]
lemma lerayHirschProd_lof (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschProd X F n b (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a) =
      (X ⊗ F).singularCup k (λ_ _).inv (λ_ _).hom q p n (by omega)
        (TopCat.singularCohomologyMap (fst X F) q a)
        (TopCat.singularCohomologyMap (snd X F) p (b p i)) := by
  simp [lerayHirschProd]

section Bijective

variable {X F n}

/-- The basis `b` identifies the source of the Leray–Hirsch map with the source of the Künneth map
of `F × X`: the summand indexed by `p + q = n` and `i : ι p` is sent by
`a ↦ b p i ⊗ (-1)^(p q) a`. -/
private def toKunnethSource :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) →ₗ[k]
      (GradedObject.Monoidal.tensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :
          ModuleCat.{w} k) :=
  DirectSum.toModule k _ _ fun j ↦
    (GradedObject.Monoidal.ιTensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
        j.1.1.1 j.1.1.2 n j.1.2).hom ∘ₗ
      (((-1 : ℤ) ^ (j.1.1.1 * j.1.1.2)) • TensorProduct.mk k _ _ (b j.1.1.1 j.2))

private lemma toKunnethSource_lof (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    toKunnethSource b (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a) =
      GradedObject.Monoidal.ιTensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
        p q n h (b p i ⊗ₜ (((-1 : ℤ) ^ (p * q)) • a)) := by
  simp [toKunnethSource]

/-- The summand of the inverse of `toKunnethSource` indexed by `p + q = n`:
`f ⊗ a ↦ ∑ᵢ (-1)^(p q) fᵢ a`, where `fᵢ` are the coordinates of `f` in the basis `b p`. -/
private def ofKunnethSourceSummand (p q : ℕ) (h : p + q = n) :
    TensorProduct k (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) →ₗ[k]
      (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :=
  ((-1 : ℤ) ^ (p * q)) •
    (Finsupp.lsum k fun i ↦ DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩) ∘ₗ
      (TensorProduct.finsuppScalarLeft k _ (ι p)).toLinearMap ∘ₗ
      TensorProduct.map (b p).repr.toLinearMap LinearMap.id

private lemma ofKunnethSourceSummand_tmul (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    ofKunnethSourceSummand b p q h (b p i ⊗ₜ a) =
      ((-1 : ℤ) ^ (p * q)) • DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a := by
  simp [ofKunnethSourceSummand, TensorProduct.finsuppScalarLeft_apply_tmul]

/-- The inverse of `toKunnethSource`. -/
private def ofKunnethSource :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n ⟶
      ModuleCat.of k (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :=
  GradedObject.Monoidal.tensorObjDesc fun p q h ↦ ModuleCat.ofHom (ofKunnethSourceSummand b p q h)

private lemma ofKunnethSource_ιTensorObj (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    ofKunnethSource b (GradedObject.Monoidal.ιTensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
        p q n h (b p i ⊗ₜ a)) =
      ((-1 : ℤ) ^ (p * q)) • DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a := by
  rw [ofKunnethSource, ← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom (GradedObject.Monoidal.ι_tensorObjDesc _ p q h) _).trans
    (ofKunnethSourceSummand_tmul b p q h i a)

private lemma neg_one_pow_smul_neg_one_pow_smul {M : Type*} [AddCommGroup M] (m : ℕ) (x : M) :
    ((-1 : ℤ) ^ m) • ((-1 : ℤ) ^ m) • x = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- `toKunnethSource` is a linear equivalence. -/
private def toKunnethSourceEquiv :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ≃ₗ[k]
      (GradedObject.Monoidal.tensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :
          ModuleCat.{w} k) :=
  LinearEquiv.ofLinearMap (toKunnethSource b) (ofKunnethSource b).hom
    (by
      have : ofKunnethSource (X := X) (n := n) b ≫ ModuleCat.ofHom (toKunnethSource b) = 𝟙 _ := by
        refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ModuleCat.hom_ext ?_
        refine TensorProduct.ext ((b p).ext fun i ↦ LinearMap.ext fun a ↦ ?_)
        simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, ModuleCat.hom_comp,
          ModuleCat.hom_ofHom, LinearMap.comp_apply, Category.comp_id]
        rw [ofKunnethSource_ιTensorObj, map_zsmul, toKunnethSource_lof, ← map_zsmul,
          TensorProduct.tmul_smul, neg_one_pow_smul_neg_one_pow_smul]
      exact congrArg ModuleCat.Hom.hom this)
    (by
      refine DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.id_comp]
      rw [toKunnethSource_lof, TensorProduct.tmul_smul, map_zsmul, map_zsmul,
        ofKunnethSource_ιTensorObj, neg_one_pow_smul_neg_one_pow_smul])

/-- The Leray–Hirsch map of `X × F` is the Künneth map of `F × X`, preceded by the basis
identification `toKunnethSource` and followed by the swap `X × F ≅ F × X` and the coefficient
isomorphism `k ⊗ k ≅ k`. -/
private lemma lerayHirschProd_eq :
    lerayHirschProd X F n b =
      (tensorUnitCoeffIso (X ⊗ F) n).hom.hom ∘ₗ
        (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) (k := k)
          (M := 𝟙_ (ModuleCat.{w} k)) (β_ X F).hom n).hom ∘ₗ
        (singularCohomologyKunneth F X (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom n).hom ∘ₗ toKunnethSource b := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  have hu : 𝟙 _ ≫ (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom = 𝟙 _ := by
    rw [Category.id_comp, braiding_tensorUnit_left, ← unitors_inv_equal, Iso.hom_inv_id]
  have hμ : (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom ≫
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom = (λ_ (𝟙_ (ModuleCat.{w} k))).hom := by
    rw [braiding_tensorUnit_left, ← unitors_inv_equal, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  simp only [LinearMap.comp_apply]
  rw [lerayHirschProd_lof X F n b p q h i a, toKunnethSource_lof b p q h i a]
  have hK := singularCohomologyKunneth_ιTensorObj_tmul F X (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h
    (b p i) (((-1 : ℤ) ^ (p * q)) • a)
  rw [TauCeti.singularCross_eq_singularCup] at hK
  rw [hK, map_zsmul, map_zsmul, map_zsmul, ← singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp,
    ← singularCohomologyMap_comp, braiding_hom_fst, braiding_hom_snd,
    TopCat.singularCup_gradedComm (X ⊗ F) k hu hμ (by omega), map_zsmul, map_zsmul,
    ← singularCup_tensorUnit_eq, mul_comm q p, neg_one_pow_smul_neg_one_pow_smul]

variable (X) [IsSemisimpleRing k]

/-- **The Leray–Hirsch theorem for a product**: over a commutative semisimple ring `k`, for
instance a field, if the homology `Hₚ(F; k)` is finitely generated in degrees `p ≤ n` and `b p` is
a basis of `Hᵖ(F; k)` for every `p`, the Leray–Hirsch map
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, `(a_{p,i}) ↦ ∑ pr₁^* a_{p,i} ⌣ pr₂^* b_{p,i}`,
is bijective. -/
theorem lerayHirschProd_bijective
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F)) :
    Function.Bijective (lerayHirschProd X F n b) := by
  have hσ : Function.Bijective (TopCat.singularCohomologyMap
      (R := 𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) (k := k) (M := 𝟙_ (ModuleCat.{w} k))
      (β_ X F).hom n) :=
    ((TauCeti.singularCohomologyFunctor _ k _ n).mapIso (β_ X F).op).toLinearEquiv.bijective
  rw [lerayHirschProd_eq]
  exact (tensorUnitCoeffIso (X ⊗ F) n).toLinearEquiv.bijective.comp (hσ.comp
    ((singularCohomologyKunneth_bijective F X n hF).comp (toKunnethSourceEquiv b).bijective))

/-- **The Leray–Hirsch isomorphism for a product**
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ≃ Hⁿ(X × F; k)`, the linear equivalence given by the
Leray–Hirsch map `TopCat.lerayHirschProd`. -/
def lerayHirschProdEquiv
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F)) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ≃ₗ[k]
      (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  LinearEquiv.ofBijective (lerayHirschProd X F n b) (lerayHirschProd_bijective X b hF)

@[simp]
lemma lerayHirschProdEquiv_apply
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (a : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :
    lerayHirschProdEquiv X b hF a = lerayHirschProd X F n b a :=
  (rfl)

end Bijective

end TopCat
