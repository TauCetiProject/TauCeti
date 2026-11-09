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
parameterized trivial-fibre case of the Leray–Hirsch theorem in degree `n`: every class in
`Hⁿ(X × F; k)` is uniquely a sum `∑ pr₁^* a_{p,i} ⌣ pr₂^* b_{p,i}` with `a_{p,i}` in `H^q(X; k)`
for `p + q = n`. When `Hₚ(F; k)` is finitely generated in every degree, this holds in all degrees,
so the cohomology of `X × F` is a free graded module over the cohomology of `X` on the pullbacks
of the fibre basis. A summand indexed by `p + q = n` and `i : ι p` carries the base degree `q`, so
`q = n - p` is the base degree `n - dᵢ` of the usual statement.

The proof is the cohomology Künneth theorem `TopCat.singularCohomologyKunnethIso` for `F × X`,
whose finitely generated factor is the first one. The basis identifies
`Hᵖ(F; k) ⊗ H^q(X; k)` with `⨁_{i : ι p} H^q(X; k)`; the cross product `b × a` on `F × X` is
`pr₁^* b ⌣ pr₂^* a`, pulling back along the swap `X × F ⟶ F × X` exchanges the two projections,
and graded commutativity of the cup product contributes the sign `(-1)^(p q)`, a unit. Finally the
Künneth theorem computes cohomology from chains with coefficients in `k ⊗ k`, which the unitor
`k ≅ k ⊗ k` identifies with the chains with coefficients in `k`
(`TopCat.singularCohomologyChainCoefficientIso`, `TopCat.singularCup_precomp`).

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
      (TensorProduct.equivFinsuppOfBasisLeft (b p)).toLinearMap

private lemma ofKunnethSourceSummand_tmul (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    ofKunnethSourceSummand b p q h (b p i ⊗ₜ a) =
      ((-1 : ℤ) ^ (p * q)) • DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a := by
  simp [ofKunnethSourceSummand]

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
        rw [ofKunnethSource_ιTensorObj, map_zsmul, toKunnethSource_lof]
        simp [TensorProduct.tmul_smul, smul_smul, ← mul_pow]
      exact congrArg ModuleCat.Hom.hom this)
    (by
      refine DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.id_comp]
      rw [toKunnethSource_lof, ofKunnethSource_ιTensorObj]
      simp [smul_smul, ← mul_pow])

/-- The Leray–Hirsch map of `X × F` is the Künneth map of `F × X`, preceded by the basis
identification `toKunnethSource` and followed by the swap `X × F ≅ F × X` and the coefficient
isomorphism `k ⊗ k ≅ k`. -/
private lemma lerayHirschProd_eq :
    lerayHirschProd X F n b =
      ((X ⊗ F).singularCohomologyChainCoefficientIso k (𝟙_ (ModuleCat.{w} k))
          (λ_ (𝟙_ (ModuleCat.{w} k))).symm n).hom.hom ∘ₗ
        (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) (k := k)
          (M := 𝟙_ (ModuleCat.{w} k)) (β_ X F).hom n).hom ∘ₗ
        (singularCohomologyKunneth F X (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom n).hom ∘ₗ toKunnethSource b := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨p, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  -- The Künneth map sends `b p i ⊗ a'` to the cross product `pr₁^* (b p i) ⌣ pr₂^* a'` on `F × X`,
  -- whose pullback along the swap is `pr₂^* (b p i) ⌣ pr₁^* a'` on `X × F`.
  have hcross (a' : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
      TopCat.singularCohomologyMap (β_ X F).hom n
          (singularCohomologyKunneth F X (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
            (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
            (GradedObject.Monoidal.ιTensorObj
              (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
              (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
              p q n h (b p i ⊗ₜ a'))) =
        (X ⊗ F).singularCup k (𝟙 _) (λ_ _).hom p q n h
          (TopCat.singularCohomologyMap (snd X F) p (b p i))
          (TopCat.singularCohomologyMap (fst X F) q a') := by
    rw [singularCohomologyKunneth_ιTensorObj_tmul, TauCeti.singularCross_eq_singularCup,
      ← singularCup_naturality, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← singularCohomologyMap_comp, ← singularCohomologyMap_comp, braiding_hom_fst,
      braiding_hom_snd]
  -- Graded commutativity swaps the two factors at the cost of the sign `(-1)^(p q)`.
  have hu : 𝟙 _ ≫ (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom = 𝟙 _ := by
    rw [Category.id_comp, braiding_tensorUnit_left, ← unitors_inv_equal, Iso.hom_inv_id]
  have hμ : (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom ≫
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom = (λ_ (𝟙_ (ModuleCat.{w} k))).hom := by
    rw [braiding_tensorUnit_left, ← unitors_inv_equal, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hcomm (a' : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :=
    (X ⊗ F).singularCup_gradedComm k hu hμ (by omega : q + p = n)
      (TopCat.singularCohomologyMap (fst X F) q a')
      (TopCat.singularCohomologyMap (snd X F) p (b p i))
  -- The cup product along the unitor is the cup product with coefficients `k ⊗ k`, transported.
  have hcoeff := (X ⊗ F).singularCup_precomp k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (𝟙 _)
    (λ_ (𝟙_ (ModuleCat.{w} k))).hom q p n (by omega)
    (TopCat.singularCohomologyMap (fst X F) q a)
    (TopCat.singularCohomologyMap (snd X F) p (b p i))
  rw [Category.comp_id] at hcoeff
  simp only [LinearMap.comp_apply, singularCohomologyChainCoefficientIso_hom, Iso.symm_hom]
  rw [lerayHirschProd_lof, toKunnethSource_lof, hcross, hcomm, hcoeff]
  simp [smul_smul, ← mul_pow, mul_comm q p]

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
  exact ((X ⊗ F).singularCohomologyChainCoefficientIso k (𝟙_ (ModuleCat.{w} k))
    (λ_ (𝟙_ (ModuleCat.{w} k))).symm n).toLinearEquiv.bijective.comp (hσ.comp
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
