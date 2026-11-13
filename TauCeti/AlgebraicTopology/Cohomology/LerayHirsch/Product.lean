/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.Kunneth
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.Defs

/-!
# The Leray–Hirsch theorem for a product

Let `k` be a commutative ring and let `F` be a space whose homology `Hₚ(F; k)` is projective in
every degree and finitely generated in degrees `p ≤ n`. Over a field, or more generally a
commutative semisimple ring, every module is projective (`Module.projective_of_isSemisimpleRing`),
so this holds for instance for a space of finite CW type; over `ℤ` it holds when the homology of
`F` is free of finite rank, as for spheres and tori. Suppose that for every degree `p ≤ n` the
family `b p : ι p → Hᵖ(F; k)` is a basis of `Hᵖ(F; k)`; the families in degrees `p > n` do not
enter. For any space `X`, the **Leray–Hirsch map of the product** `X × F` in degree `n`,

`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, `(a_{p,i}) ↦ ∑ pr₁^* a_{p,i} ⌣ pr₂^* b_{p,i}`,

(`TopCat.lerayHirsch` of the projection `X × F ⟶ X` and the pullbacks of the classes `b p i`
along the projection `X × F ⟶ F`) is bijective (`TopCat.lerayHirsch_fst_bijective`). This is the
parameterized trivial-fibre case of the Leray–Hirsch theorem in degree `n`: every class in
`Hⁿ(X × F; k)` is uniquely a sum `∑ pr₁^* a_{p,i} ⌣ pr₂^* b_{p,i}` with `a_{p,i}` in `H^q(X; k)`
for `p + q = n`. When `Hₚ(F; k)` is finitely generated and `b p` is a basis in every degree, this
holds in all degrees, so the cohomology of `X × F` is a free graded module over the cohomology of
`X` on the pullbacks of the fibre basis. A summand indexed by `p + q = n` and `i : ι p` carries
the base degree `q`, so `q = n - p` is the base degree `n - dᵢ` of the usual statement.

The proof is the cohomology Künneth theorem `TopCat.singularCohomologyKunnethIso` for `F × X`,
whose finitely generated factor is the first one. The basis identifies
`Hᵖ(F; k) ⊗ H^q(X; k)` with `⨁_{i : ι p} H^q(X; k)`; the cross product `b × a` on `F × X` is
`pr₁^* b ⌣ pr₂^* a`, pulling back along the swap `X × F ⟶ F × X` exchanges the two projections,
and graded commutativity of the cup product contributes the sign `(-1)^(p q)`, a unit. Finally the
Künneth theorem computes cohomology from chains with coefficients in `k ⊗ k`, which the unitor
`k ≅ k ⊗ k` identifies with the chains with coefficients in `k`
(`TopCat.singularCohomologyChainCoefficientIso`, `TopCat.singularCup_precomp`).

## Main definitions and results

* `TopCat.lerayHirsch_fst_bijective`, `TopCat.lerayHirschProdEquiv`: the Leray–Hirsch theorem for
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

universe w u

namespace TopCat

variable {k : Type w} [CommRing k]

variable (X F : TopCat.{w}) (n : ℕ) {ι : ℕ → Type u} [∀ p, DecidableEq (ι p)]
  (b : ∀ p, ι p → F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)

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

variable (hb : ∀ p ≤ n, LinearIndependent k (b p) ∧ ⊤ ≤ Submodule.span k (Set.range (b p)))

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
      (TensorProduct.equivFinsuppOfBasisLeft
        (Module.Basis.mk (hb p (by omega)).1 (hb p (by omega)).2)).toLinearMap

private lemma ofKunnethSourceSummand_tmul (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    ofKunnethSourceSummand b hb p q h (b p i ⊗ₜ a) =
      ((-1 : ℤ) ^ (p * q)) • DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a := by
  have hrepr : (Module.Basis.mk (hb p (by omega)).1 (hb p (by omega)).2).repr (b p i) =
      Finsupp.single i 1 := by
    simpa using (Module.Basis.mk (hb p (by omega)).1 (hb p (by omega)).2).repr_self i
  simp [ofKunnethSourceSummand, hrepr, -Module.Basis.mk_repr]

/-- The inverse of `toKunnethSource`: the summands `ofKunnethSourceSummand`, assembled through
the direct sum `⨁_{p + q = n} Hᵖ(F; k) ⊗ H^q(X; k)` presenting the graded tensor product. -/
private def ofKunnethSource :
    (GradedObject.Monoidal.tensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :
          ModuleCat.{w} k) →ₗ[k]
      (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :=
  DirectSum.toModule k _ _ (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
      ofKunnethSourceSummand b hb pq.1.1 pq.1.2 pq.2) ∘ₗ
    (GradedObject.Monoidal.tensorObjDesc fun p q h ↦ ModuleCat.ofHom
      (DirectSum.lof k {pq : ℕ × ℕ // pq.1 + pq.2 = n} (fun pq ↦ TensorProduct k
          (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) pq.1.1)
          (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) pq.1.2))
        ⟨(p, q), h⟩)).hom

private lemma ofKunnethSource_ιTensorObj (p q : ℕ) (h : p + q = n) (i : ι p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    ofKunnethSource b hb (GradedObject.Monoidal.ιTensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
        p q n h (b p i ⊗ₜ a)) =
      ((-1 : ℤ) ^ (p * q)) • DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ a := by
  rw [ofKunnethSource, LinearMap.comp_apply, ← ConcreteCategory.comp_apply,
    GradedObject.Monoidal.ι_tensorObjDesc, ModuleCat.ofHom_apply, DirectSum.toModule_lof]
  exact ofKunnethSourceSummand_tmul b hb p q h i a

/-- `toKunnethSource` is a linear equivalence. -/
private def toKunnethSourceEquiv :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ≃ₗ[k]
      (GradedObject.Monoidal.tensorObj
        (fun p ↦ F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :
          ModuleCat.{w} k) :=
  LinearEquiv.ofLinearMap (toKunnethSource b) (ofKunnethSource b hb)
    (by
      have : ModuleCat.ofHom (toKunnethSource (X := X) (n := n) b ∘ₗ ofKunnethSource b hb) =
          𝟙 _ := by
        refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ModuleCat.hom_ext ?_
        refine TensorProduct.ext ((Module.Basis.mk (hb p (by omega)).1 (hb p (by omega)).2).ext
          fun i ↦ LinearMap.ext fun a ↦ ?_)
        simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, ModuleCat.hom_comp,
          Module.Basis.mk_apply,
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
private lemma lerayHirsch_fst_eq :
    lerayHirsch (fst X F) n (fun p i ↦ TopCat.singularCohomologyMap (snd X F) p (b p i)) =
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
      ← singularCup_naturality]
    simp only [← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp, braiding_hom_fst,
      braiding_hom_snd]
  -- Graded commutativity swaps the two factors at the cost of the sign `(-1)^(p q)`.
  have hu : 𝟙 _ ≫ (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom = 𝟙 _ := by
    simp [unitors_inv_equal]
  have hμ : (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom ≫
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom = (λ_ (𝟙_ (ModuleCat.{w} k))).hom := by
    simp [unitors_inv_equal]
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
  rw [lerayHirsch_lof, toKunnethSource_lof, hcross, hcomm, hcoeff]
  simp [smul_smul, ← mul_pow, mul_comm q p]

variable (X) [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
  (𝟙_ (ModuleCat.{w} k))).obj F)]

include hb in
/-- **The Leray–Hirsch theorem for a product**: over a commutative ring `k`, if the homology
`Hₚ(F; k)` is projective in every degree and finitely generated in degrees `p ≤ n`, for instance
over a field when `F` has finite CW type, and `b p` is a basis of `Hᵖ(F; k)` for every `p ≤ n`,
the Leray–Hirsch map
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ⟶ Hⁿ(X × F; k)`, `(a_{p,i}) ↦ ∑ pr₁^* a_{p,i} ⌣ pr₂^* b_{p,i}`,
is bijective. -/
theorem lerayHirsch_fst_bijective
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F)) :
    Function.Bijective
      (lerayHirsch (fst X F) n fun p i ↦ TopCat.singularCohomologyMap (snd X F) p (b p i)) := by
  have hσ : Function.Bijective (TopCat.singularCohomologyMap
      (R := 𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) (k := k) (M := 𝟙_ (ModuleCat.{w} k))
      (β_ X F).hom n) :=
    ((TauCeti.singularCohomologyFunctor _ k _ n).mapIso (β_ X F).op).toLinearEquiv.bijective
  rw [lerayHirsch_fst_eq]
  exact ((X ⊗ F).singularCohomologyChainCoefficientIso k (𝟙_ (ModuleCat.{w} k))
    (λ_ (𝟙_ (ModuleCat.{w} k))).symm n).toLinearEquiv.bijective.comp (hσ.comp
    ((singularCohomologyKunneth_bijective F X n hF).comp (toKunnethSourceEquiv b hb).bijective))

/-- **The Leray–Hirsch isomorphism for a product**
`⨁_{p + q = n} ⨁_{i : ι p} H^q(X; k) ≃ Hⁿ(X × F; k)`, the linear equivalence given by the
Leray–Hirsch map `TopCat.lerayHirsch` of the projection `X × F ⟶ X`. -/
def lerayHirschProdEquiv
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F)) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) ≃ₗ[k]
      (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  LinearEquiv.ofBijective
    (lerayHirsch (fst X F) n fun p i ↦ TopCat.singularCohomologyMap (snd X F) p (b p i))
    (lerayHirsch_fst_bijective X b hb hF)

@[simp]
lemma lerayHirschProdEquiv_apply
    (hF : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (a : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) :
    lerayHirschProdEquiv X b hb hF a =
      lerayHirsch (fst X F) n (fun p i ↦ TopCat.singularCohomologyMap (snd X F) p (b p i)) a :=
  (rfl)

end Bijective

end TopCat
