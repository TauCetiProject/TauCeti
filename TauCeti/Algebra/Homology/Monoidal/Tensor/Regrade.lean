/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.Algebra.Homology.ComplexShape.Signs
public import TauCeti.Algebra.Homology.Embedding.Regrade
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Symmetry
import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# Regrading tensor products of chain complexes

For an integer `n`, a chain complex `K` indexed by `ℤ` is regraded into the cochain complex
`K^k = K_(n-k)` with the same differential (`ChainComplex.regradeEquivalence`). This file compares
the regrading of a tensor product with the tensor product of the regradings: for chain complexes
`K`, `L` and integers `n₁`, `n₂`, the tensor product of the regradings of `K` by `n₁` and of `L` by
`n₂` is isomorphic to the regrading of `K ⊗ L` by `n₁ + n₂` (`ChainComplex.regradeTensorIso`).
Both complexes have the same summands `K_(n₁ - a) ⊗ L_(n₂ - b)` in degree `k = a + b`, but they
are not equal: the Koszul sign of the
second factor's differential is `(-1)^p` for `x ∈ K_p` in `K ⊗ L` and `(-1)^a = (-1)^(n₁ - p)` in
the tensor product of the regradings. The isomorphism is the identity on summands twisted by the
sign `(-1)^(n₁ q)` on `K_p ⊗ L_q`, which depends on the degree of the second factor.

This is the sign identity that makes the cohomological regrading of a degree-shifting product an
actual cochain-level product. A family of maps `K_p ⊗ L_q → M_(p + q + n₀ - n₁ - n₂)` commuting
with the differentials of `K ⊗ L` and `M` is a morphism from the regrading of `K ⊗ L` by
`n₁ + n₂` to the regrading of `M` by `n₀`. Precomposing it with `ChainComplex.regradeTensorHom`
gives a morphism of cochain complexes out of the tensor product of the regradings of `K` by `n₁`
and `L` by `n₂`, of degree zero, whose Leibniz rule carries the
cohomological sign `(-1)^a`. For the pair-of-pants product `CF_i ⊗ CF_j → CF_(i+j-n)` on Floer
complexes of a symplectic manifold of dimension `2n` this is the passage to the degree-zero
product on `C^k = CF_(n-k)`, with `n₁ = n₂ = n₀ = n`.

Over a braided coefficient category the comparison also relates the two interchanges of factors
(`HomologicalComplex.tensorBraiding`): that of `K ⊗ L`, with the Koszul sign `(-1)^(p q)` of the
chain degrees, and that of the tensor product of the regradings, with the Koszul sign `(-1)^(a b)`
of the cochain degrees `a = n₁ - p`, `b = n₂ - q`. The two agree up to the global sign
`(-1)^(n₁ n₂)` (`ChainComplex.regradeTensorHom_comp_restrictionMap_tensorBraiding`), since
`a b + n₂ (n₁ - a) ≡ p q + n₁ q + n₁ n₂` modulo `2`. Consequently a chain-level product on `K`
which is graded commutative up to a sign `ε` for the raw degrees regrades to a degree-zero product
which is graded commutative up to `(-1)^n ε` for the cochain degrees
(`ChainComplex.tensorBraiding_hom_comp_regradeTensorHom_comp_restrictionMap`). This is the
conversion of the input-exchange sign of the pair-of-pants product between the raw grading of
Floer complexes and the cohomological grading in which graded commutativity reads `(-1)^(a b)`.

## Main definitions

* `ChainComplex.regradeTensorSummand`: the component of the comparison on one summand.
* `ChainComplex.regradeTensorHom`: the comparison morphism from the tensor product of the
  regradings to the regrading of the tensor product.
* `ChainComplex.regradeTensorIso`: the comparison morphism as an isomorphism between the tensor
  product of the regradings of `K` by `n₁` and `L` by `n₂` and the regrading of `K ⊗ L` by
  `n₁ + n₂`.

## Main results

* `ChainComplex.ι_regradeTensorHom_f`, `ChainComplex.ι_regradeTensorIso_inv_f`: the components of
  the isomorphism, whose `hom` is `ChainComplex.regradeTensorHom`, and of its inverse on summands.
* `ChainComplex.regradeTensorHom_naturality`, `ChainComplex.regradeTensorIso_inv_naturality`: the
  comparison is natural in both complexes.
* `ChainComplex.regradeTensorHom_associativity`: the comparison is compatible with the associators
  of chain and cochain complexes, after identifying the regradings by `(n₁ + n₂) + n₃` and
  `n₁ + (n₂ + n₃)` through `ChainComplex.regradeIsoOfEq`. On the summand `K_p ⊗ L_q ⊗ M_r` both
  composites carry the sign `(-1)^(n₁ q + n₁ r + n₂ r)`, so no correcting sign is needed.
* `ChainComplex.regradeTensorHom_comp_restrictionMap_tensorBraiding`,
  `ChainComplex.regradeTensorHom_comp_restrictionMap_tensorBraiding_self`: the comparison
  intertwines the interchanges of factors of the raw and of the regraded complexes up to the sign
  `(-1)^(n₁ n₂)`, which is `(-1)^n` for `n₁ = n₂ = n`.
* `ChainComplex.tensorBraiding_hom_comp_regradeTensorHom_comp_restrictionMap`: a product which is
  graded commutative up to `ε` for the raw degrees regrades to one which is graded commutative up
  to `(-1)^n ε` for the cochain degrees.

The tensor product of the regradings exists whenever `K ⊗ L` does, since their summands agree;
this is an instance. The tensor signs on `ComplexShape.down ℤ` that define `K ⊗ L` are
`ComplexShape.instTensorSignsDownInt`.

## References

* S. Piunikhin, D. Salamon, M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, Publ. Newton Inst. 8 (1996), for the cohomological regrading of Floer complexes and
  of their pair-of-pants product.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace ChainComplex

open HomologicalComplex ComplexShape

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  (n₁ n₂ : ℤ) (K L : ChainComplex C ℤ)

/-- The summands of the tensor product of the regradings of `K` by `n₁` and of `L` by `n₂` in
degree `k` are the summands of `K ⊗ L` in degree `n₁ + n₂ - k`, so the tensor product of the
regradings exists when `K ⊗ L` does. -/
instance [K.HasTensor L] :
    (K.restriction (embeddingUpIntDownIntSub n₁)).HasTensor
      (L.restriction (embeddingUpIntDownIntSub n₂)) := fun k ↦
  hasCoproduct_of_equiv_of_iso
    (f := ((((curriedTensor C).mapBifunctorHomologicalComplex (down ℤ) (down ℤ)).obj K).obj
      L).toGradedObject.mapObjFun (π (down ℤ) (down ℤ) (down ℤ)) (n₁ + n₂ - k)) _
    { toFun x := ⟨(n₁ - x.val.1, n₂ - x.val.2), by
        have hx : x.val.1 + x.val.2 = k := x.property
        simp only [Set.mem_preimage, Set.mem_singleton_iff, π_eq_add]
        omega⟩
      invFun y := ⟨(n₁ - y.val.1, n₂ - y.val.2), by
        have hy : y.val.1 + y.val.2 = n₁ + n₂ - k := y.property
        simp only [Set.mem_preimage, Set.mem_singleton_iff, π_eq_add]
        omega⟩
      left_inv x := by ext <;> simp
      right_inv y := by ext <;> simp }
    (fun _ ↦ Iso.refl _)

variable [K.HasTensor L]

/-- The component of the comparison between regradings of tensor products on the summand
`K_(n₁ - a) ⊗ L_(n₂ - b)` of the tensor product of the regradings: the inclusion of this summand
into `(K ⊗ L)_(n₁ + n₂ - k)`, with the sign `(-1)^(n₁ (n₂ - b))`. -/
noncomputable def regradeTensorSummand (a b k : ℤ) (h : a + b = k) :
    (K.restriction (embeddingUpIntDownIntSub n₁)).X a ⊗
        (L.restriction (embeddingUpIntDownIntSub n₂)).X b ⟶
      ((tensorObj K L).restriction (embeddingUpIntDownIntSub (n₁ + n₂))).X k :=
  (n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - k) (by omega)

/-- `ChainComplex.regradeTensorSummand` is the signed inclusion of the summand
`K_(n₁ - a) ⊗ L_(n₂ - b)` of `K ⊗ L`. -/
lemma regradeTensorSummand_def (a b k : ℤ) (h : a + b = k) :
    regradeTensorSummand n₁ n₂ K L a b k h =
      (n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - k) (by omega) :=
  (rfl)

/-- The summand components of the comparison intertwine the differential of `K ⊗ L` with the
Koszul differential of the tensor product of the regradings: the sign `(-1)^(n₁ q)` converts the
Koszul sign `(-1)^p` of `K ⊗ L` into the sign `(-1)^a = (-1)^(n₁ - p)`. -/
private lemma regradeTensorSummand_comp_d (a b k : ℤ) (h : a + b = k) :
    ((n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - k) (by omega)) ≫
        (tensorObj K L).d (n₁ + n₂ - k) (n₁ + n₂ - (k + 1)) =
      (K.d (n₁ - a) (n₁ - (a + 1)) ▷ L.X (n₂ - b)) ≫ ((n₁ * (n₂ - b)).negOnePow •
          ιTensorObj K L (n₁ - (a + 1)) (n₂ - b) (n₁ + n₂ - (k + 1)) (by omega)) +
        a.negOnePow • ((K.X (n₁ - a) ◁ L.d (n₂ - b) (n₂ - (b + 1))) ≫
          ((n₁ * (n₂ - (b + 1))).negOnePow •
            ιTensorObj K L (n₁ - a) (n₂ - (b + 1)) (n₁ + n₂ - (k + 1)) (by omega))) := by
  rw [mapBifunctor.d_eq, Linear.units_smul_comp, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (down_mk (n₁ - a) (n₁ - (a + 1)) (by omega)) (n₂ - b)
      (n₁ + n₂ - (k + 1)) (by dsimp; omega),
    mapBifunctor.d₂_eq _ _ _ _ (n₁ - a) (down_mk (n₂ - b) (n₂ - (b + 1)) (by omega))
      (n₁ + n₂ - (k + 1)) (by dsimp; omega)]
  simp only [ε₁_def, ε₂_def, ε_down_ℤ, one_smul, curriedTensor_map_app, curriedTensor_obj_map,
    Linear.comp_units_smul, smul_add, smul_smul]
  congr 2
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨n₁ - a, by ring⟩

/-- The comparison morphism from the tensor product of the regradings of `K` by `n₁` and of `L` by
`n₂` to the regrading of `K ⊗ L` by `n₁ + n₂`. On the summand `K_p ⊗ L_q` it is the identity
twisted by the sign `(-1)^(n₁ q)`. -/
noncomputable def regradeTensorHom :
    tensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
        (L.restriction (embeddingUpIntDownIntSub n₂)) ⟶
      (tensorObj K L).restriction (embeddingUpIntDownIntSub (n₁ + n₂)) where
  f k := mapBifunctorDesc (fun a b h ↦ regradeTensorSummand n₁ n₂ K L a b k h)
  comm' k k' hk := by
    replace hk : k + 1 = k' := hk
    subst hk
    apply mapBifunctor.hom_ext
    intro a b h
    replace h : a + b = k := h
    rw [ι_mapBifunctorDesc_assoc, mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
      mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc,
      mapBifunctor.d₁_eq _ _ _ _ (up_mk a (a + 1) rfl) b (k + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq _ _ _ _ a (up_mk b (b + 1) rfl) (k + 1) (by dsimp; omega)]
    simp only [ε₁_def, ε₂_def, ε_up_ℤ, one_smul, curriedTensor_map_app, curriedTensor_obj_map,
      Linear.units_smul_comp, Category.assoc, ι_mapBifunctorDesc]
    -- The summands and differentials of the regraded complexes are those of `K`, `L` and `K ⊗ L`
    -- by definition of `HomologicalComplex.restriction`, so the identity between plain summands
    -- closes the goal.
    exact regradeTensorSummand_comp_d n₁ n₂ K L a b k h

private lemma regradeTensorHom_f (k : ℤ) :
    (regradeTensorHom n₁ n₂ K L).f k =
      mapBifunctorDesc (fun a b h ↦ regradeTensorSummand n₁ n₂ K L a b k h) :=
  rfl

/-- On the summand `K_(n₁ - a) ⊗ L_(n₂ - b)`, the comparison morphism is
`ChainComplex.regradeTensorSummand`. -/
@[reassoc (attr := simp)]
lemma ι_regradeTensorHom_f (a b k : ℤ) (h : a + b = k) :
    ιTensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
          (L.restriction (embeddingUpIntDownIntSub n₂)) a b k h ≫
        (regradeTensorHom n₁ n₂ K L).f k =
      regradeTensorSummand n₁ n₂ K L a b k h := by
  rw [regradeTensorHom_f]
  exact ι_mapBifunctorDesc _ _ _ _

/-- The inverse of the comparison on the summand `K_p ⊗ L_q` of `K ⊗ L` in degree
`n₁ + n₂ - k`: the identification of `K_p ⊗ L_q` with the summand
`K_(n₁ - (n₁ - p)) ⊗ L_(n₂ - (n₂ - q))` of the tensor product of the regradings, in degree `k`, with
the sign `(-1)^(n₁ q)`. -/
noncomputable def regradeTensorInvSummand (p q k : ℤ) (h : p + q = n₁ + n₂ - k) :
    K.X p ⊗ L.X q ⟶ (tensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
      (L.restriction (embeddingUpIntDownIntSub n₂))).X k :=
  (n₁ * q).negOnePow •
    (((K.restrictionXIso (embeddingUpIntDownIntSub n₁) (by simp : n₁ - (n₁ - p) = p)).inv ⊗ₘ
      (L.restrictionXIso (embeddingUpIntDownIntSub n₂) (by simp : n₂ - (n₂ - q) = q)).inv) ≫
      ιTensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
        (L.restriction (embeddingUpIntDownIntSub n₂)) (n₁ - p) (n₂ - q) k (by omega))

/-- `ChainComplex.regradeTensorInvSummand` is the signed inclusion of `K_p ⊗ L_q`, read in the
regraded complexes, into the tensor product of the regradings. -/
lemma regradeTensorInvSummand_def (p q k : ℤ) (h : p + q = n₁ + n₂ - k) :
    regradeTensorInvSummand n₁ n₂ K L p q k h = (n₁ * q).negOnePow •
      (((K.restrictionXIso (embeddingUpIntDownIntSub n₁) (by simp : n₁ - (n₁ - p) = p)).inv ⊗ₘ
        (L.restrictionXIso (embeddingUpIntDownIntSub n₂) (by simp : n₂ - (n₂ - q) = q)).inv) ≫
        ιTensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
          (L.restriction (embeddingUpIntDownIntSub n₂)) (n₁ - p) (n₂ - q) k (by omega)) :=
  (rfl)

/-- In degree `k`, the inverse of the comparison morphism `ChainComplex.regradeTensorHom`. -/
private noncomputable def regradeTensorInvF (k : ℤ) :
    (tensorObj K L).X (n₁ + n₂ - k) ⟶
      (tensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
        (L.restriction (embeddingUpIntDownIntSub n₂))).X k :=
  mapBifunctorDesc (fun p q h ↦ regradeTensorInvSummand n₁ n₂ K L p q k h)

@[reassoc]
private lemma ι_regradeTensorInvF (p q k : ℤ) (h : p + q = n₁ + n₂ - k) :
    ιTensorObj K L p q (n₁ + n₂ - k) h ≫ regradeTensorInvF n₁ n₂ K L k =
      regradeTensorInvSummand n₁ n₂ K L p q k h :=
  ι_mapBifunctorDesc _ _ _ _

private lemma regradeTensorSummand_comp_regradeTensorInvF (a b k : ℤ) (h : a + b = k) :
    ((n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - k) (by omega)) ≫
        regradeTensorInvF n₁ n₂ K L k =
      ιTensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
        (L.restriction (embeddingUpIntDownIntSub n₂)) a b k h := by
  rw [Linear.units_smul_comp, ι_regradeTensorInvF, regradeTensorInvSummand_def, smul_smul,
    Int.units_mul_self, one_smul]
  -- `restrictionXIso` is `XIsoOfEq` of the regraded complex up to the definitional identification
  -- `C^k = K_(n-k)`, so the index-relabelling lemma for `ιTensorObj` applies to the regradings.
  exact XIsoOfEq_hom_tensorHom_XIsoOfEq_hom_ιTensorObj (K.restriction _) (L.restriction _)
    (sub_sub_cancel n₁ a).symm (sub_sub_cancel n₂ b).symm k h _

private lemma ι_regradeTensorInvF_comp_regradeTensorHom_f (p q k : ℤ)
    (h : p + q = n₁ + n₂ - k) :
    ιTensorObj K L p q (n₁ + n₂ - k) h ≫ regradeTensorInvF n₁ n₂ K L k ≫
        (regradeTensorHom n₁ n₂ K L).f k =
      ιTensorObj K L p q (n₁ + n₂ - k) h := by
  rw [ι_regradeTensorInvF_assoc, regradeTensorInvSummand_def, Linear.units_smul_comp,
    Category.assoc, ι_regradeTensorHom_f]
  have hq : (n₁ * (n₂ - (n₂ - q))).negOnePow = (n₁ * q).negOnePow := by rw [sub_sub_cancel]
  have key : (n₁ * q).negOnePow • (((K.XIsoOfEq (show p = n₁ - (n₁ - p) by omega)).hom ⊗ₘ
      (L.XIsoOfEq (show q = n₂ - (n₂ - q) by omega)).hom) ≫
        ((n₁ * (n₂ - (n₂ - q))).negOnePow • ιTensorObj K L (n₁ - (n₁ - p)) (n₂ - (n₂ - q))
          (n₁ + n₂ - k) (by omega))) = ιTensorObj K L p q (n₁ + n₂ - k) h := by
    rw [Linear.comp_units_smul, smul_smul, hq, Int.units_mul_self, one_smul,
      XIsoOfEq_hom_tensorHom_XIsoOfEq_hom_ιTensorObj]
  -- The identifications `restrictionXIso` and `XIsoOfEq` are both identities up to the
  -- equalities of indices, and `regradeTensorSummand` is the signed inclusion of a summand.
  exact key

/-- The tensor product of the regradings of `K` by `n₁` and of `L` by `n₂` is isomorphic to the
regrading of the tensor product `K ⊗ L` of chain complexes by `n₁ + n₂`, through the comparison
morphism `ChainComplex.regradeTensorHom`. On the summand `K_p ⊗ L_q` the isomorphism is the
identity twisted by the sign `(-1)^(n₁ q)` (`ChainComplex.ι_regradeTensorHom_f`). -/
noncomputable def regradeTensorIso :
    tensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
        (L.restriction (embeddingUpIntDownIntSub n₂)) ≅
      (tensorObj K L).restriction (embeddingUpIntDownIntSub (n₁ + n₂)) :=
  Hom.isoOfComponents
    (fun k ↦
      { hom := (regradeTensorHom n₁ n₂ K L).f k
        inv := regradeTensorInvF n₁ n₂ K L k
        -- The summands of the regraded complexes are those of `K`, `L` and `K ⊗ L` by definition of
        -- `HomologicalComplex.restriction`, so the identities between plain summands apply.
        hom_inv_id := mapBifunctor.hom_ext fun a b h ↦
          (ι_regradeTensorHom_f_assoc n₁ n₂ K L a b k h _).trans
            ((regradeTensorSummand_comp_regradeTensorInvF n₁ n₂ K L a b k h).trans
              (Category.comp_id _).symm)
        inv_hom_id := mapBifunctor.hom_ext fun p q h ↦
          (ι_regradeTensorInvF_comp_regradeTensorHom_f n₁ n₂ K L p q k h).trans
            (Category.comp_id _).symm })
    (fun i j _ ↦ (regradeTensorHom n₁ n₂ K L).comm i j)

/-- The isomorphism `ChainComplex.regradeTensorIso` is the comparison morphism
`ChainComplex.regradeTensorHom`. -/
@[simp]
lemma regradeTensorIso_hom : (regradeTensorIso n₁ n₂ K L).hom = regradeTensorHom n₁ n₂ K L :=
  (rfl)

/-- On the summand `K_p ⊗ L_q` of `K ⊗ L` in degree `n₁ + n₂ - k`, the inverse of
`ChainComplex.regradeTensorIso` is the identification of `K_p ⊗ L_q` with the summand
`K_(n₁ - (n₁ - p)) ⊗ L_(n₂ - (n₂ - q))` of the tensor product of the regradings, with the sign
`(-1)^(n₁ q)`. -/
@[simp, reassoc]
lemma ι_regradeTensorIso_inv_f (p q k : ℤ) (h : p + q = n₁ + n₂ - k) :
    ιTensorObj K L p q (n₁ + n₂ - k) h ≫ (regradeTensorIso n₁ n₂ K L).inv.f k =
      regradeTensorInvSummand n₁ n₂ K L p q k h :=
  ι_regradeTensorInvF n₁ n₂ K L p q k h

variable {n₁ n₂ K L} in
private lemma regradeTensorSummand_naturality {K₂ L₂ : ChainComplex C ℤ} [K₂.HasTensor L₂]
    (φ : K ⟶ K₂)
    (ψ : L ⟶ L₂) (a b k : ℤ) (h : a + b = k) :
    (φ.f (n₁ - a) ⊗ₘ ψ.f (n₂ - b)) ≫
        ((n₁ * (n₂ - b)).negOnePow • ιTensorObj K₂ L₂ (n₁ - a) (n₂ - b) (n₁ + n₂ - k)
          (by omega)) =
      ((n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - k)
          (by omega)) ≫ (tensorHom φ ψ).f (n₁ + n₂ - k) := by
  rw [Linear.comp_units_smul, Linear.units_smul_comp, ι_tensorHom]

/-- The comparison morphism `ChainComplex.regradeTensorHom` is natural in both complexes. -/
@[reassoc]
lemma regradeTensorHom_naturality {K₂ L₂ : ChainComplex C ℤ} [K₂.HasTensor L₂] (φ : K ⟶ K₂)
    (ψ : L ⟶ L₂) :
    tensorHom (restrictionMap φ (embeddingUpIntDownIntSub n₁))
        (restrictionMap ψ (embeddingUpIntDownIntSub n₂)) ≫ regradeTensorHom n₁ n₂ K₂ L₂ =
      regradeTensorHom n₁ n₂ K L ≫
        restrictionMap (tensorHom φ ψ) (embeddingUpIntDownIntSub (n₁ + n₂)) := by
  ext k a b h
  rw [comp_f, comp_f, ι_tensorHom_assoc, ι_regradeTensorHom_f, ι_regradeTensorHom_f_assoc,
    restrictionMap_f]
  simp only [restrictionMap_f]
  -- The regraded complexes and morphisms have the summands and components of `K`, `L`, `φ` and
  -- `ψ` by definition of `HomologicalComplex.restriction`.
  exact regradeTensorSummand_naturality φ ψ a b k h

/-- The inverse of the isomorphism `ChainComplex.regradeTensorIso` is natural in both
complexes. -/
@[reassoc]
lemma regradeTensorIso_inv_naturality {K₂ L₂ : ChainComplex C ℤ} [K₂.HasTensor L₂]
    (φ : K ⟶ K₂) (ψ : L ⟶ L₂) :
    restrictionMap (tensorHom φ ψ) (embeddingUpIntDownIntSub (n₁ + n₂)) ≫
        (regradeTensorIso n₁ n₂ K₂ L₂).inv =
      (regradeTensorIso n₁ n₂ K L).inv ≫
        tensorHom (restrictionMap φ (embeddingUpIntDownIntSub n₁))
          (restrictionMap ψ (embeddingUpIntDownIntSub n₂)) := by
  rw [← cancel_epi (regradeTensorIso n₁ n₂ K L).hom, Iso.hom_inv_id_assoc, regradeTensorIso_hom,
    ← regradeTensorHom_naturality_assoc, ← regradeTensorIso_hom, Iso.hom_inv_id,
    Category.comp_id]

section Braiding

variable [BraidedCategory C] [L.HasTensor K]

/-- The interchange of `K ⊗ L` on the image of the summand `K_(n₁ - a) ⊗ L_(n₂ - b)` of the
tensor product of the regradings, written on plain summands: the sign `(-1)^(n₁ (n₂ - b))` of the
comparison and the Koszul sign `(-1)^((n₁ - a) (n₂ - b))` of the chain degrees give the Koszul sign
`(-1)^(a b)` of the cochain degrees, the sign `(-1)^(n₂ (n₁ - a))` of the comparison for `L ⊗ K`,
and the global sign `(-1)^(n₁ n₂)`. -/
private lemma regradeTensorSummand_comp_tensorBraiding_hom_f (a b k : ℤ) (h : a + b = k) :
    ((n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - k) (by omega)) ≫
        (tensorBraiding K L).hom.f (n₁ + n₂ - k) =
      (n₁ * n₂).negOnePow • ((a * b).negOnePow • ((β_ (K.X (n₁ - a)) (L.X (n₂ - b))).hom ≫
          ((n₂ * (n₁ - a)).negOnePow • ιTensorObj L K (n₂ - b) (n₁ - a) (n₂ + n₁ - k)
            (by omega)) ≫
            eqToHom (congrArg (tensorObj L K).X (show n₂ + n₁ - k = n₁ + n₂ - k by ring)))) := by
  -- Shifting the total degree of a summand inclusion of `L ⊗ K` along `n₂ + n₁ - k = n₁ + n₂ - k`.
  have hι : ∀ {j j' : ℤ} (hj : j = j') (h' : n₂ - b + (n₁ - a) = j),
      ιTensorObj L K (n₂ - b) (n₁ - a) j h' ≫ eqToHom (congrArg (tensorObj L K).X hj) =
        ιTensorObj L K (n₂ - b) (n₁ - a) j' (h'.trans hj) := by
    rintro _ _ rfl _
    simp
  rw [Linear.units_smul_comp, ιTensorObj_tensorBraiding_hom_f, Linear.units_smul_comp,
    hι (show n₂ + n₁ - k = n₁ + n₂ - k by ring), Linear.comp_units_smul,
    smul_smul, smul_smul, smul_smul, ComplexShape.σ_down_ℤ, ← Int.negOnePow_add,
    ← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨-(n₁ * b), by ring⟩

/-- **The regrading of tensor products and the interchange of factors.** Interchanging the factors
of the tensor product of the regradings of `K` by `n₁` and of `L` by `n₂`, with the Koszul sign
`(-1)^(a b)` of their cochain degrees, and comparing with the regrading of `L ⊗ K`, agrees up to
the global sign `(-1)^(n₁ n₂)` with comparing with the regrading of `K ⊗ L` and interchanging the
factors there, with the Koszul sign `(-1)^(p q)` of the chain degrees. The equality of the
regradings of `L ⊗ K` by `n₂ + n₁` and by `n₁ + n₂` is the `eqToHom`.

On the summand `K_p ⊗ L_q`, with cochain degrees `a = n₁ - p` and `b = n₂ - q`, the two composites
carry the signs `(-1)^(a b + n₂ (n₁ - a))` and `(-1)^(n₁ q + p q)`, whose exponents differ by
`n₁ n₂` modulo `2`. Thus a chain-level product on raw complexes which is graded commutative with
the Koszul sign of the raw degrees becomes, after the cohomological regrading, graded commutative
with the Koszul sign of the cochain degrees twisted by `(-1)^(n₁ n₂)`
(`ChainComplex.tensorBraiding_hom_comp_regradeTensorHom_comp_restrictionMap`). -/
theorem regradeTensorHom_comp_restrictionMap_tensorBraiding :
    regradeTensorHom n₁ n₂ K L ≫
        restrictionMap (tensorBraiding K L).hom (embeddingUpIntDownIntSub (n₁ + n₂)) =
      (n₁ * n₂).negOnePow •
        ((tensorBraiding (K.restriction (embeddingUpIntDownIntSub n₁))
            (L.restriction (embeddingUpIntDownIntSub n₂))).hom ≫
          regradeTensorHom n₂ n₁ L K ≫
            eqToHom (congrArg (fun n ↦ (tensorObj L K).restriction (embeddingUpIntDownIntSub n))
              (add_comm n₂ n₁))) := by
  ext k a b h
  replace h : a + b = k := h
  simp only [comp_f, ι_regradeTensorHom_f_assoc, restrictionMap_f,
    HomologicalComplex.units_smul_f_apply, Linear.comp_units_smul, eqToHom_f,
    ιTensorObj_tensorBraiding_hom_f_assoc, regradeTensorSummand_def, Linear.units_smul_comp,
    ι_regradeTensorHom_f_assoc, Category.assoc]
  -- The summands, inclusions and components of the regraded complexes are those of `K`, `L`,
  -- `K ⊗ L` and `L ⊗ K` by definition of `HomologicalComplex.restriction`, so the identity
  -- between plain summands closes the goal.
  exact regradeTensorSummand_comp_tensorBraiding_hom_f n₁ n₂ K L a b k h

/-- **Regrading both factors by the same integer and the interchange of factors.** For the
regradings of `K` and `L` by the same `n₁`, as for the product `CF_i ⊗ CF_j → CF_(i+j-n)` on Floer
complexes of a symplectic manifold of dimension `2n` with `n₁ = n`, the interchange of the regraded
factors and the interchange of the raw factors agree up to the sign `(-1)^n₁`
(`ChainComplex.regradeTensorHom_comp_restrictionMap_tensorBraiding`). -/
theorem regradeTensorHom_comp_restrictionMap_tensorBraiding_self :
    regradeTensorHom n₁ n₁ K L ≫
        restrictionMap (tensorBraiding K L).hom (embeddingUpIntDownIntSub (n₁ + n₁)) =
      n₁.negOnePow • ((tensorBraiding (K.restriction (embeddingUpIntDownIntSub n₁))
          (L.restriction (embeddingUpIntDownIntSub n₁))).hom ≫ regradeTensorHom n₁ n₁ L K) := by
  simpa only [eqToHom_refl, Category.comp_id, Int.negOnePow_mul_self] using
    regradeTensorHom_comp_restrictionMap_tensorBraiding n₁ n₁ K L

/-- **Graded commutativity of a regraded product.** Let `m : K ⊗ K ⟶ M` be a chain-level product
which commutes with the interchange of its inputs up to a sign `ε`, and regrade `K` by `n₁` and
`K ⊗ K` by `n₁ + n₁`, so that `m` becomes the degree-zero product
`regradeTensorHom n₁ n₁ K K ≫ restrictionMap m _` on the cochain complex `K^k = K_(n₁-k)`. This
product commutes with the interchange of its regraded inputs, which carries the Koszul sign of the
cochain degrees, up to the sign `(-1)^n₁ ε`. -/
theorem tensorBraiding_hom_comp_regradeTensorHom_comp_restrictionMap [K.HasTensor K]
    {M : ChainComplex C ℤ} (m : tensorObj K K ⟶ M) (ε : ℤˣ)
    (hm : (tensorBraiding K K).hom ≫ m = ε • m) :
    (tensorBraiding (K.restriction (embeddingUpIntDownIntSub n₁))
          (K.restriction (embeddingUpIntDownIntSub n₁))).hom ≫
        regradeTensorHom n₁ n₁ K K ≫ restrictionMap m (embeddingUpIntDownIntSub (n₁ + n₁)) =
      (n₁.negOnePow * ε) •
        (regradeTensorHom n₁ n₁ K K ≫ restrictionMap m (embeddingUpIntDownIntSub (n₁ + n₁))) := by
  have hself := regradeTensorHom_comp_restrictionMap_tensorBraiding_self n₁ K K
  have hm' : restrictionMap (tensorBraiding K K).hom (embeddingUpIntDownIntSub (n₁ + n₁)) ≫
      restrictionMap m (embeddingUpIntDownIntSub (n₁ + n₁)) =
        ε • restrictionMap m (embeddingUpIntDownIntSub (n₁ + n₁)) := by
    rw [← restrictionMap_comp, hm]
    ext k
    simp [restrictionMap_f]
  rw [← Category.assoc, ← smul_left_cancel_iff n₁.negOnePow, ← Linear.units_smul_comp, ← hself,
    Category.assoc, hm', Linear.comp_units_smul, smul_smul, ← mul_assoc, Int.units_mul_self,
    one_mul]

end Braiding

end ChainComplex

/-! ### Compatibility with the associators -/

namespace ChainComplex

open HomologicalComplex ComplexShape

section Associator

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasZeroObject C] [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (n₁ n₂ n₃ : ℤ) (K L M : ChainComplex C ℤ)

/-- `ChainComplex.ι_regradeTensorHom_f` for the chain complexes `K ⊗ L` and `M`, with the summand
inclusion read in the regrading of `HomologicalComplex.tensorObj K L`, the codomain of
`ChainComplex.regradeTensorHom n₁ n₂ K L`. -/
@[reassoc]
private lemma ι_regradeTensorHom_f_tensorObj_left (a b k : ℤ) (h : a + b = k) :
    ιTensorObj ((HomologicalComplex.tensorObj K L).restriction
          (embeddingUpIntDownIntSub (n₁ + n₂)))
        (M.restriction (embeddingUpIntDownIntSub n₃)) a b k h ≫
        (regradeTensorHom (n₁ + n₂) n₃ (K ⊗ L) M).f k =
      regradeTensorSummand (n₁ + n₂) n₃ (K ⊗ L) M a b k h :=
  ι_regradeTensorHom_f (n₁ + n₂) n₃ (K ⊗ L) M a b k h

/-- `ChainComplex.ι_regradeTensorHom_f` for the chain complexes `K` and `L ⊗ M`, with the summand
inclusion read in the regrading of `HomologicalComplex.tensorObj L M`, the codomain of
`ChainComplex.regradeTensorHom n₂ n₃ L M`. -/
private lemma ι_regradeTensorHom_f_tensorObj_right (a b k : ℤ) (h : a + b = k) :
    ιTensorObj (K.restriction (embeddingUpIntDownIntSub n₁))
        ((HomologicalComplex.tensorObj L M).restriction
          (embeddingUpIntDownIntSub (n₂ + n₃))) a b k h ≫
        (regradeTensorHom n₁ (n₂ + n₃) K (L ⊗ M)).f k =
      regradeTensorSummand n₁ (n₂ + n₃) K (L ⊗ M) a b k h :=
  ι_regradeTensorHom_f n₁ (n₂ + n₃) K (L ⊗ M) a b k h

/-- On the summand `K_(n₁ - a) ⊗ L_(n₂ - b) ⊗ M_(n₃ - c)`, the two composites of
`ChainComplex.regradeTensorHom_associativity` are the associator of `C` with the signs
`(-1)^(n₁ (n₂ - b) + (n₁ + n₂) (n₃ - c))` and `(-1)^(n₂ (n₃ - c) + n₁ (n₂ + n₃ - (b + c)))`, which
agree. -/
private lemma regradeTensorSummand_associativity (a b c k : ℤ) (h : a + b + c = k) :
    ((n₁ * (n₂ - b)).negOnePow • ιTensorObj K L (n₁ - a) (n₂ - b) (n₁ + n₂ - (a + b))
          (by omega)) ▷ M.X (n₃ - c) ≫
        (((n₁ + n₂) * (n₃ - c)).negOnePow • ιTensorObj (K ⊗ L) M (n₁ + n₂ - (a + b)) (n₃ - c)
          (n₁ + n₂ + n₃ - k) (by omega)) ≫
        (α_ K L M).hom.f (n₁ + n₂ + n₃ - k) ≫
          ((HomologicalComplex.tensorObj K (L ⊗ M)).XIsoOfEq
            (show n₁ + n₂ + n₃ - k = n₁ + (n₂ + n₃) - k by ring)).hom =
      (α_ (K.X (n₁ - a)) (L.X (n₂ - b)) (M.X (n₃ - c))).hom ≫
        K.X (n₁ - a) ◁ ((n₂ * (n₃ - c)).negOnePow •
          ιTensorObj L M (n₂ - b) (n₃ - c) (n₂ + n₃ - (b + c)) (by omega)) ≫
        ((n₁ * (n₂ + n₃ - (b + c))).negOnePow •
          ιTensorObj K (L ⊗ M) (n₁ - a) (n₂ + n₃ - (b + c)) (n₁ + (n₂ + n₃) - k) (by omega)) := by
  simp only [Units.smul_def, zsmul_whiskerRight, whiskerLeft_zsmul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, smul_smul]
  rw [ι_ι_associator_hom_assoc K L M (n₁ - a) (n₂ - b) (n₃ - c) (n₁ + n₂ - (a + b))
    (n₂ + n₃ - (b + c)) (n₁ + n₂ + n₃ - k) (by omega) (by omega) (by omega) (by omega),
    ιTensorObj_comp_XIsoOfEq_hom]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 2
  ring

/-- **The regrading of tensor products is compatible with the associators.** For chain complexes
`K`, `L`, `M` and integers `n₁`, `n₂`, `n₃`, the two ways of comparing the tensor product of the
regradings of `K` by `n₁`, `L` by `n₂` and `M` by `n₃` with the regrading of `K ⊗ (L ⊗ M)` by
`n₁ + n₂ + n₃` agree: first comparing `K ⊗ L` and then applying the associator of chain complexes,
or first applying the associator of cochain complexes and then comparing `L ⊗ M`. The two
regradings by `(n₁ + n₂) + n₃` and `n₁ + (n₂ + n₃)` are identified by
`ChainComplex.regradeIsoOfEq`.

On the summand `K_p ⊗ L_q ⊗ M_r` both composites are the associator of `C` with the sign
`(-1)^(n₁ q + n₁ r + n₂ r)`. So a degree-shifting product that is associative on the chain level
remains associative after regrading, with no sign correction. This is the form of the
compatibility that the associator of the regraded Floer complexes `C^k = CF_(n-k)` requires.

This is the associativity axiom of a lax monoidal functor
(`CategoryTheory.Functor.LaxMonoidal.associativity`) for the regrading, up to the
identification of the shifts. -/
@[reassoc]
theorem regradeTensorHom_associativity :
    regradeTensorHom n₁ n₂ K L ▷ M.restriction (embeddingUpIntDownIntSub n₃) ≫
        regradeTensorHom (n₁ + n₂) n₃ (K ⊗ L) M ≫
          restrictionMap (α_ K L M).hom (embeddingUpIntDownIntSub (n₁ + n₂ + n₃)) ≫
            (regradeIsoOfEq (add_assoc n₁ n₂ n₃) (K ⊗ (L ⊗ M))).hom =
      (α_ (K.restriction (embeddingUpIntDownIntSub n₁))
          (L.restriction (embeddingUpIntDownIntSub n₂))
          (M.restriction (embeddingUpIntDownIntSub n₃))).hom ≫
        K.restriction (embeddingUpIntDownIntSub n₁) ◁ regradeTensorHom n₂ n₃ L M ≫
          regradeTensorHom n₁ (n₂ + n₃) K (L ⊗ M) := by
  ext k
  refine mapBifunctor₁₂.hom_ext (fun a b c h ↦ ?_)
  replace h : a + b + c = k := h
  rw [mapBifunctor₁₂.ι_eq_whiskerRight _ _ _ a b c (a + b) k rfl h]
  simp only [comp_f, Category.assoc]
  rw [ι_whiskerRight_assoc, ← comp_whiskerRight_assoc, ι_regradeTensorHom_f,
    ι_regradeTensorHom_f_tensorObj_left_assoc, ι_ι_associator_hom_assoc _ _ _ a b c (a + b)
      (b + c) k rfl rfl h (by omega), ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
    ι_regradeTensorHom_f, ι_regradeTensorHom_f_tensorObj_right]
  rw [regradeTensorSummand_def, regradeTensorSummand_def, regradeTensorSummand_def,
    regradeTensorSummand_def]
  rw [restrictionMap_f, regradeIsoOfEq_hom_f]
  -- The summands of the regraded complexes are those of `K`, `L`, `M` and their tensor products
  -- by definition of `HomologicalComplex.restriction`, so the identity between plain summands
  -- closes the goal.
  exact regradeTensorSummand_associativity n₁ n₂ n₃ K L M a b c k h

end Associator

end ChainComplex
