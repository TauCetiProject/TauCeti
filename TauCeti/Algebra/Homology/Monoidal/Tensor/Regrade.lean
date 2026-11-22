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
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential

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
    rw [ι_mapBifunctorDesc_assoc, ιTensorObj_d_assoc]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, ι_mapBifunctorDesc]
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

end ChainComplex
