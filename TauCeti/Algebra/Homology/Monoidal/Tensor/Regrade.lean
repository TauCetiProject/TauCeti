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
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Symmetry
import TauCeti.Algebra.Homology.Bifunctor.Single
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

The comparison is also compatible with the unitors. Write `𝟙[m]` for the monoidal unit of `C`
placed in chain degree `m`; its regrading by `m` is the unit of cochain complexes
(`ChainComplex.regradeSingleIso`). For odd `m` the left unitor `𝟙 ⊗ L_q ≅ L_q` is not a chain map
`𝟙[m] ⊗ L → L` of degree `-m`, since the differential of `𝟙[m] ⊗ L` is `(-1)^m` times that of `L`.
Twisted by `(-1)^(m q)` it is a morphism `ChainComplex.regradeSingleLeftUnitor` between the
regradings, and the comparison composed with it is the left unitor of cochain complexes, with no
further sign (`ChainComplex.regradeTensorHom_left_unitality`). The right unitor
`L_p ⊗ 𝟙 ≅ L_p` is a chain map as it stands (`ChainComplex.regradeSingleRightUnitor`), and the
comparison composed with it is `(-1)^(n₁ m)` times the right unitor of cochain complexes
(`ChainComplex.regradeTensorHom_right_unitality`). For `m = 0` both are the regradings of the
unitors of chain complexes (`ChainComplex.regradeSingleLeftUnitor_zero`,
`ChainComplex.regradeSingleRightUnitor_zero`), and when the other shift is also `0` the two
statements are the unitality axioms of a lax monoidal functor for the regrading by `0`, up to the
identification of the shifts. For a Floer complex `C^k = CF_(n-k)`, whose unit lies in chain
degree `n`, this is the passage between unit identities of the raw product and the unit laws of
the regraded product in cochain degree `0`; on the right it introduces the sign `(-1)^n`.

## Main definitions

* `ChainComplex.regradeTensorSummand`: the component of the comparison on one summand.
* `ChainComplex.regradeTensorHom`: the comparison morphism from the tensor product of the
  regradings to the regrading of the tensor product.
* `ChainComplex.regradeTensorIso`: the comparison morphism as an isomorphism between the tensor
  product of the regradings of `K` by `n₁` and `L` by `n₂` and the regrading of `K ⊗ L` by
  `n₁ + n₂`.
* `ChainComplex.regradeSingleLeftUnitor`, `ChainComplex.regradeSingleRightUnitor`: the left and
  right unitors of the monoidal unit placed in chain degree `n₁`, respectively `n₂`, as morphisms
  between regradings, the left one with the sign `(-1)^(n₁ q)` on `𝟙 ⊗ L_q`.

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
* `ChainComplex.regradeTensorHom_left_unitality`, `ChainComplex.regradeTensorHom_right_unitality`:
  the comparison is compatible with the left unitors, and with the right unitors up to the sign
  `(-1)^(n₁ n₂)`.
* `ChainComplex.regradeSingleLeftUnitor_zero`, `ChainComplex.regradeSingleRightUnitor_zero`: for the
  unit in chain degree `0` these unitors are the regradings of the unitors of chain complexes.

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
  rw [Linear.units_smul_comp, ιTensorObj_d_of_rel K L _
    (down_mk (n₁ - a) (n₁ - (a + 1)) (by omega)) (down_mk (n₂ - b) (n₂ - (b + 1)) (by omega))
    (by omega)]
  simp only [ε_down_ℤ, Linear.comp_units_smul, smul_add, smul_smul]
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
    rw [π_eq_add] at h
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

/-! ### Compatibility with the unitors -/

namespace ChainComplex

open HomologicalComplex ComplexShape

section Unitor

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasZeroObject C] [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  (n₁ n₂ : ℤ) (K L : ChainComplex C ℤ)

/-- The summand components of `ChainComplex.regradeSingleLeftUnitor` in cochain degree `k`: on
`𝟙_p ⊗ L_q` with `p = n₁`, the left unitor of `L_q` with the sign `(-1)^(n₁ q)`, and zero on the
other summands, which are zero. -/
private noncomputable def regradeSingleLeftUnitorSummand (k p q : ℤ)
    (h : p + q = n₁ + n₂ - k) :
    ((single C (down ℤ) n₁).obj (𝟙_ C)).X p ⊗ L.X q ⟶ L.X (n₂ - k) :=
  if hp : p = n₁ then
    (n₁ * q).negOnePow • ((singleObjXIsoOfEq (down ℤ) n₁ (𝟙_ C) p hp).hom ▷ L.X q ≫
      (λ_ (L.X q)).hom ≫ (L.XIsoOfEq (show q = n₂ - k by omega)).hom)
  else 0

/-- The summand components of `ChainComplex.regradeSingleLeftUnitor` intertwine the differential
of `𝟙[n₁] ⊗ L`, whose Koszul sign on the second factor is `(-1)^n₁`, with the differential of `L`:
the twist `(-1)^(n₁ q)` absorbs it. -/
private lemma regradeSingleLeftUnitorSummand_comp_d (k p q : ℤ) (h : p + q = n₁ + n₂ - k) :
    regradeSingleLeftUnitorSummand n₁ n₂ L k p q h ≫ L.d (n₂ - k) (n₂ - (k + 1)) =
      ιTensorObj ((single C (down ℤ) n₁).obj (𝟙_ C)) L p q (n₁ + n₂ - k) h ≫
        (HomologicalComplex.tensorObj ((single C (down ℤ) n₁).obj (𝟙_ C)) L).d (n₁ + n₂ - k)
          (n₁ + n₂ - (k + 1)) ≫
        mapBifunctorDesc (fun p' q' h' ↦
          regradeSingleLeftUnitorSummand n₁ n₂ L (k + 1) p' q' h') := by
  rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add, mapBifunctor.ι_D₁_assoc,
    mapBifunctor.ι_D₂_assoc, single_mapBifunctor_d₁, zero_comp, zero_add,
    mapBifunctor.d₂_eq _ _ _ _ p (down_mk q (q - 1) (by omega)) (n₁ + n₂ - (k + 1))
      (by dsimp; omega)]
  simp only [ε₂_def, ε_down_ℤ, curriedTensor_obj_map, Linear.units_smul_comp, Category.assoc,
    ι_mapBifunctorDesc]
  by_cases hp : p = n₁
  · subst hp
    simp only [regradeSingleLeftUnitorSummand, ↓reduceDIte, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, smul_smul]
    rw [whisker_exchange_assoc, leftUnitor_naturality_assoc, d_comp_XIsoOfEq_hom,
      XIsoOfEq_hom_comp_d, ← Int.negOnePow_add]
    congr 2
    ring
  · simp [regradeSingleLeftUnitorSummand, hp]

/-- **The left unitor of the unit placed in chain degree `n₁`**, as a morphism from the regrading
of `𝟙[n₁] ⊗ L` by `n₁ + n₂` to the regrading of `L` by `n₂`. Here `𝟙[n₁]` is the monoidal unit of
`C` placed in chain degree `n₁`. On the summand `𝟙[n₁]_(n₁) ⊗ L_q` it is the left unitor of `L_q`
twisted by the sign `(-1)^(n₁ q)` (`ChainComplex.ι_regradeSingleLeftUnitor_f`). The differential
of `𝟙[n₁] ⊗ L` is `(-1)^n₁` times that of `L` on these summands, and the sign makes the left
unitor commute with the differentials. For `n₁ = 0` it is the regrading of the left unitor of
chain complexes (`ChainComplex.regradeSingleLeftUnitor_zero`). -/
noncomputable def regradeSingleLeftUnitor :
    (HomologicalComplex.tensorObj ((single C (down ℤ) n₁).obj (𝟙_ C)) L).restriction
        (embeddingUpIntDownIntSub (n₁ + n₂)) ⟶ L.restriction (embeddingUpIntDownIntSub n₂) where
  -- The degree `n₁ + n₂ - k` is given explicitly so that the summand inclusions are indexed by
  -- `p + q = n₁ + n₂ - k` rather than by the unreduced degree of the restriction.
  f k := mapBifunctorDesc (j := n₁ + n₂ - k)
    (fun p q h ↦ regradeSingleLeftUnitorSummand n₁ n₂ L k p q h)
  comm' k k' hk := by
    replace hk : k + 1 = k' := hk
    subst hk
    apply mapBifunctor.hom_ext
    intro p q h
    -- The summands and differentials of the regraded complexes are those of `𝟙[n₁] ⊗ L` and `L`
    -- by definition of `HomologicalComplex.restriction`.
    exact (ι_mapBifunctorDesc_assoc _ p q h _).trans
      (regradeSingleLeftUnitorSummand_comp_d n₁ n₂ L k p q h)

/-- On the summand `𝟙[n₁]_p ⊗ L_q` with `p = n₁`, `ChainComplex.regradeSingleLeftUnitor` is the left
unitor of `L_q` with the sign `(-1)^(n₁ q)`, after identifying `𝟙[n₁]_p` with `𝟙_ C`. -/
@[reassoc]
lemma ι_regradeSingleLeftUnitor_f (p q k : ℤ) (h : p + q = n₁ + n₂ - k) (hp : p = n₁) :
    ιTensorObj ((single C (down ℤ) n₁).obj (𝟙_ C)) L p q (n₁ + n₂ - k) h ≫
        (regradeSingleLeftUnitor n₁ n₂ L).f k =
      (n₁ * q).negOnePow • ((singleObjXIsoOfEq (down ℤ) n₁ (𝟙_ C) p hp).hom ▷ L.X q ≫
        (λ_ (L.X q)).hom ≫ (L.XIsoOfEq (show q = n₂ - k by omega)).hom) := by
  -- The source of `(regradeSingleLeftUnitor n₁ n₂ L).f k` is `(𝟙[n₁] ⊗ L).X (n₁ + n₂ - k)` by
  -- definition of `HomologicalComplex.restriction`.
  refine (ι_mapBifunctorDesc _ p q h).trans ?_
  subst hp
  simp only [regradeSingleLeftUnitorSummand, ↓reduceDIte]
  -- The two identifications `L_q = L_(n₂ - k)` are stated through the defeq degrees
  -- `n₂ - k` and `(embeddingUpIntDownIntSub n₂).f k`.
  rfl

/-- On the summand `𝟙 ⊗ L^k` of the tensor product of the regradings, identifying the unit with the
regrading of `𝟙[n₁]`, then the comparison between regradings of tensor products, then
`ChainComplex.regradeSingleLeftUnitor`, is the left unitor of `L^k = L_(n₂ - k)`: the sign
`(-1)^(n₁ (n₂ - k))` of the comparison cancels that of `ChainComplex.regradeSingleLeftUnitor`. -/
private lemma regradeSingleIso_inv_whiskerRight_comp_regradeSingleLeftUnitor_f (k : ℤ) :
    (regradeSingleIso n₁ (𝟙_ C)).inv.f 0 ▷ (L.restriction (embeddingUpIntDownIntSub n₂)).X k ≫
        regradeTensorSummand n₁ n₂ ((single C (down ℤ) n₁).obj (𝟙_ C)) L 0 k k (zero_add k) ≫
          (regradeSingleLeftUnitor n₁ n₂ L).f k =
      (singleObjXSelf (up ℤ) 0 (𝟙_ C)).hom ▷ (L.restriction (embeddingUpIntDownIntSub n₂)).X k ≫
        (λ_ ((L.restriction (embeddingUpIntDownIntSub n₂)).X k)).hom := by
  rw [regradeSingleIso_inv_f_zero, regradeTensorSummand_def]
  -- State both sides through `𝟙[n₁]_(n₁ - 0)`, `L_(n₂ - k)` and `(𝟙[n₁] ⊗ L)_(n₁ + n₂ - k)`, the
  -- objects of the regradings by definition of `HomologicalComplex.restriction` and
  -- `ComplexShape.embeddingUpIntDownIntSub`, and `(regradeSingleLeftUnitor n₁ n₂ L).f k` through
  -- its summands. `rw` and `simp` cannot match `Linear.units_smul_comp` or
  -- `ChainComplex.ι_regradeSingleLeftUnitor_f` before this, as `embeddingUpIntDownIntSub` is not
  -- reducible.
  change ((singleObjXSelf (up ℤ) 0 (𝟙_ C)).hom ≫
      (singleObjXIsoOfEq (down ℤ) n₁ (𝟙_ C) (n₁ - 0) (sub_zero n₁)).inv) ▷ L.X (n₂ - k) ≫
    ((n₁ * (n₂ - k)).negOnePow • ιTensorObj ((single C (down ℤ) n₁).obj (𝟙_ C)) L (n₁ - 0)
      (n₂ - k) (n₁ + n₂ - k) (by omega)) ≫ mapBifunctorDesc (j := n₁ + n₂ - k)
        (fun p q h ↦ regradeSingleLeftUnitorSummand n₁ n₂ L k p q h) =
    (singleObjXSelf (up ℤ) 0 (𝟙_ C)).hom ▷ L.X (n₂ - k) ≫ (λ_ (L.X (n₂ - k))).hom
  simp only [comp_whiskerRight, π_def, regradeSingleLeftUnitorSummand, Linear.units_smul_comp,
    ι_mapBifunctorDesc, sub_zero, ↓reduceDIte, XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
    smul_smul, Int.units_mul_self, one_smul, Category.assoc, inv_hom_whiskerRight_assoc]

/-- The summand components of `ChainComplex.regradeSingleRightUnitor` in cochain degree `k`: on
`K_p ⊗ 𝟙_q` with `q = n₂`, the right unitor of `K_p`, and zero on the other summands, which are
zero. -/
private noncomputable def regradeSingleRightUnitorSummand (k p q : ℤ)
    (h : p + q = n₁ + n₂ - k) :
    K.X p ⊗ ((single C (down ℤ) n₂).obj (𝟙_ C)).X q ⟶ K.X (n₁ - k) :=
  if hq : q = n₂ then
    K.X p ◁ (singleObjXIsoOfEq (down ℤ) n₂ (𝟙_ C) q hq).hom ≫ (ρ_ (K.X p)).hom ≫
      (K.XIsoOfEq (show p = n₁ - k by omega)).hom
  else 0

/-- The summand components of `ChainComplex.regradeSingleRightUnitor` intertwine the differential
of `K ⊗ 𝟙[n₂]`, which is that of `K` on these summands, with the differential of `K`. -/
private lemma regradeSingleRightUnitorSummand_comp_d (k p q : ℤ) (h : p + q = n₁ + n₂ - k) :
    regradeSingleRightUnitorSummand n₁ n₂ K k p q h ≫ K.d (n₁ - k) (n₁ - (k + 1)) =
      ιTensorObj K ((single C (down ℤ) n₂).obj (𝟙_ C)) p q (n₁ + n₂ - k) h ≫
        (HomologicalComplex.tensorObj K ((single C (down ℤ) n₂).obj (𝟙_ C))).d (n₁ + n₂ - k)
          (n₁ + n₂ - (k + 1)) ≫
        mapBifunctorDesc (fun p' q' h' ↦
          regradeSingleRightUnitorSummand n₁ n₂ K (k + 1) p' q' h') := by
  rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add, mapBifunctor.ι_D₁_assoc,
    mapBifunctor.ι_D₂_assoc, mapBifunctor_single_d₂, zero_comp, add_zero,
    mapBifunctor.d₁_eq _ _ _ _ (down_mk p (p - 1) (by omega)) q (n₁ + n₂ - (k + 1))
      (by dsimp; omega)]
  simp only [ε₁_def, one_smul, curriedTensor_map_app, Category.assoc, ι_mapBifunctorDesc]
  by_cases hq : q = n₂
  · subst hq
    simp only [regradeSingleRightUnitorSummand, ↓reduceDIte]
    rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc, d_comp_XIsoOfEq_hom,
      Category.assoc, Category.assoc, XIsoOfEq_hom_comp_d]
  · simp [regradeSingleRightUnitorSummand, hq]

/-- **The right unitor of the unit placed in chain degree `n₂`**, as a morphism from the regrading
of `K ⊗ 𝟙[n₂]` by `n₁ + n₂` to the regrading of `K` by `n₁`. Here `𝟙[n₂]` is the monoidal unit of
`C` placed in chain degree `n₂`. On the summand `K_p ⊗ 𝟙[n₂]_(n₂)` it is the right unitor of `K_p`
(`ChainComplex.ι_regradeSingleRightUnitor_f`), with no sign: the differential of `K ⊗ 𝟙[n₂]` is
that of `K` on these summands. For `n₂ = 0` it is the regrading of the right unitor of chain
complexes (`ChainComplex.regradeSingleRightUnitor_zero`). -/
noncomputable def regradeSingleRightUnitor :
    (HomologicalComplex.tensorObj K ((single C (down ℤ) n₂).obj (𝟙_ C))).restriction
        (embeddingUpIntDownIntSub (n₁ + n₂)) ⟶ K.restriction (embeddingUpIntDownIntSub n₁) where
  -- The degree `n₁ + n₂ - k` is given explicitly so that the summand inclusions are indexed by
  -- `p + q = n₁ + n₂ - k` rather than by the unreduced degree of the restriction.
  f k := mapBifunctorDesc (j := n₁ + n₂ - k)
    (fun p q h ↦ regradeSingleRightUnitorSummand n₁ n₂ K k p q h)
  comm' k k' hk := by
    replace hk : k + 1 = k' := hk
    subst hk
    apply mapBifunctor.hom_ext
    intro p q h
    -- The summands and differentials of the regraded complexes are those of `K ⊗ 𝟙[n₂]` and `K`
    -- by definition of `HomologicalComplex.restriction`.
    exact (ι_mapBifunctorDesc_assoc _ p q h _).trans
      (regradeSingleRightUnitorSummand_comp_d n₁ n₂ K k p q h)

/-- On the summand `K_p ⊗ 𝟙[n₂]_q` with `q = n₂`, `ChainComplex.regradeSingleRightUnitor` is the
right unitor of `K_p`, after identifying `𝟙[n₂]_q` with `𝟙_ C`. -/
@[reassoc]
lemma ι_regradeSingleRightUnitor_f (p q k : ℤ) (h : p + q = n₁ + n₂ - k) (hq : q = n₂) :
    ιTensorObj K ((single C (down ℤ) n₂).obj (𝟙_ C)) p q (n₁ + n₂ - k) h ≫
        (regradeSingleRightUnitor n₁ n₂ K).f k =
      K.X p ◁ (singleObjXIsoOfEq (down ℤ) n₂ (𝟙_ C) q hq).hom ≫ (ρ_ (K.X p)).hom ≫
        (K.XIsoOfEq (show p = n₁ - k by omega)).hom := by
  -- The source of `(regradeSingleRightUnitor n₁ n₂ K).f k` is `(K ⊗ 𝟙[n₂]).X (n₁ + n₂ - k)` by
  -- definition of `HomologicalComplex.restriction`.
  refine (ι_mapBifunctorDesc _ p q h).trans ?_
  subst hq
  simp only [regradeSingleRightUnitorSummand, ↓reduceDIte]
  -- The two identifications `K_p = K_(n₁ - k)` are stated through the defeq degrees
  -- `n₁ - k` and `(embeddingUpIntDownIntSub n₁).f k`.
  rfl

/-- On the summand `K^k ⊗ 𝟙` of the tensor product of the regradings, identifying the unit with the
regrading of `𝟙[n₂]`, then the comparison between regradings of tensor products, then
`ChainComplex.regradeSingleRightUnitor`, is `(-1)^(n₁ n₂)` times the right unitor of
`K^k = K_(n₁ - k)`: the sign is that of the comparison, as `𝟙[n₂]` sits in chain degree `n₂`. -/
private lemma whiskerLeft_regradeSingleIso_inv_comp_regradeSingleRightUnitor_f (k : ℤ) :
    (K.restriction (embeddingUpIntDownIntSub n₁)).X k ◁ (regradeSingleIso n₂ (𝟙_ C)).inv.f 0 ≫
        regradeTensorSummand n₁ n₂ K ((single C (down ℤ) n₂).obj (𝟙_ C)) k 0 k (add_zero k) ≫
          (regradeSingleRightUnitor n₁ n₂ K).f k =
      (n₁ * n₂).negOnePow •
        ((K.restriction (embeddingUpIntDownIntSub n₁)).X k ◁ (singleObjXSelf (up ℤ) 0 (𝟙_ C)).hom ≫
          (ρ_ ((K.restriction (embeddingUpIntDownIntSub n₁)).X k)).hom) := by
  rw [regradeSingleIso_inv_f_zero, regradeTensorSummand_def]
  -- State both sides through `K_(n₁ - k)`, `𝟙[n₂]_(n₂ - 0)` and `(K ⊗ 𝟙[n₂])_(n₁ + n₂ - k)`, the
  -- objects of the regradings by definition of `HomologicalComplex.restriction` and
  -- `ComplexShape.embeddingUpIntDownIntSub`, and `(regradeSingleRightUnitor n₁ n₂ K).f k` through
  -- its summands, as in the left unitor case.
  change K.X (n₁ - k) ◁ ((singleObjXSelf (up ℤ) 0 (𝟙_ C)).hom ≫
      (singleObjXIsoOfEq (down ℤ) n₂ (𝟙_ C) (n₂ - 0) (sub_zero n₂)).inv) ≫
    ((n₁ * (n₂ - 0)).negOnePow • ιTensorObj K ((single C (down ℤ) n₂).obj (𝟙_ C)) (n₁ - k)
      (n₂ - 0) (n₁ + n₂ - k) (by omega)) ≫ mapBifunctorDesc (j := n₁ + n₂ - k)
        (fun p q h ↦ regradeSingleRightUnitorSummand n₁ n₂ K k p q h) =
    (n₁ * n₂).negOnePow • (K.X (n₁ - k) ◁ (singleObjXSelf (up ℤ) 0 (𝟙_ C)).hom ≫
      (ρ_ (K.X (n₁ - k))).hom)
  simp only [whiskerLeft_comp, sub_zero, π_def, regradeSingleRightUnitorSummand,
    Linear.units_smul_comp, ι_mapBifunctorDesc, ↓reduceDIte, XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, Linear.comp_units_smul, Category.assoc, whiskerLeft_inv_hom_assoc]

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- For the unit placed in chain degree `0`, the monoidal unit of chain complexes,
`ChainComplex.regradeSingleLeftUnitor` is the regrading of the left unitor of chain complexes. -/
theorem regradeSingleLeftUnitor_zero :
    regradeSingleLeftUnitor 0 n₂ L =
      restrictionMap (λ_ L).hom (embeddingUpIntDownIntSub (0 + n₂)) ≫
        (regradeIsoOfEq (zero_add n₂) L).hom := by
  ext k
  refine mapBifunctor.hom_ext (fun p q h ↦ ?_)
  replace h : p + q = 0 + n₂ - k := h
  rw [comp_f, restrictionMap_f, regradeIsoOfEq_hom_f]
  by_cases hp : p = 0
  · -- The summands of the regraded complexes are those of `𝟙 ⊗ L` and `L` by definition of
    -- `HomologicalComplex.restriction`.
    subst hp
    obtain rfl : q = 0 + n₂ - k := by omega
    refine (ι_regradeSingleLeftUnitor_f 0 n₂ L 0 _ k h rfl).trans ?_
    refine Eq.trans ?_ (ι_leftUnitor_hom_f_assoc L (0 + n₂ - k) _).symm
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    rfl
  · -- The source `𝟙[0]_p ⊗ L_q` is zero for `p ≠ 0`.
    exact ((tensorRight (L.X q)).map_isZero (isZero_single_obj_X _ _ _ _ hp)).eq_of_src _ _

/-- For the unit placed in chain degree `0`, the monoidal unit of chain complexes,
`ChainComplex.regradeSingleRightUnitor` is the regrading of the right unitor of chain complexes. -/
theorem regradeSingleRightUnitor_zero :
    regradeSingleRightUnitor n₁ 0 K =
      restrictionMap (ρ_ K).hom (embeddingUpIntDownIntSub (n₁ + 0)) ≫
        (regradeIsoOfEq (add_zero n₁) K).hom := by
  ext k
  refine mapBifunctor.hom_ext (fun p q h ↦ ?_)
  replace h : p + q = n₁ + 0 - k := h
  rw [comp_f, restrictionMap_f, regradeIsoOfEq_hom_f]
  by_cases hq : q = 0
  · -- The summands of the regraded complexes are those of `K ⊗ 𝟙` and `K` by definition of
    -- `HomologicalComplex.restriction`.
    subst hq
    obtain rfl : p = n₁ + 0 - k := by omega
    refine (ι_regradeSingleRightUnitor_f n₁ 0 K _ 0 k h rfl).trans ?_
    refine Eq.trans ?_ (ι_rightUnitor_hom_f_assoc K (n₁ + 0 - k) _).symm
    rfl
  · -- The source `K_p ⊗ 𝟙[0]_q` is zero for `q ≠ 0`.
    exact ((tensorLeft (K.X p)).map_isZero (isZero_single_obj_X _ _ _ _ hq)).eq_of_src _ _

/-- **The regrading of tensor products is compatible with the left unitors.** Let `𝟙[n₁]` be the
monoidal unit of `C` placed in chain degree `n₁`, whose regrading by `n₁` is the monoidal unit of
cochain complexes (`ChainComplex.regradeSingleIso`). Then comparing the tensor product of the
regradings of `𝟙[n₁]` by `n₁` and of `L` by `n₂` with the regrading of `𝟙[n₁] ⊗ L` by `n₁ + n₂`,
and applying `ChainComplex.regradeSingleLeftUnitor`, is the left unitor of cochain complexes.

On the summand `𝟙 ⊗ L_q` the comparison carries the sign `(-1)^(n₁ q)`, which is exactly the sign
of `ChainComplex.regradeSingleLeftUnitor`, so no further sign appears. For `n₁ = n₂ = 0` this is
the left unitality axiom of a lax monoidal functor
(`CategoryTheory.Functor.LaxMonoidal.left_unitality`) for the regrading by `0`, up to the
identification of the shifts, using `ChainComplex.regradeSingleLeftUnitor_zero`. For a Floer complex
`C^k = CF_(n-k)`, whose unit lies in chain degree `n`, the relevant case is `n₁ = n₂ = n`. -/
theorem regradeTensorHom_left_unitality :
    (λ_ (L.restriction (embeddingUpIntDownIntSub n₂))).hom =
      (regradeSingleIso n₁ (𝟙_ C)).inv ▷ L.restriction (embeddingUpIntDownIntSub n₂) ≫
        regradeTensorHom n₁ n₂ ((single C (down ℤ) n₁).obj (𝟙_ C)) L ≫
          regradeSingleLeftUnitor n₁ n₂ L := by
  rw [← cancel_epi (λ_ (L.restriction (embeddingUpIntDownIntSub n₂))).inv, Iso.inv_hom_id]
  ext k
  simp only [comp_f, leftUnitor_inv_f, Category.assoc, ι_whiskerRight_assoc,
    ι_regradeTensorHom_f_assoc, regradeSingleIso_inv_whiskerRight_comp_regradeSingleLeftUnitor_f,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id, id_f]

/-- **The regrading of tensor products is compatible with the right unitors, up to the sign
`(-1)^(n₁ n₂)`.** Let `𝟙[n₂]` be the monoidal unit of `C` placed in chain degree `n₂`, whose
regrading by `n₂` is the monoidal unit of cochain complexes (`ChainComplex.regradeSingleIso`).
Then comparing the tensor product of the regradings of `K` by `n₁` and of `𝟙[n₂]` by `n₂` with the
regrading of `K ⊗ 𝟙[n₂]` by `n₁ + n₂`, and applying `ChainComplex.regradeSingleRightUnitor`, is
`(-1)^(n₁ n₂)` times the right unitor of cochain complexes.

The sign is that of the comparison on the summands `K_p ⊗ 𝟙`, where the second factor sits in chain
degree `n₂`. For `n₁ = 0` or `n₂ = 0` there is no sign, and for `n₁ = n₂ = 0` this is the right
unitality axiom of a lax monoidal functor (`CategoryTheory.Functor.LaxMonoidal.right_unitality`)
for the regrading by `0`, up to the identification of the shifts, using
`ChainComplex.regradeSingleRightUnitor_zero`. For a Floer complex
`C^k = CF_(n-k)`, whose unit lies in chain degree `n`, the relevant case is `n₁ = n₂ = n`, with
the sign `(-1)^n`. -/
theorem regradeTensorHom_right_unitality :
    (ρ_ (K.restriction (embeddingUpIntDownIntSub n₁))).hom =
      (n₁ * n₂).negOnePow • (K.restriction (embeddingUpIntDownIntSub n₁) ◁
        (regradeSingleIso n₂ (𝟙_ C)).inv ≫
        regradeTensorHom n₁ n₂ K ((single C (down ℤ) n₂).obj (𝟙_ C)) ≫
          regradeSingleRightUnitor n₁ n₂ K) := by
  rw [← cancel_epi (ρ_ (K.restriction (embeddingUpIntDownIntSub n₁))).inv, Iso.inv_hom_id]
  ext k
  simp only [comp_f, units_smul_f_apply, rightUnitor_inv_f, Category.assoc, ι_whiskerLeft_assoc,
    ι_regradeTensorHom_f_assoc, whiskerLeft_regradeSingleIso_inv_comp_regradeSingleRightUnitor_f,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, whiskerLeft_inv_hom_assoc,
    Iso.inv_hom_id, id_f]

end Unitor

end ChainComplex
