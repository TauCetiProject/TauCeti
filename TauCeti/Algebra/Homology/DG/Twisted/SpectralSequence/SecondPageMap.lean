/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Continuation
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.E2
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

import TauCeti.Algebra.Homology.SpectralSequence.Basic

/-!
# Continuation maps on the second page of the index spectral sequence

Let `ν` be a continuation cocycle from a twisting cocycle `mP` on `(P, ind)` to a twisting cocycle
`mQ` on `(Q, indQ)`, with no entries strictly increasing the index, as for every continuation
cocycle over an algebra concentrated in cohomological degrees `≤ 0`
(`TauCeti.ContinuationCocycle.ν_eq_zero_of_lt_of_nonpos`). Its continuation map induces a morphism
of index spectral sequences (`TauCeti.ContinuationCocycle.indexSpectralSequenceMap`). This file
identifies this morphism on the second page with the classical continuation map.

The entries `ν x y` between generators of the same index are cycles of degree zero
(`TauCeti.ContinuationCocycle.d_ν_eq_zero_of_eq`), so they act on the cohomology of the DG module
`ℳ`. The **classical continuation map** in coefficient degree `k` is the matrix of these actions,
from the classical complex of `mP` to that of `mQ`
(`TauCeti.ContinuationCocycle.indexClassicalMap`). It is a chain map by the continuation equation
at index difference one (`TauCeti.ContinuationCocycle.d_ν_eq_sum_sub_sum_of_eq_add_one`): the two
composites differ by the action of the boundary `d (ν x y)`, which vanishes on cohomology by the
Leibniz rule.

On the first page, the morphism of spectral sequences is the map induced on the cohomology of the
graded pieces of the index filtration. On the graded piece of index `p` the continuation map is
that of the diagonal block of `ν` at `p` (`TauCeti.ContinuationCocycle.indexGradedPiece`), a
continuation cocycle between zero cocycles. So under the splitting of the first page into the
cohomology of `ℳ`, the morphism is the matrix of the actions of the entries `ν x y`
(`TauCeti.ContinuationCocycle.indexSpectralSequenceMap_hom_two_f_comp`). Passing to homology, the
morphism on the second page is the map induced by the classical continuation map on the homology
of the classical complexes
(`TauCeti.ContinuationCocycle.indexSpectralSequenceMap_hom_three_f_comp_secondPageXIso_hom`). This
comparison is what is needed to identify the second page of a direct limit of index spectral
sequences along continuation maps.

## Main definitions

* `TauCeti.ContinuationCocycle.indexClassicalEntry`: the action of an entry `ν x y` of degree zero
  on cohomology.
* `TauCeti.ContinuationCocycle.indexGradedPiece`: the diagonal block of `ν` at an index, a
  continuation cocycle between zero cocycles.
* `TauCeti.ContinuationCocycle.indexClassicalMap`: the classical continuation map between the
  classical complexes.

## Main results

* `TauCeti.ContinuationCocycle.indexSpectralSequenceMap_hom_two_f_comp`: on the first page, the
  morphism of index spectral sequences is the matrix of the actions of the entries `ν x y`.
* `TauCeti.ContinuationCocycle.indexSpectralSequenceMap_hom_three_f_comp_secondPageXIso_hom`: on
  the second page, it is the map induced on homology by the classical continuation map.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38 and Theorems 3.39, 3.49.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

namespace ContinuationCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  (hM : IsDGRightModule h ℳ dM) {ν : ContinuationCocycle mP mQ}
  (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0)

/-! ### The classical continuation map -/

/-- The entry of the classical continuation map in coefficient degree `k` between generators `x`
and `y` of the same index `q`: the action of the cycle `ν x y` of degree zero on the cohomology of
`ℳ` in degree `k`, as the cohomology of `shiftedModuleComplex hM q` in degree `k - q`. -/
noncomputable def indexClassicalEntry (k q : ℤ) (x : {x : P // ind x = q})
    (y : {y : Q // indQ y = q}) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) ⟶
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  HomologicalComplex.homologyMap (shiftedModuleComplexMul hM
    (ν.ν_mem_zero_of_eq (x.property.trans y.property.symm))
    (ν.d_ν_eq_zero_of_eq hν (x.property.trans y.property.symm)) q) (k - q)

theorem indexClassicalEntry_def (k q : ℤ) (x : {x : P // ind x = q})
    (y : {y : Q // indQ y = q}) :
    indexClassicalEntry hM hν k q x y = HomologicalComplex.homologyMap (shiftedModuleComplexMul hM
      (ν.ν_mem_zero_of_eq (x.property.trans y.property.symm))
      (ν.d_ν_eq_zero_of_eq hν (x.property.trans y.property.symm)) q) (k - q) :=
  (rfl)

/-- The classical continuation map in coefficient degree `k` and degree `q`, from the generators of
`P` of index `q` to those of `Q`: the matrix of the entries `indexClassicalEntry`. -/
noncomputable def indexClassicalHom (k q : ℤ) :
    (∏ᶜ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) ⟶
      ∏ᶜ fun _ : {y : Q // indQ y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  Pi.lift fun y ↦ ∑ x, Pi.π _ x ≫ indexClassicalEntry hM hν k q x y

/-- The components of the classical continuation map are the entries `indexClassicalEntry`. -/
@[reassoc (attr := simp)]
theorem indexClassicalHom_π (k q : ℤ) (y : {y : Q // indQ y = q}) :
    indexClassicalHom hM hν k q ≫ Pi.π _ y = ∑ x, Pi.π _ x ≫ indexClassicalEntry hM hν k q x y :=
  Pi.lift_comp_π _ _

include hM hν in
/-- The two composites of the classical continuation map with the classical differentials, on
representatives: for a cycle `α₀` of `ℳ` of degree `k`, the difference of
`∑ z, op (ν z y) • op (mP x z) • ε α₀` and `∑ z, op (mQ z y) • ε (op (ν x z) • α₀)` is
`op (d (ν x y)) • ε α₀` by the continuation equation, which is the boundary of `op (ν x y) • α₀`
by the Leibniz rule. -/
private theorem sum_op_smul_sub_sum_op_smul_eq (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : Q // indQ y = q}) {k : ℤ} {α₀ : M} (hα₀ : α₀ ∈ ℳ k) (hdα₀ : dM α₀ = 0) :
    ∑ z : {z : P // ind z = q}, op (ν.ν z y) • op (mP.m x z) •
        (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α₀ -
      ∑ z : {z : Q // indQ z = q + 1}, op (mQ.m z y) •
        (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (op (ν.ν x z) • α₀) =
      dM (op (ν.ν x y) • α₀) := by
  -- Collect each side as the action of a sum of products of entries on `ε α₀`.
  have hL : ∑ z : {z : P // ind z = q}, op (ν.ν z y) • op (mP.m x z) •
      (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α₀ =
        op (∑ z : {z : P // ind z = q}, mP.m x z * ν.ν z y) •
          (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α₀ := by
    rw [Finset.op_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun z _ ↦ by rw [op_mul, mul_smul]
  have hR : ∑ z : {z : Q // indQ z = q + 1}, op (mQ.m z y) •
      (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (op (ν.ν x z) • α₀) =
        op (∑ z : {z : Q // indQ z = q + 1}, ν.ν x z * mQ.m z y) •
          (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α₀ := by
    rw [Finset.op_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun z _ ↦ by
      rw [koszulTwist_op_smul_of_mem_zero (ν.ν_mem_zero_of_eq (x.property.trans z.property.symm))
        hα₀, op_mul, mul_smul]
  rw [hL, hR, ← sub_smul, ← MulOpposite.op_sub,
    ← ν.d_ν_eq_sum_sub_sum_of_eq_add_one hν q x.property y.property,
    hM.leibniz hα₀, hdα₀, smul_zero, zero_add,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem ℳ hα₀, one_mul, Units.smul_def,
    Int.cast_smul_eq_zsmul, smul_comm]

/-- **The classical continuation map commutes with the classical differentials, entrywise**: for
generators `x` of index `q + 1` and `y` of index `q`, the two composites agree. -/
theorem sum_indexClassicalEntry_comp (k q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : Q // indQ y = q}) :
    ∑ z : {z : P // ind z = q},
        mP.indexClassicalEntry hM k q x z ≫ indexClassicalEntry hM hν k q z y =
      ∑ z : {z : Q // indQ z = q + 1},
        indexClassicalEntry hM hν k (q + 1) x z ≫ mQ.indexClassicalEntry hM k q z y := by
  -- On a class `[α]` the two composites are the classes of `op (∑ z, mP x z * ν z y) • ε α` and
  -- `op (∑ z, ν x z * mQ z y) • ε α`, with `ε` the Koszul sign. Their difference is
  -- `op (d (ν x y)) • ε α` by the continuation equation, a boundary by the Leibniz rule.
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1)).exists_homologyπ_moduleCatCyclesMk_eq (k - (q + 1) + 1) (by simp) c
  set α₀ := (shiftedModuleComplexXEquiv hM (q + 1) _ α : M)
  have hα₀ : α₀ ∈ ℳ k := shiftedModuleComplexXEquiv_mem hM (by ring) α
  have hdα₀ : dM α₀ = 0 := (shiftedModuleComplexXEquiv_d_eq_zero_iff hM _ _ α).1 hα
  -- The entries of `mP` applied to `[α]`.
  have h1 := fun z : {z : P // ind z = q} ↦ exists_shiftedModuleComplexActHomology_homologyπ hM
    (mP.m_mem_zero_of_eq_add_one (x := x.val) (y := z.val) (by rw [x.property, z.property]))
    (mP.d_m_eq_zero_of_eq_add_one (x := x.val) (y := z.val) (by rw [x.property, z.property])) q
    (k - (q + 1)) (k - q) (by ring) α hα
  choose β hβ' hβ hβπ using h1
  -- The entries of `mQ` applied to the classes `[op (ν x z) • α]`.
  have hmul : ∀ z : {z : Q // indQ z = q + 1},
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d _ (k - (q + 1) + 1)).hom
        (((shiftedModuleComplexMul hM (ν.ν_mem_zero_of_eq (x.property.trans z.property.symm))
          (ν.d_ν_eq_zero_of_eq hν (x.property.trans z.property.symm)) (q + 1)).f _).hom α) = 0 :=
    fun z ↦ by rw [HomologicalComplex.Hom.comm_apply, hα, map_zero]
  have h2 := fun z : {z : Q // indQ z = q + 1} ↦ exists_shiftedModuleComplexActHomology_homologyπ hM
    (mQ.m_mem_zero_of_eq_add_one (x := z.val) (y := y.val) (by rw [z.property, y.property]))
    (mQ.d_m_eq_zero_of_eq_add_one (x := z.val) (y := y.val) (by rw [z.property, y.property])) q
    (k - (q + 1)) (k - q) (by ring) _ (hmul z)
  choose γ hγ' hγ hγπ using h2
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    TwistingCocycle.indexClassicalEntry_def, indexClassicalEntry_def, hβπ,
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk, hγπ]
  rw [← map_sum, ← map_sum, HomologicalComplex.sum_moduleCatCyclesMk,
    HomologicalComplex.sum_moduleCatCyclesMk]
  -- The difference of the two representatives is `dM (op (ν x y) • α₀)`.
  have hb : op (ν.ν x y) • α₀ ∈ ℳ (k - q - 1 + q) := by
    have hdeg : k - q - 1 + q = k + (indQ y - ind x) := by rw [x.property, y.property]; ring
    rw [hdeg]
    exact op_smul_mem_of_mem_graded (ν.mem_graded x y) hα₀
  refine HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d _
    ((shiftedModuleComplexXEquiv hM q _).symm ⟨_, hb⟩) ?_
  simp only [HomologicalComplex.iCycles_moduleCatCyclesMk]
  refine (shiftedModuleComplexXEquiv hM q _).injective (Subtype.ext ?_)
  have hd := shiftedModuleComplexXEquiv_d hM q (k - q - 1)
    ((shiftedModuleComplexXEquiv hM q _).symm ⟨_, hb⟩)
  rw [sub_add_cancel] at hd
  rw [hd, LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub, map_sum, map_sum,
    Submodule.coe_sum, Submodule.coe_sum]
  simp only [shiftedModuleComplexXEquiv_shiftedModuleComplexMul_f, hβ, hγ]
  exact sum_op_smul_sub_sum_op_smul_eq hM hν q x y hα₀ hdα₀

/-- The classical continuation map commutes with the classical differentials. -/
@[reassoc]
theorem indexClassicalD_comp_indexClassicalHom (k q : ℤ) :
    mP.indexClassicalD hM k q ≫ indexClassicalHom hM hν k q =
      indexClassicalHom hM hν k (q + 1) ≫ mQ.indexClassicalD hM k q := by
  refine Pi.hom_ext _ _ fun y ↦ ?_
  simp only [Category.assoc, indexClassicalHom_π, Preadditive.comp_sum,
    TwistingCocycle.indexClassicalD_π, indexClassicalHom_π_assoc,
    TwistingCocycle.indexClassicalD_π_assoc, Preadditive.sum_comp]
  rw [Finset.sum_comm, Finset.sum_comm (γ := {z : Q // indQ z = q + 1})]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, sum_indexClassicalEntry_comp]

/-- **The classical continuation map** in coefficient degree `k`: the chain map from the classical
complex of `mP` to that of `mQ` whose component in degree `q` is the matrix of the actions on the
cohomology of `ℳ` of the entries `ν x y` between generators of index `q`. -/
noncomputable def indexClassicalMap (k : ℤ) :
    mP.indexClassicalComplex hM k ⟶ mQ.indexClassicalComplex hM k where
  f q := (mP.indexClassicalComplexXIso hM k q).hom ≫ indexClassicalHom hM hν k q ≫
    (mQ.indexClassicalComplexXIso hM k q).inv
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    have hd : ∀ {S : Type uP} {indS : S → ℤ} [Fintype S] (m : TwistingCocycle 𝒜 d S indS),
        (m.indexClassicalComplex hM k).d (j + 1) j =
          (m.indexClassicalComplexXIso hM k (j + 1)).hom ≫
          m.indexClassicalD hM k j ≫ (m.indexClassicalComplexXIso hM k j).inv := fun m ↦ by
      rw [← m.indexClassicalComplexXIso_inv_comp_d_comp_hom hM k j]
      simp
    simp only [hd, Category.assoc, Iso.inv_hom_id_assoc,
      indexClassicalD_comp_indexClassicalHom_assoc]

/-- The component of the classical continuation map in degree `q` is the matrix
`indexClassicalHom`, under the identifications of the terms of the classical complexes with
products of cohomology. -/
@[reassoc (attr := simp)]
theorem indexClassicalComplexXIso_inv_comp_indexClassicalMap_f (k q : ℤ) :
    (mP.indexClassicalComplexXIso hM k q).inv ≫ (indexClassicalMap hM hν k).f q ≫
      (mQ.indexClassicalComplexXIso hM k q).hom = indexClassicalHom hM hν k q := by
  simp [indexClassicalMap]

/-! ### The graded pieces of the index filtration -/

/-- **The diagonal block of a continuation cocycle at the index `p`**: for a continuation cocycle
with no entries strictly increasing the index, the entries between the generators of index `p`
are cycles (`d_ν_eq_zero_of_eq`), so they form a continuation cocycle between the zero cocycles on
these generators. Its continuation map is the map induced by `ν` on the graded pieces of index `p`
of the index filtrations. -/
def indexGradedPiece (p : ℤ) :
    ContinuationCocycle (0 : TwistingCocycle 𝒜 d {x : P // ind x = p} fun x ↦ ind x)
      (0 : TwistingCocycle 𝒜 d {y : Q // indQ y = p} fun y ↦ indQ y) where
  ν x y := ν.ν x y
  mem_graded x y := ν.mem_graded x y
  continuation x y := by
    simp [ν.d_ν_eq_zero_of_eq hν (x.property.trans y.property.symm)]

omit [GradedAlgebra 𝒜] in
@[simp]
theorem indexGradedPiece_ν (p : ℤ) (x : {x : P // ind x = p}) (y : {y : Q // indQ y = p}) :
    (indexGradedPiece hν p).ν x y = ν.ν x y :=
  (rfl)

/-- On the graded pieces of index `p`, the continuation map followed by the evaluation at a
generator `y` is the sum over the generators `x` of the evaluations at `x` followed by the action
of `ν x y`. -/
theorem indexGradedPiece_continuationHom_comp_indexGradedPieceEval (p : ℤ)
    (y : {y : Q // indQ y = p}) :
    (indexGradedPiece hν p).continuationHom hM ≫ indexGradedPieceEval hM indQ y =
      ∑ x : {x : P // ind x = p}, indexGradedPieceEval hM ind x ≫ shiftedModuleComplexMul hM
        (ν.ν_mem_zero_of_eq (x.property.trans y.property.symm))
        (ν.d_ν_eq_zero_of_eq hν (x.property.trans y.property.symm)) p := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (shiftedModuleComplexXEquiv hM p n).injective (Subtype.ext ?_))
  rw [HomologicalComplex.sum_f, ModuleCat.hom_sum, LinearMap.sum_apply, map_sum,
    Submodule.coe_sum]
  simp only [HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply, shiftedModuleComplexXEquiv_indexGradedPieceEval_f,
    shiftedModuleComplexXEquiv_shiftedModuleComplexMul_f, continuationHom_f_apply,
    continuationMap_apply, indexGradedPiece_ν]

/-- **The continuation map on the cohomology of the graded pieces** of index `p`: under the
splittings of these cohomologies into products of the cohomology of `ℳ`, it is the classical
continuation map. -/
theorem homologyMap_continuationHom_comp_indexGradedPieceHomologyIso_hom [DecidableEq P]
    [DecidableEq Q] (k p : ℤ) :
    HomologicalComplex.homologyMap ((indexGradedPiece hν p).continuationHom hM) (k - p) ≫
        (indexGradedPieceHomologyIso hM indQ (k - p)).hom =
      (indexGradedPieceHomologyIso hM ind (k - p)).hom ≫ indexClassicalHom hM hν k p := by
  refine Pi.hom_ext _ _ fun y ↦ ?_
  rw [Category.assoc, indexGradedPieceHomologyIso_hom_π, ← HomologicalComplex.homologyMap_comp,
    indexGradedPiece_continuationHom_comp_indexGradedPieceEval, Category.assoc,
    indexClassicalHom_π, Preadditive.comp_sum]
  rw [HomologicalComplex.homologyMap_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [indexGradedPieceHomologyIso_hom_π_assoc]
  exact HomologicalComplex.homologyMap_comp _ _ _

/-- On the step `p` of the index filtration, the continuation map followed by the restriction to
the generators of index `p` is the restriction followed by the continuation map of the diagonal
block: the components from the generators of index `< p` vanish, since `ν` does not increase the
index. -/
private theorem indexFiltrationMap_app_comp_proj (p : ℤ) :
    (ν.indexFiltrationMap hM hν).app p ≫ (mQ.twistedIndexFiltrationFunctorObjIso dM hM p).hom ≫
        mQ.twistedIndexCochainComplexProj dM hM p =
      (mP.twistedIndexFiltrationFunctorObjIso dM hM p).hom ≫
        mP.twistedIndexCochainComplexProj dM hM p ≫ (indexGradedPiece hν p).continuationHom hM := by
  -- The continuation map restricted to the step `p`, as a map between the steps `p`.
  have hι : ((ν.indexFiltrationMap hM hν).app p ≫ (mQ.twistedIndexFiltrationFunctorObjIso dM hM
      p).hom) ≫ mQ.twistedIndexCochainComplexι hM p =
        (mP.twistedIndexFiltrationFunctorObjIso dM hM p).hom ≫ mP.twistedIndexCochainComplexι hM p ≫
          ν.continuationHom hM := by
    rw [Category.assoc,
      TwistingCocycle.twistedIndexFiltrationFunctorObjIso_hom_comp_indexFiltrationι,
      indexFiltrationMap_app_comp,
      TwistingCocycle.twistedIndexFiltrationFunctorObjIso_hom_comp_indexFiltrationι_assoc]
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun z ↦
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
      n).injective (Subtype.ext ?_))
  have hz := congrArg (fun φ ↦ (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM n
    ((φ.f n).hom z) : Q → M)) hι
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    TwistingCocycle.twistedIndexCochainComplexι_apply, continuationHom_f_apply] at hz
  simp only [← Category.assoc _ _ (mQ.twistedIndexCochainComplexProj dM hM p),
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    TwistingCocycle.twistedIndexCochainComplexProj_f_apply, continuationHom_f_apply]
  funext y
  set f := (mP.twistedIndexCochainComplexXEquiv hM p n
    (((mP.twistedIndexFiltrationFunctorObjIso dM hM p).hom.f n).hom z) : P → M)
  have hf : ∀ x, p < ind x → f x = 0 :=
    (mem_twistedIndexGrading_iff.mp (mP.twistedIndexCochainComplexXEquiv hM p n _).property).1
  rw [LinearMap.funLeft_apply, hz, continuationMap_apply, continuationMap_apply]
  simp only [indexGradedPiece_ν, LinearMap.funLeft_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun x ↦ ind x = p) (by simp)
    fun x ↦ op (ν.ν x y) • f x]
  refine (Finset.sum_filter_of_ne fun x _ hx ↦ ?_).symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hx (by rw [hν x y (by rw [y.property]; exact hlt), MulOpposite.op_zero, zero_smul])
  · exact hx (by rw [hf x hgt, smul_zero])

/-- On the graded pieces `F_p / F_q`, for `q + 1 = p`, the map induced by the continuation map is
the continuation map of the diagonal block of `ν` at `p`. -/
private theorem cokernel_map_comp_twistedIndexCokernelIsoOfEq_hom (q p : ℤ) (hqp : q + 1 = p) :
    cokernel.map _ _ ((ν.indexFiltrationMap hM hν).app q) ((ν.indexFiltrationMap hM hν).app p)
        ((ν.indexFiltrationMap hM hν).naturality _).symm ≫
        (mQ.twistedIndexCokernelIsoOfEq dM hM q p hqp).hom =
      (mP.twistedIndexCokernelIsoOfEq dM hM q p hqp).hom ≫
        (indexGradedPiece hν p).continuationHom hM := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  simp only [cokernel.π_desc_assoc, Category.assoc,
    TwistingCocycle.cokernel_π_comp_twistedIndexCokernelIsoOfEq_hom,
    TwistingCocycle.cokernel_π_comp_twistedIndexCokernelIsoOfEq_hom_assoc]
  exact indexFiltrationMap_app_comp_proj hM hν p

/-! ### The first and second pages -/

variable [DecidableEq P] [DecidableEq Q]

/-- **The morphism of index spectral sequences of a continuation cocycle on the first page**:
under the identifications of the first pages with products of the cohomology of `ℳ`
(`indexSpectralSequenceFirstPageXIsoOfEq` followed by `indexGradedPieceHomologyIso`), it is the
classical continuation map `indexClassicalHom`, the matrix of the actions of the entries `ν x y`
between generators of index `q`. The indices are given with equations, as in
`indexSpectralSequenceFirstPageXIsoOfEq`. -/
theorem indexSpectralSequenceMap_hom_two_f_comp (k : ℤ) (pq : ℤ × ℤ) (i₁ q : ℤ)
    (hi₁ : i₁ = pq.2) (hq : q = pq.2 + 1) (hn : k - q = pq.1 + pq.2) :
    ((ν.indexSpectralSequenceMap hM hν).hom 2).f pq ≫
        (mQ.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq i₁ q hi₁ hq _ hn ≪≫
          indexGradedPieceHomologyIso hM indQ _).hom =
      (mP.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq i₁ q hi₁ hq _ hn ≪≫
          indexGradedPieceHomologyIso hM ind _).hom ≫ indexClassicalHom hM hν k q := by
  simp only [Iso.trans_hom, TwistingCocycle.indexSpectralSequenceFirstPageXIsoOfEq_eq,
    HomologicalComplex.homologyMapIso_hom, Category.assoc]
  rw [indexSpectralSequenceMap_eq,
    CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, cokernel_map_comp_twistedIndexCokernelIsoOfEq_hom,
    HomologicalComplex.homologyMap_comp_assoc,
    homologyMap_continuationHom_comp_indexGradedPieceHomologyIso_hom]

/-- On the short complexes of the first pages computing the second pages, the morphism of index
spectral sequences is the classical continuation map, under the identifications
`indexSecondPageShortComplexIso`. -/
private theorem indexSecondPageShortComplexIso_hom_naturality (a b : ℤ) :
    (HomologicalComplex.shortComplexFunctor' _ _ (a - 2, b + 1) (a, b) (a + 2, b - 1)).map
        ((ν.indexSpectralSequenceMap hM hν).hom 2) ≫
        (mQ.indexSecondPageShortComplexIso hM a b).hom =
      (mP.indexSecondPageShortComplexIso hM a b).hom ≫
        (HomologicalComplex.shortComplexFunctor' _ _ (b + 1 + 1) (b + 1) b).map
          (indexClassicalMap hM hν (a + 2 * b + 1)) := by
  have key : ∀ (q : ℤ) {XP XQ : ModuleCat.{max uM uP} R} (f : XP ⟶ XQ)
      (eP : XP ⟶ (mP.indexClassicalComplex hM (a + 2 * b + 1)).X q)
      (eQ : XQ ⟶ (mQ.indexClassicalComplex hM (a + 2 * b + 1)).X q)
      (FP : XP ⟶ ∏ᶜ fun _ : {x : P // ind x = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (a + 2 * b + 1 - q))
      (FQ : XQ ⟶ ∏ᶜ fun _ : {y : Q // indQ y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (a + 2 * b + 1 - q)),
      eP ≫ (mP.indexClassicalComplexXIso hM (a + 2 * b + 1) q).hom = FP →
      eQ ≫ (mQ.indexClassicalComplexXIso hM (a + 2 * b + 1) q).hom = FQ →
      f ≫ FQ = FP ≫ indexClassicalHom hM hν (a + 2 * b + 1) q →
      f ≫ eQ = eP ≫ (indexClassicalMap hM hν (a + 2 * b + 1)).f q := by
    intro q XP XQ f eP eQ FP FQ hP hQ hf
    rw [← cancel_mono (mQ.indexClassicalComplexXIso hM (a + 2 * b + 1) q).hom, Category.assoc, hQ,
      hf, ← hP, Category.assoc, Category.assoc,
      ← indexClassicalComplexXIso_inv_comp_indexClassicalMap_f, Iso.hom_inv_id_assoc]
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact key _ _ _ _ _ _ (mP.indexSecondPageShortComplexIso_hom_τ₁ hM a b)
      (mQ.indexSecondPageShortComplexIso_hom_τ₁ hM a b)
      (indexSpectralSequenceMap_hom_two_f_comp hM hν _ (a - 2, b + 1) (b + 1) (b + 1 + 1) rfl rfl
        (by dsimp only; ring))
  · exact key _ _ _ _ _ _ (mP.indexSecondPageShortComplexIso_hom_τ₂ hM a b)
      (mQ.indexSecondPageShortComplexIso_hom_τ₂ hM a b)
      (indexSpectralSequenceMap_hom_two_f_comp hM hν _ (a, b) b (b + 1) rfl rfl
        (by dsimp only; ring))
  · exact key _ _ _ _ _ _ (mP.indexSecondPageShortComplexIso_hom_τ₃ hM a b)
      (mQ.indexSecondPageShortComplexIso_hom_τ₃ hM a b)
      (indexSpectralSequenceMap_hom_two_f_comp hM hν _ (a + 2, b - 1) (b - 1) b rfl
        (by dsimp only; ring) (by dsimp only; ring))

/-- The map induced on the homology of the first page at `(a, b)` is that of the classical
continuation map, under the identifications of `indexSpectralSequenceSecondPageXIso`. -/
private theorem homologyMap_indexSpectralSequenceMap_hom_two_comp (a b : ℤ) :
    HomologicalComplex.homologyMap ((ν.indexSpectralSequenceMap hM hν).hom 2) (a, b) ≫
      (((mQ.indexSpectralSequence dM hM).page 2).homologyIsoSc' (a - 2, b + 1) (a, b)
        (a + 2, b - 1)
        ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
        ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega)))).hom ≫
      ShortComplex.homologyMap (mQ.indexSecondPageShortComplexIso hM a b).hom ≫
      ((mQ.indexClassicalComplex hM (a + 2 * b + 1)).homologyIsoSc' (b + 1 + 1) (b + 1) b
        (by simp) (by simp)).inv =
    (((mP.indexSpectralSequence dM hM).page 2).homologyIsoSc' (a - 2, b + 1) (a, b)
        (a + 2, b - 1)
        ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
        ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega)))).hom ≫
      ShortComplex.homologyMap (mP.indexSecondPageShortComplexIso hM a b).hom ≫
      ((mP.indexClassicalComplex hM (a + 2 * b + 1)).homologyIsoSc' (b + 1 + 1) (b + 1) b
        (by simp) (by simp)).inv ≫
      HomologicalComplex.homologyMap (indexClassicalMap hM hν (a + 2 * b + 1)) (b + 1) := by
  rw [HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom_assoc,
    ← ShortComplex.homologyMap_comp_assoc, indexSecondPageShortComplexIso_hom_naturality,
    ShortComplex.homologyMap_comp_assoc]
  congr 2
  rw [Iso.comp_inv_eq, Category.assoc, HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom,
    Iso.inv_hom_id_assoc]

/-- **The morphism of index spectral sequences of a continuation cocycle on the second page is the
classical continuation map** (BDHO, Theorem 3.39 and the proof of Theorem 3.49): under the
identifications `indexSpectralSequenceSecondPageXIso` of the second pages with the homology of the
classical complexes, the morphism at `(a, b)` is the map induced on homology in degree `b + 1` by
the classical continuation map in coefficient degree `a + 2 * b + 1`. -/
theorem indexSpectralSequenceMap_hom_three_f_comp_secondPageXIso_hom (a b : ℤ) :
    ((ν.indexSpectralSequenceMap hM hν).hom 3).f (a, b) ≫
        (mQ.indexSpectralSequenceSecondPageXIso hM a b).hom =
      (mP.indexSpectralSequenceSecondPageXIso hM a b).hom ≫
        HomologicalComplex.homologyMap (indexClassicalMap hM hν (a + 2 * b + 1)) (b + 1) := by
  rw [TwistingCocycle.indexSpectralSequenceSecondPageXIso_eq,
    TwistingCocycle.indexSpectralSequenceSecondPageXIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom, Category.assoc]
  -- The placeholders make the rewrite reuse the goal's proofs of the page-number conditions.
  rw [SpectralSequence.Hom.hom_f_comp_iso_inv_assoc _ _ _ _ _ _,
    homologyMap_indexSpectralSequenceMap_hom_two_comp]

end ContinuationCocycle

end TauCeti
