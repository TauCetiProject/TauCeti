/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.Coalgebra.Comodule.RestrictScalars
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.RingTheory.TensorProduct.Basic

/-!
# The tautological representation of the Deligne torus

The Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` acts on the real vector space `ℂ` by multiplication: its
points over a commutative `ℝ`-algebra `R` are the units of `ℂ ⊗[ℝ] R`
(`TauCeti.DeligneTorus.pointsMulEquiv`), and these act on `R ⊗[ℝ] ℂ ≃ ℂ ⊗[ℝ] R` by
multiplication. On real points `z ∈ S(ℝ) = ℂˣ` this is `v ↦ z * v`. This is the representation
`H₁(E, ℝ)` of an elliptic curve `E = ℂ / Λ`, with `Λ ⊗ ℝ = ℂ`.

As a comodule, the representation is built from the universal point `u` of `S`, a unit of
`ℂ ⊗[ℝ] S` that is group-like over `ℂ`
(`TauCeti.Algebra.WeilRestriction.isGroupLikeElem_multiplicativeGroupPoints_toConv`). The
one-dimensional `ℂ ⊗[ℝ] S`-comodule `ℂ` with coaction `v ↦ v ⊗ u` restricts to an `S`-comodule over
`ℝ` (`TauCeti.Comodule.restrictScalars`).

Its complexification `ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ`, `a ⊗ v ↦ (a * v, a * conj v)`
(`TauCeti.DeligneTorus.tautologicalSplitting`), is the sum of two lines: a point with coordinates
`(z₁, z₂)` acts on the first by `z₁` and on the second by `z₂`. In the homology convention of
`TauCeti.DeligneTorus.hodgeComponent` the first line is `V^{-1,0}`, the second is `V^{0,-1}`, and
these are the only Hodge types. So the tautological representation is the real Hodge structure of
weight `-1` of elliptic homology, and the cocharacter `μ(z) = (z, 1)` acts on its two Hodge
components with exponents `1` and `0`.

## Main definitions

* `TauCeti.DeligneTorus.universalGroupLike`: the universal point of `S`, as a group-like element
  of the `ℂ`-coalgebra `ℂ ⊗[ℝ] S`.
* `TauCeti.DeligneTorus.tautologicalComodule`: the `S`-comodule structure on `ℂ`.
* `TauCeti.DeligneTorus.tautologicalSplitting`: the splitting `ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ` of its
  complexification.

## Main results

* `TauCeti.DeligneTorus.comm_endOfPoint_tautologicalComodule`: a point `g` of `S` acts on
  `R ⊗[ℝ] ℂ ≃ ℂ ⊗[ℝ] R` by multiplication by its unit `pointsMulEquiv R g`.
* `TauCeti.DeligneTorus.endOfPoint_real_tautologicalComodule`: a real point `z ∈ ℂˣ` acts on `ℂ`
  by multiplication by `z`.
* `TauCeti.DeligneTorus.mem_hodgeComponent_tautologicalComodule_iff`: the Hodge components of
  the tautological representation.
* `TauCeti.DeligneTorus.hodgeComponent_tautologicalComodule_ne_bot_iff`: its Hodge types are
  exactly `(-1, 0)` and `(0, -1)`.
* `TauCeti.DeligneTorus.isHodgeDecomposition_tautologicalComodule`: its Hodge components form a
  Hodge decomposition of weight `-1`.
* `TauCeti.DeligneTorus.endOfPoint_mu_of_mem_hodgeComponent_tautologicalComodule_neg_one_zero` and
  `TauCeti.DeligneTorus.endOfPoint_mu_of_mem_hodgeComponent_tautologicalComodule_zero_neg_one`:
  `μ(z)` acts on `V^{-1,0}` by `z` and on `V^{0,-1}` trivially.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The comodule -/

/-- The universal point of `S` is group-like over `ℂ`. -/
theorem isGroupLikeElem_pointsMulEquiv_id :
    IsGroupLikeElem ℂ (pointsMulEquiv S (toConv (AlgHom.id ℝ S)) : ℂ ⊗[ℝ] S) := by
  have h := WeilRestriction.isGroupLikeElem_multiplicativeGroupPoints_toConv (A := ℝ) (B := ℂ)
    (BialgHom.id ℝ S)
  rwa [WeilRestriction.multiplicativeGroupPoints_apply, ofConv_toConv, BialgHom.id_toAlgHom,
    ← ofConv_toConv (AlgHom.id ℝ S), ← coe_pointsMulEquiv] at h

/-- **The universal point of `S`**, the unit of `ℂ ⊗[ℝ] S` attached to the identity of `S`, as a
group-like element of the `ℂ`-coalgebra `ℂ ⊗[ℝ] S`. -/
noncomputable def universalGroupLike : GroupLike ℂ (ℂ ⊗[ℝ] S) :=
  ⟨pointsMulEquiv S (toConv (AlgHom.id ℝ S)), isGroupLikeElem_pointsMulEquiv_id⟩

/-- The element underlying the universal group-like element is the unit of the identity point. -/
@[simp]
theorem val_universalGroupLike :
    (universalGroupLike : ℂ ⊗[ℝ] S) = pointsMulEquiv S (toConv (AlgHom.id ℝ S)) :=
  (rfl)

/-- **The universal property of the universal point**: the unit attached to a point `g` of `S`
with values in `R` is the image of the universal point under `ℂ ⊗ g`. -/
theorem lTensor_universalGroupLike {R : Type*} [CommRing R] [Algebra ℝ R]
    (g : WithConv (S →ₐ[ℝ] R)) :
    Algebra.TensorProduct.lTensor (S := ℂ) ℂ g.ofConv (universalGroupLike : ℂ ⊗[ℝ] S) =
      pointsMulEquiv R g := by
  -- `g` is the image of the identity point of `S` under post-composition with `g`
  have h := pointsMulEquiv_mapValue g.ofConv (toConv (AlgHom.id ℝ S))
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv] at h
  rw [h, Units.coe_map, MonoidHom.coe_ofClass, val_universalGroupLike]

/-- **The tautological representation of the Deligne torus** on `ℂ`, as an `S`-comodule: the
restriction to `ℝ` of the `ℂ ⊗[ℝ] S`-comodule `ℂ` with coaction `v ↦ v ⊗ u`, for the universal
point `u` of `S`. A point of `S` acts by multiplication by its unit
(`comm_endOfPoint_tautologicalComodule`). -/
@[instance_reducible]
noncomputable def tautologicalComodule : Comodule ℝ S ℂ :=
  letI := Comodule.groupLike (R := ℂ) (C := ℂ ⊗[ℝ] S) (M := ℂ) universalGroupLike
  Comodule.restrictScalars (R := ℝ) (A := ℂ) (C := S) (M := ℂ)

/-- The coaction of the tautological comodule is `v ↦ v ⊗ u`, read in `ℂ ⊗[ℝ] S` through
`ℂ ⊗[ℂ] (ℂ ⊗[ℝ] S) ≃ ℂ ⊗[ℝ] S`. -/
theorem tautologicalComodule_coact_apply (v : ℂ) :
    tautologicalComodule.coact v =
      TensorProduct.AlgebraTensorModule.cancelBaseChange ℝ ℂ ℂ ℂ S
        (v ⊗ₜ[ℂ] (universalGroupLike : ℂ ⊗[ℝ] S)) := by
  let _ := Comodule.groupLike (R := ℂ) (C := ℂ ⊗[ℝ] S) (M := ℂ) universalGroupLike
  rw [tautologicalComodule, Comodule.restrictScalars_coact, Comodule.restrictScalarsCoact_apply,
    Comodule.groupLike_coact_apply]

/-- The point action of the tautological comodule at a point `g`, on a pure tensor, as a
computation with an arbitrary element `t` in place of the universal point. -/
private theorem comm_smul_comm_lTensor_cancelBaseChange {R : Type*} [CommRing R] [Algebra ℝ R]
    (g : S →ₐ[ℝ] R) (a : R) (v : ℂ) (t : ℂ ⊗[ℝ] S) :
    Algebra.TensorProduct.comm ℝ R ℂ (a • TensorProduct.comm ℝ ℂ R
        (LinearMap.lTensor ℂ g.toLinearMap
          (TensorProduct.AlgebraTensorModule.cancelBaseChange ℝ ℂ ℂ ℂ S (v ⊗ₜ[ℂ] t)))) =
      Algebra.TensorProduct.lTensor (S := ℂ) ℂ g t * (v ⊗ₜ[ℝ] a) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, smul_add, add_mul, ht, ht']
  | tmul c s =>
    simp [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

/-- **A point of `S` acts on the tautological representation by multiplication**: a point `g`
with values in `R` acts on `R ⊗[ℝ] ℂ ≃ ℂ ⊗[ℝ] R` by multiplication by its unit
`pointsMulEquiv R g`. -/
theorem comm_endOfPoint_tautologicalComodule {R : Type*} [CommRing R] [Algebra ℝ R]
    (g : WithConv (S →ₐ[ℝ] R)) (y : R ⊗[ℝ] ℂ) :
    letI := tautologicalComodule
    Algebra.TensorProduct.comm ℝ R ℂ (Comodule.endOfPoint ℂ g.ofConv y) =
      pointsMulEquiv R g * Algebra.TensorProduct.comm ℝ R ℂ y := by
  let _ := tautologicalComodule
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
  | tmul a v =>
    rw [Comodule.endOfPoint_tmul, tautologicalComodule_coact_apply,
      comm_smul_comm_lTensor_cancelBaseChange, lTensor_universalGroupLike,
      Algebra.TensorProduct.comm_tmul]

/-- **A real point `z ∈ S(ℝ) = ℂˣ` acts on `ℂ` by multiplication by `z`.** -/
theorem endOfPoint_real_tautologicalComodule (f : WithConv (S →ₐ[ℝ] ℝ)) (v : ℂ) :
    letI := tautologicalComodule
    Comodule.endOfPoint ℂ f.ofConv (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (realPointsMulEquiv f * v) := by
  let _ := tautologicalComodule
  apply (Algebra.TensorProduct.comm ℝ ℝ ℂ).injective
  rw [comm_endOfPoint_tautologicalComodule]
  apply (Algebra.TensorProduct.rid ℝ ℝ ℂ).injective
  simp [coe_realPointsMulEquiv]

/-! ### The Hodge decomposition -/

/-- **The splitting of the complexified tautological representation**:
`ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ`, `a ⊗ v ↦ (a * v, a * conj v)`, where `a` is the coefficient and `v` the
vector. Its first component is `V^{-1,0}` and its second `V^{0,-1}`
(`mem_hodgeComponent_tautologicalComodule_iff`). -/
noncomputable def tautologicalSplitting : ℂ ⊗[ℝ] ℂ ≃ₐ[ℝ] ℂ × ℂ :=
  (Algebra.TensorProduct.comm ℝ ℂ ℂ).trans (complexTensorProductEquivProd ℂ)

@[simp]
theorem tautologicalSplitting_tmul (a v : ℂ) :
    tautologicalSplitting (a ⊗ₜ[ℝ] v) = (a * v, a * starRingEnd ℂ v) := by
  simp [tautologicalSplitting, mul_comm]

section Complex

-- The real structure of `R` is the one induced from `ℂ`, as in
-- `endOfPoint_rTensor_of_mem_hodgeComponent`.
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The splitting of the image of `v ∈ ℂ ⊗[ℝ] ℂ` in `R ⊗[ℝ] ℂ` is the image of the splitting of
`v`. -/
private theorem complexTensorProductEquivProd_comm_rTensor (v : ℂ ⊗[ℝ] ℂ) :
    complexTensorProductEquivProd R (Algebra.TensorProduct.comm ℝ R ℂ
        (LinearMap.rTensor ℂ (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v)) =
      (algebraMap ℂ R (tautologicalSplitting v).1,
        algebraMap ℂ R (tautologicalSplitting v).2) := by
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp only [map_add, hv, hv', Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  | tmul a b => simp [Algebra.smul_def, mul_comm]

end Complex

private theorem algebraMap_monoidAlgebra (s : ℂ) :
    algebraMap ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) s = MonoidAlgebra.single 1 s := by
  simp [MonoidAlgebra.coe_algebraMap]

/-- **The Hodge components of the tautological representation.** A vector `v` of `ℂ ⊗[ℝ] ℂ` lies
in `V^{p,q}` exactly when the first component of its splitting vanishes unless
`(p, q) = (-1, 0)`, and the second vanishes unless `(p, q) = (0, -1)`. -/
theorem mem_hodgeComponent_tautologicalComodule_iff {p q : ℤ} {v : ℂ ⊗[ℝ] ℂ} :
    letI := tautologicalComodule
    v ∈ hodgeComponent ℂ p q ↔
      ((p, q) ≠ (-1, 0) → (tautologicalSplitting v).1 = 0) ∧
        ((p, q) ≠ (0, -1) → (tautologicalSplitting v).2 = 0) := by
  let _ := tautologicalComodule
  let Φ := (Algebra.TensorProduct.comm ℝ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) ℂ).trans
    (complexTensorProductEquivProd _)
  rw [mem_hodgeComponent_iff, ← Φ.injective.eq_iff]
  simp only [Φ, AlgEquiv.trans_apply, comm_endOfPoint_tautologicalComodule,
    Algebra.TensorProduct.comm_smul_left, map_mul]
  rw [complexTensorProductEquivProd_comm_rTensor,
    complexTensorProductEquivProd_pointsMulEquiv_splittingPoint, complexTensorProductEquivProd_tmul]
  simp only [Prod.mk_mul_mk, Prod.mk.injEq, map_one, one_smul, algebraMap_monoidAlgebra,
    MonoidAlgebra.single_mul_single, one_mul, mul_one, MonoidAlgebra.single_inj, and_true,
    and_self, EmbeddingLike.apply_eq_iff_eq, ne_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun hpq ↦ h₁.resolve_left (by omega), fun hpq ↦ h₂.resolve_left (by omega)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · by_cases hpq : p = -1 ∧ q = 0
      · exact Or.inl (by omega)
      · exact Or.inr (h₁ (by omega))
    · by_cases hpq : p = 0 ∧ q = -1
      · exact Or.inl (by omega)
      · exact Or.inr (h₂ (by omega))

section Types

attribute [local instance] tautologicalComodule

/-- **The Hodge types of the tautological representation** are exactly `(-1, 0)` and `(0, -1)`:
this is the Hodge type of the homology `H₁(E, ℝ)` of an elliptic curve. -/
theorem hodgeComponent_tautologicalComodule_ne_bot_iff (p q : ℤ) :
    hodgeComponent ℂ p q ≠ ⊥ ↔ (p = -1 ∧ q = 0) ∨ (p = 0 ∧ q = -1) := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hv0⟩
    rw [mem_hodgeComponent_tautologicalComodule_iff] at hv
    by_contra h
    refine hv0 (tautologicalSplitting.injective ?_)
    rw [map_zero]
    exact Prod.ext (hv.1 fun e ↦ h (Or.inl (Prod.mk.inj e)))
      (hv.2 fun e ↦ h (Or.inr (Prod.mk.inj e)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨tautologicalSplitting.symm (1, 0), ?_, fun h ↦ ?_⟩
      · rw [mem_hodgeComponent_tautologicalComodule_iff]
        simp
      · simpa using congrArg tautologicalSplitting h
    · refine ⟨tautologicalSplitting.symm (0, 1), ?_, fun h ↦ ?_⟩
      · rw [mem_hodgeComponent_tautologicalComodule_iff]
        simp
      · simpa using congrArg tautologicalSplitting h

/-- **The tautological representation is pure of weight `-1`**: the components
`p ↦ V^{p, -1 - p}` form a Hodge decomposition of weight `-1` of `ℂ ⊗[ℝ] ℂ`. -/
theorem isHodgeDecomposition_tautologicalComodule :
    Hodge.IsHodgeDecomposition (Hodge.complexificationConjugation ℂ) (-1)
      fun p ↦ hodgeComponent ℂ p (-1 - p) := by
  refine isHodgeDecomposition_hodgeComponent fun p q hpq ↦ ?_
  by_contra h
  rw [← ne_eq, hodgeComponent_tautologicalComodule_ne_bot_iff] at h
  omega

section Mu

-- The real structure of `R` is the one induced from `ℂ`, as in
-- `endOfPoint_rTensor_of_mem_hodgeComponent`.
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- **`μ` acts on `V^{-1,0}` with exponent `1`**: the point `μ(z) = (z, 1)` of `S` acts on the
Hodge component `V^{-1,0}` of the tautological representation by `z`. -/
theorem endOfPoint_mu_of_mem_hodgeComponent_tautologicalComodule_neg_one_zero (z : Rˣ)
    {v : ℂ ⊗[ℝ] ℂ} (hv : v ∈ hodgeComponent ℂ (-1) 0) :
    Comodule.endOfPoint ℂ (mu R z).ofConv
        (LinearMap.rTensor ℂ (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v) =
      (z : R) • LinearMap.rTensor ℂ (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v := by
  rw [endOfPoint_rTensor_of_mem_hodgeComponent _ hv, characterGroup_mu, neg_neg, zpow_one]

/-- **`μ` acts on `V^{0,-1}` with exponent `0`**: the point `μ(z) = (z, 1)` of `S` acts trivially
on the Hodge component `V^{0,-1}` of the tautological representation. -/
theorem endOfPoint_mu_of_mem_hodgeComponent_tautologicalComodule_zero_neg_one (z : Rˣ)
    {v : ℂ ⊗[ℝ] ℂ} (hv : v ∈ hodgeComponent ℂ 0 (-1)) :
    Comodule.endOfPoint ℂ (mu R z).ofConv
        (LinearMap.rTensor ℂ (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v) =
      LinearMap.rTensor ℂ (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v := by
  rw [endOfPoint_rTensor_of_mem_hodgeComponent _ hv, characterGroup_mu, neg_zero, zpow_zero,
    Units.val_one, one_smul]

end Mu

end Types

end TauCeti.DeligneTorus
