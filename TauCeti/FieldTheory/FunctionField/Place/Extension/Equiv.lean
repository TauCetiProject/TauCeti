/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Ramification under field isomorphisms

The ramification index depends on the extension, not on its presentation as a field carrier:
transporting a place of the upstairs field along an isomorphism over the downstairs field does not
change its ramification index. This allows an extension to be placed in a finite Galois overfield
without changing its ramification behaviour.

More generally, a commutative square of semilinear isomorphisms, `σK : K ≃+* K'` below and
`τ : L ≃+* L'` above, carrying the constants `k` onto `k'` along `σ`, carries the place of `L` over
`P` to a place of `L'` over the transport of `P`, with the same ramification index and the same
relative degree (`TauCeti.Place.restrict_equivOfRingEquiv`,
`TauCeti.Place.ramificationIdx_equivOfRingEquiv_of_comm` and
`TauCeti.Place.relativeDegree_equivOfRingEquiv_of_comm`). The constants need not be fixed, so this
is how a Galois automorphism of the constants acts on the places of a base-changed extension.

Over the identity of the constants these are `TauCeti.Place.restrict_map`,
`TauCeti.Place.ramificationIdx_map` and `TauCeti.Place.relativeDegree_map`, for `k`-algebra
isomorphisms. With `K = K'` and `L = L'` as fields, this is how a change of the embedding of the
base field by an automorphism moves places and their ramification.
-/

public section

namespace TauCeti.Place

section Semilinear

variable {k k' K K' L L' : Type*} [Field k] [Field k'] [Field K] [Field K'] [Field L] [Field L']
  [Algebra k L] [Algebra k' L'] [Algebra K L] [Algebra K' L']
  (σ : k ≃+* k') (τ : L ≃+* L') (h : ∀ c, τ (algebraMap k L c) = algebraMap k' L' (σ c))
  (σK : K ≃+* K') (hK : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σK x))

include hK in
/-- **The ramification index is invariant under a commutative square of semilinear
isomorphisms**: if `τ : L ≃+* L'` carries the image of `K` onto the image of `K'` along
`σK : K ≃+* K'`, then transporting a place of `L` along `τ` does not change its ramification
index. -/
theorem ramificationIdx_equivOfRingEquiv_of_comm (Q : Place k L) :
    ramificationIdx K' (equivOfRingEquiv σ τ h Q) = ramificationIdx K Q := by
  have hc : (equivOfRingEquiv σ τ h Q).valuation.comap (algebraMap K' L') =
      (Q.valuation.comap (algebraMap K L)).comap (σK.symm : K' →+* K) := by
    ext x
    simp [τ.symm_apply_eq.mpr (by rw [hK, σK.apply_symm_apply] :
      algebraMap K' L' x = τ (algebraMap K L (σK.symm x)))]
  rw [ramificationIdx_def, ramificationIdx_def, hc,
    Valuation.ordIndex_comap_of_surjective _ σK.symm.surjective]

include hK in
/-- **Restriction commutes with a commutative square of semilinear isomorphisms**: if
`τ : L ≃+* L'` carries the image of `K` onto the image of `K'` along `σK : K ≃+* K'`, which
carries the constants along `σ`, then the transport of a place `Q` of `L` lies over the transport
of the place below `Q`. -/
theorem restrict_equivOfRingEquiv [Algebra k K] [Algebra k' K'] [IsScalarTower k K L]
    [IsScalarTower k' K' L'] [Algebra.IsIntegral K L] [Algebra.IsIntegral K' L']
    (hσK : ∀ c, σK (algebraMap k K c) = algebraMap k' K' (σ c)) (Q : Place k L) :
    (equivOfRingEquiv σ τ h Q).restrict k' K' = equivOfRingEquiv σ σK hσK (Q.restrict k K) := by
  rw [restrict_eq_iff_integers_le]
  intro f hf
  rw [mem_integers_iff, valuation_equivOfRingEquiv, ← mem_integers_iff,
    mem_integers_restrict_iff] at hf
  rwa [mem_integers_iff, valuation_equivOfRingEquiv, ← mem_integers_iff,
    τ.symm_apply_eq.mpr (by rw [hK, σK.apply_symm_apply] :
      algebraMap K' L' f = τ (algebraMap K L (σK.symm f)))]

include hK in
/-- **The valuation ring equivalence for the restricted place along a commuting square**:
if `τ : L ≃+* L'` carries the image of `K` onto the image of `K'` along `σK : K ≃+* K'`, then
`σK` identifies the valuation ring of `Q.restrict k K` with that of
`(equivOfRingEquiv σ τ h Q).restrict k' K'`. -/
noncomputable def integersEquivRestrictOfRingEquiv [Algebra k K] [Algebra k' K']
    [IsScalarTower k K L] [IsScalarTower k' K' L'] [Algebra.IsIntegral K L]
    [Algebra.IsIntegral K' L'] (Q : Place k L) :
    (Q.restrict k K).integers ≃+* ((equivOfRingEquiv σ τ h Q).restrict k' K').integers :=
  have hσK : ∀ c, σK (algebraMap k K c) = algebraMap k' K' (σ c) := fun c ↦
    (algebraMap K' L').injective (by
      rw [← hK, ← IsScalarTower.algebraMap_apply k K L, h, IsScalarTower.algebraMap_apply k' K' L'])
  have hr := restrict_equivOfRingEquiv σ τ h σK hK hσK Q
  (integersEquivOfRingEquiv σ σK hσK (Q.restrict k K)).trans
    (RingEquiv.subringCongr (congrArg (fun P ↦ P.integers.toSubring) hr.symm))

include hK in
/-- Coercion formula for `integersEquivRestrictOfRingEquiv`: it acts on underlying field elements as
`σK`. -/
@[simp]
theorem coe_integersEquivRestrictOfRingEquiv [Algebra k K] [Algebra k' K']
    [IsScalarTower k K L] [IsScalarTower k' K' L'] [Algebra.IsIntegral K L]
    [Algebra.IsIntegral K' L'] (Q : Place k L) (x : (Q.restrict k K).integers) :
    ((integersEquivRestrictOfRingEquiv σ τ h σK hK Q x : K')) = σK x := by
  dsimp only [integersEquivRestrictOfRingEquiv]
  rw [RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply, coe_integersEquivOfRingEquiv]

include hK in
/-- **The commuting residue-field square along a commutative square of semilinear isomorphisms**:
the residue-field maps induced by `integersEquivRestrictOfRingEquiv` below and
`integersEquivOfRingEquiv` above commute with the residue-field embeddings. -/
theorem residueField_comm_equivOfRingEquiv [Algebra k K] [Algebra k' K']
    [IsScalarTower k K L] [IsScalarTower k' K' L'] [Algebra.IsIntegral K L]
    [Algebra.IsIntegral K' L'] (Q : Place k L) :
    (algebraMap ((equivOfRingEquiv σ τ h Q).restrict k' K').ResidueField
        (equivOfRingEquiv σ τ h Q).ResidueField).comp
      (IsLocalRing.ResidueField.mapEquiv
        (integersEquivRestrictOfRingEquiv σ τ h σK hK Q)).toRingHom =
      (IsLocalRing.ResidueField.mapEquiv (integersEquivOfRingEquiv σ τ h Q)).toRingHom.comp
        (algebraMap (Q.restrict k K).ResidueField Q.ResidueField) := by
  have hring :
      (algebraMap ((equivOfRingEquiv σ τ h Q).restrict k' K').integers
          (equivOfRingEquiv σ τ h Q).integers).comp
        (integersEquivRestrictOfRingEquiv σ τ h σK hK Q : _ →+* _) =
      (integersEquivOfRingEquiv σ τ h Q : _ →+* _).comp
        (algebraMap (Q.restrict k K).integers Q.integers) := by
    ext x
    simp [hK]
  have halg {P : Place k L} [Algebra k K] [IsScalarTower k K L] [Algebra.IsIntegral K L] :
      algebraMap (P.restrict k K).ResidueField P.ResidueField =
        IsLocalRing.ResidueField.map (algebraMap (P.restrict k K).integers P.integers) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  have halg' {P' : Place k' L'} [Algebra k' K'] [IsScalarTower k' K' L']
      [Algebra.IsIntegral K' L'] :
      algebraMap (P'.restrict k' K').ResidueField P'.ResidueField =
        IsLocalRing.ResidueField.map (algebraMap (P'.restrict k' K').integers P'.integers) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  have h1 :
      (IsLocalRing.ResidueField.mapEquiv
        (integersEquivRestrictOfRingEquiv σ τ h σK hK Q)).toRingHom =
      IsLocalRing.ResidueField.map (integersEquivRestrictOfRingEquiv σ τ h σK hK Q : _ →+* _) :=
    rfl
  have h2 :
      (IsLocalRing.ResidueField.mapEquiv (integersEquivOfRingEquiv σ τ h Q)).toRingHom =
      IsLocalRing.ResidueField.map (integersEquivOfRingEquiv σ τ h Q : _ →+* _) :=
    rfl
  rw [halg', halg, h1, h2, ← IsLocalRing.ResidueField.map_comp,
    ← IsLocalRing.ResidueField.map_comp]
  simp only [hring]

include hK in
/-- **The relative degree is invariant under a commutative square of semilinear isomorphisms**:
if `τ : L ≃+* L'` carries the constants along `σ` and the image of `K` onto the image of `K'`
along `σK : K ≃+* K'`, then transporting a place of `L` along `τ` does not change its relative
degree over the place below. The residue fields above and below are matched by `τ` and by `σK`. -/
theorem relativeDegree_equivOfRingEquiv_of_comm [Algebra k K] [Algebra k' K']
    [IsScalarTower k K L] [IsScalarTower k' K' L'] [Algebra.IsIntegral K L]
    [Algebra.IsIntegral K' L'] (Q : Place k L) :
    relativeDegree k' K' (equivOfRingEquiv σ τ h Q) = relativeDegree k K Q := by
  rw [relativeDegree_def, relativeDegree_def]
  exact (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (integersEquivRestrictOfRingEquiv σ τ h σK hK Q))
    (IsLocalRing.ResidueField.mapEquiv (integersEquivOfRingEquiv σ τ h Q))
    (residueField_comm_equivOfRingEquiv σ τ h σK hK Q)).symm

include hK in
/-- **Residue-field separability is invariant under a commutative square of semilinear
isomorphisms**. -/
theorem isSeparable_residueField_equivOfRingEquiv_of_comm [Algebra k K] [Algebra k' K']
    [IsScalarTower k K L] [IsScalarTower k' K' L'] [Algebra.IsIntegral K L]
    [Algebra.IsIntegral K' L'] (Q : Place k L) :
    Algebra.IsSeparable ((equivOfRingEquiv σ τ h Q).restrict k' K').ResidueField
        (equivOfRingEquiv σ τ h Q).ResidueField ↔
      Algebra.IsSeparable (Q.restrict k K).ResidueField Q.ResidueField :=
  (Algebra.IsSeparable.iff_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (integersEquivRestrictOfRingEquiv σ τ h σK hK Q))
    (IsLocalRing.ResidueField.mapEquiv (integersEquivOfRingEquiv σ τ h Q))
    (residueField_comm_equivOfRingEquiv σ τ h σK hK Q)).symm

end Semilinear

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']

/-- **The ramification index is invariant under an isomorphism of the upstairs field** over the
base field: transporting a place of `L` along `e : L ≃ₐ[F] L'` does not change its ramification
index over `F`. -/
@[simp]
theorem ramificationIdx_equivOfRingEquiv (e : L ≃ₐ[F] L') (Q : Place k L) :
    ramificationIdx F (equivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
      (fun c ↦ by simp [IsScalarTower.algebraMap_apply k F L,
        IsScalarTower.algebraMap_apply k F L']) Q) = ramificationIdx F Q :=
  ramificationIdx_equivOfRingEquiv_of_comm _ _ _ (RingEquiv.refl F) e.commutes Q

section Commute

variable {K K' : Type*} [Field K] [Field K'] [Algebra K L] [Algebra K' L'] (e : L ≃ₐ[k] L')

/-- **The ramification index is invariant under a commutative square of isomorphisms**: if
`e : L ≃ₐ[k] L'` carries the image of `K` onto the image of `K'` along `σ : K ≃+* K'`, then
transporting a place of `L` along `e` does not change its ramification index. -/
theorem ramificationIdx_map (σ : K ≃+* K')
    (he : ∀ x, e (algebraMap K L x) = algebraMap K' L' (σ x)) (Q : Place k L) :
    ramificationIdx K' (Q.map e) = ramificationIdx K Q := by
  rw [map_eq_equivOfRingEquiv]
  exact ramificationIdx_equivOfRingEquiv_of_comm _ _ _ σ he Q

/-- **Restriction commutes with a commutative square of isomorphisms**: if `e : L ≃ₐ[k] L'`
carries the image of `K` onto the image of `K'` along a `k`-algebra isomorphism `σ`, then the
transport of a place `Q` of `L` lies over the transport of the place below `Q`. -/
theorem restrict_map [Algebra k K] [Algebra k K'] [IsScalarTower k K L] [IsScalarTower k K' L']
    [Algebra.IsIntegral K L] [Algebra.IsIntegral K' L'] (σ : K ≃ₐ[k] K')
    (he : ∀ x, e (algebraMap K L x) = algebraMap K' L' (σ x)) (Q : Place k L) :
    (Q.map e).restrict k K' = (Q.restrict k K).map σ := by
  rw [map_eq_equivOfRingEquiv, map_eq_equivOfRingEquiv]
  exact restrict_equivOfRingEquiv _ _ _ σ.toRingEquiv he _ Q

/-- **The relative degree is invariant under a commutative square of isomorphisms**: if
`e : L ≃ₐ[k] L'` carries the image of `K` onto the image of `K'` along `σ : K ≃+* K'`, then
transporting a place of `L` along `e` does not change its relative degree. -/
theorem relativeDegree_map [Algebra k K] [Algebra k K'] [IsScalarTower k K L]
    [IsScalarTower k K' L'] [Algebra.IsIntegral K L] [Algebra.IsIntegral K' L'] (σ : K ≃+* K')
    (he : ∀ x, e (algebraMap K L x) = algebraMap K' L' (σ x)) (Q : Place k L) :
    relativeDegree k K' (Q.map e) = relativeDegree k K Q := by
  rw [map_eq_equivOfRingEquiv]
  exact relativeDegree_equivOfRingEquiv_of_comm _ _ _ σ he Q

/-- **Residue-field separability is invariant under a commutative square of isomorphisms**: if
`e : L ≃ₐ[k] L'` carries the image of `K` onto the image of `K'` along `σ : K ≃+* K'`, then
separability of the residue extension at `Q.map e` is equivalent to that at `Q`. -/
theorem isSeparable_residueField_map [Algebra k K] [Algebra k K'] [IsScalarTower k K L]
    [IsScalarTower k K' L'] [Algebra.IsIntegral K L] [Algebra.IsIntegral K' L'] (σ : K ≃+* K')
    (he : ∀ x, e (algebraMap K L x) = algebraMap K' L' (σ x)) (Q : Place k L) :
    Algebra.IsSeparable ((Q.map e).restrict k K').ResidueField (Q.map e).ResidueField ↔
      Algebra.IsSeparable (Q.restrict k K).ResidueField Q.ResidueField := by
  rw [map_eq_equivOfRingEquiv]
  exact isSeparable_residueField_equivOfRingEquiv_of_comm _ _ _ σ he Q

end Commute

end TauCeti.Place
