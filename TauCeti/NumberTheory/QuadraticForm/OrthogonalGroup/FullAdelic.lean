/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.FiniteAdelic

/-!
# Full adelic orthogonal, special orthogonal, and Spin groups

For a rational quadratic space and compatible compact-open reference subgroups, the full adelic
point group is the product of its real point group with its finite adelic point group. The real
factor has no integrality condition. The product topology uses the canonical local group
topologies and the restricted-product topology at the finite places.

The real factor is retained for the study of rational diagonal points in the full adeles.

This file constructs all three full adelic groups and the continuous maps `Spin → SO → O`.
Their projections to finite adeles commute with these maps. Membership in the image of `SO → O`
is characterized by properness at every place; for a nondegenerate form on a finite-dimensional
space, the kernel of `Spin → SO` is characterized by scalar `±1` at every place. On a nonzero
space the signs are independent; on the zero space the Spin group is trivial.

Local isometries `Q ⊗ ℝ ≃ Q' ⊗ ℝ` and `Q ⊗ ℚ_p ≃ Q' ⊗ ℚ_p` which carry the reference subgroups
onto one another at almost every prime give isomorphisms of topological groups between the full
adelic groups of `Q` and `Q'`, compatible with the maps `Spin → SO → O`. The finite component of
each is `TauCeti.restrictedProductCongrRight`, so forgetting the real place recovers the finite
adelic transport.

The real coordinate of a full adelic point `x` is `x.1`, and its finite coordinates are `x.2 p`.
The product and restricted-product extensionality lemmas therefore apply directly. All carriers
and maps are defined without nondegeneracy or a positive-dimension hypothesis.

## Main definitions

* `OrthogonalCompactOpens.fullAdelicOrthogonalCongr`,
  `OrthogonalCompactOpens.fullAdelicSpecialOrthogonalCongr`,
  `OrthogonalCompactOpens.fullAdelicSpinCongr`: transport of full adelic points along local
  isometries.

## Main results

* `fullAdelicSpecialOrthogonalCongr_comp_fullAdelicSpinToSpecialOrthogonal` and
  `fullAdelicSpecialOrthogonalToOrthogonal_comp_fullAdelicSpecialOrthogonalCongr`, in the
  namespace `TauCeti.QuadraticMap.OrthogonalCompactOpens`: the transports intertwine the maps
  `Spin → SO → O`.
* `fullAdelicOrthogonalToFinite_comp_fullAdelicOrthogonalCongr` and its special orthogonal and
  Spin analogues: forgetting the real place turns each full adelic transport into the
  corresponding finite adelic transport.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap
open scoped TensorProduct

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- The full adelic orthogonal group `O(V)(𝔸)`, with its unrestricted real factor. -/
abbrev fullAdelicOrthogonal : Type _ :=
  RestrictedProductGroupWithFactor (orthogonalGroup (Q.baseChange ℝ)) U.orthogonal

/-- The full adelic special orthogonal group `SO(V)(𝔸)`, with its unrestricted real factor. -/
abbrev fullAdelicSpecialOrthogonal : Type _ :=
  RestrictedProductGroupWithFactor (specialOrthogonalGroup (Q.baseChange ℝ)) U.specialOrthogonal

/-- The full adelic Spin group `Spin(V)(𝔸)`, with its unrestricted real factor. -/
abbrev fullAdelicSpin : Type _ :=
  RestrictedProductGroupWithFactor (spinGroup (Q.baseChange ℝ)) U.spin

/-- Full adelic orthogonal points form a topological group in the product topology. -/
instance instIsTopologicalGroupFullAdelicOrthogonal [FiniteDimensional ℚ V] :
    IsTopologicalGroup U.fullAdelicOrthogonal := by
  -- Supply the real automorphism-group witness explicitly before descending to the subgroup.
  let : IsTopologicalGroup (ℝ ⊗[ℚ] V ≃ₗ[ℝ] ℝ ⊗[ℚ] V) := inferInstance
  infer_instance

/-- Full adelic special orthogonal points form a topological group in the product topology. -/
instance instIsTopologicalGroupFullAdelicSpecialOrthogonal [FiniteDimensional ℚ V] :
    IsTopologicalGroup U.fullAdelicSpecialOrthogonal := by
  -- Supply the real automorphism-group witness explicitly before descending to the subgroup.
  let : IsTopologicalGroup (ℝ ⊗[ℚ] V ≃ₗ[ℝ] ℝ ⊗[ℚ] V) := inferInstance
  infer_instance

/-- Forget the real component of a full adelic orthogonal point. -/
def fullAdelicOrthogonalToFinite : U.fullAdelicOrthogonal →* U.finiteAdelicOrthogonal :=
  MonoidHom.snd _ _

/-- Forget the real component of a full adelic special orthogonal point. -/
def fullAdelicSpecialOrthogonalToFinite :
    U.fullAdelicSpecialOrthogonal →* U.finiteAdelicSpecialOrthogonal :=
  MonoidHom.snd _ _

/-- Forget the real component of a full adelic Spin point. -/
def fullAdelicSpinToFinite : U.fullAdelicSpin →* U.finiteAdelicSpin :=
  MonoidHom.snd _ _

/-- The finite projection retains the finite component of an orthogonal point. -/
@[simp]
theorem fullAdelicOrthogonalToFinite_apply (x : U.fullAdelicOrthogonal) :
    U.fullAdelicOrthogonalToFinite x = x.2 := (rfl)

/-- The finite projection retains the finite component of a special orthogonal point. -/
@[simp]
theorem fullAdelicSpecialOrthogonalToFinite_apply (x : U.fullAdelicSpecialOrthogonal) :
    U.fullAdelicSpecialOrthogonalToFinite x = x.2 := (rfl)

/-- The finite projection retains the finite component of a Spin point. -/
@[simp]
theorem fullAdelicSpinToFinite_apply (x : U.fullAdelicSpin) :
    U.fullAdelicSpinToFinite x = x.2 := (rfl)

/-- The projection from full to finite adelic orthogonal points is continuous. -/
theorem continuous_fullAdelicOrthogonalToFinite : Continuous U.fullAdelicOrthogonalToFinite :=
  continuous_snd

/-- The projection from full to finite adelic special orthogonal points is continuous. -/
theorem continuous_fullAdelicSpecialOrthogonalToFinite :
    Continuous U.fullAdelicSpecialOrthogonalToFinite :=
  continuous_snd

/-- The projection from full to finite adelic Spin points is continuous. -/
theorem continuous_fullAdelicSpinToFinite : Continuous U.fullAdelicSpinToFinite :=
  continuous_snd

/-- The full adelic Spin projection, applying the local projection at the real place and the
everywhere-preserving finite adelic projection at the finite places. -/
def fullAdelicSpinToSpecialOrthogonal :
    U.fullAdelicSpin →* U.fullAdelicSpecialOrthogonal :=
  (CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℝ)).prodMap
    U.finiteAdelicSpinToSpecialOrthogonal

/-- The full adelic inclusion of special orthogonal points into orthogonal points. -/
def fullAdelicSpecialOrthogonalToOrthogonal :
    U.fullAdelicSpecialOrthogonal →* U.fullAdelicOrthogonal :=
  (specialOrthogonalToOrthogonal (Q.baseChange ℝ)).prodMap
    U.finiteAdelicSpecialOrthogonalToOrthogonal

/-- The full adelic Spin projection acts on the real and finite components separately. -/
@[simp]
theorem fullAdelicSpinToSpecialOrthogonal_apply (x : U.fullAdelicSpin) :
    U.fullAdelicSpinToSpecialOrthogonal x =
      (CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℝ) x.1,
        U.finiteAdelicSpinToSpecialOrthogonal x.2) := (rfl)

/-- The full adelic special orthogonal inclusion acts on the real and finite components
separately. -/
@[simp]
theorem fullAdelicSpecialOrthogonalToOrthogonal_apply (x : U.fullAdelicSpecialOrthogonal) :
    U.fullAdelicSpecialOrthogonalToOrthogonal x =
      (specialOrthogonalToOrthogonal (Q.baseChange ℝ) x.1,
        U.finiteAdelicSpecialOrthogonalToOrthogonal x.2) := (rfl)

/-- The full adelic Spin projection is continuous in the product topology. -/
theorem continuous_fullAdelicSpinToSpecialOrthogonal [FiniteDimensional ℚ V] :
    Continuous U.fullAdelicSpinToSpecialOrthogonal :=
  (CliffordAlgebra.continuous_spinToSpecialOrthogonal (Q.baseChange ℝ)).prodMap
    U.continuous_finiteAdelicSpinToSpecialOrthogonal

/-- The full adelic inclusion of special orthogonal points is continuous. -/
theorem continuous_fullAdelicSpecialOrthogonalToOrthogonal :
    Continuous U.fullAdelicSpecialOrthogonalToOrthogonal :=
  (continuous_specialOrthogonalToOrthogonal (Q.baseChange ℝ)).prodMap
    U.continuous_finiteAdelicSpecialOrthogonalToOrthogonal

/-- Forgetting the real component commutes with the adelic Spin projection. -/
@[simp]
theorem fullAdelicSpecialOrthogonalToFinite_comp_fullAdelicSpinToSpecialOrthogonal :
    U.fullAdelicSpecialOrthogonalToFinite.comp U.fullAdelicSpinToSpecialOrthogonal =
      U.finiteAdelicSpinToSpecialOrthogonal.comp U.fullAdelicSpinToFinite := by
  ext x p
  simp

/-- Forgetting the real component commutes with the adelic special orthogonal inclusion. -/
@[simp]
theorem fullAdelicOrthogonalToFinite_comp_fullAdelicSpecialOrthogonalToOrthogonal :
    U.fullAdelicOrthogonalToFinite.comp U.fullAdelicSpecialOrthogonalToOrthogonal =
      U.finiteAdelicSpecialOrthogonalToOrthogonal.comp U.fullAdelicSpecialOrthogonalToFinite := by
  ext x p
  simp

/-- The full adelic inclusion `SO → O` is injective. -/
theorem fullAdelicSpecialOrthogonalToOrthogonal_injective :
    Function.Injective U.fullAdelicSpecialOrthogonalToOrthogonal :=
  Prod.map_injective.mpr
    ⟨specialOrthogonalToOrthogonal_injective,
      U.finiteAdelicSpecialOrthogonalToOrthogonal_injective⟩

/-- A full adelic isometry comes from adelic `SO` exactly when it is proper at the real place
and at every finite place. -/
theorem mem_range_fullAdelicSpecialOrthogonalToOrthogonal_iff (x : U.fullAdelicOrthogonal) :
    x ∈ U.fullAdelicSpecialOrthogonalToOrthogonal.range ↔
      x.1 ∈ specialOrthogonalWithin (Q.baseChange ℝ) ∧
        ∀ p : Nat.Primes, x.2 p ∈ specialOrthogonalWithin (Q.baseChange ℚ_[p]) := by
  rw [fullAdelicSpecialOrthogonalToOrthogonal, MonoidHom.range_prodMap, Subgroup.mem_prod,
    range_specialOrthogonalToOrthogonal,
    U.mem_range_finiteAdelicSpecialOrthogonalToOrthogonal_iff]

/-- For a nondegenerate form, a full adelic Spin element lies in the kernel exactly when each
component is `1` or `-1` in its local Clifford algebra. -/
theorem mem_ker_fullAdelicSpinToSpecialOrthogonal_iff [FiniteDimensional ℚ V]
    (hQ : Q.Nondegenerate) (x : U.fullAdelicSpin) :
    x ∈ U.fullAdelicSpinToSpecialOrthogonal.ker ↔
      ((x.1 : CliffordAlgebra (Q.baseChange ℝ)) = 1 ∨
        (x.1 : CliffordAlgebra (Q.baseChange ℝ)) = -1) ∧
      ∀ p : Nat.Primes,
        (x.2 p : CliffordAlgebra (Q.baseChange ℚ_[p])) = 1 ∨
          (x.2 p : CliffordAlgebra (Q.baseChange ℚ_[p])) = -1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · let _ : Subsingleton V := hV
    have hx : x = 1 := by
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · ext p : 1
        exact Subsingleton.elim _ _
    simp [hx]
  · let _ : Nontrivial V := hV
    have : Nontrivial (ℝ ⊗[ℚ] V) := Module.nontrivial_of_finrank_pos <| by
      rw [Module.finrank_baseChange]
      exact Module.finrank_pos
    have hQr : (Q.baseChange ℝ).Nondegenerate :=
      _root_.QuadraticForm.Nondegenerate.baseChange hQ
    rw [fullAdelicSpinToSpecialOrthogonal, MonoidHom.ker_prodMap, Subgroup.mem_prod,
      U.mem_ker_finiteAdelicSpinToSpecialOrthogonal_iff hQ,
      CliffordAlgebra.mem_ker_spinToSpecialOrthogonal_iff _ hQr]
    simp only [Subtype.ext_iff, OneMemClass.coe_one, CliffordAlgebra.spinGroup.coe_negOne]

/-! ### Transport along local isometries -/

section Congr

open Filter

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {Q' : QuadraticForm ℚ W}
  (U' : OrthogonalCompactOpens Q')
  (eR : (Q.baseChange ℝ).IsometryEquiv (Q'.baseChange ℝ))
  (e : ∀ p : Nat.Primes, (Q.baseChange ℚ_[p]).IsometryEquiv (Q'.baseChange ℚ_[p]))

/-- The isomorphism of full adelic orthogonal groups induced by a real isometry and by local
isometries at the primes which carry the orthogonal reference subgroups onto one another at almost
every prime. -/
def fullAdelicOrthogonalCongr
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    U.fullAdelicOrthogonal ≃ₜ* U'.fullAdelicOrthogonal where
  toMulEquiv := eR.orthogonalGroupCongr.prodCongr
    (restrictedProductCongrRight U.orthogonal U'.orthogonal
      (fun p ↦ (e p).orthogonalGroupCongr) he)
  continuous_toFun := eR.continuous_orthogonalGroupCongr.prodMap
    (continuous_restrictedProductCongrRight _ _ _ he fun p ↦ (e p).continuous_orthogonalGroupCongr)
  continuous_invFun := by
    refine Continuous.prodMap (f := eR.orthogonalGroupCongr.symm) ?_
      (continuous_restrictedProductCongrRight_symm _ _ _ he fun p ↦ ?_)
    · rw [eR.orthogonalGroupCongr_symm]
      exact eR.symm.continuous_orthogonalGroupCongr
    · rw [(e p).orthogonalGroupCongr_symm]
      exact (e p).symm.continuous_orthogonalGroupCongr

/-- Full adelic orthogonal transport applies the real isometry to the real component and the
local isometries to the finite components. -/
@[simp]
theorem fullAdelicOrthogonalCongr_apply
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) (x : U.fullAdelicOrthogonal) :
    U.fullAdelicOrthogonalCongr U' eR e he x =
      (eR.orthogonalGroupCongr x.1,
        restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p ↦ (e p).orthogonalGroupCongr) he x.2) := (rfl)

/-- Inverse full adelic orthogonal transport applies the inverse isometries componentwise. -/
@[simp]
theorem fullAdelicOrthogonalCongr_symm_apply
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) (y : U'.fullAdelicOrthogonal) :
    (U.fullAdelicOrthogonalCongr U' eR e he).symm y =
      (eR.orthogonalGroupCongr.symm y.1,
        (restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p ↦ (e p).orthogonalGroupCongr) he).symm y.2) := (rfl)

/-- The isomorphism of full adelic special orthogonal groups induced by a real isometry and by
local isometries at the primes which carry the special orthogonal reference subgroups onto one
another at almost every prime. -/
def fullAdelicSpecialOrthogonalCongr
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U.fullAdelicSpecialOrthogonal ≃ₜ* U'.fullAdelicSpecialOrthogonal where
  toMulEquiv := eR.specialOrthogonalGroupCongr.prodCongr
    (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
      (fun p ↦ (e p).specialOrthogonalGroupCongr) hso)
  continuous_toFun := eR.continuous_specialOrthogonalGroupCongr.prodMap
    (continuous_restrictedProductCongrRight _ _ _ hso
      fun p ↦ (e p).continuous_specialOrthogonalGroupCongr)
  continuous_invFun := by
    refine Continuous.prodMap (f := eR.specialOrthogonalGroupCongr.symm) ?_
      (continuous_restrictedProductCongrRight_symm _ _ _ hso fun p ↦ ?_)
    · rw [eR.specialOrthogonalGroupCongr_symm]
      exact eR.symm.continuous_specialOrthogonalGroupCongr
    · rw [(e p).specialOrthogonalGroupCongr_symm]
      exact (e p).symm.continuous_specialOrthogonalGroupCongr

/-- Full adelic special orthogonal transport applies the real isometry to the real component and
the local isometries to the finite components. -/
@[simp]
theorem fullAdelicSpecialOrthogonalCongr_apply
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) (x : U.fullAdelicSpecialOrthogonal) :
    U.fullAdelicSpecialOrthogonalCongr U' eR e hso x =
      (eR.specialOrthogonalGroupCongr x.1,
        restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p ↦ (e p).specialOrthogonalGroupCongr) hso x.2) := (rfl)

/-- Inverse full adelic special orthogonal transport applies the inverse isometries
componentwise. -/
@[simp]
theorem fullAdelicSpecialOrthogonalCongr_symm_apply
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) (y : U'.fullAdelicSpecialOrthogonal) :
    (U.fullAdelicSpecialOrthogonalCongr U' eR e hso).symm y =
      (eR.specialOrthogonalGroupCongr.symm y.1,
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p ↦ (e p).specialOrthogonalGroupCongr) hso).symm y.2) := (rfl)

/-- The isomorphism of full adelic Spin groups induced by a real isometry and by local isometries
at the primes which carry the Spin reference subgroups onto one another at almost every prime. -/
def fullAdelicSpinCongr
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p)) :
    U.fullAdelicSpin ≃ₜ* U'.fullAdelicSpin where
  toMulEquiv := eR.spinGroupEquiv.prodCongr
    (restrictedProductCongrRight U.spin U'.spin (fun p ↦ (e p).spinGroupEquiv) hs)
  continuous_toFun := eR.continuous_spinGroupEquiv.prodMap
    (continuous_restrictedProductCongrRight _ _ _ hs fun p ↦ (e p).continuous_spinGroupEquiv)
  continuous_invFun := by
    refine Continuous.prodMap (f := eR.spinGroupEquiv.symm) ?_
      (continuous_restrictedProductCongrRight_symm _ _ _ hs fun p ↦ ?_)
    · rw [eR.spinGroupEquiv_symm]
      exact eR.symm.continuous_spinGroupEquiv
    · rw [(e p).spinGroupEquiv_symm]
      exact (e p).symm.continuous_spinGroupEquiv

/-- Full adelic Spin transport applies the real isometry to the real component and the local
isometries to the finite components. -/
@[simp]
theorem fullAdelicSpinCongr_apply
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p))
    (x : U.fullAdelicSpin) :
    U.fullAdelicSpinCongr U' eR e hs x =
      (eR.spinGroupEquiv x.1,
        restrictedProductCongrRight U.spin U'.spin (fun p ↦ (e p).spinGroupEquiv) hs x.2) :=
  (rfl)

/-- Inverse full adelic Spin transport applies the inverse isometries componentwise. -/
@[simp]
theorem fullAdelicSpinCongr_symm_apply
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p))
    (y : U'.fullAdelicSpin) :
    (U.fullAdelicSpinCongr U' eR e hs).symm y =
      (eR.spinGroupEquiv.symm y.1,
        (restrictedProductCongrRight U.spin U'.spin (fun p ↦ (e p).spinGroupEquiv) hs).symm
          y.2) := (rfl)

/-- Full adelic transport intertwines the full adelic Spin projections. -/
theorem fullAdelicSpecialOrthogonalCongr_comp_fullAdelicSpinToSpecialOrthogonal
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p))
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    (U.fullAdelicSpecialOrthogonalCongr U' eR e hso :
        U.fullAdelicSpecialOrthogonal →* U'.fullAdelicSpecialOrthogonal).comp
        U.fullAdelicSpinToSpecialOrthogonal =
      U'.fullAdelicSpinToSpecialOrthogonal.comp
        (U.fullAdelicSpinCongr U' eR e hs : U.fullAdelicSpin →* U'.fullAdelicSpin) := by
  ext x : 1
  simp [hs]

/-- Full adelic transport intertwines the full adelic inclusions of `SO` into `O`. -/
theorem fullAdelicSpecialOrthogonalToOrthogonal_comp_fullAdelicSpecialOrthogonalCongr
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p))
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U'.fullAdelicSpecialOrthogonalToOrthogonal.comp
        (U.fullAdelicSpecialOrthogonalCongr U' eR e hso :
          U.fullAdelicSpecialOrthogonal →* U'.fullAdelicSpecialOrthogonal) =
      (U.fullAdelicOrthogonalCongr U' eR e he :
          U.fullAdelicOrthogonal →* U'.fullAdelicOrthogonal).comp
        U.fullAdelicSpecialOrthogonalToOrthogonal := by
  ext g : 1
  simp [he]

/-- Forgetting the real component turns full adelic orthogonal transport into finite adelic
orthogonal transport. -/
@[simp]
theorem fullAdelicOrthogonalToFinite_comp_fullAdelicOrthogonalCongr
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    U'.fullAdelicOrthogonalToFinite.comp
        (U.fullAdelicOrthogonalCongr U' eR e he :
          U.fullAdelicOrthogonal →* U'.fullAdelicOrthogonal) =
      (restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p ↦ (e p).orthogonalGroupCongr) he :
          U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal).comp
        U.fullAdelicOrthogonalToFinite := by
  ext x : 1
  rfl

/-- Forgetting the real component turns full adelic special orthogonal transport into finite
adelic special orthogonal transport. -/
@[simp]
theorem fullAdelicSpecialOrthogonalToFinite_comp_fullAdelicSpecialOrthogonalCongr
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U'.fullAdelicSpecialOrthogonalToFinite.comp
        (U.fullAdelicSpecialOrthogonalCongr U' eR e hso :
          U.fullAdelicSpecialOrthogonal →* U'.fullAdelicSpecialOrthogonal) =
      (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p ↦ (e p).specialOrthogonalGroupCongr) hso :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal).comp
        U.fullAdelicSpecialOrthogonalToFinite := by
  ext x : 1
  rfl

/-- Forgetting the real component turns full adelic Spin transport into finite adelic Spin
transport. -/
@[simp]
theorem fullAdelicSpinToFinite_comp_fullAdelicSpinCongr
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p)) :
    U'.fullAdelicSpinToFinite.comp
        (U.fullAdelicSpinCongr U' eR e hs : U.fullAdelicSpin →* U'.fullAdelicSpin) =
      (restrictedProductCongrRight U.spin U'.spin (fun p ↦ (e p).spinGroupEquiv) hs :
          U.finiteAdelicSpin →* U'.finiteAdelicSpin).comp
        U.fullAdelicSpinToFinite := by
  ext x : 1
  rfl

end Congr

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
