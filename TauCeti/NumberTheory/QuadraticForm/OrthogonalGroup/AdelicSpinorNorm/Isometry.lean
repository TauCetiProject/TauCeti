/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.AdelicSpinorNorm.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic

/-!
# Isometric transport of the adelic spinor norm

Local isometries of rational quadratic spaces preserve local spinor norms. When they carry the
special orthogonal reference subgroups onto one another at almost every prime, their spinor-norm
images also agree at almost every prime. Thus the adelic spinor norms commute with the induced
equivalence of restricted products and the coordinatewise identity on their square-class
codomains. The equivalence restricts to an equivalence of adelic spinor kernels.

Only eventual agreement of the reference subgroups is required. In particular these results
apply to scalar extensions of a rational isometry and to changing finitely many reference
subgroups. They do not assert that the everywhere-integral subgroups are preserved at the
exceptional primes.

The constructions use `TauCeti.restrictedProductCongrRight`, `TauCeti.restrictedProductCongr`
and `TauCeti.Subgroup.congrOfMapEq`, together with the local spinor-norm isometry theorem.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
-/

public section

namespace TauCeti.QuadraticMap.OrthogonalCompactOpens

open Filter
open _root_.QuadraticMap

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
  {Q : QuadraticForm ℚ V} {Q' : QuadraticForm ℚ W}
  (U : OrthogonalCompactOpens Q) (U' : OrthogonalCompactOpens Q')
  (hQ : Q.Nondegenerate)
  (e : ∀ p : Nat.Primes, (Q.baseChange ℚ_[p]).IsometryEquiv (Q'.baseChange ℚ_[p]))
  (he : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
    (U.specialOrthogonal p) (U'.specialOrthogonal p))

-- A single local isometry suffices to recover nondegeneracy of the target rational form.
local notation "hQ'" => QuadraticForm.Nondegenerate.of_baseChange
  (Iff.mp (_root_.QuadraticMap.IsometryEquiv.nondegenerate_iff (e (Subtype.mk 2 Nat.prime_two)))
    (QuadraticForm.Nondegenerate.baseChange hQ))

include e he in
/-- Almost-everywhere isometric transport of the special orthogonal reference family gives
almost-everywhere equality of its spinor-norm image family. -/
theorem eventually_localSpinorNormImage_eq_of_isometry :
    ∀ᶠ p in cofinite, U.localSpinorNormImage hQ p = U'.localSpinorNormImage hQ' p :=
  he.mono fun p hp ↦ U.localSpinorNormImage_eq_of_isometry U' hQ p (e p) hp

/-- The adelic spinor norm commutes with local isometric transport and the induced change of
square-class reference family. -/
@[simp]
theorem adelicSpinorNorm_restrictedProductCongrRight (g : U.finiteAdelicSpecialOrthogonal) :
    U'.adelicSpinorNorm hQ'
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p ↦ (e p).specialOrthogonalGroupCongr) he g) =
      restrictedProductCongr (U.localSpinorNormImage hQ) (U'.localSpinorNormImage hQ')
        (U.eventually_localSpinorNormImage_eq_of_isometry U' hQ e he)
        (U.adelicSpinorNorm hQ g) := by
  ext p : 1
  simp only [adelicSpinorNorm_apply, restrictedProductCongrRight_apply,
    restrictedProductCongr_apply]
  exact (e p).spinorNorm_specialOrthogonalGroupCongr
    (QuadraticForm.Nondegenerate.baseChange hQ) (g p)

/-- Local isometric transport carries the adelic spinor kernel onto the adelic spinor kernel
of the target quadratic space. -/
@[simp]
theorem map_adelicSpinorKernel_restrictedProductCongrRight :
    (U.adelicSpinorKernel hQ).map
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p ↦ (e p).specialOrthogonalGroupCongr) he :
            U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.adelicSpinorKernel hQ' := by
  apply (_root_.Subgroup.map_symm_eq_iff_map_eq (U.adelicSpinorKernel hQ)).mp
  rw [adelicSpinorKernel_def, adelicSpinorKernel_def, ← MonoidHom.ker_comp_mulEquiv]
  have hnorm :
      (U'.adelicSpinorNorm hQ').comp
          (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
            (fun p ↦ (e p).specialOrthogonalGroupCongr) he : _ →* _) =
        (restrictedProductCongr (U.localSpinorNormImage hQ) (U'.localSpinorNormImage hQ')
          (U.eventually_localSpinorNormImage_eq_of_isometry U' hQ e he) : _ →* _).comp
          (U.adelicSpinorNorm hQ) :=
    MonoidHom.ext (U.adelicSpinorNorm_restrictedProductCongrRight U' hQ e he)
  rw [hnorm, MonoidHom.ker_comp_of_injective]
  exact MulEquiv.injective _

/-- The equivalence of adelic spinor kernels induced by local isometries which carry the
special orthogonal reference subgroups onto one another at almost every prime. -/
def adelicSpinorKernelCongr : U.adelicSpinorKernel hQ ≃* U'.adelicSpinorKernel hQ' :=
  TauCeti.Subgroup.congrOfMapEq
    (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
      (fun p ↦ (e p).specialOrthogonalGroupCongr) he)
    (U.map_adelicSpinorKernel_restrictedProductCongrRight U' hQ e he)

/-- In each coordinate, adelic spinor-kernel transport is special orthogonal isometric
transport. -/
@[simp]
theorem coe_adelicSpinorKernelCongr_apply (g : U.adelicSpinorKernel hQ) (p : Nat.Primes) :
    (U.adelicSpinorKernelCongr U' hQ e he g : U'.finiteAdelicSpecialOrthogonal) p =
      (e p).specialOrthogonalGroupCongr ((g : U.finiteAdelicSpecialOrthogonal) p) := by
  rw [adelicSpinorKernelCongr, TauCeti.Subgroup.coe_congrOfMapEq_apply,
    restrictedProductCongrRight_apply]

/-- In each coordinate, inverse adelic spinor-kernel transport is inverse special orthogonal
isometric transport. -/
@[simp]
theorem coe_adelicSpinorKernelCongr_symm_apply (g : U'.adelicSpinorKernel hQ') (p : Nat.Primes) :
    ((U.adelicSpinorKernelCongr U' hQ e he).symm g : U.finiteAdelicSpecialOrthogonal) p =
      (e p).specialOrthogonalGroupCongr.symm ((g : U'.finiteAdelicSpecialOrthogonal) p) := by
  rw [adelicSpinorKernelCongr, TauCeti.Subgroup.coe_congrOfMapEq_symm_apply,
    restrictedProductCongrRight_symm_apply]

/-- Transport of adelic spinor kernels intertwines the adelic Spin projections when the local
isometries also carry the Spin reference family onto the target family at almost every prime. -/
@[simp]
theorem adelicSpinorKernelCongr_finiteAdelicSpinToSpinorKernel
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p))
    (x : U.finiteAdelicSpin) :
    U.adelicSpinorKernelCongr U' hQ e he (U.finiteAdelicSpinToSpinorKernel hQ x) =
      U'.finiteAdelicSpinToSpinorKernel hQ'
        (restrictedProductCongrRight U.spin U'.spin (fun p ↦ (e p).spinGroupEquiv) hs x) := by
  apply Subtype.ext
  ext p : 1
  simp only [coe_adelicSpinorKernelCongr_apply, coe_finiteAdelicSpinToSpinorKernel_apply,
    finiteAdelicSpinToSpecialOrthogonal_apply, restrictedProductCongrRight_apply]
  exact (e p).specialOrthogonalGroupCongr_spinToSpecialOrthogonal (x p)

end

end TauCeti.QuadraticMap.OrthogonalCompactOpens
