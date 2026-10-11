/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.SpinorNormImage
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.Spin
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.SpinorNorm
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.NumberTheory.Padics.RatCast

/-!
# The integral compact-open reference family of a basis

Let `Q` be a nondegenerate quadratic form on a finite-dimensional rational vector space `V` and
let `b` be a basis of `V`. At every prime `p`, the isometries of `V ⊗ ℚ_p` that are integral in
the scalar extension of `b`, in both directions, form a compact-open subgroup of the local
orthogonal group, and the Spin points acting through such isometries form a compact-open subgroup
of the local Spin group. Together they are compatible compact-open reference data for the
restricted products of the local orthogonal, special orthogonal and Spin groups.

For this family the reference subgroups of the local square-class groups are computed at almost
every prime: in dimension at least two, the image of the integral special orthogonal group under
the local spinor norm is the group of unit square classes. More generally, the same holds for any
compatible family whose orthogonal reference subgroups are integral in some rational basis at
almost every prime.

In dimension one the special orthogonal group is trivial, so the reference images are trivial and
the dimension hypothesis cannot be dropped
(`TauCeti.QuadraticMap.exists_localSpinorNormImage_ne_unitSquareClasses`).

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens.integral`: the integral compact-open reference
  family of a basis.

## Main results

* `OrthogonalCompactOpens.eventually_localSpinorNormImage_eq_unitSquareClasses`: for a family
  whose orthogonal reference subgroups are eventually integral in a rational basis, the local
  spinor-norm images are the unit square classes at almost every prime.
* `OrthogonalCompactOpens.eventually_localSpinorNormImage_integral_eq_unitSquareClasses`: the
  same statement for the integral family of a basis.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §92 and §101–102.
-/

public section

namespace TauCeti
namespace QuadraticMap

open Filter Module
open _root_.QuadraticMap
open scoped TensorProduct

noncomputable section

/-- The canonical invertibility witness for two over the rationals. -/
local instance integralCompactOpenInvertibleTwoRat : Invertible (2 : ℚ) :=
  invertibleOfNonzero two_ne_zero

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace OrthogonalCompactOpens

/-- The integral compact-open reference family of a basis `b`: at every prime `p`, the isometries
integral in the scalar extension of `b` in both directions, and the Spin points acting through
them. Nondegeneracy is used for compactness of the Spin subgroups. -/
def integral (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate) (b : Basis ι ℚ V) :
    OrthogonalCompactOpens Q where
  orthogonal p := integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])
  spin p := CliffordAlgebra.integralSpinSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p])
  isOpen_orthogonal _ := isOpen_integralOrthogonalSubgroup _ _
  isCompact_orthogonal _ := isCompact_integralOrthogonalSubgroup _ _
  isOpen_spin _ := CliffordAlgebra.isOpen_integralSpinSubgroup _ _
  isCompact_spin _ := CliffordAlgebra.isCompact_integralSpinSubgroup _ _
    (QuadraticForm.Nondegenerate.baseChange hQ)
  spin_maps p s hs := by
    rw [SetLike.mem_coe, Subgroup.mem_comap,
      CliffordAlgebra.specialOrthogonalToOrthogonal_spinToSpecialOrthogonal]
    exact (CliffordAlgebra.mem_integralSpinSubgroup_iff _ _ s).mp hs
  eventually_orthogonal := eventually_mem_integralOrthogonalSubgroup Q b
  eventually_spin := CliffordAlgebra.eventually_mem_integralSpinSubgroup Q b

/-- The orthogonal reference subgroups of the integral family are the integral orthogonal
subgroups. -/
@[simp]
theorem integral_orthogonal (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate) (b : Basis ι ℚ V)
    (p : Nat.Primes) :
    (integral Q hQ b).orthogonal p =
      integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p]) := (rfl)

-- Not `@[simp]`: simp would go on to try the `@[simp]` lemma
-- `CliffordAlgebra.integralSpinSubgroup_eq_top` on the right-hand side, whose
-- `Subsingleton (ℚ_[p] ⊗[ℚ] V)` side goal times out in instance search in the full library
-- environment. `mem_integral_spin` is the simp-normalizing lemma instead.
/-- The Spin reference subgroups of the integral family are the integral Spin subgroups. -/
theorem integral_spin (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate) (b : Basis ι ℚ V)
    (p : Nat.Primes) :
    (integral Q hQ b).spin p =
      CliffordAlgebra.integralSpinSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p]) := (rfl)

/-- A Spin point lies in the Spin reference subgroup of the integral family exactly when its
action is an integral isometry. -/
@[simp]
theorem mem_integral_spin (Q : QuadraticForm ℚ V) (hQ : Q.Nondegenerate) (b : Basis ι ℚ V)
    (p : Nat.Primes) (s : spinGroup (Q.baseChange ℚ_[p])) :
    s ∈ (integral Q hQ b).spin p ↔
      CliffordAlgebra.spinToOrthogonal (Q.baseChange ℚ_[p]) s ∈
        integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p]) := by
  rw [integral_spin, CliffordAlgebra.mem_integralSpinSubgroup_iff]

/-- **The local spinor-norm images are eventually the unit square classes.** Let `U` be
compatible compact-open reference data for a nondegenerate rational quadratic space of dimension
at least two, whose orthogonal reference subgroups are integral in a rational basis `b` at almost
every prime. Then at almost every prime the image of the special orthogonal reference subgroup
under the local spinor norm is the group of square classes of `p`-adic units. -/
theorem eventually_localSpinorNormImage_eq_unitSquareClasses {Q : QuadraticForm ℚ V}
    (U : OrthogonalCompactOpens Q) (hQ : Q.Nondegenerate) (b : Basis ι ℚ V)
    (hU : ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p = integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p]))
    (hV : 2 ≤ finrank ℚ V) :
    ∀ᶠ p : Nat.Primes in cofinite,
      U.localSpinorNormImage hQ p =
        (unitSquareClasses ℚ_[p]).map (N := Multiplicative (SquareClassGroup ℚ_[p]))
          (multiplicativeSquareClassEquiv (K := ℚ_[p])).toMonoidHom := by
  -- Replace `b` by a rational orthogonal basis `c`, whose norms are nonzero rationals.
  obtain ⟨c, hc, hc0⟩ := hQ.exists_orthogonal_basis
  have : Nontrivial (Fin (finrank ℚ V)) := Fin.nontrivial_iff_two_le.mpr hV
  have hodd : ∀ᶠ p : Nat.Primes in cofinite, (p : ℕ) ≠ 2 :=
    (eventually_cofinite_ne (⟨2, Nat.prime_two⟩ : Nat.Primes)).mono
      fun _ hp h ↦ hp (Subtype.ext h)
  filter_upwards [hU, eventually_integralOrthogonalSubgroup_baseChange_eq Q b c, hodd,
    eventually_all.mpr fun i ↦ Padic.eventually_norm_rat_eq_one (hc0 i)] with p hUp hbc hp hnorm
  -- At such a prime, `c` is an orthogonal basis of `p`-adic unit norms spanning the same lattice.
  have hcb : (associated (Q.baseChange ℚ_[p])).IsOrthoᵢ (c.baseChange ℚ_[p]) := fun i j hij ↦ by
    refine associated_isOrtho.mpr (isOrtho_def.mpr ?_)
    rw [Basis.baseChange_apply, Basis.baseChange_apply, ← TensorProduct.tmul_add,
      QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul,
      isOrtho_def.mp (hc i j hij), add_smul]
  have hcu (i : Fin (finrank ℚ V)) : ‖Q.baseChange ℚ_[p] (c.baseChange ℚ_[p] i)‖ = 1 := by
    rw [Basis.baseChange_apply, QuadraticForm.baseChange_tmul, mul_one, Rat.smul_one_eq_cast]
    exact hnorm i
  rw [← map_spinorNorm_comap_integralOrthogonalSubgroup_eq_unitSquareClasses hcb hcu
    (QuadraticForm.Nondegenerate.baseChange hQ) hp, ← hbc, ← hUp]
  ext x
  rw [mem_localSpinorNormImage_iff, Subgroup.mem_map]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, (U.mem_specialOrthogonal_iff p g).mp g.2, hg⟩,
    fun ⟨g, hg, hgx⟩ ↦ ⟨⟨g, (U.mem_specialOrthogonal_iff p g).mpr hg⟩, hgx⟩⟩

/-- At almost every prime, the local spinor-norm image of the integral family of a rational basis
of a nondegenerate quadratic space of dimension at least two is the group of unit square
classes. -/
theorem eventually_localSpinorNormImage_integral_eq_unitSquareClasses (Q : QuadraticForm ℚ V)
    (hQ : Q.Nondegenerate) (b : Basis ι ℚ V) (hV : 2 ≤ finrank ℚ V) :
    ∀ᶠ p : Nat.Primes in cofinite,
      (integral Q hQ b).localSpinorNormImage hQ p =
        (unitSquareClasses ℚ_[p]).map (N := Multiplicative (SquareClassGroup ℚ_[p]))
          (multiplicativeSquareClassEquiv (K := ℚ_[p])).toMonoidHom :=
  eventually_localSpinorNormImage_eq_unitSquareClasses _ hQ b (.of_forall fun _ ↦ rfl) hV

end OrthogonalCompactOpens

end

end QuadraticMap
end TauCeti
