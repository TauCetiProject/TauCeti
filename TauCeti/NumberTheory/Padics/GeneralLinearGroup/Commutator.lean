/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `commutatorSet`, `upperLeftSection` and the local-ring commutator width are applied below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Commutator
-- `TauCeti.firstCongruenceSubgroup` occurs in a statement below.
public import TauCeti.NumberTheory.Padics.SpecialLinearGroup.FirstCongruence
-- Non-public: `Matrix.SpecialLinearGroup.toGL_map`, in one proof only.
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
-- Non-public: `PadicInt.isUnit_two` and `PadicInt.isUnit_one_add_of_dvd`, in proofs only.
import TauCeti.NumberTheory.Padics.PadicIntegers
-- Non-public: the elements of `GL₂(𝔽₂)` whose cube is `1`, in one proof only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.FieldCardTwo
-- Non-public: `TauCeti.commutatorSet_pow_subset_commutator`, in one proof only.
import TauCeti.GroupTheory.Commutator

/-!
# The commutator subgroup of `GL₂(ℤ_ℓ)`

For an odd prime `ℓ`, the abstract commutator subgroup of `GL₂(ℤ_ℓ)` is `SL₂(ℤ_ℓ)`, and every
element of `SL₂(ℤ_ℓ)` is a product of four commutators. For `ℓ = 2` the commutator subgroup is the
proper subgroup of `SL₂(ℤ₂)` of the matrices whose reduction modulo `2` has cube `1`: through
`GL₂(𝔽₂) ≅ S₃` these are the matrices whose reduction lies in `A₃`, the kernel of the sign. Again
every element of it is a product of four commutators.

The bound on the number of commutators is uniform in `ℓ`. This is what lets the local statements be
assembled over all primes at once: an element of `∏_ℓ GL₂(ℤ_ℓ)` whose components all lie in the
local commutator subgroups is a product of four commutators of the product, so the abstract
commutator subgroup of the product is the product of the local ones, and is closed.

The proof writes an element `g = [[a, b], [c, d]]` of `SL₂` with `a` a unit as
`[[1, 0], [c/a, 1]] · diag(a, a⁻¹) · [[1, b/a], [0, 1]]`, and uses that `diag(a, a⁻¹)` is a
commutator, and that an elementary matrix with coefficient `(u - 1) y` is the commutator of
`diag(u, 1)` and the elementary matrix with coefficient `y`. For odd `ℓ` take `u = 2`, so that
`u - 1 = 1`. For `ℓ = 2` take `u = 3`, so that `u - 1 = 2`: this covers the first congruence
subgroup, and the commutator `[[1, -1], [-1, 2]]` of the Weyl element and `[[1, 1], [0, 1]]`, whose
reduction has order three, covers the other two cosets.

## Main results

* `TauCeti.commutator_eq_ker_det_padicInt`: for odd `ℓ`, `[GL₂(ℤ_ℓ), GL₂(ℤ_ℓ)] = SL₂(ℤ_ℓ)`.
* `TauCeti.mem_commutatorSet_pow_four_padicInt`: for odd `ℓ`, every element of `SL₂(ℤ_ℓ)` is a
  product of four commutators of `GL₂(ℤ_ℓ)`.
* `TauCeti.toGL_mem_commutatorSet_pow_three_of_mem_firstCongruenceSubgroup`: for every prime `p`,
  every element of the first congruence subgroup of `SL₂(ℤ_p)` is a product of three commutators of
  `GL₂(ℤ_p)`.
* `TauCeti.mem_commutator_padicInt_two_iff`: an element of `GL₂(ℤ₂)` is a product of commutators
  exactly when its determinant is `1` and the cube of its reduction modulo `2` is `1`.
* `TauCeti.mem_commutatorSet_pow_four_padicInt_two`: every such element is a product of four
  commutators.
* `TauCeti.transvectionUnit_one_notMem_commutator_padicInt_two`: `[[1, 1], [0, 1]]` is not a product
  of commutators in `GL₂(ℤ₂)`, so the commutator subgroup is a proper subgroup of `SL₂(ℤ₂)`.

## References

* J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*, Invent.
  Math. 15 (1972), §5.5.
* D. Zywina, *Elliptic curves with maximal Galois action on their torsion points*, Bull. Lond.
  Math. Soc. 42 (2010), §1.
-/

public section

namespace TauCeti

open Matrix PadicInt
open scoped MatrixGroups Pointwise commutatorElement

/-! ### Odd primes -/

section Odd

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- For an odd prime `ℓ`, the abstract commutator subgroup of `GL₂(ℤ_ℓ)` is the kernel of the
determinant, that is `SL₂(ℤ_ℓ)`. -/
theorem commutator_eq_ker_det_padicInt (hℓ : ℓ ≠ 2) :
    commutator (GL (Fin 2) ℤ_[ℓ]) = (GeneralLinearGroup.det : GL (Fin 2) ℤ_[ℓ] →* ℤ_[ℓ]ˣ).ker :=
  GeneralLinearGroup.commutator_eq_ker_det_fin_two_of_isLocalRing (isUnit_two hℓ).unit
    (by norm_num [IsUnit.unit_spec])

/-- For an odd prime `ℓ`, every element of `GL₂(ℤ_ℓ)` of determinant one is a product of four
commutators. -/
theorem mem_commutatorSet_pow_four_padicInt (hℓ : ℓ ≠ 2) {g : GL (Fin 2) ℤ_[ℓ]}
    (hg : GeneralLinearGroup.det g = 1) : g ∈ commutatorSet (GL (Fin 2) ℤ_[ℓ]) ^ 4 := by
  obtain ⟨s, rfl⟩ : g ∈ (SpecialLinearGroup.toGL : SL(2, ℤ_[ℓ]) →* GL (Fin 2) ℤ_[ℓ]).range := by
    rwa [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  exact s.toGL_mem_commutatorSet_pow_four (isUnit_two hℓ).unit (by norm_num [IsUnit.unit_spec])

end Odd

/-! ### The first congruence subgroup -/

/-- For every prime `p`, every element of the first congruence subgroup of `SL₂(ℤ_p)`, the
kernel of reduction modulo `p`, is a product of three commutators of `GL₂(ℤ_p)`. -/
theorem toGL_mem_commutatorSet_pow_three_of_mem_firstCongruenceSubgroup {p : ℕ} [Fact p.Prime]
    {s : SL(2, ℤ_[p])} (hs : s ∈ firstCongruenceSubgroup (Fin 2) p) :
    SpecialLinearGroup.toGL s ∈ commutatorSet (GL (Fin 2) ℤ_[p]) ^ 3 := by
  rw [mem_firstCongruenceSubgroup_iff] at hs
  have hu : IsUnit (1 + (p : ℤ_[p])) := isUnit_one_add_of_dvd dvd_rfl
  refine s.toGL_mem_commutatorSet_pow_three hu.unit ?_ ?_ ?_
  · simpa using isUnit_one_add_of_dvd (hs 0 0)
  · simpa [IsUnit.unit_spec] using hs 0 1
  · simpa [IsUnit.unit_spec] using hs 1 0

/-! ### The prime `2` -/

section Two

/-- An element of `GL₂(ℤ₂)` of determinant one reducing to the identity modulo `2` is a product of
three commutators. -/
private theorem mem_commutatorSet_pow_three_of_map_eq_one {g : GL (Fin 2) ℤ_[2]}
    (hdet : GeneralLinearGroup.det g = 1) (hg : GeneralLinearGroup.map (toZMod (p := 2)) g = 1) :
    g ∈ commutatorSet (GL (Fin 2) ℤ_[2]) ^ 3 := by
  obtain ⟨s, rfl⟩ : g ∈ (SpecialLinearGroup.toGL : SL(2, ℤ_[2]) →* GL (Fin 2) ℤ_[2]).range := by
    rwa [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  refine toGL_mem_commutatorSet_pow_three_of_mem_firstCongruenceSubgroup ?_
  rw [mem_firstCongruenceSubgroup_iff_map_eq_one]
  apply SpecialLinearGroup.toGL_injective
  rwa [SpecialLinearGroup.toGL_map, map_one]

/-- An element of `GL₂(ℤ₂)` of determinant one whose reduction modulo `2` has cube `1` is a product
of four commutators. -/
theorem mem_commutatorSet_pow_four_padicInt_two {g : GL (Fin 2) ℤ_[2]}
    (hdet : GeneralLinearGroup.det g = 1)
    (hg : GeneralLinearGroup.map (toZMod (p := 2)) g ^ 3 = 1) :
    g ∈ commutatorSet (GL (Fin 2) ℤ_[2]) ^ 4 := by
  -- The commutator `c = [[1, -1], [-1, 2]]` of the Weyl element and `[[1, 1], [0, 1]]`.
  set c : GL (Fin 2) ℤ_[2] :=
    ⁅transvectionWeylElement (A := ℤ_[2]) (zero_ne_one : (0 : Fin 2) ≠ 1),
      transvectionUnit zero_ne_one 1⁆ with hc_def
  have hcS : c ∈ commutatorSet (GL (Fin 2) ℤ_[2]) := commutator_mem_commutatorSet _ _
  have hc₁ : GeneralLinearGroup.map (toZMod (p := 2)) c ≠ 1 := by
    intro h
    have h11 := congrArg (fun x : GL (Fin 2) (ZMod 2) ↦ (x : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1) h
    -- The `(1, 1)` entry of the reduction is `(-1) * (-1) + 1 = 0` in `𝔽₂`, not `1`.
    simp [hc_def, commutatorElement_def, Matrix.mul_apply, Fin.sum_univ_two, transvection,
      Matrix.one_apply] at h11
  have hc : GeneralLinearGroup.map (toZMod (p := 2)) c ^ 3 = 1 := by
    rw [← GeneralLinearGroup.mem_commutator_fin_two_iff_pow_three_eq_one (Nat.card_zmod 2),
      map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcdet : GeneralLinearGroup.det c = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  -- The reduction of `g` is `1`, that of `c` or that of `c⁻¹`; correct `g` by `c` accordingly.
  rcases GeneralLinearGroup.eq_one_or_eq_or_eq_inv_of_pow_three_eq_one_of_card_eq_two
    (Nat.card_zmod 2) hg hc hc₁ with h | h | h
  · exact Set.pow_subset_pow_right (one_mem_commutatorSet _) (by norm_num)
      (mem_commutatorSet_pow_three_of_map_eq_one hdet h)
  · rw [← inv_mul_cancel_right g c, pow_succ]
    exact Set.mul_mem_mul (mem_commutatorSet_pow_three_of_map_eq_one (by simp [hdet, hcdet])
      (by simp [h])) hcS
  · rw [← mul_inv_cancel_right g c, pow_succ]
    refine Set.mul_mem_mul (mem_commutatorSet_pow_three_of_map_eq_one (by simp [hdet, hcdet])
      (by simp [h])) ?_
    rw [commutatorElement_inv]
    exact commutator_mem_commutatorSet _ _

/-- **The commutator subgroup of `GL₂(ℤ₂)`.** An element of `GL₂(ℤ₂)` is a product of commutators
exactly when its determinant is `1` and the cube of its reduction modulo `2` is `1`, that is, when
it lies in `SL₂(ℤ₂)` and its reduction lies in the alternating group `A₃` of `GL₂(𝔽₂) ≅ S₃`. -/
theorem mem_commutator_padicInt_two_iff {g : GL (Fin 2) ℤ_[2]} :
    g ∈ commutator (GL (Fin 2) ℤ_[2]) ↔
      GeneralLinearGroup.det g = 1 ∧ GeneralLinearGroup.map (toZMod (p := 2)) g ^ 3 = 1 := by
  refine ⟨fun hg ↦ ⟨Group.Abelianization.commutator_le_ker _ hg, ?_⟩, fun ⟨hdet, hg⟩ ↦ ?_⟩
  · have hle : (commutator (GL (Fin 2) ℤ_[2])).map (GeneralLinearGroup.map (toZMod (p := 2))) ≤
        commutator (GL (Fin 2) (ZMod 2)) := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact (GeneralLinearGroup.mem_commutator_fin_two_iff_pow_three_eq_one (Nat.card_zmod 2)).1
      (hle (Subgroup.mem_map_of_mem _ hg))
  · exact commutatorSet_pow_subset_commutator 4 (mem_commutatorSet_pow_four_padicInt_two hdet hg)

/-- The elementary matrix `[[1, 1], [0, 1]]` is not a product of commutators in `GL₂(ℤ₂)`: its
reduction modulo `2` is a transposition of `GL₂(𝔽₂) ≅ S₃`. So the commutator subgroup of `GL₂(ℤ₂)`
is a proper subgroup of `SL₂(ℤ₂)`, unlike for odd primes. -/
theorem transvectionUnit_one_notMem_commutator_padicInt_two :
    transvectionUnit (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : ℤ_[2]) ∉
      commutator (GL (Fin 2) ℤ_[2]) := by
  rw [mem_commutator_padicInt_two_iff, map_transvectionUnit, map_one]
  rintro ⟨-, h⟩
  rw [pow_three, ← transvectionUnit_add, ← transvectionUnit_add,
    ← transvectionUnit_zero (zero_ne_one : (0 : Fin 2) ≠ 1)] at h
  exact absurd (transvectionUnit_injective _ h) (by decide)

end Two

end TauCeti
