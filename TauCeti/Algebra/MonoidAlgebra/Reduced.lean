/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Tactic.Ring
import TauCeti.Algebra.MonoidAlgebra.Frobenius
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Reduced group algebras and monoid algebras

Let `R` be a formally real commutative semiring, such as `ℕ`, `ℤ`, `ℚ` or `ℝ`, and let `G` be a
commutative group. Inversion on `G` induces the ring involution `σ` of `R[G]` with
`σ x g = x g⁻¹`. The coefficient of the identity in `x * σ x` is the sum of the squares of the
coefficients of `x` (`MonoidAlgebra.coeff_mul_mapDomainRingEquiv_inv_one`), so it vanishes only
when `x = 0`.

If `x ^ 2 = 0`, then `y = x * σ x` satisfies `y * σ y = x ^ 2 * σ x ^ 2 = 0`, so `y = 0` and then
`x = 0`. Hence `R[G]` is reduced (`MonoidAlgebra.isReduced_of_isFormallyReal`). No finiteness of
`G` is needed, and `G` may have torsion: for instance `ℤ[G]` is reduced for every commutative
group `G`.

Extending scalars from `ℚ`, which is formally real and perfect, the group algebra `R[G]` is
reduced for every reduced `ℚ`-algebra `R` (`MonoidAlgebra.isReduced_of_algebraRat`), although
such an `R`, for instance `ℂ`, need not be formally real.

In prime characteristic `p` the monoid matters. For a commutative ring `R` of characteristic `p`
and a commutative monoid `M`, the `p`-th power map of `R[M]` raises coefficients and monomials to
the `p`-th power, so `R[M]` is reduced exactly when `R` is reduced and the `p`-th power map of `M`
is injective (`MonoidAlgebra.isReduced_iff_isReduced_and_pow_injective`). Together with the
characteristic-zero case this gives the criterion over a domain `R` of exponential characteristic
`p`: the group algebra `R[G]` of a commutative group `G` is reduced exactly when `G` has no
`p`-torsion (`MonoidAlgebra.isReduced_iff_forall_pow_eq_one_imp_eq_one`). For a field this is the
algebraic form of the statement that the diagonalizable group with character group `G` is
geometrically reduced exactly when `G` has no `p`-torsion.

Each statement has an additive form for `AddMonoidAlgebra`.

## References

* D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977: the trace-form argument
  for semiprimeness of group algebras in characteristic zero.
* J. S. Milne, *Algebraic Groups* (2017), Remark 12.5: the criterion in terms of `p`-torsion.
-/

public section

namespace MonoidAlgebra

section IsFormallyReal

variable {R G : Type*} [CommSemiring R] [IsFormallyReal R] [CommGroup G]

@[to_additive (dont_translate := R) eq_zero_of_coeff_mul_mapDomainRingEquiv_neg_zero]
private theorem eq_zero_of_coeff_mul_mapDomainRingEquiv_inv_one {x : MonoidAlgebra R G}
    (h : (x * mapDomainRingEquiv R (MulEquiv.inv G) x).coeff 1 = 0) : x = 0 := by
  classical
  rw [coeff_mul_mapDomainRingEquiv_inv_one] at h
  ext g
  by_cases hg : g ∈ x.coeff.support
  · rw [← Finset.add_sum_erase _ _ hg] at h
    exact IsFormallyReal.eq_zero_of_mul_self_eq_zero <|
      IsFormallyReal.eq_zero_of_add_right (.mul_self _) (.sum_mul_self _ _) h
  · simpa using hg

/-- The group algebra of a commutative group over a formally real commutative semiring is
reduced. -/
@[to_additive (dont_translate := R)
/-- The group algebra of a commutative additive group over a formally real commutative semiring
is reduced. -/]
instance isReduced_of_isFormallyReal : IsReduced (MonoidAlgebra R G) := by
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro x hx
  have hσ (z : MonoidAlgebra R G) :
      mapDomainRingEquiv R (MulEquiv.inv G) (mapDomainRingEquiv R (MulEquiv.inv G) z) = z := by
    ext; simp
  -- `y = x * σ x` satisfies `y * σ y = x ^ 2 * σ x ^ 2 = 0`, so `y = 0`.
  have hy : x * mapDomainRingEquiv R (MulEquiv.inv G) x = 0 := by
    refine eq_zero_of_coeff_mul_mapDomainRingEquiv_inv_one ?_
    rw [map_mul, hσ]
    generalize mapDomainRingEquiv R (MulEquiv.inv G) x = y
    simp [show x * y * (y * x) = x ^ 2 * y ^ 2 by ring, hx]
  exact eq_zero_of_coeff_mul_mapDomainRingEquiv_inv_one (by simp [hy])

end IsFormallyReal

section AlgebraRat

variable {R G : Type*} [CommRing R] [Algebra ℚ R] [IsReduced R] [CommGroup G]

/-- The group algebra of a commutative group over a reduced `ℚ`-algebra is reduced. -/
@[to_additive (dont_translate := R)
/-- The group algebra of a commutative additive group over a reduced `ℚ`-algebra is reduced. -/]
instance isReduced_of_algebraRat : IsReduced (MonoidAlgebra R G) :=
  -- `R[G]` is the extension of scalars `R ⊗[ℚ] ℚ[G]` of the rational group algebra, which is
  -- reduced because `ℚ` is formally real; the tensor product is reduced because `ℚ` is perfect.
  isReduced_of_injective (scalarTensorEquiv ℚ R (M := G)).symm
    (scalarTensorEquiv ℚ R (M := G)).symm.injective

end AlgebraRat

section CharP

variable {R M : Type*} [CommRing R] [CommMonoid M] (p : ℕ)

/-- **A commutative monoid algebra in prime characteristic `p` is reduced exactly when its
coefficient ring is reduced and the `p`-th power map of the monoid is injective.** -/
@[to_additive (dont_translate := R)
/-- **A commutative additive monoid algebra in prime characteristic `p` is reduced exactly when
its coefficient ring is reduced and multiplication by `p` on the monoid is injective.** -/]
theorem isReduced_iff_isReduced_and_pow_injective [Fact p.Prime] [CharP R p] :
    IsReduced (MonoidAlgebra R M) ↔ IsReduced R ∧ Function.Injective fun m : M ↦ m ^ p := by
  have hp : p.Prime := Fact.out
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.ne_one
  refine ⟨fun h ↦ ⟨isReduced_of_injective (singleOneRingHom (R := R) (M := M))
      single_right_injective, fun m n hmn ↦ ?_⟩, fun ⟨_, hM⟩ ↦ ?_⟩
  · have hmn : m ^ p = n ^ p := hmn
    refine single_left_injective (one_ne_zero (α := R))
      (frobenius_inj (MonoidAlgebra R M) p ?_)
    simp [frobenius_def, hmn]
  · rw [isReduced_iff_pow_one_lt p hp.one_lt]
    intro x hx
    have hR : Function.Injective fun r : R ↦ r ^ p := frobenius_inj R p
    exact pow_expChar_injective p hR hM (by simpa [zero_pow hp.ne_zero] using hx)

end CharP

section ExpChar

variable (R : Type*) [CommRing R] (G : Type*) [CommGroup G] (p : ℕ)

/-- **The group algebra of a commutative group over a domain of exponential characteristic `p`
is reduced exactly when the group has no `p`-torsion.** In characteristic zero, where `p = 1`,
the condition is empty and every such group algebra is reduced. -/
@[to_additive (dont_translate := R)
/-- **The group algebra of a commutative additive group over a domain of exponential
characteristic `p` is reduced exactly when the group has no `p`-torsion.** In characteristic
zero, where `p = 1`, the condition is empty and every such group algebra is reduced. -/]
theorem isReduced_iff_forall_pow_eq_one_imp_eq_one [IsDomain R] [ExpChar R p] :
    IsReduced (MonoidAlgebra R G) ↔ ∀ g : G, g ^ p = 1 → g = 1 := by
  rcases ‹ExpChar R p› with _ | hp
  · have : CharZero (FractionRing R) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
    exact iff_of_true
      (isReduced_of_injective (mapRingHom G (algebraMap R (FractionRing R)))
        (map_injective _ (IsFractionRing.injective R (FractionRing R))))
      fun g hg ↦ (pow_one g).symm.trans hg
  · have : Fact p.Prime := ⟨hp⟩
    rw [isReduced_iff_isReduced_and_pow_injective p, and_iff_right (inferInstance : IsReduced R)]
    have hpow : ⇑(powMonoidHom p : G →* G) = fun g ↦ g ^ p := funext (powMonoidHom_apply p)
    simpa only [hpow] using injective_iff_map_eq_one (powMonoidHom p : G →* G)

end ExpChar

end MonoidAlgebra
