/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Finite
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.RootsOfUnity
import Mathlib.Algebra.CharP.Reduced
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The characteristic does not divide the order of a factor-set class

Over an algebraically closed field of exponential characteristic `p`, multiplication by `p`
has trivial kernel on `H²(G, kˣ)`. A class killed by `p` has a normalized representative with
values in the `p`-th roots of unity, and Frobenius injectivity makes all those values one.
Consequently every class of finite order has order nonzero in the coefficient field.

This permits finite cyclic summands of second cohomology to be realized by roots of unity
of their exact orders, including in positive characteristic. These kernels are used to
construct finite central stem extensions with bijective character transgression.
No finiteness assumption on the group is needed for the torsion statements.
For a finite group, `TauCeti.exists_cyclic_generators_schurMultiplier` decomposes second
cohomology into cyclic summands whose orders are nonzero in the field.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
* `TauCeti.FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one`, the root-of-unity
  representative criterion.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [Field k] [IsAlgClosed k] [Group G]

/-- The second cohomology with multiplicative field coefficients has no torsion at the
exponential characteristic of an algebraically closed field. -/
@[simp]
theorem schurMultiplier_nsmul_eq_zero_iff (p : ℕ) [ExpChar k p]
    (x : schurMultiplier k G) : p • x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  obtain ⟨β, hβ, hpow⟩ :=
    (FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one x).mp hx
  have htriv : β = FactorSet.trivial G kˣ := by
    apply FactorSet.ext
    intro q
    rw [FactorSet.trivial_apply]
    apply Units.ext
    apply frobenius_inj k p
    simpa only [frobenius_def, Units.val_pow_eq_pow_val, Units.val_one, one_pow] using
      congrArg Units.val (hpow q)
  exact hβ.symm.trans (htriv ▸ FactorSet.cohomologyClass_trivial)

/-- The finite order of a second-cohomology class is not divisible by the characteristic
of the algebraically closed coefficient field. -/
theorem schurMultiplier_natCast_addOrderOf_ne_zero (x : schurMultiplier k G)
    (hx : addOrderOf x ≠ 0) : (addOrderOf x : k) ≠ 0 := by
  intro hzero
  have hdiv := (ringChar.spec k (addOrderOf x)).mp hzero
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    have hkill : ringChar k • ((addOrderOf x / ringChar k) • x) = 0 := by
      simp only [← mul_nsmul, Nat.div_mul_cancel hdiv, addOrderOf_nsmul_eq_zero]
    have hsmall := (schurMultiplier_nsmul_eq_zero_iff (ringChar k) _).mp hkill
    exact (Nat.not_dvd_of_pos_of_lt (Nat.div_pos (Nat.le_of_dvd
      (Nat.pos_of_ne_zero hx) hdiv) hp.pos)
      (Nat.div_lt_self (Nat.pos_of_ne_zero hx) hp.one_lt))
        (addOrderOf_dvd_of_nsmul_eq_zero hsmall)
  · exact hx (zero_dvd_iff.mp (hp ▸ hdiv))

variable (k G) [Finite G] in
/-- The second cohomology `H²(G, kˣ)` of a finite group has cyclic generators `x i` whose orders
`n i` are nonzero in `k`, and its cardinality is the product of the orders. -/
theorem exists_cyclic_generators_schurMultiplier :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ)
      (x : ι → groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)),
      (∀ i, (n i : k) ≠ 0) ∧ (∀ i, n i • x i = 0) ∧
      (∀ y, ∃ c : ι → ℕ, y = ∑ i, c i • x i) ∧
      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) = ∏ i, n i := by
  classical
  -- Choose cyclic generators of second cohomology, each with its own annihilating order.
  let : Finite (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) :=
    inferInstanceAs (Finite (schurMultiplier k G))
  obtain ⟨ι, hι, n, hn, ⟨e₀⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite'
      (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ))
  let e := e₀.trans (DirectSum.addEquivProd (fun i ↦ ZMod (n i)))
  let x (i : ι) : groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ) := e.symm (Pi.single i 1)
  have hne : ∀ i, NeZero (n i) := fun i ↦ ⟨by have := hn i; omega⟩
  have horder (i : ι) : addOrderOf (x i) = n i := by
    dsimp only [x]
    rw [e.symm.addOrderOf_eq]
    simpa only [AddMonoidHom.single_apply, ZMod.addOrderOf_one] using
      addOrderOf_injective (AddMonoidHom.single (fun j ↦ ZMod (n j)) i)
        (by simpa only [AddMonoidHom.coe_single] using
          Pi.single_injective (M := fun j ↦ ZMod (n j)) i) (1 : ZMod (n i))
  have hx (i : ι) : n i • x i = 0 := horder i ▸ addOrderOf_nsmul_eq_zero (x i)
  refine ⟨ι, hι, n, x, fun i ↦ ?_, hx, fun y ↦ ⟨fun i ↦ (e y i).val, ?_⟩, ?_⟩
  · rw [← horder i]
    exact schurMultiplier_natCast_addOrderOf_ne_zero (x i) (horder i ▸ (hne i).out)
  · apply e.injective
    simp only [x]
    rw [map_sum e]
    simp_rw [map_nsmul e, AddEquiv.apply_symm_apply]
    simp only [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact (Finset.univ_sum_single (e y)).symm
  · rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]

end TauCeti
