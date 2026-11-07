/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.ClassTwo
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic
public import TauCeti.RingTheory.DividedPowers.ClassTwo

/-!
# The root subgroup of a central bracket

If two nilpotent root operators have a bracket commuting with both, the divided powers of
that bracket preserve every Kostant-stable lattice. Its exponential therefore defines a
one-parameter subgroup over arbitrary commutative rings, without inverting factorials.
The Chevalley commutator formula identifies it with the commutator of the original root
subgroups at the product parameter. This constructs the extra root subgroup in a single-bond
rank-two subsystem without requiring it among the original distinguished generators.

The integral step uses `Subring.dividedPower_mem_of_commutator_eq`; the exponential identity
uses `baseChangeExp_mul_baseChangeExp_of_commutator_eq`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
  {I κ : Type*} {V : Type v} [AddCommGroup V] [Module ℚ V]
  (e : I → L) (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ a ∈ kostantForm e h, ∀ v ∈ M, ρ a v ∈ M)
  {i j : I}

attribute [local instance high] Algebra.toModule

include hM in
/-- Divided powers of a bracket centralizing its two factors preserve a Kostant-stable lattice.
The bracket need not be one of the distinguished root vectors. -/
theorem dividedPower_lie_apply_mem
    (hi : ⁅e i, ⁅e i, e j⁆⁆ = 0) (hj : ⁅e j, ⁅e i, e j⁆⁆ = 0)
    (n : ℕ) {v : V} (hv : v ∈ M) :
    Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ⁅e i, e j⁆)) v ∈ M := by
  have hz := ((kostantForm e h).map ρ.toRingHom).dividedPower_mem_of_commutator_eq
    ((sub_eq_iff_eq_add').mp (mul_sub_mul_eq_map_ι_lie ρ (e i) (e j)))
    (commute_of_lie_eq_zero ρ hi) (commute_of_lie_eq_zero ρ hj)
    (dividedPower_mem_map_kostantForm e h ρ i)
    (dividedPower_mem_map_kostantForm e h ρ j) n
  obtain ⟨a, ha, heq⟩ := hz
  rw [← heq]
  exact hM a ha v hv

/-- The one-parameter subgroup of the bracket of two root operators which commute with that
bracket. It is the integral divided-power exponential, not a choice of a root vector. -/
noncomputable def kostantBracketRootSubgroupParam
    (hi : ⁅e i, ⁅e i, e j⁆⁆ = 0) (hj : ⁅e j, ⁅e i, e j⁆⁆ = 0)
    (hni : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (A : CommAlgCat.{w} ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).symm.toMonoidHom.comp
    (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ⁅e i, e j⁆)) M
      (fun n _ hv ↦ dividedPower_lie_apply_mem e h ρ M hM hi hj n hv)
      (isNilpotent_map_ι_lie_of_isNilpotent ρ hi hj hni))

/-- The bracket subgroup acts by the divided-power exponential of the bracket operator. -/
theorem kostantBracketRootSubgroupParam_val
    (hi : ⁅e i, ⁅e i, e j⁆⁆ = 0) (hj : ⁅e j, ⁅e i, e j⁆⁆ = 0)
    (hni : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (A : CommAlgCat.{w} ℤ) (t : Multiplicative A) :
    (kostantBracketRootSubgroupParam e h ρ M hM hi hj hni A t).val =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ⁅e i, e j⁆)) M
        (fun n _ hv ↦ dividedPower_lie_apply_mem e h ρ M hM hi hj n hv)
        (Multiplicative.toAdd t) := by
  have heq :
      (kostantBracketRootSubgroupParam e h ρ M hM hi hj hni A t).toLinearEquiv =
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ⁅e i, e j⁆)) M
          (fun n _ hv ↦ dividedPower_lie_apply_mem e h ρ M hM hi hj n hv)
          (isNilpotent_map_ι_lie_of_isNilpotent ρ hi hj hni) t := by
    rw [kostantBracketRootSubgroupParam]
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).apply_symm_apply _
  apply LinearMap.ext
  intro v
  rw [← LinearMap.GeneralLinearGroup.coe_toLinearEquiv, heq, coe_baseChangeExpHom]

/-- The class-two Chevalley relation, constructing the extra root subgroup from the bracket:
`[xᵢ(t), xⱼ(u)] = x_[i,j](tu)`. It holds over every commutative value ring. -/
theorem commutatorElement_kostantRootSubgroupParam_eq_bracket
    (hi : ⁅e i, ⁅e i, e j⁆⁆ = 0) (hj : ⁅e j, ⁅e i, e j⁆⁆ = 0)
    (hni : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hnj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (A : CommAlgCat.{w} ℤ) (t u : A) :
    ⁅kostantRootSubgroupParam e h ρ M hM i hni A (Multiplicative.ofAdd t),
        kostantRootSubgroupParam e h ρ M hM j hnj A (Multiplicative.ofAdd u)⁆ =
      kostantBracketRootSubgroupParam e h ρ M hM hi hj hni A
        (Multiplicative.ofAdd (t * u)) := by
  let x := kostantRootSubgroupParam e h ρ M hM i hni A (Multiplicative.ofAdd t)
  let y := kostantRootSubgroupParam e h ρ M hM j hnj A (Multiplicative.ofAdd u)
  let z := kostantBracketRootSubgroupParam e h ρ M hM hi hj hni A
    (Multiplicative.ofAdd (t * u))
  have hxy : x * y = y * z * x := by
    apply Units.ext
    simp only [Units.val_mul]
    -- Evaluate the three bundled subgroups before applying the integral exponential identity.
    have hx := LinearMap.ext (kostantRootSubgroupParam_val_apply e h ρ M hM i hni A
      (Multiplicative.ofAdd t))
    have hy := LinearMap.ext (kostantRootSubgroupParam_val_apply e h ρ M hM j hnj A
      (Multiplicative.ofAdd u))
    rw [hx, hy, kostantBracketRootSubgroupParam_val]
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M
      ((sub_eq_iff_eq_add').mp (mul_sub_mul_eq_map_ι_lie ρ (e i) (e j)))
      (commute_of_lie_eq_zero ρ hi) (commute_of_lie_eq_zero ρ hj) hni hnj _ _ _ t u
  have hyz : Commute y z := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [LinearMap.ext (kostantRootSubgroupParam_val_apply e h ρ M hM j hnj A
      (Multiplicative.ofAdd u)), kostantBracketRootSubgroupParam_val]
    exact commute_baseChangeExp M (commute_of_lie_eq_zero ρ hj) _ _ _ _
  simp only [commutatorElement_def]
  rw [hxy, mul_inv_cancel_right, hyz.eq, mul_inv_cancel_right]

end TauCeti.UniversalEnvelopingAlgebra
