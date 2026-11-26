/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.GroupAlgebra.RelativeTrace

/-!
# Splitting through a trace from the trivial subgroup

Let `G` be a finite group and `V` a `k[G]`-module. If `φ : V → V` is a `k`-linear map whose sum
of conjugates `∑_g g⁻¹ φ(g ·)` is the identity of `V` (Higman's criterion for `H = 1`), then
every `k`-linear one-sided inverse `ψ` of a `k[G]`-linear map out of or onto `V` can be averaged
into a `k[G]`-linear one, by `ψ ↦ ∑_g g⁻¹ φ ψ(g ·)` or `ψ ↦ ∑_g g⁻¹ ψ φ(g ·)` as in Maschke's
theorem, with `φ` in place of `1 / |G|`. So if `V` is projective over `k` then it is projective
over `k[G]`.

The main source of such `φ` is multiplication by an element `a` of `k[G]` whose trace
`∑_{g ∈ G} g a g⁻¹ = Tr_1^G(a)` from the trivial subgroup acts as the identity on `V`. That
hypothesis passes to submodules, so over a field `k` every submodule of `V` has a complement and
`V` is semisimple.

## Main results

* `TauCeti.exists_leftInverse_of_sumOfConjugates_eq_id`,
  `TauCeti.exists_rightInverse_of_sumOfConjugates_eq_id`: averaging one-sided inverses through
  a `k`-linear map whose sum of conjugates is the identity.
* `TauCeti.moduleProjective_of_sumOfConjugates_eq_id`: such a module, projective over `k`, is
  projective over `k[G]`.
* `TauCeti.sumOfConjugates_distribSMul_toLinearMap_apply`: the sum of conjugates of
  multiplication by `a` is multiplication by `∑_g g a g⁻¹`.
* `TauCeti.isSemisimpleModule_of_forall_sum_conjRepresentation_smul_eq_self`: over a field, a
  module on which a trace `∑_g g a g⁻¹` from `1` acts as the identity is semisimple.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 11.3.4, pp. 198–199.
-/

public section

namespace TauCeti

open MonoidAlgebra

section Averaging

variable {k G : Type*} [CommRing k] [Group G] [Fintype G]
  {V W : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V] [AddCommGroup W] [Module k W]
  [Module (MonoidAlgebra k G) W] [IsScalarTower k (MonoidAlgebra k G) W]
  {φ : V →ₗ[k] V}

/-- **Averaging a retraction.** If a `k`-linear `φ : V → V` has sum of conjugates
`∑_g g⁻¹ φ(g ·)` equal to the identity, then a `k[G]`-linear map `i : V → W` with a `k`-linear
left inverse has a `k[G]`-linear left inverse. -/
theorem exists_leftInverse_of_sumOfConjugates_eq_id (hφ : φ.sumOfConjugates G = LinearMap.id)
    (i : V →ₗ[MonoidAlgebra k G] W) (π : W →ₗ[k] V) (hπ : ∀ v, π (i v) = v) :
    ∃ r : W →ₗ[MonoidAlgebra k G] V, ∀ v, r (i v) = v := by
  refine ⟨(φ ∘ₗ π).sumOfConjugatesEquivariant G, fun v => ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := k) v, ← hφ, LinearMap.sumOfConjugates_apply]
  rw [LinearMap.sumOfConjugatesEquivariant_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.conjugate_apply, LinearMap.conjugate_apply, LinearMap.comp_apply, ← i.map_smul,
    hπ]

/-- **Averaging a section.** If a `k`-linear `φ : V → V` has sum of conjugates
`∑_g g⁻¹ φ(g ·)` equal to the identity, then a `k[G]`-linear map `p : W → V` with a `k`-linear
right inverse has a `k[G]`-linear right inverse. -/
theorem exists_rightInverse_of_sumOfConjugates_eq_id (hφ : φ.sumOfConjugates G = LinearMap.id)
    (p : W →ₗ[MonoidAlgebra k G] V) (s : V →ₗ[k] W) (hs : ∀ v, p (s v) = v) :
    ∃ σ : V →ₗ[MonoidAlgebra k G] W, ∀ v, p (σ v) = v := by
  refine ⟨(s ∘ₗ φ).sumOfConjugatesEquivariant G, fun v => ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := k) v, ← hφ, LinearMap.sumOfConjugates_apply]
  rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.conjugate_apply, LinearMap.conjugate_apply, LinearMap.comp_apply, p.map_smul, hs]

/-- **Higman's criterion, easy direction, for `H = 1`.** A `k[G]`-module that is projective over
`k`, with a `k`-linear endomorphism `φ` whose sum of conjugates `∑_g g⁻¹ φ(g ·)` is the identity,
is projective over `k[G]`. -/
theorem moduleProjective_of_sumOfConjugates_eq_id [Module.Projective k V]
    (hφ : φ.sumOfConjugates G = LinearMap.id) :
    Module.Projective (MonoidAlgebra k G) V := by
  let p := Finsupp.linearCombination (MonoidAlgebra k G) (id : V → V)
  have hp : Function.Surjective p := fun v => ⟨Finsupp.single v 1, by simp [p]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (p.restrictScalars k) LinearMap.id hp
  obtain ⟨σ, hσ⟩ := exists_rightInverse_of_sumOfConjugates_eq_id hφ p s
    fun v => LinearMap.congr_fun hs v
  exact Module.Projective.of_split σ p (LinearMap.ext hσ)

/-- The sum of the conjugates `∑_g g⁻¹ a (g ·)` of multiplication by `a ∈ k[G]` is multiplication
by the trace `∑_g g a g⁻¹` from the trivial subgroup. -/
theorem sumOfConjugates_distribSMul_toLinearMap_apply (a : MonoidAlgebra k G) (v : V) :
    (DistribSMul.toLinearMap k V a).sumOfConjugates G v =
      (∑ g : G, conjRepresentation k G g a) • v := by
  rw [LinearMap.sumOfConjugates_apply, sum_conjRepresentation_eq_sum_inv_mul_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.conjugate_apply, DistribSMul.toLinearMap_apply, of_apply, of_apply, mul_smul,
    mul_smul]

end Averaging

section Field

variable {k G : Type*} [Field k] [Group G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V] {a : MonoidAlgebra k G}

/-- Over a field `k`, a `k[G]`-module on which a trace `∑_g g a g⁻¹` from the trivial subgroup
acts as the identity is semisimple: every submodule has a complement.

Unlike `TauCeti.moduleProjective_of_sumOfConjugates_eq_id`, this is stated for multiplication by
an element `a` of `k[G]` rather than for an arbitrary `k`-linear `φ`, so that the hypothesis
passes to submodules. For a general `φ` it fails: `φ(x) = x(1) • 1` on `k[G]` has
`∑_g g⁻¹ φ(g ·) = id`, but `k[G]` is not semisimple when the characteristic of `k` divides
`|G|`. -/
theorem isSemisimpleModule_of_forall_sum_conjRepresentation_smul_eq_self
    (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v) :
    IsSemisimpleModule (MonoidAlgebra k G) V where
  exists_isCompl N := by
    obtain ⟨π, hπ⟩ := (N.subtype.restrictScalars k).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    obtain ⟨r, hr⟩ := exists_leftInverse_of_sumOfConjugates_eq_id
      (LinearMap.ext fun v : N => by
        rw [sumOfConjugates_distribSMul_toLinearMap_apply, LinearMap.id_apply]
        exact Subtype.ext (ha v.val))
      N.subtype π fun v => LinearMap.congr_fun hπ v
    exact ⟨LinearMap.ker r, LinearMap.isCompl_of_proj hr⟩

end Field

end TauCeti
