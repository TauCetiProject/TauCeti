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

Let `G` be a finite group and `x = ∑_{g ∈ G} g a g⁻¹ = Tr_1^G(a)` a trace from the trivial
subgroup in `k[G]`. If `x` acts as the identity on a `k[G]`-module `V`, then every `k`-linear
one-sided inverse `φ` of a `k[G]`-linear map out of or onto `V` can be averaged into a
`k[G]`-linear one, by `φ ↦ ∑_g g⁻¹ a φ(g ·)` as in Maschke's theorem, with `a` in place of
`1 / |G|`. So if `V` is projective over `k` then it is projective over `k[G]`, and over a field
`k` every submodule of `V` has a complement, so `V` is semisimple.

## Main results

* `TauCeti.exists_leftInverse_of_forall_sum_conj_smul_eq`,
  `TauCeti.exists_rightInverse_of_forall_sum_conj_smul_eq`: averaging one-sided inverses through
  a trace from `1` acting as the identity.
* `TauCeti.moduleProjective_of_forall_sum_conj_smul_eq`: such a module, projective over `k`, is
  projective over `k[G]`.
* `TauCeti.isSemisimpleModule_of_forall_sum_conj_smul_eq`: over a field, such a module is
  semisimple.

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

/-- The sum of the conjugates by `g` of `a ∘ φ` applied to `w` is `∑_g g⁻¹ a φ(g w)`. -/
private theorem sumOfConjugatesEquivariant_lsmul_comp_apply (a : MonoidAlgebra k G)
    (φ : W →ₗ[k] V) (w : W) :
    (DistribSMul.toLinearMap k V a ∘ₗ φ).sumOfConjugatesEquivariant G w =
      ∑ g : G, of k G g⁻¹ • a • φ (of k G g • w) := by
  simp only [LinearMap.sumOfConjugatesEquivariant_apply, LinearMap.conjugate_apply,
    LinearMap.comp_apply, DistribSMul.toLinearMap_apply, of_apply]

variable {a : MonoidAlgebra k G}
  (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v)
include ha

/-- **Averaging a retraction.** If the trace `∑_g g a g⁻¹` acts as the identity on `V`, then a
`k[G]`-linear map `i : V → W` with a `k`-linear left inverse has a `k[G]`-linear left inverse. -/
theorem exists_leftInverse_of_forall_sum_conj_smul_eq (i : V →ₗ[MonoidAlgebra k G] W)
    (π : W →ₗ[k] V) (hπ : ∀ v, π (i v) = v) :
    ∃ r : W →ₗ[MonoidAlgebra k G] V, ∀ v, r (i v) = v := by
  refine ⟨(DistribSMul.toLinearMap k V a ∘ₗ π).sumOfConjugatesEquivariant G, fun v => ?_⟩
  rw [sumOfConjugatesEquivariant_lsmul_comp_apply]
  conv_rhs =>
    rw [← ha v, ← sum_of_inv_mul_mul_of_eq_sum_conjRepresentation, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← i.map_smul, hπ, smul_smul, smul_smul]

/-- **Averaging a section.** If the trace `∑_g g a g⁻¹` acts as the identity on `V`, then a
`k[G]`-linear map `p : W → V` with a `k`-linear right inverse has a `k[G]`-linear right
inverse. -/
theorem exists_rightInverse_of_forall_sum_conj_smul_eq (p : W →ₗ[MonoidAlgebra k G] V)
    (s : V →ₗ[k] W) (hs : ∀ v, p (s v) = v) :
    ∃ σ : V →ₗ[MonoidAlgebra k G] W, ∀ v, p (σ v) = v := by
  refine ⟨(DistribSMul.toLinearMap k W a ∘ₗ s).sumOfConjugatesEquivariant G, fun v => ?_⟩
  rw [sumOfConjugatesEquivariant_lsmul_comp_apply, map_sum]
  conv_rhs =>
    rw [← ha v, ← sum_of_inv_mul_mul_of_eq_sum_conjRepresentation, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [p.map_smul, p.map_smul, hs, smul_smul, smul_smul]

omit ha in
/-- **Higman's criterion, easy direction, relative to a trace.** A `k[G]`-module that is
projective over `k`, on which a trace `∑_g g a g⁻¹` from the trivial subgroup acts as the
identity, is projective over `k[G]`. -/
theorem moduleProjective_of_forall_sum_conj_smul_eq [Module.Projective k V]
    (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v) :
    Module.Projective (MonoidAlgebra k G) V := by
  let p := Finsupp.linearCombination (MonoidAlgebra k G) (id : V → V)
  have hp : Function.Surjective p := fun v => ⟨Finsupp.single v 1, by simp [p]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (p.restrictScalars k) LinearMap.id hp
  obtain ⟨σ, hσ⟩ := exists_rightInverse_of_forall_sum_conj_smul_eq ha p s
    fun v => LinearMap.congr_fun hs v
  exact Module.Projective.of_split σ p (LinearMap.ext hσ)

end Averaging

section Field

variable {k G : Type*} [Field k] [Group G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V] {a : MonoidAlgebra k G}

/-- Over a field `k`, a `k[G]`-module on which a trace `∑_g g a g⁻¹` from the trivial subgroup
acts as the identity is semisimple: every submodule has a complement. -/
theorem isSemisimpleModule_of_forall_sum_conj_smul_eq
    (ha : ∀ v : V, (∑ g : G, conjRepresentation k G g a) • v = v) :
    IsSemisimpleModule (MonoidAlgebra k G) V where
  exists_isCompl N := by
    obtain ⟨π, hπ⟩ := (N.subtype.restrictScalars k).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    obtain ⟨r, hr⟩ := exists_leftInverse_of_forall_sum_conj_smul_eq
      (fun v : N => Subtype.ext (ha v.val)) N.subtype π fun v => LinearMap.congr_fun hπ v
    exact ⟨LinearMap.ker r, LinearMap.isCompl_of_proj hr⟩

end Field

end TauCeti
