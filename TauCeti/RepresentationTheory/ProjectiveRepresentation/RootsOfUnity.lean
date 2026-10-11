/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Linearization
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Root-of-unity representatives of torsion cohomology classes

Over an algebraically closed field, a class in `H²(G, kˣ)` is killed by `n : ℕ` exactly
when it has a normalized factor-set representative taking values in the `n`-th roots of
unity. No finiteness assumption on `G` or restriction on the characteristic is needed.

For constructing central extensions with prescribed finite cyclic kernels, this allows
each torsion class to be represented using its own order, rather than the order of `G`.
The forward implication supplies an explicit normalized scalar rescaling of any given
representative.

A projective representation with a class killed by `n` therefore linearizes, up to a
normalized scalar rescaling, on a central extension with kernel the `n`-th roots of unity.
We use the existing factor-set classification, restriction to roots of unity, and
linearization constructions.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti.FactorSet

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [Field k] [Group G]

/-- A natural number `n` kills a cohomology class over an algebraically closed field exactly
when the class has a normalized representative valued in the `n`-th roots of unity. -/
theorem nsmul_eq_zero_iff_exists_factorSet_pow_eq_one [IsAlgClosed k] {n : ℕ}
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) :
    n • x = 0 ↔ ∃ β : FactorSet G kˣ, β.cohomologyClass = x ∧ ∀ p, β p ^ n = 1 := by
  constructor
  · intro hx
    obtain ⟨α, rfl⟩ := exists_cohomologyClass_eq x
    have hroot : n ≠ 0 → Function.Surjective (fun z : kˣ ↦ z ^ n) := by
      intro hn a
      have hn : 0 < n := Nat.pos_of_ne_zero hn
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) hn
      have hz0 : z ≠ 0 := by
        intro h
        exact a.ne_zero (by simpa [h, zero_pow hn.ne'] using hz.symm)
      exact ⟨Units.mk0 z hz0, Units.ext hz⟩
    exact α.exists_cohomologyClass_eq_and_pow_eq_one hroot hx
  · rintro ⟨β, rfl, hβ⟩
    apply (β.nsmul_cohomologyClass_eq_zero_iff n).2
    exact ⟨fun _ ↦ 1, fun g h ↦ by simp [hβ]⟩

end TauCeti.FactorSet

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [Field k] [IsAlgClosed k] [Group G]
  {V : Type*} [AddCommMonoid V] [Module k V]

/-- A projective representation whose class is killed by a natural number `n` linearizes
on a central extension by the `n`-th roots of unity. The kernel acts by its own scalars,
and the action at the canonical section agrees with the original lift after a normalized
scalar rescaling. -/
theorem IsProjectiveRep.exists_rootsOfUnityExtension_linearization
    {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ} (hρ : IsProjectiveRep ρ α)
    {n : ℕ} (hclass : n • hρ.cohomologyClass = 0) :
    ∃ (β : FactorSet G (rootsOfUnity n k)) (π : β.Extension →* (V ≃ₗ[k] V))
      (c : G → kˣ), c 1 = 1 ∧ ∀ x,
        π x = (ρ (FactorSet.rightHom β x)).trans
          (LinearEquiv.smulOfUnit ((x.left : kˣ) * c (FactorSet.rightHom β x))) := by
  rw [IsProjectiveRep.cohomologyClass_def] at hclass
  obtain ⟨γ, hγ, hpow⟩ :=
    (FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one hρ.factorSet.cohomologyClass).1 hclass
  let β := (γ.isFactorSet_curry trivialMulDistribMulAction_smul).toRootsOfUnityFactorSet
    (fun g h ↦ hpow (g, h))
  let f : rootsOfUnity n k →*[G] kˣ :=
    { (rootsOfUnity n k).subtype with map_smul' _ _ := rfl }
  have hf (a : rootsOfUnity n k) : f a = (a : kˣ) := rfl
  have hmap : β.map f = γ := by
    apply FactorSet.ext
    intro p
    simp only [FactorSet.map_apply, hf]
    exact IsFactorSet.coe_toRootsOfUnityFactorSet_apply _ _ p
  obtain ⟨c, π, hc, hπ⟩ := hρ.exists_linearization_of_characterTransgression_eq β f
    (by rw [hmap, IsProjectiveRep.cohomologyClass_def]; exact hγ)
  refine ⟨β, π, c, hc, fun x ↦ ?_⟩
  simpa only [FactorSet.rightHom_apply, hf] using hπ x

end TauCeti
