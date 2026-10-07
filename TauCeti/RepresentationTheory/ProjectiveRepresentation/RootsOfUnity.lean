/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.SchurMultiplier
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
  obtain ⟨c, hc⟩ := (FactorSet.cohomologyClass_eq_iff γ hρ.factorSet).1 hγ
  simp only [trivialMulDistribMulAction_smul, IsProjectiveRep.factorSet_apply] at hc
  have hc1 : c 1 = 1 := by simpa [hρ.isFactorSet.one_left] using hc 1 1
  let β := (γ.isFactorSet_curry trivialMulDistribMulAction_smul).toRootsOfUnityFactorSet
    (fun g h ↦ hpow (g, h))
  have hval (p : G × G) : (β p : kˣ) = γ p :=
    IsFactorSet.coe_toRootsOfUnityFactorSet_apply _ _ p
  let f : rootsOfUnity n k →*[G] kˣ :=
    { (rootsOfUnity n k).subtype with map_smul' _ _ := rfl }
  have hf (a : rootsOfUnity n k) : f a = (a : kˣ) := rfl
  have hβ : Function.curry ⇑(β.map f) =
      fun g h ↦ c g * c h * (c (g * h))⁻¹ * α g h := by
    funext g h
    simp only [Function.curry, FactorSet.map_apply, hf, hval]
    have heq := (div_eq_iff_eq_mul).1 (hc g h).symm
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using heq
  have hrep : IsProjectiveRep
      (fun g ↦ (ρ g).trans (LinearEquiv.smulOfUnit (c g))) (Function.curry ⇑(β.map f)) := by
    rw [hβ]
    exact hρ.rescale c hc1
  refine ⟨β, (hrep.linearization trivialMulDistribMulAction_smul).comp (β.mapExtension f),
    c, hc1, fun x ↦ ?_⟩
  apply LinearEquiv.ext
  intro v
  simp [MonoidHom.comp_apply, IsProjectiveRep.linearization_apply,
    LinearEquiv.smulOfUnit_apply, smul_smul, hf]

end TauCeti
