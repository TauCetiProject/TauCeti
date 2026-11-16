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

Generators of second cohomology of prescribed orders `n i` are the transgressions of the
coordinate characters of one factor set with values in `∏ i, μ_{n i}`
(`TauCeti.exists_factorSet_surjective_characterTransgression`).

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

variable (k G) in
/-- If elements `x i` killed by `n i` generate `H²(G, kˣ)`, then some factor set with values in
`∏ i, μ_{n i}` has surjective character transgression. -/
theorem exists_factorSet_surjective_characterTransgression {ι : Type} [Fintype ι]
    (n : ι → ℕ)
    (x : ι → groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) (hx : ∀ i, n i • x i = 0)
    (hgen : ∀ y, ∃ c : ι → ℕ, y = ∑ i, c i • x i) :
    ∃ α : FactorSet G (∀ i, rootsOfUnity (n i) k),
      Function.Surjective (α.characterTransgression (A := kˣ)) := by
  classical
  choose β hβ hpow using fun i ↦
    (FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one (x i)).mp (hx i)
  let γ (i : ι) : FactorSet G (rootsOfUnity (n i) k) :=
    ((β i).isFactorSet_curry trivialMulDistribMulAction_smul).toRootsOfUnityFactorSet
      (fun g h ↦ hpow i (g, h))
  -- Assemble their root-valued representatives into one central extension.
  let M := ∀ i, rootsOfUnity (n i) k
  let : MulDistribMulAction G M := trivialMulDistribMulAction G M
  -- Use the same action for characters and transgression: otherwise bare scalar-action
  -- inference on the function type M can select the pointwise Pi instance.
  let : SMul G M := (inferInstance : MulDistribMulAction G M).toMulAction.toSMul
  let α : FactorSet G M :=
    { toFun p i := γ i p
      isMulCocycle₂' g h j := by
        funext i
        exact (γ i).isMulCocycle₂ g h j
      map_one_one' := by
        funext i
        exact (γ i).map_one_one }
  have hα (p : G × G) (i : ι) : α p i = γ i p := rfl
  have hγ (i : ι) (p : G × G) : (γ i p : kˣ) = β i p :=
    IsFactorSet.coe_toRootsOfUnityFactorSet_apply _ _ p
  let ev (i : ι) : M →*[G] kˣ :=
    { (rootsOfUnity (n i) k).subtype.comp (Pi.evalMonoidHom _ i) with
      map_smul' _ _ := rfl }
  have hev (i : ι) (a : M) : ev i a = (a i : kˣ) := rfl
  let χ (i : ι) : Additive (equivariantCharacterSubgroup G M kˣ) :=
    Additive.ofMul ((equivariantCharacterEquiv G M kˣ).symm (ev i))
  have hχ (i : ι) : α.characterTransgression (χ i) = x i := by
    rw [FactorSet.characterTransgression_apply]
    have heq : α.map (equivariantCharacterEquiv G M kˣ (χ i).toMul) = β i := by
      ext p
      simp only [χ, toMul_ofMul, Equiv.apply_symm_apply, FactorSet.map_apply]
      simp only [hev, hα, hγ]
    rw [heq]
    exact hβ i
  -- Every cyclic generator is the transgression of its coordinate character.
  refine ⟨α, fun y ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hgen y
  exact ⟨∑ i, c i • χ i, by simp only [map_sum, map_nsmul, hχ]⟩

end TauCeti
