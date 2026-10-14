/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.SchurMultiplier
public import TauCeti.GroupTheory.GroupExtension.Character.Basic

/-!
# Lifting projective representations over a prescribed extension

A projective representation lifts over a factor-set extension with kernel character `χ`
exactly when its second-cohomology class is the transgression of `χ`. The lifting formula
holds on every extension element, with the kernel acting by the specified scalars.

Consequently, surjective character transgression guarantees simultaneous lifting of all
projective representations. Conversely, lifting all projective actions on the free module
`G →₀ k` already implies surjectivity: every cohomology class occurs on that module.
This criterion allows the universal lifting property to be checked independently of the
construction of an extension or the containment of its kernel in the commutator subgroup.

The coefficient action is trivial. The kernel action may be arbitrary, with `χ` equivariant;
central extensions are the special case of a trivial kernel action. Neither finiteness nor
algebraic closure is required. Faithful scalar action is needed only for the converse.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

section

variable {k G M : Type} {V : Type*} [CommSemiring k] [Group G] [CommGroup M]
  [MulDistribMulAction G M] [AddCommMonoid V] [Module k V]

variable {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

/-- A projective action lifts over a prescribed factor-set extension with kernel character
`χ` whenever its cohomology class is the transgression of `χ`. -/
theorem IsProjectiveRep.exists_linearization_of_characterTransgression_eq
    (hρ : IsProjectiveRep ρ α) (γ : FactorSet G M) (χ : M →*[G] kˣ)
    (hχ : (γ.map χ).cohomologyClass = hρ.cohomologyClass) :
    ∃ (c : G → kˣ) (π : γ.Extension →* (V ≃ₗ[k] V)), c 1 = 1 ∧
      ∀ x, π x = (ρ x.right).trans (LinearEquiv.smulOfUnit (χ x.left * c x.right)) := by
  rw [IsProjectiveRep.cohomologyClass_def] at hχ
  obtain ⟨c, hc⟩ := (FactorSet.cohomologyClass_eq_iff _ _).mp hχ
  have hc1 : c 1 = 1 := by
    simpa using hc 1 1
  have hfactor (g h : G) : c g * c h * (c (g * h))⁻¹ * α g h = χ (γ (g, h)) := by
    have heq : c g * c h * (c (g * h))⁻¹ = χ (γ (g, h)) / α g h := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hc g h
    simpa using congrArg (fun a ↦ a * α g h) heq
  have hrs : IsProjectiveRep (fun g ↦ (ρ g).trans (LinearEquiv.smulOfUnit (c g)))
      (Function.curry ⇑(γ.map χ)) := by
    convert hρ.rescale c hc1 using 1
    funext g h
    simpa only [Function.curry, FactorSet.map_apply] using (hfactor g h).symm
  refine ⟨c, (hrs.linearization trivialMulDistribMulAction_smul).comp (γ.mapExtension χ),
    hc1, fun x ↦ LinearEquiv.ext fun v ↦ ?_⟩
  simp [LinearEquiv.smulOfUnit_apply, smul_smul]

/-- A projective action lifts over a prescribed extension with kernel character `χ` exactly
when its cohomology class is the transgression of `χ`. Faithful scalar action lets the linear
action determine its factor set. -/
theorem IsProjectiveRep.characterTransgression_eq_iff_exists_linearization
    [FaithfulSMul kˣ V] (hρ : IsProjectiveRep ρ α) (γ : FactorSet G M) (χ : M →*[G] kˣ) :
    (γ.map χ).cohomologyClass = hρ.cohomologyClass ↔
      ∃ (c : G → kˣ) (π : γ.Extension →* (V ≃ₗ[k] V)), c 1 = 1 ∧
        ∀ x, π x = (ρ x.right).trans (LinearEquiv.smulOfUnit (χ x.left * c x.right)) := by
  refine ⟨hρ.exists_linearization_of_characterTransgression_eq γ χ, ?_⟩
  rintro ⟨c, π, hc1, hπ⟩
  have hker (a : M) : π (FactorSet.inl γ a) = LinearEquiv.smulOfUnit (χ a) := by
    apply LinearEquiv.ext
    intro v
    simpa [hρ.map_one, hc1] using congrArg (fun f : V ≃ₗ[k] V ↦ f v)
      (hπ (FactorSet.inl γ a))
  have hsection : IsProjectiveRep (fun g ↦ π (γ.canonicalSection g))
      (Function.curry ⇑(γ.map χ)) :=
    { isFactorSet := (γ.map χ).isFactorSet_curry trivialMulDistribMulAction_smul
      map_one := by rw [γ.canonicalSection_one, π.map_one]
      mul_apply g h v := by
        have heq := congrArg π (γ.canonicalSection_mul g h)
        simp only [map_mul, hker] at heq
        simpa only [LinearEquiv.mul_apply, LinearEquiv.smulOfUnit_apply,
          Function.curry, FactorSet.map_apply] using DFunLike.congr_fun heq v }
  have hclass := hρ.cohomologyClass_eq_of_eq_smul hsection c (fun g ↦ by
    simpa using hπ (γ.canonicalSection g))
  have hfac : hsection.factorSet = γ.map χ := by
    apply FactorSet.ext
    intro p
    simpa only [Function.curry, Prod.mk.eta] using hsection.factorSet_apply p
  rw [IsProjectiveRep.cohomologyClass_def, hfac] at hclass
  exact hclass

/-- Surjective character transgression makes an extension lift every projective action,
with a scalar action of its kernel. No faithfulness of the projective action is needed. -/
theorem IsProjectiveRep.exists_linearization_of_characterTransgression_surjective
    (hρ : IsProjectiveRep ρ α) (γ : FactorSet G M)
    (hγ : Function.Surjective (γ.characterTransgression (A := kˣ))) :
    ∃ (χ : M →*[G] kˣ) (c : G → kˣ) (π : γ.Extension →* (V ≃ₗ[k] V)), c 1 = 1 ∧
      ∀ x, π x = (ρ x.right).trans (LinearEquiv.smulOfUnit (χ x.left * c x.right)) := by
  obtain ⟨χ, hχ⟩ := hγ hρ.cohomologyClass
  rw [FactorSet.characterTransgression_apply] at hχ
  exact ⟨equivariantCharacterEquiv G M kˣ χ.toMul,
    hρ.exists_linearization_of_characterTransgression_eq γ _ hχ⟩

end

section

variable {k G M : Type} [CommSemiring k] [Group G] [CommGroup M]
  [MulDistribMulAction G M]

/-- An extension has surjective character transgression exactly when it lifts all projective
actions on `G →₀ k`, allowing a scalar kernel character. These actions already realize every
second-cohomology class, so testing this single carrier suffices for universal lifting. -/
theorem FactorSet.characterTransgression_surjective_iff (γ : FactorSet G M) :
    Function.Surjective (γ.characterTransgression (A := kˣ)) ↔
      ∀ (ρ : G → (G →₀ k) ≃ₗ[k] (G →₀ k)) (α : G → G → kˣ), IsProjectiveRep ρ α →
        ∃ (χ : M →*[G] kˣ) (c : G → kˣ) (π : γ.Extension →* ((G →₀ k) ≃ₗ[k] (G →₀ k))),
          c 1 = 1 ∧ ∀ x,
            π x = (ρ x.right).trans (LinearEquiv.smulOfUnit (χ x.left * c x.right)) := by
  refine ⟨fun hγ _ _ hρ ↦ hρ.exists_linearization_of_characterTransgression_surjective γ hγ,
    fun hlift x ↦ ?_⟩
  obtain ⟨α, ρ, hρ, hx⟩ := exists_isProjectiveRep_cohomologyClass_eq x
  obtain ⟨χ, c, π, hc, hπ⟩ := hlift ρ α hρ
  refine ⟨Additive.ofMul ((equivariantCharacterEquiv G M kˣ).symm χ), ?_⟩
  rw [FactorSet.characterTransgression_apply, toMul_ofMul, Equiv.apply_symm_apply]
  exact ((hρ.characterTransgression_eq_iff_exists_linearization γ χ).mpr ⟨c, π, hc, hπ⟩).trans hx

end

end TauCeti
