/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.InhomogeneousF2

/-!
# The degree-one class of a continuous homomorphism to `𝔽₂`

With trivial `𝔽₂` coefficients, continuous first cohomology is the group of continuous
homomorphisms to `𝔽₂`: a continuous `1`-cocycle for the trivial action is a homomorphism, and
there are no nonzero coboundaries. This file names the class `homClass H α` of a continuous
homomorphism `α : H → 𝔽₂` in Mathlib's `continuousCohomology 1 (trivialF2 H)`, identifies it with
the `TopRep.cochainClass` of the homogeneous cochain of `α`, and shows that `homClass` is a
bijection from continuous homomorphisms onto degree-one classes that turns multiplication of
homomorphisms into addition of classes.

## Main definitions

* `TauCeti.ContCohomology.evensHomCocycle`: a continuous homomorphism `G → 𝔽₂` as a continuous
  `1`-cocycle of `G` with the lifted trivial `𝔽₂` coefficients.
* `TauCeti.ContCohomology.homClass`: the class of a continuous homomorphism to `𝔽₂`.

## Main results

* `TauCeti.ContCohomology.homClass_eq_cochainClass`: `homClass` is the class of the homogeneous
  cochain `inhomogeneousCochain1` of the homomorphism.
* `TauCeti.ContCohomology.trivialF2Map_homClass`: pullback of the class of a homomorphism along a
  continuous homomorphism is the class of the composite.
* `TauCeti.ContCohomology.trivialF2ResMap_homClass`: restriction of the class of a homomorphism to
  a subgroup is the class of its restriction.
* `TauCeti.ContCohomology.homClass_one`, `TauCeti.ContCohomology.homClass_mul`: `homClass` sends
  the trivial homomorphism to `0` and products to sums.
* `TauCeti.ContCohomology.homClass_surjective`: every degree-one class is the class of a continuous
  homomorphism.
* `TauCeti.ContCohomology.homClass_inj`: two continuous homomorphisms have the same class exactly
  when they are equal.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §2.2.

## Source note

The definition of `homClass` in the explicit model and its injectivity follow the earlier Tau Ceti
formalization in [TauCeti PR #11157](https://github.com/TauCetiProject/TauCeti/pull/11157) by
@mccorvie-agent ("feat: descend the index-two Evens norm").
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section HomCocycle

variable {G : Type u} [Group G] [TopologicalSpace G]

attribute [local instance] TopRep.distribMulAction

/-- A continuous homomorphism `y : G →* Multiplicative (ZMod 2)`, as a continuous `1`-cocycle of
`G` with coefficients in the lifted trivial `𝔽₂` object `trivialF2 G`. Its restriction to a
subgroup `U` is `evensHomCocycleAmbient U (y.comp U.subtype)`. -/
noncomputable def evensHomCocycle (y : G →* Multiplicative (ZMod 2)) (hy : Continuous y) :
    Z1 G (trivialF2 G).V :=
  (Z1EquivOfSmulEqSelf (fun g x => by
    rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply])).symm
    (Additive.ofMul
      ⟨(trivialF2Equiv G).symm.toAddMonoidHom.toMultiplicative.comp y,
        (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
          (continuous_toAdd.comp hy)⟩)

/-- The underlying cochain of `evensHomCocycle`. -/
@[simp]
theorem coe_evensHomCocycle (y : G →* Multiplicative (ZMod 2)) (hy : Continuous y) :
    (evensHomCocycle y hy : G → (trivialF2 G).V) =
      fun g => (trivialF2Equiv G).symm (Multiplicative.toAdd (y g)) := by
  funext g
  simp [evensHomCocycle]

end HomCocycle

section HomClass

variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

attribute [local instance] TopRep.distribMulAction

/-- `H` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance continuousSMul_trivialF2_homClass : ContinuousSMul H (trivialF2 H).V :=
  (isSmoothDiscrete_trivialF2 H).continuousSMul

/-- The class of a continuous homomorphism `α : H → 𝔽₂` in `continuousCohomology 1 (trivialF2 H)`:
the explicit class of `α`, read as a continuous `1`-cocycle for the trivial action, carried to the
canonical object by the degree-one comparison. `homClass_eq_cochainClass` identifies it with the
class of the homogeneous cochain of `α`. -/
noncomputable def homClass (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    continuousCohomology 1 (trivialF2 H) :=
  (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
    (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V (evensHomCocycle α hα))

/-- `homClass` is the degree-one comparison applied to the explicit class of the homomorphism. -/
theorem homClass_def (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass H α hα =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
        (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V (evensHomCocycle α hα)) :=
  (rfl)

/-- **The class of a continuous homomorphism is the class of its cochain:** `homClass H α` is the
`TopRep.cochainClass` of the homogeneous cochain `(h₀, h₁) ↦ α (h₀⁻¹ * h₁)`, read additively. -/
theorem homClass_eq_cochainClass (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass H α hα =
      (trivialF2 H).cochainClass 1
        (inhomogeneousCochain1 (fun h => Multiplicative.toAdd (α h)) (continuous_toAdd.comp hα))
        (inhomogeneousCochain1_d_eq_zero _ _ fun g h => by simp [map_mul, toAdd_mul]) :=
  eqToHom_explicitH1AddEquivContinuousCohomology_eq_cochainClass _ _ _
    (fun h => by rw [coe_evensHomCocycle]) _

/-- The trivial homomorphism has the zero class. -/
@[simp]
theorem homClass_one :
    homClass H (1 : H →* Multiplicative (ZMod 2)) continuous_const = 0 := by
  have h0 : evensHomCocycle (1 : H →* Multiplicative (ZMod 2)) continuous_const = 0 := by
    ext h
    simp only [coe_evensHomCocycle, MonoidHom.one_apply, toAdd_one, map_zero,
      ZeroMemClass.coe_zero, Pi.zero_apply]
  rw [homClass_def, h0, QuotientAddGroup.mk_zero, map_zero, map_zero]

/-- **`homClass` turns products into sums:** the class of `α * β` is the sum of the classes. -/
@[simp]
theorem homClass_mul (α β : H →* Multiplicative (ZMod 2)) (hα : Continuous α)
    (hβ : Continuous β) :
    homClass H (α * β) (hα.mul hβ) = homClass H α hα + homClass H β hβ := by
  have hadd : evensHomCocycle (α * β) (hα.mul hβ) =
      evensHomCocycle α hα + evensHomCocycle β hβ := by
    ext h
    simp only [coe_evensHomCocycle, MonoidHom.mul_apply, toAdd_mul, map_add,
      AddMemClass.coe_add, Pi.add_apply]
  rw [homClass_def, homClass_def, homClass_def, hadd, QuotientAddGroup.mk_add, map_add, map_add]

/-- **Every degree-one class is the class of a continuous homomorphism.** With trivial `𝔽₂`
coefficients the continuous `1`-cocycles are the continuous homomorphisms and there are no nonzero
coboundaries, so `H¹(H, 𝔽₂)` is the group of continuous homomorphisms `H → 𝔽₂`. -/
theorem homClass_surjective (x : continuousCohomology 1 (trivialF2 H)) :
    ∃ (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α), homClass H α hα = x := by
  have htriv (g : H) (m : (trivialF2 H).V) : g • m = m := by
    rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]
  let φ := Additive.toMul (H1EquivOfSmulEqSelf htriv
    ((explicitH1AddEquivContinuousCohomology H (trivialF2 H).V).symm
      ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H).symm)).hom x)))
  let α : H →* Multiplicative (ZMod 2) :=
    (trivialF2Equiv H).toMultiplicative.toMonoidHom.comp φ.toMonoidHom
  have hα : Continuous α :=
    (continuous_of_discreteTopology : Continuous (trivialF2Equiv H).toMultiplicative).comp
      φ.continuous
  refine ⟨α, hα, ?_⟩
  have hφ : (evensHomCocycle α hα : H1 H (trivialF2 H).V) =
      (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V).symm
        ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H).symm)).hom
          x) := by
    apply (H1EquivOfSmulEqSelf htriv).injective
    rw [H1EquivOfSmulEqSelf_mk]
    apply Additive.toMul.injective
    ext h
    simp [α, φ, Z1EquivOfSmulEqSelf_apply]
  rw [homClass_def, hφ, AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply, eqToHom_trans,
    eqToHom_refl, ConcreteCategory.id_apply]

/-- **Two continuous homomorphisms have the same class exactly when they are equal.** With
trivial `𝔽₂` coefficients there are no nonzero degree-one coboundaries. -/
@[simp]
theorem homClass_inj {α β : H →* Multiplicative (ZMod 2)} (hα : Continuous α)
    (hβ : Continuous β) : homClass H α hα = homClass H β hβ ↔ α = β := by
  refine ⟨fun hcl => ?_, fun h => by subst h; rfl⟩
  have htriv (g : H) (m : (trivialF2 H).V) : g • m = m := by
    rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]
  rw [homClass_def, homClass_def] at hcl
  have hexpl := (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V).injective
    ((ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H)))).injective hcl)
  have hchar := congrArg (fun z => Additive.toMul (H1EquivOfSmulEqSelf htriv z)) hexpl
  ext h
  simpa only [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply, coe_evensHomCocycle,
    EmbeddingLike.apply_eq_iff_eq] using DFunLike.congr_fun hchar h

end HomClass

section Naturality

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

attribute [local instance] TopRep.distribMulAction

/-- A group acts continuously on its trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance continuousSMul_trivialF2_homClass_naturality (K : Type u) [Group K]
    [TopologicalSpace K] [IsTopologicalGroup K] : ContinuousSMul K (trivialF2 K).V :=
  (isSmoothDiscrete_trivialF2 K).continuousSMul

/-- **Naturality of the class of a homomorphism.** For a continuous homomorphism `φ : H → G`,
pulling the class of a continuous `α : G → 𝔽₂` back along `φ` gives the class of `α ∘ φ`. -/
theorem trivialF2Map_homClass (φ : H →ₜ* G) (α : G →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    trivialF2Map φ 1 (homClass G α hα) =
      homClass H (α.comp (φ : H →* G)) (hα.comp φ.continuous) := by
  rw [homClass_eq_cochainClass, homClass_eq_cochainClass]
  exact trivialF2Map_cochainClass_inhomogeneousCochain1 φ _ _ _ _

/-- **Restriction of the class of a homomorphism.** For a subgroup `S` of `G`, restricting the
class of a continuous `α : G → 𝔽₂` to `S` gives the class of `α|_S`. -/
theorem trivialF2ResMap_homClass (S : Subgroup G) (α : G →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    trivialF2ResMap G S 1 (homClass G α hα) =
      homClass S (α.comp S.subtype) (hα.comp continuous_subtype_val) := by
  rw [← trivialF2Map_subgroupSubtype, trivialF2Map_homClass, homClass_inj,
    ContinuousMonoidHom.coe_subgroupSubtype]

end Naturality

end TauCeti.ContCohomology
