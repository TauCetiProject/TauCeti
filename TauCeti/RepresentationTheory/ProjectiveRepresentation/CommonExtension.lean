/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Extension
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Finite

/-!
# A common finite extension lifting projective representations

For a finite group `G` over an algebraically closed field `k`, a single finite central
extension lifts every projective representation of `G`, up to a normalized scalar rescaling.
The extension depends only on `k` and `G`, not on the representation or its dimension.

Take the product of the groups of `|G|`-th roots of unity indexed by all normalized factor
sets with values in those roots. Evaluation is a factor set valued in this finite product.
Each projective representation can be rescaled to one of the indexing factor sets, so
evaluation at that coordinate supplies its linearization.

This construction gives a common finite lifting extension. Its kernel can be larger than
the Schur multiplier; no minimality or containment in the commutator subgroup is asserted.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

section

variable (k G : Type*) [CommMonoid k] [Group G]

/-- The evaluation factor set with one root-of-unity coordinate for each normalized
root-of-unity factor set of `G`. Its extension simultaneously linearizes projective
representations when `G` is finite and `k` is algebraically closed. -/
noncomputable def projectiveLiftingFactorSet :
    FactorSet G (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) where
  toFun p α := α p
  isMulCocycle₂' g h j := by
    funext α
    exact α.isMulCocycle₂ g h j
  map_one_one' := by
    funext α
    exact α.map_one_one

@[simp]
theorem projectiveLiftingFactorSet_apply (p : G × G)
    (α : FactorSet G (rootsOfUnity (Nat.card G) k)) :
    projectiveLiftingFactorSet k G p α = α p := (rfl)

/-- Evaluation at a root-valued factor set is a character of the common lifting kernel. -/
noncomputable def projectiveLiftingCharacter
    (α : FactorSet G (rootsOfUnity (Nat.card G) k)) :
    (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) →*[G] kˣ :=
  { (rootsOfUnity (Nat.card G) k).subtype.comp
      (Pi.evalMonoidHom (fun _ : FactorSet G (rootsOfUnity (Nat.card G) k) ↦
        rootsOfUnity (Nat.card G) k) α) with
    map_smul' _ _ := by simp only [Pi.smul_def, trivialMulDistribMulAction_smul] }

@[simp]
theorem projectiveLiftingCharacter_apply (α : FactorSet G (rootsOfUnity (Nat.card G) k))
    (a : FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) :
    projectiveLiftingCharacter k G α a = (a α : kˣ) :=
  (rfl)

/-- The kernel of the projection of the common lifting extension is central. -/
theorem projectiveLiftingFactorSet_ker_le_center :
    (FactorSet.rightHom (projectiveLiftingFactorSet k G)).ker ≤
      Subgroup.center (projectiveLiftingFactorSet k G).Extension := by
  rw [← FactorSet.range_inl_eq_ker_rightHom]
  exact FactorSet.inl_range_le_center _ trivialMulDistribMulAction_smul

end

section

variable {k G : Type*} [Field k] [Group G] [Finite G]
  {V : Type*} [AddCommMonoid V] [Module k V]

/-- Every projective representation of a finite group over an algebraically closed field
lifts to the same finite central extension. On every element of the extension, the lift
agrees up to a scalar with the original representation at its image in `G`. In particular,
the kernel acts by scalars. -/
theorem IsProjectiveRep.exists_commonExtension_linearization [IsAlgClosed k]
    {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ} (hρ : IsProjectiveRep ρ α) :
    ∃ (π : (projectiveLiftingFactorSet k G).Extension →* (V ≃ₗ[k] V))
      (c : (projectiveLiftingFactorSet k G).Extension → kˣ), c 1 = 1 ∧ ∀ x,
        π x = (ρ (FactorSet.rightHom (projectiveLiftingFactorSet k G) x)).trans
          (LinearEquiv.smulOfUnit (c x)) := by
  let := hρ.isFactorSet
  obtain ⟨c, hc, hpow⟩ := IsFactorSet.exists_rescale_pow_card_eq_one α
  let β (g h : G) := c g * c h * (c (g * h))⁻¹ * α g h
  have hβ := hρ.rescale c hc
  let b := hβ.isFactorSet.toRootsOfUnityFactorSet hpow
  let ev := projectiveLiftingCharacter k G b
  have hβ' : IsProjectiveRep (fun g ↦ (ρ g).trans (LinearEquiv.smulOfUnit (c g)))
      (Function.curry ⇑((projectiveLiftingFactorSet k G).map ev)) := by
    have heq : Function.curry ⇑((projectiveLiftingFactorSet k G).map ev) = β := by
      funext g h
      simp only [Function.curry, FactorSet.map_apply, ev, projectiveLiftingCharacter_apply,
        projectiveLiftingFactorSet_apply, b, IsFactorSet.coe_toRootsOfUnityFactorSet_apply, β]
    rw [heq]
    exact hβ
  refine ⟨(hβ'.linearization trivialMulDistribMulAction_smul).comp
    ((projectiveLiftingFactorSet k G).mapExtension ev),
      fun x ↦ ev x.left * c x.right, by simp [hc], fun x ↦ ?_⟩
  apply LinearEquiv.ext
  intro v
  simp [LinearEquiv.smulOfUnit_apply, smul_smul]

end

end TauCeti
