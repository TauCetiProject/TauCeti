/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Approximate unitary equivalence with multiplier unitaries

Two star homomorphisms `φ ψ : A → B` into a possibly nonunital C⋆-algebra `B` are
approximately unitarily equivalent with multiplier unitaries when, for every finite set
`F ⊆ A` and every `ε > 0`, some unitary `u` of the multiplier algebra `𝓜(ℂ, B)` satisfies
`‖u φ(a) u⋆ - ψ(a)‖ < ε` on `F`. A nonunital `B` may have no unitaries of its own, so this
is the form of the relation used for nonunital and stable targets.

The relation is defined as the target-unitary relation `TauCeti.ApproximatelyUnitarilyEquivalent`
for the composites of `φ` and `ψ` with the inclusion `B → 𝓜(ℂ, B)`. Since `B` is an ideal of
`𝓜(ℂ, B)` and the inclusion is isometric, the conjugates stay in `B`
(`DoubleCentralizer.conjStarAlgAut`), and the relation can be read inside `B`
(`multiplierApproximatelyUnitarilyEquivalent_iff`).

## Main results

* `MultiplierApproximatelyUnitarilyEquivalent.equivalence`: the relation is an equivalence
  relation.
* `MultiplierApproximatelyUnitarilyEquivalent.precomp` and
  `MultiplierApproximatelyUnitarilyEquivalent.postcomp`: it is preserved by precomposition with
  any map and by postcomposition with a nondegenerate one, which extends to the multiplier
  algebras.
* `MultiplierApproximatelyUnitarilyEquivalent.iff_exists_unitary_seq`: for a separable source it
  is implemented by a single sequence of unitary multipliers.
* `multiplierApproximatelyUnitarilyEquivalent_iff_approximatelyUnitarilyEquivalent`: for a unital
  target it coincides with the relation implemented by unitaries of the target.
* `MultiplierApproximatelyUnitarilyEquivalent.of_unitization`: the relation implemented by
  unitaries of the minimal unitization `Unitization ℂ B` implies it.

## References

* M. Rørdam, *Classification of nuclear, simple C*-algebras*, in: Classification of Nuclear
  C*-Algebras. Entropy in Operator Algebras, Encyclopaedia Math. Sci. 126, Springer, 2002,
  Definition 1.1.15 and §2.3.
-/

public section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Approximate unitary equivalence implemented by unitaries of the multiplier algebra: on every
finite set of `A`, conjugation of `φ` by a unitary of `𝓜(ℂ, B)` approximates `ψ`. It is the
target-unitary relation for the composites with the inclusion `B → 𝓜(ℂ, B)`. -/
def MultiplierApproximatelyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ApproximatelyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
    ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ)

/-- The multiplier-unitary relation is the target-unitary relation inside `𝓜(ℂ, B)`. -/
theorem multiplierApproximatelyUnitarilyEquivalent_iff_coeHom (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ ↔
      ApproximatelyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) :=
  Iff.rfl

/-- Finite-set characterization of the multiplier-unitary relation, with the conjugates computed
in `B`. -/
theorem multiplierApproximatelyUnitarilyEquivalent_iff (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ ↔
      ∀ (F : Finset A) (ε : ℝ), 0 < ε →
        ∃ u : unitary 𝓜(ℂ, B), ∀ a ∈ F,
          ‖DoubleCentralizer.conjStarAlgAut u (φ a) - ψ a‖ < ε := by
  simp only [multiplierApproximatelyUnitarilyEquivalent_iff_coeHom,
    approximatelyUnitarilyEquivalent_def, NonUnitalStarAlgHom.comp_apply,
    DoubleCentralizer.coeHom_apply, DoubleCentralizer.norm_mul_coe_mul_star_sub_coe]

namespace MultiplierApproximatelyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Conjugacy by a fixed unitary multiplier gives the multiplier-unitary relation. -/
theorem of_unitary (u : unitary 𝓜(ℂ, B))
    (h : ∀ a, DoubleCentralizer.conjStarAlgAut u (φ a) = ψ a) :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ :=
  (multiplierApproximatelyUnitarilyEquivalent_iff φ ψ).2 fun _ _ hε ↦
    ⟨u, fun a _ ↦ by simpa [h a] using hε⟩

/-- The multiplier-unitary relation is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : MultiplierApproximatelyUnitarilyEquivalent φ φ :=
  ApproximatelyUnitarilyEquivalent.refl _

/-- The multiplier-unitary relation is symmetric. -/
@[symm]
theorem symm (h : MultiplierApproximatelyUnitarilyEquivalent φ ψ) :
    MultiplierApproximatelyUnitarilyEquivalent ψ φ :=
  ApproximatelyUnitarilyEquivalent.symm h

/-- The multiplier-unitary relation is transitive. -/
@[trans]
theorem trans (h₁ : MultiplierApproximatelyUnitarilyEquivalent φ ψ)
    (h₂ : MultiplierApproximatelyUnitarilyEquivalent ψ χ) :
    MultiplierApproximatelyUnitarilyEquivalent φ χ :=
  ApproximatelyUnitarilyEquivalent.trans h₁ h₂

/-- The multiplier-unitary relation is an equivalence relation. -/
theorem equivalence :
    Equivalence (MultiplierApproximatelyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Precomposition with any star homomorphism preserves the multiplier-unitary relation. -/
theorem precomp (h : MultiplierApproximatelyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    MultiplierApproximatelyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  rw [multiplierApproximatelyUnitarilyEquivalent_iff_coeHom, ← NonUnitalStarAlgHom.comp_assoc,
    ← NonUnitalStarAlgHom.comp_assoc]
  exact ApproximatelyUnitarilyEquivalent.precomp h ρ

/-- Postcomposition with a nondegenerate star homomorphism `ρ : B → C` preserves the
multiplier-unitary relation: the unital extension of `ρ` to the multiplier algebras carries
implementing unitaries to implementing unitaries. -/
theorem postcomp (h : MultiplierApproximatelyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C)
    (hρ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).IsMultiplierNondegenerate) :
    MultiplierApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hcomp : (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).extendToMultiplier
      hρ).toNonUnitalStarAlgHom.comp (DoubleCentralizer.coeHom (𝕜 := ℂ)) =
      (DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ := by
    refine NonUnitalStarAlgHom.ext fun b ↦ ?_
    simp
  simpa only [multiplierApproximatelyUnitarilyEquivalent_iff_coeHom,
    NonUnitalStarAlgHom.comp_assoc] using
    ApproximatelyUnitarilyEquivalent.postcomp_of_comp_eq h _ hcomp

/-- Maps related by the multiplier-unitary relation have the same pointwise norm. -/
theorem norm_eq (h : MultiplierApproximatelyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ := by
  simpa only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
    DoubleCentralizer.norm_coe] using ApproximatelyUnitarilyEquivalent.norm_eq h a

/-- The multiplier-unitary relation preserves injectivity. -/
theorem injective_iff (h : MultiplierApproximatelyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ := by
  have hi : Function.Injective (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B)) :=
    DoubleCentralizer.coe_injective
  simpa only [NonUnitalStarAlgHom.coe_comp, hi.of_comp_iff] using
    ApproximatelyUnitarilyEquivalent.injective_iff h

/-- A net of unitary multipliers whose conjugates of `φ` converge pointwise to `ψ` gives the
multiplier-unitary relation. The filter must be nontrivial; no separability is needed. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] (u : ι → unitary 𝓜(ℂ, B))
    (h : ∀ a, Tendsto (fun i ↦ DoubleCentralizer.conjStarAlgAut (u i) (φ a)) l (𝓝 (ψ a))) :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ :=
  ApproximatelyUnitarilyEquivalent.of_tendsto u fun a ↦ by
    simpa only [NonUnitalStarAlgHom.comp_apply, DoubleCentralizer.coeHom_apply,
      ← DoubleCentralizer.coe_conjStarAlgAut_apply, DoubleCentralizer.tendsto_coe_iff] using h a

/-- For a separable source, the multiplier-unitary relation is equivalent to pointwise
convergence of conjugates along a sequence of unitary multipliers. -/
theorem iff_exists_unitary_seq [TopologicalSpace.SeparableSpace A] :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ ↔
      ∃ u : ℕ → unitary 𝓜(ℂ, B), ∀ a,
        Tendsto (fun n ↦ DoubleCentralizer.conjStarAlgAut (u n) (φ a)) atTop (𝓝 (ψ a)) := by
  simp only [multiplierApproximatelyUnitarilyEquivalent_iff_coeHom,
    ApproximatelyUnitarilyEquivalent.iff_exists_unitary_seq, NonUnitalStarAlgHom.comp_apply,
    DoubleCentralizer.coeHom_apply, ← DoubleCentralizer.coe_conjStarAlgAut_apply,
    DoubleCentralizer.tendsto_coe_iff]

/-- The relation implemented by unitaries of the minimal unitization `Unitization ℂ B`, that is
the target-unitary relation for the composites with `B → Unitization ℂ B`, implies the
multiplier-unitary relation. -/
theorem of_unitization
    (h : ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
      ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ)) :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ := by
  have hcomp : (Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B))
      ).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ B) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) := by
    rw [← Unitization.starLift_symm_apply]
    exact Unitization.starLift.symm_apply_apply _
  exact ApproximatelyUnitarilyEquivalent.postcomp_of_comp_eq h _ hcomp

end MultiplierApproximatelyUnitarilyEquivalent

/-- For a unital target, implementing unitaries may be taken in `B` or in `𝓜(ℂ, B)`: the
multiplier-unitary relation coincides with the target-unitary relation, since `B` is isomorphic
to its multiplier algebra. -/
theorem multiplierApproximatelyUnitarilyEquivalent_iff_approximatelyUnitarilyEquivalent
    {B : Type*} [CStarAlgebra B] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ ↔ ApproximatelyUnitarilyEquivalent φ ψ := by
  rw [multiplierApproximatelyUnitarilyEquivalent_iff_coeHom]
  constructor
  · intro h
    simpa only [NonUnitalStarAlgHom.id_comp] using
      ApproximatelyUnitarilyEquivalent.postcomp_of_comp_eq (κ := NonUnitalStarAlgHom.id ℂ B) h
        (DoubleCentralizer.coeStarAlgEquiv ℂ B).symm.toStarAlgHom (by simp)
  · intro h
    simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_toStarAlgHom,
      DoubleCentralizer.coeStarAlgEquiv_toNonUnitalStarAlgHom] using
      ApproximatelyUnitarilyEquivalent.postcomp h
        (DoubleCentralizer.coeStarAlgEquiv ℂ B).toStarAlgHom

end TauCeti
