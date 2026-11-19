/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Translation
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Torus

/-!
# The translation action of a symplectic vector space and the Heisenberg cocycle

A finite-dimensional real symplectic vector space `(V, ω)` acts on itself by translations, as the
Lie group `Multiplicative V` acting by `g • x = toAdd g + x`. Its Lie algebra is `V` itself
(`tangentSpaceCastModel`), and the fundamental vector field of `ξ` is the constant field `ξ`
(`TauCeti.InfinitesimalAction.fundamental_multiplicative`). Every translation preserves the
constant form `ω` (`TauCeti.SymplecticForm.mpullback_smul_multiplicative_constSmooth`), and

`μ(x)(ξ) = ω(ξ, x)`

is a moment map of the action
(`TauCeti.SymplecticForm.isMomentMap_fundamental_translationMomentMap`).

This moment map is not equivariant. Since `V` is commutative, the coadjoint action is trivial,
and the equivariance defect `θ(g) = μ(g • x) - Ad*_g μ(x)` of `μ` is the covector
`θ(g)(ξ) = ω(ξ, toAdd g)`, independent of `x`
(`TauCeti.SymplecticForm.momentDefect_translationMomentMap`). Every other moment map of the
action, a constant shift of `μ` on the connected space `V`, has the same defect
(`TauCeti.SymplecticForm.momentDefect_eq_translationMomentMap_of_isMomentMap`).

Separately, the Lie-algebra cocycle of the action is the **Heisenberg cocycle**
`c(ξ, η) = ω(ξ, η)` (`TauCeti.SymplecticForm.momentCocycle_fundamental_multiplicative`), the
cocycle of the central extension of the abelian Lie algebra `V` by `ℝ` that defines the Heisenberg
Lie algebra. By `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_momentDefect_one`, it is the
derivative at the identity of the defect `θ`.

Since the defect `θ(g)(ξ) = ω(ξ, toAdd g)` is nonzero as soon as `V` is nonzero, the translation
action then has no coadjoint-equivariant moment map
(`TauCeti.SymplecticForm.not_isEquivariantMomentMap_multiplicative`). For the commutative group
`V` this says that no moment map is invariant: the translation action of a nonzero symplectic
vector space carries no Hamiltonian torus data
(`TauCeti.SymplecticForm.not_hamiltonianTorusData_multiplicative`), although it preserves `ω` and
has moment maps. So for a noncompact commutative group the equivariance condition in the
definition of a Hamiltonian action does not follow from the moment equation. The moment map `μ`
is equivariant for the affine action `ν ↦ ν + θ(g)` instead
(`TauCeti.SmoothTwoForm.IsMomentMap.apply_smul_affineCoadjointAction`).

## Main results

* `TauCeti.SymplecticForm.isMomentMap_fundamental_translationMomentMap`: `μ(x)(ξ) = ω(ξ, x)` is a
  moment map of the translation action.
* `TauCeti.SymplecticForm.momentDefect_eq_translationMomentMap_of_isMomentMap`: every moment map
  of the translation action has defect `θ(g)(ξ) = ω(ξ, toAdd g)`.
* `TauCeti.SymplecticForm.momentCocycle_fundamental_multiplicative`: the Heisenberg cocycle.
* `TauCeti.SymplecticForm.not_isEquivariantMomentMap_multiplicative`,
  `TauCeti.SymplecticForm.not_hamiltonianTorusData_multiplicative`: the translation action of a
  nonzero symplectic vector space has no equivariant moment map.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (translations of a symplectic vector space and the Heisenberg group).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §12.3 (the nonequivariance cocycle of the momentum map of phase-space translations).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- **Translations preserve a constant symplectic form.** Each `g : Multiplicative V` acts on `V`
by a translation, which pulls the constant two-form `ω` back to itself. -/
theorem mpullback_smul_multiplicative_constSmooth (g : Multiplicative V) :
    SmoothForm.mpullback (fun x : V ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, V)) g) ω.constSmooth = ω.constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  -- The action of `g` is the translation `x ↦ toAdd g + x`, whose derivative is the identity.
  have h : mvfderiv 𝓘(ℝ, V) (fun x : V ↦ g • x) x =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x : TangentSpace 𝓘(ℝ, V) x →L[ℝ] V) := by
    simp only [← toAdd_vadd, vadd_eq_add]
    rw [mvfderiv_eq_fderiv, fderiv_const_add, fderiv_fun_id, ContinuousLinearMap.id_comp]
  rw [SmoothForm.eval₂_mpullback, eval₂_constSmooth_mfderiv_eq, fromTangentSpace_constSmooth_apply,
    h, ContinuousLinearEquiv.coe_coe]

/-- **The moment map of the translation action.** On a finite-dimensional symplectic vector space
`(V, ω)`, `μ(x)(ξ) = ω(ξ, x)` is a moment map of the action of `Multiplicative V` by
translations. -/
theorem isMomentMap_fundamental_translationMomentMap :
    ω.constSmooth.IsMomentMap
      (InfinitesimalAction.fundamental 𝓘(ℝ, V) (Multiplicative V) 𝓘(ℝ, V) V)
      (ω.translationMomentMap
        (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V)).toLinearMap) := by
  rw [InfinitesimalAction.fundamental_multiplicative]
  exact ω.isMomentMap_translationMomentMap _

/-- **The Heisenberg cocycle.** For the action of `Multiplicative V` by translations on `(V, ω)`,
the cocycle of every map `μ : V → 𝔤*` is `c(ξ, η) = ω(ξ, η)`. -/
theorem momentCocycle_fundamental_multiplicative
    (μ : V → Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, V) (Multiplicative V))) (x : V)
    (ξ η : GroupLieAlgebra 𝓘(ℝ, V) (Multiplicative V)) :
    ω.constSmooth.momentCocycle
        (InfinitesimalAction.fundamental 𝓘(ℝ, V) (Multiplicative V) 𝓘(ℝ, V) V) μ x ξ η =
      (TrivialLieModule.equiv ℝ _ ℝ).symm
        (ω (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V) ξ)
          (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V) η)) := by
  rw [InfinitesimalAction.fundamental_multiplicative, momentCocycle_translation,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- **The equivariance defect of the translation moment map.** For the action of `Multiplicative V`
by translations on `(V, ω)`, the coadjoint action is trivial and the moment map
`μ(x)(ξ) = ω(ξ, x)` is linear in `x`, so its defect `θ(g) = μ(g • x) - Ad*_g μ(x)` is
`μ(toAdd g)`, that is `θ(g)(ξ) = ω(ξ, toAdd g)`, at every point `x`. -/
theorem momentDefect_translationMomentMap (g : Multiplicative V) (x : V) :
    momentDefect
        (ω.translationMomentMap
          (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V)).toLinearMap) g x =
      ω.translationMomentMap
        (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V)).toLinearMap g.toAdd := by
  ext ξ
  simp only [momentDefect_def, Lie.coadjointRepresentation_eq_one, one_apply_eq_self,
    LinearMap.sub_apply, translationMomentMap_apply, ← toAdd_vadd, vadd_eq_add, map_add,
    add_sub_cancel_right]

/-- **Every moment map of the translation action has the Heisenberg defect.** Any moment map `μ`
of the action of `Multiplicative V` by translations on `(V, ω)` has the equivariance defect
`θ(g)(ξ) = ω(ξ, toAdd g)` at every point, because on the connected space `V` it differs from
`x ↦ ω(·, x)` by a constant, which is coadjoint-invariant. -/
theorem momentDefect_eq_translationMomentMap_of_isMomentMap
    {μ : V → Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, V) (Multiplicative V))}
    (h : ω.constSmooth.IsMomentMap
      (InfinitesimalAction.fundamental 𝓘(ℝ, V) (Multiplicative V) 𝓘(ℝ, V) V) μ)
    (g : Multiplicative V) (x : V) :
    momentDefect μ g x =
      ω.translationMomentMap
        (tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V)).toLinearMap g.toAdd := by
  obtain ⟨ν, rfl⟩ :=
    (ω.isMomentMap_fundamental_translationMomentMap.isMomentMap_iff_exists_eq_add).1 h
  rw [momentDefect_add_const, Lie.coadjointRepresentation_eq_one, one_apply_eq_self, sub_self,
    add_zero, momentDefect_translationMomentMap]

/-- **The translation action has no equivariant moment map.** On a nonzero finite-dimensional
symplectic vector space `(V, ω)`, no moment map of the action of `Multiplicative V` by
translations is coadjoint-equivariant, since every moment map has the nonzero defect
`θ(g)(ξ) = ω(ξ, toAdd g)`. -/
theorem not_isEquivariantMomentMap_multiplicative [Nontrivial V]
    (μ : V → Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, V) (Multiplicative V))) :
    ¬ω.constSmooth.IsEquivariantMomentMap μ := by
  intro h
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : V)
  obtain ⟨η, hη⟩ := ω.exists_apply_eq_one hξ
  -- An equivariant moment map has zero defect, but its defect at `η` pairs with `ξ` to
  -- `ω(ξ, η) = 1`.
  have hθ := (momentDefect_eq_zero_iff.2 (h.apply_smul (.ofAdd η) 0)).symm.trans
    (ω.momentDefect_eq_translationMomentMap_of_isMomentMap h.toIsMomentMap (.ofAdd η) 0)
  have hξη := congr($hθ ((tangentSpaceCastModel 𝓘(ℝ, V) (1 : Multiplicative V)).symm ξ))
  rw [LinearMap.zero_apply, translationMomentMap_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    toAdd_ofAdd] at hξη
  exact zero_ne_one (hξη.trans hη)

/-- **The translation action is not a Hamiltonian torus action.** The commutative Lie group
`Multiplicative V` acts on a nonzero finite-dimensional symplectic vector space `(V, ω)` by
translations, preserving `ω` and with moment maps, but none of its moment maps is invariant. -/
theorem not_hamiltonianTorusData_multiplicative [Nontrivial V]
    (μ : V → Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, V) (Multiplicative V))) :
    ¬ω.constSmooth.HamiltonianTorusData μ :=
  fun h ↦ ω.not_isEquivariantMomentMap_multiplicative μ h.toIsEquivariantMomentMap

end TauCeti.SymplecticForm
