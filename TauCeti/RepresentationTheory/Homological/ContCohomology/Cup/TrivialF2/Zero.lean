/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.GradedAlgebra

/-!
# Degree zero with trivial mod-two coefficients

The invariant-vector interpretation of degree zero identifies `cohomF2 G 0` with `ZMod 2`.
Unlike `cohomFp`, the coefficient representation here is over `ℤ`; its canonical mod-two scalar
structure is recovered from its additive group. The equivalence sends the cup-product unit to `1`.
-/

public section

namespace TauCeti

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Zeroth continuous cohomology with the integral trivial mod-two coefficient representation
is canonically `ZMod 2`. -/
noncomputable def cohomF2ZeroLinearEquiv : cohomF2 G 0 ≃ₗ[ZMod 2] ZMod 2 :=
  -- Keep the representation’s integral scalar action when forming its invariant subgroup.
  letI : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
  let e₀ : cohomF2 G 0 ≃+ (trivialF2 G).ρ.invariants :=
    { (_root_.ContinuousCohomology.zeroIso (trivialF2 G)).toContinuousLinearEquiv.toEquiv with
      map_add' := map_add (_root_.ContinuousCohomology.zeroIso (trivialF2 G)).hom.hom }
  let hTop : (trivialF2 G).ρ.invariants.toAddSubgroup = ⊤ :=
    (AddSubgroup.eq_top_iff' _).2 fun x g ↦ trivialF2_ρ_apply_apply G g x
  let e₁ : (trivialF2 G).ρ.invariants ≃+ (trivialF2 G).V :=
    (AddEquiv.addSubgroupCongr hTop).trans AddSubgroup.topEquiv
  let e := e₀.trans (e₁.trans (trivialF2Equiv G))
  { e with map_smul' := ZMod.map_smul e }

/-- The identification reads the value of the invariant representing the degree-zero class. -/
theorem cohomF2ZeroLinearEquiv_apply (x : cohomF2 G 0) :
    cohomF2ZeroLinearEquiv G x = trivialF2Equiv G
      ((_root_.ContinuousCohomology.zeroIso (trivialF2 G)).hom x).1 :=
  (rfl)

/-- The cup-product unit has coefficient value one. -/
@[simp]
theorem cohomF2ZeroLinearEquiv_one : cohomF2ZeroLinearEquiv G 1 = 1 := by
  rw [cohomF2ZeroLinearEquiv_apply, ← cohomF2.one_eq_one, cohomF2.one_def]
  simp

/-- Restriction on degree-zero mod-two cohomology is surjective: every invariant coefficient
on the subgroup is already invariant on the whole group. -/
theorem trivialF2ResMap_zero_surjective (S : Subgroup G) :
    Function.Surjective (trivialF2ResMap G S 0) := by
  intro y
  refine ⟨cohomF2ZeroLinearEquiv S y • (1 : cohomF2 G 0), ?_⟩
  apply (cohomF2ZeroLinearEquiv S).injective
  rw [← trivialF2Map_subgroupSubtype, ZMod.map_smul, trivialF2Map_one]
  simp

end TauCeti
