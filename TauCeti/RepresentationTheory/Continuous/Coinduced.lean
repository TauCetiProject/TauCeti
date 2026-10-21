/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Maps into coinduced representations, and coset sums of coinduced invariants

For a continuous representation `π` of `G` on `V`, Mathlib's coinduced representation
`π.coind₁` acts on `C(G, V)` by `(g • f) x = π g (f (g⁻¹ * x))`, so an invariant `f` satisfies
`π g (f x) = f (g * x)`. Evaluation at a point does not carry invariants of `π.coind₁` to
invariants of `π`, but a sum of evaluations over a transversal of a finite-index subgroup `U` does,
as soon as `f` is invariant under right translation by `U`: left multiplication by `g` permutes the
cosets of `U`, and right translation by `U` absorbs the change of representatives.

An intertwining map `f` into `σ.coind₁` is determined by its values at `1`, since equivariance
gives `f v x = σ x (f (π x⁻¹ v) 1)`. Conversely a linear map `φ : V → W`, not assumed equivariant,
spreads to the intertwining map `v ↦ (x ↦ σ x (φ (π x⁻¹ v)))` into `σ.coind₁` whose value at `1`
is `φ`, as soon as this formula is jointly continuous in `v` and `x`. This is Frobenius reciprocity
for `coind₁`, which up to the twist of the action is coinduction from the trivial subgroup; the
continuity hypothesis is why it is stated as a lift rather than as an adjunction on all of `TopRep`.
For locally constant coinduction from a subgroup of a compact group, on smooth discrete
representations, the adjunction itself is `TauCeti.smoothDiscreteResCoindAdjunction`.

## Main definitions

* `ContRepresentation.coind₁Lift`: the intertwining map into `σ.coind₁` spread from a linear map.

## Main results

* `ContRepresentation.coind₁Lift_apply_one`: the lift of `φ` evaluates at `1` to `φ`.
* `ContIntertwiningMap.coind₁_ext`: intertwining maps into `σ.coind₁` agreeing at `1` are equal.
* `ContRepresentation.sum_apply_out_mem_invariants`: summing an invariant element of the coinduced
  representation `C(G, V)` over a transversal of a finite-index subgroup stabilizing it under right
  translation gives an invariant element of `V`.
-/

public section

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [TopologicalSpace R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul R V]

/-- **Coset sums of coinduced invariants are invariant.** Let `f : C(G, V)` be invariant for the
coinduced representation `π.coind₁` and invariant under right translation by a finite-index
subgroup `U`. Then the sum of `f` over the transversal of `U` given by `Quotient.out` is invariant
for `π`. -/
theorem sum_apply_out_mem_invariants {π : ContRepresentation R G V} {f : C(G, V)}
    (hf : f ∈ π.coind₁.invariants) {U : Subgroup G} [Fintype (G ⧸ U)]
    (hU : U ≤ TauCeti.rightTranslationStabilizer f) :
    ∑ q : G ⧸ U, f q.out ∈ π.invariants := by
  intro g
  rw [map_sum]
  refine Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => ?_
  -- invariance of `f` for `π.coind₁` moves `π g` inside: `π g (f y) = f (g * y)`
  have hπ : π g (f q.out) = f (g * q.out) := by
    simpa only [ContRepresentation.coind₁_apply_apply, inv_mul_cancel_left]
      using DFunLike.congr_fun (hf g) (g * q.out)
  -- `(g • q).out` and `g * q.out` differ by an element of `U` on the right
  obtain ⟨u, hu⟩ : ∃ u : U, g * q.out * u = (g • q).out :=
    ⟨⟨(g * q.out)⁻¹ * (g • q).out, QuotientGroup.eq.mp (QuotientGroup.mk_out_smul g q).symm⟩,
      by simp [mul_assoc]⟩
  rw [hπ, ← hu]
  exact ((TauCeti.mem_rightTranslationStabilizer.mp (hU u.2)) (g * q.out)).symm

end ContRepresentation

section Lift

variable {R G V W : Type*} [Ring R] [TopologicalSpace R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [AddCommGroup W] [Module R W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul R W]
  {π : ContRepresentation R G V} {σ : ContRepresentation R G W}

namespace ContRepresentation

/-- **Frobenius reciprocity for `coind₁`, the lift.** A linear map `φ : V → W`, not assumed to be
equivariant, spreads to the intertwining map `v ↦ (x ↦ σ x (φ (π x⁻¹ v)))` from `π` into the
coinduced representation `σ.coind₁`. The hypothesis is that this formula is jointly continuous in
`v` and `x`. The lift evaluates at `1` to `φ` (`ContRepresentation.coind₁Lift_apply_one`), and an
intertwining map into `σ.coind₁` is determined by its values at `1`
(`ContIntertwiningMap.coind₁_ext`). -/
def coind₁Lift (φ : V →ₗ[R] W) (hφ : Continuous fun p : V × G ↦ σ p.2 (φ (π p.2⁻¹ p.1))) :
    π →ⁱL σ.coind₁ where
  toFun := (ContinuousMap.mk _ hφ).curry
  map_add' v w := by ext x; simp
  map_smul' r v := by ext x; simp
  cont := (ContinuousMap.mk _ hφ).curry.continuous
  isIntertwining' g := by
    ext v x
    simp [← mul_apply_eq_comp, ← map_mul]

/-- The lift of `φ` to the coinduced representation, at a point. -/
@[simp]
theorem coind₁Lift_apply_apply (φ : V →ₗ[R] W)
    (hφ : Continuous fun p : V × G ↦ σ p.2 (φ (π p.2⁻¹ p.1))) (v : V) (x : G) :
    coind₁Lift φ hφ v x = σ x (φ (π x⁻¹ v)) :=
  (rfl)

/-- The lift of `φ` to the coinduced representation evaluates at `1` to `φ`. -/
theorem coind₁Lift_apply_one (φ : V →ₗ[R] W)
    (hφ : Continuous fun p : V × G ↦ σ p.2 (φ (π p.2⁻¹ p.1))) (v : V) :
    coind₁Lift φ hφ v 1 = φ v := by
  simp

end ContRepresentation

namespace ContIntertwiningMap

open ContRepresentation

/-- An intertwining map into a coinduced representation is recovered from its values at `1`:
`f v x = σ x (f (π x⁻¹ v) 1)`. -/
theorem coind₁_apply_apply (f : π →ⁱL σ.coind₁) (v : V) (x : G) :
    f v x = σ x (f (π x⁻¹ v) 1) := by
  rw [f.isIntertwining, ContRepresentation.coind₁_apply_apply, inv_inv, mul_one,
    ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

/-- **Frobenius reciprocity for `coind₁`, uniqueness.** Two intertwining maps into a coinduced
representation that agree after evaluation at `1` are equal. -/
theorem coind₁_ext {f g : π →ⁱL σ.coind₁} (h : ∀ v, f v 1 = g v 1) : f = g := by
  ext v x
  rw [toContinuousLinearMap_apply, toContinuousLinearMap_apply, coind₁_apply_apply,
    coind₁_apply_apply g, h]

end ContIntertwiningMap

end Lift
