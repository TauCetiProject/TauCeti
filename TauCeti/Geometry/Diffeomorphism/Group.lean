/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The group of self-diffeomorphisms

Mathlib's `Diffeomorph I I' M M' n` is the type of `Cⁿ` diffeomorphisms between two manifolds,
with composition (`Diffeomorph.trans`), inverse (`Diffeomorph.symm`), and the identity
(`Diffeomorph.refl`) already in place. When the source and target coincide these assemble into a
group: this file equips the self-diffeomorphisms `M ≃ₘ^n⟮I, I⟯ M` with `One`, `Mul`, and `Inv`
instances and proves the `Group` axioms, exactly as Mathlib does for `Equiv.Perm`
(`Mathlib/Algebra/Group/End.lean`). The multiplication is `f * g = g.trans f`, so that `f * g`
acts as the function composition `f ∘ g`, matching the `Equiv.Perm` convention.

This is the group object the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology") asks for as its first deliverable: "The **group** `Diff(M) := M ≃ₘ^∞⟮I, I⟯ M` under
composition (the `Group` instance is routine from the existing `Diffeomorph` composition and
inverse)." It is the underlying group of the topological group `Diff(M)` whose homotopy type the
Smale conjecture `[Kir97, Problem 4.34]` is about; the C^∞ topology making it a topological group is
a separate, later layer-3 deliverable, so this file stops at the bare group structure. The
construction works for every smoothness exponent `n`, with `n = ∞` the case named by the roadmap.

## Main definitions

* `TauCeti.Diff I M n`: notation/abbreviation for the group `M ≃ₘ^n⟮I, I⟯ M` of `Cⁿ`
  self-diffeomorphisms of `M`.
* the `One`, `Mul`, `Inv`, and `Group` instances on `M ≃ₘ^n⟮I, I⟯ M`.
* `TauCeti.Diffeomorph.toPerm`: the forgetful group homomorphism to the underlying permutation
  group `Equiv.Perm M`, which is injective.

## Main results

* `TauCeti.Diffeomorph.mul_apply` / `one_apply` / `inv_apply` and the `coe_*` companions: the group
  operations act by composition, the identity, and the inverse diffeomorphism.
-/

namespace TauCeti

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace Diffeomorph

/-- The identity diffeomorphism is the unit of the self-diffeomorphism group. -/
instance instOne : One (M ≃ₘ^n⟮I, I⟯ M) where one := _root_.Diffeomorph.refl I M n

/-- Multiplication of self-diffeomorphisms is composition: `f * g` follows `g` then `f`, so that it
acts as `f ∘ g`, matching the `Equiv.Perm` convention. -/
instance instMul : Mul (M ≃ₘ^n⟮I, I⟯ M) where mul f g := g.trans f

/-- The inverse in the self-diffeomorphism group is the inverse diffeomorphism. -/
instance instInv : Inv (M ≃ₘ^n⟮I, I⟯ M) where inv f := f.symm

/-- The `Cⁿ` self-diffeomorphisms of `M` form a group under composition. The proofs are the
`Diffeomorph` composition lemmas (`refl_trans`, `trans_refl`, `self_trans_symm`), exactly as for
`Equiv.Perm`. -/
instance instGroup : Group (M ≃ₘ^n⟮I, I⟯ M) where
  mul_assoc _ _ _ := _root_.Diffeomorph.ext fun _ => rfl
  one_mul := _root_.Diffeomorph.trans_refl
  mul_one := _root_.Diffeomorph.refl_trans
  inv_mul_cancel := _root_.Diffeomorph.self_trans_symm

theorem one_def : (1 : M ≃ₘ^n⟮I, I⟯ M) = _root_.Diffeomorph.refl I M n := rfl

theorem mul_def (f g : M ≃ₘ^n⟮I, I⟯ M) : f * g = g.trans f := rfl

theorem inv_def (f : M ≃ₘ^n⟮I, I⟯ M) : f⁻¹ = f.symm := rfl

@[simp]
theorem coe_one : ⇑(1 : M ≃ₘ^n⟮I, I⟯ M) = id := rfl

@[simp]
theorem coe_mul (f g : M ≃ₘ^n⟮I, I⟯ M) : ⇑(f * g) = f ∘ g := rfl

theorem mul_apply (f g : M ≃ₘ^n⟮I, I⟯ M) (x : M) : (f * g) x = f (g x) := rfl

theorem one_apply (x : M) : (1 : M ≃ₘ^n⟮I, I⟯ M) x = x := rfl

theorem inv_apply (f : M ≃ₘ^n⟮I, I⟯ M) (x : M) : f⁻¹ x = f.symm x := rfl

@[simp]
theorem toEquiv_one : (1 : M ≃ₘ^n⟮I, I⟯ M).toEquiv = 1 := rfl

@[simp]
theorem toEquiv_mul (f g : M ≃ₘ^n⟮I, I⟯ M) : (f * g).toEquiv = f.toEquiv * g.toEquiv := rfl

/-- The forgetful group homomorphism from the self-diffeomorphism group to the permutation group of
the underlying set, sending a diffeomorphism to its underlying equivalence. -/
@[simps]
def toPerm : (M ≃ₘ^n⟮I, I⟯ M) →* Equiv.Perm M where
  toFun f := f.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toPerm_injective : Function.Injective (toPerm : (M ≃ₘ^n⟮I, I⟯ M) → Equiv.Perm M) :=
  _root_.Diffeomorph.toEquiv_injective

end Diffeomorph

/-- `Diff I M n` is the group of `Cⁿ` self-diffeomorphisms of the manifold `M` modelled on `I`,
under composition. With `n = ∞` this is the group underlying `Diff(M)` of the geometric-topology
roadmap. -/
abbrev Diff (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ∞ω) : Type _ := M ≃ₘ^n⟮I, I⟯ M

end TauCeti
