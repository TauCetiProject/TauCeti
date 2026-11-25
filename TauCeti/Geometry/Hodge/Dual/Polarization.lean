/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.SelfDuality
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Form

/-!
# The scaled dual form polarizes the dual Hodge structure

Let `Q` polarize an integral pure Hodge structure `V` of weight `n`. The map
`Q♭ : V → Hom(V, ℤ)`, `x ↦ Q(x, ·)`, is injective with finite cokernel. If a positive integer `a`
kills that cokernel, the integral form `a Q^∨` on `Hom(V, ℤ)`
(`LinearMap.BilinForm.scaledDualForm`), `(ξ, η) ↦ ξ(y_η)` where `Q♭ y_η = a η`, polarizes the dual
Hodge structure `V^*` of weight `-n` (`TauCeti.Hodge.IsPolarization.scaledDualForm`). When `Q` is
a perfect pairing one may take `a = 1`: the dual form `Q^∨` is then an integral, principal
polarization of `V^*` (`TauCeti.Hodge.IsPolarization.scaledDualForm_one`,
`LinearMap.BilinForm.isPerfPair_scaledDualForm_one`).

The proof: the map `η ↦ y_η` is a Hodge morphism `V^*(-n) → V`, since composed with the
self-duality `Q♭` it is multiplication by `a` (`TauCeti.Hodge.Polarization.homOfCompToDualHom`).
It is injective, and `Q(y_ξ, y_η) = a · (a Q^∨)(ξ, η)`
(`LinearMap.BilinForm.comp_scaledDualPreimage`). So `Q` pulls back to `a` times the scaled
dual form, which therefore polarizes `V^*(-n)` (`TauCeti.Hodge.IsPolarization.of_smul`); a Tate
twist then gives `V^*`.

## Main results

* `TauCeti.Hodge.IsPolarization.scaledDualHom`: the Hodge morphism `η ↦ y_η` from `V^*(-n)` to `V`.
* `TauCeti.Hodge.IsPolarization.scaledDualForm`: `a Q^∨` polarizes `V^*`.
* `TauCeti.Hodge.IsPolarization.scaledDualForm_one`: for a principal `Q`, `Q^∨` polarizes `V^*`.

## References

* Stanford VIGRE notes, *Complex theory of abelian varieties* (2004), Definitions 1.13–1.14 and
  Lemma 1.16, pp. 5–6, <https://math.stanford.edu/~conrad/vigregroup/vigre04/abvaran.pdf>.
-/

public section

namespace TauCeti.Hodge

open IsBaseChange
open scoped ComplexOrder

variable {V : Type*} {Vℂ : Type*}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}
variable {hs : HodgeStructure hℂ n}
variable {Q : LinearMap.BilinForm ℤ V} {a : ℤ}

namespace IsPolarization

variable [Module.Free ℤ V] [Module.Finite ℤ V]

/-- The map `η ↦ y_η`, with `Q♭ y_η = a η`, as a **Hodge morphism `V^*(-n) → V`**. -/
noncomputable def scaledDualHom (hQ : IsPolarization hℂ hs Q)
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range Q) :
    HodgeStructure.Hom hs.dualTateTwist hs :=
  Polarization.homOfCompToDualHom ⟨Q, hQ⟩ (Q.scaledDualPreimage hQ.injective a ha) a
    (LinearMap.ext fun η ↦ by simp)

/-- The lattice map underlying `scaledDualHom` is `η ↦ y_η`. -/
@[simp]
theorem scaledDualHom_toIntLinearMap (hQ : IsPolarization hℂ hs Q)
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range Q) :
    (hQ.scaledDualHom ha).toIntLinearMap = Q.scaledDualPreimage hQ.injective a ha :=
  Polarization.homOfCompToDualHom_toIntLinearMap _ _ _ _

/-- **The scaled dual form polarizes the dual Hodge structure.** If `Q` polarizes `V` and the
positive integer `a` kills the cokernel of `Q♭ : V → Hom(V, ℤ)`, then `a Q^∨` polarizes the dual
Hodge structure `V^*`, of weight `-n`. -/
theorem scaledDualForm (hQ : IsPolarization hℂ hs Q)
    (ha : ∀ η : Module.Dual ℤ V, a • η ∈ LinearMap.range Q) (ha0 : 0 < a) :
    IsPolarization (isBaseChange_dualLatticeMap hℂ) hs.dual
      (Q.scaledDualForm hQ.injective a ha) := by
  have hinj : Function.Injective (hQ.scaledDualHom ha).toIntLinearMap := fun ξ η h ↦ by
    have := congr(Q $h)
    simp only [scaledDualHom_toIntLinearMap, LinearMap.BilinForm.apply_scaledDualPreimage] at this
    exact smul_right_injective _ ha0.ne' this
  have htwist := (hQ.comp (hQ.scaledDualHom ha) hinj)
  rw [scaledDualHom_toIntLinearMap, Q.comp_scaledDualPreimage hQ.injective a ha] at htwist
  exact (of_smul ha0 htwist).of_F_eq_F_add n (by ring) fun p ↦ by
    rw [HodgeStructure.dualTateTwist_F, add_sub_cancel_right]

/-- **The dual form of a principal polarization polarizes the dual.** If `Q` polarizes `V`
and is a perfect pairing, the integral dual form `Q^∨` (the case `a = 1`) polarizes `V^*`; it is a
perfect pairing by `LinearMap.BilinForm.isPerfPair_scaledDualForm_one`. -/
theorem scaledDualForm_one (hQ : IsPolarization hℂ hs Q) [Q.IsPerfPair] :
    IsPolarization (isBaseChange_dualLatticeMap hℂ) hs.dual
      (Q.scaledDualForm (LinearMap.IsPerfPair.bijective_left Q).injective 1
        Q.one_smul_mem_range_of_isPerfPair) :=
  hQ.scaledDualForm Q.one_smul_mem_range_of_isPerfPair one_pos

end IsPolarization

end TauCeti.Hodge
