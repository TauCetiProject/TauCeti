/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Degree scaling of an exterior algebra

For a unit `r` of the base ring, the scalar multiplication `r • id` induces an algebra automorphism
of the exterior algebra `⋀ M`, which multiplies the `n`-th exterior power by `r ^ n`. Conjugating
by it rescales exterior multiplication by `ι m` by the factor `r`, rescales every contraction by
the factor `r⁻¹`, and commutes with the grade involution.

These are the operators that change the normalization of a Fock action: conjugating a Clifford
action on `⋀ W` by a degree scaling replaces its creation operators by `r` times themselves and
its annihilation operators by `r⁻¹` times themselves, which preserves every
creation–annihilation anticommutator.

## Main definitions

* `TauCeti.ExteriorAlgebra.degreeScaling`: the algebra automorphism of `⋀ M` induced by `r • id`.

## Main results

* `TauCeti.ExteriorAlgebra.degreeScaling_of_mem_exteriorPower`: the degree scaling acts on the
  `n`-th exterior power by `r ^ n`.
* `TauCeti.ExteriorAlgebra.degreeScaling_ι`, `ExteriorAlgebra.degreeScaling_involute` and
  `ExteriorAlgebra.degreeScaling_contractLeft`: its interaction with the generators, the
  grade involution and contraction.
-/

public section

open CliffordAlgebra ExteriorAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

namespace TauCeti.ExteriorAlgebra

/-- **The degree scaling of an exterior algebra** by a unit `r`: the algebra automorphism of
`⋀ M` induced by the scalar multiplication `r • id` of `M`. It multiplies the `n`-th exterior power
by `r ^ n` (`TauCeti.ExteriorAlgebra.degreeScaling_of_mem_exteriorPower`). -/
noncomputable def degreeScaling (r : Rˣ) : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M :=
  AlgEquiv.ofAlgHom (_root_.ExteriorAlgebra.map ((r : R) • LinearMap.id))
    (_root_.ExteriorAlgebra.map (((r⁻¹ : Rˣ) : R) • LinearMap.id))
    (by ext; simp [smul_smul]) (by ext; simp [smul_smul])

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

open TauCeti.ExteriorAlgebra

/-- The degree scaling is the exterior-algebra map induced by `r • id`. -/
theorem degreeScaling_apply (r : Rˣ) (x : ExteriorAlgebra R M) :
    degreeScaling r x = _root_.ExteriorAlgebra.map ((r : R) • LinearMap.id) x :=
  (rfl)

end ExteriorAlgebra

namespace TauCeti.ExteriorAlgebra

/-- The degree scaling by `r` multiplies a generator by `r`. -/
@[simp]
theorem degreeScaling_ι (r : Rˣ) (m : M) :
    degreeScaling r (_root_.ExteriorAlgebra.ι R m) = (r : R) • _root_.ExteriorAlgebra.ι R m := by
  rw [degreeScaling_apply, _root_.ExteriorAlgebra.map_apply_ι, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul]

/-- The inverse of the degree scaling by `r` is the degree scaling by `r⁻¹`. -/
@[simp]
theorem degreeScaling_symm (r : Rˣ) :
    (degreeScaling r).symm = degreeScaling (M := M) r⁻¹ :=
  AlgEquiv.ext fun _ ↦ (rfl)

/-- The degree scaling by the unit `1` is the identity. -/
@[simp]
theorem degreeScaling_one : degreeScaling (M := M) (1 : Rˣ) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun x ↦ ?_
  rw [degreeScaling_apply, Units.val_one, one_smul, _root_.ExteriorAlgebra.map_id,
    AlgHom.id_apply, AlgEquiv.coe_refl, id_eq]

/-- **The degree scaling acts on the `n`-th exterior power by `r ^ n`.** -/
theorem degreeScaling_of_mem_exteriorPower (r : Rˣ) {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) : degreeScaling r x = (r : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap s => rw [AlgEquiv.commutes, pow_zero, one_smul]
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, degreeScaling_ι, smul_mul_smul_comm, pow_succ']

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

open TauCeti.ExteriorAlgebra

/-- The degree scaling commutes with the grade involution. -/
@[simp]
theorem degreeScaling_involute (r : Rˣ) (x : ExteriorAlgebra R M) :
    degreeScaling r (involute (Q := (0 : QuadraticForm R M)) x) =
      involute (Q := (0 : QuadraticForm R M)) (degreeScaling r x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s => simp
  | ι m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- **Conjugating a contraction by the degree scaling by `r` multiplies it by `r⁻¹`.** -/
@[simp]
theorem degreeScaling_contractLeft (r : Rˣ) (d : Module.Dual R M) (x : ExteriorAlgebra R M) :
    degreeScaling r (contractLeft (Q := (0 : QuadraticForm R M)) d x) =
      ((r⁻¹ : Rˣ) : R) • contractLeft (Q := (0 : QuadraticForm R M)) d (degreeScaling r x) := by
  have hd : (((r⁻¹ : Rˣ) : R) • d) ∘ₗ ((r : R) • LinearMap.id) = d := by
    ext m
    simp
  rw [degreeScaling_apply, degreeScaling_apply, ← LinearMap.smul_apply, ← map_smul,
    _root_.ExteriorAlgebra.contractLeft_map, hd]

end ExteriorAlgebra
