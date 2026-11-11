/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import Mathlib.Tactic.Group

/-!
# Surface groups of small genus

This file identifies the surface groups `S±(g, m)` of `TauCeti.GroupTheory.SurfaceGroup.Basic` for
the smallest surfaces.

* **Genus zero with boundary.** In `S⁺(0, m + 1)` the relation `p₁ ⋯ p_{m+1} = 1` only determines
  the last peripheral element, so `S⁺(0, m + 1)` is free on `p₁, …, p_m`. In particular the disc
  group `S⁺(0, 1)` is trivial and the pair-of-pants group `S⁺(0, 3)` is free of rank two on `p₁`
  and `p₂`, with `p₃ = (p₁ p₂)⁻¹`.
* **The sphere.** `S⁺(0, 0)` has no generators, so it is trivial.
* **The torus.** `S⁺(1, 0) = ⟨a, b | a⁻¹ b⁻¹ a b⟩` is free abelian of rank two.
* **The projective plane.** `S⁻(1, 0) = ⟨c | c ^ 2⟩` is cyclic of order two.

These are the first consistency checks on the presentations: the Euler characteristics
`χ = 2 - 2g - m` and `χ = 2 - g - m` of the disc, sphere, pair of pants, torus and projective plane
are `1, 2, -1, 0, 1`, and in each case with boundary the group is free of rank `1 - χ`.

## Main definitions

* `TauCeti.SurfaceGroup.Orientable.genusZeroEquivFreeGroup`: `S⁺(0, m + 1) ≃* FreeGroup (Fin m)`.
* `TauCeti.SurfaceGroup.Orientable.genusZeroBasis`: the free basis `p₁, …, p_m` of `S⁺(0, m + 1)`.
* `TauCeti.SurfaceGroup.Orientable.torusEquiv`: `S⁺(1, 0) ≃* Multiplicative (Fin 2 → ℤ)`.
* `TauCeti.SurfaceGroup.Nonorientable.projectivePlaneEquiv`:
  `S⁻(1, 0) ≃* Multiplicative (ZMod 2)`.

## Main results

* `TauCeti.SurfaceGroup.Orientable.instSubsingletonOrientableZeroZero` and
  `TauCeti.SurfaceGroup.Orientable.instSubsingletonOrientableZeroOne`: the sphere and disc groups
  are trivial.
* `TauCeti.SurfaceGroup.Orientable.instIsFreeGroupOrientableZeroSucc`: `S⁺(0, m + 1)` is a free
  group.
* `TauCeti.SurfaceGroup.Orientable.commute_torus_a_b`: the two generators of the torus group
  commute.
* `TauCeti.SurfaceGroup.Nonorientable.natCard_projectivePlane`: `S⁻(1, 0)` has order two.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2 (the fundamental groups of the torus, the
  projective plane and the closed surfaces from their polygon presentations).
-/

public section

namespace TauCeti

namespace SurfaceGroup

open FreeGroup (of)

namespace Orientable

/-- The sphere group `S⁺(0, 0)` has no generators. -/
instance instIsEmptyOrientableGeneratorZeroZero : IsEmpty (OrientableGenerator 0 0) :=
  ⟨fun
    | .a i => i.elim0
    | .b i => i.elim0
    | .peripheral j => j.elim0⟩

/-- The orientable surface group `S⁺(0, 0)` of the sphere is trivial. -/
instance instSubsingletonOrientableZeroZero : Subsingleton (Orientable 0 0) := by
  refine subsingleton_of_forall_eq 1 fun x ↦ ?_
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
  rw [Subsingleton.elim w 1, map_one]

/-- The surface word of a genus-zero surface whose last peripheral element closes up the product
of the others is trivial. -/
private theorem orientableWord_genusZero {G : Type*} [Group G] {m : ℕ} (γ : Fin m → G) :
    orientableWord (Fin.elim0 : Fin 0 → G) Fin.elim0
      (Fin.lastCases (List.ofFn γ).prod⁻¹ γ) = 1 := by
  rw [orientableWord_def, List.ofFn_succ' (Fin.lastCases _ _), List.prod_concat]
  simp only [List.ofFn_zero, List.prod_nil, one_mul, Fin.lastCases_castSucc, Fin.lastCases_last,
    mul_inv_cancel]

/-- **Genus-zero surface groups with boundary are free.** The orientable surface group
`S⁺(0, m + 1)` is the free group on the peripheral elements `p₁, …, p_m`; the last peripheral
element is `p_{m+1} = (p₁ ⋯ p_m)⁻¹`. -/
def genusZeroEquivFreeGroup (m : ℕ) : Orientable 0 (m + 1) ≃* FreeGroup (Fin m) :=
  MonoidHom.toMulEquiv
    (lift Fin.elim0 Fin.elim0 (Fin.lastCases (List.ofFn of).prod⁻¹ of)
      (orientableWord_genusZero of))
    (FreeGroup.lift fun j ↦ peripheral 0 (m + 1) j.castSucc)
    (hom_ext (fun i ↦ i.elim0) (fun i ↦ i.elim0) fun j ↦ by
      induction j using Fin.lastCases with
      | last =>
        simp [peripheral_last, map_list_prod, List.map_ofFn, Function.comp_def]
      | cast j => simp)
    (FreeGroup.ext_hom _ _ fun j ↦ by simp)

@[simp]
theorem genusZeroEquivFreeGroup_peripheral_castSucc {m : ℕ} (j : Fin m) :
    genusZeroEquivFreeGroup m (peripheral 0 (m + 1) j.castSucc) = of j := by
  simp [genusZeroEquivFreeGroup]

@[simp]
theorem genusZeroEquivFreeGroup_peripheral_last (m : ℕ) :
    genusZeroEquivFreeGroup m (peripheral 0 (m + 1) (Fin.last m)) = (List.ofFn of).prod⁻¹ := by
  simp [genusZeroEquivFreeGroup]

@[simp]
theorem genusZeroEquivFreeGroup_symm_of {m : ℕ} (j : Fin m) :
    (genusZeroEquivFreeGroup m).symm (of j) = peripheral 0 (m + 1) j.castSucc := by
  simp [genusZeroEquivFreeGroup]

/-- The free basis `p₁, …, p_m` of the orientable surface group `S⁺(0, m + 1)`. -/
def genusZeroBasis (m : ℕ) : FreeGroupBasis (Fin m) (Orientable 0 (m + 1)) :=
  .ofRepr (genusZeroEquivFreeGroup m)

@[simp]
theorem genusZeroBasis_apply {m : ℕ} (j : Fin m) :
    genusZeroBasis m j = peripheral 0 (m + 1) j.castSucc :=
  genusZeroEquivFreeGroup_symm_of j

/-- A genus-zero orientable surface group with nonempty boundary is free. -/
instance instIsFreeGroupOrientableZeroSucc (m : ℕ) : IsFreeGroup (Orientable 0 (m + 1)) :=
  (genusZeroBasis m).isFreeGroup

/-- The orientable surface group `S⁺(0, 1)` of the disc is trivial. -/
instance instSubsingletonOrientableZeroOne : Subsingleton (Orientable 0 1) :=
  (genusZeroEquivFreeGroup 0).toEquiv.subsingleton

/-- The two generators of the torus group `S⁺(1, 0)` commute. -/
theorem commute_torus_a_b : Commute (a 1 0 0) (b 1 0 0) := by
  have h := orientableWord_a_b_peripheral 1 0
  simp only [orientableWord_def, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one] at h
  refine (inv_mul_eq_one.mp ?_).symm
  rw [mul_inv_rev, ← h]
  group

/-- The isomorphism from `ℤ²` to the torus group `S⁺(1, 0)`, sending `(x, y)` to `a ^ x * b ^ y`;
it is a homomorphism because `a` and `b` commute. -/
private def torusEquivSymm : Multiplicative (Fin 2 → ℤ) →* Orientable 1 0 where
  toFun v := a 1 0 0 ^ v.toAdd 0 * b 1 0 0 ^ v.toAdd 1
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, mul_assoc,
      (commute_torus_a_b.zpow_zpow (w.toAdd 0) (v.toAdd 1)).symm.left_comm]

/-- **The torus group is free abelian of rank two.** The orientable surface group `S⁺(1, 0)` is
isomorphic to `ℤ²`, written multiplicatively, by sending `a` and `b` to the two standard basis
vectors. -/
def torusEquiv : Orientable 1 0 ≃* Multiplicative (Fin 2 → ℤ) :=
  MonoidHom.toMulEquiv
    (lift (fun _ ↦ .ofAdd (Pi.single 0 1)) (fun _ ↦ .ofAdd (Pi.single 1 1)) Fin.elim0
      (by simp [orientableWord_def]))
    torusEquivSymm
    (hom_ext (fun i ↦ by simp [Subsingleton.elim i 0, torusEquivSymm])
      (fun i ↦ by simp [Subsingleton.elim i 0, torusEquivSymm]) fun j ↦ j.elim0)
    (MonoidHom.ext fun v ↦ by
      ext k
      fin_cases k <;> simp [torusEquivSymm])

@[simp]
theorem torusEquiv_a (i : Fin 1) : torusEquiv (a 1 0 i) = .ofAdd (Pi.single 0 1) := by
  simp [torusEquiv]

@[simp]
theorem torusEquiv_b (i : Fin 1) : torusEquiv (b 1 0 i) = .ofAdd (Pi.single 1 1) := by
  simp [torusEquiv]

@[simp]
theorem torusEquiv_symm_apply (v : Multiplicative (Fin 2 → ℤ)) :
    torusEquiv.symm v = a 1 0 0 ^ v.toAdd 0 * b 1 0 0 ^ v.toAdd 1 :=
  (rfl)

end Orientable

namespace Nonorientable

/-- The homomorphism from `ℤ / 2` to the projective-plane group `S⁻(1, 0)`, sending the generator
to `c`; it is well defined because `c ^ 2 = 1`. -/
private def projectivePlaneEquivSymm : Multiplicative (ZMod 2) →* Nonorientable 1 0 :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift 2
    ⟨zmultiplesHom _ (Additive.ofMul (c 1 0 0)), by
      have h := nonorientableWord_c_peripheral 1 0
      simp only [nonorientableWord_def, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
        List.prod_nil, mul_one] at h
      simp [← ofMul_zpow, h]⟩

private theorem projectivePlaneEquivSymm_intCast (k : ℤ) :
    projectivePlaneEquivSymm (.ofAdd (k : ZMod 2)) = c 1 0 0 ^ k := by
  simp [projectivePlaneEquivSymm, ZMod.lift_coe]

/-- **The projective-plane group has order two.** The nonorientable surface group `S⁻(1, 0)` is
isomorphic to `ℤ / 2`, written multiplicatively, by sending `c` to the generator. -/
def projectivePlaneEquiv : Nonorientable 1 0 ≃* Multiplicative (ZMod 2) :=
  MonoidHom.toMulEquiv
    (lift (fun _ ↦ .ofAdd 1) Fin.elim0 (by simp [nonorientableWord_def]; rfl))
    projectivePlaneEquivSymm
    (hom_ext (fun i ↦ by
      simpa [Subsingleton.elim i 0] using projectivePlaneEquivSymm_intCast 1) fun j ↦ j.elim0)
    (MonoidHom.ext fun x ↦ by
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
      rw [MonoidHom.comp_apply, ← ofAdd_toAdd x, ← hk, projectivePlaneEquivSymm_intCast, map_zpow,
        lift_c, ← ofAdd_zsmul, zsmul_one, MonoidHom.id_apply])

@[simp]
theorem projectivePlaneEquiv_c (i : Fin 1) : projectivePlaneEquiv (c 1 0 i) = .ofAdd 1 := by
  simp [projectivePlaneEquiv]

@[simp]
theorem projectivePlaneEquiv_symm_ofAdd_intCast (k : ℤ) :
    projectivePlaneEquiv.symm (.ofAdd (k : ZMod 2)) = c 1 0 0 ^ k :=
  projectivePlaneEquivSymm_intCast k

/-- The nonorientable surface group `S⁻(1, 0)` of the projective plane has order two. -/
theorem natCard_projectivePlane : Nat.card (Nonorientable 1 0) = 2 := by
  rw [Nat.card_congr (projectivePlaneEquiv.toEquiv.trans Multiplicative.toAdd), Nat.card_zmod]

end Nonorientable

end SurfaceGroup

end TauCeti
