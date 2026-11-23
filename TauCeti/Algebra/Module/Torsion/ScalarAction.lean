/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Scalar actions on modules killed by an ideal

Let `A` be a `k`-algebra and `N` an `A`-module killed by an ideal `J`. Elements of `A` that are
congruent modulo `J` act in the same way on `N`. In particular, if `a * f ≡ c • f` modulo `J`
for a scalar `c : k`, then `a` acts as `c` on every vector fixed by `f`, and if
`f * a ≡ c • f` modulo `J`, then `f * a` acts as `c • f` on all of `N`.

Similarly, if `π : A →+* k` is a surjective ring homomorphism and `M` is an `A`-module annihilated
by `RingHom.ker π`, then the scalar action of `A` descends to a `k`-module structure on `M`
(`Module.IsTorsionBySet.moduleOfSurjective`).

## Main results

* `Module.IsTorsionBySet.smul_eq_smul_of_smul_eq_self`: on a vector fixed by `f`, `a` acts as
  `c` when `a * f ≡ c • f` modulo `J`.
* `Module.IsTorsionBySet.smul_smul_eq_smul_smul`: `f • a • x = c • f • x` when
  `f * a ≡ c • f` modulo `J`.
* `Module.IsTorsionBySet.smul_eq_smul_of_sub_mem`, `Module.IsTorsionBySet.smul_eq_smul_of_map_eq`:
  congruent scalars modulo `J` (or with equal image under `π`) act identically.
* `Module.IsTorsionBySet.moduleOfSurjective`, `Module.IsTorsionBySet.moduleOfSurjective_smul`,
  `Module.IsTorsionBySet.semilinearMapOfSurjective`,
  `Module.IsTorsionBySet.semilinearMapOfSurjective_bijective`: descent of scalar multiplication
  along a surjective ring homomorphism `π : A →+* k` and the corresponding `π`-semilinear
  bijective identity map.
* `Ideal.isTorsionBySet_of_mul_eq_bot`: an ideal `I` with `J * I = ⊥` is annihilated by `J`.
-/

public section

namespace Module.IsTorsionBySet

section Algebra

variable {k A N : Type*} [CommSemiring k] [Ring A] [Algebra k A] {J : Ideal A}
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- On a vector fixed by `f` in a module killed by `J`, an element `a` acts as the scalar `c`
with `a * f ≡ c • f` modulo `J`. -/
theorem smul_eq_smul_of_smul_eq_self (hN : Module.IsTorsionBySet A N J) {f a : A} {c : k}
    (hr : a * f - c • f ∈ J) {n : N} (hn : f • n = n) : a • n = c • n :=
  calc a • n = a • f • n := by rw [hn]
    _ = (a * f - c • f) • n + (c • f) • n := by rw [← add_smul, sub_add_cancel, mul_smul]
    _ = c • n := by rw [@hN n ⟨_, hr⟩, zero_add, smul_assoc, hn]

/-- In a module killed by `J`, `f * a` acts as the scalar `c • f` with `f * a ≡ c • f`
modulo `J`. -/
theorem smul_smul_eq_smul_smul (hN : Module.IsTorsionBySet A N J) {f a : A} {c : k}
    (hl : f * a - c • f ∈ J) (x : N) : f • a • x = c • f • x :=
  calc f • a • x = (f * a - c • f) • x + (c • f) • x := by
        rw [← add_smul, sub_add_cancel, mul_smul]
    _ = c • f • x := by rw [@hN x ⟨_, hl⟩, zero_add, smul_assoc]

end Algebra

section Surjective

variable {A k M : Type*} [Ring A] [Ring k] [AddCommGroup M] [Module A M]

/-- In an `A`-module annihilated by `J`, elements of `A` congruent modulo `J` act identically. -/
theorem smul_eq_smul_of_sub_mem {J : Set A} (hM : Module.IsTorsionBySet A M J)
    {a₁ a₂ : A} (ha : a₁ - a₂ ∈ J) (x : M) : a₁ • x = a₂ • x := by
  rw [← sub_eq_zero, ← sub_smul]
  exact @hM x ⟨a₁ - a₂, ha⟩

/-- In an `A`-module annihilated by `RingHom.ker π`, elements of `A` with the same image under
`π` act identically. -/
theorem smul_eq_smul_of_map_eq {π : A →+* k} (hM : Module.IsTorsionBySet A M (RingHom.ker π))
    {a₁ a₂ : A} (ha : π a₁ = π a₂) (x : M) : a₁ • x = a₂ • x :=
  hM.smul_eq_smul_of_sub_mem (by rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, ha, sub_self]) x

/-- Descent of scalar multiplication along a surjective ring homomorphism `π : A →+* k` for an
`A`-module `M` annihilated by `RingHom.ker π`, obtained by transporting `hM.module` across
`RingHom.quotientKerEquivOfSurjective`. -/
@[instance_reducible]
noncomputable def moduleOfSurjective {π : A →+* k}
    (hM : Module.IsTorsionBySet A M (RingHom.ker π)) (hπ : Function.Surjective π) :
    Module k M :=
  letI := hM.module
  Module.compHom M (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/-- The identity on an `A`-module annihilated by `RingHom.ker π`, bundled as a `π`-semilinear map
into the descended `k`-module `hM.moduleOfSurjective hπ` by transporting `hM.semilinearMap`. -/
noncomputable def semilinearMapOfSurjective {π : A →+* k}
    (hM : Module.IsTorsionBySet A M (RingHom.ker π)) (hπ : Function.Surjective π) :
    letI := hM.moduleOfSurjective hπ
    M →ₛₗ[π] M :=
  letI := hM.module
  letI := hM.moduleOfSurjective hπ
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have : RingHomCompTriple (Ideal.Quotient.mk (RingHom.ker π)) e.toRingHom π :=
    ⟨RingHom.ext fun a ↦ RingHom.quotientKerEquivOfSurjective_apply_mk hπ a⟩
  let id_e : M →ₛₗ[e.toRingHom] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change r • x = e.symm (e r) • x
        rw [e.symm_apply_apply] }
  id_e.comp hM.semilinearMap

/-- Evaluating `semilinearMapOfSurjective` returns the input vector. -/
@[simp]
theorem semilinearMapOfSurjective_apply {π : A →+* k}
    (hM : Module.IsTorsionBySet A M (RingHom.ker π)) (hπ : Function.Surjective π) (x : M) :
    hM.semilinearMapOfSurjective hπ x = x := (rfl)

/-- `semilinearMapOfSurjective` is bijective. -/
theorem semilinearMapOfSurjective_bijective {π : A →+* k}
    (hM : Module.IsTorsionBySet A M (RingHom.ker π)) (hπ : Function.Surjective π) :
    Function.Bijective (hM.semilinearMapOfSurjective hπ) :=
  ⟨fun x y h ↦ by simpa [semilinearMapOfSurjective_apply] using h,
    fun y ↦ ⟨y, hM.semilinearMapOfSurjective_apply hπ y⟩⟩

/-- In `hM.moduleOfSurjective hπ`, the descended scalar `π a` acts as `a`. -/
@[simp]
theorem moduleOfSurjective_smul {π : A →+* k}
    (hM : Module.IsTorsionBySet A M (RingHom.ker π)) (hπ : Function.Surjective π)
    (a : A) (x : M) :
    letI := hM.moduleOfSurjective hπ
    π a • x = a • x := by
  let := hM.moduleOfSurjective hπ
  simpa only [semilinearMapOfSurjective_apply] using
    ((hM.semilinearMapOfSurjective hπ).map_smulₛₗ a x).symm

end Surjective

end Module.IsTorsionBySet

namespace Ideal

/-- If `J * I = ⊥`, then `I` viewed as an `A`-module is annihilated by `J`. -/
theorem isTorsionBySet_of_mul_eq_bot {A : Type*} [Ring A] {J I : Ideal A}
    (hJI : J * I = ⊥) : Module.IsTorsionBySet A I J := fun x r ↦
  Subtype.ext <| mem_bot.mp (hJI ▸ mul_mem_mul r.property x.property)

end Ideal
