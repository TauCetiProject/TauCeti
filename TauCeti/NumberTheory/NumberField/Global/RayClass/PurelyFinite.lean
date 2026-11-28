/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact

/-!
# Moduli without archimedean conditions and their residue-unit quotients

When the infinite part of a modulus `𝔪` of a number field `K` is empty — as is automatic for every
modulus of a totally complex number field (`Modulus.infinitePart_eq_empty`) — no archimedean sign
conditions appear in `IsCongrOne 𝔪`. The ray class exact sequence of
`TauCeti.NumberTheory.NumberField.Global.RayClass.Exact` then simplifies to

```text
1 → unitsCongruenceSubgroup 𝔪 → (𝓞 K)ˣ → (𝓞 K ⧸ 𝔪.finitePart)ˣ
  → RayClassGroup 𝔪 → ClassGroup (𝓞 K) → 1.
```

Using the purely finite moduli `Modulus.ofIdeal` and `Modulus.spanNat` from
`TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus`, this file characterizes
`unitsCongruenceSubgroup` when `𝔪.infinitePart = ∅`
(`unitsCongruenceSubgroup_eq_ker_of_infinitePart_eq_empty`,
`mem_unitsCongruenceSubgroup_iff_of_infinitePart_eq_empty`), and establishes the group isomorphism
`residueUnitsQuotientEquivKerRayClassToClassGroup` between `(𝓞 K ⧸ 𝔪.finitePart)ˣ` modulo the image
of `(𝓞 K)ˣ` and `(rayClassToClassGroup 𝔪).ker` via `residueRayClass`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Integer units modulo the finite part -/

/-- When `𝔪` has empty infinite part, the sign component of any element of
`𝔪.infinitePart → ℤˣ` is trivial. -/
private theorem eq_one_of_infinitePart_eq_empty {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅)
    (s : 𝔪.infinitePart → ℤˣ) : s = 1 := by
  ext w
  exact False.elim ((Finset.eq_empty_iff_forall_notMem.mp h) w.val w.property)

/-- When `𝔪.infinitePart = ∅`, the units congruent to one modulo `𝔪` are the kernel of reduction
modulo `𝔪.finitePart`. -/
theorem unitsCongruenceSubgroup_eq_ker_of_infinitePart_eq_empty {𝔪 : Modulus K}
    (h : 𝔪.infinitePart = ∅) :
    unitsCongruenceSubgroup 𝔪 =
      (Units.map (Ideal.Quotient.mk 𝔪.finitePart : 𝓞 K →* 𝓞 K ⧸ 𝔪.finitePart)).ker := by
  ext u
  rw [← ker_unitsResidueSignHom, MonoidHom.mem_ker, MonoidHom.mem_ker, Prod.ext_iff,
    unitsResidueSignHom_fst]
  simp [eq_one_of_infinitePart_eq_empty h]

/-- When `𝔪.infinitePart = ∅`, an integer unit `u` is congruent to one modulo `𝔪` if and only if
`u - 1 ∈ 𝔪.finitePart`. -/
theorem mem_unitsCongruenceSubgroup_iff_of_infinitePart_eq_empty {𝔪 : Modulus K}
    (h : 𝔪.infinitePart = ∅) {u : (𝓞 K)ˣ} :
    u ∈ unitsCongruenceSubgroup 𝔪 ↔ (u : 𝓞 K) - 1 ∈ 𝔪.finitePart := by
  rw [unitsCongruenceSubgroup_eq_ker_of_infinitePart_eq_empty h, MonoidHom.mem_ker, Units.ext_iff,
    Units.coe_map, MonoidHom.coe_ofClass, Units.val_one,
    ← map_one (Ideal.Quotient.mk 𝔪.finitePart), Ideal.Quotient.eq]

/-- Membership in `unitsCongruenceSubgroup (Modulus.ofIdeal I hI)` is `u - 1 ∈ I`. -/
theorem mem_unitsCongruenceSubgroup_ofIdeal_iff {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {u : (𝓞 K)ˣ} :
    u ∈ unitsCongruenceSubgroup (Modulus.ofIdeal I hI) ↔ (u : 𝓞 K) - 1 ∈ I :=
  mem_unitsCongruenceSubgroup_iff_of_infinitePart_eq_empty (Modulus.ofIdeal_infinitePart I hI)

/-- Membership in `unitsCongruenceSubgroup (Modulus.spanNat K n)` is `(n : 𝓞 K) ∣ u - 1`. -/
theorem mem_unitsCongruenceSubgroup_spanNat_iff {n : ℕ} [NeZero n] {u : (𝓞 K)ˣ} :
    u ∈ unitsCongruenceSubgroup (Modulus.spanNat K n) ↔
      (n : 𝓞 K) ∣ (u : 𝓞 K) - 1 :=
  (mem_unitsCongruenceSubgroup_iff_of_infinitePart_eq_empty
    (Modulus.spanNat_infinitePart n)).trans Ideal.mem_span_singleton

/-! ### The purely finite residue-unit map to the ray class group -/

/-- When `𝔪.infinitePart = ∅`, the kernel of `residueRayClass 𝔪` is the image of `(𝓞 K)ˣ` in
`(𝓞 K ⧸ 𝔪.finitePart)ˣ`. -/
theorem ker_residueRayClass_of_infinitePart_eq_empty {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅) :
    (residueRayClass 𝔪).ker =
      (Units.map (Ideal.Quotient.mk 𝔪.finitePart : 𝓞 K →* 𝓞 K ⧸ 𝔪.finitePart)).range := by
  ext u
  rw [MonoidHom.mem_ker, residueRayClass_apply, ← MonoidHom.mem_ker, ker_residueSignRayClass,
    MonoidHom.mem_range, MonoidHom.mem_range]
  refine exists_congr fun v ↦ ?_
  rw [Prod.ext_iff, unitsResidueSignHom_fst]
  simp [eq_one_of_infinitePart_eq_empty h]

/-- When `𝔪.infinitePart = ∅`, the image of `residueRayClass 𝔪` is the kernel of
`rayClassToClassGroup 𝔪`. -/
theorem range_residueRayClass_of_infinitePart_eq_empty {𝔪 : Modulus K} (h : 𝔪.infinitePart = ∅) :
    (residueRayClass 𝔪).range = (rayClassToClassGroup 𝔪).ker := by
  rw [← range_residueSignRayClass]
  ext c
  rw [MonoidHom.mem_range, MonoidHom.mem_range]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨(u, 1), ?_⟩, fun ⟨a, ha⟩ ↦ ⟨a.1, ?_⟩⟩
  · rwa [← residueRayClass_apply]
  · rw [residueRayClass_apply, ← eq_one_of_infinitePart_eq_empty h a.2, Prod.mk.eta, ha]

/-- **The kernel of `RayClassGroup 𝔪 → ClassGroup (𝓞 K)` when `𝔪.infinitePart = ∅`** is canonically
isomorphic to the quotient of `(𝓞 K ⧸ 𝔪.finitePart)ˣ` by the image of the global integer units. -/
noncomputable def residueUnitsQuotientEquivKerRayClassToClassGroup {𝔪 : Modulus K}
    (h : 𝔪.infinitePart = ∅) :
    (𝓞 K ⧸ 𝔪.finitePart)ˣ ⧸
        (Units.map (Ideal.Quotient.mk 𝔪.finitePart : 𝓞 K →* 𝓞 K ⧸ 𝔪.finitePart)).range ≃*
      (rayClassToClassGroup 𝔪).ker :=
  ((QuotientGroup.quotientMulEquivOfEq
      (ker_residueRayClass_of_infinitePart_eq_empty h).symm).trans
    (QuotientGroup.quotientKerEquivRange (residueRayClass 𝔪))).trans
    (MulEquiv.subgroupCongr (range_residueRayClass_of_infinitePart_eq_empty h))

/-- `residueUnitsQuotientEquivKerRayClassToClassGroup` sends the coset of `u` to
`residueRayClass 𝔪 u`. -/
@[simp]
theorem coe_residueUnitsQuotientEquivKerRayClassToClassGroup_mk {𝔪 : Modulus K}
    (h : 𝔪.infinitePart = ∅) (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) :
    (residueUnitsQuotientEquivKerRayClassToClassGroup h u : RayClassGroup 𝔪) =
      residueRayClass 𝔪 u := by
  simp [residueUnitsQuotientEquivKerRayClassToClassGroup]

end TauCeti.GlobalNumberFields
