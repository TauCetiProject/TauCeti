/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transvection
public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The Iwasawa structure of the symplectic group on projective space

Over a field `K`, the standard symplectic group `Sp_{2m}(K)` (`TauCeti.GLSymplecticFin m K`) acts on
the projective space `ℙ K (Fin (m + m) → K)` through its action on vectors. To a point `p` of
projective space attach the group of symplectic transvections along `p`,

```text
T(p) = { τ_{v,c} : c ∈ K },        v a nonzero vector on the line p.
```

It does not depend on the choice of `v`, because `τ_{a v,c} = τ_{v,a²c}` and `a² ≠ 0`. Each `T(p)`
is abelian, being the image of the additive group of `K`; conjugation by `g` carries `T(p)` to
`T(g p)`, because `g τ_{v,c} g⁻¹ = τ_{g v,c}`; and the `T(p)` generate the symplectic group, because
the symplectic transvections do. These are exactly the axioms of Mathlib's
`MulAction.IwasawaStructure`, the data of Iwasawa's simplicity criterion
`MulAction.IwasawaStructure.isSimpleGroup`. This file packages them as
`TauCeti.GLSymplecticFin.iwasawaStructure`.

Applying the criterion to the projective symplectic group needs three further inputs: perfectness
of `Sp_{2m}(K)` (`TauCeti.GLSymplecticFin.commutator_eq_top` gives it when `K` has an element
`a ≠ 0` with `a² ≠ 1`), quasiprimitivity of the action on projective space, and the identification
of the kernel of that action with the centre `{±1}`. The last two are not proved here.

## Main declarations

* `TauCeti.GLSymplecticFin.transvectionSubgroup`: the subgroup `T(p)` of transvections along `p`,
  with `TauCeti.GLSymplecticFin.transvectionSubgroup_mk` computing it from any representative.
* `TauCeti.GLSymplecticFin.transvectionSubgroup_smul`: `T(g p) = g T(p) g⁻¹`.
* `TauCeti.GLSymplecticFin.iSup_transvectionSubgroup`: the `T(p)` generate `Sp_{2m}(K)`.
* `TauCeti.GLSymplecticFin.iwasawaStructure`: the resulting Iwasawa structure.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* E. Artin, *Geometric Algebra* (1957), Chapter III, §§4--5, and Chapter IV, §1.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization Pointwise

namespace TauCeti.GLSymplecticFin

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- **The symplectic transvections along a point `p` of projective space**: the group of
transvections `τ_{v,c}` along a nonzero vector `v` on the line `p`. It does not depend on the
choice of `v` (`TauCeti.GLSymplecticFin.transvectionSubgroup_mk`). -/
noncomputable def transvectionSubgroup (p : ℙ K (Fin (m + m) → K)) :
    Subgroup (GLSymplecticFin m K) :=
  (symplecticTransvectionHom p.rep).range

/-- The transvection group along the point of a nonzero vector `v` consists of the transvections
along `v`. -/
theorem transvectionSubgroup_mk {v : Fin (m + m) → K} (hv : v ≠ 0) :
    transvectionSubgroup (Projectivization.mk K v hv) = (symplecticTransvectionHom v).range := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ v (Projectivization.rep_nonzero _) hv).mp
    (Projectivization.mk_rep _)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact Projectivization.rep_nonzero (Projectivization.mk K v hv) (by rw [← ha, zero_smul])
  rw [transvectionSubgroup, ← ha, range_symplecticTransvectionHom_smul ha0]

/-- An element lies in the transvection group along the point of a nonzero vector `v` exactly when
it is a transvection along `v`. -/
@[simp]
theorem mem_transvectionSubgroup_mk {v : Fin (m + m) → K} (hv : v ≠ 0)
    {g : GLSymplecticFin m K} :
    g ∈ transvectionSubgroup (Projectivization.mk K v hv) ↔
      ∃ c : K, symplecticTransvection v c = g := by
  rw [transvectionSubgroup_mk hv, MonoidHom.mem_range]
  simp only [symplecticTransvectionHom_apply]
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ ↦ ⟨Multiplicative.ofAdd c, hc⟩⟩

/-- Each transvection group is abelian, being the image of the additive group of the field. -/
instance (p : ℙ K (Fin (m + m) → K)) : IsMulCommutative (transvectionSubgroup p) :=
  inferInstanceAs (IsMulCommutative (symplecticTransvectionHom p.rep).range)

/-- **Conjugation moves transvection groups along the action**: `T(g p) = g T(p) g⁻¹`. -/
theorem transvectionSubgroup_smul (g : GLSymplecticFin m K) (p : ℙ K (Fin (m + m) → K)) :
    transvectionSubgroup (g • p) = MulAut.conj g • transvectionSubgroup p := by
  induction p using Projectivization.ind with
  | h v hv =>
  ext x
  rw [Subgroup.smul_def, Projectivization.smul_mk, mem_transvectionSubgroup_mk,
    Subgroup.mem_smul_pointwise_iff_exists]
  simp only [mem_transvectionSubgroup_mk, MulAut.smul_def, MulAut.conj_apply, exists_exists_eq_and,
    mul_symplecticTransvection_mul_inv, Units.smul_def, Matrix.smul_eq_mulVec]

/-- **The transvection groups generate the symplectic group over a field.** -/
theorem iSup_transvectionSubgroup :
    ⨆ p : ℙ K (Fin (m + m) → K), transvectionSubgroup p = ⊤ := by
  refine eq_top_of_symplecticTransvection_mem _ fun v c ↦ ?_
  by_cases hv : v = 0
  · rw [hv, symplecticTransvection_zero_left]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_iSup_of_mem (Projectivization.mk K v hv)
      ((mem_transvectionSubgroup_mk hv).mpr ⟨c, rfl⟩)

/-- **The Iwasawa structure of the symplectic group on projective space**: the groups of
symplectic transvections along the points of `ℙ K (Fin (m + m) → K)` are abelian, permuted by
conjugation compatibly with the action, and generate `Sp_{2m}(K)`. -/
noncomputable def iwasawaStructure :
    MulAction.IwasawaStructure (GLSymplecticFin m K) (ℙ K (Fin (m + m) → K)) where
  T := transvectionSubgroup
  is_comm _ := inferInstance
  is_conj := transvectionSubgroup_smul
  is_generator := iSup_transvectionSubgroup

/-- The subgroups of the symplectic Iwasawa structure are the transvection groups. -/
@[simp]
theorem iwasawaStructure_T (p : ℙ K (Fin (m + m) → K)) :
    (iwasawaStructure (m := m)).T p = transvectionSubgroup p :=
  (rfl)

end TauCeti.GLSymplecticFin
