/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm

/-!
# The norm-one idele class group

The idele norm `‖·‖ : 𝕀_K → ℝ>0` of a number field `K` is trivial on the principal ideles by the
product formula, so it descends to a continuous surjective homomorphism
`ideleClassNorm : C_K → ℝ>0` on the idele class group `C_K = 𝕀_K / Kˣ`.  Its kernel is the
**norm-one idele class group** `C_K¹`, a closed subgroup of `C_K`.

The full idele class group is not compact, since it surjects continuously onto the positive reals,
and `C_K¹` is a proper subgroup.  The norm-one subgroup is the carrier of the compactness theorem
for `C_K¹`, the adelic form of the finiteness of the class group and Dirichlet's unit theorem.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleClassNorm`: the idele norm on the idele class group.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.normOne`: the norm-one idele class group, the kernel
  of `ideleClassNorm`.

## Main results

* `TauCeti.GlobalNumberFields.ideleClassNorm_mk`: the norm of the class of an idele is its idele
  norm.
* `TauCeti.GlobalNumberFields.continuous_ideleClassNorm`: the idele class norm is continuous.
* `TauCeti.GlobalNumberFields.ideleClassNorm_surjective`: the idele class norm is surjective.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.isClosed_normOne`: the norm-one idele class group is
  closed.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.comap_normOne`: the ideles whose class has norm one
  are exactly the ideles of norm one.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The idele norm on the idele class group of a number field: the idele norm descends along the
quotient by the principal ideles, on which it is trivial by the product formula. -/
def ideleClassNorm : IdeleClassGroup (𝓞 K) K →* ℝ≥0ˣ :=
  QuotientGroup.lift _ ideleNorm principalSubgroup_le_ker_ideleNorm

/-- The idele class norm of the class of an idele is its idele norm. -/
@[simp]
theorem ideleClassNorm_mk (x : IdeleGroup (𝓞 K) K) :
    ideleClassNorm (x : IdeleClassGroup (𝓞 K) K) = ideleNorm x :=
  (rfl)

/-- The idele class norm is continuous. -/
theorem continuous_ideleClassNorm : Continuous (ideleClassNorm (K := K)) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_ideleNorm (K := K))

/-- The idele class norm is surjective. -/
theorem ideleClassNorm_surjective : Function.Surjective (ideleClassNorm (K := K)) :=
  QuotientGroup.lift_surjective_of_surjective _ _ ideleNorm_surjective _

namespace IdeleClassGroup

variable (K) in
/-- The **norm-one idele class group** `C_K¹` of a number field: the classes of ideles of idele
norm one. -/
def normOne : Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (ideleClassNorm (K := K)).ker

/-- An idele class lies in the norm-one subgroup exactly when its idele class norm is `1`. -/
theorem mem_normOne_iff {x : IdeleClassGroup (𝓞 K) K} : x ∈ normOne K ↔ ideleClassNorm x = 1 :=
  MonoidHom.mem_ker

/-- The class of an idele lies in the norm-one subgroup exactly when the idele has norm `1`. -/
@[simp]
theorem mk_mem_normOne_iff {x : IdeleGroup (𝓞 K) K} :
    (x : IdeleClassGroup (𝓞 K) K) ∈ normOne K ↔ ideleNorm x = 1 :=
  MonoidHom.mem_ker

variable (K)

/-- The preimage of the norm-one idele class group in the idele group is the kernel of the idele
norm. -/
theorem comap_normOne :
    (normOne K).comap (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) =
      (ideleNorm (K := K)).ker := by
  ext x
  simp

/-- The norm-one idele class group is the image of the norm-one ideles under the quotient map. -/
theorem map_ker_ideleNorm :
    (ideleNorm (K := K)).ker.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) =
      normOne K := by
  rw [← comap_normOne, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- The norm-one idele class group is closed in the idele class group. -/
theorem isClosed_normOne : IsClosed (normOne K : Set (IdeleClassGroup (𝓞 K) K)) :=
  isClosed_singleton.preimage continuous_ideleClassNorm

/-- The norm-one idele class group is a proper subgroup: the idele class norm is surjective onto
the nontrivial group `ℝ>0`. -/
theorem normOne_ne_top : normOne K ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := ideleClassNorm_surjective (K := K) (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  have hx1 : ideleClassNorm x = 1 := mem_normOne_iff.mp (h ▸ Subgroup.mem_top x)
  rw [hx1] at hx
  have := congrArg (fun u : ℝ≥0ˣ ↦ (u : ℝ≥0)) hx
  norm_num at this

end IdeleClassGroup

end TauCeti.GlobalNumberFields
