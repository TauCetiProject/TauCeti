/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Perfect
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Primitive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Projective

/-!
# Simplicity of the projective symplectic groups

The projective symplectic group `PSp_{2m}(K)` is the quotient of the standard symplectic group
`Sp_{2m}(K)` (`TauCeti.GLSymplecticFin m K`) by its centre. This file proves Iwasawa's theorem
for it: in positive rank, `PSp_{2m}(K)` is simple as soon as `Sp_{2m}(K)` is perfect.

The inputs are the action of `Sp_{2m}(K)` on the projective space `ℙ K (Fin (m + m) → K)`: it is
primitive (`TauCeti.GLSymplecticFin.isPreprimitive`), its kernel is the centre
(`TauCeti.GLSymplecticFin.forall_projective_smul_eq_iff_mem_center`), and the groups of symplectic
transvections along the points form an Iwasawa structure
(`TauCeti.GLSymplecticFin.iwasawaStructure`). When `Sp_{2m}(K)` is perfect, the generic
central-quotient criterion `MulAction.IwasawaStructure.isSimpleGroup_quotient_center` then shows
that the quotient by the centre is simple. The group is nontrivial in positive rank because its
central quotient is (`TauCeti.GLSymplecticFin.instNontrivialQuotientCenter`).

Combined with the perfectness results of `Symplectic/Perfect`, this gives the classical cases:
`PSp_{2m}(K)` is simple for `m ≥ 2` unless `m = 2` and `K = 𝔽₂`, and `PSp₂(K) = PSL₂(K)` is
simple over a field with a nonzero element whose square is not one.

## Main results

* `TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center`: `PSp_{2m}(K)` is simple when
  `Sp_{2m}(K)` is perfect and `m ≠ 0`.
* `TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center_of_two_le` and
  `TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center_of_sq_ne_one`: the classical cases.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* E. Artin, *Geometric Algebra* (1957), Chapter III, §§4--6, and Chapter IV, §1.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.GLSymplecticFin

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- **Iwasawa's theorem for the projective symplectic group.** In positive rank, the quotient
`PSp_{2m}(K)` of the symplectic group by its centre is simple as soon as `Sp_{2m}(K)` is
perfect. -/
theorem isSimpleGroup_quotient_center [NeZero m] (h : commutator (GLSymplecticFin m K) = ⊤) :
    IsSimpleGroup (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) :=
  have : Group.IsPerfect (GLSymplecticFin m K) := ⟨h⟩
  have : Nontrivial (GLSymplecticFin m K) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (GLSymplecticFin m K))).nontrivial
  iwasawaStructure.isSimpleGroup_quotient_center fun g hg ↦
    (forall_projective_smul_eq_iff_mem_center g).mp hg

/-- **`PSp_{2m}(K)` is simple for `m ≥ 2` unless `m = 2` and `K = 𝔽₂`.** The second hypothesis
says that the rank is at least three or the field has an element other than `0` and `1`. -/
theorem isSimpleGroup_quotient_center_of_two_le (hm : 2 ≤ m)
    (hK : 3 ≤ m ∨ ∃ a : K, a ≠ 0 ∧ a ≠ 1) :
    IsSimpleGroup (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) :=
  have : NeZero m := ⟨by omega⟩
  isSimpleGroup_quotient_center (commutator_eq_top_of_two_le hm hK)

/-- **`PSp_{2m}(K)` is simple in every positive rank** over a field with a nonzero element whose
square is not one, for example a field with at least four elements. -/
theorem isSimpleGroup_quotient_center_of_sq_ne_one [NeZero m] {a : K} (ha : a ≠ 0)
    (hasq : a ^ 2 ≠ 1) :
    IsSimpleGroup (GLSymplecticFin m K ⧸ Subgroup.center (GLSymplecticFin m K)) :=
  isSimpleGroup_quotient_center (commutator_eq_top ha hasq)

end TauCeti.GLSymplecticFin
