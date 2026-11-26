/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PiCore
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic
import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.NormalPSubgroup

/-!
# Normal `p`-subgroups lie in every defect group

Let `k` be a field of characteristic `p`, `G` a finite group and `Q` a normal `p`-subgroup of
`G`, for instance `O_p(G)` (`TauCeti.piCore {p} G`). Then `Q` lies in every defect group of every
block of `k[G]` (Webb, Corollary 12.3.4, pp. 236–237; Martínez, Corollary 3.9, p. 21, proves
this over an algebraically closed field). The proof avoids vertices.

* A nonzero idempotent `e` of `k[G]` fixed by conjugation by `Q` has `Br_Q(e) ≠ 0`
  (`TauCeti.brauerProjection_ne_zero_of_isPGroup_of_normal`), since otherwise `e` acts as `0` on
  every simple module and so lies in the Jacobson radical.
* A defect group `D` of a block idempotent `e` is minimal with `e ∈ Tr_D^G(k[G]^D)`
  (`TauCeti.isDefectGroup_iff_minimal`), so the `p`-subgroup `Q` with `Br_Q(e) ≠ 0` lies in a
  conjugate of `D` (`TauCeti.exists_le_conj_of_mem_relTraceIdeal`). As `Q` is normal, `Q ≤ D`
  (`TauCeti.IsBlockIdempotent.le_of_isDefectGroup_of_isPGroup_of_normal`).

Normality is needed: for `S₃` at `p = 2`, `⟨(12)⟩` is a `2`-subgroup, but the defect group of the
block `r + r²` is `1`.

## Main results

* `TauCeti.IsDefectGroup.le_of_normal`: a normal `p`-subgroup lies in every defect group of a
  primitive idempotent of `Z(k[G])`.
* `TauCeti.IsBlockIdempotent.le_of_isDefectGroup_of_isPGroup_of_normal`: a normal `p`-subgroup
  lies in every defect group of a block.
* `TauCeti.IsBlockIdempotent.piCore_le_of_isDefectGroup`: `O_p(G)` lies in every defect group of
  a block.
* `TauCeti.IsBlockIdempotent.zpowers_le_of_isDefectGroup_centralizer`: for a `p`-element `x`,
  `⟨x⟩` lies in every defect group of every block of `k[C_G(x)]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Corollary 12.3.4, pp. 236–237.
* A. Martínez, *Modular representation theory of finite groups*, Corollary 3.9, p. 21 (over an
  algebraically closed field).
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]
  {Q : Subgroup G} [Q.Normal]

/-- **A normal `p`-subgroup lies in every defect group.** Let `e` be a primitive idempotent of
`k[G]^G = Z(k[G])`, `k` a field of characteristic `p`. Every normal `p`-subgroup `Q` of `G` lies
in every defect group `D` of `e` (Webb, Corollary 12.3.4, pp. 236–237): `Br_Q(e) ≠ 0` by
`TauCeti.brauerProjection_ne_zero_of_isPGroup_of_normal`, so `Q` lies in a conjugate of `D`, hence
in `D`. -/
theorem IsDefectGroup.le_of_normal {e : conjInvariants k (⊤ : Subgroup G)}
    (he : IsPrimitiveIdempotent e) {D : Subgroup G}
    (hD : IsDefectGroup k p (e : MonoidAlgebra k G) D) (hQ : IsPGroup p Q) : Q ≤ D := by
  have hQe : brauerProjection Q (e : MonoidAlgebra k G) ≠ 0 :=
    brauerProjection_ne_zero_of_isPGroup_of_normal hQ (conjInvariants_anti le_top e.property)
      (he.isIdempotentElem.map (conjInvariants k ⊤).val) (fun h => he.ne_zero (Subtype.ext h))
  obtain ⟨g, hg⟩ :=
    exists_le_conj_of_mem_relTraceIdeal ((isDefectGroup_iff_minimal he).1 hD).prop hQ hQe
  rw [← Subgroup.Normal.conj_smul_eq_self g Q] at hg
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.1 hg

namespace IsBlockIdempotent

variable {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- **A normal `p`-subgroup lies in every defect group of a block** (Webb, Corollary 12.3.4,
pp. 236–237). Let `Q` be a normal `p`-subgroup of a finite group `G` and `k` a field of
characteristic `p`. Then `Q` lies in every defect group of every block idempotent of `k[G]`. -/
theorem le_of_isDefectGroup_of_isPGroup_of_normal (hb : IsBlockIdempotent b) (hQ : IsPGroup p Q)
    {D : Subgroup G} (hD : IsDefectGroup k p (b : MonoidAlgebra k G) D) : Q ≤ D :=
  IsDefectGroup.le_of_normal hb.isPrimitiveIdempotent_conjInvariants hD hQ

/-- **`O_p(G)` lies in every defect group of a block** (Webb, Corollary 12.3.4, pp. 236–237;
Martínez, Corollary 3.9, p. 21, over an algebraically closed field): for a finite group `G` and a
field `k` of characteristic `p`, the `p`-core `O_p(G) = TauCeti.piCore {p} G` lies in every defect
group of every block of `k[G]`. -/
theorem piCore_le_of_isDefectGroup (hb : IsBlockIdempotent b) {D : Subgroup G}
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) D) : piCore {p} G ≤ D :=
  hb.le_of_isDefectGroup_of_isPGroup_of_normal
    ((isPiGroup_singleton_iff Fact.out).1 (isPiGroup_piCore {p} G)) hD

/-- **A central `p`-element lies in every defect group.** If `x` is central in a finite group `G`
and `⟨x⟩` is a `p`-group, then `⟨x⟩`, a normal `p`-subgroup, lies in every defect group of every
block of `k[G]`, `k` a field of characteristic `p`. -/
theorem zpowers_le_of_isDefectGroup (hb : IsBlockIdempotent b) {x : G}
    (hx : x ∈ Subgroup.center G) (hxp : IsPGroup p (Subgroup.zpowers x)) {D : Subgroup G}
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) D) : Subgroup.zpowers x ≤ D :=
  have : (Subgroup.zpowers x).Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le (H := Subgroup.center G)).2 hx)
  hb.le_of_isDefectGroup_of_isPGroup_of_normal hxp hD

/-- **A `p`-element lies in every defect group of every block of its centralizer** (Webb,
Corollary 12.3.4, pp. 236–237): for a `p`-element `x` of a finite group `G` and a field `k` of
characteristic `p`, `⟨x⟩` lies in every defect group of every block of `k[C_G(x)]`. -/
theorem zpowers_le_of_isDefectGroup_centralizer {x : G} (hxp : IsPGroup p (Subgroup.zpowers x))
    {b : Subalgebra.center k (MonoidAlgebra k (Subgroup.centralizer {x}))}
    (hb : IsBlockIdempotent b) {D : Subgroup (Subgroup.centralizer {x})}
    (hD : IsDefectGroup k p (b : MonoidAlgebra k (Subgroup.centralizer {x})) D) :
    Subgroup.zpowers (⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
      Subgroup.centralizer {x}) ≤ D := by
  refine hb.zpowers_le_of_isDefectGroup (Subgroup.mem_center_iff.2 fun g => ?_) ?_ hD
  · exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.property)
  · have hmap : IsPGroup p ((Subgroup.zpowers (⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
        Subgroup.centralizer {x})).map (Subgroup.centralizer {x}).subtype) := by
      rwa [MonoidHom.map_zpowers]
    exact hmap.of_equiv (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).symm

end IsBlockIdempotent

end TauCeti
