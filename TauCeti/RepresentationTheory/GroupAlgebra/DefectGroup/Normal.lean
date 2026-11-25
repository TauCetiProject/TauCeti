/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PiCore
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic
import TauCeti.RepresentationTheory.PGroupInvariants
import TauCeti.RingTheory.Idempotents.Jacobson

/-!
# Normal `p`-subgroups lie in every defect group

Let `k` be a field of characteristic `p` and `G` a finite group. A normal `p`-subgroup `Q` of `G`
is contained in every defect group of every block of `k[G]` (Webb, Corollary 12.3.4,
pp. 236–237; Martínez, Corollary 3.9, p. 21). In particular the `p`-core `O_p(G)` lies in every
defect group, and for an element `x` of `p`-power order the cyclic group `⟨x⟩` lies in every
defect group of every block of the centralizer `C_G(x)`, where it is a central `p`-subgroup.

The proof uses no vertices. `Q` acts trivially on every simple `k[G]`-module
(`IsPGroup.of_smul_eq_self_of_isSimpleModule`), so an element `e ∈ k[G]^Q` acts on every simple
module as its Brauer projection `Br_Q(e)`
(`TauCeti.smul_eq_mapDomainRingHom_brauerProjection_smul`). If `Br_Q(e) = 0`, then `e` kills every
simple module and lies in the Jacobson radical, so `e = 0` when `e` is idempotent
(`TauCeti.brauerProjection_ne_zero_of_normal`). For a block idempotent `e`, `Q` then lies in a
conjugate of a defect group `D`, since `e` is a trace from `D`
(`TauCeti.exists_le_conj_of_mem_relTraceIdeal`), and so in `D` by normality.

## Main results

* `TauCeti.brauerProjection_ne_zero_of_normal`: a nonzero idempotent of `k[G]^Q`, for `Q` a normal
  `p`-subgroup, has nonzero Brauer projection at `Q`.
* `TauCeti.IsDefectGroup.le_of_normal`, `TauCeti.IsBlockIdempotent.le_of_isDefectGroup_of_normal`:
  a normal `p`-subgroup lies in every defect group of a primitive idempotent of `Z(k[G])`, in
  particular of a block idempotent.
* `TauCeti.IsBlockIdempotent.piCore_le_of_isDefectGroup`: `O_p(G)` lies in every defect group of
  every block.
* `TauCeti.IsBlockIdempotent.zpowers_le_of_isDefectGroup`: for `x` of `p`-power order, `⟨x⟩` lies in
  every defect group of every block of `k[C_G(x)]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Corollary 12.3.4, pp. 236–237.
* A. Martínez, *Modular representation theory of finite groups*, Corollary 3.9, p. 21.
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **The Brauer projection at a normal `p`-subgroup is faithful on idempotents.** Let `Q` be a
normal `p`-subgroup of a finite group `G` and `k` a field of characteristic `p`. A nonzero
idempotent `e` of `k[G]` fixed by conjugation by `Q` has `Br_Q(e) ≠ 0`: since `Q` acts trivially
on every simple `k[G]`-module, `e` acts there as `Br_Q(e)`, and an idempotent killing every simple
module lies in the Jacobson radical, so it is zero. -/
theorem brauerProjection_ne_zero_of_normal {Q : Subgroup G} [Q.Normal] (hQ : IsPGroup p Q)
    {e : MonoidAlgebra k G} (he : IsIdempotentElem e) (he0 : e ≠ 0)
    (heQ : e ∈ conjInvariants k Q) : brauerProjection Q e ≠ 0 := by
  intro h0
  refine he0 (he.eq_zero_of_mem_jacobson ?_)
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
  intro 𝔪 h𝔪
  -- `e` acts as `Br_Q(e) = 0` on the simple module `k[G] ⧸ 𝔪`, so it kills the class of `1`.
  have : IsSimpleModule (MonoidAlgebra k G) (MonoidAlgebra k G ⧸ 𝔪) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 h𝔪)
  have h := smul_eq_mapDomainRingHom_brauerProjection_smul hQ heQ
    (fun g hg m => hQ.of_smul_eq_self_of_isSimpleModule _ hg m)
    (Submodule.Quotient.mk (1 : MonoidAlgebra k G) : MonoidAlgebra k G ⧸ 𝔪)
  rwa [h0, map_zero, zero_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
    Submodule.Quotient.mk_eq_zero] at h

/-- **A normal `p`-subgroup lies in every defect group.** Let `e` be a primitive idempotent of
`k[G]^G = Z(k[G])`, `k` a field of characteristic `p`. Every normal `p`-subgroup `Q` of `G` lies
in every defect group `D` of `e` (Webb, Corollary 12.3.4, pp. 236–237): `Br_Q(e) ≠ 0` by
`TauCeti.brauerProjection_ne_zero_of_normal`, so `Q` lies in a conjugate of `D`, hence in `D`. -/
theorem IsDefectGroup.le_of_normal {e : conjInvariants k (⊤ : Subgroup G)}
    (he : IsPrimitiveIdempotent e) {D : Subgroup G}
    (hD : IsDefectGroup k p (e : MonoidAlgebra k G) D) {Q : Subgroup G} [Q.Normal]
    (hQ : IsPGroup p Q) : Q ≤ D := by
  have hQe : brauerProjection Q (e : MonoidAlgebra k G) ≠ 0 :=
    brauerProjection_ne_zero_of_normal hQ (he.isIdempotentElem.map (conjInvariants k ⊤).val)
      (fun h => he.ne_zero (Subtype.ext h)) (conjInvariants_anti le_top e.property)
  obtain ⟨g, hg⟩ :=
    exists_le_conj_of_mem_relTraceIdeal ((isDefectGroup_iff_minimal he).1 hD).prop hQ hQe
  rw [← Subgroup.Normal.conj_smul_eq_self g Q] at hg
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.1 hg

namespace IsBlockIdempotent

variable {b : Subalgebra.center k (MonoidAlgebra k G)} {D : Subgroup G}

/-- **A normal `p`-subgroup lies in every defect group of a block.** For a block idempotent `e_B`
of `k[G]`, `k` a field of characteristic `p`, every normal `p`-subgroup of `G` lies in every
defect group of `e_B` (Webb, Corollary 12.3.4, pp. 236–237). -/
theorem le_of_isDefectGroup_of_normal (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) D) {Q : Subgroup G} [Q.Normal]
    (hQ : IsPGroup p Q) : Q ≤ D :=
  IsDefectGroup.le_of_normal hb.isPrimitiveIdempotent_conjInvariants hD hQ

/-- **`O_p(G)` lies in every defect group.** For a block idempotent `e_B` of `k[G]`, `k` a field
of characteristic `p`, the `p`-core `O_p(G)` lies in every defect group of `e_B` (Webb,
Corollary 12.3.4, pp. 236–237; Martínez, Corollary 3.9, p. 21). -/
theorem piCore_le_of_isDefectGroup (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) D) : piCore {p} G ≤ D :=
  hb.le_of_isDefectGroup_of_normal hD
    ((isPiGroup_singleton_iff (Fact.out : p.Prime)).1 (isPiGroup_piCore {p} G))

/-- **`⟨x⟩` lies in every defect group of a block of `C_G(x)`.** For `x ∈ G` of `p`-power order
and a block idempotent `e_b` of `k[C_G(x)]`, `k` a field of characteristic `p`, the cyclic group
generated by `x`, a central `p`-subgroup of `C_G(x)`, lies in every defect group of `e_b`. -/
theorem zpowers_le_of_isDefectGroup {x : G} {n : ℕ} (hx : orderOf x = p ^ n)
    {b : Subalgebra.center k (MonoidAlgebra k (Subgroup.centralizer {x}))}
    (hb : IsBlockIdempotent b) {D : Subgroup (Subgroup.centralizer {x})}
    (hD : IsDefectGroup k p (b : MonoidAlgebra k (Subgroup.centralizer {x})) D) :
    Subgroup.zpowers ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ ≤ D := by
  have : (Subgroup.zpowers
      (⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : Subgroup.centralizer {x})).Normal :=
    Subgroup.normal_of_le_center <| (Subgroup.zpowers_le).2 <| Subgroup.mem_center_iff.2
      fun y => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.property)
  exact hb.le_of_isDefectGroup_of_normal hD
    (IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx]))

end IsBlockIdempotent

end TauCeti
