/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Exact
public import TauCeti.Algebra.MonoidAlgebra.Etale
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Connected–étale sequences for finite diagonalizable groups

Let `G` be a finite abelian character group over a field. There is a subgroup `S ≤ G`
for which the sequence

```text
1 → D(G / S) → D(G) → D(S) → 1
```

is short exact, `D(G / S)` is geometrically connected, and `D(S)` is finite étale.
The coordinate maps are induced by the subgroup inclusion and the quotient map.
Finiteness of all three group schemes follows from finiteness of their character groups.

In prime characteristic `p`, the proof chooses a complement to the Sylow `p`-subgroup using
Mathlib's Schur–Zassenhaus theorem. The complement has order prime to `p`, while its quotient
is a `p`-group. In characteristic zero, take `S = G`. No perfectness assumption on the base
field is needed.
-/

public section

namespace TauCeti.DiagonalizableGroup

universe u v

variable (k : Type u) [Field k]

/-- Every finite diagonalizable group over a field has a connected–étale sequence.
The witness `S` is a subgroup of the character group: the quotient `D(S)` is étale and the
kernel `D(G / S)` is geometrically connected. -/
theorem exists_connected_etale_sequence (G : Type v) [CommGroup G] [Finite G] :
    ∃ S : Subgroup G,
      CommHopfAlgCat.IsShortExact
        (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k S.subtype))
        (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k (QuotientGroup.mk' S))) ∧
      geometricallyConnectedCommHopfAlgProperty k
        (CommHopfAlgCat.of k (MonoidAlgebra k (G ⧸ S))) ∧
      Algebra.Etale k (MonoidAlgebra k S) := by
  classical
  obtain ⟨p, hp⟩ := ExpChar.exists k
  let := hp
  suffices ∃ S : Subgroup G, IsPGroup p (G ⧸ S) ∧ IsUnit (Nat.card S : k) by
    obtain ⟨S, hconnected, hetale⟩ := this
    refine ⟨S, ?_, geometricallyConnected_of_isPGroup k p hconnected,
      TauCeti.MonoidAlgebra.etale_of_isUnit_card k S hetale⟩
    exact isShortExact_mapDomainBialgHom k S.subtype (QuotientGroup.mk' S)
      Subtype.coe_injective (QuotientGroup.mk'_surjective S)
      (by simp only [Subgroup.range_subtype, QuotientGroup.ker_mk'])
  cases hp with
  | zero =>
    refine ⟨⊤, isPGroup_one_iff_subsingleton.mpr QuotientGroup.subsingleton_quotient_top, ?_⟩
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  | prime hprime =>
    let : Fact p.Prime := ⟨hprime⟩
    let P : Sylow p G := default
    obtain ⟨S, hS⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
    refine ⟨S, P.isPGroup'.of_equiv hS.QuotientMulEquiv.symm, ?_⟩
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply P.not_dvd_index
    rw [hS.symm.index_eq_card]
    exact (CharP.cast_eq_zero_iff k p _).mp hzero

end TauCeti.DiagonalizableGroup
