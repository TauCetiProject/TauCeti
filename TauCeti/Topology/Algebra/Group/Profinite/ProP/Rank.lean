/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration
public import TauCeti.Topology.Algebra.Group.Profinite.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basis

/-!
# Generator rank and the Frattini quotient

For a topologically finitely generated pro-`p` group, Burnside's basis theorem identifies the
least number of topological generators with the dimension of the Frattini quotient over
`ZMod p`. Consequently the quotient has order `p` raised to the generator rank.

## Main results

* `TauCeti.IsProP.topologicalGeneratorRankNat_eq_finrank_quotient_proPFrattini`: the generator
  rank is the dimension of the Frattini quotient.
* `TauCeti.IsProP.natCard_quotient_proPFrattini`: the Frattini quotient has order `p ^ d(G)`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsProP

/-- For a topologically finitely generated pro-`p` group, the natural-number topological
generator rank is the dimension of its Frattini quotient over `ZMod p`. -/
theorem topologicalGeneratorRankNat_eq_finrank_quotient_proPFrattini
    (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) :
    topologicalGeneratorRankNat G hfg =
      Module.finrank (ZMod p) (Additive (G ⧸ proPFrattini p G)) := by
  classical
  let V := Additive (G ⧸ proPFrattini p G)
  let q : G → V := fun g ↦ Additive.ofMul (QuotientGroup.mk' (proPFrattini p G) g)
  let _ : Finite (G ⧸ proPFrattini p G) := hfg.finite_quotient_proPFrattini p
  let _ : Finite V := inferInstance
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_finite
  apply le_antisymm
  · let b := Module.finBasis (ZMod p) V
    obtain ⟨g, -, hg⟩ := exists_lift_basis_frattiniQuotient_topologicallyGenerates hG b
    let s : Finset G := Finset.univ.image g
    have hs : (s : Set G) = Set.range g := by
      ext x
      simp [s]
    calc
      topologicalGeneratorRankNat G hfg
          ≤ s.card := topologicalGeneratorRankNat_le hfg (by rw [hs]; exact hg)
      _ ≤ Fintype.card (Fin (Module.finrank (ZMod p) V)) := by
        simpa [s] using Finset.card_image_le (s := Finset.univ) (f := g)
      _ = Module.finrank (ZMod p) V := Fintype.card_fin _
  · obtain ⟨s, hs, hgen⟩ := exists_finset_card_eq_topologicalGeneratorRankNat hfg
    have hspan : Submodule.span (ZMod p) (q '' (s : Set G)) = ⊤ := by
      simpa only [q, V] using
        (topologicallyGenerates_iff_frattiniQuotient_span_eq_top hG (s : Set G)).mp hgen
    let t : Finset V := s.image q
    have ht : (t : Set V) = q '' (s : Set G) := by
      ext x
      simp [t]
    calc
      Module.finrank (ZMod p) V
          = Module.finrank (ZMod p) (Submodule.span (ZMod p) (t : Set V)) := by
              rw [ht, hspan]
              simp
      _ ≤ t.card := finrank_span_finset_le_card t
      _ ≤ s.card := by simpa [t] using Finset.card_image_le (s := s) (f := q)
      _ = topologicalGeneratorRankNat G hfg := hs

/-- The Frattini quotient of a topologically finitely generated pro-`p` group has order `p`
raised to the natural-number topological generator rank. -/
theorem natCard_quotient_proPFrattini (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    Nat.card (G ⧸ proPFrattini p G) = p ^ topologicalGeneratorRankNat G hfg := by
  let _ : Finite (G ⧸ proPFrattini p G) := hfg.finite_quotient_proPFrattini p
  calc
    Nat.card (G ⧸ proPFrattini p G) = Nat.card (Additive (G ⧸ proPFrattini p G)) :=
      Nat.card_congr Additive.ofMul
    _ = Nat.card (ZMod p) ^
        Module.finrank (ZMod p) (Additive (G ⧸ proPFrattini p G)) :=
      Module.natCard_eq_pow_finrank
    _ = p ^ topologicalGeneratorRankNat G hfg := by
      rw [Nat.card_zmod, hG.topologicalGeneratorRankNat_eq_finrank_quotient_proPFrattini hfg]

end IsProP

end TauCeti
