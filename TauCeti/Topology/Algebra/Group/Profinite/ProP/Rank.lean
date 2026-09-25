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

Counting orders through this identifies when a continuous surjection `f : G ↠ H` of pro-`p`
groups preserves the rank: the preimage `Φ(G) ⊔ ker f` of `Φ(H)` has index `p ^ d(H)` in `G`,
while `Φ(G)` has index `p ^ d(G)`, so `d(H) = d(G)` holds exactly when `ker f ≤ Φ(G)`.

## Main results

* `TauCeti.IsProP.topologicalGeneratorRankNat_eq_finrank_quotient_proPFrattini`: the generator
  rank is the dimension of the Frattini quotient.
* `TauCeti.IsProP.natCard_quotient_proPFrattini`: the Frattini quotient has order `p ^ d(G)`.
* `TauCeti.IsProP.topologicalGeneratorRank_quotient_proPFrattini`: a pro-`p` group and its
  Frattini quotient have the same cardinal topological generator rank.
* `TauCeti.IsProP.index_proPFrattini_sup_ker`: along a continuous surjection `f : G ↠ H` onto a
  topologically finitely generated pro-`p` group, `Φ(G) ⊔ ker f` has index `p ^ d(H)`.
* `TauCeti.IsProP.topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini`: for a continuous
  surjection `f : G ↠ H` of pro-`p` groups with `G` topologically finitely generated,
  `d(H) = d(G)` exactly when `ker f ≤ Φ(G)`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

open scoped Cardinal

universe u v

variable {p : ℕ} [hp : Fact p.Prime]
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

/-- **A profinite pro-`p` group and its Frattini quotient have the same topological generator
rank.** Generation passes to the quotient; conversely a generating set of the quotient converging
to `1` has a set of representatives converging to `1`, which generates `G` by Burnside's basis
theorem. -/
theorem topologicalGeneratorRank_quotient_proPFrattini (hG : IsProP p G) :
    topologicalGeneratorRank (G ⧸ proPFrattini p G) = topologicalGeneratorRank G := by
  refine le_antisymm (topologicalGeneratorRank_quotient_le _) ?_
  obtain ⟨s, hs, hgen, hcard⟩ :=
    exists_convergesToOne_mk_eq_topologicalGeneratorRank (G ⧸ proPFrattini p G)
  obtain ⟨t, ht, htimage⟩ :=
    (proPFrattini p G).exists_convergesToOne_lift_quotient isClosed_proPFrattini hs
  -- Thin the representatives out to one per element of `s`, so that they are no more numerous.
  obtain ⟨t', ht'sub, ht'bij⟩ := Set.exists_subset_bijOn t (QuotientGroup.mk' (proPFrattini p G))
  rw [htimage] at ht'bij
  calc
    topologicalGeneratorRank G ≤ #(t' : Set G) :=
      topologicalGeneratorRank_le (ht.mono ht'sub)
        ((topologicallyGenerates_iff_frattiniQuotient hG t').mpr
          (by rw [ht'bij.image_eq]; exact hgen))
    _ = #(s : Set (G ⧸ proPFrattini p G)) := Cardinal.mk_congr (ht'bij.equiv _)
    _ = topologicalGeneratorRank (G ⧸ proPFrattini p G) := hcard

section Surjective

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

omit [TotallyDisconnectedSpace G] in
/-- Along a continuous surjection `f : G ↠ H` from a compact group onto a topologically finitely
generated profinite pro-`p` group, the subgroup `Φ(G) ⊔ ker f`, the preimage of the Frattini
subgroup of `H`, has index `p ^ d(H)` in `G`. -/
theorem index_proPFrattini_sup_ker (hH : IsProP p H) (hfg : IsTopologicallyFinitelyGenerated H)
    (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    (proPFrattini p G ⊔ f.ker).index = p ^ topologicalGeneratorRankNat H hfg := by
  rw [← comap_proPFrattini_eq_of_surjective hp.out f hf hsurj,
    Subgroup.index_comap_of_surjective _ hsurj, Subgroup.index_eq_card,
    hH.natCard_quotient_proPFrattini hfg]

/-- **Rank preservation along a surjection.** For a continuous surjection `f : G ↠ H` of profinite
pro-`p` groups with `G` topologically finitely generated, the topological generator rank of `H`
equals that of `G` exactly when the kernel of `f` lies in the Frattini subgroup of `G`. The
inequality `d(H) ≤ d(G)` is `TauCeti.topologicalGeneratorRankNat_le_of_surjective`. -/
theorem topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    topologicalGeneratorRankNat H (hfg.of_surjective hf hsurj) =
        topologicalGeneratorRankNat G hfg ↔
      f.ker ≤ proPFrattini p G := by
  -- Both `Φ(G)` and `Φ(G) ⊔ ker f` have index a power of `p`, and the exponents are the two ranks.
  have hidx := index_proPFrattini_sup_ker (hG.of_surjective f hf hsurj)
    (hfg.of_surjective hf hsurj) f hf hsurj
  have hΦ : (proPFrattini p G).index = p ^ topologicalGeneratorRankNat G hfg := by
    rw [Subgroup.index_eq_card, hG.natCard_quotient_proPFrattini hfg]
  constructor
  · intro heq
    -- Equal ranks force the relative index of `Φ(G)` in `Φ(G) ⊔ ker f` to be `1`.
    have hmul := Subgroup.relIndex_mul_index
      (le_sup_left : proPFrattini p G ≤ proPFrattini p G ⊔ f.ker)
    rw [hidx, hΦ, heq] at hmul
    have hone : (proPFrattini p G).relIndex (proPFrattini p G ⊔ f.ker) = 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos _) (by rw [hmul, one_mul])
    exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)
  · intro hle
    rw [sup_eq_left.mpr hle, hΦ] at hidx
    exact (Nat.pow_right_injective hp.out.two_le hidx).symm

end Surjective

end IsProP

end TauCeti
