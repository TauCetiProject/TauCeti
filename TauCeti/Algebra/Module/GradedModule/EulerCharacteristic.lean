/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import TauCeti.Algebra.Module.GradedModule.Homology

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.LinearAlgebra.Dimension.RankNullity

/-!
# Euler characteristics of the homology of a homogeneous square-zero endomorphism

Let `G` be an internal grading, indexed by an additive group `ι`, of a finitely generated module
`V` over a Noetherian ring `K` with the rank-nullity property, such as a field or `ℤ`. Let `d` be a
square-zero endomorphism of `V` which is homogeneous of degree `r`. Its homology `ker d ⧸ im d`
inherits the grading `G.homology` (`TauCeti.Algebra.Module.GradedModule.Homology`). This file
proves the Euler–Poincaré principle for it: for every weight `w : ι → A`, with values in an
additive group, which changes sign under a shift by the degree of `d`, `w (p + r) = -w p`,

`∑ₚ rank (H_p) • w p = ∑ₚ rank (V_p) • w p`.

Over `ℤ`, ranks forget torsion, so the identity also holds there.

The proof counts in each degree. Write `Z_p` for the cycles and `B_p` for the boundaries of
degree `p`. Rank-nullity for `d` on `V_p` gives `rank V_p = rank Z_p + rank B_(p + r)`, since `d`
carries `V_p` onto `B_(p + r)` (`LinearMap.IsHomogeneous.map_piece_eq_inf_range`), and for
the quotient map from cycles to homology it gives `rank Z_p = rank H_p + rank B_p`. Summed with
the weights, the two families of boundary terms cancel after the shift `p ↦ p + r`.

The typical weights are `(-1) ^ p` for a grading by `ℤ` and a differential of degree `±1`, the
usual Euler characteristic, and `(-1) ^ m T ^ a` for a bigrading by `ℤ × ℤ` and a differential of
bidegree `(-1, 0)`, the graded Euler characteristic of a bigraded complex such as hat knot Floer
homology.

## Main results

* `TauCeti.InternalGrading.finrank_piece_eq_finrank_homology_piece_add`: in each degree, the rank
  of the piece is the rank of the homology plus the ranks of the boundaries in that degree and in
  the degree `r` above.
* `TauCeti.InternalGrading.finsum_finrank_homology_piece_smul`: the weighted Euler–Poincaré
  identity.
-/

public section

open Module DirectSum

namespace TauCeti.InternalGrading

universe v

variable {ι : Type*} [DecidableEq ι] {K : Type*} {V : Type v} [Ring K] [AddCommGroup V]
  [Module K V]

section AddRightCancelMonoid

variable [AddRightCancelMonoid ι] (G : InternalGrading K V ι) {d : V →ₗ[K] V} {r : ι}
  (hhom : LinearMap.IsHomogeneous d G.piece G.piece r)

variable (hd : d ∘ₗ d = 0)

include hd in
/-- The degree-`p` boundaries of `d`, viewed in `V`, are the elements of degree `p` in its
image. -/
private theorem map_subtype_ker_piece_inf_boundariesInKer (p : ι) :
    ((G.ker hhom).piece p ⊓ d.boundariesInKer).map (LinearMap.ker d).subtype =
      G.piece p ⊓ LinearMap.range d := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, mem_ker_piece,
    LinearMap.mem_boundariesInKer]
  refine ⟨fun ⟨z, ⟨hz, hb⟩, hzx⟩ ↦ hzx ▸ ⟨hz, hb⟩, fun ⟨hx, hr⟩ ↦ ⟨⟨x, ?_⟩, ⟨hx, hr⟩, rfl⟩⟩
  obtain ⟨y, rfl⟩ := hr
  exact LinearMap.congr_fun hd y

variable [IsNoetherianRing K] [HasRankNullity.{v} K] [StrongRankCondition K] [Module.Finite K V]

/-- **The rank of a piece in terms of homology and boundaries.** In each degree `p`, the rank of
the piece `V_p` is the rank of the homology `H_p` plus the ranks of the boundaries of degree `p`
and of degree `p + r`. -/
theorem finrank_piece_eq_finrank_homology_piece_add (p : ι) :
    finrank K (G.piece p) = finrank K ((G.homology hhom hd).piece p) +
      finrank K ↥(G.piece p ⊓ LinearMap.range d) +
      finrank K ↥(G.piece (p + r) ⊓ LinearMap.range d) := by
  -- Rank-nullity for `d` on `V_p`, whose image is `B_(p + r)` and whose kernel is `Z_p`.
  have hV := d.finrank_map_add_finrank_inf_ker (G.piece p)
  rw [hhom.map_piece_eq_inf_range] at hV
  -- Rank-nullity for the quotient map from cycles to homology on the cycles `Z_p` of degree `p`,
  -- whose image is `H_p` and whose kernel is `B_p`.
  have hZ := (d.homologyπ hd).finrank_map_add_finrank_inf_ker ((G.ker hhom).piece p)
  have hH : ((G.ker hhom).piece p).map (d.homologyπ hd) = (G.homology hhom hd).piece p := by
    ext y
    simp only [Submodule.mem_map, mem_ker_piece, G.mem_homology_piece_iff hhom hd]
  have hker : LinearMap.ker (d.homologyπ hd) = d.boundariesInKer := by
    ext z
    rw [LinearMap.mem_ker, LinearMap.homologyπ_eq_zero_iff, LinearMap.mem_boundariesInKer]
  rw [hH, hker, ← Submodule.finrank_map_subtype_eq (LinearMap.ker d) ((G.ker hhom).piece p),
    G.map_subtype_ker_piece hhom, ← Submodule.finrank_map_subtype_eq _ (_ ⊓ _),
    map_subtype_ker_piece_inf_boundariesInKer G hhom hd] at hZ
  omega

end AddRightCancelMonoid

section AddCommGroup

variable [AddCommGroup ι] {A : Type*} [AddCommGroup A]

variable [IsNoetherianRing K] [HasRankNullity.{v} K] [StrongRankCondition K]
  [Module.Finite K V] (G : InternalGrading K V ι) {d : V →ₗ[K] V} {r : ι}
  (hhom : LinearMap.IsHomogeneous d G.piece G.piece r) (hd : d ∘ₗ d = 0)

omit [AddCommGroup ι] [IsNoetherianRing K] [StrongRankCondition K] in
/-- A family of natural numbers bounded by the ranks of the pieces of a finitely generated graded
module has finite support. -/
private theorem finite_support_of_le_finrank {f : ι → ℕ} (hf : ∀ p, f p ≤ finrank K (G.piece p)) :
    (Function.support f).Finite :=
  G.finite_piece_ne_bot.subset fun p hp hbot ↦
    hp (Nat.le_zero.mp ((hf p).trans (by rw [hbot, finrank_bot])))

/-- **Euler–Poincaré for a homogeneous square-zero endomorphism.** For a weight `w` changing sign
under the shift by the degree `r` of `d`, the weighted sum of the ranks of the homogeneous pieces
of the homology equals that of the pieces of the module. -/
theorem finsum_finrank_homology_piece_smul {w : ι → A} (hw : ∀ p, w (p + r) = -w p) :
    ∑ᶠ p, finrank K ((G.homology hhom hd).piece p) • w p = ∑ᶠ p, finrank K (G.piece p) • w p := by
  have hrank := G.finrank_piece_eq_finrank_homology_piece_add hhom hd
  -- Name the ranks of the homology and of the boundaries, so that they can be shifted.
  obtain ⟨h, hh⟩ : ∃ h : ι → ℕ, ∀ p, finrank K ((G.homology hhom hd).piece p) = h p :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ι → ℕ, ∀ p, finrank K ↥(G.piece p ⊓ LinearMap.range d) = b p :=
    ⟨_, fun _ ↦ rfl⟩
  simp only [hh, hb] at hrank ⊢
  have hhfin := G.finite_support_of_le_finrank (f := h) fun p ↦ by have := hrank p; omega
  have hbfin := G.finite_support_of_le_finrank (f := b) fun p ↦ by have := hrank p; omega
  have hfin : ∀ {f : ι → ℕ}, (Function.support f).Finite → ∀ u : ι → A,
      Function.HasFiniteSupport fun p ↦ f p • u p := fun hf u ↦
    hf.subset fun p hp h0 ↦ hp (by simp [h0])
  have hbr : (Function.support fun p ↦ b (p + r)).Finite :=
    (hbfin.preimage (add_left_injective r).injOn).subset fun _ hp ↦ hp
  simp only [hrank, add_smul]
  rw [finsum_add_distrib (((hfin hhfin w).union (hfin hbfin w)).subset (Function.support_add _ _))
      (hfin hbr _), finsum_add_distrib (hfin hhfin _) (hfin hbfin _), add_assoc,
    finsum_smul_add_finsum_comp_add_right_smul_eq_zero hbfin hw, add_zero]

end AddCommGroup

end TauCeti.InternalGrading
