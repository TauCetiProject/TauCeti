/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.ProjectiveCorrespondence
public import TauCeti.RepresentationTheory.Induction.Clifford.Surjectivity
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Degree

/-!
# The degree ratio over a normal subgroup divides the index

Let `N` be a normal subgroup of a finite group `G`, let `k` be an algebraically closed field of
characteristic zero, and let `W` be an irreducible representation of `G` lying over an irreducible
representation `V` of `N`. Then `dim V` divides `dim W`, and the ratio `dim W / dim V` divides the
index `|G : N|` (Isaacs, Corollary 11.29): in characters, `θ(1) ∣ χ(1)` and
`χ(1)/θ(1) ∣ |G : N|` for `χ ∈ Irr(G)` and an irreducible constituent `θ` of `χ|_N`.

The proof follows Reynolds (1963), proof of Theorem 8. With `T` the inertia group of `V`, the
Clifford correspondence writes `W` as induced from an irreducible representation `U` of `T` lying
over `V` (`FDRep.exists_simple_liesOver_inertia_nonempty_iso_indFDRep`), so
`dim W = |G : T| dim U`. A projective extension of `V` to `T` compatible with `N` exists
(`TauCeti.exists_isProjectiveInertiaExtension`), and `U` is the tensor product of `V` with the
multiplicity space `M = Hom_N(V, U)` (`TauCeti.IsProjectiveInertiaExtension.tensorRepEquiv`), so
`dim U = dim V · dim M`. The space `M` carries an irreducible projective representation of `T/N`
(`TauCeti.IsProjectiveInertiaExtension.eq_bot_or_eq_top_of_homAction_mem`), so `dim M` divides
`|T : N|` by Schur's theorem (`TauCeti.IsProjectiveRep.finrank_dvd_card`). The ratio is
`|G : T| dim M`, which divides `|G : T| |T : N| = |G : N|`.

The ratio need not be the index of the inertia group: for `G = Q₈`, `N = Z(Q₈)` and `V` faithful,
`V` is invariant, `T = G`, and the ratio is `2 = dim M`.

## Main results

* `FDRep.exists_finrank_eq_mul_dvd_relIndex_of_liesOver_inertia`: for an irreducible
  representation `U` of the inertia group lying over `V`, `dim U = dim V · m` with `m ∣ |T : N|`
  (`N.relIndex T`).
* `FDRep.exists_finrank_eq_mul_dvd_index_of_liesOver`: for an irreducible representation `W` of
  `G` lying over `V`, `dim W = dim V · m` with `m ∣ |G : N|`.
* `FDRep.finrank_dvd_finrank_and_finrank_div_finrank_dvd_index_of_liesOver`: `dim V ∣ dim W`
  and `dim W / dim V ∣ |G : N|`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 11,
  Corollary 11.29.
* W. F. Reynolds, *Blocks and normal subgroups of finite groups*, Nagoya Math. J. 22 (1963),
  15–32, proof of Theorem 8, p. 30.
-/

public section

open CategoryTheory Module TensorProduct

namespace FDRep

open TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {N : Subgroup G} [N.Normal]

/-- **The degree ratio over the inertia group.** Let `V` be an irreducible representation of a
normal subgroup `N` of a finite group, over an algebraically closed field of characteristic zero,
and let `U` be an irreducible representation of the inertia group `T` of `V` lying over `V`. Then
`dim U = dim V · m` for some `m` dividing `|T : N|`. -/
theorem exists_finrank_eq_mul_dvd_relIndex_of_liesOver_inertia (V : FDRep k N) [Simple V]
    (U : FDRep k (inertia V)) [Simple U]
    (hU : U.LiesOver (Subgroup.inclusion (le_inertia V)) V) :
    ∃ m, finrank k U = finrank k V * m ∧ m ∣ N.relIndex (inertia V) := by
  have : Nontrivial V := (FDRep.isIrreducible_of_simple V).nontrivial
  obtain ⟨ρ, β, h⟩ := exists_isProjectiveInertiaExtension V (endomorphism_simple_eq_smul_id k)
  obtain ⟨f, hf⟩ := liesOver_iff.1 hU
  have : Representation.IsIrreducible U.ρ := FDRep.isIrreducible_of_simple U
  let φ : Representation.IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V))) :=
    ((forget₂ (FDRep k N) (Rep k N)).map f).hom
  have hφ : φ ≠ 0 := fun h0 => hf <| by
    ext v
    exact congr($h0 v)
  let M := Representation.IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V)))
  have : Nontrivial M := ⟨φ, 0, hφ⟩
  refine ⟨finrank k M, ?_, ?_⟩
  · rw [← (h.tensorRepEquiv U.ρ hφ).toLinearEquiv.finrank_eq, finrank_tensorProduct]
  · rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact (h.isProjectiveRep_homAction U.ρ).finrank_dvd_card
      fun p hp => h.eq_bot_or_eq_top_of_homAction_mem U.ρ hφ p hp

/-- **The degree ratio over a normal subgroup divides the index** (Isaacs, Corollary 11.29). Let
`N` be a normal subgroup of a finite group `G` and `W` an irreducible representation of `G`, over
an algebraically closed field of characteristic zero, lying over an irreducible representation `V`
of `N`. Then `dim W = dim V · m` for some `m` dividing `|G : N|`. -/
theorem exists_finrank_eq_mul_dvd_index_of_liesOver (V : FDRep k N) [Simple V] (W : FDRep k G)
    [Simple W] (hW : W.LiesOver N.subtype V) :
    ∃ m, finrank k W = finrank k V * m ∧ m ∣ N.index := by
  obtain ⟨U, _, hU, ⟨e⟩⟩ := exists_simple_liesOver_inertia_nonempty_iso_indFDRep V W hW
  obtain ⟨m, hm, hmdvd⟩ := exists_finrank_eq_mul_dvd_relIndex_of_liesOver_inertia V U hU
  refine ⟨(inertia V).index * m, ?_, ?_⟩
  · rw [← (FDRep.isoToLinearEquiv e).finrank_eq, finrank_indFDRep, hm]
    ring
  · rw [← Subgroup.relIndex_mul_index (le_inertia V), mul_comm]
    exact mul_dvd_mul_right hmdvd _

/-- **The degree ratio divides the index.** For an irreducible representation `W` of a finite
group `G` lying over an irreducible representation `V` of a normal subgroup `N`, over an
algebraically closed field of characteristic zero, `dim V ∣ dim W` and
`dim W / dim V ∣ |G : N|` (Isaacs, Corollary 11.29). -/
theorem finrank_dvd_finrank_and_finrank_div_finrank_dvd_index_of_liesOver (V : FDRep k N)
    [Simple V] (W : FDRep k G) [Simple W] (hW : W.LiesOver N.subtype V) :
    finrank k V ∣ finrank k W ∧ finrank k W / finrank k V ∣ N.index := by
  obtain ⟨m, hm, hmdvd⟩ := exists_finrank_eq_mul_dvd_index_of_liesOver V W hW
  have : Nontrivial V := (FDRep.isIrreducible_of_simple V).nontrivial
  have hV : 0 < finrank k V := finrank_pos
  refine ⟨⟨m, hm⟩, ?_⟩
  rwa [hm, Nat.mul_div_cancel_left _ hV]

end FDRep
