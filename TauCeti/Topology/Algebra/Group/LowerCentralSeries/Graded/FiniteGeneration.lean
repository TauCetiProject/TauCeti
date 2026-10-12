/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Closed
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.ClosedSpan
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CompactModule

/-!
# Finite generation of closed lower central series graded pieces

Every graded piece of the closed lower central series of a topologically finitely generated
pro-`p` group is a finitely generated `ℤ_p`-module. The degree-zero piece is an abelian pro-`p`
quotient. In higher degrees, the finite bracket spanning theorem presents each piece as a
quotient of a finite product of the preceding piece. This gives the finite generation needed
to study the graded Lie algebra of a finitely generated pro-`p` group.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954), for graded Lie rings of central series.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.3, for compact abelian pro-`p`
  groups and their `ℤ_p`-module structures.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Every closed lower central series graded piece of a topologically finitely generated
pro-`p` group is finitely generated over `ℤ_p`, with its canonical module structure. -/
theorem IsProP.module_finite_lcsGradedPiece (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (n : ℕ) :
    letI := hG.gradedPieceModule 0 n
    Module.Finite ℤ_[p] (lcsGradedPiece G n) := by
  classical
  induction n with
  | zero =>
    rw [hG.gradedPieceModule_def]
    let R := pLowerCentralSeries 0 G 0
    let N := (pLowerCentralSeries 0 G 1).subgroupOf R
    let _ : IsClosed (R : Set G) := isClosed_pLowerCentralSeries 0
    let _ : IsClosed (N : Set R) :=
      (isClosed_pLowerCentralSeries 1).preimage continuous_subtype_val
    let f : G →* R := (MonoidHom.id G).codRestrict R (mem_pLowerCentralSeries_zero 0)
    have hf : Continuous f := continuous_id.subtype_mk _
    have hsurj : Function.Surjective f := fun x ↦ ⟨x, Subtype.ext rfl⟩
    exact ((hG.subgroup R).quotient N).isTopologicallyFinitelyGenerated_iff_module_finite.mp
      ((hfg.of_surjective hf hsurj).quotient N)
  | succ n ih =>
    -- The bracket indexes its target degree as `0 + n + 1`.
    rw [← Nat.zero_add n]
    let _ := hG.gradedPieceModule 0 0
    let _ := hG.gradedPieceModule 0 n
    let _ := hG.gradedPieceModule 0 (0 + n + 1)
    let _ : Module.Finite ℤ_[p] (gradedPiece 0 G n) := ih
    let _ : IsClosed (pLowerCentralSeries 0 G n : Set G) := isClosed_pLowerCentralSeries n
    obtain ⟨S, hS⟩ := isTopologicallyFinitelyGenerated_iff.mp hfg
    let fs (s : S) : gradedPiece 0 G n →ₗ[ℤ_[p]] gradedPiece 0 G (0 + n + 1) :=
      { toFun := gradedBracket 0 G 0 n (gradedMkZero 0 G s)
        map_add' := map_add _
        map_smul' := by
          intro u y
          exact hG.gradedBracket_smul_right u (gradedMkZero 0 G s) y }
    let f := LinearMap.lsum ℤ_[p] (fun _ : S ↦ gradedPiece 0 G n) ℤ_[p] fs
    have hrange : Set.range (fun s : S ↦ (s : G)) = (S : Set G) := by ext; simp
    have hsurj : Function.Surjective f := by
      intro z
      simpa only [f, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, fs, LinearMap.coe_mk, AddHom.coe_mk] using
        exists_sum_gradedBracket_eq_of_range n (fun s : S ↦ (s : G))
          (by rwa [hrange]) z
    exact Module.Finite.of_surjective f hsurj

end TauCeti
