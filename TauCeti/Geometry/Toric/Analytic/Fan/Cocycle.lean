/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Overlap

/-!
# Cocycle of analytic toric chart overlaps

The transitions between affine charts of a regular fan preserve triple overlaps and
satisfy the cocycle law there. These are the compatibility conditions for gluing the
charts as open complex subspaces.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- A point in the intersection of two overlap loci comes from the chart of the
triple intersection cone. -/
theorem exists_analyticTripleOverlap (σ τ υ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ)
    (hτ : x ∈ Φ.analyticOverlapOpens hΦ σ τ)
    (hυ : x ∈ Φ.analyticOverlapOpens hΦ σ υ) :
    ∃ z : (Φ.analyticAffineChartDiagram hΦ).obj ((σ ⊓ τ) ⊓ υ),
      (Φ.analyticAffineChartDiagram hΦ).map (homOfLE (inf_le_left.trans inf_le_left)) z = x := by
  obtain ⟨a, ha⟩ := (Φ.mem_analyticOverlapOpens hΦ σ τ x).mp hτ
  obtain ⟨b, hb⟩ := (Φ.mem_analyticOverlapOpens hΦ σ υ x).mp hυ
  rw [Φ.analyticOverlapLeft_def hΦ] at ha hb
  let F := Φ.analyticAffineChartDiagram hΦ
  obtain ⟨ρ, f, g, w, hfw, hgw⟩ :=
    (Φ.isLocallyDirected_analyticAffineChartDiagram hΦ).cond
      (homOfLE inf_le_left : σ ⊓ τ ⟶ σ)
      (homOfLE inf_le_left : σ ⊓ υ ⟶ σ) a b (ha.trans hb.symm)
  -- Forgetting the chart topology leaves the same underlying point map.
  change (Φ.analyticAffineChartDiagram hΦ).map f w = a at hfw
  have hρ : ρ ≤ (σ ⊓ τ) ⊓ υ :=
    le_inf (leOfHom f) ((leOfHom g).trans inf_le_right)
  refine ⟨F.map (homOfLE hρ) w, ?_⟩
  rw [Φ.analyticChartMap_comp hΦ]
  have heq : (homOfLE hρ : ρ ⟶ (σ ⊓ τ) ⊓ υ) ≫
      homOfLE (inf_le_left.trans inf_le_left) =
      f ≫ (homOfLE inf_le_left : σ ⊓ τ ⟶ σ) := Subsingleton.elim _ _
  rw [heq, ← Φ.analyticChartMap_comp hΦ, hfw]
  exact ha

/-- An overlap transition sends the triple overlap of the first and third charts
into the overlap of the second and third charts. -/
theorem analyticOverlapHomeomorph_mem (σ τ υ : Φ.cones)
    (x : Φ.analyticOverlapOpens hΦ σ τ)
    (h : (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) ∈
      Φ.analyticOverlapOpens hΦ σ υ) :
    ((Φ.analyticOverlapHomeomorph hΦ σ τ x) :
      (Φ.analyticAffineChartDiagram hΦ).obj τ) ∈
        Φ.analyticOverlapOpens hΦ τ υ := by
  obtain ⟨z, hz⟩ := Φ.exists_analyticTripleOverlap hΦ σ τ υ x x.2 h
  have hx : x = ⟨(Φ.analyticAffineChartDiagram hΦ).map
      (homOfLE (inf_le_left.trans inf_le_left)) z,
      Φ.mem_analyticOverlapOpens_of_le hΦ
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) z⟩ :=
    Subtype.ext hz.symm
  rw [hx, Φ.analyticOverlapHomeomorph_apply_of_le hΦ]
  exact Φ.mem_analyticOverlapOpens_of_le hΦ
    (inf_le_left.trans inf_le_right) inf_le_right z

/-- The overlap transitions obey the cocycle law on a triple overlap. -/
theorem analyticOverlapHomeomorph_cocycle (σ τ υ : Φ.cones)
    (x : Φ.analyticOverlapOpens hΦ σ τ)
    (h : (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) ∈
      Φ.analyticOverlapOpens hΦ σ υ) :
    (((Φ.analyticOverlapHomeomorph hΦ τ υ)
      ⟨(Φ.analyticOverlapHomeomorph hΦ σ τ x).1,
        Φ.analyticOverlapHomeomorph_mem hΦ σ τ υ x h⟩).1) =
      ((Φ.analyticOverlapHomeomorph hΦ σ υ) ⟨x.1, h⟩).1 := by
  obtain ⟨z, hz⟩ := Φ.exists_analyticTripleOverlap hΦ σ τ υ x x.2 h
  have hx : x = ⟨(Φ.analyticAffineChartDiagram hΦ).map
      (homOfLE (inf_le_left.trans inf_le_left)) z,
      Φ.mem_analyticOverlapOpens_of_le hΦ
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) z⟩ :=
    Subtype.ext hz.symm
  have ht : (Φ.analyticOverlapHomeomorph hΦ σ τ x).1 =
      (Φ.analyticAffineChartDiagram hΦ).map
        (homOfLE (inf_le_left.trans inf_le_right)) z := by
    rw [hx, Φ.analyticOverlapHomeomorph_apply_of_le hΦ]
  have ht' : (⟨(Φ.analyticOverlapHomeomorph hΦ σ τ x).1,
      Φ.analyticOverlapHomeomorph_mem hΦ σ τ υ x h⟩ :
      Φ.analyticOverlapOpens hΦ τ υ) =
      ⟨(Φ.analyticAffineChartDiagram hΦ).map
        (homOfLE (inf_le_left.trans inf_le_right)) z,
        Φ.mem_analyticOverlapOpens_of_le hΦ
          (inf_le_left.trans inf_le_right) inf_le_right z⟩ := Subtype.ext ht
  rw [ht', Φ.analyticOverlapHomeomorph_apply_of_le hΦ
    (inf_le_left.trans inf_le_right) inf_le_right z]
  have hx' : (⟨x.1, h⟩ : Φ.analyticOverlapOpens hΦ σ υ) =
      ⟨(Φ.analyticAffineChartDiagram hΦ).map
        (homOfLE (inf_le_left.trans inf_le_left)) z,
        Φ.mem_analyticOverlapOpens_of_le hΦ
          (inf_le_left.trans inf_le_left) inf_le_right z⟩ := Subtype.ext hz.symm
  rw [hx', Φ.analyticOverlapHomeomorph_apply_of_le hΦ
    (inf_le_left.trans inf_le_left) inf_le_right z]

end TauCeti.Toric.Fan
