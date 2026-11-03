/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Basic

/-!
# The subgroup accepted by a Stallings fold

Identifying equally labelled outgoing darts does not change the subgroup read by loops.
The key point is that the two vertices identified by a fold are connected by a path
whose label is the identity. Such paths repair the joins when a path in the quotient
is lifted dart by dart. This is the local step needed for finite folding.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Lemma 3.4.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

variable {α : Type u} (S : StallingsGraph.{u, v, w} α)
variable (f₁ f₂ : S.graph.E)
variable (hsrc : S.graph.src f₁ = S.graph.src f₂)
variable (hlabel : S.label f₁ = S.label f₂)

private theorem exists_path_read_eq_one_tgt_tgt (hsrc : S.graph.src f₁ = S.graph.src f₂)
    (hlabel : S.label f₁ = S.label f₂) :
    ∃ p : S.graph.Path (S.graph.tgt f₁) (S.graph.tgt f₂), S.read p = 1 := by
  let e₁ := S.graph.dart f₁
  let e₂ : Quiver.Hom (S.graph.src f₁) (S.graph.tgt f₂) :=
    ⟨f₂, hsrc.symm, rfl⟩
  refine ⟨(Quiver.reverse e₁).toPath.comp e₂.toPath, ?_⟩
  simp only [S.read_comp, ← Quiver.Path.reverse_toPath, S.read_reverse,
    S.read_toPath, e₁, e₂, S.graph.dart_val, hlabel, inv_mul_cancel]

private theorem exists_path_read_eq_one_of_EqvGen
    (hsrc : S.graph.src f₁ = S.graph.src f₂)
    (hlabel : S.label f₁ = S.label f₂) {x y : S.graph.V}
    (h : Relation.EqvGen (fun a b =>
      a = S.graph.tgt f₁ ∧ b = S.graph.tgt f₂) x y) :
    ∃ p : S.graph.Path x y, S.read p = 1 := by
  induction h with
  | rel x y h =>
      rcases h with ⟨rfl, rfl⟩
      exact S.exists_path_read_eq_one_tgt_tgt f₁ f₂ hsrc hlabel
  | refl => exact ⟨.nil, by simp⟩
  | symm x y _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨p.reverse, by simp [hp]⟩
  | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨p, hp⟩ := ih₁
      obtain ⟨q, hq⟩ := ih₂
      exact ⟨p.comp q, by simp [hp, hq]⟩

/-- Vertices identified by a fold can be joined by a path with trivial reading. -/
theorem exists_path_read_eq_one_of_foldHom_mapV_eq {x y : S.graph.V}
    (hxy : (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV x =
      (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV y) :
    ∃ p : S.graph.Path x y, S.read p = 1 :=
  S.exists_path_read_eq_one_of_EqvGen f₁ f₂ hsrc hlabel
    ((S.foldHom_mapV_eq_iff f₁ f₂ hsrc hlabel x y).mp hxy)

/-- A path in a single fold can be lifted from any chosen preimage of its start,
without changing its free-group reading. -/
theorem exists_fold_path_lift {a b : (S.foldAt f₁ f₂ hsrc hlabel).graph.V}
    (q : (S.foldAt f₁ f₂ hsrc hlabel).graph.Path a b)
    (x : S.graph.V)
    (hx : (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV x = a) :
    ∃ (y : S.graph.V) (p : S.graph.Path x y),
      (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV y = b ∧
        S.read p = (S.foldAt f₁ f₂ hsrc hlabel).read q := by
  let F := S.foldAt f₁ f₂ hsrc hlabel
  let φ := S.foldHom f₁ f₂ hsrc hlabel
  induction q generalizing x with
  | nil =>
      exact ⟨x, .nil, hx, by simp⟩
  | @cons b c q e ih =>
      obtain ⟨y, p, hy, hp⟩ := ih x hx
      obtain ⟨d, hd⟩ := S.foldHom_mapE_surjective f₁ f₂ hsrc hlabel e.1
      have hb : φ.graphHom.mapV (S.graph.src d) = b := by
        rw [← e.2.1, ← hd]
        exact (φ.graphHom.map_src d).symm
      obtain ⟨r, hr⟩ := S.exists_path_read_eq_one_of_foldHom_mapV_eq
        f₁ f₂ hsrc hlabel (hy.trans hb.symm)
      have hc : φ.graphHom.mapV (S.graph.tgt d) = c := by
        rw [← e.2.2, ← hd]
        exact (SerreGraph.Hom.map_tgt S.graph φ.graphHom d).symm
      have hre : S.read (S.graph.dart d).toPath = F.read e.toPath := by
        simp only [S.read_toPath, F.read_toPath, S.graph.dart_val]
        rw [← φ.map_label d, hd]
      refine ⟨S.graph.tgt d, (p.comp r).comp (S.graph.dart d).toPath, hc, ?_⟩
      simp only [S.read_comp, hp, hr, mul_one, hre]
      simpa only [F.read_toPath] using (F.read_cons q e).symm

/-- A single Stallings fold preserves the subgroup read at every vertex. -/
@[simp]
theorem foldAt_subgroup (x : S.graph.V) :
    (S.foldAt f₁ f₂ hsrc hlabel).subgroup
      ((S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV x) = S.subgroup x := by
  apply le_antisymm
  · intro g hg
    obtain ⟨q, rfl⟩ := (S.foldAt f₁ f₂ hsrc hlabel).mem_subgroup_iff.mp hg
    obtain ⟨y, p, hy, hp⟩ := S.exists_fold_path_lift f₁ f₂ hsrc hlabel q
      x rfl
    obtain ⟨r, hr⟩ := S.exists_path_read_eq_one_of_foldHom_mapV_eq f₁ f₂ hsrc hlabel
      hy
    exact S.mem_subgroup_iff.mpr ⟨p.comp r, by simp [hp, hr]⟩
  · exact (S.foldHom f₁ f₂ hsrc hlabel).subgroup_le_subgroup_mapV x

/-- A single Stallings fold preserves the subgroup accepted at its base vertex. -/
@[simp]
theorem foldAt_subgroup_base :
    (S.foldAt f₁ f₂ hsrc hlabel).subgroup
      (S.foldAt f₁ f₂ hsrc hlabel).base = S.subgroup S.base := by
  rw [← (S.foldHom f₁ f₂ hsrc hlabel).map_base, foldAt_subgroup]

end TauCeti.StallingsGraph
