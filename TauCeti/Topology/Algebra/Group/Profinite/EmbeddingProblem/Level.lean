/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Solutions
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Finite levels of a lifting problem

For a continuous surjection `α : A → B`, an open normal subgroup `U` of `A`
gives the quotient map `A/U → B/α(U)`. The map induced by `f : G → B` need
not be surjective. Accordingly `levelProblem` restricts the quotient map to the
preimage of that map's range.

`LevelSolution` records the equivalent lift into `A/U`. Solvability follows
from `HasPGroupSolutions`, and topological finite generation of `G` makes each
level's solution set finite.
-/

public section

namespace TauCeti

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
variable {B : Type w} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- The image of an open normal subgroup under a continuous surjection from a compact group. -/
def levelImage (α : A →ₜ* B) (hα : Function.Surjective α) (U : OpenNormalSubgroup A) :
    OpenNormalSubgroup B := by
  let M := U.toSubgroup.map α.toMonoidHom
  have : M.Normal := U.isNormal'.map α.toMonoidHom hα
  let q := QuotientGroup.map U.toSubgroup M α.toMonoidHom
    (Subgroup.le_comap_map _ _)
  have : Finite (B ⧸ M) := Finite.of_surjective q
    (QuotientGroup.map_surjective_of_surjective _ _ _
      ((QuotientGroup.mk'_surjective M).comp hα) _)
  have : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact
    { toSubgroup := M
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex M
        (U.toOpenSubgroup.isClosed.isCompact.image α.continuous).isClosed
      isNormal' := inferInstance }

@[simp]
theorem levelImage_toSubgroup (α : A →ₜ* B) (hα : Function.Surjective α)
    (U : OpenNormalSubgroup A) :
    (levelImage α hα U).toSubgroup = U.toSubgroup.map α.toMonoidHom :=
  (rfl)

/-- The finite quotient map induced by `α` at `U`. -/
def levelMap (α : A →ₜ* B) (hα : Function.Surjective α) (U : OpenNormalSubgroup A) :
    A ⧸ U.toSubgroup →* B ⧸ (levelImage α hα U).toSubgroup :=
  QuotientGroup.map _ _ α.toMonoidHom (Subgroup.le_comap_map _ _)

@[simp]
theorem levelMap_mk (α : A →ₜ* B) (hα : Function.Surjective α)
    (U : OpenNormalSubgroup A) (a : A) :
    levelMap α hα U (a : A ⧸ U.toSubgroup) = (α a : B ⧸ (levelImage α hα U).toSubgroup) :=
  (rfl)

/-- The finite quotient map induced by a surjection is surjective. -/
theorem levelMap_surjective (α : A →ₜ* B) (hα : Function.Surjective α)
    (U : OpenNormalSubgroup A) : Function.Surjective (levelMap α hα U) :=
  QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hα) _

/-- The finite embedding problem obtained by restricting to the image of `G` in `B/α(U)`. -/
abbrev levelProblem (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    (U : OpenNormalSubgroup A) : FiniteEmbeddingProblem G :=
  FiniteEmbeddingProblem.ofSurjective (levelMap α hα U) (levelMap_surjective α hα U)
    ((QuotientGroup.mk' (levelImage α hα U).toSubgroup).comp f.toMonoidHom)
    (MonoidHom.continuous_iff_isOpen_ker _ |>.mp
      (QuotientGroup.continuous_mk.comp f.continuous))

/-- A continuous lift of `f` at the finite quotient `A/U`. -/
abbrev LevelSolution (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    (U : OpenNormalSubgroup A) :=
  {β : G →ₜ* A ⧸ U.toSubgroup //
    ∀ g, levelMap α hα U (β g) =
      QuotientGroup.mk' (levelImage α hα U).toSubgroup (f g)}

/-- Range restriction identifies solutions of the embedding problem with lifts into `A/U`. -/
def levelSolutionEquiv (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    (U : OpenNormalSubgroup A) :
    {β : G →* (levelProblem α hα f U).E // (levelProblem α hα f U).IsSolution β} ≃
      LevelSolution α hα f U where
  toFun β :=
    ⟨⟨_, (MonoidHom.continuous_iff_isOpen_ker _).mpr β.2.isOpen_ker_subtype_comp⟩,
      fun g ↦ DFunLike.congr_fun β.2.comp_subtype_comp g⟩
  invFun β := by
    let φ := levelMap α hα U
    let π := (QuotientGroup.mk' (levelImage α hα U).toSubgroup).comp f.toMonoidHom
    let β' : G →* π.range.comap φ := β.1.toMonoidHom.codRestrict _ fun g ↦
      ⟨g, (β.2 g).symm⟩
    refine ⟨β', FiniteEmbeddingProblem.isSolution_ofSurjective_iff.mpr ⟨?_, ?_⟩⟩
    · exact (MonoidHom.continuous_iff_isOpen_ker _).mp
        (β.1.continuous.subtype_mk _)
    · ext g
      exact β.2 g
  left_inv β := by
    apply Subtype.ext
    ext g
    rfl
  right_inv β := by
    apply Subtype.ext
    ext g
    rfl

/-- The lift into `A/U` associated with a solution has the same underlying map. -/
-- Not `@[simp]`: the `simpNF` linter rewrites the coercions inside the domain type of
-- `levelSolutionEquiv`, so the left-hand side is not in simp-normal form.
theorem levelSolutionEquiv_apply_coe (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    (U : OpenNormalSubgroup A)
    (β : {β : G →* (levelProblem α hα f U).E // (levelProblem α hα f U).IsSolution β}) (g : G) :
    (levelSolutionEquiv α hα f U β).1 g = (β.1 g : A ⧸ U.toSubgroup) :=
  (rfl)

/-- The solution associated with a lift into `A/U` has the same underlying map. -/
-- Not `@[simp]`, for the same reason as `levelSolutionEquiv_apply_coe`.
theorem levelSolutionEquiv_symm_apply_coe (α : A →ₜ* B) (hα : Function.Surjective α)
    (f : G →ₜ* B) (U : OpenNormalSubgroup A) (β : LevelSolution α hα f U) (g : G) :
    (((levelSolutionEquiv α hα f U).symm β).1 g : A ⧸ U.toSubgroup) = β.1 g :=
  (rfl)

/-- Every finite level has a solution when all finite `p`-kernel embedding problems do. -/
theorem nonempty_isSolution_levelProblem {p : ℕ} (hG : HasPGroupSolutions p G)
    (hA : IsProP p A) (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    (U : OpenNormalSubgroup A) :
    Nonempty {β : G →* (levelProblem α hα f U).E //
      (levelProblem α hα f U).IsSolution β} := by
  have hE := (isProP_iff.mp hA U).to_subgroup
    (((QuotientGroup.mk' (levelImage α hα U).toSubgroup).comp f.toMonoidHom).range.comap
      (levelMap α hα U))
  obtain ⟨β, hβ⟩ := hG.exists_isSolution (levelProblem α hα f U) (hE.to_subgroup _)
  exact ⟨β, hβ⟩

/-- Solvability of all finite `p`-kernel embedding problems gives a solution at every level. -/
theorem nonempty_levelSolution {p : ℕ} (hG : HasPGroupSolutions p G) (hA : IsProP p A)
    (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B) (U : OpenNormalSubgroup A) :
    Nonempty (LevelSolution α hα f U) :=
  (nonempty_isSolution_levelProblem hG hA α hα f U).map (levelSolutionEquiv α hα f U)

/-- Topological finite generation makes each level's solution set finite. -/
theorem IsTopologicallyFinitelyGenerated.finite_levelSolution
    (hG : IsTopologicallyFinitelyGenerated G) (α : A →ₜ* B) (hα : Function.Surjective α)
    (f : G →ₜ* B) (U : OpenNormalSubgroup A) : Finite (LevelSolution α hα f U) := by
  have := hG.finite_isSolution (levelProblem α hα f U)
  exact Finite.of_equiv _ (levelSolutionEquiv α hα f U)

end TauCeti
