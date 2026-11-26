/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.InverseSet.Sphere
import TauCeti.Topology.Compactness.Normed
import TauCeti.Topology.Sphere.Stereographic
import TauCeti.Topology.Compactification.OnePoint.Collapse

/-!
# A compact space covered by two Euclidean open sets is a sphere

Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`, each homeomorphic to a
real normed space `E` of dimension `m > 0`. Then `X` is homeomorphic to the sphere `Sᵐ`
(`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`). This is the topological form of
Milnor's recognition of spheres (Milnor 1959, Theorem 1 (3) and Corollary 1; Rosen 1960, Lemma 1),
and it is what identifies a closed manifold carrying a function with exactly two critical points,
possibly degenerate, with a sphere.

The proof collapses the complement `C = X \ U` to a point. The collapse `X → OnePoint U` is
continuous, and `OnePoint U ≃ₜ OnePoint E` is the sphere `Sᵐ`. Since `C` is a compact subset of
`V ≃ₜ E`, it lies in the open unit ball of suitably scaled coordinates `κ : E → V`. It remains to
see that `C` is cellular in these coordinates, for then collapsing it does not change `X`
(`TauCeti.IsCellularSet.nonempty_homeomorph_onePoint`).

The collapse restricted to the closed unit ball of `E`, read through `κ`, maps the ball into `Sᵐ`
and is injective off `C`; so `C` is the only inverse set of a map of an `m`-cell into `Sᵐ`, and it
is cellular by M. Brown's theorem on inverse sets
(`TauCeti.isCellularSet_closedBall_inter_preimage`).

Conversely, the sphere `Sᵐ` has such a cover: the complement of any point of `Sᵐ` is homeomorphic
to `ℝᵐ` (`TauCeti.nonempty_homeomorph_sphere_compl_singleton`), so the complements of two antipodal
points, the poles, cover `Sᵐ` (`TauCeti.exists_two_euclidean_opens_sphere`). Hence for `m > 0` a
space is homeomorphic to `Sᵐ` exactly when it is compact, Hausdorff and covered by two open sets
homeomorphic to `ℝᵐ` (`TauCeti.nonempty_homeomorph_sphere_iff_exists_two_euclidean_opens`). The
examples at the end of the file show that neither `m > 0` nor compactness can be dropped: a point
is covered twice by `ℝ⁰` but is not `S⁰`, and `ℝᵐ` is covered twice by itself but is not compact.

## Main results

* `TauCeti.IsCellularSet.nonempty_homeomorph_onePoint`: if the complement of an open set `U` of a
  compact Hausdorff space `X` is cellular in Euclidean coordinates, then `X` is the one-point
  compactification of `U`.
* `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`: a compact Hausdorff space covered
  by two open sets homeomorphic to `ℝᵐ`, `m > 0`, is homeomorphic to `Sᵐ`.
* `TauCeti.nonempty_homeomorph_sphere_iff_exists_two_euclidean_opens`: for `m > 0`, a space is
  homeomorphic to `Sᵐ` if and only if it is compact, Hausdorff and covered by two open sets
  homeomorphic to `ℝᵐ`.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 2 and 3.
-/

public section

open Function Metric Module OnePoint Set Topology

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A cellular complement of an open set.** Let `U` be an open subset of a compact Hausdorff
space `X` whose complement is the image of a cellular set `A ⊆ E` under an open embedding
`κ : E → X` of a finite-dimensional real normed space. Then `X` is homeomorphic to the one-point
compactification of `U`: collapsing `X \ U` to a point does not change `X`. -/
theorem IsCellularSet.nonempty_homeomorph_onePoint [FiniteDimensional ℝ E] [CompactSpace X]
    [T2Space X] {U : Set X} (hU : IsOpen U) {A : Set E} (hA : IsCellularSet E A) {κ : E → X}
    (hκ : IsOpenEmbedding κ) (hAU : κ '' A = Uᶜ) : Nonempty (X ≃ₜ OnePoint U) := by
  have := hU.locallyCompactSpace
  refine hA.nonempty_homeomorph_of_isOpenEmbedding hκ
    (continuous_onePointCollapse hU.isOpenEmbedding_subtypeVal isProperMap_id) (fun z ↦ ?_)
    fun x y ↦ by
      rw [hAU, onePointCollapse_eq_onePointCollapse_iff Subtype.val_injective injective_id,
        Subtype.range_coe]
      rfl
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨x, hx⟩ := hA.nonempty.image κ
    rw [hAU] at hx
    exact ⟨x, onePointCollapse_of_notMem_range (by rwa [Subtype.range_coe])⟩
  | coe u => exact ⟨u, onePointCollapse_apply Subtype.val_injective id u⟩

/-- The complement of `U` read in coordinates `κ` which carry the open unit ball over it is
cellular. It is the only inverse set of the collapse of `X \ U` to `∞`, restricted to the closed
unit ball, so this is M. Brown's theorem on inverse sets. -/
private theorem exists_isCellularSet_image_eq_compl [FiniteDimensional ℝ E] [T2Space X]
    {U : Set X} (hU : IsOpen U) (eU : U ≃ₜ E) {κ : E → X}
    (hκ : IsOpenEmbedding κ) (hUκ : Uᶜ ⊆ κ '' ball 0 1) (hne : Uᶜ.Nonempty) :
    ∃ A : Set E, IsCellularSet E A ∧ κ '' A = Uᶜ := by
  set j : OnePoint U ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 :=
    eU.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp))
  set f := j ∘ onePointCollapse ((↑) : U → X) id ∘ κ
  have hf : Continuous f := j.continuous.comp
    ((continuous_onePointCollapse hU.isOpenEmbedding_subtypeVal isProperMap_id).comp hκ.continuous)
  have hfy (v : E) : f v = j ∞ ↔ κ v ∉ U := by
    simp only [f, comp_apply, j.injective.eq_iff]
    rw [onePointCollapse_eq_infty_iff Subtype.val_injective, Subtype.range_coe]
  have hball {v : E} (hv : κ v ∉ U) : v ∈ ball 0 1 := by
    obtain ⟨w, hw, hwv⟩ := hUκ hv
    rwa [← hκ.injective hwv]
  refine ⟨closedBall 0 1 ∩ f ⁻¹' {j ∞}, isCellularSet_closedBall_inter_preimage (by simp)
    hf.continuousOn (fun v hv w _ hvw ↦ ?_) ?_ ?_, ?_⟩
  · -- `f` is injective off the fibre over `∞`.
    have := (onePointCollapse_eq_onePointCollapse_iff Subtype.val_injective injective_id).1
      (j.injective hvw)
    rw [Subtype.range_coe] at this
    exact hκ.injective (this.resolve_right fun h ↦ hv.2 ((hfy v).2 h.1))
  · rintro ⟨v, hv, hfv⟩
    exact sphere_disjoint_ball.ne_of_mem hv (hball ((hfy v).1 hfv)) rfl
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨v, hv, rfl⟩ := hUκ hx
    exact ⟨v, ball_subset_closedBall hv, (hfy v).2 hx⟩
  · ext x
    refine ⟨fun ⟨v, ⟨_, hv⟩, hvx⟩ ↦ hvx ▸ (hfy v).1 hv, fun hx ↦ ?_⟩
    obtain ⟨v, hv, rfl⟩ := hUκ hx
    exact ⟨v, ⟨ball_subset_closedBall hv, (hfy v).2 hx⟩, rfl⟩

/-- **A compact space covered by two Euclidean open sets is a sphere.** Let `X` be a compact
Hausdorff space covered by two open sets `U` and `V`, each homeomorphic to a real normed space `E`
of dimension `m > 0`. Then `X` is homeomorphic to the unit sphere of any real normed space of
dimension `m + 1` (Milnor 1959, Corollary 1; Rosen 1960, Lemma 1).

Neither `m > 0` nor compactness can be dropped: a point is covered twice by `ℝ⁰` and is not `S⁰`,
and `ℝᵐ` is covered by two copies of itself but is not compact. -/
theorem nonempty_homeomorph_sphere_of_two_euclidean_opens [CompactSpace X] [T2Space X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (eU : U ≃ₜ E)
    (eV : V ≃ₜ E) (hE : 0 < finrank ℝ E) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hEF : finrank ℝ F = finrank ℝ E + 1) : Nonempty (X ≃ₜ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hE
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hE
  -- The one-point compactification of `U` is the sphere.
  suffices Nonempty (X ≃ₜ OnePoint U) from this.map fun h ↦ h.trans <| eU.onePointCongr.trans <|
    (onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ E + 1)) (by simp)).trans
      (sphereHomeomorphOfFinrankEq (by simp [hEF]))
  -- The complement of `U` is nonempty, since `E` is not compact.
  have hne : Uᶜ.Nonempty := by
    by_contra h
    have : CompactSpace U := isCompact_iff_compactSpace.1 (by
      rw [compl_empty_iff.1 (not_nonempty_iff_eq_empty.1 h)]; exact isCompact_univ)
    exact noncompact_univ E (eU.compactSpace.isCompact_univ)
  -- Coordinates `κ` on `V`, scaled so that the open unit ball covers the complement of `U`.
  obtain ⟨S, hS0, hS⟩ := exists_nonneg_forall_notMem_norm_lt hU (by rwa [union_comm]) eV
  set κ : E → X := fun v ↦ (eV.symm ((S + 1) • v) : X)
  have hS1 : S + 1 ≠ 0 := by positivity
  have hκ : IsOpenEmbedding κ := hV.isOpenEmbedding_subtypeVal.comp
    (eV.symm.isOpenEmbedding.comp (Homeomorph.smulOfNeZero (S + 1) hS1).isOpenEmbedding)
  have hUκ : Uᶜ ⊆ κ '' ball 0 1 := fun x hx ↦ by
    have hxV : x ∈ V := (eq_univ_iff_forall.1 hUV x).resolve_left hx
    refine ⟨(S + 1)⁻¹ • eV ⟨x, hxV⟩, ?_, by simp [κ, smul_smul, hS1]⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_lt_one₀ (by positivity)]
    linarith [hS ⟨x, hxV⟩ hx]
  obtain ⟨A, hA, hAU⟩ := exists_isCellularSet_image_eq_compl hU eU hκ hUκ hne
  exact hA.nonempty_homeomorph_onePoint hU hκ hAU

/-! ### The converse: the sphere is covered by two Euclidean open sets -/

section Converse

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Recognition of the topological sphere.** A space `X` is homeomorphic to the sphere `Sᵐ`,
`m > 0`, if and only if it is a compact Hausdorff space covered by two open sets, each
homeomorphic to a real normed space `E` of dimension `m`. Here `Sᵐ` is the unit sphere of any real
normed space of dimension `m + 1`.

The reverse direction is `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`; the forward
direction carries over the cover of `Sᵐ` by the complements of its two poles
(`TauCeti.exists_two_euclidean_opens_sphere`). -/
theorem nonempty_homeomorph_sphere_iff_exists_two_euclidean_opens (hE : 0 < finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) :
    Nonempty (X ≃ₜ sphere (0 : F) 1) ↔ CompactSpace X ∧ T2Space X ∧
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ Nonempty (U ≃ₜ E) ∧
        Nonempty (V ≃ₜ E) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hE
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  refine ⟨fun ⟨φ⟩ ↦ ⟨φ.symm.compactSpace, φ.isEmbedding.t2Space, ?_⟩,
    fun ⟨_, _, U, V, hU, hV, hUV, ⟨eU⟩, ⟨eV⟩⟩ ↦
      nonempty_homeomorph_sphere_of_two_euclidean_opens hU hV hUV eU eV hE hEF⟩
  obtain ⟨U, V, hU, hV, hUV, ⟨eU⟩, ⟨eV⟩⟩ := exists_two_euclidean_opens_sphere (E := E) hEF
  exact ⟨φ ⁻¹' U, φ ⁻¹' V, hU.preimage φ.continuous, hV.preimage φ.continuous,
    by rw [← preimage_union, hUV, preimage_univ], ⟨(φ.sets rfl).trans eU⟩,
    ⟨(φ.sets rfl).trans eV⟩⟩

/-- Dimension `0` must be excluded from `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`:
a point is covered twice by its only open set `univ ≃ₜ ℝ⁰`, but it is not `S⁰`, which has the two
points `±1`. -/
example :
    (∃ U V : Set Unit, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 0)) ∧ Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 0))) ∧
    IsEmpty (Unit ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  have e : (univ : Set Unit) ≃ₜ EuclideanSpace ℝ (Fin 0) :=
    (Homeomorph.Set.univ Unit).trans (Homeomorph.homeomorphOfUnique _ _)
  refine ⟨⟨univ, univ, isOpen_univ, isOpen_univ, union_self _, ⟨e⟩, ⟨e⟩⟩, ⟨fun φ ↦ ?_⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin 1)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp)
  obtain ⟨p⟩ : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    ((NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 1)))).2 zero_le_one).to_subtype
  exact ne_neg_of_mem_unit_sphere ℝ p (φ.symm.injective (Subsingleton.elim _ _))

/-- Compactness cannot be dropped from
`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`: `ℝᵐ`, `m > 0`, is covered twice by
itself, but it is not compact, so it is not `Sᵐ`. -/
example {m : ℕ} (hm : 0 < m) :
    (∃ U V : Set (EuclideanSpace ℝ (Fin m)), IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin m)) ∧ Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin m))) ∧
    IsEmpty (EuclideanSpace ℝ (Fin m) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
  have e := Homeomorph.Set.univ (EuclideanSpace ℝ (Fin m))
  refine ⟨⟨univ, univ, isOpen_univ, isOpen_univ, union_self _, ⟨e⟩, ⟨e⟩⟩, ?_⟩
  rw [← not_nonempty_iff, nonempty_homeomorph_sphere_iff_exists_two_euclidean_opens
    (E := EuclideanSpace ℝ (Fin m)) (by simpa using hm) (by simp)]
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hm)
  exact fun ⟨h, _⟩ ↦ (noncompact_univ (EuclideanSpace ℝ (Fin m))) h.isCompact_univ

end Converse

end TauCeti
