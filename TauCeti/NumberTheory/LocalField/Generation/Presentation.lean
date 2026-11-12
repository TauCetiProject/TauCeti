/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
import TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup
import TauCeti.Topology.Algebra.Group.Profinite.Gaschutz

/-!
# Free presentations lifting prescribed local Galois generators

Let `L/K` be a finite Galois extension of finite extensions of `ℚ_p`. Every generating
family of `Gal(L/K)` with at least `[K : ℚ_p] + 2` members lifts to a topological generating family
of `G_K`. Consequently it is the image of the free generators under a continuous
surjection onto `G_K` that commutes with restriction to `L`.

The compatibility is retained for every element of the free profinite group. Restricting
this presentation to its relation subgroup therefore gives the arithmetic relation map
on pro-`p` abelianizations, which Lyndon's isomorphism and local reciprocity read as a
surjection onto the completed multiplicative group of `L`.

## Main results

* `TauCeti.exists_surjective_presentation_of_card_le`: a free profinite presentation of
  `G_K` lifting any prescribed generating family of `Gal(L/K)` of size at least `[K : ℚ_p] + 2`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.2)(i).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 2.5.4, for Gaschütz's lemma.
-/

public section

namespace TauCeti

/-- Every generating family of a finite local Galois group with at least `[K : ℚ_p] + 2` members
lifts to a continuous surjective free profinite presentation of `G_K`. The presentation
commutes with restriction along the chosen embedding of `L` into the separable closure. -/
theorem exists_surjective_presentation_of_card_le (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [Module.Finite ℚ_[p] L]
    [IsGalois K L] {ι : Type} [Fintype ι] {g : ι → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hι : Module.finrank ℚ_[p] K + 2 ≤ Fintype.card ι)
    (j : L →ₐ[K] SeparableClosure K) :
    ∃ φ : freeProfiniteGroup ι →ₜ* AbsoluteGaloisGroup K,
      Function.Surjective φ ∧
        ∀ z, j.restrictNormalHom (φ z) = freeProfiniteGroup.lift g z := by
  classical
  have : Module.Finite ℚ_[p] K := .left ℚ_[p] K L
  have : FiniteDimensional K L := .right ℚ_[p] K L
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsAlgebraic ℚ_[p] K := Algebra.IsAlgebraic.of_finite ℚ_[p] K
  let _ := algebraicExtensionValuativeRel ℚ_[p] K
  let _ := algebraicExtensionNormedFieldTopology ℚ_[p] K
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] K
  have := algebraicExtension_valuativeExtension ℚ_[p] K
  -- Pad a generating family of `G_K` with identities to the required indexing type.
  obtain ⟨x, hx⟩ := exists_tuple_generating_mod_wildInertiaCommutator p K
  have hxgen := topologicalClosure_eq_top_of_sup_wildInertiaCommutator hx
  let a := absoluteGaloisGroupRestrictEquiv K
  obtain ⟨e : Fin (Module.finrank ℚ_[p] K + 2) ↪ ι⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin (Module.finrank ℚ_[p] K + 2)) (β := ι) (by simpa using hι)
  let t := Function.extend e (a ∘ x) (fun _ ↦ 1)
  have hxt : Set.range (a ∘ x) ⊆ Set.range t := by
    simpa only [t, Function.extend_comp e.injective] using Set.range_comp_subset_range e t
  have ht : (Subgroup.closure (Set.range t)).topologicalClosure = ⊤ := by
    apply eq_top_mono (Subgroup.topologicalClosure_mono (Subgroup.closure_mono hxt))
    simpa [Set.range_comp] using
      topologicalClosure_closure_image_eq_top (f := a.toMulEquiv.toMonoidHom)
        hxgen a.continuous a.surjective.denseRange
  -- Gaschütz's lemma replaces that family by one lifting the prescribed generators.
  let r : AbsoluteGaloisGroup K →ₜ* (L ≃ₐ[K] L) :=
    (quotientGaloisSubgroupEquiv K L j : _ →ₜ* _).comp
      (Subgroup.quotientMkContinuousMonoidHom (galoisSubgroup K L j).toSubgroup)
  have hr (σ) : r σ = j.restrictNormalHom σ := by simp [r]
  have hrsurj : Function.Surjective r := fun σ ↦ by
    obtain ⟨τ, hτ⟩ := j.restrictNormalHom_surjective σ
    exact ⟨τ, (hr τ).trans hτ⟩
  obtain ⟨y, hy, hygen⟩ := exists_comp_eq_and_topologicalClosure_closure_range_eq_top
    r.continuous hrsurj ht (by rw [hg]; exact eq_top_iff.mpr (Subgroup.le_topologicalClosure _))
  refine ⟨freeProfiniteGroup.lift y, freeProfiniteGroup.lift_surjective
    (Subgroup.dense_iff_topologicalClosure_eq_top.mpr hygen), fun z ↦ ?_⟩
  have hcomp : r.comp (freeProfiniteGroup.lift y) = freeProfiniteGroup.lift g := by
    rw [freeProfiniteGroup.comp_lift]
    exact congrArg freeProfiniteGroup.lift (by simpa using hy)
  exact (hr _).symm.trans (DFunLike.congr_fun hcomp z)

end TauCeti
