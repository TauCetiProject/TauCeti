/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.GroupTheory.Amenable.Foelner

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.GroupTheory.Amenable.DiscreteFoelner
import TauCeti.GroupTheory.Amenable.Subgroup

/-!
# Finite-index subgroups and invariant atoms for amenable groups

If a finite-index subgroup `H` of a topological group `G` is amenable, then `G` is amenable, with
no discreteness assumption on `G`: pushing a left-invariant mean on `UCB H` forward along the
inclusion gives an `H`-left-invariant mean `μ` on `UCB G`, and averaging `f ↦ μ (L_{(s q)⁻¹} f)`
over a section `s` of the finite coset space `G ⧸ H` produces a `G`-left-invariant mean, because
left multiplication permutes the cosets while the discrepancy `(s (g⁻¹ • q))⁻¹ * (g⁻¹ * s q)` lies
in `H`. Combining this with subgroup inheritance on discrete groups shows that Følner sets pass
both ways across finite-index subgroups.

As an application to group actions, if a topological group `G` acts on a measurable space `X` with
measurable singletons preserving a finite measure `μ`, and some point `x : X` with `μ {x} ≠ 0` has
amenable stabilizer in `G`, then `G` is amenable: every point in the orbit `G • x` has the same
nonzero singleton mass `μ {x}`, so the orbit is finite, giving `stabilizer G x` finite index in
`G`.

## Main results

* `TauCeti.Amenable.of_finiteIndex`: a topological group containing a finite-index amenable
  subgroup is amenable.
* `Subgroup.hasFoelnerSets_iff_of_finiteIndex`: a group has Følner sets iff a finite-index
  subgroup does.
* `TauCeti.Amenable.of_measure_singleton_ne_zero`: a topological group preserving a finite measure
  with an atom whose stabilizer is amenable is itself amenable.

## References

* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Proposition G.2.2.
* R. J. Zimmer, *Ergodic Theory and Semisimple Groups*, Birkhäuser (1984), Corollary 3.2.2.
-/

public section

open MeasureTheory MulAction
open scoped BigOperators ENNReal

namespace TauCeti

/-- **Finite-index supergroups of amenable groups.** If a finite-index subgroup `H` of a
topological group `G` is amenable, then `G` is amenable. -/
theorem Amenable.of_finiteIndex {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.FiniteIndex] [Amenable H] : Amenable G := by
  classical
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := H)
  let ι : H →ₜ* G := ⟨H.subtype, continuous_subtype_val⟩
  let μ : Mean G := m.map ι
  let s : G ⧸ H → G := Function.surjInv QuotientGroup.mk_surjective
  have hs (q : G ⧸ H) : (s q : G ⧸ H) = q := Function.surjInv_eq QuotientGroup.mk_surjective q
  let M : Mean G := Mean.mk₀
    { toFun f := 𝔼 q : G ⧸ H, μ (UCB.leftTranslation (s q)⁻¹ f)
      map_add' f₁ f₂ := by simp [-map_inv, Finset.expect_add_distrib]
      map_smul' c f := by simp [-map_inv, Finset.mul_expect] }
    (fun f hf ↦ Finset.expect_nonneg fun q _ ↦ map_nonneg μ <| by
      rwa [← UCB.leftTranslation_le_leftTranslation_iff (g := (s q)⁻¹), map_zero] at hf)
    (by simp [-map_inv, UCB.leftTranslation_apply_one])
  refine ⟨⟨M, Mean.isLeftInvariant_iff.mpr fun g f ↦ ?_⟩⟩
  simp only [M, Mean.mk₀_apply, LinearMap.coe_mk, AddHom.coe_mk]
  -- Left multiplication by `g⁻¹` permutes `G ⧸ H`, and on each coset the section values differ by
  -- an element of `H`, which `μ` absorbs.
  have hcoset (q : G ⧸ H) :
      μ (UCB.leftTranslation (s q)⁻¹ (UCB.leftTranslation g f)) =
        μ (UCB.leftTranslation (s (g⁻¹ • q))⁻¹ f) := by
    have hmem : (s (g⁻¹ • q))⁻¹ * (g⁻¹ * s q) ∈ H := QuotientGroup.eq.mp <| by
      rw [← smul_eq_mul, ← Quotient.smul_mk, hs (g⁻¹ • q), hs q]
    let k : H := ⟨(s (g⁻¹ • q))⁻¹ * (g⁻¹ * s q), hmem⟩
    have hι (y : H) : ι y = y := rfl
    have htrans : UCB.leftTranslation (s q)⁻¹ (UCB.leftTranslation g f) =
        UCB.leftTranslation (ι k⁻¹) (UCB.leftTranslation (s (g⁻¹ • q))⁻¹ f) := by
      ext x
      simp only [UCB.leftTranslation_apply]
      simp [hι, k, mul_assoc]
    rw [htrans]
    exact hm.map_apply_leftTranslation ι k⁻¹ _
  simp_rw [hcoset]
  exact Fintype.expect_equiv (MulAction.toPerm g⁻¹) _ _ fun _ ↦ rfl

/-- If a topological group `G` acts on a measurable space `X` with measurable singletons preserving
a finite measure `μ`, and `x : X` is an atom (`μ {x} ≠ 0`) with amenable stabilizer, then `G` is
amenable. Measurability of the action maps is derived from `Measure.map (g • ·) μ = μ` and
`μ {x} ≠ 0`. -/
theorem Amenable.of_measure_singleton_ne_zero {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MulAction G X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : ∀ g : G, Measure.map (g • ·) μ = μ) {x : X}
    (hx : μ {x} ≠ 0) [Amenable (stabilizer G x)] : Amenable G := by
  have hμ0 : μ ≠ 0 := fun h ↦ hx (by simp [h])
  -- Every point in the orbit of `x` has the same nonzero singleton mass `μ {x}`.
  have horb_mass (g : G) : μ {g • x} = μ {x} := by
    have hae : AEMeasurable (g • ·) μ := by
      by_contra hna
      have : Nonempty X := ⟨x⟩
      have hdirac : μ = Measure.dirac Classical.ofNonempty := by
        rw [← hμ g, Measure.map_of_not_aemeasurable_of_ne_zero hna hμ0]
      exact hna (hdirac ▸ aemeasurable_dirac)
    have hpre : (g • ·) ⁻¹' {g • x} = ({x} : Set X) := by
      ext y
      simp [(MulAction.bijective g).injective.eq_iff]
    calc μ {g • x} = (Measure.map (g • ·) μ) {g • x} := by rw [hμ g]
      _ = μ {x} := by rw [Measure.map_apply_of_aemeasurable hae (measurableSet_singleton _), hpre]
  have htsum : ∑' y : X, μ {y} ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ Set.univ) <| by
      rw [tsum_eq_iSup_sum]
      refine iSup_le fun s ↦ ?_
      rw [MeasureTheory.sum_measure_singleton]
      exact measure_mono (Set.subset_univ _)
  have hfin_orb : (orbit G x).Finite :=
    (ENNReal.finite_const_le_of_tsum_ne_top htsum hx).subset <| by
      rintro _ ⟨g, rfl⟩
      exact (horb_mass g).symm.le
  have : Finite (orbit G x) := hfin_orb.to_subtype
  have : Finite (G ⧸ stabilizer G x) := Finite.of_equiv _ (orbitEquivQuotientStabilizer G x)
  have : (stabilizer G x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact .of_finiteIndex (stabilizer G x)

end TauCeti

namespace Subgroup

/-- A group has Følner sets iff a finite-index subgroup does. -/
theorem hasFoelnerSets_iff_of_finiteIndex {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] : TauCeti.HasFoelnerSets G ↔ TauCeti.HasFoelnerSets H := by
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  rw [← TauCeti.amenable_iff_hasFoelnerSets, ← TauCeti.amenable_iff_hasFoelnerSets]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ TauCeti.Amenable.of_finiteIndex H⟩

end Subgroup
