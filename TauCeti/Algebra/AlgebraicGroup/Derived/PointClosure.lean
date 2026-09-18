/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.Solvable
public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
import TauCeti.RingTheory.TensorProduct.PointSeparation

/-!
# Derived subgroups of closures of point subgroups

The derived closed subgroup of the reduced closure of a rational-point subgroup `S` is the
reduced closure of `⁅S, S⁆`. This holds over any field: the points of `S` separate functions
on their own closure, and their pairs therefore separate its tensor square. In particular,
this comparison can be iterated along the abstract derived series.

For a reduced finite-type affine group over an algebraically closed field, specializing to
all rational points identifies the derived defining ideal with the vanishing ideal of the
abstract commutator subgroup. Thus the all-points comparison is a specialization of the
subgroup-closure comparison.

If the rational points of the ambient group have finite derived length, then commutators of
closures lie in the closure of the commutator
(`TauCeti.HopfIdeal.commutator_quotientPointsSubgroup_vanishingIdeal_le`), so the rational points
of the derived subgroup have strictly smaller derived length. This is the measure the Lie--Kolchin
induction decreases.

## Main declarations

* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal_eq_vanishingIdeal_commutator`: the derived
  subgroup is the closure of the abstract commutator subgroup of rational points.
* `TauCeti.CommHopfAlgCat.derivedSeries_points_derived_eq_bot`: if the rational points have
  derived length at most `n + 1`, those of the derived subgroup have derived length at most `n`.

## References

* A. Borel, *Linear Algebraic Groups*, §2.3 and §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.CommHopfAlgCat

noncomputable section

-- The subgroup-closure proof adapts the in-repository proof of
-- `derivedDefiningIdeal_eq_vanishingIdeal_commutator` previously in this module.

section Field

variable {k : Type*} [Field k] {H : _root_.CommHopfAlgCat k}

private theorem map_vanishingIdeal_commutator_le_derivedDefiningIdeal
    (S : Subgroup (WithConv (H →ₐ[k] k))) :
    (HopfIdeal.vanishingIdeal ⁅S, S⁆).map
        (mkQuotient H (HopfIdeal.vanishingIdeal S)).hom ≤
      derivedDefiningIdeal (quotient H
        (HopfIdeal.vanishingIdeal S)) := by
  let A := H
  let I := HopfIdeal.vanishingIdeal S
  let lift (g : S) := liftQuotientPoint A I (CommAlgCat.of k k) g.val
    (fun x hx ↦ (HopfIdeal.mem_vanishingIdeal S x).mp hx g)
  have hsep := HopfIdeal.eq_zero_of_forall_liftQuotientPoint_apply_eq_zero S
  rw [le_derivedDefiningIdeal_iff]
  intro x hx
  obtain ⟨x, hmem, rfl⟩ :=
    (HopfIdeal.mem_map_iff_of_surjective (mkQuotient_surjective A I)).mp hx
  apply RingHom.mem_ker.mpr
  apply tensor_eq_zero_of_forall_productMap_eq_zero
    (fun g : S ↦ (lift g).ofConv) (fun g : S ↦ (lift g).ofConv) hsep hsep
  intro g h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← AlgHom.comp_apply, HopfAlgebra.productMap_comp_commutatorAlgHom]
  rw [commutator_liftQuotientPoint_apply_mkQuotient]
  exact (HopfIdeal.mem_vanishingIdeal ⁅S, S⁆ x).mp hmem
    ⟨⁅g.val, h.val⁆, Subgroup.commutator_mem_commutator g.2 h.2⟩

/-- Taking the derived closed subgroup commutes with taking the reduced closure of a
rational-point subgroup. The equality is stated as equality of defining ideals in the
ambient coordinate algebra. -/
theorem comapOfSurjective_derivedDefiningIdeal_quotient_vanishingIdeal_eq_vanishingIdeal_commutator
    (S : Subgroup (WithConv (H →ₐ[k] k))) :
    (derivedDefiningIdeal (quotient H
      (HopfIdeal.vanishingIdeal S))).comapOfSurjective
        (mkQuotient H (HopfIdeal.vanishingIdeal S)).hom
        (mkQuotient_surjective _ _) = HopfIdeal.vanishingIdeal ⁅S, S⁆ := by
  let A := H
  let I := HopfIdeal.vanishingIdeal S
  let q := (mkQuotient A I).hom
  apply le_antisymm
  · apply (HopfIdeal.le_vanishingIdeal_iff _ _).mpr
    apply Subgroup.commutator_le.mpr
    intro g hg h hh
    let g' := liftQuotientPoint A I (CommAlgCat.of k k) g
      (fun x hx ↦ (HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨g, hg⟩)
    let h' := liftQuotientPoint A I (CommAlgCat.of k k) h
      (fun x hx ↦ (HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨h, hh⟩)
    apply (mem_quotientPointsSubgroup_iff A _ _ _).mpr
    intro x hx
    have hzero := (mem_quotientPointsSubgroup_iff (quotient A I) _ _ _).mp
      (commutator_mem_derivedPointsSubgroup (quotient A I) (CommAlgCat.of k k) g' h')
      (q x) (HopfIdeal.mem_comapOfSurjective.mp hx)
    rw [commutator_liftQuotientPoint_apply_mkQuotient] at hzero
    exact hzero
  · exact (HopfIdeal.map_le_iff_le_comapOfSurjective (mkQuotient_surjective A I)).mp
      (map_vanishingIdeal_commutator_le_derivedDefiningIdeal S)

end Field

variable {k H : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H]

/-- The derived subgroup is the reduced closed subgroup generated by the abstract
commutator subgroup of rational points. -/
theorem derivedDefiningIdeal_eq_vanishingIdeal_commutator :
    derivedDefiningIdeal (R := k) H =
      HopfIdeal.vanishingIdeal (commutator (WithConv (H →ₐ[k] k))) := by
  have h :=
    comapOfSurjective_derivedDefiningIdeal_quotient_vanishingIdeal_eq_vanishingIdeal_commutator
      (H := _root_.CommHopfAlgCat.of k H) ⊤
  rw [HopfIdeal.vanishingIdeal_top] at h
  have hbot := comapOfSurjective_derivedDefiningIdeal
    (quotientBotIso (_root_.CommHopfAlgCat.of k H)).symm
  simp only [CategoryTheory.Iso.symm_hom, quotientBotIso_inv] at hbot
  rw [hbot] at h
  simpa only [← commutator_def] using h

/-- A function vanishes on the derived subgroup exactly when it vanishes on every
element of the abstract commutator subgroup of rational points. -/
@[simp] theorem mem_derivedDefiningIdeal_iff_forall_commutator_apply_eq_zero (x : H) :
    x ∈ derivedDefiningIdeal (R := k) H ↔
      ∀ g : commutator (WithConv (H →ₐ[k] k)), g.val.ofConv x = 0 := by
  rw [derivedDefiningIdeal_eq_vanishingIdeal_commutator, HopfIdeal.mem_vanishingIdeal]

/-- **The derived subgroup has strictly shorter derived length.** If the rational points of a
reduced finite-type affine group over an algebraically closed field have derived length at most
`n + 1`, then the rational points of its scheme-theoretic derived subgroup have derived length at
most `n`. -/
theorem derivedSeries_points_derived_eq_bot {n : ℕ}
    (hn : derivedSeries (WithConv (H →ₐ[k] k)) (n + 1) = ⊥) :
    derivedSeries (WithConv (quotient (_root_.CommHopfAlgCat.of k H)
      (derivedDefiningIdeal (R := k) H) →ₐ[k] k)) n = ⊥ := by
  let A := _root_.CommHopfAlgCat.of k H
  let cl (S : Subgroup (WithConv (H →ₐ[k] k))) :=
    quotientPointsSubgroup A (HopfIdeal.vanishingIdeal S) (CommAlgCat.of k k)
  let φ := (quotientPointsHom A (derivedDefiningIdeal H) (CommAlgCat.of k k)).hom
  -- The `i`-th derived subgroup of the derived points lies in the closure of the `(i + 1)`-st
  -- derived subgroup of the ambient points.
  have hle (i : ℕ) : (derivedSeries _ i).map φ ≤ cl (derivedSeries _ (i + 1)) := by
    induction i with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map, derivedSeries_one]
      -- `quotientPointsSubgroup` is defined as the range of `quotientPointsHom`.
      exact (congrArg (fun I ↦ quotientPointsSubgroup A I (CommAlgCat.of k k))
        derivedDefiningIdeal_eq_vanishingIdeal_commutator).le
    | succ i ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, derivedSeries_succ _ (i + 1)]
      exact (Subgroup.commutator_mono ih ih).trans
        (HopfIdeal.commutator_quotientPointsSubgroup_vanishingIdeal_le _ _)
  have hmap : (derivedSeries _ n).map φ = ⊥ := by
    have h := hle n
    rw [hn] at h
    exact le_bot_iff.mp (h.trans HopfIdeal.quotientPointsSubgroup_vanishingIdeal_bot.le)
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (quotientPointsHom_injective A _ (CommAlgCat.of k k))).mp hmap

end

end TauCeti.CommHopfAlgCat
