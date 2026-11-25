/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.CircleFamily
public import TauCeti.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Instances.ZMultiples
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# The circle family as the orbit space of its deck action

The real representative map `Q(p, t) = (p, [t]_p)` of `TauCeti.CircleFamily.representative`
identifies the total family of positive-period circles with a quotient of `ℝ_{>0} × ℝ`. This file
makes that identification explicit. The type synonym `TauCeti.CircleFamily.Cover` of
`ℝ_{>0} × ℝ` carries the action of `Multiplicative ℤ` by the deck translations

`n • (p, t) = (p, t + n p)`,

whose translation length is the period of the fiber, so it varies with the base point. The action
is free and properly discontinuous, and each element acts by an analytic map; hence the orbit
space is an analytic manifold, by `TauCeti.instIsManifoldQuotient`. Two real representatives have
the same image under `Q` exactly when they differ by a deck translation
(`TauCeti.CircleFamily.representative_eq_representative_iff`), so the deck orbits are the fibers
of `Q` (`TauCeti.CircleFamily.Cover.orbitRel_iff`), and the induced map from the orbit space is a
diffeomorphism onto `TauCeti.CircleFamily`
(`TauCeti.CircleFamily.Cover.quotientDiffeomorph`), with its normalized atlas. It keeps the
positive period: the orbit of `(p, t)` is sent to `(p, [t]_p)`, a point of period `p`.

The construction follows `TauCeti.PeriodLine`, the fixed-period case for `AddCircle p`.

## Main definitions

* `TauCeti.CircleFamily.Cover`: the real cover `ℝ_{>0} × ℝ`, with the deck action of
  `Multiplicative ℤ`.
* `TauCeti.CircleFamily.Cover.ofProd`: the identification of `PositivePeriod × ℝ` with the
  cover, and `TauCeti.CircleFamily.Cover.prodDiffeomorph`, the same map as a diffeomorphism.
* `TauCeti.CircleFamily.Cover.quotientDiffeomorph`: the orbit space of the deck action is
  diffeomorphic to the circle family, through the representative map; for `n = 0` its
  `Diffeomorph.toHomeomorph` identifies the two as topological spaces.

## Main results

* `TauCeti.CircleFamily.Cover.instIsCancelSMul`,
  `TauCeti.CircleFamily.Cover.instProperlyDiscontinuousSMul`,
  `TauCeti.CircleFamily.Cover.instContMDiffConstSMul`: the deck action is free, properly
  discontinuous, and by analytic maps.
* `TauCeti.CircleFamily.Cover.orbitRel_iff`: the orbit relation is equality under `Q`.
* `TauCeti.CircleFamily.Cover.quotientDiffeomorph_mk`,
  `TauCeti.CircleFamily.Cover.quotientDiffeomorph_symm_representative`: the diffeomorphism sends
  the orbit of `(p, t)` to `(p, [t]_p)`, and its inverse sends `(p, [t]_p)` back to that orbit.

## References

* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3
  (covering spaces and deck transformations).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace CircleFamily

/-- The real cover `ℝ_{>0} × ℝ` of the circle family, a type synonym for `PositivePeriod × ℝ`
carrying the deck action `n • (p, t) = (p, t + n p)` of `Multiplicative ℤ`. -/
def Cover : Type := PositivePeriod × ℝ

namespace Cover

instance : TopologicalSpace Cover := inferInstanceAs (TopologicalSpace (PositivePeriod × ℝ))

instance : T2Space Cover := inferInstanceAs (T2Space (PositivePeriod × ℝ))

instance : LocallyCompactSpace Cover :=
  haveI : LocallyCompactSpace PositivePeriod := isOpen_Ioi.locallyCompactSpace
  inferInstanceAs (LocallyCompactSpace (PositivePeriod × ℝ))

instance : ChartedSpace (ModelProd ℝ ℝ) Cover :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ ℝ) (PositivePeriod × ℝ))

instance {n : ℕ∞ω} : IsManifold (𝓘(ℝ).prod 𝓘(ℝ)) n Cover :=
  inferInstanceAs (IsManifold (𝓘(ℝ).prod 𝓘(ℝ)) n (PositivePeriod × ℝ))

/-- The identification of `PositivePeriod × ℝ` with the real cover. -/
def ofProd : PositivePeriod × ℝ ≃ Cover := Equiv.refl _

/- `Cover` carries the topology and the manifold structure of `PositivePeriod × ℝ`, and `ofProd` is
the identity map; this is why its smoothness in both directions holds by `contMDiff_id`. -/

/-- The identification of `PositivePeriod × ℝ` with the real cover is a diffeomorphism. -/
def prodDiffeomorph (n : ℕ∞ω) :
    (PositivePeriod × ℝ) ≃ₘ^n⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ).prod 𝓘(ℝ)⟯ Cover where
  toEquiv := ofProd
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id

/-- The diffeomorphism `prodDiffeomorph n` is the identification `ofProd`. -/
@[simp]
theorem coe_prodDiffeomorph (n : ℕ∞ω) : ⇑(prodDiffeomorph n) = ofProd := (rfl)

/-- The inverse of `prodDiffeomorph n` is the inverse identification `ofProd.symm`. -/
@[simp]
theorem coe_prodDiffeomorph_symm (n : ℕ∞ω) : ⇑(prodDiffeomorph n).symm = ofProd.symm := (rfl)

/-! ### The deck action -/

instance : SMul (Multiplicative ℤ) Cover where
  smul k z := ofProd ((ofProd.symm z).1, (ofProd.symm z).2 + k.toAdd * ((ofProd.symm z).1 : ℝ))

/-- The integer `k` acts on the real cover by the deck translation `(p, t) ↦ (p, t + k p)`. -/
@[simp]
theorem smul_ofProd (k : Multiplicative ℤ) (z : PositivePeriod × ℝ) :
    k • ofProd z = ofProd (z.1, z.2 + k.toAdd * (z.1 : ℝ)) := (rfl)

/-- The integer `k` acts on the real cover by the deck translation `(p, t) ↦ (p, t + k p)`, read
in `PositivePeriod × ℝ`. -/
@[simp]
theorem ofProd_symm_smul (k : Multiplicative ℤ) (z : Cover) :
    ofProd.symm (k • z) =
      ((ofProd.symm z).1, (ofProd.symm z).2 + k.toAdd * ((ofProd.symm z).1 : ℝ)) := (rfl)

/-- `Multiplicative ℤ` acts on the real cover by the deck translations. -/
instance : MulAction (Multiplicative ℤ) Cover where
  one_smul z := ofProd.symm.injective (by simp)
  mul_smul j k z := ofProd.symm.injective (by simp; ring)

/-- The deck translation by `k` is the analytic map `(p, t) ↦ (p, t + k p)`. -/
private theorem contMDiff_deck (k : ℤ) {n : ℕ∞ω} :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n
      fun z : PositivePeriod × ℝ ↦ (z.1, z.2 + k * (z.1 : ℝ)) :=
  contMDiff_fst.prodMk
    (contMDiff_snd.add (contMDiff_const.mul (contMDiff_subtypeVal.comp contMDiff_fst)))

/-- The deck action is jointly continuous. -/
instance : ContinuousSMul (Multiplicative ℤ) Cover where
  continuous_smul := by
    -- The group is discrete, so continuity can be checked one deck translation at a time.
    refine continuous_prod_of_discrete_left.2 fun k ↦ ?_
    exact (prodDiffeomorph 0).continuous.comp
      ((contMDiff_deck k.toAdd (n := 0)).continuous.comp (prodDiffeomorph 0).symm.continuous)

/-- The deck action is by analytic maps. -/
instance instContMDiffConstSMul {n : ℕ∞ω} :
    ContMDiffConstSMul (𝓘(ℝ).prod 𝓘(ℝ)) n (Multiplicative ℤ) Cover where
  contMDiff_const_smul k :=
    (prodDiffeomorph n).contMDiff.comp
      ((contMDiff_deck k.toAdd).comp (prodDiffeomorph n).symm.contMDiff)

/-- The deck action is free: a translation by a nonzero multiple of the positive period has no
fixed point. -/
instance instIsCancelSMul : IsCancelSMul (Multiplicative ℤ) Cover where
  left_cancel' k z w h := by
    have h' := congrArg ofProd.symm h
    simp only [ofProd_symm_smul, Prod.mk.injEq] at h'
    obtain ⟨h₁, h₂⟩ := h'
    rw [h₁, add_left_inj] at h₂
    exact ofProd.symm.injective (Prod.ext h₁ h₂)
  right_cancel' j k z h := by
    have h' := congrArg (fun w ↦ (ofProd.symm w).2) h
    simp only [ofProd_symm_smul, add_right_inj] at h'
    exact Multiplicative.toAdd.injective
      (Int.cast_injective (mul_right_cancel₀ (ofProd.symm z).1.property.ne' h'))

/-- The deck action is properly discontinuous: only finitely many deck translations move a compact
set to meet another compact set. -/
instance instProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul (Multiplicative ℤ) Cover where
  finite_disjoint_inter_image {K L} hK hL := by
    -- If `k • z ∈ L` for some `z ∈ K`, then `k` is the value at `(k • z, z)` of the continuous
    -- function `(w, z) ↦ (w₂ - z₂) / z₁`, which lies in a compact set.
    let f : Cover × Cover → ℝ := fun x ↦
      ((ofProd.symm x.1).2 - (ofProd.symm x.2).2) / ((ofProd.symm x.2).1 : ℝ)
    have hf : Continuous f := by
      have hc := (prodDiffeomorph 0).symm.continuous
      exact ((continuous_snd.comp (hc.comp continuous_fst)).sub
        (continuous_snd.comp (hc.comp continuous_snd))).div
        (continuous_subtypeVal.comp (continuous_fst.comp (hc.comp continuous_snd)))
        fun x ↦ (ofProd.symm x.2).1.property.ne'
    have hfin := tendsto_cofinite_cocompact_iff.mp Int.tendsto_coe_cofinite _
      ((hL.prod hK).image hf)
    refine (hfin.preimage Multiplicative.toAdd.injective.injOn).subset fun k hk ↦ ?_
    obtain ⟨_, ⟨z, hz, rfl⟩, hkz⟩ := hk
    refine ⟨(k • z, z), ⟨hkz, hz⟩, ?_⟩
    simp only [f, ofProd_symm_smul, add_sub_cancel_left]
    exact mul_div_cancel_right₀ _ (ofProd.symm z).1.property.ne'

/-! ### The orbit space -/

/-- Two points of the real cover lie in one deck orbit exactly when they have the same image under
the representative map. -/
theorem orbitRel_iff {z w : Cover} :
    MulAction.orbitRel (Multiplicative ℤ) Cover z w ↔
      representative (ofProd.symm z) = representative (ofProd.symm w) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, representative_eq_representative_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨-k.toAdd, ?_⟩
    simp only [ofProd_symm_smul, Int.cast_neg]
    ext <;> simp
  · rintro ⟨k, hk⟩
    refine ⟨Multiplicative.ofAdd (-k), ofProd.symm.injective ?_⟩
    rw [ofProd_symm_smul, hk]
    simp

/-- The representative map, read on the real cover. -/
private abbrev coverRep (z : Cover) : CircleFamily := representative (ofProd.symm z)

private theorem coverRep_surjective : Function.Surjective coverRep :=
  representative_surjective.comp ofProd.symm.surjective

private theorem isLocalDiffeomorph_coverRep (n : ℕ∞ω) :
    IsLocalDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n coverRep := fun z ↦
  ((prodDiffeomorph n).symm.isLocalDiffeomorph z).comp _ _ (isLocalDiffeomorph_representative n _)

/-- The map from the orbit space to the circle family induced by the representative map. -/
private def quotientEquiv :
    MulAction.orbitRel.Quotient (Multiplicative ℤ) Cover ≃ CircleFamily :=
  Equiv.ofBijective (MulAction.orbitRelQuotientLift coverRep fun k z ↦ (orbitRel_iff.1 ⟨k, rfl⟩))
    ⟨fun x y hxy ↦ by
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      exact Quotient.sound (orbitRel_iff.2 (by simpa using hxy)),
    fun y ↦ (coverRep_surjective y).elim fun z hz ↦ ⟨Quotient.mk _ z, by simpa using hz⟩⟩

private theorem quotientEquiv_mk (z : Cover) : quotientEquiv (Quotient.mk _ z) = coverRep z :=
  MulAction.orbitRelQuotientLift_mk z

variable (n : ℕ∞ω)

/-- The orbit projection of the real cover is an analytic local diffeomorphism. -/
private theorem isLocalDiffeomorph_quotientMk_cover :
    IsLocalDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n
      (Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) Cover)) :=
  isLocalDiffeomorph_quotientMk

/-- **The deck quotient of the circle family.** The orbit space of the deck action of
`Multiplicative ℤ` on the real cover is diffeomorphic to the circle family, by the map induced by
the representative map `(p, t) ↦ (p, [t]_p)`. -/
def quotientDiffeomorph :
    MulAction.orbitRel.Quotient (Multiplicative ℤ) Cover ≃ₘ^n⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ).prod 𝓘(ℝ)⟯
      CircleFamily :=
  -- The orbit projection and the representative map are surjective local diffeomorphisms out of
  -- the real cover, hence submersions, and `quotientEquiv` commutes with them.
  quotientEquiv.diffeomorphOfSubmersions
    ((isLocalDiffeomorph_quotientMk_cover n).isSubmersion_comp Manifold.IsSubmersion.id)
    Quotient.mk_surjective
    ((isLocalDiffeomorph_coverRep n).isSubmersion_comp Manifold.IsSubmersion.id)
    (funext quotientEquiv_mk)

/-- The deck quotient diffeomorphism sends the orbit of `(p, t)` to `(p, [t]_p)`. -/
@[simp]
theorem quotientDiffeomorph_mk (z : Cover) :
    quotientDiffeomorph n (Quotient.mk _ z) = representative (ofProd.symm z) := by
  rw [quotientDiffeomorph, Equiv.diffeomorphOfSubmersions_apply, quotientEquiv_mk]

/-- The inverse deck quotient diffeomorphism sends `(p, [t]_p)` to the orbit of `(p, t)`. -/
@[simp]
theorem quotientDiffeomorph_symm_representative (z : PositivePeriod × ℝ) :
    (quotientDiffeomorph n).symm (representative z) = Quotient.mk _ (ofProd z) :=
  (quotientDiffeomorph n).symm_apply_eq.2 (by simp)

end Cover

end CircleFamily

end TauCeti
