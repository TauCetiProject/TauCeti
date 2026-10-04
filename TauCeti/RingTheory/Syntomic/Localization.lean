/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Syntomic.StandardSyntomic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.KrullDimension.Presentation

/-!
# Standard syntomic algebras and localization

Standard syntomic algebras of relative dimension `n` are stable under composition with
localizations away from an element, on either side:

* if `S` is standard syntomic of relative dimension `n` over `R` and `g ∈ S`, then so is `S[1/g]`;
* if `r ∈ R` and `T` is standard syntomic of relative dimension `n` over `R[1/r]`, then `T` is
  standard syntomic of relative dimension `n` over `R`.

In both cases a presentation is obtained by composing with the presentation of a localization by
one generator `x` and one relation `rx - 1`, which adds one generator and one relation. The content
is the fibre dimension. In the first case the fibre of `S[1/g]` over a prime `p` is the localization
of the fibre `κ(p) ⊗[R] S` at `1 ⊗ g`. This fibre is a global complete intersection over `κ(p)`, so
each of its nonzero localizations still has dimension `n`
(`Algebra.Presentation.ringKrullDim_eq_of_isLocalization_away`). In the second case a nonempty
fibre lies over a prime `p` not containing `r`, and `κ(p) ⊗[R] T` is then the fibre
`κ(p) ⊗[R[1/r]] T` of `T` over `R[1/r]`.

These two stability properties, together with stability under base change, are what make
"locally standard syntomic of relative dimension `n`" a property of ring maps that is local on the
source and the target, and hence define syntomic morphisms of schemes of relative dimension `n`.

## Main results

* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.trans_localization_away`: if `S` is
  standard syntomic of relative dimension `n` over `R`, so is every localization `S[1/g]`.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.localization_away_trans`: an algebra that
  is standard syntomic of relative dimension `n` over `R[1/r]` is standard syntomic of relative
  dimension `n` over `R`.

## References

* The Stacks Project, Commutative Algebra, Section *Syntomic morphisms*: the stability of relative
  global complete intersections under localization `S → S_g`, and the locality of syntomic ring
  maps.
-/

public section

open TensorProduct

namespace TauCeti

namespace Algebra.IsStandardSyntomicOfRelativeDimension

variable {n : ℕ} {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- If `S` is standard syntomic of relative dimension `n` over `R`, then so is its localization
`S[1/g]` away from any `g ∈ S`. -/
theorem trans_localization_away [h : IsStandardSyntomicOfRelativeDimension n R S] (g : S)
    [IsLocalization.Away g T] : IsStandardSyntomicOfRelativeDimension n R T := by
  have := h.flat
  have : Module.Flat S T := IsLocalization.flat T (.powers g)
  have : Module.Flat R T := .trans R S T
  obtain ⟨ι, σ, _, _, P, hP⟩ := h.exists_presentation
  let L := _root_.Algebra.Presentation.localizationAway T g
  refine (L.comp P).isStandardSyntomicOfRelativeDimension
    (by simp [Nat.card_sum, hP]; omega) fun p _ _ ↦ ?_
  -- The fibre `κ(p) ⊗[R] T` is the localization of the fibre `κ(p) ⊗[R] S` at `1 ⊗ g`, and the
  -- base change of `P` presents `κ(p) ⊗[R] S` over `κ(p)` with `n + c` generators and `c`
  -- relations.
  let e := IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField g T
  have : Nontrivial (Localization.Away ((1 : p.ResidueField) ⊗ₜ[R] g)) := e.symm.toEquiv.nontrivial
  have hdim : (P.baseChange p.ResidueField).dimension = n := by
    simp [_root_.Algebra.Presentation.dimension, hP]
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← hdim]
  exact (P.baseChange p.ResidueField).ringKrullDim_eq_of_isLocalization_away
    (hdim ▸ h.ringKrullDim_fiber_le p) ((1 : p.ResidueField) ⊗ₜ[R] g) _

/-- If `T` is standard syntomic of relative dimension `n` over the localization `S = R[1/r]` of `R`
away from `r`, then `T` is standard syntomic of relative dimension `n` over `R`. -/
theorem localization_away_trans (r : R) [IsLocalization.Away r S]
    [h : IsStandardSyntomicOfRelativeDimension n S T] :
    IsStandardSyntomicOfRelativeDimension n R T := by
  have := h.flat
  have : Module.Flat R S := IsLocalization.flat S (.powers r)
  have : Module.Flat R T := .trans R S T
  obtain ⟨ι, σ, _, _, Q, hQ⟩ := h.exists_presentation
  let L := _root_.Algebra.Presentation.localizationAway S r
  refine (Q.comp L).isStandardSyntomicOfRelativeDimension
    (by simp [Nat.card_sum, hQ]; omega) fun p _ _ ↦ ?_
  -- A nonempty fibre lies over a prime not containing `r`: the image of `r` in `κ(p) ⊗[R] T` is a
  -- unit, since `r` is invertible in `T`.
  have hr : IsUnit (algebraMap R p.ResidueField r) := by
    by_contra hr
    rw [isUnit_iff_ne_zero, ne_eq, not_not] at hr
    have hu := ((IsLocalization.Away.algebraMap_isUnit r).map (algebraMap S T)).map
      (_root_.Algebra.TensorProduct.includeRight : T →ₐ[R] p.Fiber T)
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber T), hr,
      map_zero, isUnit_zero_iff] at hu
    exact zero_ne_one hu
  -- So `κ(p)` is an algebra over `S = R[1/r]`, and the fibre of `T` over `R` at `p` is its fibre
  -- `κ(p) ⊗[S] T` over `S`.
  let : Algebra S p.ResidueField := (IsLocalization.Away.lift r hr).toAlgebra
  have : IsScalarTower R S p.ResidueField := .of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (M := .powers r) (S := S) _ x).symm
  let e := IsLocalization.algebraTensorEquiv (.powers r) S p.ResidueField T
  have : Nontrivial (p.ResidueField ⊗[S] T) := e.toEquiv.nontrivial
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv, h.ringKrullDim_tensorProduct_of_field]

end Algebra.IsStandardSyntomicOfRelativeDimension

end TauCeti
