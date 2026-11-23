/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FixedPoints.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.RingTheory.Invariant.Coinvariant

/-!
# Smoothness of fixed-point closed subgroup schemes under tame finite group actions

For a commutative Hopf algebra `H` over `R` and a finite group action `ρ : Θ →* Aut H` with
`IsUnit (Nat.card Θ : R)`, Edixhoven's theorem (`TauCeti.smooth_quotient_of_eq_iSup_span_range_sub`,
Edixhoven 1992, Propositions 3.1 and 3.4) shows that `fixedPoints (fun θ ↦ (ρ θ).asIso.hom)`
preserves formal smoothness and smoothness over `R`.

## Main declarations

* `TauCeti.CommHopfAlgCat.formallySmooth_fixedPoints`,
  `TauCeti.CommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints`: formal smoothness and smoothness
  of `fixedPoints (fun θ ↦ (ρ θ).asIso.hom)` when `IsUnit (Nat.card Θ : R)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints`,
  `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: finite-type counterparts producing the
  smooth quotient `H ⟶ H'` representing `Θ`-fixed points over every `R`-algebra.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), pp. 293–295.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w w'

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- **Edixhoven's formal smoothness theorem** for affine group schemes under tame finite actions. -/
theorem formallySmooth_fixedPoints {H : _root_.CommHopfAlgCat.{v} R} [Algebra.FormallySmooth R H]
    {Θ : Type w} [Group Θ] [_root_.Finite Θ] (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    Algebra.FormallySmooth R (fixedPoints fun θ ↦ (ρ θ).asIso.hom) := by
  refine formallySmooth_quotient_of_eq_iSup_span_range_sub
    ((_root_.CommHopfAlgCat.autToAlgEquiv H).comp ρ) ?_ hΘ
  simp [_root_.CommHopfAlgCat.autToAlgEquiv_apply, fixedPointsHopfIdeal_toIdeal]

/-- **Edixhoven's smoothness theorem** for affine group schemes under tame finite actions. -/
theorem smoothCommHopfAlgProperty_fixedPoints {H : _root_.CommHopfAlgCat.{v} R}
    (hH : smoothCommHopfAlgProperty R H) {Θ : Type w} [Group Θ] [_root_.Finite Θ]
    (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (fixedPoints fun θ ↦ (ρ θ).asIso.hom) := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  refine smooth_quotient_of_eq_iSup_span_range_sub
    ((_root_.CommHopfAlgCat.autToAlgEquiv H).comp ρ) ?_ hΘ
  simp [_root_.CommHopfAlgCat.autToAlgEquiv_apply, fixedPointsHopfIdeal_toIdeal]

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [CommRing k]

/-- **Edixhoven's smoothness theorem** in `FiniteTypeCommHopfAlgCat`. -/
theorem smoothCommHopfAlgProperty_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) {Θ : Type w} [Group Θ] [_root_.Finite Θ]
    (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    smoothCommHopfAlgProperty k (fixedPoints fun θ ↦ (ρ θ).asIso.hom).obj := by
  simpa only [MonoidHom.comp_apply, Functor.mapAut_apply_asIso, Functor.mapIso_hom,
    forget₂_commHopfAlgCat_map] using
    CommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints hH
      (((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
        (_root_.CommHopfAlgCat.{v} k)).mapAut H).comp ρ) hΘ

/-- **Fixed-point closed subgroup scheme of a smooth affine group under a tame finite group**
(Edixhoven 1992, Propositions 3.1 and 3.4). -/
theorem smooth_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) (Θ : Type w) [Group Θ] [_root_.Finite Θ]
    (ρ : Θ →* Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} k) (f : H ⟶ H'),
      smoothCommHopfAlgProperty k H'.obj ∧ Function.Surjective f.hom.hom ∧
      ∀ (R : Type w') [CommRing R] [Algebra k R],
        Set.range (BialgHom.mapDomain (A := R) (f.hom.hom : (H : Type v) →ₐc[k] H')) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := R)
              ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[k] H) g = g} :=
  ⟨fixedPoints fun θ ↦ (ρ θ).asIso.hom, mkFixedPoints fun θ ↦ (ρ θ).asIso.hom,
    smoothCommHopfAlgProperty_fixedPoints H hH ρ hΘ,
    mkFixedPoints_surjective fun θ ↦ (ρ θ).asIso.hom,
    fun R _ _ ↦ range_mapDomain_mkFixedPoints (fun θ ↦ (ρ θ).asIso.hom) R⟩

end FiniteTypeCommHopfAlgCat

end TauCeti
