/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Reductive.Equiv
import Mathlib.Algebra.Lie.Abelian
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Reductive.Basic

/-!
# Reductive Cartan involutions

A **reductive Cartan involution** of a Lie algebra `L` over an ordered ring `R` is an involutive
automorphism `θ : L ≃ₗ⁅R⁆ L` of a Lie algebra splitting as `L = Z(L) ⊕ [L, L]` whose restriction
to the derived ideal `[L, L]` is a Cartan involution (`LieEquiv.IsReductiveCartanInvolution`).
On the centre `Z(L)`, `θ` may be an arbitrary involution.

When `L = Z(L) ⊕ [L, L]`, the `-1`-eigenspace splits correspondingly as
`𝔭 = (𝔭 ∩ Z(L)) ⊕ (𝔭 ∩ [L, L])` (`LieEquiv.cartanP_eq_sup_center_derivedSeries` and
`LieEquiv.disjoint_cartanP_center_derivedSeries`), and any involution of `Z(L)` together with a
Cartan involution of `[L, L]` assembles into a reductive Cartan involution of `L`
(`LieEquiv.isReductiveCartanInvolution_ofCenterDerived`).

Over a partially ordered field, every Cartan involution is a reductive Cartan involution, and any
Lie algebra admitting a reductive Cartan involution has semisimple finite-dimensional derived ideal
and central radical (`LieAlgebra.HasCentralRadical`). On an abelian Lie algebra, `[L, L] = 0`, so
every involution is a reductive Cartan involution, whereas no nontrivial abelian Lie algebra admits
a Cartan involution in the semisimple sense.

## Main definitions

* `LieEquiv.IsReductiveCartanInvolution`: predicate for a reductive Cartan involution.

## Main results

* `LieEquiv.isReductiveCartanInvolution_iff`: characterization of a reductive Cartan involution.
* `LieEquiv.cartanP_eq_sup_center_derivedSeries` and
  `LieEquiv.disjoint_cartanP_center_derivedSeries`: the splitting
  `𝔭 = (𝔭 ∩ Z(L)) ⊕ (𝔭 ∩ [L, L])`.
* `LieEquiv.isReductiveCartanInvolution_ofCenterDerived`: extending a Cartan involution of `[L, L]`
  by any involution of `Z(L)`.
* `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution`: every Cartan involution is reductive.
* `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical` and
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_derivedSeries`: structure consequences.
* `LieEquiv.isReductiveCartanInvolution_iff_involutive_of_isLieAbelian` and
  `LieEquiv.not_isCartanInvolution_of_isLieAbelian`: the abelian case.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2 and Chapter VII, §2.
-/

public section

open LieAlgebra

namespace LieEquiv

/-! ### Splitting of `𝔭` on a centre/derived direct sum -/

section CommRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- When `L = Z(L) ⊕ [L, L]`, the central and derived parts of `θ.cartanP` are disjoint. -/
theorem disjoint_cartanP_center_derivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (θ : L ≃ₗ⁅R⁆ L) :
    Disjoint (θ.cartanP ⊓ (center R L).toSubmodule)
      (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) :=
  (LieSubmodule.isCompl_toSubmodule.mpr hcompl).disjoint.mono inf_le_right inf_le_right

/-- **Splitting of `𝔭` on a reductive Lie algebra**: when `L = Z(L) ⊕ [L, L]`, every Lie
automorphism `θ` satisfies `𝔭 = (𝔭 ∩ Z(L)) ⊔ (𝔭 ∩ [L, L])`. -/
theorem cartanP_eq_sup_center_derivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanP =
      (θ.cartanP ⊓ (center R L).toSubmodule) ⊔
        (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  let a := prodCenterDerivedEquiv hcompl
  obtain ⟨⟨z, d⟩, hzd⟩ := a.surjective x
  have hsum : (z : L) + d = x := by simpa [a] using hzd
  have hpair : (θ.restrictCenter z, θ.restrictDerivedSeries 1 d) = (-z, -d) := by
    apply a.injective
    calc
      a (θ.restrictCenter z, θ.restrictDerivedSeries 1 d) = θ z + θ d := by
        simp [a]
      _ = θ ((z : L) + d) := (map_add θ _ _).symm
      _ = -x := by rw [hsum, mem_cartanP_iff.mp hx]
      _ = -((z : L) + d) := by rw [hsum]
      _ = a (-z, -d) := by
        simp only [a, prodCenterDerivedEquiv_apply, NegMemClass.coe_neg]
        abel
  have hzP : (z : L) ∈ θ.cartanP := by
    rw [mem_cartanP_iff, ← coe_restrictCenter]
    exact congrArg (fun p : center R L × derivedSeries R L 1 ↦ (p.1 : L)) hpair
  have hdP : (d : L) ∈ θ.cartanP := by
    rw [mem_cartanP_iff, ← coe_restrictDerivedSeries]
    exact congrArg (fun p : center R L × derivedSeries R L 1 ↦ (p.2 : L)) hpair
  exact Submodule.mem_sup.mpr ⟨z, ⟨hzP, z.property⟩, d, ⟨hdP, d.property⟩, hsum⟩

end CommRing

/-! ### Reductive Cartan involutions -/

section PartialOrder

variable {R L M : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- A **reductive Cartan involution** of a Lie algebra `L` over an ordered ring `R`: `L` splits as
`Z(L) ⊕ [L, L]`, `θ` is an involutive automorphism, and the restriction of `θ` to the derived ideal
`[L, L]` is a Cartan involution. On the centre `Z(L)`, `θ` is an arbitrary involution. -/
def IsReductiveCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop :=
  IsCompl (center R L) (derivedSeries R L 1) ∧
    Function.Involutive θ ∧
    (θ.restrictDerivedSeries 1).IsCartanInvolution

/-- Characterization of a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_iff {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsReductiveCartanInvolution ↔
      IsCompl (center R L) (derivedSeries R L 1) ∧
        Function.Involutive θ ∧
        (θ.restrictDerivedSeries 1).IsCartanInvolution :=
  Iff.rfl

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅R⁆ L}

/-- A Lie algebra admitting a reductive Cartan involution splits as `Z(L) ⊕ [L, L]`. -/
theorem isCompl_center_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsCompl (center R L) (derivedSeries R L 1) :=
  hθ.1

/-- A reductive Cartan involution is involutive. -/
theorem involutive (hθ : θ.IsReductiveCartanInvolution) : Function.Involutive θ :=
  hθ.2.1

/-- The restriction of a reductive Cartan involution to `[L, L]` is a Cartan involution. -/
theorem isCartanInvolution_restrictDerivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    (θ.restrictDerivedSeries 1).IsCartanInvolution :=
  hθ.2.2

/-- The restriction of a reductive Cartan involution to the centre is involutive. -/
theorem involutive_restrictCenter (hθ : θ.IsReductiveCartanInvolution) :
    Function.Involutive θ.restrictCenter := fun z ↦
  Subtype.ext (by simpa using hθ.involutive (z : L))

/-- The derived ideal `[L, L]` of a Lie algebra with a reductive Cartan involution is Killing. -/
theorem isKilling_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsKilling R (derivedSeries R L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.isKilling

/-- The derived ideal `[L, L]` of a Lie algebra with a reductive Cartan involution is finite over
the base ring. -/
theorem finite_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    Module.Finite R (derivedSeries R L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.finite

/-- Conjugating a reductive Cartan involution by a Lie algebra equivalence yields a reductive
Cartan involution. -/
theorem conj (hθ : θ.IsReductiveCartanInvolution) (e : L ≃ₗ⁅R⁆ M) :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution := by
  refine ⟨?_, fun y ↦ by simp [hθ.involutive (e.symm y)], ?_⟩
  · rw [← LieSubmodule.isCompl_toSubmodule]
    have hL := LieSubmodule.isCompl_toSubmodule.mpr hθ.isCompl_center_derivedSeries
    have hZ : (center R L).toSubmodule.map (e.toLinearEquiv : L →ₗ[R] M) =
        (center R M).toSubmodule :=
      congrArg LieSubalgebra.toSubmodule e.map_center
    have hD : (derivedSeries R L 1).toSubmodule.map (e.toLinearEquiv : L →ₗ[R] M) =
        (derivedSeries R M 1).toSubmodule :=
      congrArg LieSubalgebra.toSubmodule (e.map_derivedSeries 1)
    rw [← hZ, ← hD]
    exact hL.map (Submodule.orderIsoMapComap e.toLinearEquiv)
  · rw [restrictDerivedSeries_trans, restrictDerivedSeries_trans, restrictDerivedSeries_symm]
    exact hθ.isCartanInvolution_restrictDerivedSeries.conj (e.restrictDerivedSeries 1)

end IsReductiveCartanInvolution

/-- **Extension from the derived ideal and centre**: when `L = Z(L) ⊕ [L, L]`, any involutive
automorphism of the centre and Cartan involution of the derived ideal assemble into a reductive
Cartan involution of `L`. -/
theorem isReductiveCartanInvolution_ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    {θZ : center R L ≃ₗ⁅R⁆ center R L}
    {θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1}
    (hθZ : Function.Involutive θZ) (hθD : θD.IsCartanInvolution) :
    (ofCenterDerived hcompl θZ θD).IsReductiveCartanInvolution := by
  refine ⟨hcompl, fun x ↦ ?_, by rwa [restrictDerivedSeries_ofCenterDerived]⟩
  obtain ⟨⟨z, d⟩, rfl⟩ := (prodCenterDerivedEquiv hcompl).surjective x
  simp [hθZ z, hθD.involutive d]

/-- On an abelian Lie algebra, `[L, L] = 0`, so every involutive automorphism is a reductive Cartan
involution. -/
theorem isReductiveCartanInvolution_iff_involutive_of_isLieAbelian [IsLieAbelian L]
    {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsReductiveCartanInvolution ↔ Function.Involutive θ := by
  have hZ : center R L = ⊤ := (isLieAbelian_iff_center_eq_top R L).mp inferInstance
  have hD : derivedSeries R L 1 = ⊥ := by
    rw [eq_bot_iff, derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
      LieSubmodule.lie_le_iff]
    intro x _ y _
    simp [trivial_lie_zero]
  refine ⟨fun h ↦ h.involutive, fun hθ ↦ ⟨by rw [hZ, hD]; exact isCompl_top_bot, hθ, ?_⟩⟩
  rw [isCartanInvolution_iff]
  refine ⟨fun x ↦ Subtype.ext (by simpa using hθ (x : L)), fun x hx ↦ ?_⟩
  exfalso
  apply hx
  apply Subtype.ext
  have hx' : (x : L) ∈ (⊥ : LieIdeal R L) := hD ▸ x.property
  exact (LieSubmodule.mem_bot _).mp hx'

/-- A nontrivial abelian Lie algebra admits no Cartan involution in the semisimple sense, because
its Killing form vanishes identically. -/
theorem not_isCartanInvolution_of_isLieAbelian [Nontrivial L] [IsLieAbelian L] (θ : L ≃ₗ⁅R⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hpos := hθ.cartanBilinForm_self_pos hx
  have had : ad R L x = 0 := LieAlgebra.ad_eq_zero_of_isLieAbelian x
  have hB : killingForm R L x (θ x) = 0 := by
    rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero]
  rw [cartanBilinForm_apply, hB, neg_zero] at hpos
  exact lt_irrefl 0 hpos

end PartialOrder

/-! ### Structure consequences over a partially ordered field -/

section FieldPartialOrder

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

/-- Every Cartan involution over a partially ordered field is a reductive Cartan involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) : θ.IsReductiveCartanInvolution := by
  refine ⟨by rw [hθ.center_eq_bot, hθ.derivedSeries_one_eq_top]; exact isCompl_bot_top,
    hθ.involutive, ?_⟩
  let e : L ≃ₗ⁅K⁆ derivedSeries K L 1 :=
    (LieSubalgebra.topEquiv (R := K) (L := L)).symm.trans
      (LieEquiv.ofEq (⊤ : LieSubalgebra K L) (derivedSeries K L 1).toLieSubalgebra
        (by rw [hθ.derivedSeries_one_eq_top]; rfl))
  have hconj : θ.restrictDerivedSeries 1 = e.symm.trans (θ.trans e) := by
    ext x
    rw [coe_restrictDerivedSeries]
    rfl
  rw [hconj]
  exact hθ.conj e

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- The derived ideal `[L, L]` of a Lie algebra admitting a reductive Cartan involution is
semisimple. -/
theorem isSemisimple_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsSemisimple K (derivedSeries K L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.isSemisimple

/-- A Lie algebra admitting a reductive Cartan involution is reductive: its radical equals its
centre (`LieAlgebra.HasCentralRadical`). -/
theorem hasCentralRadical (hθ : θ.IsReductiveCartanInvolution) :
    HasCentralRadical K L := by
  have := hθ.isSemisimple_derivedSeries
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

end IsReductiveCartanInvolution

end FieldPartialOrder

end LieEquiv
