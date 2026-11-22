/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Reductive.Equiv
import Mathlib.Algebra.Lie.Abelian
import TauCeti.Algebra.Lie.Reductive.Basic

/-!
# Reductive Cartan involutions

A **reductive Cartan involution** of a Lie algebra `L` over an ordered field is an involutive
automorphism `θ : L ≃ₗ⁅K⁆ L` of a Lie algebra splitting as `L = Z(L) ⊕ [L, L]` whose restriction
to `[L, L]` is a Cartan involution (`LieEquiv.IsReductiveCartanInvolution`).

## Main definitions and results

* `LieEquiv.IsReductiveCartanInvolution`, `LieEquiv.isReductiveCartanInvolution_iff`,
  `LieEquiv.isReductiveCartanInvolution_conj_iff`,
  `LieEquiv.cartanP_eq_sup_center_derivedSeries`,
  `LieEquiv.isReductiveCartanInvolution_ofCenterDerived_iff`,
  `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution`,
  `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical`,
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_derivedSeries`,
  `LieEquiv.isReductiveCartanInvolution_iff_involutive_of_isLieAbelian`.

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
    θ.cartanP = (θ.cartanP ⊓ (center R L).toSubmodule) ⊔
      (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  obtain ⟨⟨z, d⟩, hzd⟩ := (prodCenterDerivedEquiv hcompl).surjective x
  have hsum : (z : L) + d = x := by simpa using hzd
  have hpair : (θ.restrictCenter z, θ.restrictDerivedSeries 1 d) = (-z, -d) := by
    apply (prodCenterDerivedEquiv hcompl).injective
    simp only [coe_toLieHom, prodCenterDerivedEquiv_apply, coe_restrictCenter,
      coe_restrictDerivedSeries, NegMemClass.coe_neg, ← map_add, hsum, mem_cartanP.mp hx]
    rw [← hsum, neg_add]
  refine Submodule.mem_sup.mpr ⟨z, ⟨?_, z.property⟩, d, ⟨?_, d.property⟩, hsum⟩
  · rw [SetLike.mem_coe, mem_cartanP, ← coe_restrictCenter]
    exact congrArg (fun p : center R L × derivedSeries R L 1 ↦ (p.fst : L)) hpair
  · rw [SetLike.mem_coe, mem_cartanP, ← coe_restrictDerivedSeries]
    exact congrArg (fun p : center R L × derivedSeries R L 1 ↦ (p.snd : L)) hpair

end CommRing

/-! ### Reductive Cartan involutions -/

section LinearOrder

variable {K L M : Type*} [Field K] [LinearOrder K]
  [LieRing L] [LieAlgebra K L] [LieRing M] [LieAlgebra K M]

/-- A **reductive Cartan involution** of a Lie algebra `L` over an ordered field `K`: `L` splits
as `Z(L) ⊕ [L, L]`, `θ` is an involutive automorphism, and the restriction of `θ` to the derived
ideal `[L, L]` is a Cartan involution. On the centre `Z(L)`, `θ` is an arbitrary involution. -/
structure IsReductiveCartanInvolution (θ : L ≃ₗ⁅K⁆ L) : Prop where
  /-- The centre and derived ideal of `L` are complementary. -/
  isCompl_center_derivedSeries : IsCompl (center K L) (derivedSeries K L 1)
  /-- A reductive Cartan involution is involutive. -/
  involutive : Function.Involutive θ
  /-- The restriction of `θ` to `[L, L]` is a Cartan involution. -/
  isCartanInvolution_restrictDerivedSeries : (θ.restrictDerivedSeries 1).IsCartanInvolution

/-- Characterization of a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_iff {θ : L ≃ₗ⁅K⁆ L} :
    θ.IsReductiveCartanInvolution ↔ IsCompl (center K L) (derivedSeries K L 1) ∧
      Function.Involutive θ ∧ (θ.restrictDerivedSeries 1).IsCartanInvolution :=
  ⟨fun h ↦ ⟨h.isCompl_center_derivedSeries, h.involutive,
    h.isCartanInvolution_restrictDerivedSeries⟩, fun h ↦ ⟨h.left, h.right.left, h.right.right⟩⟩

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- A reductive Cartan involution is its own inverse. -/
theorem symm_eq_self (hθ : θ.IsReductiveCartanInvolution) : θ.symm = θ :=
  LieEquiv.ext fun x ↦ by rw [symm_apply_eq, hθ.involutive x]

/-- The restriction of a reductive Cartan involution to the centre is involutive. -/
theorem involutive_restrictCenter (hθ : θ.IsReductiveCartanInvolution) :
    Function.Involutive θ.restrictCenter := fun z ↦
  Subtype.ext (by simpa using hθ.involutive (z : L))

/-- The derived ideal `[L, L]` of a Lie algebra with a reductive Cartan involution is Killing. -/
theorem isKilling_derivedSeries [IsStrictOrderedRing K] (hθ : θ.IsReductiveCartanInvolution) :
    IsKilling K (derivedSeries K L 1) := hθ.isCartanInvolution_restrictDerivedSeries.isKilling

/-- The derived ideal `[L, L]` of a Lie algebra with a reductive Cartan involution is
finite-dimensional. -/
theorem finiteDimensional_derivedSeries [IsStrictOrderedRing K]
    (hθ : θ.IsReductiveCartanInvolution) :
    FiniteDimensional K (derivedSeries K L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.finiteDimensional

/-- Conjugating a reductive Cartan involution by a Lie algebra equivalence yields a reductive
Cartan involution. -/
theorem conj [IsStrictOrderedRing K] (hθ : θ.IsReductiveCartanInvolution) (e : L ≃ₗ⁅K⁆ M) :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution := by
  refine ⟨?_, fun y ↦ by simp [hθ.involutive (e.symm y)], ?_⟩
  · have hZ : (center K L).toSubmodule.map e.toLinearMap = (center K M).toSubmodule :=
      congrArg LieSubalgebra.toSubmodule e.map_center
    have hD : (derivedSeries K L 1).toSubmodule.map e.toLinearMap =
        (derivedSeries K M 1).toSubmodule :=
      congrArg LieSubalgebra.toSubmodule (e.map_derivedSeries 1)
    rw [← LieSubmodule.isCompl_toSubmodule, ← hZ, ← hD]
    exact (LieSubmodule.isCompl_toSubmodule.mpr hθ.isCompl_center_derivedSeries).map
      (Submodule.orderIsoMapComap e.toLinearEquiv)
  · simpa using hθ.isCartanInvolution_restrictDerivedSeries.conj (e.restrictDerivedSeries 1)

/-- The derived ideal `[L, L]` of a Lie algebra admitting a reductive Cartan involution is
semisimple. -/
theorem isSemisimple_derivedSeries [IsStrictOrderedRing K] (hθ : θ.IsReductiveCartanInvolution) :
    IsSemisimple K (derivedSeries K L 1) :=
  hθ.isCartanInvolution_restrictDerivedSeries.isSemisimple

/-- A Lie algebra admitting a reductive Cartan involution is reductive: its radical equals its
centre (`LieAlgebra.HasCentralRadical`). -/
theorem hasCentralRadical [IsStrictOrderedRing K] (hθ : θ.IsReductiveCartanInvolution) :
    HasCentralRadical K L :=
  have := hθ.isSemisimple_derivedSeries
  TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

end IsReductiveCartanInvolution

/-- Conjugation by a Lie algebra equivalence preserves the reductive Cartan involution property. -/
@[simp]
theorem isReductiveCartanInvolution_conj_iff [IsStrictOrderedRing K] (θ : L ≃ₗ⁅K⁆ L)
    (e : L ≃ₗ⁅K⁆ M) :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj e⟩
  have heq : e.symm.symm.trans ((e.symm.trans (θ.trans e)).trans e.symm) = θ := by ext x; simp
  simpa only [heq] using h.conj e.symm

/-- **Extension from the derived ideal and centre**: when `L = Z(L) ⊕ [L, L]`, an assembled
automorphism `ofCenterDerived hcompl θZ θD` is a reductive Cartan involution iff `θZ` is involutive
and `θD` is a Cartan involution. -/
@[simp]
theorem isReductiveCartanInvolution_ofCenterDerived_iff
    (hcompl : IsCompl (center K L) (derivedSeries K L 1))
    {θZ : center K L ≃ₗ⁅K⁆ center K L} {θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1} :
    (ofCenterDerived hcompl θZ θD).IsReductiveCartanInvolution ↔
      Function.Involutive θZ ∧ θD.IsCartanInvolution := by
  refine ⟨fun h ↦ ⟨by simpa using h.involutive_restrictCenter,
      by simpa using h.isCartanInvolution_restrictDerivedSeries⟩, fun ⟨hθZ, hθD⟩ ↦
    ⟨hcompl, fun x ↦ ?_, by simpa using hθD⟩⟩
  obtain ⟨⟨z, d⟩, rfl⟩ := (prodCenterDerivedEquiv hcompl).surjective x
  simp [hθZ z, hθD.involutive d]

/-- **Extension from the derived ideal and centre**: when `L = Z(L) ⊕ [L, L]`, any involutive
automorphism of the centre and Cartan involution of the derived ideal assemble into a reductive
Cartan involution of `L`. -/
theorem isReductiveCartanInvolution_ofCenterDerived
    (hcompl : IsCompl (center K L) (derivedSeries K L 1))
    {θZ : center K L ≃ₗ⁅K⁆ center K L} {θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1}
    (hθZ : Function.Involutive θZ) (hθD : θD.IsCartanInvolution) :
    (ofCenterDerived hcompl θZ θD).IsReductiveCartanInvolution :=
  (isReductiveCartanInvolution_ofCenterDerived_iff hcompl).mpr ⟨hθZ, hθD⟩

/-- On an abelian Lie algebra, `[L, L] = 0`, so every involutive automorphism is a reductive Cartan
involution. -/
theorem isReductiveCartanInvolution_iff_involutive_of_isLieAbelian [IsStrictOrderedRing K]
    [IsLieAbelian L] {θ : L ≃ₗ⁅K⁆ L} : θ.IsReductiveCartanInvolution ↔ Function.Involutive θ := by
  have hZ : center K L = ⊤ := (isLieAbelian_iff_center_eq_top K L).mp inferInstance
  have hD : derivedSeries K L 1 = ⊥ := by
    rw [eq_bot_iff, derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
      LieSubmodule.lie_le_iff]
    exact fun x _ y _ ↦ by simp [trivial_lie_zero]
  refine ⟨fun h ↦ h.involutive, fun hθ ↦ ⟨by rw [hZ, hD]; exact isCompl_top_bot, hθ, ?_⟩⟩
  rw [isCartanInvolution_iff]
  refine ⟨fun x ↦ Subtype.ext (by simpa using hθ (x : L)), fun x hx ↦ ?_⟩
  have hx' : (x : L) ∈ (⊥ : LieIdeal K L) := hD ▸ x.property
  exact absurd (Subtype.ext ((LieSubmodule.mem_bot _).mp hx')) hx

/-- Every Cartan involution over an ordered field is a reductive Cartan involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution [IsStrictOrderedRing K] {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) : θ.IsReductiveCartanInvolution := by
  refine ⟨by rw [hθ.center_eq_bot, hθ.derivedSeries_one_eq_top]; exact isCompl_bot_top,
    hθ.involutive, ?_⟩
  let e₁ : L ≃ₗ⁅K⁆ (⊤ : LieSubalgebra K L) := (LieSubalgebra.topEquiv (R := K) (L := L)).symm
  let e₂ : (⊤ : LieSubalgebra K L) ≃ₗ⁅K⁆ (derivedSeries K L 1).toLieSubalgebra :=
    LieEquiv.ofEq (⊤ : LieSubalgebra K L) (derivedSeries K L 1).toLieSubalgebra
      (by rw [hθ.derivedSeries_one_eq_top, LieIdeal.top_toLieSubalgebra])
  let e : L ≃ₗ⁅K⁆ derivedSeries K L 1 := e₁.trans e₂
  have he (y : L) : (e y : L) = y :=
    (LieSubalgebra.topEquiv (R := K) (L := L)).apply_symm_apply y
  exact hθ.of_intertwines e fun y ↦ Subtype.ext (by simp [he])

end LinearOrder

end LieEquiv
