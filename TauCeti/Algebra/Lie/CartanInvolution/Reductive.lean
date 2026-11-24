/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Automorphism
import Mathlib.Algebra.Lie.Prod
import TauCeti.Algebra.Lie.Prod

/-!
# Reductive Cartan involutions and extensions

A *reductive Cartan involution* of a Lie algebra `L` over a partially ordered commutative ring is
an involutive automorphism `θ` whose restriction `θ.restrictDerivedSeries 1` to the derived ideal
`⁅L, L⁆` is a Cartan involution (`LieEquiv.IsReductiveCartanInvolution`). Unlike an ordinary
Cartan involution, it allows a nontrivial centre on which `θ` may act by any linear involution.

When `L` splits as `center R L ⊕ derivedSeries R L 1` (in particular, for any finite-dimensional
reductive Lie algebra in characteristic zero by `TauCeti.isCompl_center_derivedSeries`), the
`-1`-eigenspace `θ.cartanP` decomposes into its central and derived parts, and any linear involution
on `center R L` extends with any Cartan involution on `derivedSeries R L 1` to a reductive Cartan
involution of `L` (`LieEquiv.exists_isReductiveCartanInvolution_extend`). Moreover, every Cartan
involution over a partially ordered PID is reductive
(`LieEquiv.IsCartanInvolution.isReductiveCartanInvolution`).

## Main definitions

* `LieEquiv.IsReductiveCartanInvolution`: the predicate that an involutive automorphism restricts
  to a Cartan involution on the derived ideal.

## Main results

* `LieEquiv.disjoint_cartanP_inf_center_derivedSeries`,
  `LieEquiv.sup_cartanP_inf_center_derivedSeries`: central/derived splitting of `θ.cartanP`.
* `LieEquiv.IsReductiveCartanInvolution.conj`,
  `LieEquiv.isReductiveCartanInvolution_conj_iff`,
  `LieEquiv.isReductiveCartanInvolution_of_isLieAbelian`: conjugation invariance and abelian case.
* `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution`: every Cartan involution over a
  partially ordered PID is reductive.
* `LieEquiv.IsReductiveCartanInvolution.isKilling_derivedSeries`,
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_derivedSeries`,
  `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical`: structural consequences for `⁅L, L⁆`
  and `L`.
* `LieEquiv.exists_isReductiveCartanInvolution_extend`: extending an involution of the centre and a
  Cartan involution of the derived ideal to a reductive Cartan involution of `L`.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

section ReductiveCartanP

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- When the centre and derived ideal are disjoint, the central and derived parts of `θ.cartanP`
are disjoint for any automorphism `θ`. -/
theorem disjoint_cartanP_inf_center_derivedSeries
    (hd : Disjoint (center R L) (derivedSeries R L 1)) (θ : L ≃ₗ⁅R⁆ L) :
    Disjoint (θ.cartanP ⊓ (center R L).toSubmodule)
      (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) :=
  (LieSubmodule.disjoint_toSubmodule.mpr hd).mono inf_le_right inf_le_right

/-- When `L` splits as the direct sum of its centre and derived ideal, `θ.cartanP` splits as
`(θ.cartanP ⊓ Z(L)) ⊔ (θ.cartanP ⊓ ⁅L, L⁆)` for any automorphism `θ`. -/
theorem sup_cartanP_inf_center_derivedSeries
    (hc : IsCompl (center R L) (derivedSeries R L 1)) (θ : L ≃ₗ⁅R⁆ L) :
    (θ.cartanP ⊓ (center R L).toSubmodule) ⊔
      (θ.cartanP ⊓ (derivedSeries R L 1).toSubmodule) = θ.cartanP := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx ↦ ?_
  obtain ⟨⟨z, d⟩, ⟨hz, hd, hsum⟩, _⟩ :=
    θ.existsUnique_center_add_derivedSeries_of_apply_eq_smul hc (c := (-1 : R))
      (by simpa only [neg_one_smul] using mem_cartanP.mp hx)
  rw [← hsum]
  exact Submodule.add_mem_sup
    ⟨mem_cartanP.mpr (by simpa only [neg_one_smul] using hz), z.property⟩
    ⟨mem_cartanP.mpr (by simpa only [neg_one_smul] using hd), d.property⟩

end ReductiveCartanP

section PartialOrder

variable {R L L' : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- A **reductive Cartan involution** of a Lie algebra `L`: an involutive Lie algebra automorphism
whose restriction to the derived ideal `⁅L, L⁆` is a Cartan involution. -/
structure IsReductiveCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop where
  /-- A reductive Cartan involution is involutive: `θ (θ x) = x`. -/
  involutive : Function.Involutive θ
  /-- The restriction of `θ` to the derived ideal `⁅L, L⁆` is a Cartan involution. -/
  derivedSeries_isCartanInvolution : (θ.restrictDerivedSeries 1).IsCartanInvolution

/-- Conjugation by a Lie algebra equivalence preserves reductive Cartan involutions. -/
theorem IsReductiveCartanInvolution.conj {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution where
  involutive y := by simp [hθ.involutive _]
  derivedSeries_isCartanInvolution := by
    let eD := e.restrictDerivedSeries 1
    have hres : (e.symm.trans (θ.trans e)).restrictDerivedSeries 1 =
        eD.symm.trans ((θ.restrictDerivedSeries 1).trans eD) :=
      LieEquiv.ext fun x ↦ Subtype.ext (by simp [eD])
    rw [hres]
    exact hθ.derivedSeries_isCartanInvolution.conj eD

/-- Conjugating an automorphism by a Lie algebra equivalence preserves and reflects being a
reductive Cartan involution. -/
@[simp]
theorem isReductiveCartanInvolution_conj_iff {θ : L ≃ₗ⁅R⁆ L} (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution :=
  ⟨fun h ↦ by simpa using h.conj e.symm, fun h ↦ h.conj e⟩

/-- Every involutive automorphism of an abelian Lie algebra is a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_of_isLieAbelian [IsLieAbelian L] {θ : L ≃ₗ⁅R⁆ L}
    (hinv : Function.Involutive θ) :
    θ.IsReductiveCartanInvolution where
  involutive := hinv
  derivedSeries_isCartanInvolution := by
    have hbot : derivedSeries R L 1 = ⊥ :=
      (LieAlgebra.abelian_iff_derived_one_eq_bot (⊤ : LieIdeal R L)).mp
        ((lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv).mpr inferInstance)
    have hsub : Subsingleton (derivedSeries R L 1) := by
      rw [hbot]
      infer_instance
    exact ⟨fun _ ↦ Subsingleton.elim _ _, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩

/-- Every Cartan involution over a partially ordered principal ideal domain is a reductive Cartan
involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution [IsDomain R] [IsPrincipalIdealRing R]
    {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution) :
    θ.IsReductiveCartanInvolution where
  involutive := hθ.involutive
  derivedSeries_isCartanInvolution :=
    hθ.restrict (θ.restrictDerivedSeries 1) (θ.coe_restrictDerivedSeries 1)

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is Killing. -/
theorem IsReductiveCartanInvolution.isKilling_derivedSeries {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) :
    IsKilling R (derivedSeries R L 1) :=
  hθ.derivedSeries_isCartanInvolution.isKilling

/-- When `L` splits as the direct sum of its centre and derived ideal, combining a linear
involution `θZ` of the centre with a Cartan involution `θD` of the derived ideal produces a
reductive Cartan involution of `L`. -/
theorem exists_isReductiveCartanInvolution_extend
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ[R] center R L) (hθZ : Function.Involutive θZ)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (hθD : θD.IsCartanInvolution) :
    ∃ θ : L ≃ₗ⁅R⁆ L, θ.IsReductiveCartanInvolution ∧
      (∀ z : center R L, θ z = θZ z) ∧ ∀ d : derivedSeries R L 1, θ d = θD d := by
  let e : (↥(center R L) × ↥(derivedSeries R L 1)) ≃ₗ⁅R⁆ L :=
    TauCeti.idealProdEquivOfIsCompl hc
  have he (z : center R L) (d : derivedSeries R L 1) : e (z, d) = (z : L) + d :=
    TauCeti.idealProdEquivOfIsCompl_apply hc (z, d)
  have hz_lie (z₁ z₂ : center R L) : ⁅z₁, z₂⁆ = 0 :=
    Subtype.ext ((LieModule.mem_maxTrivSubmodule R L L z₂).mp z₂.property z₁)
  let θZ_lie : ↥(center R L) ≃ₗ⁅R⁆ ↥(center R L) :=
    { __ := θZ
      map_lie' := fun {z₁ z₂} ↦ by rw [hz_lie z₁ z₂, hz_lie]; exact map_zero θZ }
  let θprod : (↥(center R L) × ↥(derivedSeries R L 1)) ≃ₗ⁅R⁆
      (↥(center R L) × ↥(derivedSeries R L 1)) :=
    { __ := θZ.prodCongr θD.toLinearEquiv
      map_lie' := fun {p q} ↦ Prod.ext (θZ_lie.map_lie p.1 q.1) (θD.map_lie p.2 q.2) }
  let θ : L ≃ₗ⁅R⁆ L := (e.symm.trans θprod).trans e
  have hθ_apply (z : center R L) (d : derivedSeries R L 1) :
      θ ((z : L) + d) = (θZ z : L) + θD d := by
    have hp : θprod (z, d) = (θZ z, θD d) := rfl
    rw [← he z d, ← he (θZ z) (θD d)]
    simp [θ, hp]
  have hinv : Function.Involutive θ := fun x ↦ by
    obtain ⟨⟨z, d⟩, rfl⟩ := e.surjective x
    rw [coe_toLieHom, he z d, hθ_apply, hθ_apply, hθZ, hθD.involutive]
  have hres : θ.restrictDerivedSeries 1 = θD := LieEquiv.ext fun d ↦ Subtype.ext <| by
    simpa [coe_restrictDerivedSeries] using hθ_apply 0 d
  refine ⟨θ, ⟨hinv, ?_⟩, fun z ↦ by simpa using hθ_apply z 0, fun d ↦ by simpa using hθ_apply 0 d⟩
  rw [hres]
  exact hθD

end PartialOrder

section Field

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsSemisimple K (derivedSeries K L 1) :=
  hθ.derivedSeries_isCartanInvolution.isSemisimple

/-- A Lie algebra admitting a reductive Cartan involution is reductive (has central radical). -/
theorem hasCentralRadical (hθ : θ.IsReductiveCartanInvolution) :
    HasCentralRadical K L := by
  have := hθ.isSemisimple_derivedSeries
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

end IsReductiveCartanInvolution

end Field

end LieEquiv
