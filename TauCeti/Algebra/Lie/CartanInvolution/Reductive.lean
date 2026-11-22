/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Reductive.Basic
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.TraceForm
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Reductive.Fixed
import TauCeti.Algebra.Lie.SemiDirect.Basic
import TauCeti.Algebra.Lie.Subalgebra.Automorphism

/-!
# Reductive Cartan involutions and extensions

A *reductive Cartan involution* of a Lie algebra `L` over a partially ordered commutative ring is
an involutive automorphism `θ` whose restriction to the derived ideal `⁅L, L⁆` is a Cartan
involution (`LieEquiv.IsReductiveCartanInvolution`). Unlike an ordinary Cartan involution, it allows
a nontrivial centre on which `θ` may act by any linear involution.

When `L` splits as `center R L ⊕ derivedSeries R L 1` (in particular, for any finite-dimensional
reductive Lie algebra in characteristic zero by `TauCeti.isCompl_center_derivedSeries`), the
`-1`-eigenspace `θ.cartanP` decomposes into its central and derived parts, and any linear involution
on `center R L` extends with any Cartan involution on `derivedSeries R L 1` to a reductive Cartan
involution of `L` (`LieEquiv.exists_isReductiveCartanInvolution_extend`). Moreover, every Cartan
involution restricts to any invariant Lie ideal over a partially ordered PID
(`LieEquiv.IsCartanInvolution.ofSubalgebras`), hence in particular is reductive.

## Main definitions

* `LieEquiv.IsReductiveCartanInvolution`: the predicate that an involutive automorphism restricts
  to a Cartan involution on the derived ideal.

## Main results

* `LieEquiv.disjoint_cartanP_inf_center_derivedSeries`,
  `LieEquiv.sup_cartanP_inf_center_derivedSeries`: central/derived splitting of `θ.cartanP`.
* `LieEquiv.isReductiveCartanInvolution_iff`, `LieEquiv.IsReductiveCartanInvolution.conj`,
  `LieEquiv.isReductiveCartanInvolution_conj_iff`,
  `LieEquiv.isReductiveCartanInvolution_of_isLieAbelian`: characterization, conjugation invariance,
  and abelian case.
* `LieEquiv.IsCartanInvolution.ofSubalgebras`,
  `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution`: restriction of a Cartan involution to
  any invariant Lie ideal over a partially ordered PID, and to the derived ideal.
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
  derivedSeries_isCartanInvolution :
    ∃ θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1,
      (∀ x : derivedSeries R L 1, (θD x : L) = θ x) ∧ θD.IsCartanInvolution

/-- Unfolded characterization of `LieEquiv.IsReductiveCartanInvolution`. -/
theorem isReductiveCartanInvolution_iff {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsReductiveCartanInvolution ↔
      Function.Involutive θ ∧
        ∃ θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1,
          (∀ x : derivedSeries R L 1, (θD x : L) = θ x) ∧ θD.IsCartanInvolution :=
  ⟨fun h ↦ ⟨h.involutive, h.derivedSeries_isCartanInvolution⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

/-- Conjugation by a Lie algebra equivalence preserves reductive Cartan involutions. -/
theorem IsReductiveCartanInvolution.conj {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution where
  involutive y := by simp [hθ.involutive _]
  derivedSeries_isCartanInvolution := by
    obtain ⟨θD, hθD_eq, hθD⟩ := hθ.derivedSeries_isCartanInvolution
    let eD := e.restrictDerivedSeries 1
    refine ⟨eD.symm.trans (θD.trans eD), fun y ↦ ?_, hθD.conj eD⟩
    simp [eD, hθD_eq]

/-- Conjugating an automorphism by a Lie algebra equivalence preserves and reflects being a
reductive Cartan involution. -/
@[simp]
theorem isReductiveCartanInvolution_conj_iff {θ : L ≃ₗ⁅R⁆ L} (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution :=
  ⟨fun h ↦ by
    have h' := h.conj e.symm
    have heq : e.symm.symm.trans ((e.symm.trans (θ.trans e)).trans e.symm) = θ :=
      LieEquiv.ext fun x ↦ by simp
    rwa [heq] at h', fun h ↦ h.conj e⟩

/-- Every involutive automorphism of an abelian Lie algebra is a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_of_isLieAbelian [IsLieAbelian L] {θ : L ≃ₗ⁅R⁆ L}
    (hinv : Function.Involutive θ) :
    θ.IsReductiveCartanInvolution where
  involutive := hinv
  derivedSeries_isCartanInvolution := by
    have hbot : derivedSeries R L 1 = ⊥ := by
      rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
        LieSubmodule.lie_eq_bot_iff]
      intro x _ y _
      exact trivial_lie_zero L L x y
    have hsub : Subsingleton (derivedSeries R L 1) := by
      rw [hbot]
      infer_instance
    refine ⟨LieEquiv.refl, fun x ↦ ?_,
      ⟨fun _ ↦ rfl, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩⟩
    have hx0 : (x : L) = 0 := congrArg Subtype.val (Subsingleton.elim x 0)
    simp [hx0]

/-- Restricting a Cartan involution to any invariant Lie ideal yields a Cartan involution of that
ideal, over a partially ordered principal ideal domain. -/
theorem IsCartanInvolution.ofSubalgebras [IsDomain R] [IsPrincipalIdealRing R]
    {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution) (I : LieIdeal R L)
    (hI : I.toLieSubalgebra.map θ = I.toLieSubalgebra) :
    (θ.ofSubalgebras I.toLieSubalgebra I.toLieSubalgebra hI).IsCartanInvolution where
  involutive x := Subtype.ext (by simp [hθ.involutive x])
  posDef_twistedKillingForm x hx := by
    have := hθ.isKilling
    have := TauCeti.free_of_isKilling (R := R) (L := L)
    have := TauCeti.finite_of_isKilling (R := R) (L := L)
    let eI : I.toLieSubalgebra ≃ₗ⁅R⁆ I :=
      { toFun := fun y ↦ ⟨y.val, y.property⟩
        invFun := fun y ↦ ⟨y.val, y.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        map_lie' := fun {_ _} ↦ rfl }
    have hkf : killingForm R I (eI x)
        (eI ((θ.ofSubalgebras I.toLieSubalgebra I.toLieSubalgebra hI) x)) =
        killingForm R L x (θ x) := by
      have h : killingForm R I (eI x)
          (eI ((θ.ofSubalgebras I.toLieSubalgebra I.toLieSubalgebra hI) x)) =
          ((killingForm R L).restrict I.toSubmodule) ⟨x.val, x.property⟩
            ⟨(θ.ofSubalgebras I.toLieSubalgebra I.toLieSubalgebra hI x).val,
              (θ.ofSubalgebras I.toLieSubalgebra I.toLieSubalgebra hI x).property⟩ :=
        LinearMap.congr_fun₂ (LieIdeal.killingForm_eq (R := R) (L := L) (I := I))
          (eI x) (eI ((θ.ofSubalgebras I.toLieSubalgebra I.toLieSubalgebra hI) x))
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LieEquiv.ofSubalgebras_apply] using h
    rw [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply,
      ← LieAlgebra.killingForm_of_equiv_apply eI, hkf, ← twistedKillingForm_apply]
    exact hθ.twistedKillingForm_pos (fun h ↦ hx (Subtype.ext h))

/-- Every Cartan involution over a partially ordered principal ideal domain is a reductive Cartan
involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution [IsDomain R] [IsPrincipalIdealRing R]
    {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution) :
    θ.IsReductiveCartanInvolution where
  involutive := hθ.involutive
  derivedSeries_isCartanInvolution := by
    have hmap : (derivedSeries R L 1).toLieSubalgebra.map θ =
        (derivedSeries R L 1).toLieSubalgebra :=
      LieSubalgebra.map_eq_of_mem θ
        (fun _ hx ↦ LieIdeal.derivedSeries_map_le (f := θ.toLieHom) 1 (LieIdeal.mem_map hx))
        (fun _ hy ↦ LieIdeal.derivedSeries_map_le (f := θ.symm.toLieHom) 1 (LieIdeal.mem_map hy))
    let θD := θ.restrictDerivedSeries 1
    let eD : (derivedSeries R L 1).toLieSubalgebra ≃ₗ⁅R⁆ derivedSeries R L 1 :=
      { toFun := fun y ↦ ⟨y.val, y.property⟩
        invFun := fun y ↦ ⟨y.val, y.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        map_lie' := fun {_ _} ↦ rfl }
    have hθD_eq : θD = eD.symm.trans ((θ.ofSubalgebras _ _ hmap).trans eD) := by
      ext x
      have hl : (θD x : L) = θ x := θ.coe_restrictDerivedSeries 1 x
      have hr : ((eD.symm.trans ((θ.ofSubalgebras _ _ hmap).trans eD) x :
          derivedSeries R L 1) : L) = θ x := by
        simp [eD, LieEquiv.ofSubalgebras_apply]
      exact hl.trans hr.symm
    refine ⟨θD, fun x ↦ θ.coe_restrictDerivedSeries 1 x, ?_⟩
    rw [hθD_eq, isCartanInvolution_conj_iff]
    exact hθ.ofSubalgebras (derivedSeries R L 1) hmap

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is Killing. -/
theorem IsReductiveCartanInvolution.isKilling_derivedSeries {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) :
    IsKilling R (derivedSeries R L 1) := by
  obtain ⟨_, _, hθD⟩ := hθ.derivedSeries_isCartanInvolution
  exact hθD.isKilling

/-- When `L` splits as the direct sum of its centre and derived ideal, combining a linear
involution `θZ` of the centre with a Cartan involution `θD` of the derived ideal produces a
reductive Cartan involution of `L`. -/
theorem exists_isReductiveCartanInvolution_extend
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ[R] center R L) (hθZ : Function.Involutive θZ)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (hθD : θD.IsCartanInvolution) :
    ∃ θ : L ≃ₗ⁅R⁆ L, θ.IsReductiveCartanInvolution ∧
      (∀ z : center R L, θ z = θZ z) ∧ ∀ d : derivedSeries R L 1, θ d = θD d := by
  let S : LieIdeal R L := derivedSeries R L 1
  let Z : LieSubalgebra R L := (center R L).toLieSubalgebra
  have hc' : IsCompl S.toSubmodule Z.toSubmodule := (LieSubmodule.isCompl_toSubmodule.mpr hc).symm
  have hψ : (LieIdeal.ad S).comp Z.incl = 0 := by
    ext z d
    simp only [LieHom.comp_apply, LieSubalgebra.coe_incl, LieIdeal.ad_apply_apply,
      zero_apply, LieDerivation.zero_apply, LieSubmodule.coe_zero, LieSubmodule.coe_bracket]
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule R L L z).mp z.property, neg_zero]
  let e₀ : (↥S ⋊⁅(0 : ↥Z →ₗ⁅R⁆ LieDerivation R S S)⁆ ↥Z) ≃ₗ⁅R⁆
      (↥S ⋊⁅(LieIdeal.ad S).comp Z.incl⁆ ↥Z) :=
    { toFun := fun x ↦ ⟨x.left, x.right⟩
      invFun := fun x ↦ ⟨x.left, x.right⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := fun {x y} ↦ by
        ext <;> simp [hψ] }
  let e : (↥S × ↥Z) ≃ₗ⁅R⁆ L :=
    (LieAlgebra.SemiDirectSum.prod_iso R S Z).symm.trans
      (e₀.trans (LieIdeal.semiDirectSumEquiv S Z hc'))
  have he (d : S) (z : Z) : e (d, z) = (d : L) + z := by
    rw [LieEquiv.trans_apply, LieEquiv.trans_apply, LieIdeal.semiDirectSumEquiv_apply]
    rfl
  have hz_lie (z₁ z₂ : Z) : ⁅z₁, z₂⁆ = 0 :=
    Subtype.ext ((LieModule.mem_maxTrivSubmodule R L L z₂).mp z₂.property z₁)
  let eZ : ↥Z ≃ₗ[R] center R L :=
    { toFun := fun z ↦ ⟨z.val, z.property⟩
      invFun := fun z ↦ ⟨z.val, z.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let θZ_lie : ↥Z ≃ₗ⁅R⁆ ↥Z :=
    { __ := eZ.trans (θZ.trans eZ.symm)
      map_lie' := fun {z₁ z₂} ↦ by
        rw [hz_lie z₁ z₂, hz_lie]
        exact (eZ.trans (θZ.trans eZ.symm)).map_zero }
  let θprod : (↥S × ↥Z) ≃ₗ⁅R⁆ (↥S × ↥Z) :=
    { __ := θD.toLieHom.prodMap θZ_lie.toLieHom
      invFun := θD.symm.toLieHom.prodMap θZ_lie.symm.toLieHom
      left_inv := fun ⟨d, z⟩ ↦ by simp
      right_inv := fun ⟨d, z⟩ ↦ by simp }
  let θ : L ≃ₗ⁅R⁆ L := (e.symm.trans θprod).trans e
  have hθ_apply (d : S) (z : center R L) : θ ((d : L) + z) = (θD d : L) + θZ z := by
    have hval : ((eZ.symm z : Z) : L) = (z : L) := rfl
    rw [← hval, ← he d (eZ.symm z)]
    dsimp only [θ]
    rw [LieEquiv.trans_apply (e.symm.trans θprod) e, LieEquiv.trans_apply e.symm θprod,
      e.symm_apply_apply]
    have hp : θprod (d, eZ.symm z) = (θD d, eZ.symm (θZ z)) := rfl
    rw [hp, he]
    rfl
  refine ⟨θ, ⟨fun x ↦ ?_, ⟨θD, fun d ↦ ?_, hθD⟩⟩, fun z ↦ ?_, fun d ↦ ?_⟩
  · obtain ⟨⟨d, z⟩, hx⟩ := e.surjective x
    have hval : ((eZ z : center R L) : L) = (z : L) := rfl
    rw [← hx, coe_toLieHom, he, ← hval, hθ_apply, hθ_apply, hθD.involutive d, hθZ]
  · simpa using (hθ_apply d 0).symm
  · simpa using hθ_apply 0 z
  · simpa using hθ_apply d 0

end PartialOrder

section Field

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsSemisimple K (derivedSeries K L 1) := by
  obtain ⟨_, _, hθD⟩ := hθ.derivedSeries_isCartanInvolution
  exact hθD.isSemisimple

/-- A Lie algebra admitting a reductive Cartan involution is reductive (has central radical). -/
theorem hasCentralRadical (hθ : θ.IsReductiveCartanInvolution) :
    HasCentralRadical K L := by
  have := hθ.isSemisimple_derivedSeries
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

end IsReductiveCartanInvolution

end Field

end LieEquiv
