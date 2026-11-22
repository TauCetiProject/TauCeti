/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# Cartan involutions

A *Cartan involution* of a Lie algebra `L` over an ordered field is an involutive Lie algebra
automorphism `θ` whose twisted Killing form `B_θ(x, y) = -B(x, θ y)` is positive definite, `B`
being the Killing form. Over `ℝ` these are the Cartan involutions of real semisimple Lie
algebras, and `L = 𝔨 ⊕ 𝔭` (`LieEquiv.isCompl_fixedSubalgebra_cartanP`) is the Cartan
decomposition.

For a Cartan involution, `B_θ` is an inner product on `L` for which `θ` is orthogonal, `ad x` is
skew-adjoint for `x ∈ 𝔨` and self-adjoint for `x ∈ 𝔭` (see
`TauCeti.Algebra.Lie.CartanInvolution.Decomposition`). This file adds the sign of the Killing
form: it is negative definite on `𝔨` and positive definite on `𝔭`. Consequently the Killing form
of `L` is nondegenerate, so a Lie algebra with a Cartan involution is finite-dimensional,
semisimple, and perfect, with trivial centre; `𝔭` is the Killing-orthogonal complement of `𝔨`,
so a Cartan involution is determined by `𝔨` (and commuting Cartan involutions agree); `𝔨` carries
the negative definite invariant form `-B|_𝔨`, so `𝔨` is reductive and is the direct sum of its
centre and its derived algebra, the latter semisimple with negative definite Killing form; and
over `ℝ`, `ad x` is diagonalizable for `x ∈ 𝔭`.

## Main definitions

* `LieEquiv.IsCartanInvolution`: the predicate that `θ` is a Cartan involution.

## Main results

* `LieEquiv.IsCartanInvolution.killingForm_apply_self_neg_of_mem_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_apply_self_pos_of_mem_cartanP`: the Killing form is
  negative definite on `𝔨` and positive definite on `𝔭`.
* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.isSemisimple`: a Lie
  algebra with a Cartan involution has nondegenerate Killing form, hence is finite-dimensional
  (`LieEquiv.IsCartanInvolution.finiteDimensional`) and semisimple.
* `LieEquiv.IsCartanInvolution.orthogonal_fixedSubalgebra_eq_cartanP`: `𝔭` is the
  Killing-orthogonal complement of `𝔨`.
* `LieEquiv.IsCartanInvolution.eq_of_fixedSubalgebra_eq`,
  `LieEquiv.IsCartanInvolution.eq_of_commute`: a Cartan involution is determined by `𝔨`, and
  commuting Cartan involutions are equal.
* `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`: `𝔨` is
  reductive and is the direct sum of its centre and its derived algebra, which is semisimple with
  negative definite Killing form.
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: over `ℝ`, `ad x` is diagonalizable
  for `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter III, §7.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Minus the Killing form of `L`, restricted to the fixed subalgebra `𝔨` of `θ`. -/
private noncomputable def negKillingFormFixed (θ : L ≃ₗ⁅K⁆ L) :
    LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
  -(killingForm K L).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
    θ.toLieHom.fixedSubalgebra.incl.toLinearMap

private theorem negKillingFormFixed_apply {θ : L ≃ₗ⁅K⁆ L} (x y : θ.toLieHom.fixedSubalgebra) :
    negKillingFormFixed θ x y = -killingForm K L x y := by
  simp [negKillingFormFixed]

private theorem isSymm_negKillingFormFixed {θ : L ≃ₗ⁅K⁆ L} : (negKillingFormFixed θ).IsSymm :=
  ⟨fun x y ↦ by rw [negKillingFormFixed_apply, negKillingFormFixed_apply, traceForm_comm]⟩

private theorem lieInvariant_negKillingFormFixed {θ : L ≃ₗ⁅K⁆ L} :
    (negKillingFormFixed θ).lieInvariant θ.toLieHom.fixedSubalgebra := by
  intro x y z
  simp only [negKillingFormFixed_apply, LieSubalgebra.coe_bracket, traceForm_apply_lie_apply']

section LinearOrder

variable [LinearOrder K]

/-- A *Cartan involution* of a Lie algebra `L` over an ordered field: an involutive Lie algebra
automorphism `θ` whose twisted Killing form `B_θ(x, y) = -B(x, θ y)` is positive definite. -/
structure IsCartanInvolution (θ : L ≃ₗ⁅K⁆ L) : Prop where
  /-- A Cartan involution is an involution. -/
  involutive : Function.Involutive θ
  /-- The twisted Killing form `B_θ` of a Cartan involution is positive definite. -/
  posDef_twistedKillingForm : θ.twistedKillingForm.toQuadraticMap.PosDef

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- A Cartan involution is its own inverse. -/
theorem symm_eq_self (hθ : θ.IsCartanInvolution) : θ.symm = θ := by
  ext x
  rw [symm_apply_eq, hθ.involutive x]

/-- The twisted Killing form `B_θ` of a Cartan involution is symmetric. -/
theorem isSymm_twistedKillingForm (hθ : θ.IsCartanInvolution) :
    θ.twistedKillingForm.IsSymm :=
  LieEquiv.isSymm_twistedKillingForm hθ.involutive

/-- Positivity of `B_θ(x, x) = -B(x, θ x)` on nonzero vectors. -/
theorem twistedKillingForm_self_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.twistedKillingForm x x :=
  hθ.posDef_twistedKillingForm x hx

/-- A Lie algebra admitting a Cartan involution has trivial centre. -/
theorem center_eq_bot (hθ : θ.IsCartanInvolution) : center K L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  by_contra hx0
  have hpos := hθ.twistedKillingForm_self_pos hx0
  have had : ad K L x = 0 := LinearMap.ext fun z ↦ by
    rw [ad_apply, ← lie_skew, (LieModule.mem_maxTrivSubmodule K L L x).mp hx z, neg_zero,
      LinearMap.zero_apply]
  have hz : killingForm K L x (θ x) = 0 := by
    rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero]
  rw [twistedKillingForm_apply, hz, neg_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Conjugating a Cartan involution by a Lie algebra equivalence yields a Cartan involution. -/
theorem conj {M : Type*} [LieRing M] [LieAlgebra K M] (hθ : θ.IsCartanInvolution)
    (e : L ≃ₗ⁅K⁆ M) : (e.symm.trans (θ.trans e)).IsCartanInvolution := by
  refine ⟨fun y ↦ by simp [hθ.involutive (e.symm y)], fun y hy ↦ ?_⟩
  have he : e.symm y ≠ 0 := fun h ↦ hy (by simpa using congrArg e h)
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_conj] using
    hθ.twistedKillingForm_self_pos he

end IsCartanInvolution

/-- Conjugation by a Lie algebra equivalence preserves the Cartan involution property. -/
@[simp]
theorem isCartanInvolution_conj_iff {M : Type*} [LieRing M] [LieAlgebra K M]
    (θ : L ≃ₗ⁅K⁆ L) (e : L ≃ₗ⁅K⁆ M) :
    (e.symm.trans (θ.trans e)).IsCartanInvolution ↔ θ.IsCartanInvolution :=
  ⟨fun h ↦ by simpa only [symm_symm, trans_conj_symm] using h.conj e.symm, fun h ↦ h.conj e⟩

/-- If `e : L ≃ₗ⁅K⁆ M` intertwines `θ` with `θ'` (`∀ x, θ' (e x) = e (θ x)`), then `θ'` is a
Cartan involution whenever `θ` is. -/
theorem IsCartanInvolution.of_intertwines {M : Type*} [LieRing M] [LieAlgebra K M] {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) (e : L ≃ₗ⁅K⁆ M) {θ' : M ≃ₗ⁅K⁆ M}
    (h : ∀ x, θ' (e x) = e (θ x)) : θ'.IsCartanInvolution := by
  have hconj : θ' = e.symm.trans (θ.trans e) :=
    LieEquiv.ext fun y ↦ by obtain ⟨x, rfl⟩ := e.surjective y; simp [h x]
  rwa [hconj, isCartanInvolution_conj_iff]

/-- A nontrivial abelian Lie algebra admits no Cartan involution, because a Lie algebra admitting
a Cartan involution has trivial centre. -/
theorem not_isCartanInvolution_of_isLieAbelian [Nontrivial L] [IsLieAbelian L] (θ : L ≃ₗ⁅K⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hx0 : x ∈ center K L :=
    (LieModule.mem_maxTrivSubmodule K L L x).mpr fun y ↦ trivial_lie_zero L L y x
  rw [hθ.center_eq_bot] at hx0
  exact hx ((LieSubmodule.mem_bot x).mp hx0)

variable [IsStrictOrderedRing K]

/-- An involution is a Cartan involution exactly when `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅K⁆ L} :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → killingForm K L x (θ x) < 0 := by
  refine ⟨fun h ↦ ⟨h.involutive, fun x hx ↦ ?_⟩, fun h ↦ ⟨h.left, fun x hx ↦ ?_⟩⟩
  · have := h.posDef_twistedKillingForm x hx
    rwa [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos] at this
  · rw [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos]
    exact h.right x hx

/-- The identity automorphism is a Cartan involution if and only if the Killing form is negative
definite (the compact case). -/
theorem isCartanInvolution_refl_iff :
    (LieEquiv.refl : L ≃ₗ⁅K⁆ L).IsCartanInvolution ↔
      ∀ x : L, x ≠ 0 → killingForm K L x x < 0 := by
  simp [isCartanInvolution_iff, Function.Involutive]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- For a Cartan involution, `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem killingForm_apply_apply_neg (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    killingForm K L x (θ x) < 0 :=
  (isCartanInvolution_iff.mp hθ).right x hx

/-- The Killing form is negative definite on the fixed subalgebra `𝔨` of a Cartan
involution. -/
theorem killingForm_apply_self_neg_of_mem_fixedSubalgebra (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx₀ : x ≠ 0) : killingForm K L x x < 0 := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  have := hθ.killingForm_apply_apply_neg hx₀
  rwa [hx] at this

/-- The Killing form is positive definite on the `-1`-eigenspace `𝔭` of a Cartan involution. -/
theorem killingForm_apply_self_pos_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) (hx₀ : x ≠ 0) : 0 < killingForm K L x x := by
  have := hθ.killingForm_apply_apply_neg hx₀
  rwa [mem_cartanP.mp hx, map_neg, neg_lt_zero] at this

/-- A Lie algebra with a Cartan involution has nondegenerate Killing form. -/
theorem isKilling (hθ : θ.IsCartanInvolution) : IsKilling K L := by
  refine ⟨(LieSubmodule.toSubmodule_eq_bot _).mp <|
    (LieIdeal.coe_killingCompl_top K L).trans (eq_bot_iff.mpr fun x hx ↦ ?_)⟩
  by_contra hx₀
  have := hθ.killingForm_apply_apply_neg hx₀
  rw [LinearMap.mem_ker.mp hx, LinearMap.zero_apply] at this
  exact this.false

/-- A Lie algebra with a Cartan involution is finite-dimensional, since its Killing form is
nondegenerate. -/
theorem finiteDimensional (hθ : θ.IsCartanInvolution) : FiniteDimensional K L :=
  have := hθ.isKilling
  TauCeti.finite_of_isKilling

/-- A Lie algebra with a Cartan involution is semisimple. -/
theorem isSemisimple (hθ : θ.IsCartanInvolution) : IsSemisimple K L :=
  have := hθ.isKilling
  have := hθ.finiteDimensional
  inferInstance

/-- A Lie algebra admitting a Cartan involution is perfect: `⁅L, L⁆ = L`. -/
theorem derivedSeries_one_eq_top (hθ : θ.IsCartanInvolution) : derivedSeries K L 1 = ⊤ :=
  have := hθ.isKilling
  have := hθ.finiteDimensional
  TauCeti.derivedSeries_one_eq_top_of_isKilling K L

/-- The `-1`-eigenspace `𝔭` of a Cartan involution is the Killing-orthogonal complement of its
fixed subalgebra `𝔨`. -/
theorem orthogonal_fixedSubalgebra_eq_cartanP (hθ : θ.IsCartanInvolution) :
    (killingForm K L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule = θ.cartanP := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · have hsup := (θ.isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit
      hθ.involutive).sup_eq_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
    have hk' := (LieSubalgebra.mem_toSubmodule _).mp hk
    have hkk : killingForm K L k k = 0 := by
      have := (killingForm K L).mem_orthogonal_iff.mp hx k hk
      rwa [map_add,
        killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hk' hp, add_zero] at this
    obtain rfl : k = 0 := by
      by_contra hk₀
      exact (hθ.killingForm_apply_self_neg_of_mem_fixedSubalgebra hk' hk₀).ne hkk
    rwa [zero_add]
  · exact (killingForm K L).mem_orthogonal_iff.mpr fun k hk ↦
      killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP
        ((LieSubalgebra.mem_toSubmodule _).mp hk) hx

/-- A Cartan involution is determined by its fixed subalgebra `𝔨`. -/
theorem eq_of_fixedSubalgebra_eq {θ' : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution)
    (h : θ.toLieHom.fixedSubalgebra = θ'.toLieHom.fixedSubalgebra) : θ = θ' := by
  have hp : θ.cartanP = θ'.cartanP := by
    rw [← hθ.orthogonal_fixedSubalgebra_eq_cartanP, ← hθ'.orthogonal_fixedSubalgebra_eq_cartanP, h]
  exact LinearMap.ext_on_codisjoint
    (θ.isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit hθ.involutive).codisjoint
    (fun k hk ↦ (LieHom.mem_fixedSubalgebra.mp ((LieSubalgebra.mem_toSubmodule _).mp hk)).trans
      (LieHom.mem_fixedSubalgebra.mp (h ▸ (LieSubalgebra.mem_toSubmodule _).mp hk)).symm)
    fun p hp' ↦ (mem_cartanP.mp hp').trans (mem_cartanP.mp (hp ▸ hp')).symm

/-- **Two commuting Cartan involutions are equal.** -/
theorem eq_of_commute {θ' : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution) (hcomm : ∀ x, θ (θ' x) = θ' (θ x)) : θ = θ' := by
  have hzero {θ₁ θ₂ : L ≃ₗ⁅K⁆ L} (h₁ : θ₁.IsCartanInvolution) (h₂ : θ₂.IsCartanInvolution)
      {z : L} (hz₁ : z ∈ θ₁.toLieHom.fixedSubalgebra) (hz₂ : z ∈ θ₂.cartanP) : z = 0 := by
    by_contra hne
    exact (h₁.killingForm_apply_self_neg_of_mem_fixedSubalgebra hz₁ hne).not_gt
      (h₂.killingForm_apply_self_pos_of_mem_cartanP hz₂ hne)
  ext x
  have hfix : (x + θ x) - θ' (x + θ x) ∈ θ.toLieHom.fixedSubalgebra := by
    have h1 : θ (x + θ x) = x + θ x :=
      LieHom.mem_fixedSubalgebra.mp (add_apply_mem_fixedSubalgebra hθ.involutive x)
    rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_sub, hcomm, h1]
  have hu := hzero hθ hθ' hfix (sub_apply_mem_cartanP hθ'.involutive (x + θ x))
  have hP : (x - θ x) + θ' (x - θ x) ∈ θ.cartanP := by
    have h1 := mem_cartanP.mp (sub_apply_mem_cartanP hθ.involutive x)
    rw [mem_cartanP, map_add, hcomm, h1, map_neg, neg_add]
  have hw := hzero hθ' hθ (add_apply_mem_fixedSubalgebra hθ'.involutive (x - θ x)) hP
  have h2 : (θ x - θ' x) + (θ x - θ' x) = 0 := by
    have hcalc : (θ x - θ' x) + (θ x - θ' x) =
        ((x + θ x) - θ' (x + θ x)) - ((x - θ x) + θ' (x - θ x)) := by
      simp only [map_add, map_sub]
      abel
    rw [hcalc, hu, hw, sub_self]
  refine sub_eq_zero.mp ?_
  by_contra hne
  have hpos := hθ.twistedKillingForm_self_pos hne
  have hsum := lt_of_lt_of_le hpos (le_add_of_nonneg_right hpos.le)
  rw [← map_add, h2, map_zero] at hsum
  exact lt_irrefl 0 hsum

/-- On a compact Lie algebra (negative definite Killing form), the identity is the unique Cartan
involution. -/
theorem eq_refl_of_killingForm_self_neg (hθ : θ.IsCartanInvolution)
    (hneg : ∀ x : L, x ≠ 0 → killingForm K L x x < 0) : θ = LieEquiv.refl :=
  hθ.eq_of_commute (isCartanInvolution_refl_iff.mpr hneg) (fun _ ↦ rfl)

/-! ### The fixed subalgebra `𝔨` -/

private theorem posDef_negKillingFormFixed (hθ : θ.IsCartanInvolution) :
    (negKillingFormFixed θ).toQuadraticMap.PosDef := by
  intro x hx
  rw [LinearMap.BilinMap.toQuadraticMap_apply, negKillingFormFixed_apply, neg_pos]
  exact hθ.killingForm_apply_self_neg_of_mem_fixedSubalgebra x.property (by simpa using hx)

/-- The fixed subalgebra `𝔨` of a Cartan involution is the direct sum of its centre and its
derived algebra. -/
theorem isCompl_center_derivedSeries_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    IsCompl (center K θ.toLieHom.fixedSubalgebra)
      (derivedSeries K θ.toLieHom.fixedSubalgebra 1) :=
  have := hθ.finiteDimensional
  (negKillingFormFixed θ).isCompl_center_derivedSeries_one_of_anisotropic
    isSymm_negKillingFormFixed.isRefl (posDef_negKillingFormFixed hθ).anisotropic
    lieInvariant_negKillingFormFixed

/-- The derived algebra of the fixed subalgebra `𝔨` of a Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    IsSemisimple K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) :=
  have := hθ.finiteDimensional
  (negKillingFormFixed θ).isSemisimple_derivedSeries_one_of_anisotropic
    isSymm_negKillingFormFixed.isRefl (posDef_negKillingFormFixed hθ).anisotropic
    lieInvariant_negKillingFormFixed

/-- The fixed subalgebra `𝔨` of a Cartan involution is reductive (its radical equals its
centre). -/
theorem hasCentralRadical_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    HasCentralRadical K θ.toLieHom.fixedSubalgebra :=
  have := hθ.finiteDimensional
  (negKillingFormFixed θ).hasCentralRadical_of_anisotropic
    isSymm_negKillingFormFixed.isRefl (posDef_negKillingFormFixed hθ).anisotropic
    lieInvariant_negKillingFormFixed

/-- The derived algebra of the fixed subalgebra `𝔨` of a Cartan involution has negative definite
Killing form. -/
theorem killingForm_derivedSeries_fixedSubalgebra_self_neg (hθ : θ.IsCartanInvolution)
    {x : derivedSeries K θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) x x < 0 :=
  have := hθ.finiteDimensional
  (negKillingFormFixed θ).killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero
    isSymm_negKillingFormFixed (posDef_negKillingFormFixed hθ) lieInvariant_negKillingFormFixed
    x hx

end IsCartanInvolution

end LinearOrder

/-! ### Real diagonalizability of `ad x` on `𝔭` -/

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- **Real diagonalizability of `ad x` for `x ∈ 𝔭`**: for a Cartan involution `θ` of a real Lie
algebra and `x ∈ θ.cartanP`, the eigenspaces of `ad x` span `L`. -/
theorem IsCartanInvolution.iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L}
    (hθ : θ.IsCartanInvolution) {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ :=
  have := hθ.finiteDimensional
  LinearMap.BilinForm.iSup_eigenspace_eq_top_of_isSelfAdjoint hθ.isSymm_twistedKillingForm
    (fun _ hv ↦ hθ.twistedKillingForm_self_pos hv)
    ((LinearMap.mem_selfAdjointSubmodule _).mp (ad_mem_selfAdjointSubmodule_twistedKillingForm hx))

end Real

end LieEquiv
