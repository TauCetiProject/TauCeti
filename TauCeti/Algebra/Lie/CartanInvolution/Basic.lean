/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Logic.Equiv.Basic

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
of `L` is nondegenerate, so a Lie algebra with a Cartan involution is semisimple; `𝔭` is the
Killing-orthogonal complement of `𝔨`, so a Cartan involution is determined by `𝔨`; and `𝔨`
carries the negative definite invariant form `B|_𝔨`, so that `𝔨` is reductive and is the direct
sum of its centre and its derived algebra, the latter semisimple with negative definite Killing
form.

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
* `LieEquiv.IsCartanInvolution.eq_of_fixedSubalgebra_eq`: a Cartan involution is determined by
  `𝔨`.
* `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`: `𝔨` is
  reductive and splits as the direct sum of its centre and its derived algebra, which is
  semisimple with negative definite Killing form.

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

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- A *Cartan involution* of a Lie algebra `L` over an ordered field: an involutive Lie algebra
automorphism `θ` whose twisted Killing form `B_θ(x, y) = -B(x, θ y)` is positive definite. -/
structure IsCartanInvolution (θ : L ≃ₗ⁅K⁆ L) : Prop where
  /-- A Cartan involution is an involution. -/
  involutive : Function.Involutive θ
  /-- The twisted Killing form `B_θ` of a Cartan involution is positive definite. -/
  posDef_twistedKillingForm : θ.twistedKillingForm.toQuadraticMap.PosDef

/-- An involution is a Cartan involution exactly when `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅K⁆ L} :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → killingForm K L x (θ x) < 0 := by
  refine ⟨fun h ↦ ⟨h.involutive, fun x hx ↦ ?_⟩, fun h ↦ ⟨h.1, fun x hx ↦ ?_⟩⟩
  · have := h.posDef_twistedKillingForm x hx
    rwa [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos] at this
  · rw [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos]
    exact h.2 x hx

omit [IsStrictOrderedRing K] in
/-- Transport of `IsCartanInvolution` along an intertwining Lie equivalence. -/
theorem isCartanInvolution_iff_of_intertwine {L' : Type*} [LieRing L'] [LieAlgebra K L']
    (e : L ≃ₗ⁅K⁆ L') {θ : L ≃ₗ⁅K⁆ L} {θ' : L' ≃ₗ⁅K⁆ L'} (h : ∀ x, θ' (e x) = e (θ x)) :
    θ'.IsCartanInvolution ↔ θ.IsCartanInvolution := by
  refine ⟨fun hθ' ↦ ⟨(e.toLinearEquiv.toEquiv.involutive_iff_of_intertwine h).mp hθ'.involutive,
      fun x hx ↦ ?_⟩,
    fun hθ ↦ ⟨(e.toLinearEquiv.toEquiv.involutive_iff_of_intertwine h).mpr hθ.involutive,
      fun y hy ↦ ?_⟩⟩
  · rw [LinearMap.BilinMap.toQuadraticMap_apply,
      ← twistedKillingForm_map_map_of_intertwine e h x x]
    exact hθ'.posDef_twistedKillingForm (e x) (by simpa using hx)
  · obtain ⟨x, hx⟩ := e.surjective y
    rw [← hx, LinearMap.BilinMap.toQuadraticMap_apply]
    change 0 < θ'.twistedKillingForm (e x) (e x)
    rw [twistedKillingForm_map_map_of_intertwine e h x x]
    exact hθ.posDef_twistedKillingForm x (fun hx0 ↦ hy (by rw [← hx, hx0, map_zero]))

omit [IsStrictOrderedRing K] in
/-- Conjugating a Lie automorphism by a Lie equivalence preserves the Cartan-involution
property. -/
theorem isCartanInvolution_conj {L' : Type*} [LieRing L'] [LieAlgebra K L']
    (e : L ≃ₗ⁅K⁆ L') (θ : L ≃ₗ⁅K⁆ L) :
    ((e.symm.trans θ).trans e).IsCartanInvolution ↔ θ.IsCartanInvolution :=
  isCartanInvolution_iff_of_intertwine e fun x ↦ by simp

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

omit [IsStrictOrderedRing K] in
/-- `B_θ(x, x) > 0` for every nonzero `x`. -/
theorem twistedKillingForm_self_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.twistedKillingForm x x :=
  hθ.posDef_twistedKillingForm x hx

omit [IsStrictOrderedRing K] in
/-- `B_θ(x, x) ≥ 0` for every `x`. -/
theorem twistedKillingForm_self_nonneg (hθ : θ.IsCartanInvolution) (x : L) :
    0 ≤ θ.twistedKillingForm x x :=
  hθ.posDef_twistedKillingForm.nonneg x

omit [IsStrictOrderedRing K] in
/-- The twisted Killing form of a Cartan involution is symmetric. -/
theorem isSymm_twistedKillingForm (hθ : θ.IsCartanInvolution) :
    θ.twistedKillingForm.IsSymm :=
  θ.isSymm_twistedKillingForm hθ.involutive

omit [IsStrictOrderedRing K] in
/-- A Cartan involution is its own inverse. -/
theorem symm_eq (hθ : θ.IsCartanInvolution) : θ.symm = θ :=
  symm_eq_self_of_involutive hθ.involutive

omit [IsStrictOrderedRing K] in
/-- The twisted Killing form of a Cartan involution is nondegenerate. -/
theorem twistedKillingForm_nondegenerate (hθ : θ.IsCartanInvolution) :
    θ.twistedKillingForm.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_of_anisotropic θ.twistedKillingForm
    hθ.posDef_twistedKillingForm.anisotropic

/-- For a Cartan involution, `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem killingForm_apply_apply_neg (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    killingForm K L x (θ x) < 0 :=
  (isCartanInvolution_iff.mp hθ).2 x hx

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

omit [IsStrictOrderedRing K] in
/-- A Lie algebra with a Cartan involution has nondegenerate Killing form. -/
theorem isKilling (hθ : θ.IsCartanInvolution) : IsKilling K L :=
  (TauCeti.isKilling_iff_killingForm_nondegenerate K L).mpr
    ⟨fun x hx ↦ hθ.twistedKillingForm_nondegenerate.1 x fun y ↦ by
      rw [twistedKillingForm_apply, hx (θ y), neg_zero],
    fun y hy ↦ by
      have hsymm : θ.symm y = 0 := hθ.twistedKillingForm_nondegenerate.2 (θ.symm y) fun x ↦ by
        rw [twistedKillingForm_apply, apply_symm_apply, hy x, neg_zero]
      exact (θ.symm_apply_eq.mp hsymm).trans (map_zero θ)⟩

omit [IsStrictOrderedRing K] in
/-- A Lie algebra with a Cartan involution is finite-dimensional, since its Killing form is
nondegenerate. -/
theorem finiteDimensional (hθ : θ.IsCartanInvolution) : FiniteDimensional K L :=
  have := hθ.isKilling
  TauCeti.finite_of_isKilling

omit [IsStrictOrderedRing K] in
/-- A Lie algebra with a Cartan involution is semisimple. -/
theorem isSemisimple (hθ : θ.IsCartanInvolution) : IsSemisimple K L :=
  have := hθ.isKilling
  have := hθ.finiteDimensional
  inferInstance

/-- The Cartan decomposition `L = 𝔨 ⊕ 𝔭` for a Cartan involution. -/
theorem isCompl_fixedSubalgebra_cartanP (hθ : θ.IsCartanInvolution) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP :=
  θ.isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit hθ.involutive

/-- The `-1`-eigenspace `𝔭` of a Cartan involution is the Killing-orthogonal complement of its
fixed subalgebra `𝔨`. -/
theorem orthogonal_fixedSubalgebra_eq_cartanP (hθ : θ.IsCartanInvolution) :
    (killingForm K L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule = θ.cartanP := by
  have h2 : IsSMulRegular K (2 : K) := two_ne_zero.isUnit.isRegular.left.isSMulRegular
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · have hsup := (θ.isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit
      hθ.involutive).sup_eq_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
    have hk' := (LieSubalgebra.mem_toSubmodule _).mp hk
    have hkk : killingForm K L k k = 0 := by
      have := (killingForm K L).mem_orthogonal_iff.mp hx k hk
      rwa [map_add,
        killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP h2 hk' hp, add_zero] at this
    obtain rfl : k = 0 := by
      by_contra hk₀
      exact (hθ.killingForm_apply_self_neg_of_mem_fixedSubalgebra hk' hk₀).ne hkk
    rwa [zero_add]
  · exact (killingForm K L).mem_orthogonal_iff.mpr fun k hk ↦
      killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP h2
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

/-- The fixed subalgebra `𝔨` of a Cartan involution is reductive (`HasCentralRadical`). -/
theorem hasCentralRadical_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    LieAlgebra.HasCentralRadical K θ.toLieHom.fixedSubalgebra :=
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

end LieEquiv
