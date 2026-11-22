/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

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
Killing-orthogonal complement of `𝔨`, so a Cartan involution is determined by `𝔨`; `𝔨` carries
the negative definite invariant form `B|_𝔨`, so that `𝔨` is reductive and is the direct sum of
its centre and its derived algebra, the latter semisimple with negative definite Killing form; and
over `ℝ`, self-adjointness of `ad x` for `x ∈ 𝔭` with respect to `B_θ` yields diagonalizability
of `ad x`.

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
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top` and
  `LieEquiv.IsCartanInvolution.isSemisimple_ad`: over `ℝ`, `ad x` is diagonalizable for every
  `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter III, §7.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

section General

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- The `-1`-eigenspace of the identity automorphism is `⊥` when `2` is invertible. -/
@[simp]
theorem cartanP_refl [Invertible (2 : R)] :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP, refl_apply, Submodule.mem_bot]
  constructor
  · intro hx
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hx
    simpa using congrArg ((⅟2 : R) • ·) h2
  · rintro rfl
    simp

/-- An involutive Lie automorphism is its own inverse. -/
theorem symm_eq_self_of_involutive {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ x).symm

/-- An intertwining Lie equivalence maps `θ.cartanP` onto `θ'.cartanP`. -/
theorem map_cartanP (e : L ≃ₗ⁅R⁆ L') {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (h : ∀ x, θ' (e x) = e (θ x)) :
    θ.cartanP.map (e : L →ₗ[R] L') = θ'.cartanP := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cartanP] at hx ⊢
    simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, h, hx, map_neg]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_cartanP] at hy ⊢
    apply e.injective
    simp only [coe_toLieHom]
    rw [← h, e.apply_symm_apply, hy, map_neg, e.apply_symm_apply]

/-- `[𝔭, 𝔨] ⊆ 𝔭`: bracketing a `-1`-eigenvector with a fixed vector lands in `cartanP`. -/
theorem lie_mem_cartanP_of_mem_cartanP_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  rw [← lie_skew]
  exact neg_mem (lie_mem_cartanP hy hx)

/-- Symmetric form of `B(𝔨, 𝔭) = 0`: `B(𝔭, 𝔨) = 0`. -/
theorem killingForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra [IsAddTorsionFree R]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x y = 0 := by
  rw [LieModule.traceForm_comm]
  exact killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hy hx

/-- The twisted Killing form of the identity automorphism is minus the Killing form. -/
@[simp]
theorem twistedKillingForm_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).twistedKillingForm = -killingForm R L := by
  ext x y
  simp

/-- An intertwining Lie equivalence is an isometry between the corresponding twisted Killing
forms. -/
theorem twistedKillingForm_map_map_of_intertwine (e : L ≃ₗ⁅R⁆ L')
    {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'} (h : ∀ x, θ' (e x) = e (θ x)) (x y : L) :
    θ'.twistedKillingForm (e x) (e y) = θ.twistedKillingForm x y := by
  simp only [twistedKillingForm_apply, h, killingForm_of_equiv_apply]

/-- On `𝔨` in the right argument, `B_θ(x, y) = -B(x, y)`. -/
theorem twistedKillingForm_apply_of_mem_fixedSubalgebra_right (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    θ.twistedKillingForm x y = -killingForm R L x y := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hy
  simp [hy]

/-- On `𝔭` in the right argument, `B_θ(x, y) = B(x, y)`. -/
theorem twistedKillingForm_apply_of_mem_cartanP_right (θ : L ≃ₗ⁅R⁆ L) {x y : L}
    (hy : y ∈ θ.cartanP) :
    θ.twistedKillingForm x y = killingForm R L x y := by
  rw [mem_cartanP] at hy
  simp [hy]

/-- `𝔨` and `𝔭` are orthogonal for `B_θ` over a base ring without additive torsion. -/
theorem twistedKillingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [IsAddTorsionFree R]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    θ.twistedKillingForm x y = 0 := by
  rw [θ.twistedKillingForm_apply_of_mem_cartanP_right hy]
  exact killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy

/-- Symmetric form of `B_θ(𝔨, 𝔭) = 0`: `B_θ(𝔭, 𝔨) = 0`. -/
theorem twistedKillingForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra [IsAddTorsionFree R]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    θ.twistedKillingForm x y = 0 := by
  rw [θ.twistedKillingForm_apply_of_mem_fixedSubalgebra_right hy,
    killingForm_eq_zero_of_mem_cartanP_of_mem_fixedSubalgebra hx hy, neg_zero]

/-- For an involutive automorphism `θ`, the `B_θ`-adjoint of `ad x` is `-ad (θ x)`. -/
theorem isAdjointPair_twistedKillingForm_ad {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ)
    (x : L) :
    LinearMap.IsAdjointPair θ.twistedKillingForm θ.twistedKillingForm (ad R L x)
      (-ad R L (θ x)) := by
  intro y z
  simp only [twistedKillingForm_apply, ad_apply, Pi.neg_apply, map_neg, neg_neg]
  have h1 : killingForm R L ⁅x, y⁆ (θ z) = -killingForm R L y ⁅x, θ z⁆ := by
    rw [← lie_skew x y, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply]
  have h2 : ⁅x, θ z⁆ = θ ⁅θ x, z⁆ := by
    rw [map_lie, hθ x]
  rw [h1, neg_neg, h2]

end General

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
  constructor
  · intro hθ'
    refine ⟨fun x ↦ e.injective ?_, fun x hx ↦ ?_⟩
    · simp only [coe_toLieHom]
      rw [← h, ← h, hθ'.involutive (e x)]
    · rw [LinearMap.BilinMap.toQuadraticMap_apply,
        ← twistedKillingForm_map_map_of_intertwine e h x x]
      exact hθ'.posDef_twistedKillingForm (e x) (by simpa using hx)
  · intro hθ
    refine ⟨fun y ↦ ?_, fun y hy ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective y
      simp only [coe_toLieHom]
      rw [h, h, hθ.involutive x]
    · obtain ⟨x, rfl⟩ := e.surjective y
      simp only [coe_toLieHom, LinearMap.BilinMap.toQuadraticMap_apply]
      rw [twistedKillingForm_map_map_of_intertwine e h x x]
      exact hθ.posDef_twistedKillingForm x (fun hx ↦ hy (by simp [hx]))

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

/-- The Cartan decomposition `L = 𝔨 ⊕ 𝔭` for a Cartan involution. -/
theorem isCompl_fixedSubalgebra_cartanP (hθ : θ.IsCartanInvolution) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP :=
  θ.isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit hθ.involutive

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

/-- The centre and derived ideal of `𝔨` are orthogonal for the ambient Killing form `B|_𝔨`. -/
theorem killingForm_eq_zero_of_mem_center_of_mem_derivedSeries_fixedSubalgebra
    (hθ : θ.IsCartanInvolution) {z d : θ.toLieHom.fixedSubalgebra}
    (hz : z ∈ center K θ.toLieHom.fixedSubalgebra)
    (hd : d ∈ derivedSeries K θ.toLieHom.fixedSubalgebra 1) :
    killingForm K L (z : L) (d : L) = 0 := by
  have := hθ.finiteDimensional
  have hnd : (negKillingFormFixed θ).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_of_anisotropic _
      (posDef_negKillingFormFixed hθ).anisotropic
  have hortho := LinearMap.BilinForm.orthogonal_derivedSeries_one_eq_center
    (negKillingFormFixed θ) hnd.2 lieInvariant_negKillingFormFixed
  have hz' : z ∈ (negKillingFormFixed θ).orthogonal
      (derivedSeries K θ.toLieHom.fixedSubalgebra 1).toSubmodule := by
    rw [← LieAlgebra.InvariantForm.orthogonal_toSubmodule (L := θ.toLieHom.fixedSubalgebra)
      (negKillingFormFixed θ) lieInvariant_negKillingFormFixed, hortho]
    exact hz
  have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hz') d hd
  rw [negKillingFormFixed_apply, neg_eq_zero, LieModule.traceForm_comm] at h0
  exact h0

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

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

namespace IsCartanInvolution

/-- **Diagonalizability of `ad x` on `𝔭`.** For a Cartan involution of a real Lie algebra and
every `x ∈ 𝔭`, the eigenspaces of `ad x` over `ℝ` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have : FiniteDimensional ℝ L := hθ.finiteDimensional
  exact LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top
    (fun _ ↦ hθ.twistedKillingForm_self_pos)
    ((LinearMap.mem_selfAdjointSubmodule _).mp
      (θ.ad_mem_selfAdjointSubmodule_twistedKillingForm hx))

/-- For a Cartan involution of a real Lie algebra and every `x ∈ 𝔭`, the adjoint operator `ad x`
is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsCartanInvolution

end Real

end LieEquiv
