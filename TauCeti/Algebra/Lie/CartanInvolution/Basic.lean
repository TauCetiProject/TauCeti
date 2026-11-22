/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Cartan involutions

A *Cartan involution* of a Lie algebra `L` over a partially ordered commutative ring is an
involutive Lie algebra automorphism `θ` whose twisted Killing form `B_θ(x, y) = -B(x, θ y)` is
positive definite, `B` being the Killing form. Over `ℝ` these are the Cartan involutions of real
semisimple Lie algebras, and `L = 𝔨 ⊕ 𝔭` (`LieEquiv.isCompl_fixedSubalgebra_cartanP`) is the
Cartan decomposition.

For a Cartan involution, `B_θ` is a positive definite symmetric form on `L` for which `θ` is
orthogonal, `ad x` is skew-adjoint for `x ∈ 𝔨` and self-adjoint for `x ∈ 𝔭` (see
`TauCeti.Algebra.Lie.CartanInvolution.Decomposition`). This file adds:

* nondegeneracy of the Killing form (`LieEquiv.IsCartanInvolution.isKilling`), hence finiteness and
  semisimplicity over a field (`LieEquiv.IsCartanInvolution.finiteDimensional`,
  `LieEquiv.IsCartanInvolution.isSemisimple`);
* signs of the Killing form when addition is strictly monotone: negative definite on `𝔨` and
  positive definite on `𝔭`;
* uniqueness of Cartan involutions: two commuting Cartan involutions are equal
  (`LieEquiv.IsCartanInvolution.eq_of_commute`), on a Lie algebra with negative-definite
  Killing form the identity is the unique Cartan involution
  (`LieEquiv.IsCartanInvolution.eq_refl_of_killingForm_neg`), and over an additively torsion-free
  ordered field a Cartan involution is determined by either `𝔨` or `𝔭`, which are mutual
  Killing-orthogonal complements;
* structure of the fixed subalgebra `𝔨`: `𝔨` is reductive and splits as the direct sum of its
  centre and its derived algebra, the latter semisimple with negative definite Killing form.

Real adjoint diagonalizability is in `TauCeti/Algebra/Lie/CartanInvolution/Spectral.lean`, and
reductive Cartan involutions are in `TauCeti/Algebra/Lie/CartanInvolution/Reductive.lean`.

## Main definitions

* `LieEquiv.IsCartanInvolution`: the predicate that `θ` is a Cartan involution.

## Main results

* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.finiteDimensional`,
  `LieEquiv.IsCartanInvolution.isSemisimple`, `LieEquiv.IsCartanInvolution.restrict`: a Lie
  algebra with a Cartan involution is Killing, hence finite-dimensional and semisimple over a field,
  and Cartan involutions restrict to Lie ideals over a PID.
* `LieEquiv.IsCartanInvolution.killingForm_apply_self_neg_of_mem_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_apply_self_pos_of_mem_cartanP`: the Killing form is
  negative definite on `𝔨` and positive definite on `𝔭`.
* `LieEquiv.IsCartanInvolution.eq_of_commute`,
  `LieEquiv.IsCartanInvolution.eq_refl_of_killingForm_neg`: commuting Cartan involutions agree, and
  only the identity is Cartan when the Killing form is negative definite.
* `LieEquiv.IsCartanInvolution.orthogonal_fixedSubalgebra_eq_cartanP`,
  `LieEquiv.IsCartanInvolution.orthogonal_cartanP_eq_fixedSubalgebra`: `𝔨` and `𝔭` are mutual
  Killing-orthogonal complements.
* `LieEquiv.IsCartanInvolution.eq_of_fixedSubalgebra_eq`,
  `LieEquiv.IsCartanInvolution.eq_of_cartanP_eq`: a Cartan involution is determined by `𝔨` or `𝔭`.
* `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`:
  structure of `𝔨`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter III, §7.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv

/-! ### Cartan involutions over a partially ordered commutative ring -/

section PartialOrder

variable {R L L' : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- A *Cartan involution* of a Lie algebra `L` over a partially ordered commutative ring: an
involutive Lie algebra automorphism `θ` whose twisted Killing form `B_θ(x, y) = -B(x, θ y)` is
positive definite. -/
structure IsCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop where
  /-- A Cartan involution is an involution. -/
  involutive : Function.Involutive θ
  /-- The twisted Killing form `B_θ` of a Cartan involution is positive definite. -/
  posDef_twistedKillingForm : θ.twistedKillingForm.toQuadraticMap.PosDef

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅R⁆ L}

/-- A Cartan involution is its own inverse. -/
theorem symm_eq (hθ : θ.IsCartanInvolution) : θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ.involutive x).symm

/-- The twisted Killing form of a Cartan involution is strictly positive on nonzero vectors. -/
theorem twistedKillingForm_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.twistedKillingForm x x :=
  hθ.posDef_twistedKillingForm x hx

/-- The twisted Killing form of a Cartan involution is symmetric. -/
theorem twistedKillingForm_isSymm (hθ : θ.IsCartanInvolution) : θ.twistedKillingForm.IsSymm :=
  isSymm_twistedKillingForm hθ.involutive

/-- The twisted Killing form of a Cartan involution is nondegenerate. -/
theorem twistedKillingForm_nondegenerate (hθ : θ.IsCartanInvolution) :
    θ.twistedKillingForm.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_of_anisotropic _ hθ.posDef_twistedKillingForm.anisotropic

/-- Conjugation by a Lie algebra equivalence preserves Cartan involutions. -/
theorem conj (hθ : θ.IsCartanInvolution) (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsCartanInvolution where
  involutive y := by simp [hθ.involutive _]
  posDef_twistedKillingForm y hy := by
    have h0 : e.symm y ≠ 0 := fun h ↦ hy (by simpa using congrArg e h)
    rw [LinearMap.BilinMap.toQuadraticMap_apply, ← apply_symm_apply e y,
      twistedKillingForm_conj_apply]
    exact hθ.twistedKillingForm_pos h0

/-- A Lie algebra with a Cartan involution has nondegenerate Killing form. -/
theorem isKilling (hθ : θ.IsCartanInvolution) : IsKilling R L := by
  refine ⟨(LieSubmodule.toSubmodule_eq_bot _).mp <|
    (LieIdeal.coe_killingCompl_top R L).trans (eq_bot_iff.mpr fun x hx ↦ ?_)⟩
  exact hθ.twistedKillingForm_nondegenerate.left x fun y ↦ by
    rw [twistedKillingForm_apply, LinearMap.mem_ker.mp hx, LinearMap.zero_apply, neg_zero]

/-- Restricting a Cartan involution to a Lie ideal yields a Cartan involution of that ideal,
over a partially ordered principal ideal domain. -/
theorem restrict [IsDomain R] [IsPrincipalIdealRing R] (hθ : θ.IsCartanInvolution)
    {I : LieIdeal R L} (θI : I ≃ₗ⁅R⁆ I) (hθI : ∀ x : I, (θI x : L) = θ x) :
    θI.IsCartanInvolution where
  involutive x := Subtype.ext (by simp [hθI, hθ.involutive x])
  posDef_twistedKillingForm x hx := by
    have := hθ.isKilling
    have := TauCeti.free_of_isKilling (R := R) (L := L)
    have := TauCeti.finite_of_isKilling (R := R) (L := L)
    have hkf : killingForm R I x (θI x) = killingForm R L x (θ x) := by
      have h := LinearMap.congr_fun₂ (LieIdeal.killingForm_eq (R := R) (L := L) (I := I))
        x (θI x)
      change killingForm R I x (θI x) = killingForm R L x (θI x) at h
      rwa [hθI x] at h
    rw [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, hkf,
      ← twistedKillingForm_apply]
    exact hθ.twistedKillingForm_pos (fun h ↦ hx (Subtype.ext h))

omit [PartialOrder R] in
private theorem killingForm_eq_zero_of_isUnit_two (h2 : IsUnit (2 : R))
    {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [mem_cartanP] at hy
  have h : killingForm R L x y = -killingForm R L x y := by
    conv_lhs => rw [← killingForm_of_equiv_apply θ, hx, hy, map_neg]
  have hmul : killingForm R L x y * 2 = 0 := by
    rw [mul_two, eq_neg_iff_add_eq_zero.mp h]
  exact h2.mul_left_eq_zero.mp hmul

/-- The `-1`-eigenspace `𝔭` of a Cartan involution is the Killing-orthogonal complement of its
fixed subalgebra `𝔨`. -/
theorem orthogonal_fixedSubalgebra_eq_cartanP (hθ : θ.IsCartanInvolution)
    (h2 : IsUnit (2 : R)) :
    (killingForm R L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule = θ.cartanP := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · have hsup := (θ.isCompl_fixedSubalgebra_cartanP h2 hθ.involutive).sup_eq_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
    have hk' := (LieSubalgebra.mem_toSubmodule _).mp hk
    have hkk : killingForm R L k k = 0 := by
      have := (killingForm R L).mem_orthogonal_iff.mp hx k hk
      rwa [map_add, killingForm_eq_zero_of_isUnit_two h2 hk' hp, add_zero] at this
    obtain rfl : k = 0 := by
      by_contra hk₀
      have hpos := hθ.twistedKillingForm_pos hk₀
      have hθk : θ k = k := LieHom.mem_fixedSubalgebra.mp hk'
      rw [twistedKillingForm_apply, hθk, hkk, neg_zero] at hpos
      exact lt_irrefl 0 hpos
    rwa [zero_add]
  · exact (killingForm R L).mem_orthogonal_iff.mpr fun k hk ↦
      killingForm_eq_zero_of_isUnit_two h2 ((LieSubalgebra.mem_toSubmodule _).mp hk) hx

/-- The Killing-orthogonal complement of `θ.cartanP` is the fixed subalgebra `𝔨`. -/
theorem orthogonal_cartanP_eq_fixedSubalgebra (hθ : θ.IsCartanInvolution)
    (h2 : IsUnit (2 : R)) :
    (killingForm R L).orthogonal θ.cartanP = θ.toLieHom.fixedSubalgebra.toSubmodule := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · have hsup := (θ.isCompl_fixedSubalgebra_cartanP h2 hθ.involutive).sup_eq_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
    have hk' := (LieSubalgebra.mem_toSubmodule _).mp hk
    have hpp : killingForm R L p p = 0 := by
      have := (killingForm R L).mem_orthogonal_iff.mp hx p hp
      rw [map_add] at this
      have hpk : killingForm R L p k = 0 := by
        rw [traceForm_comm]
        exact killingForm_eq_zero_of_isUnit_two h2 hk' hp
      rwa [hpk, zero_add] at this
    obtain rfl : p = 0 := by
      by_contra hp₀
      have hpos := hθ.twistedKillingForm_pos hp₀
      rw [twistedKillingForm_apply, mem_cartanP.mp hp, map_neg, neg_neg, hpp] at hpos
      exact lt_irrefl 0 hpos
    rwa [add_zero]
  · exact (killingForm R L).mem_orthogonal_iff.mpr fun p hp ↦ by
      rw [traceForm_comm]
      exact killingForm_eq_zero_of_isUnit_two h2 ((LieSubalgebra.mem_toSubmodule _).mp hx) hp

/-- A Cartan involution is determined by its fixed subalgebra `𝔨`. -/
theorem eq_of_fixedSubalgebra_eq {θ' : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution) (h2 : IsUnit (2 : R))
    (h : θ.toLieHom.fixedSubalgebra = θ'.toLieHom.fixedSubalgebra) : θ = θ' := by
  have hp : θ.cartanP = θ'.cartanP := by
    rw [← hθ.orthogonal_fixedSubalgebra_eq_cartanP h2,
      ← hθ'.orthogonal_fixedSubalgebra_eq_cartanP h2, h]
  exact LinearMap.ext_on_codisjoint
    (θ.isCompl_fixedSubalgebra_cartanP h2 hθ.involutive).codisjoint
    (fun k hk ↦ (LieHom.mem_fixedSubalgebra.mp ((LieSubalgebra.mem_toSubmodule _).mp hk)).trans
      (LieHom.mem_fixedSubalgebra.mp (h ▸ (LieSubalgebra.mem_toSubmodule _).mp hk)).symm)
    fun p hp' ↦ (mem_cartanP.mp hp').trans (mem_cartanP.mp (hp ▸ hp')).symm

/-- A Cartan involution is uniquely determined by its `-1`-eigenspace `𝔭`: two Cartan involutions
with the same `-1`-eigenspace are equal. -/
theorem eq_of_cartanP_eq {θ' : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution) (h2 : IsUnit (2 : R)) (h : θ.cartanP = θ'.cartanP) :
    θ = θ' := by
  apply hθ.eq_of_fixedSubalgebra_eq hθ' h2
  apply LieSubalgebra.toSubmodule_injective
  rw [← hθ.orthogonal_cartanP_eq_fixedSubalgebra h2,
    ← hθ'.orthogonal_cartanP_eq_fixedSubalgebra h2, h]

end IsCartanInvolution

/-- Conjugating an automorphism by a Lie algebra equivalence preserves and reflects being a Cartan
involution. -/
@[simp]
theorem isCartanInvolution_conj_iff {θ : L ≃ₗ⁅R⁆ L} (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsCartanInvolution ↔ θ.IsCartanInvolution :=
  ⟨fun h ↦ by
    have h' := h.conj e.symm
    have heq : e.symm.symm.trans ((e.symm.trans (θ.trans e)).trans e.symm) = θ :=
      LieEquiv.ext fun x ↦ by simp
    rwa [heq] at h', fun h ↦ h.conj e⟩

/-- A nontrivial abelian Lie algebra admits no Cartan involution. -/
theorem not_isCartanInvolution_of_isLieAbelian [IsLieAbelian L] [Nontrivial L]
    (θ : L ≃ₗ⁅R⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  have := hθ.isKilling
  exact not_subsingleton L (TauCeti.subsingleton_of_isKilling_of_isLieAbelian R L)

end PartialOrder

/-! ### Killing-form signs and commuting uniqueness -/

section OrderedAddCommRing

variable {R L : Type*} [CommRing R] [PartialOrder R] [AddLeftStrictMono R]
  [LieRing L] [LieAlgebra R L]

/-- An involution is a Cartan involution exactly when `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → killingForm R L x (θ x) < 0 := by
  refine ⟨fun h ↦ ⟨h.involutive, fun x hx ↦ ?_⟩, fun h ↦ ⟨h.left, fun x hx ↦ ?_⟩⟩
  · have := h.posDef_twistedKillingForm x hx
    rwa [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos] at this
  · rw [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos]
    exact h.right x hx

/-- The identity automorphism is a Cartan involution iff the Killing form is strictly negative on
nonzero vectors. -/
theorem isCartanInvolution_refl_iff :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).IsCartanInvolution ↔
      ∀ x : L, x ≠ 0 → killingForm R L x x < 0 := by
  simp [isCartanInvolution_iff, Function.Involutive]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅R⁆ L}

/-- For a Cartan involution, `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem killingForm_apply_apply_neg (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    killingForm R L x (θ x) < 0 :=
  (isCartanInvolution_iff.mp hθ).right x hx

/-- The Killing form is negative definite on the fixed subalgebra `𝔨` of a Cartan
involution. -/
theorem killingForm_apply_self_neg_of_mem_fixedSubalgebra (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx₀ : x ≠ 0) : killingForm R L x x < 0 := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  have := hθ.killingForm_apply_apply_neg hx₀
  rwa [hx] at this

/-- The Killing form is nonpositive on the fixed subalgebra `𝔨` of a Cartan involution. -/
theorem killingForm_nonpos_of_mem_fixedSubalgebra (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) : killingForm R L x x ≤ 0 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp
  · exact (hθ.killingForm_apply_self_neg_of_mem_fixedSubalgebra hx hx₀).le

/-- The Killing form is positive definite on the `-1`-eigenspace `𝔭` of a Cartan involution. -/
theorem killingForm_apply_self_pos_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) (hx₀ : x ≠ 0) : 0 < killingForm R L x x := by
  have := hθ.killingForm_apply_apply_neg hx₀
  rwa [mem_cartanP.mp hx, map_neg, neg_lt_zero] at this

/-- The Killing form is nonnegative on the `-1`-eigenspace `𝔭` of a Cartan involution. -/
theorem killingForm_nonneg_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) : 0 ≤ killingForm R L x x := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp
  · exact (hθ.killingForm_apply_self_pos_of_mem_cartanP hx hx₀).le

/-- Two commuting Cartan involutions are equal. -/
theorem eq_of_commute {θ' : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution) (hcomm : ∀ x, θ (θ' x) = θ' (θ x)) :
    θ = θ' := by
  refine LieEquiv.ext fun x ↦ sub_eq_zero.mp ?_
  set v : L := θ x - θ' x
  have hθ'_v : θ' v = -θ v := by
    simp only [v, map_sub, hθ'.involutive x, hcomm x, hθ.involutive x, neg_sub]
  have hsum : θ'.twistedKillingForm v v + θ.twistedKillingForm v v = 0 := by
    rw [twistedKillingForm_apply, twistedKillingForm_apply, hθ'_v, map_neg, neg_neg,
      add_neg_cancel]
  by_contra hv
  have hpos : (0 : R) < θ'.twistedKillingForm v v + θ.twistedKillingForm v v :=
    add_pos (hθ'.twistedKillingForm_pos hv) (hθ.twistedKillingForm_pos hv)
  rw [hsum] at hpos
  exact lt_irrefl 0 hpos

/-- On a compact Lie algebra (negative-definite Killing form), the identity is the unique Cartan
involution. -/
theorem eq_refl_of_killingForm_neg (hθ : θ.IsCartanInvolution)
    (hneg : ∀ x : L, x ≠ 0 → killingForm R L x x < 0) :
    θ = LieEquiv.refl :=
  hθ.eq_of_commute (isCartanInvolution_refl_iff.mpr hneg) fun _ ↦ rfl

end IsCartanInvolution

end OrderedAddCommRing

/-! ### Structure over partially ordered fields -/

section Field

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

section PartialOrder

variable [PartialOrder K]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

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

/-! ### The fixed subalgebra `𝔨` -/

private theorem posDef_negKillingFormFixed (hθ : θ.IsCartanInvolution) :
    (negKillingFormFixed θ).toQuadraticMap.PosDef := by
  intro x hx
  have hx' : (x : L) ≠ 0 := by simpa using hx
  have hfx : θ (x : L) = x := LieHom.mem_fixedSubalgebra.mp x.property
  rw [LinearMap.BilinMap.toQuadraticMap_apply, negKillingFormFixed_apply]
  nth_rw 2 [← hfx]
  rw [← twistedKillingForm_apply]
  exact hθ.twistedKillingForm_pos hx'

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

/-- The fixed subalgebra `𝔨` of a Cartan involution is reductive (has central radical). -/
theorem hasCentralRadical_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    HasCentralRadical K θ.toLieHom.fixedSubalgebra :=
  have := hθ.finiteDimensional
  (negKillingFormFixed θ).hasCentralRadical_of_anisotropic
    isSymm_negKillingFormFixed.isRefl (posDef_negKillingFormFixed hθ).anisotropic
    lieInvariant_negKillingFormFixed

end IsCartanInvolution

end PartialOrder

section LinearOrder

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The derived algebra of the fixed subalgebra `𝔨` of a Cartan involution has negative definite
Killing form. -/
theorem IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution)
    {x : derivedSeries K θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) x x < 0 :=
  have := hθ.finiteDimensional
  (negKillingFormFixed θ).killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero
    isSymm_negKillingFormFixed (posDef_negKillingFormFixed hθ) lieInvariant_negKillingFormFixed
    x hx

end LinearOrder

end Field

end LieEquiv
