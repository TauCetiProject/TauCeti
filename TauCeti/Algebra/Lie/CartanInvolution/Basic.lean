/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
public import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Reductive.Fixed
import TauCeti.Algebra.Lie.Subalgebra.Automorphism
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.BilinearForm.Basic
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
Killing-orthogonal complement of `𝔨`, so a Cartan involution is determined by `𝔨`; and `𝔨` carries
the negative definite invariant form `B|_𝔨`, so that `𝔨` is the direct sum of its centre and its
derived algebra, the latter semisimple with negative definite Killing form. Over `ℝ`, `ad x` is
diagonalizable for every `x ∈ 𝔭` (`LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`).

A **reductive Cartan involution** (`LieEquiv.IsReductiveCartanInvolution`) is an involutive
automorphism whose restriction to the derived ideal `⁅L, L⁆` is a Cartan involution. Over an
ordered field, such a Lie algebra has central radical (`LieAlgebra.HasCentralRadical`). For any
automorphism `θ` of a finite-dimensional reductive Lie algebra of characteristic zero, `θ`
preserves both `Z(L)` and `⁅L, L⁆`, splitting `θ.cartanP` into the disjoint submodules
`θ.cartanP ⊓ Z(L)` and `θ.cartanP ⊓ ⁅L, L⁆` whose supremum is `θ.cartanP`. Conversely, extending a
Cartan involution of `⁅L, L⁆` by any linear involution of `Z(L)` yields a reductive Cartan
involution.

## Main definitions

* `LieEquiv.IsCartanInvolution`: the predicate that `θ` is a Cartan involution.
* `LieEquiv.IsReductiveCartanInvolution`: the predicate that `θ` is involutive and restricts to a
  Cartan involution on `derivedSeries K L 1`.

## Main results

* `LieEquiv.map_maximal_abelian_cartanP`: intertwining Lie equivalences transport maximal abelian
  subspaces of `θ.cartanP`.
* `LieEquiv.IsCartanInvolution.killingForm_apply_self_neg_of_mem_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_apply_self_pos_of_mem_cartanP`: the Killing form is
  negative definite on `𝔨` and positive definite on `𝔭`.
* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.isSemisimple`: a Lie
  algebra with a Cartan involution has nondegenerate Killing form, hence is finite-dimensional
  (`LieEquiv.IsCartanInvolution.finiteDimensional`) and semisimple.
* `LieEquiv.IsCartanInvolution.orthogonal_fixedSubalgebra_eq_cartanP`,
  `LieEquiv.IsCartanInvolution.orthogonal_cartanP_eq_fixedSubalgebra`: `𝔨` and `𝔭` are mutual
  Killing-orthogonal complements.
* `LieEquiv.IsCartanInvolution.eq_of_fixedSubalgebra_eq`: a Cartan involution is determined by
  `𝔨`.
* `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`: `𝔨` is
  reductive and the direct sum of its centre and its derived algebra, which is semisimple with
  negative definite Killing form.
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: for `x ∈ θ.cartanP` over `ℝ`,
  `ad ℝ L x` is diagonalizable over `ℝ`.
* `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical`,
  `LieEquiv.sup_cartanP_inf_center_derivedSeries`,
  `LieEquiv.exists_isReductiveCartanInvolution_extend`: structure and extension of reductive
  Cartan involutions.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter III, §7.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv

/-! ### Additional decomposition and transport lemmas -/

section CommRing

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- An intertwining equivalence maps `θ.cartanP` onto `θ'.cartanP`. -/
theorem map_cartanP {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'} (e : L ≃ₗ⁅R⁆ L')
    (h : ∀ x, θ' (e x) = e (θ x)) :
    θ.cartanP.map (e : L →ₗ[R] L') = θ'.cartanP := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cartanP, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, h, mem_cartanP.mp hx,
      map_neg]
  · intro hy
    refine ⟨e.symm y, mem_cartanP.mpr (e.injective ?_), by simp⟩
    simp only [coe_toLieHom]
    rw [← h, e.apply_symm_apply, mem_cartanP.mp hy, map_neg, e.apply_symm_apply]

/-- Conjugating `θ` by `e` transports `θ.cartanP` along `e`. -/
theorem cartanP_conj (θ : L ≃ₗ⁅R⁆ L) (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).cartanP = θ.cartanP.map (e : L →ₗ[R] L') :=
  (map_cartanP e fun x ↦ by simp).symm

/-- An intertwining Lie equivalence `e : L ≃ₗ⁅R⁆ L'` maps maximal abelian subspaces of
`θ.cartanP` to maximal abelian subspaces of `θ'.cartanP`. -/
theorem map_maximal_abelian_cartanP {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (e : L ≃ₗ⁅R⁆ L') (he : ∀ x, θ' (e x) = e (θ x)) {𝔞 : Submodule R L}
    (h𝔞 : Maximal
      (fun 𝔟 : Submodule R L ↦ 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) 𝔞) :
    Maximal
      (fun 𝔟 : Submodule R L' ↦ 𝔟 ≤ θ'.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0)
      (𝔞.map (e : L →ₗ[R] L')) := by
  have hmapP : θ.cartanP.map (e : L →ₗ[R] L') = θ'.cartanP := map_cartanP e he
  refine ⟨⟨?_, ?_⟩, fun 𝔟' ⟨h𝔟'P, h𝔟'ab⟩ hle ↦ ?_⟩
  · rw [← hmapP]
    exact Submodule.map_mono h𝔞.prop.left
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, ← e.map_lie,
      h𝔞.prop.right x hx y hy, map_zero]
  · let 𝔟 : Submodule R L := 𝔟'.map (e.symm : L' →ₗ[R] L)
    have he_symm : ∀ y, θ (e.symm y) = e.symm (θ' y) := fun y ↦ e.injective <| by
      simp only [coe_toLieHom]
      rw [← he, e.apply_symm_apply, e.apply_symm_apply]
    have h𝔟P : 𝔟 ≤ θ.cartanP := by
      rw [← map_cartanP e.symm he_symm]
      exact Submodule.map_mono h𝔟'P
    have h𝔟ab : ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0 := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, ← e.symm.map_lie, h𝔟'ab x hx y hy,
        map_zero]
    have h𝔞_le : 𝔞 ≤ 𝔟 := fun x hx ↦ ⟨e x, hle ⟨x, hx, rfl⟩, by simp⟩
    have h𝔟_le : 𝔟 ≤ 𝔞 := h𝔞.le_of_ge ⟨h𝔟P, h𝔟ab⟩ h𝔞_le
    intro y hy
    exact ⟨e.symm y, h𝔟_le ⟨y, hy, rfl⟩, by simp⟩

/-- The inverse of a Lie automorphism has the same `-1`-eigenspace. -/
@[simp]
theorem cartanP_symm (θ : L ≃ₗ⁅R⁆ L) : θ.symm.cartanP = θ.cartanP := by
  ext x
  rw [mem_cartanP, mem_cartanP, symm_apply_eq, map_neg, eq_comm, neg_eq_iff_eq_neg]

/-- Bracketing an element of `θ.cartanP` with a fixed element stays in `θ.cartanP`. -/
theorem lie_mem_cartanP_of_mem_cartanP_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [mem_cartanP, θ.map_lie, mem_cartanP.mp hx, hy', neg_lie]

/-- The twisted Killing form of the identity automorphism is the negative Killing form. -/
@[simp]
theorem twistedKillingForm_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).twistedKillingForm = -killingForm R L := by
  ext x y
  simp

/-- The twisted Killing form of a conjugate automorphism is the transport of the original twisted
Killing form. -/
theorem twistedKillingForm_conj_apply (θ : L ≃ₗ⁅R⁆ L) (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    (e.symm.trans (θ.trans e)).twistedKillingForm (e x) (e y) = θ.twistedKillingForm x y := by
  simp

/-- On a fixed second argument, the Killing form is the negative of the twisted Killing form. -/
theorem killingForm_eq_neg_twistedKillingForm_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x y = -θ.twistedKillingForm x y := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [twistedKillingForm_apply, hy', neg_neg]

/-- On a second argument in `θ.cartanP`, the Killing form agrees with the twisted Killing
form. -/
theorem killingForm_eq_twistedKillingForm_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.cartanP) :
    killingForm R L x y = θ.twistedKillingForm x y := by
  rw [twistedKillingForm_apply, mem_cartanP.mp hy, map_neg, neg_neg]

/-- The fixed subalgebra and `θ.cartanP` are orthogonal for the twisted Killing form over a base
ring without additive torsion. -/
theorem twistedKillingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [IsAddTorsionFree R]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    θ.twistedKillingForm x y = 0 := by
  rw [twistedKillingForm_apply, mem_cartanP.mp hy, map_neg, neg_neg,
    killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy]

/-- The identity automorphism has trivial `-1`-eigenspace when `2` is invertible. -/
@[simp]
theorem cartanP_refl [Invertible (2 : R)] : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP, refl_apply, Submodule.mem_bot]
  exact ⟨TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R), fun hx ↦ by simp [hx]⟩

end CommRing

/-! ### Cartan involutions over an ordered field -/

variable {K L L' : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing L'] [LieAlgebra K L']

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
theorem symm_eq (hθ : θ.IsCartanInvolution) : θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ.involutive x).symm

/-- The twisted Killing form of a Cartan involution is strictly positive on nonzero vectors. -/
theorem twistedKillingForm_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.twistedKillingForm x x :=
  hθ.posDef_twistedKillingForm x hx

/-- The diagonal of the twisted Killing form of a Cartan involution is nonnegative everywhere. -/
theorem twistedKillingForm_nonneg (hθ : θ.IsCartanInvolution) (x : L) :
    0 ≤ θ.twistedKillingForm x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hθ.twistedKillingForm_pos hx).le

/-- The diagonal of the twisted Killing form of a Cartan involution vanishes only at zero. -/
theorem twistedKillingForm_self_eq_zero_iff (hθ : θ.IsCartanInvolution) {x : L} :
    θ.twistedKillingForm x x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ (hθ.twistedKillingForm_pos hx).ne' h, fun h ↦ by simp [h]⟩

/-- The twisted Killing form of a Cartan involution is symmetric. -/
theorem twistedKillingForm_isSymm (hθ : θ.IsCartanInvolution) : θ.twistedKillingForm.IsSymm :=
  isSymm_twistedKillingForm hθ.involutive

/-- The twisted Killing form of a Cartan involution is nondegenerate. -/
theorem twistedKillingForm_nondegenerate (hθ : θ.IsCartanInvolution) :
    θ.twistedKillingForm.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_of_anisotropic _ hθ.posDef_twistedKillingForm.anisotropic

end IsCartanInvolution

end PartialOrder

section OrderedField

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- An involution is a Cartan involution exactly when `B(x, θ x) < 0` for every `x ≠ 0`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅K⁆ L} :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → killingForm K L x (θ x) < 0 := by
  refine ⟨fun h ↦ ⟨h.involutive, fun x hx ↦ ?_⟩, fun h ↦ ⟨h.left, fun x hx ↦ ?_⟩⟩
  · have := h.posDef_twistedKillingForm x hx
    rwa [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos] at this
  · rw [LinearMap.BilinMap.toQuadraticMap_apply, twistedKillingForm_apply, neg_pos]
    exact h.right x hx

/-- The identity automorphism is a Cartan involution iff the Killing form is strictly negative on
nonzero vectors. -/
theorem isCartanInvolution_refl_iff :
    (LieEquiv.refl : L ≃ₗ⁅K⁆ L).IsCartanInvolution ↔
      ∀ x : L, x ≠ 0 → killingForm K L x x < 0 := by
  simp [isCartanInvolution_iff, Function.Involutive]

/-- Conjugation by a Lie algebra equivalence preserves Cartan involutions. -/
theorem IsCartanInvolution.conj {θ : L ≃ₗ⁅K⁆ L} (hθ : θ.IsCartanInvolution)
    (e : L ≃ₗ⁅K⁆ L') :
    (e.symm.trans (θ.trans e)).IsCartanInvolution := by
  refine isCartanInvolution_iff.mpr ⟨fun y ↦ by simp [hθ.involutive _], fun y hy ↦ ?_⟩
  have h0 : e.symm y ≠ 0 := fun h ↦ hy (by simpa using congrArg e h)
  have hval := twistedKillingForm_conj_apply θ e (e.symm y) (e.symm y)
  simp only [twistedKillingForm_apply, apply_symm_apply, neg_inj] at hval
  rw [hval]
  exact (isCartanInvolution_iff.mp hθ).right (e.symm y) h0

/-- Conjugating an automorphism by a Lie algebra equivalence preserves and reflects being a Cartan
involution. -/
@[simp]
theorem isCartanInvolution_conj_iff {θ : L ≃ₗ⁅K⁆ L} (e : L ≃ₗ⁅K⁆ L') :
    (e.symm.trans (θ.trans e)).IsCartanInvolution ↔ θ.IsCartanInvolution :=
  ⟨fun h ↦ by
    have h' := h.conj e.symm
    have heq : e.symm.symm.trans ((e.symm.trans (θ.trans e)).trans e.symm) = θ :=
      LieEquiv.ext fun x ↦ by simp
    rwa [heq] at h', fun h ↦ h.conj e⟩

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

/-- The Killing form is nonpositive on the fixed subalgebra `𝔨` of a Cartan involution. -/
theorem killingForm_nonpos_of_mem_fixedSubalgebra (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) : killingForm K L x x ≤ 0 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp
  · exact (hθ.killingForm_apply_self_neg_of_mem_fixedSubalgebra hx hx₀).le

/-- The Killing form is positive definite on the `-1`-eigenspace `𝔭` of a Cartan involution. -/
theorem killingForm_apply_self_pos_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) (hx₀ : x ≠ 0) : 0 < killingForm K L x x := by
  have := hθ.killingForm_apply_apply_neg hx₀
  rwa [mem_cartanP.mp hx, map_neg, neg_lt_zero] at this

/-- The Killing form is nonnegative on the `-1`-eigenspace `𝔭` of a Cartan involution. -/
theorem killingForm_nonneg_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) : 0 ≤ killingForm K L x x := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp
  · exact (hθ.killingForm_apply_self_pos_of_mem_cartanP hx hx₀).le

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

/-- The Killing-orthogonal complement of `θ.cartanP` is the fixed subalgebra `𝔨`. -/
theorem orthogonal_cartanP_eq_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    (killingForm K L).orthogonal θ.cartanP = θ.toLieHom.fixedSubalgebra.toSubmodule := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · have hsup := (θ.isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit
      hθ.involutive).sup_eq_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
    have hk' := (LieSubalgebra.mem_toSubmodule _).mp hk
    have hpp : killingForm K L p p = 0 := by
      have := (killingForm K L).mem_orthogonal_iff.mp hx p hp
      rwa [map_add, traceForm_comm K L L p k,
        killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hk' hp, zero_add] at this
    obtain rfl : p = 0 := by
      by_contra hp₀
      exact (hθ.killingForm_apply_self_pos_of_mem_cartanP hp hp₀).ne' hpp
    rwa [add_zero]
  · exact (killingForm K L).mem_orthogonal_iff.mpr fun p hp ↦ by
      rw [traceForm_comm]
      exact killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP
        ((LieSubalgebra.mem_toSubmodule _).mp hx) hp

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

/-- The fixed subalgebra `𝔨` of a Cartan involution is reductive (has central radical). -/
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

/-- A nontrivial abelian Lie algebra admits no Cartan involution. -/
theorem not_isCartanInvolution_of_isLieAbelian [IsLieAbelian L] [Nontrivial L]
    (θ : L ≃ₗ⁅K⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have had : ad K L x = 0 := by
    ext y
    exact trivial_lie_zero L L x y
  have hkill : killingForm K L x (θ x) = 0 := by
    rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero]
  have hpos := hθ.killingForm_apply_apply_neg hx
  rw [hkill] at hpos
  exact lt_irrefl 0 hpos

end OrderedField

/-! ### Real diagonalizability of `ad x` for `x ∈ 𝔭` -/

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

namespace IsCartanInvolution

/-- For a Cartan involution `θ` of a real Lie algebra and `x ∈ θ.cartanP`, the adjoint operator
`ad ℝ L x` is diagonalizable over `ℝ`: its real eigenspaces span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have := hθ.finiteDimensional
  let q : LinearMap.BilinForm ℝ L :=
    θ.twistedKillingForm.compl₁₂ (ad ℝ L x) LinearMap.id
  have hq : q.IsSymm := LinearMap.BilinForm.isSymm_def.mpr fun y z ↦ by
    simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply]
    have hself := ad_mem_selfAdjointSubmodule_twistedKillingForm hx
    rw [LinearMap.mem_selfAdjointSubmodule] at hself
    rw [hself y z, hθ.twistedKillingForm_isSymm.eq]
  have heig (μ : ℝ) :
      θ.twistedKillingForm.relativeEigenspace q μ = Module.End.eigenspace (ad ℝ L x) μ := by
    ext y
    rw [LinearMap.BilinForm.mem_relativeEigenspace_iff, Module.End.mem_eigenspace_iff]
    constructor
    · intro hy
      refine sub_eq_zero.mp (hθ.twistedKillingForm_nondegenerate.left _ fun z ↦ ?_)
      have h1 := hy z
      simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply] at h1
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h1, sub_self]
    · intro hy z
      simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply, hy, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
  have huniv := LinearMap.BilinForm.relativeSpectralSubspace_univ hθ.twistedKillingForm_isSymm
    (fun v hv ↦ hθ.twistedKillingForm_pos hv) hq
  rw [LinearMap.BilinForm.relativeSpectralSubspace_def] at huniv
  simpa only [Set.mem_univ, iSup_pos, heig] using huniv

/-- For a Cartan involution `θ` of a real Lie algebra and `x ∈ θ.cartanP`, `ad ℝ L x` is a
semisimple endomorphism. -/
theorem isSemisimple_ad_of_mem_cartanP {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsCartanInvolution

end Real

/-! ### Reductive Cartan involutions -/

section Reductive

section ReductiveCartanP

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

/-- In a finite-dimensional reductive Lie algebra of characteristic zero, the central and derived
parts of `θ.cartanP` are disjoint for any automorphism `θ`. -/
theorem disjoint_cartanP_inf_center_derivedSeries (θ : L ≃ₗ⁅K⁆ L) :
    Disjoint (θ.cartanP ⊓ (center K L).toSubmodule)
      (θ.cartanP ⊓ (derivedSeries K L 1).toSubmodule) := by
  have hc := LieSubmodule.isCompl_toSubmodule.mpr (TauCeti.isCompl_center_derivedSeries K L)
  exact hc.disjoint.mono inf_le_right inf_le_right

/-- In a finite-dimensional reductive Lie algebra of characteristic zero, `θ.cartanP` splits as
`(θ.cartanP ⊓ Z(L)) ⊔ (θ.cartanP ⊓ ⁅L, L⁆)` for any automorphism `θ`. -/
theorem sup_cartanP_inf_center_derivedSeries (θ : L ≃ₗ⁅K⁆ L) :
    (θ.cartanP ⊓ (center K L).toSubmodule) ⊔
      (θ.cartanP ⊓ (derivedSeries K L 1).toSubmodule) = θ.cartanP := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx ↦ ?_
  obtain ⟨⟨z, d⟩, ⟨hz, hd, hsum⟩, _⟩ :=
    θ.existsUnique_center_add_derivedSeries_of_apply_eq_smul
      (TauCeti.isCompl_center_derivedSeries K L) (c := (-1 : K))
      (by simpa only [neg_one_smul] using mem_cartanP.mp hx)
  rw [← hsum]
  exact Submodule.add_mem_sup
    ⟨mem_cartanP.mpr (by simpa only [neg_one_smul] using hz), z.property⟩
    ⟨mem_cartanP.mpr (by simpa only [neg_one_smul] using hd), d.property⟩

end ReductiveCartanP

section PartialOrder

variable {K L L' : Type*} [Field K] [PartialOrder K]
  [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']

/-- A **reductive Cartan involution** of a Lie algebra `L`: an involutive Lie algebra automorphism
whose restriction to the derived ideal `⁅L, L⁆` is a Cartan involution. -/
structure IsReductiveCartanInvolution (θ : L ≃ₗ⁅K⁆ L) : Prop where
  /-- A reductive Cartan involution is involutive: `θ (θ x) = x`. -/
  involutive : Function.Involutive θ
  /-- The restriction of `θ` to the derived ideal `⁅L, L⁆` is a Cartan involution. -/
  derivedSeries_isCartanInvolution :
    ∃ θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1,
      (∀ x : derivedSeries K L 1, (θD x : L) = θ x) ∧ θD.IsCartanInvolution

/-- Unfolded characterization of `LieEquiv.IsReductiveCartanInvolution`. -/
theorem isReductiveCartanInvolution_iff {θ : L ≃ₗ⁅K⁆ L} :
    θ.IsReductiveCartanInvolution ↔
      Function.Involutive θ ∧
        ∃ θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1,
          (∀ x : derivedSeries K L 1, (θD x : L) = θ x) ∧ θD.IsCartanInvolution :=
  ⟨fun h ↦ ⟨h.involutive, h.derivedSeries_isCartanInvolution⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

end PartialOrder

section OrderedField

variable {K L L' : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']

/-- Conjugation by a Lie algebra equivalence preserves reductive Cartan involutions. -/
theorem IsReductiveCartanInvolution.conj {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) (e : L ≃ₗ⁅K⁆ L') :
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
theorem isReductiveCartanInvolution_conj_iff {θ : L ≃ₗ⁅K⁆ L} (e : L ≃ₗ⁅K⁆ L') :
    (e.symm.trans (θ.trans e)).IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution :=
  ⟨fun h ↦ by
    have h' := h.conj e.symm
    have heq : e.symm.symm.trans ((e.symm.trans (θ.trans e)).trans e.symm) = θ :=
      LieEquiv.ext fun x ↦ by simp
    rwa [heq] at h', fun h ↦ h.conj e⟩

/-- Every involutive automorphism of an abelian Lie algebra is a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_of_isLieAbelian [IsLieAbelian L] {θ : L ≃ₗ⁅K⁆ L}
    (hinv : Function.Involutive θ) :
    θ.IsReductiveCartanInvolution where
  involutive := hinv
  derivedSeries_isCartanInvolution := by
    have hbot : derivedSeries K L 1 = ⊥ := by
      rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
        LieSubmodule.lie_eq_bot_iff]
      intro x _ y _
      exact trivial_lie_zero L L x y
    have hsub : Subsingleton (derivedSeries K L 1) := by
      rw [hbot]
      infer_instance
    refine ⟨LieEquiv.refl, fun x ↦ ?_, isCartanInvolution_iff.mpr
      ⟨fun _ ↦ rfl, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩⟩
    have hx0 : (x : L) = 0 := congrArg Subtype.val (Subsingleton.elim x 0)
    simp [hx0]

/-- Every Cartan involution over an ordered field is a reductive Cartan involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) :
    θ.IsReductiveCartanInvolution where
  involutive := hθ.involutive
  derivedSeries_isCartanInvolution := by
    have := hθ.finiteDimensional
    let θD := θ.restrictDerivedSeries 1
    refine ⟨θD, fun x ↦ θ.coe_restrictDerivedSeries 1 x, isCartanInvolution_iff.mpr
      ⟨fun x ↦ Subtype.ext (by simp [θD, hθ.involutive x]), fun x hx ↦ ?_⟩⟩
    have hval : killingForm K (derivedSeries K L 1) x (θD x) = killingForm K L x (θ x) := by
      rw [LieIdeal.killingForm_eq]
      change killingForm K L x (θD x) = killingForm K L x (θ x)
      rw [θ.coe_restrictDerivedSeries]
    rw [hval]
    exact hθ.killingForm_apply_apply_neg (fun h ↦ hx (Subtype.ext h))

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is Killing. -/
theorem isKilling_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsKilling K (derivedSeries K L 1) := by
  obtain ⟨_, _, hθD⟩ := hθ.derivedSeries_isCartanInvolution
  exact hθD.isKilling

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

/-- On a finite-dimensional reductive Lie algebra over an ordered field, combining a linear
involution `θZ` of the centre with a Cartan involution `θD` of the derived ideal produces a
reductive Cartan involution of `L`. -/
theorem exists_isReductiveCartanInvolution_extend [FiniteDimensional K L]
    [HasCentralRadical K L] (θZ : center K L ≃ₗ[K] center K L)
    (hθZ : Function.Involutive θZ)
    (θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1) (hθD : θD.IsCartanInvolution) :
    ∃ θ : L ≃ₗ⁅K⁆ L, θ.IsReductiveCartanInvolution ∧
      (∀ z : center K L, θ z = θZ z) ∧ ∀ d : derivedSeries K L 1, θ d = θD d := by
  have hc := LieSubmodule.isCompl_toSubmodule.mpr (TauCeti.isCompl_center_derivedSeries K L)
  let e : (center K L × derivedSeries K L 1) ≃ₗ[K] L :=
    Submodule.prodEquivOfIsCompl (center K L).toSubmodule (derivedSeries K L 1).toSubmodule hc
  have he (z : center K L) (d : derivedSeries K L 1) : e (z, d) = (z : L) + d :=
    Submodule.coe_prodEquivOfIsCompl' _ _ _ _
  let f : L ≃ₗ[K] L := (e.symm.trans (θZ.prodCongr θD.toLinearEquiv)).trans e
  have hf_add (z : center K L) (d : derivedSeries K L 1) :
      f ((z : L) + d) = (θZ z : L) + θD d := by
    rw [← he z d]
    simp only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, coe_toLinearEquiv]
    exact he (θZ z) (θD d)
  have hf_z (z : center K L) : f z = θZ z := by simpa using hf_add z 0
  have hf_d (d : derivedSeries K L 1) : f d = θD d := by simpa using hf_add 0 d
  have hlie (x y : L) : f ⁅x, y⁆ = ⁅f x, f y⁆ := by
    obtain ⟨⟨zx, dx⟩, hx⟩ := e.surjective x
    obtain ⟨⟨zy, dy⟩, hy⟩ := e.surjective y
    have hx' : (zx : L) + dx = x := (he zx dx).symm.trans hx
    have hy' : (zy : L) + dy = y := (he zy dy).symm.trans hy
    have hzL (z : center K L) (w : L) : ⁅(z : L), w⁆ = 0 := by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K L L z).mp z.property w, neg_zero]
    have hzR (z : center K L) (w : L) : ⁅w, (z : L)⁆ = 0 :=
      (LieModule.mem_maxTrivSubmodule K L L z).mp z.property w
    rw [← hx', ← hy', hf_add, hf_add]
    simp only [add_lie, lie_add, hzL, hzR, zero_add]
    have hD (u v : derivedSeries K L 1) :
        ((⁅u, v⁆ : derivedSeries K L 1) : L) = ⁅(u : L), (v : L)⁆ :=
      (derivedSeries K L 1).toLieSubalgebra.incl.map_lie u v
    rw [← hD dx dy, hf_d, θD.map_lie, hD]
  let θ : L ≃ₗ⁅K⁆ L := { f with map_lie' := fun {x y} ↦ hlie x y }
  refine ⟨θ, ⟨fun x ↦ ?_, ⟨θD, fun d ↦ (hf_d d).symm, hθD⟩⟩,
    fun z ↦ hf_z z, fun d ↦ hf_d d⟩
  obtain ⟨⟨z, d⟩, hx⟩ := e.surjective x
  have hx' : (z : L) + d = x := (he z d).symm.trans hx
  rw [← hx']
  exact (congrArg f (hf_add z d)).trans
    ((hf_add (θZ z) (θD d)).trans (by rw [hθZ z, hθD.involutive d]))

end OrderedField

end Reductive

end LieEquiv
