/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.Algebra.Lie.InvariantForm.Basic
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Cartan involutions and the Cartan decomposition

A **Cartan involution** of a Lie algebra `L` over an ordered field `K` (most importantly `ℝ`) is an
involutive Lie algebra automorphism `θ : L ≃ₗ⁅K⁆ L` whose twisted Killing form
`B_θ(x, y) = -B(x, θ y)` (`LieEquiv.cartanBilinForm`) is positive definite.

Every involutive automorphism `θ` over a ring in which `2` is a unit decomposes `L` as the direct
sum of its `+1`-eigenspace `𝔨 = θ.toLieHom.fixedSubalgebra` (a Lie subalgebra) and its
`-1`-eigenspace `𝔭 = θ.cartanP` (a submodule), satisfying the grading relations `[𝔨, 𝔨] ⊆ 𝔨`,
`[𝔨, 𝔭] ⊆ 𝔭`, `[𝔭, 𝔭] ⊆ 𝔨`, and Killing-orthogonality `B(𝔨, 𝔭) = 0`. Moreover, `B_θ` is symmetric,
invariant under `θ` and every automorphism commuting with `θ`, and makes `ad x` skew-adjoint for
`x ∈ 𝔨` and self-adjoint for `x ∈ 𝔭`.

When `θ` is a Cartan involution over an ordered field `K`, positivity of `B_θ` forces the Killing
form `B` to be nondegenerate, so `L` is automatically Killing, finite-dimensional, and semisimple.
The Killing form is negative definite on `𝔨` and positive definite on `𝔭`, making `𝔨` a compact
reductive Lie algebra (the direct sum of its centre and its semisimple derived ideal, whose own
Killing form is negative definite). The subspace `𝔭` is the Killing orthogonal complement of `𝔨`,
so a Cartan involution is uniquely determined by its fixed subalgebra `𝔨`, and any two commuting
Cartan involutions are equal. Over `ℝ`, the `B_θ`-symmetry of `ad x` for `x ∈ 𝔭` makes `ad x`
diagonalizable over `ℝ`.

## Main definitions

* `LieEquiv.cartanP`: the `-1`-eigenspace `ker (θ + 1)` of a Lie algebra automorphism `θ`.
* `LieEquiv.cartanBilinForm`: the twisted Killing form `B_θ(x, y) = -B(x, θ y)`.
* `LieEquiv.IsCartanInvolution`: predicate that `θ` is involutive and `B_θ` is positive definite.

## Main results

* `LieEquiv.isCompl_fixedSubalgebra_cartanP`: the Cartan decomposition `L = 𝔨 ⊕ 𝔭`.
* `LieEquiv.lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP` and
  `LieEquiv.lie_mem_fixedSubalgebra_of_mem_cartanP`: the bracket relations `[𝔨, 𝔭] ⊆ 𝔭` and
  `[𝔭, 𝔭] ⊆ 𝔨`.
* `LieEquiv.killingForm_apply_of_mem_fixedSubalgebra_of_mem_cartanP`: `B(𝔨, 𝔭) = 0`.
* `LieEquiv.cartanBilinForm_isSymm`, `LieEquiv.cartanBilinForm_map_map`,
  `LieEquiv.ad_mem_skewAdjointSubmodule_cartanBilinForm`,
  `LieEquiv.cartanBilinForm_ad_of_mem_cartanP`: symmetry, invariance, and adjointness of `B_θ`.
* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.finite`,
  `LieEquiv.IsCartanInvolution.isSemisimple`: a Lie algebra admitting a Cartan involution is
  Killing, finite-dimensional, and semisimple.
* `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_self_neg`: compactness and
  reductivity of the fixed subalgebra `𝔨`.
* `LieEquiv.IsCartanInvolution.orthogonal_fixedSubalgebra_eq_cartanP`,
  `LieEquiv.IsCartanInvolution.eq_of_fixedSubalgebra_eq`,
  `LieEquiv.IsCartanInvolution.eq_of_commute`,
  `LieEquiv.not_isCartanInvolution_of_isLieAbelian`: `𝔭 = 𝔨^{⊥_B}`, uniqueness of `θ` from `𝔨`,
  equality of commuting Cartan involutions, and nonexistence on nontrivial abelian Lie algebras.
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: over `ℝ`, `ad x` is diagonalizable for
  every `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Graduate Studies in
  Mathematics 34, AMS, 2001, Chapter III, §7.
-/

public section

open LieAlgebra

namespace LieEquiv

/-! ### Involutive automorphisms, eigenspaces, and the twisted Killing form -/

section CommRing

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- The `-1`-eigenspace `𝔭 = ker (θ + 1)` of a Lie algebra automorphism `θ`. -/
def cartanP (θ : L ≃ₗ⁅R⁆ L) : Submodule R L :=
  LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id)

/-- Membership in `θ.cartanP` is the negation equation `θ x = -x`. -/
@[simp, grind =]
theorem mem_cartanP_iff {θ : L ≃ₗ⁅R⁆ L} {x : L} : x ∈ θ.cartanP ↔ θ x = -x := by
  simp [cartanP, add_eq_zero_iff_eq_neg]

/-- `θ.cartanP` is the `-1`-eigenspace of the underlying linear endomorphism of `θ`. -/
theorem cartanP_eq_eigenspace (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanP = Module.End.eigenspace (θ : L →ₗ[R] L) (-1) := by
  ext x
  simp

/-- When `2` is a unit, the identity automorphism has trivial `-1`-eigenspace. -/
@[simp]
theorem cartanP_refl (h2 : IsUnit (2 : R)) :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP_iff, refl_apply, Submodule.mem_bot]
  refine ⟨fun hx ↦ h2.smul_eq_zero.mp ?_, fun hx ↦ by simp [hx]⟩
  rw [two_smul]
  calc
    x + x = x + -x := by rw [← hx]
    _ = 0 := add_neg_cancel x

/-- An intertwining Lie equivalence maps `θ.cartanP` onto `θ'.cartanP`. -/
theorem map_cartanP (e : L ≃ₗ⁅R⁆ M) {θ : L ≃ₗ⁅R⁆ L} {θ' : M ≃ₗ⁅R⁆ M}
    (h : ∀ x, θ' (e x) = e (θ x)) :
    θ.cartanP.map (e : L →ₗ[R] M) = θ'.cartanP := by
  ext y
  simp only [Submodule.mem_map, mem_cartanP_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [coe_toLinearEquiv, LinearEquiv.coe_coe, h, hx, map_neg]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    simp only [coe_toLieHom]
    rw [← h, e.apply_symm_apply, hy, map_neg, e.apply_symm_apply]

/-- The bracket relation `[𝔨, 𝔭] ⊆ 𝔭`: bracketing a fixed vector with a `-1`-eigenvector stays in
`θ.cartanP`. -/
theorem lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  rw [mem_cartanP_iff, map_lie, hx', mem_cartanP_iff.mp hy, lie_neg]

/-- The bracket relation `[𝔭, 𝔭] ⊆ 𝔨`: the bracket of two `-1`-eigenvectors is fixed by `θ`. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_lie, mem_cartanP_iff.mp hx,
    mem_cartanP_iff.mp hy, neg_lie, lie_neg, neg_neg]

/-- **Cartan decomposition `L = 𝔨 ⊕ 𝔭`**: for an involutive Lie automorphism `θ` over a ring in
which `2` is a unit, the fixed subalgebra `𝔨` and the `-1`-eigenspace `𝔭` are complementary
submodules. -/
theorem isCompl_fixedSubalgebra_cartanP {θ : L ≃ₗ⁅R⁆ L} (h2 : IsUnit (2 : R))
    (hθ : Function.Involutive θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  have hlin : θ.toLieHom.toLinearMap = (θ : L →ₗ[R] L) := LinearMap.ext fun x ↦ by simp
  rw [LieHom.fixedSubalgebra_toSubmodule_eq_eigenspace, hlin, cartanP_eq_eigenspace]
  exact TauCeti.isCompl_eigenspace_one_neg_one h2 hθ

/-- The eigenspaces `𝔨` and `𝔭` are orthogonal for the Killing form whenever `2` is a unit. -/
theorem killingForm_apply_of_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L}
    (h2 : IsUnit (2 : R)) {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  have hneg : killingForm R L x y = -killingForm R L x y := by
    calc
      killingForm R L x y = killingForm R L (θ x) (θ y) :=
        (killingForm_of_equiv_apply θ x y).symm
      _ = killingForm R L x (-y) := by rw [hx', mem_cartanP_iff.mp hy]
      _ = -killingForm R L x y := map_neg (killingForm R L x) y
  refine h2.mul_right_eq_zero.mp ?_
  rw [two_mul]
  calc
    killingForm R L x y + killingForm R L x y =
        killingForm R L x y + -killingForm R L x y := by rw [← hneg]
    _ = 0 := add_neg_cancel _

/-- The twisted Killing form `B_θ(x, y) = -B(x, θ y)` attached to a Lie algebra automorphism `θ`. -/
noncomputable def cartanBilinForm (θ : L ≃ₗ⁅R⁆ L) : LinearMap.BilinForm R L :=
  -((killingForm R L).compl₁₂ LinearMap.id (θ : L →ₗ[R] L))

/-- Evaluation of the twisted Killing form: `B_θ(x, y) = -B(x, θ y)`. -/
@[simp, grind =]
theorem cartanBilinForm_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanBilinForm x y = -killingForm R L x (θ y) :=
  (rfl)

/-- On the second argument in `𝔨`, the twisted Killing form is `-B`. -/
theorem cartanBilinForm_apply_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    θ.cartanBilinForm x y = -killingForm R L x y := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [cartanBilinForm_apply, hy']

/-- On the second argument in `𝔭`, the twisted Killing form coincides with `B`. -/
theorem cartanBilinForm_apply_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.cartanP) :
    θ.cartanBilinForm x y = killingForm R L x y := by
  rw [cartanBilinForm_apply, mem_cartanP_iff.mp hy, map_neg, neg_neg]

/-- For an involutive automorphism `θ`, the twisted Killing form `B_θ` is symmetric. -/
theorem cartanBilinForm_isSymm {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    θ.cartanBilinForm.IsSymm := by
  refine LinearMap.BilinForm.isSymm_iff.mpr ⟨fun x y ↦ ?_⟩
  simp only [cartanBilinForm_apply, RingHom.id_apply]
  rw [← killingForm_of_equiv_apply θ x (θ y), hθ y]
  exact congrArg Neg.neg (LieModule.traceForm_comm R L L (θ x) y)

/-- Any Lie automorphism commuting with `θ` preserves the twisted Killing form `B_θ`. -/
theorem cartanBilinForm_map_map {θ φ : L ≃ₗ⁅R⁆ L} (hφ : ∀ x, φ (θ x) = θ (φ x)) (x y : L) :
    θ.cartanBilinForm (φ x) (φ y) = θ.cartanBilinForm x y := by
  simp only [cartanBilinForm_apply, ← hφ, killingForm_of_equiv_apply]

/-- The automorphism `θ` is `B_θ`-orthogonal. -/
theorem cartanBilinForm_apply_self_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanBilinForm (θ x) (θ y) = θ.cartanBilinForm x y :=
  cartanBilinForm_map_map (fun _ ↦ rfl) x y

/-- The `B_θ`-adjoint of `ad x` is `-ad (θ x)` for an involutive automorphism `θ`:
`B_θ(ad x y, z) = -B_θ(y, ad (θ x) z)`. -/
theorem cartanBilinForm_ad_left {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) (x y z : L) :
    θ.cartanBilinForm (ad R L x y) z = -θ.cartanBilinForm y (ad R L (θ x) z) := by
  simp only [cartanBilinForm_apply, ad_apply, neg_neg]
  calc
    -killingForm R L ⁅x, y⁆ (θ z) = killingForm R L y ⁅x, θ z⁆ := by
      rw [LieModule.traceForm_lieInvariant R L L x y (θ z), neg_neg]
    _ = killingForm R L y (θ ⁅θ x, z⁆) := by
      rw [map_lie, hθ x]

/-- For `x ∈ 𝔨`, `ad x` is skew-adjoint with respect to `B_θ`. -/
theorem ad_mem_skewAdjointSubmodule_cartanBilinForm {θ : L ≃ₗ⁅R⁆ L}
    (hθ : Function.Involutive θ) {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    ad R L x ∈ θ.cartanBilinForm.skewAdjointSubmodule := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro y z
  rw [Pi.neg_apply, map_neg, cartanBilinForm_ad_left hθ, hx']

/-- For `x ∈ 𝔭`, `ad x` is self-adjoint with respect to `B_θ`:
`B_θ(ad x y, z) = B_θ(y, ad x z)`. -/
theorem cartanBilinForm_ad_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ)
    {x : L} (hx : x ∈ θ.cartanP) (y z : L) :
    θ.cartanBilinForm (ad R L x y) z = θ.cartanBilinForm y (ad R L x z) := by
  rw [cartanBilinForm_ad_left hθ, mem_cartanP_iff.mp hx, map_neg, LinearMap.neg_apply,
    map_neg, neg_neg]

end CommRing

/-! ### Cartan involutions -/

section PartialOrder

variable {R L M : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- A **Cartan involution** of a Lie algebra `L` over an ordered ring `R`: an involutive Lie
algebra automorphism `θ` whose twisted Killing form `B_θ(x, y) = -B(x, θ y)` is positive definite.
Over an ordered field, admitting a Cartan involution automatically forces `L` to be
finite-dimensional and semisimple. -/
def IsCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop :=
  Function.Involutive θ ∧ θ.cartanBilinForm.toQuadraticMap.PosDef

/-- Characterization of a Cartan involution in terms of `θ (θ x) = x` and
`0 < -B(x, θ x)` for nonzero `x`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → 0 < -killingForm R L x (θ x) := by
  simp [IsCartanInvolution, LinearMap.BilinForm.posDef_toQuadraticMap_iff]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅R⁆ L}

/-- A Cartan involution is involutive. -/
theorem involutive (hθ : θ.IsCartanInvolution) : Function.Involutive θ :=
  hθ.1

/-- A Cartan involution is its own inverse. -/
theorem symm_eq_self (hθ : θ.IsCartanInvolution) : θ.symm = θ := by
  ext x
  rw [symm_apply_eq, hθ.involutive x]

/-- The twisted Killing form `B_θ` of a Cartan involution is positive definite. -/
theorem posDef_cartanBilinForm (hθ : θ.IsCartanInvolution) :
    θ.cartanBilinForm.toQuadraticMap.PosDef :=
  hθ.2

/-- The twisted Killing form `B_θ` of a Cartan involution is symmetric. -/
theorem isSymm_cartanBilinForm (hθ : θ.IsCartanInvolution) :
    θ.cartanBilinForm.IsSymm :=
  cartanBilinForm_isSymm hθ.involutive

/-- Positivity of `B_θ(x, x) = -B(x, θ x)` on nonzero vectors. -/
theorem cartanBilinForm_self_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.cartanBilinForm x x :=
  hθ.posDef_cartanBilinForm x hx

/-- The Killing form is positive definite on `θ.cartanP`. -/
theorem killingForm_self_pos_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) (hx0 : x ≠ 0) :
    0 < killingForm R L x x := by
  rw [← cartanBilinForm_apply_of_mem_cartanP hx]
  exact hθ.cartanBilinForm_self_pos hx0

/-- Conjugating a Cartan involution by a Lie algebra equivalence yields a Cartan involution. -/
theorem conj (hθ : θ.IsCartanInvolution) (e : L ≃ₗ⁅R⁆ M) :
    (e.symm.trans (θ.trans e)).IsCartanInvolution := by
  rw [isCartanInvolution_iff]
  refine ⟨fun y ↦ by simp [hθ.involutive (e.symm y)], fun y hy ↦ ?_⟩
  have he : e.symm y ≠ 0 := fun h ↦ hy (by simpa using congrArg e h)
  have hB : killingForm R M y (e (θ (e.symm y))) = killingForm R L (e.symm y) (θ (e.symm y)) := by
    rw [← killingForm_of_equiv_apply e (e.symm y) (θ (e.symm y)), e.apply_symm_apply]
  simpa only [trans_apply, hB, ← cartanBilinForm_apply] using hθ.cartanBilinForm_self_pos he

/-- The Killing form of a Lie algebra admitting a Cartan involution is nondegenerate. -/
theorem killingForm_nondegenerate (hθ : θ.IsCartanInvolution) :
    (killingForm R L).Nondegenerate := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · by_contra hx0
    have hpos := hθ.cartanBilinForm_self_pos hx0
    rw [cartanBilinForm_apply, hx (θ x), neg_zero] at hpos
    exact lt_irrefl 0 hpos
  · by_contra hx0
    have hpos := hθ.cartanBilinForm_self_pos hx0
    rw [cartanBilinForm_apply, LieModule.traceForm_comm R L L x (θ x), hx (θ x), neg_zero] at hpos
    exact lt_irrefl 0 hpos

/-- A Lie algebra admitting a Cartan involution has nondegenerate Killing form (`IsKilling`). -/
theorem isKilling (hθ : θ.IsCartanInvolution) : IsKilling R L :=
  TauCeti.isKilling_of_killingForm_nondegenerate R L hθ.killingForm_nondegenerate

/-- A Lie algebra admitting a Cartan involution is automatically finite over the base ring. -/
theorem finite (hθ : θ.IsCartanInvolution) : Module.Finite R L := by
  have := hθ.isKilling
  exact TauCeti.finite_of_isKilling

/-- A Lie algebra admitting a Cartan involution has trivial centre. -/
theorem center_eq_bot (hθ : θ.IsCartanInvolution) : center R L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  have had : ad R L x = 0 := LinearMap.ext fun z ↦ by
    rw [ad_apply, ← lie_skew, (LieModule.mem_maxTrivSubmodule R L L x).mp hx z, neg_zero,
      LinearMap.zero_apply]
  refine hθ.killingForm_nondegenerate.1 x fun y ↦ ?_
  rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero]

end IsCartanInvolution

/-- A nontrivial abelian Lie algebra admits no Cartan involution, because a Lie algebra admitting
a Cartan involution has trivial centre. -/
theorem not_isCartanInvolution_of_isLieAbelian [Nontrivial L] [IsLieAbelian L] (θ : L ≃ₗ⁅R⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hx0 : x ∈ center R L :=
    (LieModule.mem_maxTrivSubmodule R L L x).mpr fun y ↦ trivial_lie_zero L L y x
  rw [hθ.center_eq_bot] at hx0
  exact hx ((LieSubmodule.mem_bot x).mp hx0)

end PartialOrder

section OrderedAddMonoid

variable {R L : Type*} [CommRing R] [PartialOrder R] [IsOrderedAddMonoid R]
  [LieRing L] [LieAlgebra R L]

/-- The Killing form is negative definite on the fixed subalgebra `𝔨` of a Cartan involution. -/
theorem IsCartanInvolution.killingForm_self_neg_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsCartanInvolution) {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx0 : x ≠ 0) :
    killingForm R L x x < 0 := by
  have h := hθ.cartanBilinForm_self_pos hx0
  rw [cartanBilinForm_apply_of_mem_fixedSubalgebra hx] at h
  exact neg_pos.mp h

/-- The identity automorphism is a Cartan involution if and only if the Killing form is negative
definite (the compact case). -/
theorem isCartanInvolution_refl_iff :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).IsCartanInvolution ↔
      ∀ x : L, x ≠ 0 → killingForm R L x x < 0 := by
  simp [isCartanInvolution_iff, Function.Involutive]

/-- **Two commuting Cartan involutions are equal.** -/
theorem IsCartanInvolution.eq_of_commute {θ θ' : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution) (hcomm : ∀ x, θ (θ' x) = θ' (θ x)) : θ = θ' := by
  ext x
  have hu : (x + θ x) - θ' (x + θ x) = 0 := by
    by_contra hne
    have hK : (x + θ x) - θ' (x + θ x) ∈ θ.toLieHom.fixedSubalgebra := by
      rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_sub, map_add, hθ.involutive,
        hcomm, map_add, hθ.involutive, add_comm (θ x) x]
    have hP' : (x + θ x) - θ' (x + θ x) ∈ θ'.cartanP := by
      rw [mem_cartanP_iff, map_sub, hθ'.involutive, neg_sub]
    exact (hθ.killingForm_self_neg_of_mem_fixedSubalgebra hK hne).not_gt
      (hθ'.killingForm_self_pos_of_mem_cartanP hP' hne)
  have hw : (x - θ x) + θ' (x - θ x) = 0 := by
    by_contra hne
    have hP : (x - θ x) + θ' (x - θ x) ∈ θ.cartanP := by
      rw [mem_cartanP_iff, map_add, map_sub, hθ.involutive, hcomm, map_sub, hθ.involutive,
        ← neg_sub x (θ x), map_neg]
      abel
    have hK' : (x - θ x) + θ' (x - θ x) ∈ θ'.toLieHom.fixedSubalgebra := by
      rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_add, hθ'.involutive, add_comm]
    exact (hθ'.killingForm_self_neg_of_mem_fixedSubalgebra hK' hne).not_gt
      (hθ.killingForm_self_pos_of_mem_cartanP hP hne)
  have h2 : (θ x - θ' x) + (θ x - θ' x) = 0 := by
    calc
      (θ x - θ' x) + (θ x - θ' x) =
          ((x + θ x) - θ' (x + θ x)) - ((x - θ x) + θ' (x - θ x)) := by
            simp only [map_add, map_sub]; abel
      _ = 0 := by rw [hu, hw, sub_self]
  refine sub_eq_zero.mp ?_
  by_contra hne
  have hpos := hθ.cartanBilinForm_self_pos hne
  have hsum : 0 < θ.cartanBilinForm (θ x - θ' x) (θ x - θ' x) +
      θ.cartanBilinForm (θ x - θ' x) (θ x - θ' x) :=
    lt_of_lt_of_le hpos (le_add_of_nonneg_right hpos.le)
  rw [← map_add, h2, map_zero] at hsum
  exact lt_irrefl 0 hsum

/-- On a compact Lie algebra (negative definite Killing form), the identity is the unique Cartan
involution. -/
theorem IsCartanInvolution.eq_refl_of_killingForm_self_neg {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsCartanInvolution) (hneg : ∀ x : L, x ≠ 0 → killingForm R L x x < 0) :
    θ = LieEquiv.refl :=
  hθ.eq_of_commute (isCartanInvolution_refl_iff.mpr hneg) (fun _ ↦ rfl)

end OrderedAddMonoid

/-! ### Semisimplicity, compactness of `𝔨`, and uniqueness over a field -/

section FieldPartialOrder

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

namespace IsCartanInvolution

variable {θ θ' : L ≃ₗ⁅K⁆ L}

/-- A Lie algebra admitting a Cartan involution over a partially ordered field is semisimple. -/
theorem isSemisimple (hθ : θ.IsCartanInvolution) : IsSemisimple K L := by
  have := hθ.isKilling
  have := hθ.finite
  infer_instance

/-- A Lie algebra admitting a Cartan involution over a partially ordered field is perfect:
`⁅L, L⁆ = L`. -/
theorem derivedSeries_one_eq_top (hθ : θ.IsCartanInvolution) : derivedSeries K L 1 = ⊤ := by
  have := hθ.isKilling
  have := hθ.finite
  exact TauCeti.derivedSeries_one_eq_top_of_isKilling K L

private theorem killingForm_restrict_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    let Φ : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
      (killingForm K L).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap
    Φ.IsSymm ∧ Φ.toQuadraticMap.Anisotropic ∧ Φ.lieInvariant θ.toLieHom.fixedSubalgebra := by
  refine ⟨?_, ?_, ?_⟩
  · exact (LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L L)).compl₁₂ _
  · intro x hx
    by_contra hx0
    have hval : (x : L) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    have hpos := hθ.cartanBilinForm_self_pos hval
    have hB : killingForm K L x x = 0 := by
      simpa only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₁₂_apply,
        LieHom.coe_toLinearMap, LieSubalgebra.coe_incl] using hx
    rw [cartanBilinForm_apply_of_mem_fixedSubalgebra x.property, hB, neg_zero] at hpos
    exact lt_irrefl 0 hpos
  · have hinv : (killingForm K L).lieInvariant L := fun x y z ↦
      LieModule.traceForm_lieInvariant K L L x y z
    exact hinv.compl₁₂ θ.toLieHom.fixedSubalgebra.incl

/-- The fixed subalgebra `𝔨` of a Cartan involution is the direct sum of its centre and its
derived ideal. -/
theorem isCompl_center_derivedSeries_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    IsCompl (center K θ.toLieHom.fixedSubalgebra)
      (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have := hθ.finite
  obtain ⟨hsymm, hani, hinv⟩ := hθ.killingForm_restrict_fixedSubalgebra
  exact LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic
    _ hsymm.isRefl hani hinv

/-- The derived ideal of the fixed subalgebra `𝔨` of a Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    IsSemisimple K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have := hθ.finite
  obtain ⟨hsymm, hani, hinv⟩ := hθ.killingForm_restrict_fixedSubalgebra
  exact LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic
    _ hsymm.isRefl hani hinv

/-- The fixed subalgebra `𝔨` of a Cartan involution is reductive (its radical equals its
centre). -/
theorem hasCentralRadical_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    HasCentralRadical K θ.toLieHom.fixedSubalgebra := by
  have := hθ.finite
  obtain ⟨hsymm, hani, hinv⟩ := hθ.killingForm_restrict_fixedSubalgebra
  exact LinearMap.BilinForm.hasCentralRadical_of_anisotropic
    _ hsymm.isRefl hani hinv

/-- For a Cartan involution `θ`, the `-1`-eigenspace `𝔭` is the Killing orthogonal complement of
the fixed subalgebra `𝔨`. -/
theorem orthogonal_fixedSubalgebra_eq_cartanP [NeZero (2 : K)] (hθ : θ.IsCartanInvolution) :
    (killingForm K L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule = θ.cartanP := by
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (NeZero.ne 2)
  ext x
  constructor
  · intro hx
    have hsplit : x ∈ θ.toLieHom.fixedSubalgebra.toSubmodule ⊔ θ.cartanP := by
      rw [(isCompl_fixedSubalgebra_cartanP h2 hθ.involutive).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp hsplit
    have hk0 : k = 0 := by
      by_contra hk0
      have hkx : killingForm K L k (k + p) = 0 := hx k hk
      rw [map_add, killingForm_apply_of_mem_fixedSubalgebra_of_mem_cartanP h2 hk hp, add_zero]
        at hkx
      have hpos := hθ.cartanBilinForm_self_pos hk0
      rw [cartanBilinForm_apply_of_mem_fixedSubalgebra hk, hkx, neg_zero] at hpos
      exact lt_irrefl 0 hpos
    simpa [hk0] using hp
  · intro hx k hk
    exact killingForm_apply_of_mem_fixedSubalgebra_of_mem_cartanP h2 hk hx

/-- **Uniqueness from `𝔨`**: a Cartan involution is uniquely determined by its fixed subalgebra
`𝔨`. -/
theorem eq_of_fixedSubalgebra_eq [NeZero (2 : K)] (hθ : θ.IsCartanInvolution)
    (hθ' : θ'.IsCartanInvolution)
    (h : θ.toLieHom.fixedSubalgebra = θ'.toLieHom.fixedSubalgebra) : θ = θ' := by
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (NeZero.ne 2)
  have hP : θ.cartanP = θ'.cartanP := by
    rw [← hθ.orthogonal_fixedSubalgebra_eq_cartanP,
      ← hθ'.orthogonal_fixedSubalgebra_eq_cartanP, h]
  ext x
  have hsplit : x ∈ θ.toLieHom.fixedSubalgebra.toSubmodule ⊔ θ.cartanP := by
    rw [(isCompl_fixedSubalgebra_cartanP h2 hθ.involutive).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp hsplit
  have hk1 : θ k = k := LieHom.mem_fixedSubalgebra.mp hk
  have hk2 : θ' k = k := LieHom.mem_fixedSubalgebra.mp (h ▸ hk)
  have hp' : p ∈ θ'.cartanP := hP ▸ hp
  rw [map_add, map_add, hk1, hk2, mem_cartanP_iff.mp hp, mem_cartanP_iff.mp hp']

end IsCartanInvolution

end FieldPartialOrder

section OrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

private theorem neg_killingForm_restrict_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    let Φ : LinearMap.BilinForm K θ.toLieHom.fixedSubalgebra :=
      (-killingForm K L).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap
    Φ.IsSymm ∧ Φ.toQuadraticMap.PosDef ∧ Φ.lieInvariant θ.toLieHom.fixedSubalgebra := by
  refine ⟨?_, ?_, ?_⟩
  · exact (LinearMap.BilinForm.isSymm_iff.mpr
      (LieModule.traceForm_isSymm K L L)).neg.compl₁₂ _
  · rw [LinearMap.BilinForm.posDef_toQuadraticMap_iff]
    intro x hx
    have hx0 : (x : L) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    simpa only [LinearMap.compl₁₂_apply, LinearMap.neg_apply, LieHom.coe_toLinearMap,
      LieSubalgebra.coe_incl, neg_pos] using
      hθ.killingForm_self_neg_of_mem_fixedSubalgebra x.property hx0
  · have hinv : (-killingForm K L).lieInvariant L := fun x y z ↦ by
      simp [LieModule.traceForm_lieInvariant K L L x y z]
    exact hinv.compl₁₂ θ.toLieHom.fixedSubalgebra.incl

/-- The Killing form of the derived ideal `⁅𝔨, 𝔨⁆` of the fixed subalgebra of a Cartan involution
is negative definite. -/
theorem killingForm_derivedSeries_fixedSubalgebra_self_neg (hθ : θ.IsCartanInvolution)
    {x : derivedSeries K θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) x x < 0 := by
  have := hθ.finite
  obtain ⟨hsymm, hpos, hinv⟩ := hθ.neg_killingForm_restrict_fixedSubalgebra
  exact LinearMap.BilinForm.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero
    _ hsymm hpos hinv x hx

end IsCartanInvolution

end OrderedField

/-! ### Real diagonalizability of `ad x` on `𝔭` -/

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- **Real diagonalizability of `ad x` for `x ∈ 𝔭`**: for a Cartan involution `θ` of a real Lie
algebra and `x ∈ θ.cartanP`, the eigenspaces of `ad x` span `L`. -/
theorem IsCartanInvolution.iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L}
    (hθ : θ.IsCartanInvolution) {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have := hθ.finite
  let q : LinearMap.BilinForm ℝ L := θ.cartanBilinForm.compl₁₂ (ad ℝ L x) LinearMap.id
  have hq : q.IsSymm := by
    refine LinearMap.BilinForm.isSymm_iff.mpr ⟨fun y z ↦ ?_⟩
    simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply, RingHom.id_apply]
    rw [cartanBilinForm_ad_of_mem_cartanP hθ.involutive hx, hθ.isSymm_cartanBilinForm.eq]
  have hpos : ∀ v : L, v ≠ 0 → 0 < θ.cartanBilinForm v v := fun v hv ↦
    hθ.cartanBilinForm_self_pos hv
  have heig (μ : ℝ) :
      θ.cartanBilinForm.relativeEigenspace q μ = Module.End.eigenspace (ad ℝ L x) μ := by
    ext v
    rw [LinearMap.BilinForm.mem_relativeEigenspace_iff, Module.End.mem_eigenspace_iff]
    constructor
    · intro hv
      by_contra hne
      have h0 : θ.cartanBilinForm (ad ℝ L x v - μ • v) (ad ℝ L x v - μ • v) = 0 := by
        rw [map_sub θ.cartanBilinForm, map_smul θ.cartanBilinForm, LinearMap.sub_apply,
          LinearMap.smul_apply, smul_eq_mul]
        exact sub_eq_zero.mpr (hv (ad ℝ L x v - μ • v))
      exact (hpos _ (sub_ne_zero.mpr hne)).ne' h0
    · intro hv w
      simp [q, hv]
  have huniv := LinearMap.BilinForm.relativeSpectralSubspace_univ hθ.isSymm_cartanBilinForm hpos hq
  rw [LinearMap.BilinForm.relativeSpectralSubspace_def] at huniv
  simpa only [Set.mem_univ, iSup_pos, heig] using huniv

end Real

end LieEquiv
