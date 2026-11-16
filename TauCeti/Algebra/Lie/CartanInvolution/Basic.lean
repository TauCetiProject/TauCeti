/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Algebra.Lie.InvariantForm.Positive
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# Cartan involutions and the Cartan decomposition

A **Cartan involution** of a real Lie algebra `L` is an involutive Lie algebra automorphism
`θ : L ≃ₗ⁅ℝ⁆ L` for which the symmetric bilinear form
`B_θ(x, y) = -κ(x, θ y)` is positive definite, where `κ = killingForm ℝ L` is the Killing form.
Positivity of `B_θ` forces `κ` to be nondegenerate, hence forces `L` to be finite-dimensional and
semisimple.

The `+1`-eigenspace `𝔨 = θ.toLieHom.fixedSubalgebra` is a Lie subalgebra and the `-1`-eigenspace
`𝔭 = TauCeti.cartanP θ` is a complementary subspace, giving the **Cartan decomposition**
`L = 𝔨 ⊕ 𝔭` with bracket relations `[𝔨, 𝔨] ⊆ 𝔨`, `[𝔨, 𝔭] ⊆ 𝔭`, `[𝔭, 𝔭] ⊆ 𝔨`, and Killing
orthogonality `κ(𝔨, 𝔭) = 0`. For a Cartan involution:

* `κ` is negative definite on `𝔨` and positive definite on `𝔭`, so `𝔭 = 𝔨^{⊥_κ}` and `θ` is
  uniquely determined by `𝔨`;
* `B_θ` defines an inner product on `L` (`TauCeti.IsCartanInvolution.innerProductCore`), `θ` and
  every automorphism commuting with `θ` preserve `B_θ`, and `ad x` is `B_θ`-skew-adjoint for
  `x ∈ 𝔨` and `B_θ`-self-adjoint (hence diagonalizable over `ℝ`) for `x ∈ 𝔭`;
* restricting `B_θ` to `𝔨` exhibits `-κ|_𝔨` as a positive-definite symmetric `ad(𝔨)`-invariant
  form, so `𝔨` is reductive (`𝔨 = Z(𝔨) ⊕ [𝔨, 𝔨]`) with semisimple derived ideal of
  negative-definite Killing form;
* `L` is compact (`κ(x, x) < 0` for `x ≠ 0`) if and only if the identity is a Cartan involution,
  equivalently `cartanP θ = ⊥`.

## Main definitions

* `TauCeti.cartanP`: the `-1`-eigenspace `ker (θ + id)` of a Lie algebra automorphism `θ`.
* `TauCeti.cartanBilinForm`: the twisted Killing form `B_θ(x, y) = -κ(x, θ y)`.
* `TauCeti.cartanBilinFormFixed`: the restriction of `B_θ` to the fixed subalgebra `𝔨`.
* `TauCeti.IsCartanInvolution`: predicate for a Cartan involution of a real Lie algebra.
* `TauCeti.IsCartanInvolution.innerProductCore`: `B_θ` packaged as an `InnerProductSpace.Core`.

## Main results

* `TauCeti.isCompl_fixedSubalgebra_cartanP`: the Cartan decomposition `L = 𝔨 ⊕ 𝔭`.
* `TauCeti.IsCartanInvolution.isKilling`, `TauCeti.IsCartanInvolution.finiteDimensional`,
  `TauCeti.IsCartanInvolution.isSemisimple`: a real Lie algebra with a Cartan involution is
  finite-dimensional, Killing, and semisimple.
* `TauCeti.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: for `x ∈ cartanP θ`, `ad x` is
  diagonalizable over `ℝ`.
* `TauCeti.IsCartanInvolution.cartanP_eq_orthogonal_fixedSubalgebra` and
  `TauCeti.IsCartanInvolution.eq_of_fixedSubalgebra_eq`: `𝔭` is the Killing orthogonal complement
  of `𝔨`, so `θ` is uniquely determined by `𝔨`.
* `TauCeti.IsCartanInvolution.isCompl_center_derivedSeries_one_fixedSubalgebra` and
  `TauCeti.IsCartanInvolution.killingForm_derivedSeries_one_fixedSubalgebra_neg`: structure of the
  compact subalgebra `𝔨`.
* `TauCeti.isCartanInvolution_refl_iff` and
  `TauCeti.IsCartanInvolution.eq_refl_iff_cartanP_eq_bot`: compactness criterion.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, §7.
-/

public section

open LieAlgebra

namespace TauCeti

/-! ### Involutive automorphisms, eigenspace decomposition and the twisted Killing form -/

section Involutive

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- The `-1`-eigenspace `𝔭 = ker (θ + id)` of a Lie algebra automorphism `θ`. -/
def cartanP (θ : L ≃ₗ⁅R⁆ L) : Submodule R L :=
  LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id)

/-- Membership in `cartanP θ` is the `-1`-eigenvector equation `θ x = -x`. -/
@[simp]
theorem mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x : L} : x ∈ cartanP θ ↔ θ x = -x := by
  simp only [cartanP, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, add_eq_zero_iff_eq_neg]

/-- `cartanP θ` is the `(-1)`-eigenspace of `θ` as an endomorphism of `L`. -/
theorem cartanP_eq_eigenspace (θ : L ≃ₗ⁅R⁆ L) :
    cartanP θ = Module.End.eigenspace (θ : L →ₗ[R] L) (-1) := by
  ext x
  simp

/-- The `-1`-eigenspace of the identity automorphism is trivial when `2` is invertible. -/
@[simp]
theorem cartanP_refl [Invertible (2 : R)] :
    cartanP (LieEquiv.refl : L ≃ₗ⁅R⁆ L) = ⊥ := by
  ext x
  simp only [mem_cartanP, LieEquiv.refl_apply, Submodule.mem_bot]
  constructor
  · intro hx
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul, ← sub_neg_eq_add, sub_eq_zero]
      exact hx
    simpa [smul_smul] using congrArg (fun v : L ↦ (⅟(2 : R)) • v) h2
  · rintro rfl
    simp

/-- An intertwining Lie equivalence maps `cartanP θ` onto `cartanP θ'`. -/
theorem map_cartanP (e : L ≃ₗ⁅R⁆ L') {θ : L ≃ₗ⁅R⁆ L} {θ' : L' ≃ₗ⁅R⁆ L'}
    (h : ∀ x, θ' (e x) = e (θ x)) :
    (cartanP θ).map e.toLinearMap = cartanP θ' := by
  ext y
  simp only [Submodule.mem_map, LieEquiv.coe_toLieHom, LieHom.coe_toLinearMap, mem_cartanP]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [h x, hx, map_neg]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    simp only [LieEquiv.coe_toLieHom]
    rw [← h, e.apply_symm_apply, hy, map_neg, e.apply_symm_apply]

/-- `[𝔨, 𝔭] ⊆ 𝔭`: bracketing a fixed vector with a `(-1)`-eigenvector yields a
`(-1)`-eigenvector. -/
theorem lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ cartanP θ) : ⁅x, y⁆ ∈ cartanP θ := by
  have hθx : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  rw [mem_cartanP, θ.map_lie, hθx, mem_cartanP.mp hy, lie_neg]

/-- `[𝔭, 𝔨] ⊆ 𝔭`: bracketing a `(-1)`-eigenvector with a fixed vector yields a
`(-1)`-eigenvector. -/
theorem lie_mem_cartanP_of_mem_cartanP_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ cartanP θ) (hy : y ∈ θ.toLieHom.fixedSubalgebra) : ⁅x, y⁆ ∈ cartanP θ := by
  have hθy : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [mem_cartanP, θ.map_lie, mem_cartanP.mp hx, hθy, neg_lie]

/-- `[𝔭, 𝔭] ⊆ 𝔨`: bracketing two `(-1)`-eigenvectors yields a fixed vector. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ cartanP θ) (hy : y ∈ cartanP θ) : ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [LieHom.mem_fixedSubalgebra]
  simp [mem_cartanP.mp hx, mem_cartanP.mp hy]

/-- **Eigenspace decomposition for an involutive automorphism**: when `2` is invertible, `L` is
the direct sum of the fixed subalgebra `𝔨` and `cartanP θ`. -/
theorem isCompl_fixedSubalgebra_cartanP [Invertible (2 : R)] {θ : L ≃ₗ⁅R⁆ L}
    (hinv : ∀ x, θ (θ x) = x) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule (cartanP θ) := by
  rw [isCompl_iff, Submodule.disjoint_def, codisjoint_iff, eq_top_iff]
  refine ⟨fun x hxK hxP ↦ ?_, fun x _ ↦ ?_⟩
  · have hK : θ x = x := LieHom.mem_fixedSubalgebra.mp hxK
    have hP : θ x = -x := mem_cartanP.mp hxP
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul]
      calc
        x + x = θ x + x := by rw [hK]
        _ = -x + x := by rw [hP]
        _ = 0 := neg_add_cancel x
    simpa [smul_smul] using congrArg (fun v : L ↦ (⅟(2 : R)) • v) h2
  · rw [Submodule.mem_sup]
    refine ⟨(⅟(2 : R)) • (x + θ x), ?_, (⅟(2 : R)) • (x - θ x), ?_, ?_⟩
    · rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra]
      simp [map_smul, map_add, hinv, add_comm]
    · rw [mem_cartanP, map_smul, map_sub, hinv, ← smul_neg, neg_sub]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul R x, smul_smul, invOf_mul_self, one_smul]

/-- The twisted Killing bilinear form `B_θ(x, y) = -κ(x, θ y)` attached to an automorphism `θ`. -/
noncomputable def cartanBilinForm (θ : L ≃ₗ⁅R⁆ L) : LinearMap.BilinForm R L :=
  -(killingForm R L).compl₁₂ LinearMap.id θ.toLinearMap

/-- Evaluation of the twisted Killing form `B_θ(x, y) = -κ(x, θ y)`. -/
@[simp]
theorem cartanBilinForm_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    cartanBilinForm θ x y = -killingForm R L x (θ y) :=
  (rfl)

/-- An involutive Lie automorphism is self-adjoint with respect to the Killing form. -/
theorem killingForm_apply_left_eq_right {θ : L ≃ₗ⁅R⁆ L} (hinv : ∀ x, θ (θ x) = x) (x y : L) :
    killingForm R L (θ x) y = killingForm R L x (θ y) := by
  rw [← killingForm_of_equiv_apply θ (θ x) y, hinv]

/-- For an involutive automorphism `θ`, the twisted Killing form `B_θ` is symmetric. -/
theorem cartanBilinForm_isSymm {θ : L ≃ₗ⁅R⁆ L} (hinv : ∀ x, θ (θ x) = x) :
    (cartanBilinForm θ).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff]
  refine ⟨fun x y ↦ ?_⟩
  simp only [RingHom.id_apply, cartanBilinForm_apply]
  rw [← killingForm_apply_left_eq_right hinv, LieModule.traceForm_comm]

/-- Any Lie algebra automorphism `θ` is orthogonal for `B_θ`. -/
theorem cartanBilinForm_apply_map (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    cartanBilinForm θ (θ x) (θ y) = cartanBilinForm θ x y := by
  rw [cartanBilinForm_apply, cartanBilinForm_apply, killingForm_of_equiv_apply]

/-- Any automorphism commuting with `θ` preserves `B_θ`. -/
theorem cartanBilinForm_apply_of_commute {θ φ : L ≃ₗ⁅R⁆ L}
    (hcomm : ∀ x, φ (θ x) = θ (φ x)) (x y : L) :
    cartanBilinForm θ (φ x) (φ y) = cartanBilinForm θ x y := by
  simp only [cartanBilinForm_apply, ← hcomm, killingForm_of_equiv_apply]

/-- For `x ∈ 𝔨`, `ad x` is skew-adjoint with respect to `B_θ`. -/
theorem cartanBilinForm_lie_left_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (y z : L) :
    cartanBilinForm θ ⁅x, y⁆ z = -cartanBilinForm θ y ⁅x, z⁆ := by
  have hθx : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  simp only [cartanBilinForm_apply, θ.map_lie, hθx, neg_neg]
  rw [LieModule.traceForm_lieInvariant, neg_neg]

/-- For `x ∈ 𝔭`, `ad x` is self-adjoint with respect to `B_θ`. -/
theorem cartanBilinForm_lie_left_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x : L}
    (hx : x ∈ cartanP θ) (y z : L) :
    cartanBilinForm θ ⁅x, y⁆ z = cartanBilinForm θ y ⁅x, z⁆ := by
  have hθx : θ x = -x := mem_cartanP.mp hx
  simp only [cartanBilinForm_apply, θ.map_lie, hθx, neg_lie, map_neg, neg_neg]
  rw [LieModule.traceForm_lieInvariant, neg_neg]

/-- The fixed subalgebra `𝔨` and `cartanP θ` are orthogonal with respect to the Killing form. -/
theorem killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [Invertible (2 : R)]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ cartanP θ) :
    killingForm R L x y = 0 := by
  have h := killingForm_of_equiv_apply θ x y
  have hθx : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  have hθy : θ y = -y := mem_cartanP.mp hy
  rw [hθx, hθy, map_neg] at h
  have h2 : (2 : R) * killingForm R L x y = 0 := by
    rw [two_mul, ← sub_neg_eq_add, sub_eq_zero]
    exact h.symm
  simpa [mul_assoc] using congrArg (fun r : R ↦ (⅟(2 : R)) * r) h2

/-- The fixed subalgebra `𝔨` and `cartanP θ` are orthogonal with respect to `B_θ`. -/
theorem cartanBilinForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [Invertible (2 : R)]
    {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ cartanP θ) :
    cartanBilinForm θ x y = 0 := by
  rw [cartanBilinForm_apply, mem_cartanP.mp hy, map_neg, neg_neg,
    killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy]

/-- On `𝔨`, `B_θ` agrees with `-κ`. -/
theorem cartanBilinForm_apply_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    cartanBilinForm θ x y = -killingForm R L x y := by
  have hθy : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [cartanBilinForm_apply, hθy]

/-- On `𝔭`, `B_θ` agrees with `κ`. -/
theorem cartanBilinForm_apply_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ cartanP θ) :
    cartanBilinForm θ x y = killingForm R L x y := by
  rw [cartanBilinForm_apply, mem_cartanP.mp hy, map_neg, neg_neg]

/-- The restriction of `B_θ` to the fixed subalgebra `𝔨`. -/
noncomputable def cartanBilinFormFixed (θ : L ≃ₗ⁅R⁆ L) :
    LinearMap.BilinForm R θ.toLieHom.fixedSubalgebra :=
  (cartanBilinForm θ).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
    θ.toLieHom.fixedSubalgebra.incl.toLinearMap

/-- Evaluation of `cartanBilinFormFixed`: on `𝔨`, `B_θ` equals `-κ`. -/
@[simp]
theorem cartanBilinFormFixed_apply (θ : L ≃ₗ⁅R⁆ L) (x y : θ.toLieHom.fixedSubalgebra) :
    cartanBilinFormFixed θ x y = -killingForm R L x y :=
  cartanBilinForm_apply_of_mem_fixedSubalgebra y.property

/-- The restriction of `B_θ` to `𝔨` is an `ad(𝔨)`-invariant bilinear form. -/
theorem cartanBilinFormFixed_lieInvariant (θ : L ≃ₗ⁅R⁆ L) :
    (cartanBilinFormFixed θ).lieInvariant θ.toLieHom.fixedSubalgebra := by
  intro x y z
  simpa only [cartanBilinFormFixed, LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap,
    LieSubalgebra.coe_incl, LieSubalgebra.coe_bracket] using
      cartanBilinForm_lie_left_of_mem_fixedSubalgebra x.property (y : L) (z : L)

end Involutive

/-! ### Cartan involutions of real Lie algebras -/

section CartanInvolution

variable {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']

/-- A **Cartan involution** of a real Lie algebra `L`: an involutive Lie algebra automorphism `θ`
for which the twisted Killing form `B_θ(x, y) = -κ(x, θ y)` is positive definite. A real Lie
algebra admitting a Cartan involution is necessarily finite-dimensional and semisimple. -/
def IsCartanInvolution (θ : L ≃ₗ⁅ℝ⁆ L) : Prop :=
  (∀ x, θ (θ x) = x) ∧ ∀ x : L, x ≠ 0 → 0 < -(killingForm ℝ L x (θ x))

/-- Characterization of a Cartan involution by involutivity and positivity of `-κ(x, θ x)`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅ℝ⁆ L} :
    IsCartanInvolution θ ↔ (∀ x, θ (θ x) = x) ∧ ∀ x : L, x ≠ 0 → 0 < -(killingForm ℝ L x (θ x)) :=
  Iff.rfl

namespace IsCartanInvolution

variable {θ θ' : L ≃ₗ⁅ℝ⁆ L}

/-- A Cartan involution is involutive. -/
theorem involutive (hθ : IsCartanInvolution θ) : Function.Involutive θ :=
  hθ.1

/-- Applying a Cartan involution twice is the identity. -/
theorem apply_apply (hθ : IsCartanInvolution θ) (x : L) : θ (θ x) = x :=
  hθ.1 x

/-- A Cartan involution is its own inverse. -/
theorem symm_eq_self (hθ : IsCartanInvolution θ) : θ.symm = θ := by
  ext x
  rw [LieEquiv.symm_apply_eq, hθ.apply_apply]

/-- The twisted Killing form `B_θ` is strictly positive on nonzero vectors. -/
theorem cartanBilinForm_pos (hθ : IsCartanInvolution θ) {x : L} (hx : x ≠ 0) :
    0 < cartanBilinForm θ x x :=
  hθ.2 x hx

/-- The twisted Killing form `B_θ` is nonnegative on the diagonal. -/
theorem cartanBilinForm_nonneg (hθ : IsCartanInvolution θ) (x : L) :
    0 ≤ cartanBilinForm θ x x := by
  by_cases hx : x = 0
  · subst hx; simp
  · exact (hθ.cartanBilinForm_pos hx).le

/-- The diagonal of `B_θ` vanishes only at `0`. -/
theorem cartanBilinForm_self_eq_zero_iff (hθ : IsCartanInvolution θ) {x : L} :
    cartanBilinForm θ x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hx0
    exact (hθ.cartanBilinForm_pos hx0).ne' hx
  · rintro rfl; simp

/-- The twisted Killing form `B_θ` is symmetric. -/
theorem cartanBilinForm_isSymm (hθ : IsCartanInvolution θ) : (cartanBilinForm θ).IsSymm :=
  TauCeti.cartanBilinForm_isSymm hθ.1

/-- The twisted Killing form `B_θ` is positive definite. -/
theorem cartanBilinForm_posDef (hθ : IsCartanInvolution θ) :
    (cartanBilinForm θ).toQuadraticMap.PosDef :=
  (LinearMap.BilinForm.posDef_toQuadraticMap_iff (cartanBilinForm θ)).mpr fun _ hx ↦
    hθ.cartanBilinForm_pos hx

/-- The twisted Killing form `B_θ` packaged as an `InnerProductSpace.Core ℝ L`. -/
@[instance_reducible]
noncomputable def innerProductCore (hθ : IsCartanInvolution θ) : InnerProductSpace.Core ℝ L where
  inner x y := cartanBilinForm θ x y
  conj_inner_symm x y := by
    simpa [RCLike.conj_to_real] using hθ.cartanBilinForm_isSymm.eq y x
  re_inner_nonneg x := hθ.cartanBilinForm_nonneg x
  add_left x y z := by simp
  smul_left x y r := by simp [smul_eq_mul]
  definite x hx := hθ.cartanBilinForm_self_eq_zero_iff.mp hx

/-- The inner product of `innerProductCore` is `B_θ`. -/
@[simp]
theorem innerProductCore_inner (hθ : IsCartanInvolution θ) (x y : L) :
    @inner ℝ L hθ.innerProductCore.toInner x y = cartanBilinForm θ x y :=
  (rfl)

/-- A real Lie algebra admitting a Cartan involution has nondegenerate Killing form (trivial
kernel). -/
theorem ker_killingForm_eq_bot (hθ : IsCartanInvolution θ) :
    LinearMap.ker (killingForm ℝ L) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h0 : killingForm ℝ L x (θ x) = 0 := by
    simpa using LinearMap.congr_fun (LinearMap.mem_ker.mp hx) (θ x)
  exact hθ.cartanBilinForm_self_eq_zero_iff.mp (by rw [cartanBilinForm_apply, h0, neg_zero])

/-- A real Lie algebra admitting a Cartan involution is Killing. -/
theorem isKilling (hθ : IsCartanInvolution θ) : IsKilling ℝ L :=
  isKilling_of_ker_killingForm_eq_bot ℝ L hθ.ker_killingForm_eq_bot

/-- A real Lie algebra admitting a Cartan involution is finite-dimensional. -/
theorem finiteDimensional (hθ : IsCartanInvolution θ) : FiniteDimensional ℝ L :=
  let _ := hθ.isKilling
  finite_of_isKilling

/-- A real Lie algebra admitting a Cartan involution is semisimple. -/
theorem isSemisimple (hθ : IsCartanInvolution θ) : IsSemisimple ℝ L :=
  let _ := hθ.isKilling
  let _ := hθ.finiteDimensional
  inferInstance

/-- A real Lie algebra admitting a Cartan involution has trivial centre. -/
theorem center_eq_bot (hθ : IsCartanInvolution θ) : center ℝ L = ⊥ :=
  let _ := hθ.isSemisimple
  LieAlgebra.center_eq_bot ℝ L

/-- A real Lie algebra admitting a Cartan involution is perfect: `⁅L, L⁆ = L`. -/
theorem derivedSeries_one_eq_top (hθ : IsCartanInvolution θ) : derivedSeries ℝ L 1 = ⊤ :=
  let _ := hθ.isKilling
  derivedSeries_one_eq_top_of_isKilling ℝ L

/-- The Killing form is negative definite on the fixed subalgebra `𝔨`. -/
theorem killingForm_neg_of_mem_fixedSubalgebra (hθ : IsCartanInvolution θ) {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx0 : x ≠ 0) : killingForm ℝ L x x < 0 := by
  have hpos := hθ.cartanBilinForm_pos hx0
  rw [cartanBilinForm_apply_of_mem_fixedSubalgebra hx] at hpos
  linarith

/-- The Killing form is positive definite on `cartanP θ`. -/
theorem killingForm_pos_of_mem_cartanP (hθ : IsCartanInvolution θ) {x : L}
    (hx : x ∈ cartanP θ) (hx0 : x ≠ 0) : 0 < killingForm ℝ L x x := by
  have hpos := hθ.cartanBilinForm_pos hx0
  rwa [cartanBilinForm_apply_of_mem_cartanP hx] at hpos

/-- The Cartan decomposition `L = 𝔨 ⊕ 𝔭`. -/
theorem isCompl_fixedSubalgebra_cartanP (hθ : IsCartanInvolution θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule (cartanP θ) :=
  TauCeti.isCompl_fixedSubalgebra_cartanP hθ.1

/-- `cartanP θ` is the Killing orthogonal complement of the fixed subalgebra `𝔨`. -/
theorem cartanP_eq_orthogonal_fixedSubalgebra (hθ : IsCartanInvolution θ) :
    cartanP θ = (killingForm ℝ L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule := by
  ext y
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hy x hx
    exact killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy
  · intro hy
    have hsup : y ∈ θ.toLieHom.fixedSubalgebra.toSubmodule ⊔ cartanP θ := by
      rw [hθ.isCompl_fixedSubalgebra_cartanP.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, p, hp, hkp⟩ := Submodule.mem_sup.mp hsup
    have hk' : k ∈ θ.toLieHom.fixedSubalgebra := hk
    have hk0 : k = 0 := by
      by_contra hkne
      have hneg := hθ.killingForm_neg_of_mem_fixedSubalgebra hk' hkne
      have hzero : killingForm ℝ L k k = 0 := by
        have hky := hy k hk
        rw [← hkp, map_add,
          killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hk' hp, add_zero] at hky
        exact hky
      linarith
    subst hk0
    simpa [← hkp] using hp

/-- **Uniqueness of a Cartan involution from its fixed subalgebra**: two Cartan involutions with
the same fixed subalgebra `𝔨` are equal. -/
theorem eq_of_fixedSubalgebra_eq (hθ : IsCartanInvolution θ) (hθ' : IsCartanInvolution θ')
    (h : θ.toLieHom.fixedSubalgebra = θ'.toLieHom.fixedSubalgebra) : θ = θ' := by
  have hP : cartanP θ = cartanP θ' := by
    rw [hθ.cartanP_eq_orthogonal_fixedSubalgebra, hθ'.cartanP_eq_orthogonal_fixedSubalgebra, h]
  ext x
  have hsup : x ∈ θ.toLieHom.fixedSubalgebra.toSubmodule ⊔ cartanP θ := by
    rw [hθ.isCompl_fixedSubalgebra_cartanP.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp hsup
  have hkK : k ∈ θ.toLieHom.fixedSubalgebra := hk
  have hk' : k ∈ θ'.toLieHom.fixedSubalgebra := h ▸ hkK
  have hp' : p ∈ cartanP θ' := hP ▸ hp
  have hθk : θ k = k := LieHom.mem_fixedSubalgebra.mp hkK
  have hθ'k : θ' k = k := LieHom.mem_fixedSubalgebra.mp hk'
  rw [map_add, map_add, hθk, hθ'k, mem_cartanP.mp hp, mem_cartanP.mp hp']

/-- For `x ∈ cartanP θ`, the adjoint operator `ad x` is diagonalizable over `ℝ`. -/
theorem iSup_eigenspace_ad_eq_top (hθ : IsCartanInvolution θ) {x : L} (hx : x ∈ cartanP θ) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  let _ : NormedAddCommGroup L := hθ.innerProductCore.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ L := InnerProductSpace.ofCore hθ.innerProductCore.toCore
  have _ : FiniteDimensional ℝ L := hθ.finiteDimensional
  have hsymm : (ad ℝ L x).IsSymmetric := fun y z ↦ by
    simpa [ad_apply] using cartanBilinForm_lie_left_of_mem_cartanP hx y z
  let b := hsymm.eigenvectorBasis rfl
  rw [eq_top_iff, ← b.toBasis.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (hsymm.eigenvalues rfl i)
    (hsymm.hasEigenvector_eigenvectorBasis rfl i).1

/-- Transporting a Cartan involution along a Lie algebra equivalence yields a Cartan involution. -/
theorem conj (hθ : IsCartanInvolution θ) (e : L ≃ₗ⁅ℝ⁆ L') :
    IsCartanInvolution ((e.symm.trans θ).trans e) := by
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · simp [hθ.apply_apply]
  · simp only [LieEquiv.trans_apply]
    have hsymm : e.symm x ≠ 0 := by
      intro h0
      exact hx (by simpa using congrArg e h0)
    have h := hθ.2 (e.symm x) hsymm
    rwa [← killingForm_of_equiv_apply e (e.symm x) (θ (e.symm x)), e.apply_symm_apply] at h

/-- Conjugation by a Lie algebra equivalence preserves the Cartan-involution property. -/
theorem conj_iff (e : L ≃ₗ⁅ℝ⁆ L') :
    IsCartanInvolution ((e.symm.trans θ).trans e) ↔ IsCartanInvolution θ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj e⟩
  have heq : ((e.trans ((e.symm.trans θ).trans e)).trans e.symm) = θ := by
    ext x
    simp
  simpa [heq] using h.conj e.symm

/-! #### Structure of the fixed subalgebra `𝔨` -/

/-- The restriction `B_θ|_𝔨` is symmetric. -/
theorem cartanBilinFormFixed_isSymm (hθ : IsCartanInvolution θ) :
    LinearMap.BilinForm.IsSymm (cartanBilinFormFixed θ) :=
  hθ.cartanBilinForm_isSymm.compl₁₂ _

/-- The restriction `B_θ|_𝔨` is positive definite. -/
theorem cartanBilinFormFixed_posDef (hθ : IsCartanInvolution θ) :
    (cartanBilinFormFixed θ).toQuadraticMap.PosDef :=
  (cartanBilinForm θ).posDef_toQuadraticMap_compl₁₂ hθ.cartanBilinForm_posDef
    θ.toLieHom.fixedSubalgebra.incl.toLinearMap Subtype.val_injective

/-- Under `B_θ|_𝔨`, the orthogonal complement of `[𝔨, 𝔨]` is the centre of `𝔨`. -/
theorem orthogonal_derivedSeries_one_fixedSubalgebra_eq_center (hθ : IsCartanInvolution θ) :
    InvariantForm.orthogonal (cartanBilinFormFixed θ)
      (cartanBilinFormFixed_lieInvariant θ)
      (derivedSeries ℝ θ.toLieHom.fixedSubalgebra 1) =
        center ℝ θ.toLieHom.fixedSubalgebra :=
  LinearMap.BilinForm.orthogonal_derivedSeries_one_eq_center _
    (LinearMap.BilinForm.nondegenerate_of_anisotropic _
      hθ.cartanBilinFormFixed_posDef.anisotropic).2
    (cartanBilinFormFixed_lieInvariant θ)

/-- The fixed subalgebra `𝔨` is the direct sum of its centre and its derived ideal. -/
theorem isCompl_center_derivedSeries_one_fixedSubalgebra (hθ : IsCartanInvolution θ) :
    IsCompl (center ℝ θ.toLieHom.fixedSubalgebra)
      (derivedSeries ℝ θ.toLieHom.fixedSubalgebra 1) :=
  let _ := hθ.finiteDimensional
  LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic _
    hθ.cartanBilinFormFixed_isSymm.isRefl
    hθ.cartanBilinFormFixed_posDef.anisotropic
    (cartanBilinFormFixed_lieInvariant θ)

/-- The derived ideal `[𝔨, 𝔨]` of the fixed subalgebra is semisimple. -/
theorem isSemisimple_derivedSeries_one_fixedSubalgebra (hθ : IsCartanInvolution θ) :
    IsSemisimple ℝ (derivedSeries ℝ θ.toLieHom.fixedSubalgebra 1) :=
  let _ := hθ.finiteDimensional
  LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic _
    hθ.cartanBilinFormFixed_isSymm.isRefl
    hθ.cartanBilinFormFixed_posDef.anisotropic
    (cartanBilinFormFixed_lieInvariant θ)

/-- The fixed subalgebra `𝔨` is reductive (its solvable radical equals its centre). -/
theorem hasCentralRadical_fixedSubalgebra (hθ : IsCartanInvolution θ) :
    HasCentralRadical ℝ θ.toLieHom.fixedSubalgebra :=
  let _ := hθ.finiteDimensional
  LinearMap.BilinForm.hasCentralRadical_of_anisotropic _
    hθ.cartanBilinFormFixed_isSymm.isRefl
    hθ.cartanBilinFormFixed_posDef.anisotropic
    (cartanBilinFormFixed_lieInvariant θ)

/-- The Killing form of the derived ideal `[𝔨, 𝔨]` is negative definite. -/
theorem killingForm_derivedSeries_one_fixedSubalgebra_neg (hθ : IsCartanInvolution θ)
    {x : derivedSeries ℝ θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm ℝ (derivedSeries ℝ θ.toLieHom.fixedSubalgebra 1) x x < 0 :=
  let _ := hθ.finiteDimensional
  LinearMap.BilinForm.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero _
    hθ.cartanBilinFormFixed_isSymm
    hθ.cartanBilinFormFixed_posDef
    (cartanBilinFormFixed_lieInvariant θ) x hx

/-! #### Compactness criterion -/

/-- A Cartan involution equals the identity if and only if its `-1`-eigenspace `cartanP θ`
vanishes. -/
theorem eq_refl_iff_cartanP_eq_bot (hθ : IsCartanInvolution θ) :
    θ = LieEquiv.refl ↔ cartanP θ = ⊥ := by
  constructor
  · rintro rfl
    exact cartanP_refl
  · intro hP
    ext x
    have hsup : x ∈ θ.toLieHom.fixedSubalgebra.toSubmodule ⊔ cartanP θ := by
      rw [hθ.isCompl_fixedSubalgebra_cartanP.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, p, hp, rfl⟩ := Submodule.mem_sup.mp hsup
    have hp0 : p = 0 := (Submodule.mem_bot ℝ).mp (hP ▸ hp)
    subst hp0
    have hθk : θ k = k := LieHom.mem_fixedSubalgebra.mp hk
    simp [hθk]

/-- A Cartan involution equals the identity if and only if the Killing form of `L` is negative
definite (i.e., `L` is compact). -/
theorem eq_refl_iff_forall_killingForm_neg (hθ : IsCartanInvolution θ) :
    θ = LieEquiv.refl ↔ ∀ x : L, x ≠ 0 → killingForm ℝ L x x < 0 := by
  constructor
  · rintro rfl x hx
    have hpos := hθ.2 x hx
    simp only [LieEquiv.refl_apply] at hpos
    linarith
  · intro hneg
    rw [hθ.eq_refl_iff_cartanP_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    linarith [hneg x hx0, hθ.killingForm_pos_of_mem_cartanP hx hx0]

end IsCartanInvolution

/-- The identity automorphism is a Cartan involution if and only if the Killing form is negative
definite. -/
theorem isCartanInvolution_refl_iff :
    IsCartanInvolution (LieEquiv.refl : L ≃ₗ⁅ℝ⁆ L) ↔
      ∀ x : L, x ≠ 0 → killingForm ℝ L x x < 0 := by
  simp [IsCartanInvolution]

/-- A nontrivial abelian real Lie algebra admits no Cartan involution in the semisimple sense. -/
theorem not_isCartanInvolution_of_isLieAbelian [IsLieAbelian L] [Nontrivial L]
    (θ : L ≃ₗ⁅ℝ⁆ L) : ¬ IsCartanInvolution θ := by
  intro hθ
  have _ := hθ.isKilling
  have _ := hθ.finiteDimensional
  have hsub : Subsingleton L := (IsKilling.isLieAbelian_iff_subsingleton ℝ L).mp inferInstance
  exact not_subsingleton L hsub

end CartanInvolution

end TauCeti
