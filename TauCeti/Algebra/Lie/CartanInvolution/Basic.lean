/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Algebra.Lie.InvariantForm.Positive
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Reductive.Fixed
import TauCeti.Algebra.Lie.Subalgebra.Automorphism
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Cartan involutions and the Cartan decomposition

A **Cartan involution** of a Lie algebra `L` over an ordered ring `R` (chiefly `ℝ`) is an
involutive Lie algebra automorphism `θ : L ≃ₗ⁅R⁆ L` whose twisted Killing form

`θ.cartanForm x y = -killingForm R L x (θ y)`

is positive definite. Its `+1`-eigenspace is the fixed Lie subalgebra `θ.toLieHom.fixedSubalgebra`
(`𝔨`) and its `-1`-eigenspace is `θ.cartanP` (`𝔭`).

For any involutive automorphism over a ring where `2` is invertible, `L` splits as the direct sum
`𝔨 ⊕ 𝔭`, the brackets satisfy `[𝔨, 𝔨] ⊆ 𝔨`, `[𝔨, 𝔭] ⊆ 𝔭`, `[𝔭, 𝔭] ⊆ 𝔨`, the two summands are
orthogonal for both the Killing form and `θ.cartanForm`, and `θ.cartanForm` is symmetric,
`θ`-orthogonal, and satisfies `B_θ(⁅x, y⁆, z) = -B_θ(y, ⁅θ x, z⁆)`.

When `θ` is a Cartan involution:

* `θ.cartanForm` is symmetric and positive definite, hence nondegenerate;
* the Killing form is nondegenerate, so `L` is automatically Killing and finite over `R`, and
  semisimple over a field (`LieEquiv.IsCartanInvolution.isKilling`, `finite`, `isSemisimple`);
* the Killing form is negative definite on `𝔨` and positive definite on `𝔭`, and `𝔨` and `𝔭` are
  each other's Killing orthogonal complements;
* `ad x` is `θ.cartanForm`-skew for `x ∈ 𝔨` and `θ.cartanForm`-symmetric for `x ∈ 𝔭`; over `ℝ`,
  `ad x` is therefore diagonalizable for every `x ∈ 𝔭`;
* `-(killingForm K L)|_𝔨` is a symmetric positive-definite invariant form on `𝔨`, so by
  `TauCeti.Algebra.Lie.InvariantForm.Positive`, `𝔨 = Z(𝔨) ⊕ [𝔨, 𝔨]` is reductive with semisimple
  derived ideal whose Killing form is negative definite.

A **reductive Cartan involution** (`LieEquiv.IsReductiveCartanInvolution`) is an involutive
automorphism whose restriction to the derived ideal `⁅L, L⁆` is a Cartan involution. Over a
partially ordered field, such a Lie algebra has central radical (`LieAlgebra.HasCentralRadical`).
For any automorphism `θ` of a finite-dimensional reductive Lie algebra of characteristic zero,
`θ` preserves both `Z(L)` and `⁅L, L⁆`, splitting `θ.cartanP` into the disjoint submodules
`θ.cartanP ⊓ Z(L)` and `θ.cartanP ⊓ ⁅L, L⁆` whose supremum is `θ.cartanP`. Conversely, extending a
Cartan involution of `⁅L, L⁆` by any linear involution of `Z(L)` yields a reductive Cartan
involution.

## Main definitions

* `LieEquiv.cartanP`: the `-1`-eigenspace `ker (θ + id)` of a Lie algebra automorphism.
* `LieEquiv.cartanForm`: the bilinear form `(x, y) ↦ -killingForm R L x (θ y)`.
* `LieEquiv.IsCartanInvolution`: predicate that `θ` is involutive and `θ.cartanForm` is positive
  on nonzero vectors.
* `LieEquiv.IsReductiveCartanInvolution`: predicate that `θ` is involutive and restricts to a
  Cartan involution on `derivedSeries R L 1`.

## Main results

* `LieEquiv.map_maximal_abelian_cartanP`: intertwining Lie equivalences transport maximal abelian
  subspaces of `θ.cartanP`.
* `LieEquiv.isCompl_fixedSubalgebra_cartanP_of_involutive`: the Cartan decomposition `L = 𝔨 ⊕ 𝔭`.
* `LieEquiv.IsCartanInvolution.isKilling`, `LieEquiv.IsCartanInvolution.finite`,
  `LieEquiv.IsCartanInvolution.isSemisimple`: a Lie algebra admitting a Cartan involution is
  Killing, finite, and (over a field) semisimple.
* `LieEquiv.IsCartanInvolution.orthogonal_fixedSubalgebra_eq_cartanP` and
  `LieEquiv.IsCartanInvolution.orthogonal_cartanP_eq_fixedSubalgebra`: `𝔨` and `𝔭` are mutual
  Killing orthogonal complements.
* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: for `x ∈ θ.cartanP` over `ℝ`,
  `ad ℝ L x` is diagonalizable over `ℝ`.
* `LieEquiv.IsCartanInvolution.isCompl_center_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.isSemisimple_derivedSeries_fixedSubalgebra`,
  `LieEquiv.IsCartanInvolution.hasCentralRadical_fixedSubalgebra`, and
  `LieEquiv.IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_neg`: `𝔨` is compact and
  reductive with semisimple derived ideal of negative-definite Killing form.
* `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical`,
  `LieEquiv.sup_cartanP_inf_center_derivedSeries`, and
  `LieEquiv.exists_isReductiveCartanInvolution_extend`: structure and extension of reductive
  Cartan involutions.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press (1978),
  Chapter III, §7.
-/

public section

open LieAlgebra Module

namespace LieEquiv

/-! ### The `-1`-eigenspace and the Cartan form -/

section CommRing

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- The `-1`-eigenspace `𝔭 = ker (θ + id)` of a Lie algebra automorphism `θ`. -/
def cartanP (θ : L ≃ₗ⁅R⁆ L) : Submodule R L :=
  LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id)

/-- Definitional characterization of `LieEquiv.cartanP`. -/
theorem cartanP_def (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanP = LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id) :=
  (rfl)

/-- Membership in `θ.cartanP` is the equation `θ x = -x`. -/
@[simp]
theorem mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x : L} : x ∈ θ.cartanP ↔ θ x = -x := by
  simp only [cartanP, LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe,
    LieEquiv.coe_toLinearEquiv, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

/-- `θ.cartanP` is the `(-1)`-eigenspace of `θ` as a linear endomorphism. -/
theorem cartanP_eq_eigenspace_neg_one (θ : L ≃ₗ⁅R⁆ L) :
    θ.cartanP = Module.End.eigenspace (θ : L →ₗ[R] L) (-1) := by
  ext x
  simp

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
    exact Submodule.map_mono h𝔞.prop.1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, ← e.map_lie, h𝔞.prop.2 x hx y hy,
      map_zero]
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
    have h𝔞_le : 𝔞 ≤ 𝔟 := fun x hx ↦
      ⟨e x, hle ⟨x, hx, rfl⟩, by simp⟩
    have h𝔟_le : 𝔟 ≤ 𝔞 := h𝔞.le_of_ge ⟨h𝔟P, h𝔟ab⟩ h𝔞_le
    intro y hy
    refine ⟨e.symm y, h𝔟_le ⟨y, hy, rfl⟩, by simp⟩

/-- The inverse of a Lie automorphism has the same `-1`-eigenspace. -/
@[simp]
theorem cartanP_symm (θ : L ≃ₗ⁅R⁆ L) : θ.symm.cartanP = θ.cartanP := by
  ext x
  rw [mem_cartanP, mem_cartanP, symm_apply_eq, map_neg, eq_comm, neg_eq_iff_eq_neg]

/-- Bracketing a fixed element with an element of `θ.cartanP` stays in `θ.cartanP`. -/
theorem lie_mem_cartanP_of_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  rw [mem_cartanP, θ.map_lie, hx', mem_cartanP.mp hy, lie_neg]

/-- Bracketing an element of `θ.cartanP` with a fixed element stays in `θ.cartanP`. -/
theorem lie_mem_cartanP_of_mem_cartanP_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [mem_cartanP, θ.map_lie, mem_cartanP.mp hx, hy', neg_lie]

/-- Bracketing two elements of `θ.cartanP` lands in the fixed subalgebra. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.cartanP) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, θ.map_lie, mem_cartanP.mp hx, mem_cartanP.mp hy,
    neg_lie, lie_neg, neg_neg]

/-- The Cartan bilinear form `B_θ(x, y) = -B(x, θ y)` associated to a Lie algebra automorphism
`θ`, where `B` is the Killing form. -/
noncomputable def cartanForm (θ : L ≃ₗ⁅R⁆ L) : LinearMap.BilinForm R L :=
  -((killingForm R L).compl₁₂ LinearMap.id (θ : L →ₗ[R] L))

/-- Pointwise evaluation of the Cartan bilinear form. -/
@[simp]
theorem cartanForm_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanForm x y = -killingForm R L x (θ y) :=
  (rfl)

/-- The Cartan form of the identity automorphism is the negative Killing form. -/
@[simp]
theorem cartanForm_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanForm = -killingForm R L := by
  ext x y
  simp

/-- The Cartan form of a conjugate automorphism is the transport of the original Cartan form. -/
theorem cartanForm_conj_apply (θ : L ≃ₗ⁅R⁆ L) (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    (e.symm.trans (θ.trans e)).cartanForm (e x) (e y) = θ.cartanForm x y := by
  simp

/-- The Cartan form is invariant under every Lie automorphism commuting with `θ`. -/
theorem cartanForm_apply_of_commute {θ φ : L ≃ₗ⁅R⁆ L} (h : ∀ x, φ (θ x) = θ (φ x)) (x y : L) :
    θ.cartanForm (φ x) (φ y) = θ.cartanForm x y := by
  rw [cartanForm_apply, ← h, LieAlgebra.killingForm_of_equiv_apply, cartanForm_apply]

/-- `θ` is orthogonal for its own Cartan form. -/
theorem cartanForm_apply_self_apply (θ : L ≃ₗ⁅R⁆ L) (x y : L) :
    θ.cartanForm (θ x) (θ y) = θ.cartanForm x y :=
  cartanForm_apply_of_commute (fun _ ↦ rfl) x y

/-- On a fixed second argument, the Killing form is the negative of the Cartan form. -/
theorem killingForm_eq_neg_cartanForm_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x y = -θ.cartanForm x y := by
  have hy' : θ y = y := LieHom.mem_fixedSubalgebra.mp hy
  rw [cartanForm_apply, hy', neg_neg]

/-- On a second argument in `θ.cartanP`, the Killing form agrees with the Cartan form. -/
theorem killingForm_eq_cartanForm_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L} (hy : y ∈ θ.cartanP) :
    killingForm R L x y = θ.cartanForm x y := by
  rw [cartanForm_apply, mem_cartanP.mp hy, map_neg, neg_neg]

/-! ### Involutive Lie automorphisms -/

/-- For an involutive automorphism `θ`, the Cartan form `B_θ(x, y) = -B(x, θ y)` is symmetric. -/
theorem cartanForm_isSymm_of_involutive {θ : L ≃ₗ⁅R⁆ L} (hinv : Function.Involutive θ) :
    θ.cartanForm.IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  rw [cartanForm_apply, cartanForm_apply, ← LieAlgebra.killingForm_of_equiv_apply θ x (θ y),
    hinv y, LieModule.traceForm_comm]

/-- For an involutive automorphism `θ`, `ad x` has `B_θ`-adjoint `-ad (θ x)`:
`B_θ(⁅x, y⁆, z) = -B_θ(y, ⁅θ x, z⁆)`. -/
theorem cartanForm_apply_lie_left_of_involutive {θ : L ≃ₗ⁅R⁆ L} (hinv : Function.Involutive θ)
    (x y z : L) :
    θ.cartanForm ⁅x, y⁆ z = -θ.cartanForm y ⁅θ x, z⁆ := by
  rw [cartanForm_apply, cartanForm_apply, neg_neg, LieModule.traceForm_lieInvariant, neg_neg,
    θ.map_lie, hinv x]

/-- For an involutive automorphism `θ` and `x ∈ 𝔨`, `ad x` is skew-adjoint for
`θ.cartanForm`. -/
theorem cartanForm_apply_lie_of_mem_fixedSubalgebra {θ : L ≃ₗ⁅R⁆ L}
    (hinv : Function.Involutive θ) {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (y z : L) :
    θ.cartanForm ⁅x, y⁆ z = -θ.cartanForm y ⁅x, z⁆ := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  rw [cartanForm_apply_lie_left_of_involutive hinv, hx']

/-- For an involutive automorphism `θ` and `x ∈ 𝔭`, `ad x` is symmetric for `θ.cartanForm`. -/
theorem cartanForm_apply_lie_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} (hinv : Function.Involutive θ)
    {x : L} (hx : x ∈ θ.cartanP) (y z : L) :
    θ.cartanForm ⁅x, y⁆ z = θ.cartanForm y ⁅x, z⁆ := by
  rw [cartanForm_apply_lie_left_of_involutive hinv, mem_cartanP.mp hx, neg_lie, map_neg, neg_neg]

section InvertibleTwo

variable [Invertible (2 : R)]

/-- The identity automorphism has trivial `-1`-eigenspace when `2` is invertible. -/
@[simp]
theorem cartanP_refl : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP, refl_apply, Submodule.mem_bot]
  exact ⟨TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R), fun hx ↦ by simp [hx]⟩

/-- **The Cartan decomposition `L = 𝔨 ⊕ 𝔭`**: for an involutive Lie automorphism over a ring
where `2` is invertible, the fixed subalgebra and `-1`-eigenspace are complementary submodules. -/
theorem isCompl_fixedSubalgebra_cartanP_of_involutive {θ : L ≃ₗ⁅R⁆ L}
    (hinv : Function.Involutive θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxk hxp
    have h1 : θ x = x := LieHom.mem_fixedSubalgebra.mp hxk
    exact TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R)
      (h1.symm.trans (mem_cartanP.mp hxp))
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hk : ⅟(2 : R) • (x + θ x) ∈ θ.toLieHom.fixedSubalgebra.toSubmodule := by
      rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra, coe_toLieHom, map_smul,
        map_add, hinv x, add_comm]
    have hp : ⅟(2 : R) • (x - θ x) ∈ θ.cartanP := by
      rw [mem_cartanP, map_smul, map_sub, hinv x, ← smul_neg, neg_sub]
    have hsum : ⅟(2 : R) • (x + θ x) + ⅟(2 : R) • (x - θ x) = x := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul R x, smul_smul, invOf_mul_self, one_smul]
    rw [← hsum]
    exact Submodule.add_mem_sup hk hp

/-- The fixed subalgebra and `θ.cartanP` are orthogonal for the Killing form when `2` is
invertible. -/
theorem killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  have hx' : θ x = x := LieHom.mem_fixedSubalgebra.mp hx
  refine TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R) ?_
  calc killingForm R L x y = killingForm R L (θ x) (θ y) :=
        (LieAlgebra.killingForm_of_equiv_apply θ x y).symm
    _ = killingForm R L x (-y) := by rw [hx', mem_cartanP.mp hy]
    _ = -killingForm R L x y := map_neg _ y

/-- The fixed subalgebra and `θ.cartanP` are orthogonal for the Cartan form when `2` is
invertible. -/
theorem cartanForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP {θ : L ≃ₗ⁅R⁆ L} {x y : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    θ.cartanForm x y = 0 := by
  rw [cartanForm_apply, mem_cartanP.mp hy, map_neg, neg_neg,
    killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy]

end InvertibleTwo

end CommRing

/-! ### The Cartan involution predicate -/

section Predicate

variable {R L L' : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- A **Cartan involution** of a Lie algebra `L`: an involutive Lie algebra automorphism `θ` for
which the Cartan form `B_θ(x, y) = -killingForm R L x (θ y)` is positive on nonzero vectors. -/
structure IsCartanInvolution (θ : L ≃ₗ⁅R⁆ L) : Prop where
  /-- A Cartan involution is involutive: `θ (θ x) = x`. -/
  involutive : Function.Involutive θ
  /-- The Cartan form `x ↦ -killingForm R L x (θ x)` is strictly positive on nonzero vectors. -/
  neg_killingForm_pos : ∀ x : L, x ≠ 0 → 0 < -(killingForm R L x (θ x))

/-- Unfolded characterization of `LieEquiv.IsCartanInvolution`. -/
theorem isCartanInvolution_iff {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsCartanInvolution ↔
      Function.Involutive θ ∧ ∀ x : L, x ≠ 0 → 0 < -(killingForm R L x (θ x)) :=
  ⟨fun h ↦ ⟨h.involutive, h.neg_killingForm_pos⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

/-- A Lie automorphism is a Cartan involution exactly when it is involutive and its Cartan form is
positive definite. -/
theorem isCartanInvolution_iff_posDef {θ : L ≃ₗ⁅R⁆ L} :
    θ.IsCartanInvolution ↔ Function.Involutive θ ∧ θ.cartanForm.toQuadraticMap.PosDef := by
  rw [isCartanInvolution_iff, LinearMap.BilinForm.posDef_toQuadraticMap_iff]
  simp only [cartanForm_apply]

/-- The identity automorphism is a Cartan involution iff `-killingForm R L` is positive on nonzero
vectors. -/
theorem isCartanInvolution_refl_iff :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).IsCartanInvolution ↔
      ∀ x : L, x ≠ 0 → 0 < -(killingForm R L x x) := by
  simp [isCartanInvolution_iff, Function.Involutive]

/-- Conjugation by a Lie algebra equivalence preserves Cartan involutions. -/
theorem IsCartanInvolution.conj {θ : L ≃ₗ⁅R⁆ L} (hθ : θ.IsCartanInvolution)
    (e : L ≃ₗ⁅R⁆ L') :
    (e.symm.trans (θ.trans e)).IsCartanInvolution where
  involutive y := by simp [hθ.involutive _]
  neg_killingForm_pos y hy := by
    have h0 : e.symm y ≠ 0 := fun h ↦ hy (by simpa using congrArg e h)
    have hval := cartanForm_conj_apply θ e (e.symm y) (e.symm y)
    simp only [cartanForm_apply, apply_symm_apply] at hval
    rw [hval]
    exact hθ.neg_killingForm_pos (e.symm y) h0

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

/-- Over a partially ordered commutative ring with ordered addition, the identity automorphism is a
Cartan involution iff the Killing form is strictly negative on nonzero vectors. -/
theorem isCartanInvolution_refl_iff_neg [IsOrderedAddMonoid R] :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).IsCartanInvolution ↔
      ∀ x : L, x ≠ 0 → killingForm R L x x < 0 := by
  simp only [isCartanInvolution_refl_iff, neg_pos]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅R⁆ L}

/-- A Cartan involution is its own inverse. -/
theorem symm_eq (hθ : θ.IsCartanInvolution) : θ.symm = θ :=
  LieEquiv.ext fun x ↦ θ.symm_apply_eq.mpr (hθ.involutive x).symm

/-- The Cartan form of a Cartan involution is strictly positive on nonzero vectors. -/
theorem cartanForm_pos (hθ : θ.IsCartanInvolution) {x : L} (hx : x ≠ 0) :
    0 < θ.cartanForm x x :=
  hθ.neg_killingForm_pos x hx

/-- The diagonal of the Cartan form is nonnegative everywhere. -/
theorem cartanForm_nonneg (hθ : θ.IsCartanInvolution) (x : L) : 0 ≤ θ.cartanForm x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hθ.cartanForm_pos hx).le

/-- The diagonal of the Cartan form vanishes only at zero. -/
theorem cartanForm_self_eq_zero_iff (hθ : θ.IsCartanInvolution) {x : L} :
    θ.cartanForm x x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ (hθ.cartanForm_pos hx).ne' h, fun h ↦ by simp [h]⟩

/-- The Cartan form of a Cartan involution has positive-definite quadratic map. -/
theorem cartanForm_posDef (hθ : θ.IsCartanInvolution) : θ.cartanForm.toQuadraticMap.PosDef :=
  (isCartanInvolution_iff_posDef.mp hθ).2

/-- The Cartan form of a Cartan involution is symmetric. -/
theorem cartanForm_isSymm (hθ : θ.IsCartanInvolution) : θ.cartanForm.IsSymm :=
  cartanForm_isSymm_of_involutive hθ.involutive

/-- The Cartan form of a Cartan involution is nondegenerate. -/
theorem cartanForm_nondegenerate (hθ : θ.IsCartanInvolution) : θ.cartanForm.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_of_anisotropic _ hθ.cartanForm_posDef.anisotropic

/-- The Killing form of a Lie algebra carrying a Cartan involution is nondegenerate. -/
theorem killingForm_nondegenerate (hθ : θ.IsCartanInvolution) :
    (killingForm R L).Nondegenerate := by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  by_contra hx0
  have hpos := hθ.neg_killingForm_pos x hx0
  rw [hx (θ x), neg_zero] at hpos
  exact lt_irrefl 0 hpos

/-- A Lie algebra admitting a Cartan involution is Killing. -/
theorem isKilling (hθ : θ.IsCartanInvolution) : LieAlgebra.IsKilling R L :=
  TauCeti.isKilling_of_killingForm_nondegenerate R L hθ.killingForm_nondegenerate

/-- A Lie algebra admitting a Cartan involution is finite over the base ring. -/
theorem finite (hθ : θ.IsCartanInvolution) : Module.Finite R L := by
  have := hθ.isKilling
  exact TauCeti.finite_of_isKilling

/-- The Killing form is strictly positive on nonzero vectors of `θ.cartanP`. -/
theorem killingForm_pos_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) (hx0 : x ≠ 0) :
    0 < killingForm R L x x := by
  rw [killingForm_eq_cartanForm_of_mem_cartanP hx]
  exact hθ.cartanForm_pos hx0

/-- The Killing form is nonnegative on `θ.cartanP`. -/
theorem killingForm_nonneg_of_mem_cartanP (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ θ.cartanP) :
    0 ≤ killingForm R L x x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · exact (hθ.killingForm_pos_of_mem_cartanP hx hx0).le

/-- The Killing form is strictly negative on nonzero vectors of the fixed subalgebra `𝔨`. -/
theorem killingForm_neg_of_mem_fixedSubalgebra [IsOrderedAddMonoid R]
    (hθ : θ.IsCartanInvolution) {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hx0 : x ≠ 0) :
    killingForm R L x x < 0 := by
  rw [killingForm_eq_neg_cartanForm_of_mem_fixedSubalgebra hx, neg_lt_zero]
  exact hθ.cartanForm_pos hx0

/-- The Killing form is nonpositive on the fixed subalgebra `𝔨`. -/
theorem killingForm_nonpos_of_mem_fixedSubalgebra [IsOrderedAddMonoid R]
    (hθ : θ.IsCartanInvolution) {x : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    killingForm R L x x ≤ 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · exact (hθ.killingForm_neg_of_mem_fixedSubalgebra hx hx0).le

/-- The Killing orthogonal complement of the fixed subalgebra `𝔨` is `θ.cartanP`. -/
theorem orthogonal_fixedSubalgebra_eq_cartanP [Invertible (2 : R)]
    (hθ : θ.IsCartanInvolution) :
    (killingForm R L).orthogonal θ.toLieHom.fixedSubalgebra.toSubmodule = θ.cartanP := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hx
    have hcompl := isCompl_fixedSubalgebra_cartanP_of_involutive hθ.involutive
    obtain ⟨k, hk, p, hp, rfl⟩ :=
      Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top (x := x))
    have hkk : killingForm R L k k = 0 := by
      have h1 := hx k hk
      have h2 := killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hk hp
      rw [map_add, h2, add_zero] at h1
      exact h1
    have hk0 : k = 0 := by
      by_contra hne
      rw [killingForm_eq_neg_cartanForm_of_mem_fixedSubalgebra hk, neg_eq_zero] at hkk
      exact (hθ.cartanForm_pos hne).ne' hkk
    simpa [hk0] using hp
  · intro hx y hy
    exact killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hy hx

/-- The Killing orthogonal complement of `θ.cartanP` is the fixed subalgebra `𝔨`. -/
theorem orthogonal_cartanP_eq_fixedSubalgebra [Invertible (2 : R)]
    (hθ : θ.IsCartanInvolution) :
    (killingForm R L).orthogonal θ.cartanP = θ.toLieHom.fixedSubalgebra.toSubmodule := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hx
    have hcompl := isCompl_fixedSubalgebra_cartanP_of_involutive hθ.involutive
    obtain ⟨k, hk, p, hp, rfl⟩ :=
      Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top (x := x))
    have hpp : killingForm R L p p = 0 := by
      have h1 := hx p hp
      have h2 := killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hk hp
      rw [map_add, LieModule.traceForm_comm R L L p k, h2, zero_add] at h1
      exact h1
    have hp0 : p = 0 := by
      by_contra hne
      exact (hθ.killingForm_pos_of_mem_cartanP hp hne).ne' hpp
    simpa [hp0] using hk
  · intro hx y hy
    rw [LieModule.traceForm_comm]
    exact killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP hx hy

/-- The restriction of `-killingForm R L` to the fixed subalgebra `𝔨` is symmetric, positive
definite, and `𝔨`-invariant. -/
private theorem neg_killingForm_restrict_fixedSubalgebra_spec (hθ : θ.IsCartanInvolution) :
    let B : LinearMap.BilinForm R θ.toLieHom.fixedSubalgebra :=
      (-(killingForm R L)).compl₁₂ θ.toLieHom.fixedSubalgebra.incl.toLinearMap
        θ.toLieHom.fixedSubalgebra.incl.toLinearMap
    B.IsSymm ∧ B.toQuadraticMap.PosDef ∧ B.lieInvariant θ.toLieHom.fixedSubalgebra := by
  refine ⟨?_, ?_, ?_⟩
  · refine (LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_).compl₁₂ _
    simp only [LinearMap.neg_apply, LieModule.traceForm_comm]
  · rw [LinearMap.BilinForm.posDef_toQuadraticMap_iff]
    intro x hx
    simp only [LinearMap.compl₁₂_apply, LinearMap.neg_apply, LieHom.coe_toLinearMap,
      LieSubalgebra.coe_incl]
    have hfx : θ x = x := LieHom.mem_fixedSubalgebra.mp x.property
    simpa only [hfx] using hθ.neg_killingForm_pos x (fun h ↦ hx (Subtype.ext h))
  · have hinv : (-(killingForm R L)).lieInvariant L := by
      intro x y z
      simp only [LinearMap.neg_apply]
      rw [LieModule.traceForm_lieInvariant, neg_neg]
    exact hinv.compl₁₂ θ.toLieHom.fixedSubalgebra.incl

end IsCartanInvolution

/-- A nontrivial abelian Lie algebra admits no Cartan involution. -/
theorem not_isCartanInvolution_of_isLieAbelian [IsLieAbelian L] [Nontrivial L]
    (θ : L ≃ₗ⁅R⁆ L) :
    ¬ θ.IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have had : LieAlgebra.ad R L x = 0 := by
    ext y
    exact trivial_lie_zero L L x y
  have hkill : killingForm R L x (θ x) = 0 := by
    rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero]
  have hpos := hθ.neg_killingForm_pos x hx
  rw [hkill, neg_zero] at hpos
  exact lt_irrefl 0 hpos

end Predicate

/-! ### Semisimplicity and compactness of `𝔨` over a field -/

section Field

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

namespace IsCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- A Lie algebra admitting a Cartan involution over a partially ordered field is semisimple. -/
theorem isSemisimple (hθ : θ.IsCartanInvolution) : LieAlgebra.IsSemisimple K L := by
  have := hθ.isKilling
  have := hθ.finite
  infer_instance

/-- The fixed subalgebra `𝔨` is the direct sum of its centre and its derived ideal. -/
theorem isCompl_center_derivedSeries_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    IsCompl (center K θ.toLieHom.fixedSubalgebra)
      (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have := hθ.finite
  obtain ⟨hsymm, hpos, hinv⟩ := hθ.neg_killingForm_restrict_fixedSubalgebra_spec
  exact LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic _ hsymm.isRefl
    hpos.anisotropic hinv

/-- The derived ideal `[𝔨, 𝔨]` of the fixed subalgebra is semisimple. -/
theorem isSemisimple_derivedSeries_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    LieAlgebra.IsSemisimple K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) := by
  have := hθ.finite
  obtain ⟨hsymm, hpos, hinv⟩ := hθ.neg_killingForm_restrict_fixedSubalgebra_spec
  exact LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic _ hsymm.isRefl
    hpos.anisotropic hinv

/-- The fixed subalgebra `𝔨` is reductive (has central radical). -/
theorem hasCentralRadical_fixedSubalgebra (hθ : θ.IsCartanInvolution) :
    LieAlgebra.HasCentralRadical K θ.toLieHom.fixedSubalgebra := by
  have := hθ.finite
  obtain ⟨hsymm, hpos, hinv⟩ := hθ.neg_killingForm_restrict_fixedSubalgebra_spec
  exact LinearMap.BilinForm.hasCentralRadical_of_anisotropic _ hsymm.isRefl
    hpos.anisotropic hinv

end IsCartanInvolution

end Field

section OrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [LieRing L] [LieAlgebra K L]

/-- The Killing form of `[𝔨, 𝔨]` is strictly negative on nonzero vectors. -/
theorem IsCartanInvolution.killingForm_derivedSeries_fixedSubalgebra_neg {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution)
    {x : derivedSeries K θ.toLieHom.fixedSubalgebra 1} (hx : x ≠ 0) :
    killingForm K (derivedSeries K θ.toLieHom.fixedSubalgebra 1) x x < 0 := by
  have := hθ.finite
  obtain ⟨hsymm, hpos, hinv⟩ := hθ.neg_killingForm_restrict_fixedSubalgebra_spec
  exact LinearMap.BilinForm.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero _ hsymm
    hpos hinv x hx

end OrderedField

/-! ### Real diagonalizability of `ad x` for `x ∈ 𝔭` -/

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

namespace IsCartanInvolution

/-- For a Cartan involution `θ` of a real Lie algebra and `x ∈ θ.cartanP`, the adjoint operator
`ad ℝ L x` is diagonalizable over `ℝ`: its real eigenspaces span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (LieAlgebra.ad ℝ L x) μ = ⊤ := by
  have := hθ.finite
  let q : LinearMap.BilinForm ℝ L :=
    θ.cartanForm.compl₁₂ (LieAlgebra.ad ℝ L x) LinearMap.id
  have hq : q.IsSymm := LinearMap.BilinForm.isSymm_def.mpr fun y z ↦ by
    simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply, LieAlgebra.ad_apply]
    rw [cartanForm_apply_lie_of_mem_cartanP hθ.involutive hx, hθ.cartanForm_isSymm.eq]
  have heig (μ : ℝ) :
      θ.cartanForm.relativeEigenspace q μ = Module.End.eigenspace (LieAlgebra.ad ℝ L x) μ := by
    ext y
    rw [LinearMap.BilinForm.mem_relativeEigenspace_iff, Module.End.mem_eigenspace_iff]
    constructor
    · intro hy
      refine sub_eq_zero.mp (hθ.cartanForm_nondegenerate.1 _ fun z ↦ ?_)
      have h1 := hy z
      simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply] at h1
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h1, sub_self]
    · intro hy z
      simp only [q, LinearMap.compl₁₂_apply, LinearMap.id_apply, hy, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
  have huniv := LinearMap.BilinForm.relativeSpectralSubspace_univ hθ.cartanForm_isSymm
    (fun v hv ↦ hθ.cartanForm_pos hv) hq
  rw [LinearMap.BilinForm.relativeSpectralSubspace_def] at huniv
  simpa only [Set.mem_univ, iSup_pos, heig] using huniv

/-- For a Cartan involution `θ` of a real Lie algebra and `x ∈ θ.cartanP`, `ad ℝ L x` is a
semisimple endomorphism. -/
theorem isSemisimple_ad_of_mem_cartanP {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (LieAlgebra.ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsCartanInvolution

end Real

/-! ### Reductive Cartan involutions -/

section Reductive

section CommRing

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

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is Killing. -/
theorem IsReductiveCartanInvolution.isKilling_derivedSeries {θ : L ≃ₗ⁅R⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.IsKilling R (derivedSeries R L 1) := by
  obtain ⟨_, _, hθD⟩ := hθ.derivedSeries_isCartanInvolution
  exact hθD.isKilling

end CommRing

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

section Field

variable {K L : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]

/-- Every Cartan involution over a partially ordered field is a reductive Cartan involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) :
    θ.IsReductiveCartanInvolution where
  involutive := hθ.involutive
  derivedSeries_isCartanInvolution := by
    have := hθ.finite
    let θD := θ.restrictDerivedSeries 1
    refine ⟨θD, fun x ↦ θ.coe_restrictDerivedSeries 1 x,
      ⟨fun x ↦ Subtype.ext (by simp [θD, hθ.involutive x]), fun x hx ↦ ?_⟩⟩
    have hval : killingForm K (derivedSeries K L 1) x (θD x) = killingForm K L x (θ x) := by
      rw [LieIdeal.killingForm_eq]
      change killingForm K L x (θD x) = killingForm K L x (θ x)
      rw [θ.coe_restrictDerivedSeries]
    rw [hval]
    exact hθ.neg_killingForm_pos x (fun h ↦ hx (Subtype.ext h))

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- The derived ideal of a Lie algebra with a reductive Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.IsSemisimple K (derivedSeries K L 1) := by
  obtain ⟨_, _, hθD⟩ := hθ.derivedSeries_isCartanInvolution
  exact hθD.isSemisimple

/-- A Lie algebra admitting a reductive Cartan involution is reductive (has central radical). -/
theorem hasCentralRadical (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.HasCentralRadical K L := by
  have := hθ.isSemisimple_derivedSeries
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

end IsReductiveCartanInvolution

/-- On a finite-dimensional reductive Lie algebra over a partially ordered field of characteristic
zero, combining a linear involution `θZ` of the centre with a Cartan involution `θD` of the
derived ideal produces a reductive Cartan involution of `L`. -/
theorem exists_isReductiveCartanInvolution_extend [CharZero K] [FiniteDimensional K L]
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
  have hf_z (z : center K L) : f z = θZ z := by
    simpa using hf_add z 0
  have hf_d (d : derivedSeries K L 1) : f d = θD d := by
    simpa using hf_add 0 d
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
  let θ : L ≃ₗ⁅K⁆ L :=
    { f with map_lie' := fun {x y} ↦ hlie x y }
  refine ⟨θ, ⟨fun x ↦ ?_, ⟨θD, fun d ↦ (hf_d d).symm, hθD⟩⟩,
    fun z ↦ hf_z z, fun d ↦ hf_d d⟩
  obtain ⟨⟨z, d⟩, hx⟩ := e.surjective x
  have hx' : (z : L) + d = x := (he z d).symm.trans hx
  rw [← hx']
  exact (congrArg f (hf_add z d)).trans
    ((hf_add (θZ z) (θD d)).trans (by rw [hθZ z, hθD.involutive d]))

end Field

end Reductive

end LieEquiv
