/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.RankOne
import TauCeti.Algebra.Lie.Orthogonal.CrossProduct.Spectrum

/-!
# The Cartan integers of a compact Lie algebra

Let `L` be a finite-dimensional real Lie algebra with a symmetric positive definite invariant
bilinear form `B`, the Lie algebra of a compact Lie group for instance, and let `t` be a subspace,
such as a maximal commutative subspace. A **root pair** of `t` with root `α ∈ t*` is a pair `x, y`
that every `H ∈ t` rotates by the angle `α(H)`: `⁅H, x⁆ = α(H) y` and `⁅H, y⁆ = -α(H) x`. These
are the bases `v, J v` of the real root planes `TauCeti.IsRootPlane B t α E J`.

This file proves that the real roots are **crystallographic**. If `x ≠ 0, y` is a root pair with
root `α` whose bracket `Z = ⁅x, y⁆` lies in `t`, and `u ≠ 0, w` is a root pair with root `β`, then

`2 β(Z) / α(Z) ∈ ℤ`

(`LinearMap.BilinForm.exists_int_two_mul_root_apply_lie_eq_mul_of_lie_eq_smul`). In terms of the
vectors `a, b ∈ t` representing `α, β` through `B`, this is the integrality of the Cartan integer

`⟨β, α^∨⟩ = 2 B(a, b) / B(a, a)`

(`LinearMap.BilinForm.exists_int_two_mul_apply_eq_mul_of_lie_eq_smul`), where `α^∨ = 2 a / B(a, a)`
is the coroot of `α`. For root planes of a maximal commutative subspace this is
`TauCeti.IsRootPlane.exists_int_two_mul_apply_eq_mul`.

The proof uses the rank-one subalgebra of the root pair `x, y`
(`LinearMap.BilinForm.exists_injective_lieHom_soThree_of_lie_eq_smul`): a copy of `so(3)` in `L`
whose third basis vector `K` is the element of `t` with `α(K) = 1`, a positive multiple of `Z`. Its
adjoint action makes `L` a finite-dimensional representation of `so(3)`, in which `K` rotates the
pair `u, w` at the speed `β(K)`. Such speeds are half-integers
(`TauCeti.exists_int_two_mul_eq_of_lie_eq_smul`), because the complexification of `so(3)` is
`𝔰𝔩₂(ℂ)`; so `2 β(K) = 2 β(Z) / α(Z)` is an integer.

## Main results

* `LinearMap.BilinForm.exists_int_two_mul_root_apply_lie_eq_mul_of_lie_eq_smul`:
  `2 β(⁅x, y⁆) / α(⁅x, y⁆)` is an integer.
* `LinearMap.BilinForm.exists_int_two_mul_apply_eq_mul_of_lie_eq_smul`: the Cartan integer
  `2 B(a, b) / B(a, a)` is an integer.
* `TauCeti.IsRootPlane.exists_int_two_mul_apply_eq_mul`: the same for two root planes.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, §2 (the roots of a compact Lie group form a root
  system).
-/

public section

open LieAlgebra.Orthogonal Module

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {t : Submodule ℝ L} {α β : Dual ℝ t} {x y u w : L}

open TauCeti

/-- **The real roots are crystallographic.** Let `B` be a symmetric positive definite invariant
form on a finite-dimensional real Lie algebra `L` and `t` a subspace. Let `x, y` be a root pair of
`t` with root `α` whose bracket `⁅x, y⁆` lies in `t`, and let `u ≠ 0, w` be a root pair with root
`β`. Then `2 β(⁅x, y⁆)` is an integer multiple of `α(⁅x, y⁆)`. When `x ≠ 0` and `α ≠ 0`,
`α(⁅x, y⁆) > 0` (`LinearMap.BilinForm.lieInvariant.root_apply_lie_pos_of_lie_eq_smul`), and the
integer is the Cartan integer `2 β(⁅x, y⁆) / α(⁅x, y⁆)`. -/
theorem exists_int_two_mul_root_apply_lie_eq_mul_of_lie_eq_smul (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x))
    (hxy : ⁅x, y⁆ ∈ t) (hu : ∀ H : t, ⁅(H : L), u⁆ = β H • w)
    (hw : ∀ H : t, ⁅(H : L), w⁆ = -(β H • u)) (hu0 : u ≠ 0) :
    ∃ n : ℤ, 2 * β ⟨⁅x, y⁆, hxy⟩ = n * α ⟨⁅x, y⁆, hxy⟩ := by
  set Z : t := ⟨⁅x, y⁆, hxy⟩ with hZ
  rcases eq_or_ne Z 0 with hZ0 | hZ0
  · exact ⟨0, by simp [hZ0]⟩
  -- A vanishing root or a vanishing `x` would force `⁅x, y⁆ = 0`.
  have hα : α ≠ 0 := by
    rintro rfl
    refine hZ0 (Subtype.ext ((hBp.anisotropic _ ?_)))
    simpa using hB.apply_lie_eq_mul_of_lie_eq_smul hx Z
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hZ0 (Subtype.ext (by simp [hZ]))
  -- The rank-one subalgebra of `x, y`: its third basis vector `K` lies in `t`, with `α(K) = 1`.
  obtain ⟨f, -, ⟨c, -, hf₀, hf₁⟩, hK, hαK⟩ :=
    B.exists_injective_lieHom_soThree_of_lie_eq_smul hBs hBp hB hα hx0 hx hy hxy
  let a : Fin 3 → L := fun i ↦ f (soThreeEquiv ℝ (Pi.single i 1))
  have h₀ : ⁅a 0, a 1⁆ = a 2 := by simp only [a, ← LieHom.map_lie, lie_soThreeEquiv_single_zero_one]
  have h₁ : ⁅a 1, a 2⁆ = a 0 := by simp only [a, ← LieHom.map_lie, lie_soThreeEquiv_single_one_two]
  have h₂ : ⁅a 2, a 0⁆ = a 1 := by simp only [a, ← LieHom.map_lie, lie_soThreeEquiv_single_two_zero]
  -- `K = c² ⁅x, y⁆`, so `α(K) = 1` gives `c² α(⁅x, y⁆) = 1`.
  have hKZ : (⟨a 2, hK⟩ : t) = (c * c) • Z :=
    Subtype.ext (by simp only [← h₀, a, hf₀, hf₁, smul_lie, lie_smul, smul_smul, hZ,
      SetLike.val_smul])
  -- In the adjoint representation, `K` rotates `u, w` at the speed `β(K)`.
  obtain ⟨n, hn⟩ := exists_int_two_mul_eq_of_lie_eq_smul h₀ h₁ h₂ (hu ⟨a 2, hK⟩) (hw ⟨a 2, hK⟩) hu0
  refine ⟨n, ?_⟩
  rw [hKZ, map_smul, smul_eq_mul] at hn hαK
  rw [← hn]
  linear_combination (-2 * β Z) * hαK

/-- **The Cartan integers of a compact Lie algebra are integers.** Let `B` be a symmetric positive
definite invariant form on a finite-dimensional real Lie algebra `L` and `t` a subspace. Let
`x ≠ 0, y` be a root pair of `t` with root `α` whose bracket `⁅x, y⁆` lies in `t`, and `u ≠ 0, w`
a root pair with root `β`. If `a, b ∈ t` represent `α` and `β` through `B`, then `2 B(a, b)` is an
integer multiple of `B(a, a)`: the Cartan integer `⟨β, α^∨⟩ = 2 B(a, b) / B(a, a)` is an integer.
-/
theorem exists_int_two_mul_apply_eq_mul_of_lie_eq_smul (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L) (hx0 : x ≠ 0)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x))
    (hxy : ⁅x, y⁆ ∈ t) (hu : ∀ H : t, ⁅(H : L), u⁆ = β H • w)
    (hw : ∀ H : t, ⁅(H : L), w⁆ = -(β H • u)) (hu0 : u ≠ 0) {a b : t}
    (ha : ∀ H : t, B a H = α H) (hb : ∀ H : t, B b H = β H) :
    ∃ n : ℤ, 2 * B a b = n * B a a := by
  obtain ⟨n, hn⟩ := B.exists_int_two_mul_root_apply_lie_eq_mul_of_lie_eq_smul hBs hBp hB hx hy hxy
    hu hw hu0
  refine ⟨n, ?_⟩
  -- `B(H, ⁅x, y⁆) = α(H) B(y, y)`, so `β(⁅x, y⁆) = B(a, b) B(y, y)` and
  -- `α(⁅x, y⁆) = B(a, a) B(y, y)`.
  have hZ (H : t) : B H ⁅x, y⁆ = B a H * B y y := by
    rw [ha, hB.apply_lie_eq_mul_of_lie_eq_smul hx H]
  rw [← hb, ← ha, hZ, hZ] at hn
  -- The root `α` is nonzero on `x ≠ 0` only if `y ≠ 0`, so `B(y, y) > 0` or both sides vanish.
  rcases eq_or_ne y 0 with rfl | hy0
  · have hα : α = 0 := LinearMap.ext fun H ↦ by
      simpa [hx0] using (hy H).symm
    simp [ha, hα]
  have hyy : B y y ≠ 0 := (by simpa using hBp y hy0 : 0 < B y y).ne'
  exact mul_right_cancel₀ hyy (by linear_combination hn)

end LinearMap.BilinForm

namespace TauCeti.IsRootPlane

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {B : LinearMap.BilinForm ℝ L} {t : Submodule ℝ L} {α β : Dual ℝ t} {E E' : Submodule ℝ L}
  {J : Module.End ℝ E} {J' : Module.End ℝ E'}

/-- **The Cartan integers of two root planes are integers.** Let `B` be a symmetric positive
definite invariant form on a finite-dimensional real Lie algebra `L` and `t` a subspace containing
every element that commutes with it, such as a maximal commutative subspace. If `E` and `E'` are
nonzero root planes of `t` with roots `α` and `β`, and `a, b ∈ t` represent `α` and `β` through
`B`, then the Cartan integer `⟨β, α^∨⟩ = 2 B(a, b) / B(a, a)` is an integer. -/
theorem exists_int_two_mul_apply_eq_mul (hE : IsRootPlane B t α E J)
    (hE' : IsRootPlane B t β E' J') (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant L) (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t) (hE0 : E ≠ ⊥)
    (hE'0 : E' ≠ ⊥) {a b : t} (ha : ∀ H : t, B a H = α H) (hb : ∀ H : t, B b H = β H) :
    ∃ n : ℤ, 2 * B a b = n * B a a := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
  obtain ⟨v', hv', hv'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE'0
  have hx (H : t) := hE.lie_apply H ⟨v, hv⟩
  have hy (H : t) : ⁅(H : L), (J ⟨v, hv⟩ : L)⁆ = -(α H • v) := by
    rw [hE.lie_apply, hE.apply_apply, Submodule.coe_neg, smul_neg]
  have hy' (H : t) : ⁅(H : L), (J' ⟨v', hv'⟩ : L)⁆ = -(β H • v') := by
    rw [hE'.lie_apply, hE'.apply_apply, Submodule.coe_neg, smul_neg]
  exact B.exists_int_two_mul_apply_eq_mul_of_lie_eq_smul hBs hBp hB hv0 hx hy
    (lie_mem_of_lie_eq_smul ht hx hy) (fun H ↦ hE'.lie_apply H ⟨v', hv'⟩) hy' hv'0 ha hb

end TauCeti.IsRootPlane
