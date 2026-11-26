/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.RankOne
public import TauCeti.Algebra.Lie.InvariantForm.Exponential

/-!
# Root reflections of a compact Lie algebra

Let `L` be a finite-dimensional real Lie algebra with a symmetric positive definite invariant
bilinear form `B`, the Lie algebra of a compact Lie group for instance, and let `t` be a subspace,
such as a maximal commutative subspace. A **root pair** of `t` with root `α ∈ t*` is a pair `x, y`
that every `H ∈ t` rotates by the angle `α(H)`: `⁅H, x⁆ = α(H) y` and `⁅H, y⁆ = -α(H) x`. These
are the bases `v, J v` of the real root planes `TauCeti.IsRootPlane B t α E J`.

Let `x, y` be a root pair with root `α` whose bracket `Z = ⁅x, y⁆` lies in `t`. When `x ≠ 0` and
`α ≠ 0`, the value `α(Z)` is positive, and `α^∨ = (2 / α(Z)) Z ∈ t` is the **coroot** of `α`: it
satisfies `α(α^∨) = 2`, and it is the coroot `2 a / B(a, a)` of
`TauCeti.Algebra.Lie.InvariantForm.CartanInteger`, for the vector `a ∈ t` representing `α`
through `B`. This file proves that the **root reflection**

`s_α(H) = H - α(H) α^∨`

of `t` is the restriction of a Lie algebra automorphism `θ` of `L` preserving `B`
(`LinearMap.BilinForm.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul`). Consequently the real
roots are **closed under the root reflections**: `θ` carries a root pair `u ≠ 0, w` with root `β`
to a root pair with root

`s_α(β) = β ∘ s_α = β - ⟨β, α^∨⟩ α`,  `⟨β, α^∨⟩ = 2 β(Z) / α(Z)`

(`LinearMap.BilinForm.exists_ne_zero_lie_eq_sub_smul_of_lie_eq_smul`), and a nonzero root plane with
root `β` to a nonzero root plane with root `s_α(β)`
(`TauCeti.IsRootPlane.exists_isRootPlane_sub_smul`). The Cartan integer `⟨β, α^∨⟩` is an integer by
`LinearMap.BilinForm.exists_int_two_mul_root_apply_lie_eq_mul_of_lie_eq_smul`.

The automorphism `θ` is the inner automorphism `exp (π ad X)` for a multiple `X = c • x` of `x`:
the statement records that the matrix of `θ` in every basis of `L` is the matrix exponential of `π`
times the matrix of `ad X`. Here `X` lies in the rank-one subalgebra of the root pair
(`LinearMap.BilinForm.exists_soThree_triple_of_lie_eq_smul`). With
`X = x / √α(Z)`, `Y = y / √α(Z)` and `K = Z / α(Z)`, the elements `X, Y, K` satisfy the bracket
relations of the standard basis of `so(3)`, so `ad X` rotates the plane of `K` and `Y`, and the
rotation through the angle `π` sends `K` to `-K`. On the other hand `ad X` kills the kernel of `α`
in `t`, which `θ` therefore fixes. The exponential `exp (π ad X)` preserves the bracket and the
invariant form (`LinearMap.BilinForm.exists_lieEquiv_apply_eq_cos_smul_add_sin_smul`). This is the
Lie-algebra form of the Weyl group element `exp (π X)` of the subgroup `SU(2)` or `SO(3)` attached
to the root.

## Main results

* `LinearMap.BilinForm.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul`: the root reflection
  `H ↦ H - α(H) α^∨` of `t` extends to the Lie algebra automorphism `exp (π ad X)` of `L`, for a
  multiple `X` of `x`, and it preserves `B`.
* `LinearMap.BilinForm.exists_ne_zero_lie_eq_sub_smul_of_lie_eq_smul`: the real roots are closed
  under the root reflections.
* `TauCeti.IsRootPlane.exists_isRootPlane_sub_smul`: the reflection of the root of a nonzero root
  plane is the root of a nonzero root plane.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, §2 (the roots of a compact Lie group form a root
  system, with the reflections realized by the subgroups `SU(2)` and `SO(3)` of the roots).
-/

public section

open Module

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {t : Submodule ℝ L} {α β : Dual ℝ t} {x y u w : L}

open TauCeti

omit [FiniteDimensional ℝ L] in
/-- If a Lie algebra automorphism `θ` acts on `t` as the reflection
`H ↦ H - (2 α(H) / α(Z)) Z` for some `Z ∈ t`, then every `H ∈ t` is the image `θ (s H)` of an
element `s H ∈ t`, on which each `γ ∈ t*` takes the value `(γ - (2 γ(Z) / α(Z)) α)(H)`. -/
private theorem exists_apply_eq_of_apply_eq_sub_smul {θ : L ≃ₗ⁅ℝ⁆ L} {Z : t}
    (hθ : ∀ H : t, θ H = (H : L) - (2 * α H / α Z) • (Z : L)) :
    ∃ s : t → t, (∀ H, θ (s H) = H) ∧
      ∀ (γ : Dual ℝ t) H, γ (s H) = (γ - (2 * γ Z / α Z) • α) H := by
  refine ⟨fun H ↦ H - (2 * α H / α Z) • Z, fun H ↦ ?_, fun γ H ↦ ?_⟩
  · rw [hθ]
    rcases eq_or_ne (α Z) 0 with hZ | hZ
    · simp [hZ]
    -- `α` takes the value `-α(H)` on the reflection of `H`.
    have h : 2 * α (H - (2 * α H / α Z) • Z) / α Z = -(2 * α H / α Z) := by
      rw [map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    simp only [h, neg_smul, sub_neg_eq_add, Submodule.coe_sub, Submodule.coe_smul]
    abel
  · simp only [map_sub, map_smul, smul_eq_mul, LinearMap.sub_apply, LinearMap.smul_apply]
    ring

/-- **The root reflections extend to automorphisms.** Let `B` be a symmetric positive definite
invariant form on a finite-dimensional real Lie algebra `L` and `t` a subspace. Let `x, y` be a root
pair of `t` with root `α`, `⁅H, x⁆ = α(H) y` and `⁅H, y⁆ = -α(H) x` for `H ∈ t`, whose bracket
`Z = ⁅x, y⁆` lies in `t`. Then there is a Lie algebra automorphism `θ` of `L` preserving `B` which
acts on `t` as the root reflection `H ↦ H - α(H) α^∨`, with coroot `α^∨ = (2 / α(Z)) Z`. It is
`exp (π ad X)` for a multiple `X = c • x` of `x`: its matrix in every basis `b`, indexed by a finite
type in `Type`, is the matrix exponential of `π` times the matrix of `ad X`. When `α(Z) = 0`, which
happens only when `x = 0` or `α = 0`, the reflection is the identity, with `c = 0`. -/
theorem exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x))
    (hxy : ⁅x, y⁆ ∈ t) :
    ∃ (c : ℝ) (θ : L ≃ₗ⁅ℝ⁆ L),
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ L),
        LinearMap.toMatrix b b θ.toLinearEquiv =
          NormedSpace.exp (Real.pi • LinearMap.toMatrix b b (LieAlgebra.ad ℝ L (c • x)))) ∧
      (∀ v w, B (θ v) (θ w) = B v w) ∧
      ∀ H : t, θ H = (H : L) - (2 * α H / α ⟨⁅x, y⁆, hxy⟩) • ⁅x, y⁆ := by
  set Z : t := ⟨⁅x, y⁆, hxy⟩
  -- In the degenerate cases the identity `exp (π ad 0)` works.
  have hrefl {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ L) :
      LinearMap.toMatrix b b (LieEquiv.refl : L ≃ₗ⁅ℝ⁆ L).toLinearEquiv =
        NormedSpace.exp (Real.pi • LinearMap.toMatrix b b (LieAlgebra.ad ℝ L ((0 : ℝ) • x))) := by
    simp only [zero_smul, map_zero, smul_zero, NormedSpace.exp_zero]
    rw [show ((LieEquiv.refl : L ≃ₗ⁅ℝ⁆ L).toLinearEquiv : L →ₗ[ℝ] L) = LinearMap.id from
      LinearMap.ext LieEquiv.refl_apply]
    exact LinearMap.toMatrix_id b
  by_cases hα : α = 0
  · exact ⟨0, LieEquiv.refl, fun b ↦ hrefl b, fun _ _ ↦ rfl, fun H ↦ by simp [hα]⟩
  by_cases hx0 : x = 0
  · exact ⟨0, LieEquiv.refl, fun b ↦ hrefl b, fun _ _ ↦ rfl, fun H ↦ by simp [hx0]⟩
  -- The rank-one subalgebra of `x, y`: its third basis vector is `K = c² ⁅x, y⁆`, with
  -- `α(K) = c² α(⁅x, y⁆) = 1`.
  obtain ⟨a, c, -, h₀, -, h₂, hf₀, hf₁, hKZ, hcZ⟩ :=
    B.exists_soThree_triple_of_lie_eq_smul hBs hBp hB hα hx0 hx hy hxy
  -- `θ = exp (π ad X)` for `X = a 0 = c • x`.
  obtain ⟨θ, hθexp, hθB, hθ0, hθrot⟩ :=
    B.exists_lieEquiv_apply_eq_cos_smul_add_sin_smul hB (a 0) Real.pi
  refine ⟨c, θ, fun b ↦ hf₀ ▸ hθexp b, hθB, fun H ↦ ?_⟩
  -- `ad X` kills `H - α(H) K` and rotates the plane of `K` and `Y = a 1`.
  have hHX : ⁅(H : L), a 0⁆ = α H • a 1 := by
    simp only [hf₀, hf₁, lie_smul, hx, smul_comm c]
  have hker : ⁅a 0, (H : L) - α H • a 2⁆ = 0 := by
    rw [lie_sub, lie_smul, ← lie_skew, hHX, ← lie_skew (a 0) (a 2), h₂]
    simp
  have hK' : θ (a 2) = -a 2 := by
    rw [hθrot (a 2) (-a 1) (by rw [← lie_skew, h₂]) (by rw [lie_neg, h₀]), Real.cos_pi,
      Real.sin_pi]
    simp
  have hθH : θ H = (H : L) - (α H + α H) • a 2 := by
    calc θ H = θ (((H : L) - α H • a 2) + α H • a 2) := by rw [sub_add_cancel]
      _ = _ := by rw [map_add, hθ0 _ hker, map_smul, hK']; module
  have hαZ : α Z ≠ 0 := right_ne_zero_of_mul_eq_one hcZ
  rw [hθH, hKZ, smul_smul, eq_div_iff hαZ |>.mpr (by linear_combination (2 * α H) * hcZ :
    (α H + α H) * (c * c) * α Z = 2 * α H)]

/-- **The real roots are closed under the root reflections.** Let `B` be a symmetric positive
definite invariant form on a finite-dimensional real Lie algebra `L` and `t` a subspace. Let `x, y`
be a root pair of `t` with root `α` whose bracket `Z = ⁅x, y⁆` lies in `t`, and let `u ≠ 0, w` be a
root pair with root `β`. Then there is a root pair `u' ≠ 0, w'` with root
`s_α(β) = β - (2 β(Z) / α(Z)) α`, the reflection of `β` in the root `α`. -/
theorem exists_ne_zero_lie_eq_sub_smul_of_lie_eq_smul (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x))
    (hxy : ⁅x, y⁆ ∈ t) (hu : ∀ H : t, ⁅(H : L), u⁆ = β H • w)
    (hw : ∀ H : t, ⁅(H : L), w⁆ = -(β H • u)) (hu0 : u ≠ 0) :
    ∃ u' w' : L, u' ≠ 0 ∧
      (∀ H : t, ⁅(H : L), u'⁆ =
        (β - (2 * β ⟨⁅x, y⁆, hxy⟩ / α ⟨⁅x, y⁆, hxy⟩) • α) H • w') ∧
      ∀ H : t, ⁅(H : L), w'⁆ =
        -((β - (2 * β ⟨⁅x, y⁆, hxy⟩ / α ⟨⁅x, y⁆, hxy⟩) • α) H • u') := by
  obtain ⟨-, θ, -, -, hθ⟩ := B.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul hBs hBp hB hx hy hxy
  obtain ⟨s, hs, hγs⟩ := exists_apply_eq_of_apply_eq_sub_smul hθ
  refine ⟨θ u, θ w, (map_ne_zero_iff θ θ.injective).mpr hu0, fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [← hs H, ← LieEquiv.map_lie, hu, map_smul, hγs]
  · rw [← hs H, ← LieEquiv.map_lie, hw, map_neg, map_smul, hγs]

end LinearMap.BilinForm

namespace TauCeti.IsRootPlane

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {B : LinearMap.BilinForm ℝ L} {t : Submodule ℝ L} {α β : Dual ℝ t} {E E' : Submodule ℝ L}
  {J : Module.End ℝ E} {J' : Module.End ℝ E'}

/-- **Root planes are closed under the root reflections.** Let `B` be a symmetric positive
definite invariant form on a finite-dimensional real Lie algebra `L` and `t` a subspace containing
every element that commutes with it, such as a maximal commutative subspace. Let `E` and `E'` be
nonzero root planes of `t` with roots `α` and `β`, and let `a ∈ t` represent `α` through `B`. Then
there is a nonzero root plane with root `s_α(β) = β - (2 β(a) / α(a)) α`, the reflection of `β` in
the root `α`. -/
theorem exists_isRootPlane_sub_smul (hE : IsRootPlane B t α E J)
    (hE' : IsRootPlane B t β E' J') (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant L) (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t) (hE0 : E ≠ ⊥)
    (hE'0 : E' ≠ ⊥) {a : t} (ha : ∀ H : t, B a H = α H) :
    ∃ (E'' : Submodule ℝ L) (J'' : Module.End ℝ E''),
      IsRootPlane B t (β - (2 * β a / α a) • α) E'' J'' ∧ E'' ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
  set y : L := ↑(J ⟨v, hv⟩) with hy_def
  have hx (H : t) : ⁅(H : L), v⁆ = α H • y := hE.lie_apply H ⟨v, hv⟩
  have hy (H : t) : ⁅(H : L), y⁆ = -(α H • v) := by
    rw [hy_def, hE.lie_apply, hE.apply_apply, Submodule.coe_neg, smul_neg]
  have hxy := lie_mem_of_lie_eq_smul ht hx hy
  obtain ⟨-, θ, -, hθB, hθ⟩ :=
    B.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul hBs hBp hB hx hy hxy
  obtain ⟨s, hs, hγs⟩ := LinearMap.BilinForm.exists_apply_eq_of_apply_eq_sub_smul hθ
  -- The bracket `Z = ⁅v, J v⁆` is `B(J v, J v) • a`.
  have hZa : (⟨⁅v, y⁆, hxy⟩ : t) = B y y • a :=
    Subtype.ext (hB.lie_eq_smul_of_lie_eq_smul hBs hBp hx hxy ha)
  have hyy : B y y ≠ 0 := by
    have hy0 : y ≠ 0 := fun h ↦ hv0 (congrArg Subtype.val
      (hE.injective ((Subtype.ext h : J ⟨v, hv⟩ = 0).trans (map_zero J).symm)))
    exact (by simpa using hBp y hy0 : 0 < B y y).ne'
  have hratio : 2 * β ⟨⁅v, y⁆, hxy⟩ / α ⟨⁅v, y⁆, hxy⟩ = 2 * β a / α a := by
    rw [hZa]
    simp only [map_smul, smul_eq_mul]
    field_simp
  -- The image of `E'` under `θ`, with the conjugated complex structure.
  let e : E' ≃ₗ[ℝ] E'.map (θ.toLinearEquiv : L →ₗ[ℝ] L) := θ.toLinearEquiv.submoduleMap E'
  have he (z : E') : (e z : L) = θ z := θ.toLinearEquiv.submoduleMap_apply E' z
  have he' (z : E'.map (θ.toLinearEquiv : L →ₗ[ℝ] L)) : θ (e.symm z) = z := by
    rw [← he, LinearEquiv.apply_symm_apply]
  refine ⟨_, e.conj J', ⟨fun z ↦ ?_, fun z z' ↦ ?_, fun H z ↦ ?_⟩, ?_⟩
  · simp [LinearEquiv.conj_apply, hE'.apply_apply]
  · simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
    rw [← he' z, ← he' z', hθB, hθB]
    exact hE'.apply_left _ _
  · simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
    rw [← he' z, ← hs H, ← LieEquiv.map_lie, hE'.lie_apply, map_smul, hγs, hratio]
  · obtain ⟨v', hv', hv'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE'0
    refine Submodule.ne_bot_iff _ |>.mpr ⟨θ v', Submodule.mem_map_of_mem hv', ?_⟩
    exact (map_ne_zero_iff θ θ.injective).mpr hv'0

end TauCeti.IsRootPlane
