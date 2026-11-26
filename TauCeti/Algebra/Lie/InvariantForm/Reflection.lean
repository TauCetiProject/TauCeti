/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import TauCeti.Analysis.Normed.Operator.Exponential

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

The automorphism is the inner automorphism `θ = exp (π ad X)` for an element `X` of the rank-one
subalgebra of the root pair
(`LinearMap.BilinForm.exists_injective_lieHom_soThree_of_lie_eq_smul`). With `X = x / √α(Z)`,
`Y = y / √α(Z)` and `K = Z / α(Z)`, the elements `X, Y, K` satisfy the bracket relations of the
standard basis of `so(3)`, so `ad X` rotates the plane of `K` and `Y`, and the
rotation through the angle `π` sends `K` to `-K`. On the other hand `ad X` kills the kernel of `α`
in `t`, which `θ` therefore fixes. The exponential of the derivation `ad X` preserves the bracket
and the invariant form (`ContinuousLinearMap.exp_apply_apply_of_leibniz`); it is computed for an
auxiliary norm on `L`, which does not appear in the statements. This is the Lie-algebra form of the
Weyl group element `exp (π X)` of the subgroup `SU(2)` or `SO(3)` attached to the root.

## Main results

* `LinearMap.BilinForm.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul`: the root reflection
  `H ↦ H - α(H) α^∨` of `t` extends to a Lie algebra automorphism of `L` preserving `B`.
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

open LieAlgebra.Orthogonal Module NormedSpace Real

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {t : Submodule ℝ L} {α β : Dual ℝ t} {x y u w : L}

open TauCeti

/-- **The inner automorphism `exp (π ad X)`.** For an element `X` of a finite-dimensional real Lie
algebra `L` and an invariant bilinear form `B`, there is a Lie algebra automorphism `θ` of `L`,
namely `exp (π ad X)` for any norm on `L`, which preserves `B`, fixes every element commuting with
`X`, and sends `p` to `-p` whenever `⁅X, p⁆ = q` and `⁅X, q⁆ = -p`. -/
private theorem exists_lieEquiv_of_lieInvariant (B : LinearMap.BilinForm ℝ L)
    (hB : B.lieInvariant L) (X : L) :
    ∃ θ : L ≃ₗ⁅ℝ⁆ L, (∀ v w, B (θ v) (θ w) = B v w) ∧ (∀ v, ⁅X, v⁆ = 0 → θ v = v) ∧
      ∀ p q : L, ⁅X, p⁆ = q → ⁅X, q⁆ = -p → θ p = -p := by
  -- The exponential is computed for an auxiliary norm on `L`, transported from coordinates.
  let e := (Module.finBasis ℝ L).equivFun
  let _ : NormedAddCommGroup L := NormedAddCommGroup.induced L _ e e.injective
  let _ : NormedSpace ℝ L := NormedSpace.induced ℝ L _ e
  have : CompleteSpace L := FiniteDimensional.completeSpace ℝ L
  let D : L →L[ℝ] L := π • LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L X)
  have hD (v : L) : D v = π • ⁅X, v⁆ := by simp [D]
  -- The bracket and the form, as continuous bilinear maps.
  let br : L →L[ℝ] L →L[ℝ] L := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : Module.End ℝ L ≃ₗ[ℝ] (L →L[ℝ] L)).toLinearMap ∘ₗ
      (LieAlgebra.ad ℝ L : L →ₗ[ℝ] Module.End ℝ L))
  have hbr (v w : L) : br v w = ⁅v, w⁆ := by simp [br]
  let bB : L →L[ℝ] L →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (L →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (L →L[ℝ] ℝ)).toLinearMap ∘ₗ B)
  have hbB (v w : L) : bB v w = B v w := by simp [bB]
  let θ₀ := ContinuousLinearMap.expEquiv D
  have hθ₀ (v : L) : θ₀ v = exp D v := D.expEquiv_apply v
  -- `ad X` is a derivation of the bracket, by the Jacobi identity, so `exp D` preserves it.
  have hlie (v w : L) : θ₀ ⁅v, w⁆ = ⁅θ₀ v, θ₀ w⁆ := by
    have h := ContinuousLinearMap.exp_apply_apply_of_leibniz br (D₁ := D) (D₂ := D) (D₃ := D)
      (fun a b ↦ by rw [hbr, hbr, hbr, hD, hD, hD, leibniz_lie, smul_add, smul_lie, lie_smul]) v w
    rwa [hbr, hbr, ← hθ₀, ← hθ₀, ← hθ₀] at h
  let θ : L ≃ₗ⁅ℝ⁆ L := { θ₀.toLinearEquiv with map_lie' := fun {v w} ↦ hlie v w }
  -- By construction, the underlying map of `θ` is that of `θ₀`.
  have hθ (v : L) : θ v = exp D v := hθ₀ v
  refine ⟨θ, fun v w ↦ ?_, fun v hv ↦ ?_, fun p q hp hq ↦ ?_⟩
  · -- `ad X` is skew for the invariant form, so `exp D` preserves it.
    have h := ContinuousLinearMap.exp_apply_apply_of_leibniz bB (D₁ := D) (D₂ := D) (D₃ := 0)
      (fun a b ↦ by simp [hD, hbB, hB X a b]) v w
    rw [hbB, hbB, NormedSpace.exp_zero, one_apply_eq_self] at h
    rw [hθ, hθ, h]
  · rw [hθ]
    exact ContinuousLinearMap.exp_apply_of_apply_eq_zero (by simp [hD, hv])
  · -- `D` rotates the pair `p, q` at the speed `π`.
    have h := D.exp_apply_eq_cos_smul_add_sin_smul (x := p) (y := q) (a := π) (by rw [hD, hp])
      (by rw [hD, hq, smul_neg])
    rw [hθ, h, Real.cos_pi, Real.sin_pi]
    simp

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
acts on `t` as the root reflection `H ↦ H - α(H) α^∨`, with coroot `α^∨ = (2 / α(Z)) Z`. When
`α(Z) = 0`, which happens only when `x = 0` or `α = 0`, the reflection is the identity. -/
theorem exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L)
    (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x))
    (hxy : ⁅x, y⁆ ∈ t) :
    ∃ θ : L ≃ₗ⁅ℝ⁆ L, (∀ v w, B (θ v) (θ w) = B v w) ∧
      ∀ H : t, θ H = (H : L) - (2 * α H / α ⟨⁅x, y⁆, hxy⟩) • ⁅x, y⁆ := by
  set Z : t := ⟨⁅x, y⁆, hxy⟩
  -- In the degenerate cases the identity works.
  by_cases hα : α = 0
  · exact ⟨LieEquiv.refl, fun _ _ ↦ rfl, fun H ↦ by simp [hα]⟩
  by_cases hx0 : x = 0
  · exact ⟨LieEquiv.refl, fun _ _ ↦ rfl, fun H ↦ by simp [hx0]⟩
  -- The rank-one subalgebra of `x, y`: its third basis vector `K` lies in `t`, with `α(K) = 1`.
  obtain ⟨f, -, ⟨c, -, hf₀, hf₁⟩, hK, hαK⟩ :=
    B.exists_injective_lieHom_soThree_of_lie_eq_smul hBs hBp hB hα hx0 hx hy hxy
  let a : Fin 3 → L := fun i ↦ f (soThreeEquiv ℝ (Pi.single i 1))
  have h₀ : ⁅a 0, a 1⁆ = a 2 := by simp only [a, ← LieHom.map_lie, lie_soThreeEquiv_single_zero_one]
  have h₂ : ⁅a 2, a 0⁆ = a 1 := by simp only [a, ← LieHom.map_lie, lie_soThreeEquiv_single_two_zero]
  -- `K = c² ⁅x, y⁆`, so `α(K) = 1` gives `c² α(⁅x, y⁆) = 1`.
  have hKZ : a 2 = (c * c) • ⁅x, y⁆ := by
    simp only [← h₀, a, hf₀, hf₁, smul_lie, lie_smul, smul_smul]
  have hcZ : c * c * α Z = 1 := by
    rw [← hαK, ← smul_eq_mul, ← map_smul]
    exact congrArg α (Subtype.ext hKZ.symm)
  -- `θ = exp (π ad X)` for `X = a 0`.
  obtain ⟨θ, hθB, hθ0, hθrot⟩ := exists_lieEquiv_of_lieInvariant B hB (a 0)
  refine ⟨θ, hθB, fun H ↦ ?_⟩
  -- `ad X` kills `H - α(H) K` and rotates the plane of `K` and `Y = a 1`.
  have hHX : ⁅(H : L), a 0⁆ = α H • a 1 := by
    simp only [a, hf₀, hf₁, lie_smul, hx, smul_comm c]
  have hker : ⁅a 0, (H : L) - α H • a 2⁆ = 0 := by
    rw [lie_sub, lie_smul, ← lie_skew, hHX, ← lie_skew (a 0) (a 2), h₂]
    simp
  have hK' : θ (a 2) = -a 2 :=
    hθrot (a 2) (-a 1) (by rw [← lie_skew, h₂]) (by rw [lie_neg, h₀])
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
  obtain ⟨θ, -, hθ⟩ := B.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul hBs hBp hB hx hy hxy
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
the root `α`. It is the image of `E'` under a Lie algebra automorphism preserving `B`. -/
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
  obtain ⟨θ, hθB, hθ⟩ := B.exists_lieEquiv_apply_eq_sub_smul_of_lie_eq_smul hBs hBp hB hx hy hxy
  obtain ⟨s, hs, hγs⟩ := LinearMap.BilinForm.exists_apply_eq_of_apply_eq_sub_smul hθ
  -- The bracket `Z = ⁅v, J v⁆` is `B(J v, J v) • a`, since both pair with `H ∈ t` to
  -- `α(H) B(J v, J v)` and `B` is definite on `t`.
  have hZa : (⟨⁅v, y⁆, hxy⟩ : t) = B y y • a := by
    have hd : (⟨⁅v, y⁆, hxy⟩ - B y y • a : t) = 0 := by
      set d : t := ⟨⁅v, y⁆, hxy⟩ - B y y • a
      refine Subtype.ext (hBp.anisotropic _ ?_)
      have h₁ : B d ⁅v, y⁆ = α d * B y y := hB.apply_lie_eq_mul_of_lie_eq_smul hx d
      have h₂ : B d a = α d := by rw [← ha, hBs.eq]
      simp only [LinearMap.BilinMap.toQuadraticMap_apply]
      calc B (d : L) d = B d ⁅v, y⁆ - B y y * B d a := by simp [d, map_sub]
        _ = 0 := by rw [h₁, h₂]; ring
    exact sub_eq_zero.mp hd
  have hyy : B y y ≠ 0 := by
    have hy0 : y ≠ 0 := fun h ↦ hv0 (congrArg Subtype.val
      (hE.injective ((Subtype.ext h : J ⟨v, hv⟩ = 0).trans (map_zero J).symm)))
    exact (by simpa using hBp y hy0 : 0 < B y y).ne'
  have hratio : 2 * β ⟨⁅v, y⁆, hxy⟩ / α ⟨⁅v, y⁆, hxy⟩ = 2 * β a / α a := by
    rw [hZa, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm,
      mul_div_mul_left _ _ hyy]
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
