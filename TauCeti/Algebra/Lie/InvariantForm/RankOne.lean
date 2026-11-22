/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct.LieHom
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Algebra.Lie.MaximalCommuting
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.NormalForm
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# The rank-one subalgebras of a compact Lie algebra

Let `L` be a finite-dimensional real Lie algebra with a symmetric positive definite invariant
bilinear form `B`, the Lie algebra of a compact Lie group for instance, and let `t` be a maximal
commutative subspace of `L`: its elements commute, and every element of `L` commuting with all of
`t` lies in `t`. A **root pair** of `t` with root `α ∈ t*` is a pair `x, y` that every `H ∈ t`
rotates by the angle `α(H)`:

`⁅H, x⁆ = α(H) y`,  `⁅H, y⁆ = -α(H) x`.

These are the bases `v, J v` of the root planes `TauCeti.IsRootPlane B t α E J`. This file shows
that a root pair with `α ≠ 0` and `x ≠ 0` spans, together with `Z = ⁅x, y⁆`, a copy of `so(3)`,
the Lie algebra of `SO(3)` and of `SU(2)`:

* `Z` commutes with `t` (`TauCeti.lie_lie_eq_zero_of_lie_eq_smul`), so it lies in `t`
  (`TauCeti.lie_mem_of_lie_eq_smul`);
* `B(H, Z) = α(H) B(y, y)` for `H ∈ t`
  (`LinearMap.BilinForm.lieInvariant.apply_lie_eq_mul_of_lie_eq_smul`), so `Z ≠ 0` and
  `μ = α(Z) = B(Z, Z) / B(y, y) > 0`;
* hence `⁅Z, x⁆ = μ y` and `⁅Z, y⁆ = -μ x`, and `x / √μ, y / √μ, Z / μ` satisfy the cyclic
  relations of the basis `ê₀, ê₁, ê₂` of `so(3)`. They are `B`-orthogonal and nonzero, so the
  resulting homomorphism `so(3) → L` is injective
  (`LinearMap.BilinForm.exists_injective_lieHom_soThree_of_lie_eq_smul`).

The image of `ê₂` is the element `Z / μ` of `t` on which `α` takes the value `1`, so `2ê₂` goes to
the coroot of `α`. The isomorphism `TauCeti.suTwoLieEquivSoThree` sends `-iσ₃/2 ∈ 𝔰𝔲(2)` to `ê₂`,
so these homomorphisms are the rank-one homomorphisms `𝔰𝔲(2) → L` of the roots. For a root plane
this is `TauCeti.IsRootPlane.exists_injective_lieHom_soThree`.

Every maximal commutative subspace of a non-abelian such `L` has a root pair with nonzero root
(`LinearMap.BilinForm.exists_lie_eq_smul_of_not_isLieAbelian`), from the real normal form of
commuting skew-symmetric maps (`TauCeti.exists_orthonormal_apply_eq_smul_of_skew_of_linearMap`),
and maximal commutative subspaces exist (`TauCeti.exists_maximal_commuting_submodule`). So a
non-abelian Lie algebra with a positive definite invariant form, such as the Lie algebra of a
nontrivial compact connected semisimple Lie group, receives an injective homomorphism from
`so(3) ≅ 𝔰𝔲(2)` (`LinearMap.BilinForm.exists_injective_lieHom_soThree`).

## Main results

* `LinearMap.BilinForm.exists_injective_lieHom_soThree_of_lie_eq_smul`: the injective homomorphism
  `so(3) → L` of a root pair, normalized by the root.
* `TauCeti.IsRootPlane.exists_injective_lieHom_soThree`: the same for a root plane.
* `LinearMap.BilinForm.exists_lie_eq_smul_of_not_isLieAbelian`: every maximal commutative subspace
  of a non-abelian finite-dimensional real Lie algebra with a symmetric positive definite
  invariant form has a root pair with nonzero root.
* `LinearMap.BilinForm.exists_injective_lieHom_soThree`: a non-abelian finite-dimensional real Lie
  algebra with a symmetric positive definite invariant form receives an injective homomorphism
  from `so(3)`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, GTM 98, Springer, 1985,
  Chapter V (roots of compact Lie groups and their subgroups `SU(2)` and `SO(3)`).
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, Theorem 12.4 and Proposition 12.5.
-/

public section

open LieAlgebra.Orthogonal Module

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

open TauCeti

/-- The rescaled triple `c x, d y, e ⁅x, y⁆` of a root pair with `α(H₀) ≠ 0` is orthogonal for a
symmetric invariant form. -/
private theorem iIsOrtho_lie_eq_smul {B : LinearMap.BilinForm ℝ L} (hBs : B.IsSymm)
    (hB : B.lieInvariant L) {t : Submodule ℝ L} {α : Dual ℝ t} {H₀ : t} (hH₀ : α H₀ ≠ 0)
    {x y : L} (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y) (c d e : ℝ) :
    B.iIsOrtho ![c • x, d • y, e • ⁅x, y⁆] := by
  -- `B(x, y) = -B(y, x)` by invariance under `H₀`, and `B` is symmetric.
  have hxy : B x y = 0 := by
    have h : α H₀ * B x y = -(α H₀ * B x y) := by simpa [hx, hBs.eq y x] using hB H₀ x x
    exact (mul_eq_zero.mp (by linear_combination h / 2 : α H₀ * B x y = 0)).resolve_left hH₀
  -- `B(⁅x, y⁆, x) = -B(y, ⁅x, x⁆)` and `B(⁅y, x⁆, y) = -B(x, ⁅y, y⁆)` vanish.
  have hZx : B ⁅x, y⁆ x = 0 := by simpa using hB x y x
  have hZy : B ⁅x, y⁆ y = 0 := by
    rw [← lie_skew, map_neg, LinearMap.neg_apply, neg_eq_zero]
    simpa using hB y x y
  rw [iIsOrtho_def]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hxy, hZx, hZy, hBs.eq y x, hBs.eq x ⁅x, y⁆, hBs.eq y ⁅x, y⁆] at hij ⊢

/-- For a root pair `x ≠ 0, y` with `α(H₀) ≠ 0` and a positive definite invariant form, `y` and
`⁅x, y⁆` are nonzero and `α(⁅x, y⁆) > 0`, since `B(⁅x, y⁆, ⁅x, y⁆) = α(⁅x, y⁆) B(y, y)`. -/
private theorem pos_apply_lie_of_lie_eq_smul {B : LinearMap.BilinForm ℝ L}
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L) {t : Submodule ℝ L}
    (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t) {α : Dual ℝ t} {H₀ : t} (hH₀ : α H₀ ≠ 0)
    {x y : L} (hx0 : x ≠ 0) (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y)
    (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x)) :
    y ≠ 0 ∧ ⁅x, y⁆ ≠ 0 ∧ 0 < α ⟨⁅x, y⁆, lie_mem_of_lie_eq_smul ht hx hy⟩ := by
  have hpos (v : L) (hv : v ≠ 0) : 0 < B v v := by simpa using hBp v hv
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h := hy H₀
    rw [lie_zero, eq_comm, neg_eq_zero, smul_eq_zero] at h
    exact h.elim hH₀ hx0
  have hBZ := hB.apply_lie_eq_mul_of_lie_eq_smul hx
  have hZ0 : ⁅x, y⁆ ≠ 0 := by
    intro h
    have h₀ := hBZ H₀
    rw [h, map_zero, eq_comm] at h₀
    exact (mul_ne_zero hH₀ (hpos y hy0).ne') h₀
  exact ⟨hy0, hZ0, (pos_iff_pos_of_mul_pos (hBZ _ ▸ hpos _ hZ0)).mpr (hpos y hy0)⟩

/-- **The rank-one subalgebra of a root pair.** Let `B` be a symmetric positive definite invariant
form on a real Lie algebra `L`, let `t` be a subspace containing every element that commutes with
it, and let `x ≠ 0, y` be a root pair of `t` with nonzero root `α`: `⁅H, x⁆ = α(H) y` and
`⁅H, y⁆ = -α(H) x` for `H ∈ t`. Then there is an injective Lie algebra homomorphism
`f : so(3) → L` sending the basis elements `ê₀, ê₁` to the same positive multiple of `x` and `y`,
and `ê₂ = ⁅ê₀, ê₁⁆`, hence a positive multiple of `⁅x, y⁆`, to the element of `t` on which `α`
takes the value `1`. -/
theorem exists_injective_lieHom_soThree_of_lie_eq_smul (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L) {t : Submodule ℝ L}
    (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t) {α : Dual ℝ t} (hα : α ≠ 0) {x y : L}
    (hx0 : x ≠ 0) (hx : ∀ H : t, ⁅(H : L), x⁆ = α H • y)
    (hy : ∀ H : t, ⁅(H : L), y⁆ = -(α H • x)) :
    ∃ f : so (Fin 3) ℝ →ₗ⁅ℝ⁆ L, Function.Injective f ∧
      (∃ c : ℝ, 0 < c ∧ f (soThreeEquiv ℝ (Pi.single 0 1)) = c • x ∧
        f (soThreeEquiv ℝ (Pi.single 1 1)) = c • y) ∧
      ∃ h : f (soThreeEquiv ℝ (Pi.single 2 1)) ∈ t, α ⟨_, h⟩ = 1 := by
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, α H₀ ≠ 0 := by simpa using DFunLike.ne_iff.mp hα
  obtain ⟨hy0, hZ0, hμpos⟩ := pos_apply_lie_of_lie_eq_smul hBp hB ht hH₀ hx0 hx hy
  set Z := ⁅x, y⁆ with hZ
  have hZt : Z ∈ t := lie_mem_of_lie_eq_smul ht hx hy
  set μ := α ⟨Z, hZt⟩ with hμ
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ s * s = μ :=
    ⟨√μ, Real.sqrt_pos.mpr hμpos, Real.mul_self_sqrt hμpos.le⟩
  have hZx : ⁅Z, x⁆ = μ • y := hx ⟨Z, hZt⟩
  have hyZ : ⁅y, Z⁆ = μ • x := by rw [← lie_skew, hy ⟨Z, hZt⟩, neg_neg]
  -- The normalized triple satisfies the cyclic relations of `so(3)`.
  set a : Fin 3 → L := ![s⁻¹ • x, s⁻¹ • y, μ⁻¹ • Z] with ha
  obtain ⟨ha₀, ha₁, ha₂⟩ : a 0 = s⁻¹ • x ∧ a 1 = s⁻¹ • y ∧ a 2 = μ⁻¹ • Z := by simp [ha]
  have h₀ : ⁅a 0, a 1⁆ = a 2 := by
    simp only [ha₀, ha₁, ha₂, smul_lie, lie_smul, smul_smul, ← hZ, ← hs, mul_inv]
  have h₁ : ⁅a 1, a 2⁆ = a 0 := by
    simp only [ha₀, ha₁, ha₂, smul_lie, lie_smul, smul_smul, hyZ]
    congr 1
    field_simp
  have h₂ : ⁅a 2, a 0⁆ = a 1 := by
    simp only [ha₀, ha₁, ha₂, smul_lie, lie_smul, smul_smul, hZx]
    congr 1
    field_simp
  refine ⟨soThreeLieHom a h₀ h₁ h₂, injective_soThreeLieHom_iff.mpr ?_,
    ⟨s⁻¹, inv_pos.mpr hs0, soThreeLieHom_soThreeEquiv_single 0,
      soThreeLieHom_soThreeEquiv_single 1⟩, ?_⟩
  · refine linearIndependent_of_iIsOrtho (iIsOrtho_lie_eq_smul hBs hB hH₀ hx _ _ _) fun i ↦ ?_
    have hi : a i ≠ 0 := by fin_cases i <;> simp [ha, hx0, hy0, hZ0, hs0.ne', hμpos.ne']
    simpa using (hBp _ hi).ne'
  · rw [soThreeLieHom_soThreeEquiv_single, ha₂]
    have hsmul : (⟨μ⁻¹ • Z, t.smul_mem _ hZt⟩ : t) = μ⁻¹ • ⟨Z, hZt⟩ :=
      Subtype.ext (by simp)
    refine ⟨t.smul_mem _ hZt, ?_⟩
    rw [hsmul, map_smul, smul_eq_mul, ← hμ, inv_mul_cancel₀ hμpos.ne']

/-- A maximal commutative subspace `t` of a non-abelian finite-dimensional real Lie algebra with a
symmetric positive definite invariant form has a root pair with nonzero root. -/
theorem exists_lie_eq_smul_of_not_isLieAbelian [FiniteDimensional ℝ L]
    (B : LinearMap.BilinForm ℝ L) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant L) {t : Submodule ℝ L} (htc : ∀ a ∈ t, ∀ b ∈ t, ⁅a, b⁆ = 0)
    (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t) (hL : ¬IsLieAbelian L) :
    ∃ α : Dual ℝ t, α ≠ 0 ∧ ∃ x y : L, x ≠ 0 ∧ (∀ H : t, ⁅(H : L), x⁆ = α H • y) ∧
      ∀ H : t, ⁅(H : L), y⁆ = -(α H • x) := by
  -- Read `ad` on `t` in a Euclidean model of `(L, B)`: commuting skew-symmetric maps.
  obtain ⟨e, he⟩ := exists_linearEquiv_euclideanSpace_apply_apply hBs fun v hv ↦ by
    simpa using hBp v hv
  let ρ : t →ₗ[ℝ] Module.End ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) :=
    { toFun H := e.symm.conj (LieAlgebra.ad ℝ L H)
      map_add' H H' := by simp only [Submodule.coe_add, map_add]
      map_smul' c H := by simp only [Submodule.coe_smul, map_smul, RingHom.id_apply] }
  have hρ (H : t) (v) : e (ρ H v) = ⁅(H : L), e v⁆ := by simp [ρ]
  obtain ⟨r, q, p, α, hon, hact, hne, hker⟩ :=
    exists_orthonormal_apply_eq_smul_of_skew_of_linearMap ρ
      (fun H v w ↦ by rw [← he, ← he, hρ, hρ]; exact hB _ _ _)
      (fun H H' ↦ (commute_iff_eq _ _).mpr <| LinearMap.ext fun v ↦ e.injective <| by
        simp only [Module.End.mul_eq_comp, LinearMap.comp_apply, hρ]
        rw [leibniz_lie (H : L), htc _ H.property _ H'.property, zero_lie, zero_add])
  -- Some plane occurs: otherwise every `ad H` vanishes, so `L = t` is abelian.
  obtain ⟨k⟩ : Nonempty (Fin r) := by
    by_contra hr
    have : IsEmpty (Fin r) := not_nonempty_iff.mp hr
    have hall (z : L) : z ∈ t := ht z fun H ↦ by
      have hz : e.symm z ∈ ⨅ H, LinearMap.ker (ρ H) := by
        rw [← hker, Set.range_eq_empty, Submodule.span_empty, Submodule.bot_orthogonal_eq_top]
        trivial
      have h := congrArg e (LinearMap.mem_ker.mp (Submodule.mem_iInf _ |>.mp hz H))
      rwa [hρ, LinearEquiv.apply_symm_apply, map_zero] at h
    exact hL ⟨fun z w ↦ htc z (hall z) w (hall w)⟩
  refine ⟨α k, hne k, e (q k), e (p k), e.map_ne_zero_iff.mpr (hon.ne_zero (.inl k)),
    fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [← hρ, (hact k H).1, map_smul]
  · rw [← hρ, (hact k H).2, map_smul, neg_smul]

/-- **A non-abelian compact Lie algebra contains `so(3) ≅ 𝔰𝔲(2)`.** A finite-dimensional real Lie
algebra with a symmetric positive definite invariant form which is not abelian receives an
injective Lie algebra homomorphism from `so(3)`. -/
theorem exists_injective_lieHom_soThree [FiniteDimensional ℝ L] (B : LinearMap.BilinForm ℝ L)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L)
    (hL : ¬IsLieAbelian L) : ∃ f : so (Fin 3) ℝ →ₗ⁅ℝ⁆ L, Function.Injective f := by
  obtain ⟨t, htc, ht⟩ := exists_maximal_commuting_submodule (R := ℝ) (L := L)
  obtain ⟨α, hα, x, y, hx0, hx, hy⟩ :=
    B.exists_lie_eq_smul_of_not_isLieAbelian hBs hBp hB htc ht hL
  obtain ⟨f, hf, -⟩ := B.exists_injective_lieHom_soThree_of_lie_eq_smul hBs hBp hB ht hα hx0 hx hy
  exact ⟨f, hf⟩

end LinearMap.BilinForm

namespace TauCeti.IsRootPlane

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {B : LinearMap.BilinForm ℝ L}
  {t : Submodule ℝ L} {α : Dual ℝ t} {E : Submodule ℝ L} {J : Module.End ℝ E}

/-- **The rank-one subalgebra of a root plane.** For a symmetric positive definite invariant form
`B` and a subspace `t` containing every element that commutes with it, a root plane `E` of `t`
with nonzero root `α` and rotation `J` spans, with its brackets, a copy of `so(3)`: for every
`v ≠ 0` in `E` there is an injective Lie algebra homomorphism `f : so(3) → L` sending `ê₀, ê₁` to
the same positive multiple of `v` and `J v`, and `ê₂` to the element of `t` on which `α` takes the
value `1`. -/
theorem exists_injective_lieHom_soThree (h : IsRootPlane B t α E J) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant L)
    (ht : ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t) (hα : α ≠ 0) {v : E} (hv : v ≠ 0) :
    ∃ f : so (Fin 3) ℝ →ₗ⁅ℝ⁆ L, Function.Injective f ∧
      (∃ c : ℝ, 0 < c ∧ f (soThreeEquiv ℝ (Pi.single 0 1)) = c • (v : L) ∧
        f (soThreeEquiv ℝ (Pi.single 1 1)) = c • (J v : L)) ∧
      ∃ h : f (soThreeEquiv ℝ (Pi.single 2 1)) ∈ t, α ⟨_, h⟩ = 1 :=
  B.exists_injective_lieHom_soThree_of_lie_eq_smul hBs hBp hB ht hα (fun h' ↦ hv (Subtype.ext h'))
    (fun H ↦ h.lie_apply H v) fun H ↦ by
      rw [h.lie_apply, h.apply_apply, Submodule.coe_neg, smul_neg]

end TauCeti.IsRootPlane
