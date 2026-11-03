/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transitivity
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitivity of the symplectic group on projective space

Over every field `K`, the standard symplectic group `Sp_{2m}(K)` (`TauCeti.GLSymplecticFin m K`)
acts primitively on the points of the projective space `ℙ K (Fin (m + m) → K)`: the only blocks
of the action are the subsingletons and the whole space. Together with the Iwasawa structure of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Iwasawa` and the faithful projective
action of `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Projective`, this is the
quasiprimitivity input of Iwasawa's simplicity criterion for the projective symplectic groups.

Write `ω(x, y) = xᵀ J y` for the standard alternating form. In rank at least two the action has
rank three, with orbitals given by `[y] = [x]`, `ω(y, x) = 0` and `ω(y, x) ≠ 0`, so it is not
two-transitive and primitivity needs an argument. Only symplectic transvections
`τ_{u,c} : v ↦ v + c ω(u, v) u` are used, so the proof covers every field, including `𝔽₂` and
`𝔽₃`, and every rank.

* A transvection along a vector `u` with `ω(u, x) = 0` fixes `x`. Products of two such
  transvections fix `x` and act transitively on the vectors `y` with a prescribed nonzero value
  of `ω(y, x)` (`TauCeti.GLSymplecticFin.exists_mulVec_eq_of_dotProduct_JFin_mulVec_eq`).
* Let `B` be a block. If `B` contains two points `[x]`, `[y]` with `ω(y, x) ≠ 0`, then every
  element fixing `[x]` preserves `B`, so `B` contains every point non-orthogonal to `[x]`. Any
  two points have a common non-orthogonal point, so `B` is everything.
* If `B` contains two distinct orthogonal points `[x]`, `[y]`, choose `u` with `ω(u, x) = 0` and
  `ω(u, y) ≠ 0`; it exists because `y` is not a multiple of `x`. The transvection `τ_{u,1}` fixes
  `[x]`, so it preserves `B`, and it moves `y` to a vector `y'` with `ω(y', y) = ω(u, y)² ≠ 0`.
  The previous case applies to `[y]` and `[y']`.

## Main results

* `TauCeti.GLSymplecticFin.exists_dotProduct_JFin_mulVec_eq_zero_and_ne_zero`: if `y` is not a
  multiple of `x`, some `u` is orthogonal to `x` but not to `y`.
* `TauCeti.GLSymplecticFin.exists_mulVec_eq_of_dotProduct_JFin_mulVec_eq`: the vectors `y` with a
  prescribed nonzero pairing with `x` form a single orbit of the symplectic matrices fixing `x`.
* `TauCeti.GLSymplecticFin.instIsPreprimitiveProjectivization`: the symplectic group acts
  primitively on projective space.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, §§4--5, and Chapter IV, §1.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.
-/

public section

open Matrix MulAction
open scoped LinearAlgebra.Projectivization Pointwise

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ} {K : Type u} [Field K]

/-- **A vector orthogonal to `x` but not to `y`.** If `y` is not a multiple of `x`, some `u` has
`ω(u, x) = 0` and `ω(u, y) ≠ 0`: the linear forms `ω(·, x)` and `ω(·, y)` are not proportional. -/
theorem exists_dotProduct_JFin_mulVec_eq_zero_and_ne_zero {x y : Fin (m + m) → K}
    (hy : ∀ c : K, c • x ≠ y) :
    ∃ u, u ⬝ᵥ (JFin m K *ᵥ x) = 0 ∧ u ⬝ᵥ (JFin m K *ᵥ y) ≠ 0 := by
  by_contra! h
  by_cases hx : x = 0
  · subst hx
    apply hy 0
    rw [smul_zero]
    exact (eq_zero_of_forall_dotProduct_JFin_mulVec_eq_zero fun w ↦ h w (by simp)).symm
  obtain ⟨z, hz⟩ := exists_dotProduct_JFin_mulVec_ne_zero hx
  set c := (z ⬝ᵥ (JFin m K *ᵥ y)) / (z ⬝ᵥ (JFin m K *ᵥ x))
  refine hy c (sub_eq_zero.mp (eq_zero_of_forall_dotProduct_JFin_mulVec_eq_zero fun w ↦ ?_)).symm
  -- The vector `ω(z, x) w - ω(w, x) z` is orthogonal to `x`, hence to `y`.
  have hw := h ((z ⬝ᵥ (JFin m K *ᵥ x)) • w - (w ⬝ᵥ (JFin m K *ᵥ x)) • z) (by
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    ring)
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul] at hw
  simp only [c, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  field_simp
  linear_combination hw

/-- If `ω(z, x) = ω(y, x)` and `ω(z, y) ≠ 0`, one transvection fixes `x` and sends `y` to `z`. -/
private theorem exists_mulVec_eq_of_dotProduct_JFin_mulVec_ne_zero {x y z : Fin (m + m) → K}
    (hzx : z ⬝ᵥ (JFin m K *ᵥ x) = y ⬝ᵥ (JFin m K *ᵥ x)) (hzy : z ⬝ᵥ (JFin m K *ᵥ y) ≠ 0) :
    ∃ g : GLSymplecticFin m K,
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = x ∧
        ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ y = z := by
  refine ⟨symplecticTransvection (z - y) (z ⬝ᵥ (JFin m K *ᵥ y))⁻¹, ?_,
    coe_symplecticTransvection_sub_mulVec hzy⟩
  rw [coe_symplecticTransvection_mulVec, sub_dotProduct, hzx, sub_self, mul_zero, zero_smul,
    add_zero]

/-- **The stabilizer of a vector is transitive on each level set of its pairing.** If
`ω(y, x) ≠ 0` and `ω(y', x) = ω(y, x)`, some symplectic matrix fixes `x` and sends `y` to `y'`.
The proof uses a product of at most two symplectic transvections. -/
theorem exists_mulVec_eq_of_dotProduct_JFin_mulVec_eq {x y y' : Fin (m + m) → K}
    (hy : y ⬝ᵥ (JFin m K *ᵥ x) ≠ 0) (hy' : y' ⬝ᵥ (JFin m K *ᵥ x) = y ⬝ᵥ (JFin m K *ᵥ x)) :
    ∃ g : GLSymplecticFin m K,
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = x ∧
        ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ y = y' := by
  by_cases hyy' : y' ⬝ᵥ (JFin m K *ᵥ y) ≠ 0
  · exact exists_mulVec_eq_of_dotProduct_JFin_mulVec_ne_zero hy' hyy'
  -- Otherwise pass through `y + x`, which pairs nontrivially with both `y` and `y'`.
  rw [not_not] at hyy'
  have hxy : x ⬝ᵥ (JFin m K *ᵥ y) ≠ 0 := by
    rw [dotProduct_JFin_mulVec_eq_neg]
    exact neg_ne_zero.mpr hy
  obtain ⟨g₁, hg₁x, hg₁y⟩ := exists_mulVec_eq_of_dotProduct_JFin_mulVec_ne_zero
    (z := y + x) (x := x) (y := y)
    (by rw [add_dotProduct, dotProduct_JFin_mulVec_self, add_zero])
    (by rwa [add_dotProduct, dotProduct_JFin_mulVec_self, zero_add])
  obtain ⟨g₂, hg₂x, hg₂y⟩ := exists_mulVec_eq_of_dotProduct_JFin_mulVec_ne_zero
    (z := y') (x := x) (y := y + x)
    (by rw [hy', add_dotProduct, dotProduct_JFin_mulVec_self, add_zero])
    (by rwa [mulVec_add, dotProduct_add, hyy', zero_add, hy'])
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hg₁x, hg₂x]
  · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hg₁y, hg₂y]

/-- A symplectic matrix fixing the projective point of a vector in a block preserves the block. -/
private theorem smul_eq_of_mulVec_eq {B : Set (ℙ K (Fin (m + m) → K))}
    (hB : IsBlock (GLSymplecticFin m K) B) {x : Fin (m + m) → K} (hx : x ≠ 0)
    (hxB : Projectivization.mk K x hx ∈ B) {g : GLSymplecticFin m K}
    (hg : ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = x) :
    g • B = B :=
  hB.smul_eq_of_mem hxB (by rwa [smul_mk_eq_mk_of_mulVec_eq hx hx hg])

/-- A block containing two non-orthogonal points `[x]` and `[y]` contains every point
non-orthogonal to `[x]`. -/
private theorem mk_mem_of_isBlock {B : Set (ℙ K (Fin (m + m) → K))}
    (hB : IsBlock (GLSymplecticFin m K) B) {x y y' : Fin (m + m) → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxB : Projectivization.mk K x hx ∈ B) (hyB : Projectivization.mk K y hy ∈ B)
    (hyx : y ⬝ᵥ (JFin m K *ᵥ x) ≠ 0) (hy'x : y' ⬝ᵥ (JFin m K *ᵥ x) ≠ 0) :
    ∃ hy' : y' ≠ 0, Projectivization.mk K y' hy' ∈ B := by
  have hy'0 : y' ≠ 0 := by
    rintro rfl
    exact hy'x (zero_dotProduct _)
  refine ⟨hy'0, ?_⟩
  -- Rescale `y'` to the level set of `y`, then move `y` there inside the stabilizer of `x`.
  set a := (y ⬝ᵥ (JFin m K *ᵥ x)) / (y' ⬝ᵥ (JFin m K *ᵥ x))
  have ha : a ≠ 0 := div_ne_zero hyx hy'x
  have hay' : a • y' ≠ 0 := smul_ne_zero ha hy'0
  obtain ⟨g, hgx, hgy⟩ := exists_mulVec_eq_of_dotProduct_JFin_mulVec_eq (y' := a • y') hyx
    (by rw [smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hy'x])
  have hmk : Projectivization.mk K y' hy'0 = Projectivization.mk K (a • y') hay' :=
    (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a⁻¹, by rw [smul_smul, inv_mul_cancel₀ ha,
      one_smul]⟩
  rw [hmk, ← smul_mk_eq_mk_of_mulVec_eq hy hay' hgy, ← smul_eq_of_mulVec_eq hB hx hxB hgx]
  exact Set.smul_mem_smul_set hyB

/-- A block containing two non-orthogonal points is the whole projective space. -/
private theorem eq_univ_of_isBlock {B : Set (ℙ K (Fin (m + m) → K))}
    (hB : IsBlock (GLSymplecticFin m K) B) {x y : Fin (m + m) → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxB : Projectivization.mk K x hx ∈ B) (hyB : Projectivization.mk K y hy ∈ B)
    (hyx : y ⬝ᵥ (JFin m K *ᵥ x) ≠ 0) : B = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  induction p using Projectivization.ind with
  | h w hw =>
  -- A common non-orthogonal point `[v]` of `[x]` and `[w]` lies in `B`, and then so does `[w]`.
  obtain ⟨v, hvx, hvw⟩ := exists_dotProduct_JFin_mulVec_ne_zero_pair hx hw
  obtain ⟨hv, hvB⟩ := mk_mem_of_isBlock hB hx hy hxB hyB hyx hvx
  have hxv : x ⬝ᵥ (JFin m K *ᵥ v) ≠ 0 := by
    rw [dotProduct_JFin_mulVec_eq_neg]
    exact neg_ne_zero.mpr hvx
  have hwv : w ⬝ᵥ (JFin m K *ᵥ v) ≠ 0 := by
    rw [dotProduct_JFin_mulVec_eq_neg]
    exact neg_ne_zero.mpr hvw
  exact (mk_mem_of_isBlock hB hv hx hvB hxB hxv hwv).2

/-- **The symplectic group acts primitively on projective space**, over every field and in every
rank: it is transitive on the points of `ℙ K (Fin (m + m) → K)`, and its only blocks are the
subsingletons and the whole space. -/
instance instIsPreprimitiveProjectivization :
    IsPreprimitive (GLSymplecticFin m K) (ℙ K (Fin (m + m) → K)) where
  toIsPretransitive := inferInstance
  isTrivialBlock_of_isBlock {B} hB := by
    rw [IsTrivialBlock, or_iff_not_imp_left, Set.not_subsingleton_iff]
    rintro ⟨p, hp, q, hq, hpq⟩
    induction p using Projectivization.ind with
    | h x hx =>
    induction q using Projectivization.ind with
    | h y hy =>
    by_cases hyx : y ⬝ᵥ (JFin m K *ᵥ x) ≠ 0
    · exact eq_univ_of_isBlock hB hx hy hp hq hyx
    -- Orthogonal points: a transvection fixing `x` moves `y` to a point non-orthogonal to `y`.
    have hxy : ∀ c : K, c • x ≠ y := by
      rintro c rfl
      exact hpq ((Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨c, rfl⟩).symm
    obtain ⟨u, hux, huy⟩ := exists_dotProduct_JFin_mulVec_eq_zero_and_ne_zero hxy
    set g := symplecticTransvection u (1 : K)
    have hgx : ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ x = x := by
      rw [coe_symplecticTransvection_mulVec, hux, mul_zero, zero_smul, add_zero]
    set y' := ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *ᵥ y
    have hy'y : y' ⬝ᵥ (JFin m K *ᵥ y) ≠ 0 := by
      simp only [y', g, coe_symplecticTransvection_mulVec, one_mul, add_dotProduct,
        dotProduct_JFin_mulVec_self, smul_dotProduct, smul_eq_mul, zero_add]
      exact mul_ne_zero huy huy
    have hy' : y' ≠ 0 := by
      rintro h
      exact hy'y (by rw [h, zero_dotProduct])
    have hy'B : Projectivization.mk K y' hy' ∈ B := by
      rw [← smul_mk_eq_mk_of_mulVec_eq hy hy' rfl, ← smul_eq_of_mulVec_eq hB hx hp hgx]
      exact Set.smul_mem_smul_set hq
    exact eq_univ_of_isBlock hB hy hy' hq hy'B hy'y

end TauCeti.GLSymplecticFin
