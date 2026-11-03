/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Injectivity
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Line
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Line
import TauCeti.Analysis.Normed.Field.ZPowers
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# The Tate uniformisation is a group homomorphism

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. This file proves
that the Tate uniformisation `Kˣ / q^ℤ → E_q(K)` sends products of parameters to sums of points
(`TauCeti.tateUniformization_mul`), and bundles it as an injective homomorphism out of
`Additive (Kˣ / q^ℤ)`. The same holds over every complete normed extension `L` of `K`, for the
map `Lˣ / q^ℤ → E_q(L)`.

Let `P` denote the uniformisation. For classes `x, y` such that `x`, `y` and `(x y)⁻¹` are
pairwise distinct and different from `1`, there is a line `Y = μ X + ν` through `P x`, `P y` and
`P (x y)⁻¹` (`TauCeti.exists_tateQuotientCoordinates_snd_eq_iff`), and the three points have
pairwise distinct first coordinates (`TauCeti.tateQuotientCoordinates_fst_eq_iff`). So the three
points sum to zero (`WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero`), and
`P (x y) = P x + P y` since `P` respects inversion.

The remaining pairs, including the tangent case `x = y`, follow by comparison with a third
parameter `z` in general position: `P (x y) + P z = P (x z) + P y = P x + P z + P y`. Such a `z`
exists because the classes of the units `1 - qⁿ⁺¹` of norm one are pairwise distinct, and each
class is the square of at most two of them. Neither a discrete value group nor any restriction
on the characteristic is needed.

## Main results

* `TauCeti.tateUniformization_mul`: the Tate uniformisation is additive.
* `TauCeti.tateUniformizationHom`: the injective homomorphism `Additive (Kˣ / q^ℤ) →+ E_q(K)`.
* `TauCeti.tateUniformizationBaseChange_mul`, `TauCeti.tateUniformizationBaseChangeHom`: the
  same over a complete normed extension `L`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The secant case.** If `x`, `y` and `(x y)⁻¹` are pairwise distinct and different from `1`,
then `P (x y) = P x + P y`: the third point of the line through `P x` and `P y` is
`P (x y)⁻¹`. -/
private theorem tateUniformization_mul_of_ne [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x y : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x * y ≠ 1)
    (hne : x ≠ y) (hx' : x * (x * y) ≠ 1) (hy' : y * (x * y) ≠ 1) :
    tateUniformization q hq (x * y) = tateUniformization q hq x + tateUniformization q hq y := by
  have hw : (x * y)⁻¹ ≠ 1 := inv_ne_one.mpr hxy
  obtain ⟨μ, ν, hline⟩ := exists_tateQuotientCoordinates_snd_eq_iff q hq hx hy hxy
  have d₁₂ : (tateQuotientCoordinates q x).1 ≠ (tateQuotientCoordinates q y).1 := by
    rw [Ne, tateQuotientCoordinates_fst_eq_iff q hq hx hy]
    rintro (h | rfl)
    · exact hne h
    · exact hxy (inv_mul_cancel y)
  have d₃₁ : (tateQuotientCoordinates q (x * y)⁻¹).1 ≠ (tateQuotientCoordinates q x).1 := by
    rw [Ne, tateQuotientCoordinates_fst_eq_iff q hq hw hx]
    rintro (h | h)
    · exact hx' (by rw [mul_comm x]; exact inv_eq_iff_mul_eq_one.mp h)
    · have h' : x * y = x := inv_inj.mp h
      exact hy (by rw [← inv_mul_cancel_left x y, h', inv_mul_cancel])
  have d₃₂ : (tateQuotientCoordinates q (x * y)⁻¹).1 ≠ (tateQuotientCoordinates q y).1 := by
    rw [Ne, tateQuotientCoordinates_fst_eq_iff q hq hw hy]
    rintro (h | h)
    · exact hy' (by rw [mul_comm y]; exact inv_eq_iff_mul_eq_one.mp h)
    · have h' : x * y = y := inv_inj.mp h
      exact hx (by rw [← mul_inv_cancel_right x y, h', mul_inv_cancel])
  -- the images of `x`, `y` and `(x y)⁻¹` lie on the line and sum to zero
  rw [← inv_inv (x * y), tateUniformization_inv]
  refine (eq_neg_of_add_eq_zero_left ?_).symm
  rw [tateUniformization_of_ne_one q hq hx, tateUniformization_of_ne_one q hq hy,
    tateUniformization_of_ne_one q hq hw]
  exact Point.some_add_some_add_some_eq_zero _ _ _ d₁₂ d₃₁.symm d₃₂.symm
    ((hline x hx).mpr (.inl rfl)) ((hline y hy).mpr (.inr (.inl rfl)))
    ((hline _ hw).mpr (.inr (.inr rfl)))

/-- **Additivity from additivity in general position.** A map `f` from a commutative group to an
additive commutative group which preserves the identity and inverses, and which is additive on
pairs `x, y` such that `x`, `y` and `(x y)⁻¹` are pairwise distinct and different from `1`, is
additive, provided finitely many conditions `z ≠ c` and `z² ≠ c` can always be met at once.
Indeed `f (x y) + f z = f (x z) + f y = f x + f z + f y` for `z` in general position. -/
private theorem map_mul_of_forall_ne {G A : Type*} [CommGroup G] [AddCommGroup A] (f : G → A)
    (h₁ : f 1 = 0) (hinv : ∀ x, f x⁻¹ = -f x)
    (hex : ∀ s t : Set G, s.Finite → t.Finite → ∃ z, z ∉ s ∧ z ^ 2 ∉ t)
    (hf : ∀ x y, x ≠ 1 → y ≠ 1 → x * y ≠ 1 → x ≠ y → x * (x * y) ≠ 1 → y * (x * y) ≠ 1 →
      f (x * y) = f x + f y)
    (x y : G) : f (x * y) = f x + f y := by
  by_cases hx : x = 1
  · simp [hx, h₁]
  by_cases hy : y = 1
  · simp [hy, h₁]
  by_cases hxy : x * y = 1
  · rw [hxy, h₁, eq_inv_of_mul_eq_one_right hxy, hinv, add_neg_cancel]
  obtain ⟨z, hz, hz₂⟩ := hex
    {1, x⁻¹, x, (x * x)⁻¹, (x * y)⁻¹, x⁻¹ * y, (x * y * y)⁻¹, x * y, (x * y * (x * y))⁻¹}
    {x⁻¹, (x * x * y)⁻¹, (x * y)⁻¹} (Set.toFinite _) (Set.toFinite _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz hz₂
  obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := hz
  obtain ⟨k₁, k₂, k₃⟩ := hz₂
  have hxz : x * z ≠ 1 := fun h ↦ n₂ (eq_inv_of_mul_eq_one_right h)
  have hxyz : x * y * z ≠ 1 := fun h ↦ n₅ (eq_inv_of_mul_eq_one_right h)
  have e₁ := hf x z hx n₁ hxz (fun h ↦ n₃ h.symm)
    (fun h ↦ n₄ (eq_inv_of_mul_eq_one_right ((mul_assoc x x z).trans h)))
    (fun h ↦ k₁ (eq_inv_of_mul_eq_one_right (by rw [← h, sq]; ac_rfl)))
  have e₂ := hf (x * z) y hxz hy (by rwa [mul_right_comm])
    (fun h ↦ n₆ (by rw [← h, inv_mul_cancel_left]))
    (fun h ↦ k₂ (eq_inv_of_mul_eq_one_right (by rw [← h, sq]; ac_rfl)))
    (fun h ↦ n₇ (eq_inv_of_mul_eq_one_right (by rw [← h]; ac_rfl)))
  have e₃ := hf (x * y) z hxy n₁ hxyz (fun h ↦ n₈ h.symm)
    (fun h ↦ n₉ (eq_inv_of_mul_eq_one_right (by rw [← h]; ac_rfl)))
    (fun h ↦ k₃ (eq_inv_of_mul_eq_one_right (by rw [← h, sq]; ac_rfl)))
  rw [mul_right_comm, e₂, e₁, add_right_comm] at e₃
  exact add_right_cancel e₃.symm

omit [CompleteSpace K] in
/-- Outside finitely many classes, and away from finitely many prescribed squares, there is still
a class of `Kˣ / q^ℤ`. The units `1 - qⁿ⁺¹` have norm one, so distinct ones have distinct classes,
and each class is the square of at most two of them. -/
private theorem exists_notMem_and_sq_notMem (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (s t : Set (Kˣ ⧸ Subgroup.zpowers q)) (hs : s.Finite) (ht : t.Finite) :
    ∃ z, z ∉ s ∧ z ^ 2 ∉ t := by
  have hq₀ : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  have hnorm (n : ℕ) : ‖1 - (q : K) ^ (n + 1)‖ = 1 :=
    norm_one_sub_of_norm_lt_one (by rw [norm_pow]; exact pow_lt_one₀ hq₀.le hq n.succ_ne_zero)
  let F (n : ℕ) : Kˣ := Units.mk0 (1 - (q : K) ^ (n + 1)) (norm_ne_zero_iff.mp (by simp [hnorm]))
  have hF : Function.Injective fun n ↦ (F n : K) := by
    intro m n h
    have h' : ‖(q : K)‖ ^ (m + 1) = ‖(q : K)‖ ^ (n + 1) := by
      simpa [F, ← norm_pow] using congrArg norm (sub_right_injective h)
    simpa using pow_right_injective₀ hq₀ hq.ne h'
  -- classes of units of norm one determine the units
  have hcls {u v : Kˣ} (hu : ‖(u : K)‖ = 1) (hv : ‖(v : K)‖ = 1)
      (huv : (u : Kˣ ⧸ Subgroup.zpowers q) = v) : u = v :=
    eq_of_norm_mem_Ioc_of_quotient_zpowers_eq q hq ⟨hu ▸ hq, hu.le⟩ ⟨hv ▸ hq, hv.le⟩ huv
  have hF₁ (n : ℕ) : ‖((F n : Kˣ) : K)‖ = 1 := hnorm n
  have hsq (n : ℕ) : ‖((F n ^ 2 : Kˣ) : K)‖ = 1 := by simp [hF₁]
  have hfin : ({n | (F n : Kˣ ⧸ Subgroup.zpowers q) ∈ s} ∪
      ⋃ c ∈ t, {n | (F n : Kˣ ⧸ Subgroup.zpowers q) ^ 2 = c}).Finite := by
    refine .union (hs.preimage fun m _ n _ h ↦ hF ?_) ?_
    · exact congrArg Units.val (hcls (hF₁ m) (hF₁ n) h)
    refine ht.biUnion fun c _ ↦ ?_
    by_cases hc : ∃ m, (F m : Kˣ ⧸ Subgroup.zpowers q) ^ 2 = c
    · obtain ⟨m, rfl⟩ := hc
      refine ((Set.toFinite {(F m : K), -(F m : K)}).preimage hF.injOn).subset fun n hn ↦ ?_
      have h := congrArg Units.val (hcls (hsq n) (hsq m) (by simpa using hn))
      simpa [sq_eq_sq_iff_eq_or_eq_neg] using h
    · exact Set.finite_empty.subset fun n hn ↦ hc ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hfin.exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists] at hn
  exact ⟨F n, hn.1, fun h ↦ hn.2 _ h rfl⟩

/-- **The Tate uniformisation is additive.** For a complete non-archimedean normed field `K` and
`q ∈ Kˣ` with `‖q‖ < 1`, the map `Kˣ / q^ℤ → E_q(K)` sends products of parameters to sums of
points. -/
@[simp]
theorem tateUniformization_mul [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x y : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformization q hq (x * y) = tateUniformization q hq x + tateUniformization q hq y :=
  map_mul_of_forall_ne _ (tateUniformization_one q hq) (tateUniformization_inv q hq)
    (exists_notMem_and_sq_notMem q hq) (fun _ _ ↦ tateUniformization_mul_of_ne q hq) x y

/-- **The Tate uniformisation as a group homomorphism** `Kˣ / q^ℤ → E_q(K)`, written additively on
the source. It is injective (`tateUniformizationHom_injective`). -/
noncomputable def tateUniformizationHom [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Additive (Kˣ ⧸ Subgroup.zpowers q) →+ (tateCurveAt q hq).toAffine.Point where
  toFun x := tateUniformization q hq x.toMul
  map_zero' := tateUniformization_one q hq
  map_add' x y := tateUniformization_mul q hq x.toMul y.toMul

@[simp]
theorem tateUniformizationHom_apply [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Additive (Kˣ ⧸ Subgroup.zpowers q)) :
    tateUniformizationHom q hq x = tateUniformization q hq x.toMul :=
  (rfl)

/-- **The Tate uniformisation homomorphism is injective.** -/
theorem tateUniformizationHom_injective [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Injective (tateUniformizationHom q hq) :=
  (tateUniformization_injective q hq).comp Additive.toMul.injective

/-! ### The uniformisation over an extension -/

section Extension

variable (L : Type*) [NormedField L] [NormedAlgebra K L] [CompleteSpace L] [IsUltrametricDist L]
  [DecidableEq L]

/-- **The Tate uniformisation over an extension is additive.** For a complete normed extension `L`
of `K`, the map `Lˣ / q^ℤ → E_q(L)` sends products of parameters to sums of points. -/
@[simp]
theorem tateUniformizationBaseChange_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x y : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateUniformizationBaseChange L q hq (x * y) =
      tateUniformizationBaseChange L q hq x + tateUniformizationBaseChange L q hq y := by
  rw [tateUniformizationBaseChange_def, tateUniformizationBaseChange_def,
    tateUniformizationBaseChange_def, tateUniformization_mul]
  exact map_add (AddEquiv.cast (M := fun W : WeierstrassCurve L ↦ W.toAffine.Point)
    (baseChange_tateCurveAt L q hq).symm) _ _

/-- **The Tate uniformisation over an extension as a group homomorphism** `Lˣ / q^ℤ → E_q(L)`,
written additively on the source. It is injective
(`tateUniformizationBaseChangeHom_injective`). -/
noncomputable def tateUniformizationBaseChangeHom (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Additive (Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) →+
      ((tateCurveAt q hq)⁄L).toAffine.Point where
  toFun x := tateUniformizationBaseChange L q hq x.toMul
  map_zero' := tateUniformizationBaseChange_one L q hq
  map_add' x y := tateUniformizationBaseChange_mul L q hq x.toMul y.toMul

@[simp]
theorem tateUniformizationBaseChangeHom_apply (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Additive (Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q))) :
    tateUniformizationBaseChangeHom L q hq x = tateUniformizationBaseChange L q hq x.toMul :=
  (rfl)

/-- **The Tate uniformisation homomorphism over an extension is injective.** -/
theorem tateUniformizationBaseChangeHom_injective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Injective (tateUniformizationBaseChangeHom L q hq) :=
  (tateUniformizationBaseChange_injective L q hq).comp Additive.toMul.injective

end Extension

end TauCeti

end
