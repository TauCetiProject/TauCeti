/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Cyclic

import TauCeti.Data.ZMod.BinaryQuadraticForm
import TauCeti.Data.ZMod.BinaryQuadraticForm.PlaneCyclic
import TauCeti.Data.ZMod.Two
import TauCeti.Data.ZMod.UnitSquare
import TauCeti.Data.ZMod.MulCastHom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Relations between dyadic generators

Two copies of the dyadic hyperbolic generator `u^{(2)}(2^k)` are isometric to two copies
of `v^{(2)}(2^k)`. This is a relation among the generators of nondegenerate finite quadratic
modules, with preservation of the quadratic values in the half-norm convention. It allows
pairs of `v`-blocks to be replaced by hyperbolic blocks when comparing orthogonal decompositions.

Multiplying both odd coefficients of a cyclic pair of the same exponent by five also
preserves its isometry class. For coefficients `θ` and `η`, put `r = η/θ` modulo
`2^{k+1}` and choose `a` with `a² + 4r = 5`. The coordinate change
`(x,y) ↦ (ax - 2ry, 2x + ay)` preserves the quadratic forms.

The mixed cyclic and rank-two relations replace a `v` summand by `u` while
multiplying the odd cyclic coefficient by five. A unit square supplies a cyclic
vector of the required norm; its orthogonal complement has hyperbolic binary form.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(b), (c), (e), (f), (k).
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-- Coordinates adapted to an isotropic pair in the sum of two copies of `v`.
The last two input coordinates parametrize its orthogonal complement. -/
private def dyadicSplitCoordinates (k : ℕ) (s : ZMod (2 ^ k)) :
    ((ZMod (2 ^ k) × ZMod (2 ^ k)) × (ZMod (2 ^ k) × ZMod (2 ^ k))) →+
      ((ZMod (2 ^ k) × ZMod (2 ^ k)) × (ZMod (2 ^ k) × ZMod (2 ^ k))) where
  toFun x :=
    let c := (2 + s) * x.2.1 + (1 + 2 * s) * x.2.2
    let l := x.1.1 - x.1.2 + 2 * c
    ((l, x.1.2 - c), (l + x.2.1, s * l + x.2.2))
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- The complement has binary form with coefficients `1 + (2+s)²`,
`1 + 2(2+s)(1+2s)`, and `1 + (1+2s)²`. -/
private theorem dyadicSplitCoordinates_quadratic (k : ℕ) {s : ZMod (2 ^ k)}
    (hs : s ^ 2 + s + 2 = 0)
    (x : (ZMod (2 ^ k) × ZMod (2 ^ k)) × (ZMod (2 ^ k) × ZMod (2 ^ k))) :
    ((dyadicV k).prod (dyadicV k)).quadratic (dyadicSplitCoordinates k s x) =
      ZMod.toRatAddCircle (2 ^ k)
        (x.1.1 * x.1.2 + (1 + (2 + s) ^ 2) * x.2.1 ^ 2 +
          (1 + 2 * (2 + s) * (1 + 2 * s)) * x.2.1 * x.2.2 +
          (1 + (1 + 2 * s) ^ 2) * x.2.2 ^ 2) := by
  dsimp [dyadicSplitCoordinates]
  -- `erw` crosses the bundled generator carrier to its concrete coordinate group.
  erw [QuadraticMap.prod_apply, dyadicV_quadratic, dyadicV_quadratic, ← map_add]
  congr 1
  -- The defect of this coordinate splitting is the norm of the first isotropic vector,
  -- `s²+s+2`, times the square of its coefficient.
  linear_combination
    (x.1.1 - x.1.2 + 2 * ((2 + s) * x.2.1 + (1 + 2 * s) * x.2.2)) ^ 2 * hs

/-- An isometry realizing the relation
`u^{(2)}(2^k) ⊥ u^{(2)}(2^k) ≅ v^{(2)}(2^k) ⊥ v^{(2)}(2^k)`.
At `k = 0` both sides are the trivial quadratic module. -/
noncomputable def dyadicUProdSelfIsometryDyadicVProdSelf (k : ℕ) :
    Isometry ((dyadicU k).prod (dyadicU k)) ((dyadicV k).prod (dyadicV k)) :=
  Classical.choice <| by
    cases k with
    | zero =>
      let : Subsingleton ((dyadicU 0).prod (dyadicU 0)).carrier :=
        inferInstanceAs (Subsingleton ((ZMod 1 × ZMod 1) × (ZMod 1 × ZMod 1)))
      let g : Hom ((dyadicU 0).prod (dyadicU 0)) ((dyadicV 0).prod (dyadicV 0)) :=
        { toLinearMap := LinearMap.id
          map_app' := fun x ↦ by
            have hx : x = 0 := Subsingleton.elim _ _
            simp [hx] }
      exact ⟨g.toIsometry (by exact Function.bijective_id)⟩
    | succ k =>
      -- The even root `s = 2t` makes `(1,0,1,s)` isotropic in `v ⊥ v`.
      obtain ⟨t, ht⟩ := (ZMod.two_mul_sq_add_bijective
        (k := k) (c := 1) isUnit_one).2 (-1)
      have hs : (2 * t) ^ 2 + 2 * t + 2 = 0 := by
        linear_combination 2 * ht
      -- In the complementary plane the second diagonal coefficient is even,
      -- while the middle coefficient is odd, so that plane is hyperbolic too.
      obtain ⟨e₁, e₂, f₁, f₂, h⟩ :=
        ZMod.BinaryQuadraticForm.exists_hyperbolic_of_two_mul
          (1 + 4 * t + 8 * t ^ 2) (1 + (2 + 2 * t) ^ 2)
          (u := 1 + 2 * (2 + 2 * t) * (1 + 4 * t)) (by
            convert ZMod.isUnit_two_mul_add
              (c := (2 + 2 * t) * (1 + 4 * t)) isUnit_one using 1; ring)
      let β : (ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1))) →+
          (ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1))) :=
        ((AddMonoidHom.mulRight e₂).coprod (AddMonoidHom.mulRight f₂)).prod
          ((AddMonoidHom.mulRight e₁).coprod (AddMonoidHom.mulRight f₁))
      have hβ (p : ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1))) :
          β p = (p.1 * e₂ + p.2 * f₂, p.1 * e₁ + p.2 * f₁) := by
        simp [β, AddMonoidHom.coprod_apply, AddMonoidHom.mulRight_apply]
      let Ψ := (dyadicSplitCoordinates (k + 1) (2 * t)).comp
        ((AddMonoidHom.id (ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))).prodMap β)
      let g : Hom ((dyadicU (k + 1)).prod (dyadicU (k + 1)))
          ((dyadicV (k + 1)).prod (dyadicV (k + 1))) :=
        { toLinearMap := Ψ.toIntLinearMap
          map_app' := fun x ↦ by
            simp only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap]
            -- Computing the locally defined composite puts its value in the coordinates
            -- accepted by the splitting equation; no generator construction is unfolded.
            rw [show Ψ x = dyadicSplitCoordinates (k + 1) (2 * t) (x.1, β x.2) from rfl,
              dyadicSplitCoordinates_quadratic _ hs]
            have hsource := (prod_quadratic _ _ x.1 x.2).trans
              ((congrArg₂ (· + ·) (dyadicU_quadratic (k + 1) x.1)
                (dyadicU_quadratic (k + 1) x.2)).trans (map_add _ _ _).symm)
            rw [hsource]
            congr 1
            rw [hβ x.2]
            dsimp only [Prod.fst, Prod.snd]
            linear_combination h x.2.1 x.2.2 }
      have hinj : Function.Injective g := fun x y hxy ↦
        FiniteBilinearModule.Hom.injective g.toFiniteBilinearModule
          ((isNondegenerate_prod _ _).2
            ⟨isNondegenerate_dyadicU _, isNondegenerate_dyadicU _⟩)
          ((Hom.toFiniteBilinearModule_apply g x).trans
            (hxy.trans (Hom.toFiniteBilinearModule_apply g y).symm))
      exact ⟨g.toIsometry ((Nat.bijective_iff_injective_and_card g).2 ⟨hinj, rfl⟩)⟩

private theorem dyadicCyclic_prod_quadratic_intCast (k : ℕ) [NeZero k]
    (θ η x y : ℤ) :
    ((dyadicCyclic k θ).prod (dyadicCyclic k η)).quadratic
        ((x : ZMod (2 ^ k)), (y : ZMod (2 ^ k))) =
      ZMod.toRatAddCircle (2 ^ (k + 1))
        ((θ * x ^ 2 + η * y ^ 2 : ℤ) : ZMod (2 ^ (k + 1))) := by
  rw [ZMod.toRatAddCircle_intCast]
  erw [prod_quadratic, dyadicCyclic_quadratic_intCast, dyadicCyclic_quadratic_intCast]
  rw [← AddCircle.coe_add, ← add_div]
  push_cast
  rfl

private def dyadicPairRotation (k : ℕ) (a r : ℤ) :
    (ZMod (2 ^ k) × ZMod (2 ^ k)) →+ (ZMod (2 ^ k) × ZMod (2 ^ k)) where
  toFun x := ((a : ZMod (2 ^ k)) * x.1 - 2 * (r : ZMod (2 ^ k)) * x.2,
    2 * x.1 + (a : ZMod (2 ^ k)) * x.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

private theorem dyadicPairRotation_quadratic (k : ℕ) [NeZero k] (θ η a b : ℤ)
    (hsq : (a : ZMod (2 ^ (k + 1))) ^ 2 + 4 * b = 5)
    (hcoef : (θ : ZMod (2 ^ (k + 1))) * b = η)
    (x : ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic k (5 * η))).carrier) :
    ((dyadicCyclic k θ).prod (dyadicCyclic k η)).quadratic
        (dyadicPairRotation k a b x) =
      ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic k (5 * η))).quadratic x := by
  rcases x with ⟨x, y⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) y
  have hrot : dyadicPairRotation k a b
      ((m : ZMod (2 ^ k)), (n : ZMod (2 ^ k))) =
    (((a * m - 2 * b * n : ℤ) : ZMod (2 ^ k)),
      ((2 * m + a * n : ℤ) : ZMod (2 ^ k))) := by
    ext <;> dsimp [dyadicPairRotation] <;> push_cast <;> ring
  erw [hrot]
  erw [dyadicCyclic_prod_quadratic_intCast, dyadicCyclic_prod_quadratic_intCast]
  congr 1
  push_cast
  rw [← hcoef]
  linear_combination
    (θ : ZMod (2 ^ (k + 1))) * ((m : ZMod (2 ^ (k + 1))) ^ 2 + b * n ^ 2) * hsq

/-- Simultaneously multiplying two odd cyclic dyadic coefficients by five preserves
their orthogonal sum, as in Nikulin's relation 1.8.2(c). -/
noncomputable def dyadicCyclicProdIsometryFiveMul (k : ℕ) [NeZero k] {θ η : ℤ}
    (hθ : Odd θ) (hη : Odd η) :
    Isometry ((dyadicCyclic k θ).prod (dyadicCyclic k η))
      ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic k (5 * η))) :=
  Classical.choice <| by
    have hunit (s : ℤ) (hs : Odd s) : IsUnit (s : ZMod (2 ^ (k + 1))) := by
      obtain ⟨t, rfl⟩ := hs
      convert ZMod.isUnit_two_mul_add (c := (t : ZMod (2 ^ (k + 1)))) isUnit_one using 1
      push_cast
      ring
    obtain ⟨Θ, hΘ⟩ := hunit θ hθ
    let r : ZMod (2 ^ (k + 1)) := (η : ZMod (2 ^ (k + 1))) * (Θ⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)
    have hr : IsUnit r := (hunit η hη).mul (Units.isUnit Θ⁻¹)
    have hθr : (θ : ZMod (2 ^ (k + 1))) * r = η := by
      dsimp [r]
      rw [← hΘ]
      rw [mul_left_comm, Units.mul_inv, mul_one]
    obtain ⟨u, hu⟩ := ZMod.exists_unit_sq_eq_five_sub_four_mul hr
    let a : ℤ := u.val.val
    let b : ℤ := r.val
    have ha : (a : ZMod (2 ^ (k + 1))) = u.val := by simp [a]
    have hb : (b : ZMod (2 ^ (k + 1))) = r := by simp [b]
    have hsq : (a : ZMod (2 ^ (k + 1))) ^ 2 + 4 * b = 5 := by
      rw [ha, hb, hu]
      ring
    have hcoef : (θ : ZMod (2 ^ (k + 1))) * b = η := by rw [hb]; exact hθr
    let g : Hom ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic k (5 * η)))
        ((dyadicCyclic k θ).prod (dyadicCyclic k η)) :=
      { toLinearMap := (dyadicPairRotation k a b).toIntLinearMap
        map_app' := fun x ↦ by
          simpa only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap] using
            dyadicPairRotation_quadratic k θ η a b hsq hcoef x }
    have hsource : ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic k (5 * η))).IsNondegenerate :=
      (isNondegenerate_prod _ _).mpr
        ⟨(isNondegenerate_dyadicCyclic_iff _ _).mpr ((by decide : Odd (5 : ℤ)).mul hθ),
          (isNondegenerate_dyadicCyclic_iff _ _).mpr ((by decide : Odd (5 : ℤ)).mul hη)⟩
    have hinj : Function.Injective g := fun x y hxy ↦
      FiniteBilinearModule.Hom.injective g.toFiniteBilinearModule hsource
        ((Hom.toFiniteBilinearModule_apply g x).trans
          (hxy.trans (Hom.toFiniteBilinearModule_apply g y).symm))
    exact ⟨(g.toIsometry ((Nat.bijective_iff_injective_and_card g).mpr ⟨hinj, rfl⟩)).symm⟩

private theorem dyadicV_prod_cyclic_succ_quadratic_intCast (k : ℕ) (θ x y z : ℤ) :
    ((dyadicV k).prod (dyadicCyclic (k + 1) θ)).quadratic
        (((x : ZMod (2 ^ k)), (y : ZMod (2 ^ k))), (z : ZMod (2 ^ (k + 1)))) =
      ZMod.toRatAddCircle (2 ^ (k + 2))
        ((4 * (x ^ 2 + x * y + y ^ 2) + θ * z ^ 2 : ℤ) : ZMod (2 ^ (k + 2))) := by
  have hv := ZMod.toRatAddCircle_intCast (2 ^ k) (x ^ 2 + x * y + y ^ 2)
  simp only [Int.cast_add, Int.cast_pow, Int.cast_mul] at hv
  rw [ZMod.toRatAddCircle_intCast]
  erw [prod_quadratic, dyadicV_quadratic, hv, dyadicCyclic_quadratic_intCast]
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  rw [pow_add]
  norm_num
  field_simp
  ring

private theorem dyadicU_prod_cyclic_succ_quadratic_intCast (k : ℕ) (θ x y z : ℤ) :
    ((dyadicU k).prod (dyadicCyclic (k + 1) θ)).quadratic
        (((x : ZMod (2 ^ k)), (y : ZMod (2 ^ k))), (z : ZMod (2 ^ (k + 1)))) =
      ZMod.toRatAddCircle (2 ^ (k + 2))
        ((4 * x * y + θ * z ^ 2 : ℤ) : ZMod (2 ^ (k + 2))) := by
  have hu := ZMod.toRatAddCircle_intCast (2 ^ k) (x * y)
  simp only [Int.cast_mul] at hu
  rw [ZMod.toRatAddCircle_intCast]
  erw [prod_quadratic, dyadicU_quadratic, hu, dyadicCyclic_quadratic_intCast]
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  rw [pow_add]
  norm_num
  field_simp
  ring

private def dyadicPlaneCyclicSuccChange (k : ℕ) (u t a b c d : ℤ) :
    ((ZMod (2 ^ k) × ZMod (2 ^ k)) × ZMod (2 ^ (k + 1))) →+
      ((ZMod (2 ^ k) × ZMod (2 ^ k)) × ZMod (2 ^ (k + 1))) where
  toFun x :=
    (((a : ZMod (2 ^ k)) * x.1.1 + (b : ZMod (2 ^ k)) * x.1.2 +
        ZMod.castHom (pow_dvd_pow 2 (by omega : k ≤ k + 1)) (ZMod (2 ^ k)) x.2,
      (c : ZMod (2 ^ k)) * x.1.1 + (d : ZMod (2 ^ k)) * x.1.2),
      ZMod.mulCastHom 2 (by simp [pow_succ])
        (((-t * (2 * a + c) : ℤ) : ZMod (2 ^ k)) * x.1.1 +
          ((-t * (2 * b + d) : ℤ) : ZMod (2 ^ k)) * x.1.2) +
        (u : ZMod (2 ^ (k + 1))) * x.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add] <;> ring

private theorem dyadicPlaneCyclicSuccChange_intCast (k : ℕ) (u t a b c d m n z : ℤ) :
    dyadicPlaneCyclicSuccChange k u t a b c d
      (((m : ZMod (2 ^ k)), (n : ZMod (2 ^ k))), (z : ZMod (2 ^ (k + 1)))) =
    ((((a * m + b * n + z : ℤ) : ZMod (2 ^ k)),
      ((c * m + d * n : ℤ) : ZMod (2 ^ k))),
      ((-2 * t * (2 * (a * m + b * n) + (c * m + d * n)) + u * z : ℤ) :
        ZMod (2 ^ (k + 1)))) := by
  simp only [dyadicPlaneCyclicSuccChange, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  apply Prod.ext
  · apply Prod.ext
    · rw [map_intCast]
      push_cast
      ring
    · push_cast
      ring
  · -- Combine the reduced linear terms before lifting them by multiplication by two.
    have hlinear : (((-t * (2 * a + c) : ℤ) : ZMod (2 ^ k)) * (m : ZMod (2 ^ k)) +
        ((-t * (2 * b + d) : ℤ) : ZMod (2 ^ k)) * (n : ZMod (2 ^ k))) =
        ((-t * (2 * (a * m + b * n) + (c * m + d * n)) : ℤ) : ZMod (2 ^ k)) := by
      push_cast
      ring
    rw [hlinear, ZMod.mulCastHom_intCast]
    push_cast
    ring

private theorem dyadicPlaneCyclicSuccChange_quadratic (k : ℕ) (θ u t a b c d : ℤ)
    (hroot : (θ : ZMod (2 ^ (k + 2))) * (u : ZMod (2 ^ (k + 2))) ^ 2 + 4 = 5 * θ)
    (hinv : (θ : ZMod (2 ^ (k + 2))) * (u : ZMod (2 ^ (k + 2))) * t = 1)
    (hplane : ∀ m n : ZMod (2 ^ (k + 2)),
      (θ : ZMod (2 ^ (k + 2))) * (-t * (2 * (a * m + b * n) + (c * m + d * n))) ^ 2 +
        (a * m + b * n) ^ 2 + (a * m + b * n) * (c * m + d * n) +
        (c * m + d * n) ^ 2 = m * n)
    (x : ((dyadicU k).prod (dyadicCyclic (k + 1) (5 * θ))).carrier) :
    ((dyadicV k).prod (dyadicCyclic (k + 1) θ)).quadratic
        (dyadicPlaneCyclicSuccChange k u t a b c d x) =
      ((dyadicU k).prod (dyadicCyclic (k + 1) (5 * θ))).quadratic x := by
  rcases x with ⟨⟨m, n⟩, z⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) m
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) n
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ (k + 1)) z
  erw [dyadicPlaneCyclicSuccChange_intCast, dyadicV_prod_cyclic_succ_quadratic_intCast,
    dyadicU_prod_cyclic_succ_quadratic_intCast]
  congr 1
  push_cast
  linear_combination 4 * hplane m n + (z : ZMod (2 ^ (k + 2))) ^ 2 * hroot -
    4 * z * (2 * (a * (m : ZMod (2 ^ (k + 2))) + b * n) + (c * m + d * n)) * hinv

/-- Replacing `v(2^k)` by `u(2^k)` multiplies the odd coefficient of an accompanying
cyclic form of order `2^{k+1}` by five, as in Nikulin's relation 1.8.2(e). -/
noncomputable def dyadicVProdCyclicSuccIsometryUProdFiveMul (k : ℕ) {θ : ℤ} (hθ : Odd θ) :
    Isometry ((dyadicV k).prod (dyadicCyclic (k + 1) θ))
      ((dyadicU k).prod (dyadicCyclic (k + 1) (5 * θ))) :=
  Classical.choice <| by
    obtain ⟨u, t, a, b, c, d, hroot, hinv, hplane⟩ :=
      ZMod.BinaryQuadraticForm.exists_plane_cyclic_coefficients_of_odd (k + 1) hθ
    let ui : ℤ := u.val
    let ti : ℤ := t.val
    let ai : ℤ := a.val
    let bi : ℤ := b.val
    let ci : ℤ := c.val
    let di : ℤ := d.val
    have hroot' : (θ : ZMod (2 ^ (k + 2))) * (ui : ZMod (2 ^ (k + 2))) ^ 2 + 4 = 5 * θ := by
      simpa only [ui, Int.cast_natCast, ZMod.natCast_zmod_val] using hroot
    have hinv' : (θ : ZMod (2 ^ (k + 2))) * (ui : ZMod (2 ^ (k + 2))) * ti = 1 := by
      simpa only [ui, ti, Int.cast_natCast, ZMod.natCast_zmod_val] using hinv
    have hplane' : ∀ m n : ZMod (2 ^ (k + 2)),
        (θ : ZMod (2 ^ (k + 2))) * (-ti * (2 * (ai * m + bi * n) + (ci * m + di * n))) ^ 2 +
          (ai * m + bi * n) ^ 2 + (ai * m + bi * n) * (ci * m + di * n) +
          (ci * m + di * n) ^ 2 = m * n := by
      simpa only [ti, ai, bi, ci, di, Int.cast_natCast, ZMod.natCast_zmod_val] using hplane
    let g : Hom ((dyadicU k).prod (dyadicCyclic (k + 1) (5 * θ)))
        ((dyadicV k).prod (dyadicCyclic (k + 1) θ)) :=
      { toLinearMap := (dyadicPlaneCyclicSuccChange k ui ti ai bi ci di).toIntLinearMap
        map_app' := fun x ↦ by
          simpa only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap] using
            dyadicPlaneCyclicSuccChange_quadratic k θ ui ti ai bi ci di hroot' hinv' hplane' x }
    have hsource : ((dyadicU k).prod (dyadicCyclic (k + 1) (5 * θ))).IsNondegenerate :=
      (isNondegenerate_prod _ _).mpr ⟨isNondegenerate_dyadicU k,
        (isNondegenerate_dyadicCyclic_iff _ _).mpr ((by decide : Odd (5 : ℤ)).mul hθ)⟩
    have hinj : Function.Injective g := fun x y hxy ↦
      FiniteBilinearModule.Hom.injective g.toFiniteBilinearModule hsource
        ((Hom.toFiniteBilinearModule_apply g x).trans
          (hxy.trans (Hom.toFiniteBilinearModule_apply g y).symm))
    exact ⟨(g.toIsometry ((Nat.bijective_iff_injective_and_card g).mpr ⟨hinj, rfl⟩)).symm⟩

private theorem dyadicCyclic_prod_V_succ_quadratic_intCast (k : ℕ) [NeZero k] (θ x y z : ℤ) :
    ((dyadicCyclic k θ).prod (dyadicV (k + 1))).quadratic
        ((x : ZMod (2 ^ k)), ((y : ZMod (2 ^ (k + 1))), (z : ZMod (2 ^ (k + 1))))) =
      ZMod.toRatAddCircle (2 ^ (k + 2))
        ((2 * (θ * x ^ 2 + y ^ 2 + y * z + z ^ 2) : ℤ) : ZMod (2 ^ (k + 2))) := by
  have hv := ZMod.toRatAddCircle_intCast (2 ^ (k + 1)) (y ^ 2 + y * z + z ^ 2)
  simp only [Int.cast_add, Int.cast_pow, Int.cast_mul] at hv
  rw [ZMod.toRatAddCircle_intCast]
  erw [prod_quadratic, dyadicCyclic_quadratic_intCast, dyadicV_quadratic, hv]
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  simp only [pow_add, pow_one, pow_two]
  field_simp
  ring

private theorem dyadicCyclic_prod_U_succ_quadratic_intCast (k : ℕ) [NeZero k] (θ x y z : ℤ) :
    ((dyadicCyclic k θ).prod (dyadicU (k + 1))).quadratic
        ((x : ZMod (2 ^ k)), ((y : ZMod (2 ^ (k + 1))), (z : ZMod (2 ^ (k + 1))))) =
      ZMod.toRatAddCircle (2 ^ (k + 2))
        ((2 * (θ * x ^ 2 + y * z) : ℤ) : ZMod (2 ^ (k + 2))) := by
  have hu := ZMod.toRatAddCircle_intCast (2 ^ (k + 1)) (y * z)
  simp only [Int.cast_mul] at hu
  rw [ZMod.toRatAddCircle_intCast]
  erw [prod_quadratic, dyadicCyclic_quadratic_intCast, dyadicU_quadratic, hu]
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  simp only [pow_add, pow_one, pow_two]
  field_simp

private def dyadicCyclicPlaneSuccChange (k : ℕ) (u t a b c d : ℤ) :
    (ZMod (2 ^ k) × (ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →+
      (ZMod (2 ^ k) × (ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) where
  toFun x :=
    ((u : ZMod (2 ^ k)) * x.1 +
      ZMod.castHom (pow_dvd_pow 2 (by omega : k ≤ k + 1)) (ZMod (2 ^ k))
        (((-t * (2 * a + c) : ℤ) : ZMod (2 ^ (k + 1))) * x.2.1 +
          ((-t * (2 * b + d) : ℤ) : ZMod (2 ^ (k + 1))) * x.2.2),
      (ZMod.mulCastHom 2 (by simp [pow_succ]) x.1 +
        (a : ZMod (2 ^ (k + 1))) * x.2.1 + (b : ZMod (2 ^ (k + 1))) * x.2.2,
        (c : ZMod (2 ^ (k + 1))) * x.2.1 + (d : ZMod (2 ^ (k + 1))) * x.2.2))
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add] <;> ring

private theorem dyadicCyclicPlaneSuccChange_intCast (k : ℕ) (u t a b c d m n z : ℤ) :
    dyadicCyclicPlaneSuccChange k u t a b c d
      ((m : ZMod (2 ^ k)), ((n : ZMod (2 ^ (k + 1))), (z : ZMod (2 ^ (k + 1))))) =
    (((u * m - t * (2 * (a * n + b * z) + (c * n + d * z)) : ℤ) : ZMod (2 ^ k)),
      (((2 * m + a * n + b * z : ℤ) : ZMod (2 ^ (k + 1))),
        ((c * n + d * z : ℤ) : ZMod (2 ^ (k + 1))))) := by
  simp only [dyadicCyclicPlaneSuccChange, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  apply Prod.ext
  · simp only [map_add, map_mul, map_intCast]
    push_cast
    ring
  · apply Prod.ext
    · rw [ZMod.mulCastHom_intCast]
      push_cast
      ring
    · push_cast
      ring

private theorem dyadicCyclicPlaneSuccChange_quadratic (k : ℕ) [NeZero k] (θ u t a b c d : ℤ)
    (hroot : (θ : ZMod (2 ^ (k + 2))) * (u : ZMod (2 ^ (k + 2))) ^ 2 + 4 = 5 * θ)
    (hinv : (θ : ZMod (2 ^ (k + 2))) * (u : ZMod (2 ^ (k + 2))) * t = 1)
    (hplane : ∀ n z : ZMod (2 ^ (k + 2)),
      (θ : ZMod (2 ^ (k + 2))) * (-t * (2 * (a * n + b * z) + (c * n + d * z))) ^ 2 +
        (a * n + b * z) ^ 2 + (a * n + b * z) * (c * n + d * z) +
        (c * n + d * z) ^ 2 = n * z)
    (x : ((dyadicCyclic k (5 * θ)).prod (dyadicU (k + 1))).carrier) :
    ((dyadicCyclic k θ).prod (dyadicV (k + 1))).quadratic
        (dyadicCyclicPlaneSuccChange k u t a b c d x) =
      ((dyadicCyclic k (5 * θ)).prod (dyadicU (k + 1))).quadratic x := by
  rcases x with ⟨m, n, z⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) m
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ (k + 1)) n
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ (k + 1)) z
  erw [dyadicCyclicPlaneSuccChange_intCast, dyadicCyclic_prod_V_succ_quadratic_intCast,
    dyadicCyclic_prod_U_succ_quadratic_intCast]
  congr 1
  push_cast
  linear_combination 2 * hplane n z + 2 * (m : ZMod (2 ^ (k + 2))) ^ 2 * hroot -
    4 * m * (2 * (a * (n : ZMod (2 ^ (k + 2))) + b * z) + (c * n + d * z)) * hinv

/-- Replacing an accompanying `v(2^{k+1})` by `u(2^{k+1})` multiplies the odd
coefficient of a cyclic form of order `2^k` by five, as in Nikulin's relation 1.8.2(f). -/
noncomputable def dyadicCyclicProdVSuccIsometryFiveMulProdU (k : ℕ) [NeZero k]
    {θ : ℤ} (hθ : Odd θ) :
    Isometry ((dyadicCyclic k θ).prod (dyadicV (k + 1)))
      ((dyadicCyclic k (5 * θ)).prod (dyadicU (k + 1))) :=
  Classical.choice <| by
    obtain ⟨u, t, a, b, c, d, hroot, hinv, hplane⟩ :=
      ZMod.BinaryQuadraticForm.exists_plane_cyclic_coefficients_of_odd (k + 1) hθ
    let ui : ℤ := u.val
    let ti : ℤ := t.val
    let ai : ℤ := a.val
    let bi : ℤ := b.val
    let ci : ℤ := c.val
    let di : ℤ := d.val
    have hroot' : (θ : ZMod (2 ^ (k + 2))) * (ui : ZMod (2 ^ (k + 2))) ^ 2 + 4 = 5 * θ := by
      simpa only [ui, Int.cast_natCast, ZMod.natCast_zmod_val] using hroot
    have hinv' : (θ : ZMod (2 ^ (k + 2))) * (ui : ZMod (2 ^ (k + 2))) * ti = 1 := by
      simpa only [ui, ti, Int.cast_natCast, ZMod.natCast_zmod_val] using hinv
    have hplane' : ∀ n z : ZMod (2 ^ (k + 2)),
        (θ : ZMod (2 ^ (k + 2))) * (-ti * (2 * (ai * n + bi * z) + (ci * n + di * z))) ^ 2 +
          (ai * n + bi * z) ^ 2 + (ai * n + bi * z) * (ci * n + di * z) +
          (ci * n + di * z) ^ 2 = n * z := by
      simpa only [ti, ai, bi, ci, di, Int.cast_natCast, ZMod.natCast_zmod_val] using hplane
    let g : Hom ((dyadicCyclic k (5 * θ)).prod (dyadicU (k + 1)))
        ((dyadicCyclic k θ).prod (dyadicV (k + 1))) :=
      { toLinearMap := (dyadicCyclicPlaneSuccChange k ui ti ai bi ci di).toIntLinearMap
        map_app' := fun x ↦ by
          simpa only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap] using
            dyadicCyclicPlaneSuccChange_quadratic k θ ui ti ai bi ci di hroot' hinv' hplane' x }
    have hsource : ((dyadicCyclic k (5 * θ)).prod (dyadicU (k + 1))).IsNondegenerate :=
      (isNondegenerate_prod _ _).mpr
        ⟨(isNondegenerate_dyadicCyclic_iff _ _).mpr ((by decide : Odd (5 : ℤ)).mul hθ),
          isNondegenerate_dyadicU (k + 1)⟩
    have hinj : Function.Injective g := fun x y hxy ↦
      FiniteBilinearModule.Hom.injective g.toFiniteBilinearModule hsource
        ((Hom.toFiniteBilinearModule_apply g x).trans
          (hxy.trans (Hom.toFiniteBilinearModule_apply g y).symm))
    exact ⟨(g.toIsometry ((Nat.bijective_iff_injective_and_card g).mpr ⟨hinj, rfl⟩)).symm⟩


end TauCeti.FiniteQuadraticModule
