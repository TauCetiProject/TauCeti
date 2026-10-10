/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Basic

import TauCeti.Data.ZMod.BinaryQuadraticForm
import TauCeti.Data.ZMod.Two

/-!
# Relations between the rank-two dyadic generators

Two copies of the dyadic hyperbolic generator `u^{(2)}(2^k)` are isometric to two copies
of `v^{(2)}(2^k)`. This is a relation among the generators of nondegenerate finite quadratic
modules, with preservation of the quadratic values in the half-norm convention. It allows
pairs of `v`-blocks to be replaced by hyperbolic blocks when comparing orthogonal decompositions.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(b), (k).
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

end TauCeti.FiniteQuadraticModule
