/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Irreducible.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.SystemGroup
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Surface
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.LimitGroup.FreeProduct
import TauCeti.GroupTheory.LimitGroup.SurfaceGroup

/-!
# The radical of the genus-two equation `[x₁, y₁][x₂, y₂] = 1`

Let `G` be a nonabelian CSA group with the big powers property, for instance a nonabelian fully
residually free group. The standard quadratic equation `S = [x₁, y₁][x₂, y₂] = 1` over `G` has
no coefficients, and its group `G_S = G[X] ⧸ ncl(S)` is the free product
`G ∗ (S⁺(2, 0) ∗ F(X ∖ {x₁, y₁, x₂, y₂}))` of `G`, the closed orientable surface group of genus
two and the free group on the variables that do not occur in the equation
(`TauCeti.GroupAlgGeom.Quadratic.Standard.orientableSystemGroupEquiv`).

The surface group `S⁺(2, 0)` is nonabelian and fully residually free (G. Baumslag), and so is its
free product with a free group. Hence `G_S` is discriminated by `G` over `G`
(`TauCeti.LimitGroup.isDiscriminatedBy_inl_coprod`). Consequently:

* the radical of `S` over `G` is the normal closure of `S`, so `G_{R(S)} = G_S`;
* the algebraic set `V_G(S)` is irreducible in the Zariski topology.

This is the genus-two half of case (1) of the radicals of consistent standard quadratic
equations over a freely discriminated group ([IFT], Theorem 2 (1); [VAR-I], §2). The equation
has the trivial solution, so no consistency hypothesis is needed.

Nonabelianity of `G` is necessary: over an abelian group `G` every solution of `S` takes values
in `G`, so the commutator of `x₁` and `y₁` lies in the radical of `S`. It does not lie in the
normal closure of `S`, since `x₁ ↦ a`, `y₁ ↦ b`, `x₂ ↦ b`, `y₂ ↦ a` solves `S` in the free group
on `a` and `b`, where `[a, b] ≠ 1`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.isDiscriminatedBy_coeff_orientable_two`: the group of
  the genus-two equation is discriminated by `G` over `G`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_toWord_orientable_two`: the radical of the
  genus-two equation is its normal closure.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isIrreducible_V_orientable_two`: the algebraic set of
  the genus-two equation is irreducible.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.normalClosure_lt_Rad_orientable_two`: over an abelian
  group the radical is strictly larger than the normal closure.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Theorem 2 (1).
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §2.
* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
-/

public section

open Monoid.Coprod Subgroup Group
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

open SurfaceGroup LimitGroup

variable {G X : Type*} [Group G] {x y : Fin 2 → X}

/-- **The group of the genus-two equation is discriminated by `G`.** Over a nonabelian CSA group
`G` with the big powers property, the group `G_S` of `[x₁, y₁][x₂, y₂] = 1` is discriminated by
`G` over `G`: it is the free product of `G` with the fully residually free group
`S⁺(2, 0) ∗ F(X ∖ {x₁, y₁, x₂, y₂})`. -/
theorem isDiscriminatedBy_coeff_orientable_two (hBP : IsBP G) (hG : IsCSA G)
    (hGc : ¬IsMulCommutative G) (inj : (Sum.elim x y).Injective) :
    IsDiscriminatedBy (SystemGroup.coeff {(orientable (G := G) 2 two_pos x y inj).toWord})
      (MonoidHom.id G) := by
  have hK := isFullyResiduallyFree_orientable_two_zero.coprod
    (Orientable.not_isMulCommutative_of_eulerChar_neg (by simp [Orientable.eulerChar_def]))
    (isFullyResiduallyFree_of_isFreeGroup (G := FreeGroup ↥(Set.range (Sum.elim x y))ᶜ))
  exact (isDiscriminatedBy_inl_coprod hBP hG hGc hK).of_injective _
    (GHom.ofMulEquiv_bijective (orientableSystemGroupEquiv G two_pos inj) fun g => by simp).1

/-- **The radical of the genus-two equation** ([IFT], Theorem 2 (1)). Over a nonabelian CSA group
`G` with the big powers property, for instance a nonabelian fully residually free group, the
radical of `[x₁, y₁][x₂, y₂] = 1` is the normal closure of the equation. -/
theorem Rad_toWord_orientable_two (hBP : IsBP G) (hG : IsCSA G) (hGc : ¬IsMulCommutative G)
    (inj : (Sum.elim x y).Injective) :
    Rad (.id G) {(orientable (G := G) 2 two_pos x y inj).toWord} =
      normalClosure {(orientable (G := G) 2 two_pos x y inj).toWord} :=
  (SystemGroup.isSeparatedBy_coeff_iff _).1
    (isDiscriminatedBy_coeff_orientable_two hBP hG hGc inj).isSeparatedBy

/-- **The genus-two equation is irreducible.** Over a nonabelian CSA group `G` with the big powers
property, the algebraic set of `[x₁, y₁][x₂, y₂] = 1` is irreducible in the Zariski topology. -/
theorem isIrreducible_V_orientable_two (hBP : IsBP G) (hG : IsCSA G) (hGc : ¬IsMulCommutative G)
    (inj : (Sum.elim x y).Injective) :
    @IsIrreducible (X → G) (zariskiTopology (.id G) X)
      (V (.id G) {(orientable (G := G) 2 two_pos x y inj).toWord}) := by
  set S := (orientable (G := G) 2 two_pos x y inj).toWord
  -- `V(S)` is the algebraic set of the kernel `ncl(S)` of `G[X] → G_S`.
  let π : GHom (inl : G →* GX G X) (SystemGroup.coeff {S}) :=
    ⟨QuotientGroup.mk' (normalClosure {S}), fun g => (SystemGroup.coeff_apply _ g).symm⟩
  have hπ : (π : GX G X →* SystemGroup G {S}).ker = normalClosure {S} :=
    QuotientGroup.ker_mk' _
  have h := (isDiscriminatedBy_coeff_orientable_two hBP hG hGc inj).isIrreducible_V_ker π
  rwa [hπ, V_normalClosure] at h

/-- **Nonabelian coefficients are needed.** Over an abelian group `G`, the radical of the genus-two
equation `[x₁, y₁][x₂, y₂] = 1` is strictly larger than its normal closure: it contains the
commutator `⁅x₁, y₁⁆`, which is not a consequence of the equation. -/
theorem normalClosure_lt_Rad_orientable_two [IsMulCommutative G]
    (inj : (Sum.elim x y).Injective) :
    normalClosure {(orientable (G := G) 2 two_pos x y inj).toWord} <
      Rad (.id G) {(orientable (G := G) 2 two_pos x y inj).toWord} := by
  set S := (orientable (G := G) 2 two_pos x y inj).toWord
  set w : GX G X := ⁅(inr (FreeGroup.of (x 0)) : GX G X), inr (FreeGroup.of (y 0))⁆
  refine lt_of_le_of_ne' (normalClosure_le_Rad _) fun h => ?_
  -- Every point of `G` kills the commutator, since `G` is abelian.
  have hw : w ∈ Rad (.id G) {S} := mem_Rad.2 fun v _ => by
    simpa [w, map_commutatorElement, commutatorElement_eq_one_iff_commute, commute_iff_eq] using
      mul_comm' (v (x 0)) (v (y 0))
  -- The point `x₁ ↦ a`, `y₁ ↦ b`, `x₂ ↦ b`, `y₂ ↦ a` of `F(a, b)` solves `S` but not `w`.
  let a : FreeGroup (Fin 2) := FreeGroup.of 0
  let b : FreeGroup (Fin 2) := FreeGroup.of 1
  let v : X → FreeGroup (Fin 2) :=
    Function.extend (Sum.elim x y) (Sum.elim ![a, b] ![b, a]) 1
  have hvx (i : Fin 2) : v (x i) = ![a, b] i := by
    simpa using inj.extend_apply (Sum.elim ![a, b] ![b, a]) 1 (.inl i)
  have hvy (i : Fin 2) : v (y i) = ![b, a] i := by
    simpa using inj.extend_apply (Sum.elim ![a, b] ![b, a]) 1 (.inr i)
  have hv : v ∈ V (1 : G →* FreeGroup (Fin 2)) {S} := by
    simp [S, mem_V, eval_toWord_orientable, orientableWord_def, hvx, hvy, mul_assoc]
  have hw' := mem_Rad.1 (normalClosure_le_Rad (ι := (1 : G →* FreeGroup (Fin 2))) {S}
    (h ▸ hw)) v hv
  simp only [w, map_commutatorElement, eval_inr, FreeGroup.lift_apply_of, hvx, hvy,
    commutatorElement_eq_one_iff_commute] at hw'
  exact zero_ne_one (FreeGroup.eq_of_commute_of_of (by simpa [a, b] using hw'))

end TauCeti.GroupAlgGeom.Quadratic.Standard
