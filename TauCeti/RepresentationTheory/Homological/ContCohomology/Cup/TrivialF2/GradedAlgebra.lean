/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.GradedComm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.GradedRing
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic

/-!
# The graded mod-two continuous cohomology algebra

For a topological group `G`, the groups `H^n(G, 𝔽₂)` with trivial coefficients form a
graded-commutative algebra under the cup product. In characteristic two the Koszul sign is
invisible, so the external direct sum

```text
⊕ n : ℕ, H^n(G, 𝔽₂)
```

is an ordinary commutative ring. This file packages the all-degree cup product along
`TauCeti.trivialF2TopPairing` in that form: the graded ring structure is the general
`TauCeti.TopPairing.cohomologyGRing` of that pairing, whose unit is `TauCeti.cohomF2One`, and its
value on the direct-sum generators is fixed by `TauCeti.cohomF2.of_mul_of`.

The coefficient object `TauCeti.trivialF2` is an object of `TopRep ℤ G`, the coefficients over
which the existing mod-two corpus is stated, so its cohomology groups carry a priori only a
`ℤ`-module structure. Each of them is nevertheless killed by `2`
(`TauCeti.cohomF2.two_nsmul_eq_zero`), and therefore has its canonical `ZMod 2`-module structure.
The resulting direct sum is a `ZMod 2`-algebra whose multiplication preserves degrees.

## Main definitions

* `TauCeti.gradedCohomF2`: the external direct sum of the cohomology groups, a commutative
  `ZMod 2`-algebra.

## Main results

* `TauCeti.cohomF2.of_mul_of`: multiplication of homogeneous elements is the cup product.
* `TauCeti.cohomF2.algebraMap_apply`: scalars from `ZMod 2` lie in degree zero.

The cup-product identities used here are the Alexander–Whitney identities in Brown,
*Cohomology of Groups*, Chapter V, §3, and Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (1.4.4).
-/

public section

namespace TauCeti

open CategoryTheory DirectSum

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The graded mod-two continuous cohomology algebra, as the external direct sum of the groups
`cohomF2 G n`. -/
noncomputable abbrev gradedCohomF2 : Type u :=
  ⨁ n : ℕ, cohomF2 G n

namespace cohomF2

/-- Mod-two continuous cohomology is a graded ring under the cup product along
`TauCeti.trivialF2TopPairing`, with unit `TauCeti.cohomF2One`. -/
noncomputable instance instGRing : DirectSum.GRing (cohomF2 G) :=
  (trivialF2TopPairing G).cohomologyGRing ((trivialF2Equiv G).symm 1)
    (fun g ↦ trivialF2_ρ_apply_apply G g _) (trivialF2TopPairing_bil_one_left G)
    (trivialF2TopPairing_bil_one_right G) (trivialF2TopPairing_bil_assoc G)

/-- The multiplication supplied by the graded ring structure is the cup product. -/
@[simp]
theorem gMul_eq_cup {m n : ℕ} (x : cohomF2 G m) (y : cohomF2 G n) :
    GradedMonoid.GMul.mul x y = (trivialF2TopPairing G).cup m n x y :=
  (rfl)

/-- The unit supplied by the graded ring structure is the degree-zero unit class. -/
@[simp]
theorem gOne_eq_cohomF2One : (GradedMonoid.GOne.one : cohomF2 G 0) = cohomF2One G :=
  (cohomF2One_def G).symm

/-- Homogeneous classes commute: the Koszul sign of `TauCeti.TopPairing.cup_gradedComm` acts
trivially. -/
private theorem mk_mul_mk_comm {m n : ℕ} (x : cohomF2 G m) (y : cohomF2 G n) :
    GradedMonoid.mk m x * GradedMonoid.mk n y = GradedMonoid.mk n y * GradedMonoid.mk m x := by
  rw [GradedMonoid.mk_mul_mk, GradedMonoid.mk_mul_mk, gMul_eq_cup, gMul_eq_cup]
  have hcup : (trivialF2TopPairing G).cup m n x y =
      (ContinuousCohomology.degreeCast (trivialF2 G) (Nat.add_comm n m)).hom
        ((trivialF2TopPairing G).cup n m y x) := by
    rw [(trivialF2TopPairing G).cup_gradedComm m n x y, trivialF2TopPairing_flip]
    congr 1
    -- `cup_gradedComm` scales by the `ℤ`-module structure of the module category, which is not
    -- definitionally the canonical `ℤ`-action; `int_smul_eq_zsmul` identifies the two
    refine (int_smul_eq_zsmul _ _ _).trans ?_
    -- the Koszul sign acts trivially: every class is killed by `2`, so `-c = c`
    obtain h | h := neg_one_pow_eq_or ℤ (m * n) <;> rw [h]
    · exact one_zsmul _
    · rw [neg_one_zsmul]
      exact ZModModule.neg_eq_self _
  exact Sigma.ext (Nat.add_comm m n)
    (hcup.heq.trans (ContinuousCohomology.degreeCast_hom_apply_heq _ _))

/-- In characteristic two the graded-commutative cup product is an ordinary commutative
multiplication on the graded pieces. -/
noncomputable instance instGCommRing : DirectSum.GCommRing (cohomF2 G) where
  -- `by exact` keeps the private helper inside a proof rather than in the exposed instance body
  mul_comm := fun ⟨_, x⟩ ⟨_, y⟩ ↦ by exact mk_mul_mk_comm G x y

/-- Multiplying by the degree-zero class `r • 1` is the scalar action of `r : ZMod 2`. -/
private theorem mk_smul_cohomF2One_mul (r : ZMod 2) {n : ℕ} (x : cohomF2 G n) :
    GradedMonoid.mk 0 (r • cohomF2One G) * GradedMonoid.mk n x = GradedMonoid.mk n (r • x) := by
  obtain rfl | rfl : r = 0 ∨ r = 1 := by revert r; decide
  · rw [zero_smul, zero_smul, GradedMonoid.mk_mul_mk,
      DirectSum.GNonUnitalNonAssocSemiring.zero_mul, Nat.zero_add]
  · rw [one_smul, one_smul, ← gOne_eq_cohomF2One]
    exact one_mul (GradedMonoid.mk n x)

/-- Degree-zero scalar multiples of the unit make mod-two continuous cohomology a graded
`ZMod 2`-algebra. -/
noncomputable instance instGAlgebra : DirectSum.GAlgebra (ZMod 2) (cohomF2 G) where
  toFun := (LinearMap.toSpanSingleton (ZMod 2) _ (cohomF2One G)).toAddMonoidHom
  map_one := (one_smul (ZMod 2) (cohomF2One G)).trans (gOne_eq_cohomF2One G).symm
  -- as in `instGCommRing`, `by exact` keeps the private helper out of the exposed body
  map_mul r s := by
    exact (congrArg (GradedMonoid.mk 0) (mul_smul r s (cohomF2One G))).trans
      (mk_smul_cohomF2One_mul G r _).symm
  commutes r x := mul_comm _ x
  smul_def r := fun ⟨_, x⟩ ↦ by exact (mk_smul_cohomF2One_mul G r x).symm

/-- Multiplication of homogeneous elements in `gradedCohomF2` is their cup product. -/
@[simp]
theorem of_mul_of {m n : ℕ} (x : cohomF2 G m) (y : cohomF2 G n) :
    DirectSum.of (cohomF2 G) m x * DirectSum.of (cohomF2 G) n y =
      DirectSum.of (cohomF2 G) (m + n) ((trivialF2TopPairing G).cup m n x y) := by
  rw [DirectSum.of_mul_of, gMul_eq_cup]

/-- The scalar `r : ZMod 2` in the total cohomology algebra is the degree-zero class
`r • 1`. -/
@[simp]
theorem algebraMap_apply (r : ZMod 2) :
    algebraMap (ZMod 2) (gradedCohomF2 G) r =
      DirectSum.of (cohomF2 G) 0 (r • cohomF2One G) := by
  rw [DirectSum.algebraMap_apply]
  -- the scalar map of `instGAlgebra` is `r ↦ r • cohomF2One G` by definition
  rfl

end cohomF2

end TauCeti
