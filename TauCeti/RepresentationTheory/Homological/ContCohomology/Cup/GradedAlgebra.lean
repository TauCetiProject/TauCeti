/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Module.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Assoc
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.GradedComm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Unit

/-!
# The graded mod-two continuous cohomology algebra

For a topological group `G`, the groups `H^n(G, ᵓ₂)` with trivial coefficients form a
graded-commutative algebra under the cup product. In characteristic two the Koszul sign is
invisible, so the external direct sum

```text
⊕ n : ℕ, H^n(G, ᵓ₂)
```

is an ordinary commutative ring. This file packages the all-degree cup product in that form.
The homogeneous multiplication is `TauCeti.cohomF2Cup`; its value on the direct-sum generators
is fixed by `TauCeti.cohomF2.of_mul_of`.

The coefficient object `TauCeti.trivialF2` is a representation over `ℤ`, as required by the
all-degree continuous-cohomology API. Each cohomology group is nevertheless killed by `2`, and
therefore has its canonical `ZMod 2`-module structure. The resulting direct sum is a `ZMod 2`
algebra whose multiplication preserves degrees.

## Main definitions

* `TauCeti.cohomF2`: continuous cohomology with trivial `ᵓ₂` coefficients.
* `TauCeti.cohomF2Cup`: the homogeneous cup product.
* `TauCeti.cohomF2One`: the degree-zero unit class.
* `TauCeti.cohomologyF2`: the external direct sum of the cohomology groups.

## Main results

* `TauCeti.cohomF2.two_nsmul`: every homogeneous cohomology class is killed by `2`.
* `TauCeti.cohomF2.of_mul_of`: multiplication of homogeneous elements is the cup product.
* `TauCeti.cohomF2.algebraMap_apply`: scalars from `ZMod 2` lie in degree zero.

The cup-product identities used here are the Alexander–Whitney identities in Brown,
*Cohomology of Groups*, Chapter V, §3, and Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (1.4.4).
-/

public section

namespace TauCeti

open CategoryTheory DirectSum
open TauCeti.ContinuousCohomology (degreeZeroClass)

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous cohomology with trivial `ᵓ₂` coefficients, indexed by its degree. -/
noncomputable abbrev cohomF2 (n : ℕ) : Type u :=
  continuousCohomology n (trivialF2 G)

/-- The homogeneous cup product on continuous cohomology with trivial `ᵓ₂` coefficients. -/
noncomputable def cohomF2Cup (m n : ℕ) : cohomF2 G m → cohomF2 G n → cohomF2 G (m + n) :=
  fun x y ↦ (trivialF2TopPairing G).cup m n x y

/-- The unit in degree zero of continuous cohomology with trivial `ᵓ₂` coefficients. -/
noncomputable def cohomF2One : cohomF2 G 0 :=
  degreeZeroClass (trivialF2 G) ((trivialF2Equiv G).symm 1) fun g ↦ by simp

/-- The graded mod-two continuous cohomology ring, as the external direct sum of its homogeneous
pieces. -/
noncomputable abbrev cohomologyF2 : Type u :=
  ⨁ n : ℕ, cohomF2 G n

namespace cohomF2

attribute [local instance] TopRep.distribMulAction

/-- Every element of every term in the coinduced resolution of `trivialF2` is killed by `2`. -/
private theorem resolutionX_two_nsmul : ∀ (n : ℕ) (x : (TopRep.resolutionX (trivialF2 G) n).V),
    2 • x = 0
  | 0, x => by
      apply (trivialF2Equiv G).injective
      rw [map_nsmul, map_zero]
      simpa only [two_nsmul] using CharTwo.add_self_eq_zero (trivialF2Equiv G x)
  | n + 1, x => by
      apply ContinuousMap.ext
      intro g
      exact resolutionX_two_nsmul n (x g)

/-- Every class in continuous cohomology with trivial `ᵓ₂` coefficients is killed by `2`. -/
theorem two_nsmul (n : ℕ) (x : cohomF2 G n) : 2 • x = 0 := by
  let K := TopRep.homogeneousCochains (trivialF2 G)
  obtain ⟨a, rfl⟩ := K.homologyπ_surjective n x
  rw [← map_nsmul]
  rw [show 2 • a = 0 by
    apply K.iCycles_injective n
    rw [map_nsmul, map_zero]
    apply Subtype.ext
    exact resolutionX_two_nsmul G (n + 1) (K.iCycles n a).1, map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The coefficient pairing sends the lifted unit to a left unit. -/
private theorem cup_one_coeff_left (x : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil ((trivialF2Equiv G).symm 1) x = x := by
  apply (trivialF2Equiv G).injective
  simp

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The coefficient pairing sends the lifted unit to a right unit. -/
private theorem cup_one_coeff_right (x : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil x ((trivialF2Equiv G).symm 1) = x := by
  apply (trivialF2Equiv G).injective
  simp

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Multiplication in the lifted coefficient field is associative. -/
private theorem cup_coeff_assoc (x y z : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil ((trivialF2TopPairing G).bil x y) z =
      (trivialF2TopPairing G).bil x ((trivialF2TopPairing G).bil y z) := by
  apply (trivialF2Equiv G).injective
  simp only [trivialF2TopPairing_bil_apply, AddEquiv.apply_symm_apply, mul_assoc]

private theorem degreeCast_heq {m n : ℕ} (h : m = n) (x : cohomF2 G m) :
    (ContinuousCohomology.degreeCast (trivialF2 G) h).hom x ≍ x := by
  subst n
  simp

private theorem cast_zero {m n : ℕ} (h : m = n) :
    cast (congrArg (cohomF2 G) h) (0 : cohomF2 G m) = 0 := by
  subst n
  rfl

/-- The degree-zero unit of mod-two continuous cohomology as a graded unit. -/
noncomputable instance instGOne : GradedMonoid.GOne (cohomF2 G) where
  one := cohomF2One G

/-- The cup product as a multiplication of homogeneous mod-two cohomology classes. -/
noncomputable instance instGMul : GradedMonoid.GMul (cohomF2 G) where
  mul := fun x y ↦ cohomF2Cup G _ _ x y

/-- The multiplication supplied by the graded multiplication is the homogeneous cup product. -/
@[simp]
theorem gMul_eq_cup {m n : ℕ} (x : cohomF2 G m) (y : cohomF2 G n) :
    GradedMonoid.GMul.mul x y = cohomF2Cup G m n x y :=
  (rfl)

/-- The unit supplied by the graded unit structure is the degree-zero unit class. -/
@[simp]
theorem gOne_eq_one : (GradedMonoid.GOne.one : cohomF2 G 0) = cohomF2One G :=
  (rfl)

/-- Mod-two continuous cohomology is a graded monoid under cup product. -/
noncomputable instance instGMonoid : GradedMonoid.GMonoid (cohomF2 G) where
  one_mul := fun x ↦ by
    rcases x with ⟨n, x⟩
    apply Sigma.ext (Nat.zero_add n)
    exact HEq.trans (((trivialF2TopPairing G).cup_one_left
      (u := (trivialF2Equiv G).symm 1) (cup_one_coeff_left G)
      (fun g ↦ by simp) n x).heq) (degreeCast_heq G _ _)
  mul_one := fun x ↦ by
    rcases x with ⟨n, x⟩
    apply Sigma.ext (Nat.add_zero n)
    exact ((trivialF2TopPairing G).cup_one_right
      (u := (trivialF2Equiv G).symm 1) (cup_one_coeff_right G)
      (fun g ↦ by simp) n x).heq
  mul_assoc := fun x y z ↦ by
    rcases x with ⟨m, x⟩
    rcases y with ⟨n, y⟩
    rcases z with ⟨p, z⟩
    apply Sigma.ext (Nat.add_assoc m n p)
    exact HEq.trans (((trivialF2TopPairing G).cup_assoc
      (trivialF2TopPairing G) (trivialF2TopPairing G) (trivialF2TopPairing G)
      (cup_coeff_assoc G) m n p x y z).heq) (degreeCast_heq G _ _)

/-- The homogeneous cup product is additive in both arguments and therefore makes the graded
monoid into a graded ring. -/
noncomputable instance instGRing : DirectSum.GRing (cohomF2 G) where
  mul_zero := fun {i j} x ↦ by
    change (trivialF2TopPairing G).cup i j x 0 = 0
    exact map_zero _
  zero_mul := fun {i j} x ↦ by
    change (trivialF2TopPairing G).cup i j 0 x = 0
    rw [map_zero, LinearMap.zero_apply]
  mul_add := fun {i j} x y z ↦ by
    change (trivialF2TopPairing G).cup i j x (y + z) = _
    exact map_add ((trivialF2TopPairing G).cup i j x) y z
  add_mul := fun {i j} x y z ↦ by
    change (trivialF2TopPairing G).cup i j (x + y) z =
      ((trivialF2TopPairing G).cup i j x + (trivialF2TopPairing G).cup i j y) z
    exact congrArg (fun f ↦ f z) (((trivialF2TopPairing G).cup i j).map_add' x y)
  natCast := fun n ↦ n • cohomF2One G
  natCast_zero := zero_nsmul _
  natCast_succ := fun n ↦ succ_nsmul (cohomF2One G) n
  intCast := fun n ↦ n • cohomF2One G
  intCast_ofNat := fun n ↦ natCast_zsmul (cohomF2One G) n
  intCast_negSucc_ofNat := fun n ↦ negSucc_zsmul (cohomF2One G) n

/-- In characteristic two the graded-commutative cup product is an ordinary commutative
multiplication on the graded pieces. -/
noncomputable instance instGCommRing : DirectSum.GCommRing (cohomF2 G) where
  mul_comm := fun x y ↦ by
    rcases x with ⟨m, x⟩
    rcases y with ⟨n, y⟩
    apply Sigma.ext (Nat.add_comm m n)
    change (trivialF2TopPairing G).cup m n x y ≍
      (trivialF2TopPairing G).cup n m y x
    have hcup := (trivialF2TopPairing G).cup_gradedComm m n x y
    rw [trivialF2TopPairing_flip] at hcup
    by_cases h : Even (m * n)
    · rw [Even.neg_one_pow h] at hcup
      exact HEq.trans hcup.heq (HEq.trans (degreeCast_heq G _ _)
        ((continuousCohomology (n + m) (trivialF2 G)).isModule.one_smul
          ((trivialF2TopPairing G).cup n m y x)).heq)
    · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp h)] at hcup
      have htwo := two_nsmul G (n + m) ((trivialF2TopPairing G).cup n m y x)
      have hneg : -((trivialF2TopPairing G).cup n m y x) =
          (trivialF2TopPairing G).cup n m y x :=
        neg_eq_of_add_eq_zero_left (by simpa only [_root_.two_nsmul] using htwo)
      rw [neg_one_smul] at hcup
      exact HEq.trans hcup.heq (HEq.trans (degreeCast_heq G _ _) hneg.heq)

private theorem graded_zero_mul {n : ℕ} (x : cohomF2 G n) :
    GradedMonoid.mk 0 (0 : cohomF2 G 0) * GradedMonoid.mk n x =
      GradedMonoid.mk n 0 := by
  apply Sigma.ext (Nat.zero_add n)
  apply heq_of_cast_eq (congrArg (cohomF2 G) (Nat.zero_add n))
  change cast (congrArg (cohomF2 G) (Nat.zero_add n))
    (GradedMonoid.GMul.mul (0 : cohomF2 G 0) x) = 0
  rw [DirectSum.GNonUnitalNonAssocSemiring.zero_mul]
  exact cast_zero G (Nat.zero_add n)

/-- The canonical `ZMod 2`-module structure on each homogeneous cohomology group. -/
noncomputable instance instModule (n : ℕ) : Module (ZMod 2) (cohomF2 G n) :=
  AddCommGroup.zmodModule (two_nsmul G n)

private theorem zmod_zero_smul (n : ℕ) (x : cohomF2 G n) : (0 : ZMod 2) • x = 0 :=
  (instModule G n).zero_smul x

private theorem zmod_one_smul (n : ℕ) (x : cohomF2 G n) : (1 : ZMod 2) • x = x :=
  (instModule G n).one_smul x

private theorem zmod_two_eq_zero_or_one (r : ZMod 2) : r = 0 ∨ r = 1 := by
  have hlt := ZMod.val_lt r
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : r.val ≤ 1) with h | h
  · exact Or.inl ((ZMod.val_eq_zero r).mp h)
  · right
    apply ZMod.val_injective 2
    rw [h, ZMod.val_one]

/-- Degree-zero scalar multiples of the unit make mod-two continuous cohomology a graded
`ZMod 2`-algebra. -/
noncomputable instance instGAlgebra : DirectSum.GAlgebra (ZMod 2) (cohomF2 G) where
  toFun := (LinearMap.toSpanSingleton (ZMod 2) _ (cohomF2One G)).toAddMonoidHom
  map_one := one_smul (ZMod 2) (cohomF2One G)
  map_mul r s := by
    change GradedMonoid.mk 0 ((r * s) • cohomF2One G) =
      GradedMonoid.mk 0 (r • cohomF2One G) * GradedMonoid.mk 0 (s • cohomF2One G)
    rcases zmod_two_eq_zero_or_one r with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one s with rfl | rfl
    · rw [zero_mul, zmod_zero_smul]
      exact (graded_zero_mul G (0 : cohomF2 G 0)).symm
    · rw [zero_mul, zmod_zero_smul, zmod_one_smul]
      exact (graded_zero_mul G (cohomF2One G)).symm
    · rw [mul_zero, zmod_zero_smul, zmod_one_smul]
      exact ((mul_comm (GradedMonoid.mk 0 (cohomF2One G))
        (GradedMonoid.mk 0 (0 : cohomF2 G 0))).trans
          (graded_zero_mul G (cohomF2One G))).symm
    · rw [one_mul, zmod_one_smul]
      exact (one_mul (1 : GradedMonoid (cohomF2 G))).symm
  commutes r x := by
    exact mul_comm (GradedMonoid.mk 0 (r • cohomF2One G)) x
  smul_def r x := by
    rcases x with ⟨n, x⟩
    change GradedMonoid.mk n (r • x) =
      GradedMonoid.mk 0 (r • cohomF2One G) * GradedMonoid.mk n x
    rcases zmod_two_eq_zero_or_one r with rfl | rfl
    · rw [zmod_zero_smul G n, zmod_zero_smul G 0]
      exact (graded_zero_mul G x).symm
    · rw [zmod_one_smul G n, zmod_one_smul G 0, ← gOne_eq_one]
      exact (one_mul (GradedMonoid.mk n x)).symm

/-- Multiplication of homogeneous elements in `cohomologyF2` is their cup product. -/
@[simp]
theorem of_mul_of {m n : ℕ} (x : cohomF2 G m) (y : cohomF2 G n) :
    DirectSum.of (cohomF2 G) m x * DirectSum.of (cohomF2 G) n y =
      DirectSum.of (cohomF2 G) (m + n) (cohomF2Cup G m n x y) := by
  rw [DirectSum.of_mul_of]
  rw [gMul_eq_cup]

/-- The scalar `r : ZMod 2` in the total cohomology algebra is the degree-zero class
`r • 1`. -/
@[simp]
theorem algebraMap_apply (r : ZMod 2) :
    algebraMap (ZMod 2) (cohomologyF2 G) r =
      DirectSum.of (cohomF2 G) 0 (r • cohomF2One G) :=
  (rfl)

end cohomF2

end TauCeti
