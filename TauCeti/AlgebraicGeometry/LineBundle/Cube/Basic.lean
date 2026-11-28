/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.GroupPairing
import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange
import Mathlib.Tactic.Abel

/-!
# The cube class of a line bundle

For a class `c` on a monoid scheme `G` over `S`, the cube class is the alternating product of the
pullbacks of `c` along the partial products of the three coordinates of `G ×ₛ G ×ₛ G`. The term
for the empty product accounts for the restriction of the line bundle to the unit section.

The cube class tests multiplicativity of `LineBundleClass.pairing`. Its pullback by three
`T`-points is the quotient of the pairing on the product of the first two points by the product
of their individual pairings. If the cube class is trivial, the pairing is multiplicative in
both arguments on all test schemes over `S`. Triviality of the cube class is preserved by
arbitrary base change of a group scheme.

## References

* J. S. Milne, *Abelian Varieties* (2008), Corollary 5.2.
* B. Conrad, *Abelian Varieties*, notes by T. Feng (2015), Theorem 3.1.6.
-/

public section

open CategoryTheory CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {S : AlgebraicGeometry.Scheme.{u}}

section Monoid

variable {G : Over S} [MonObj G]

/-- The cube class of `c` on `G ×ₛ G ×ₛ G`, including the inverse of the pullback by the unit
section composed with the structure morphism. -/
noncomputable def cubeClass (c : LineBundleClass G.left) : LineBundleClass ((G ⊗ G) ⊗ G).left :=
  let x := fst (G ⊗ G) G ≫ fst G G
  let y := fst (G ⊗ G) G ≫ snd G G
  let z := snd (G ⊗ G) G
  pairing c (x * y) z / (pairing c x z * pairing c y z)

/-- The cube class is the alternating product over the eight subsets of three coordinates. -/
lemma cubeClass_eq (c : LineBundleClass G.left) :
    let x := fst (G ⊗ G) G ≫ fst G G
    let y := fst (G ⊗ G) G ≫ snd G G
    let z := snd (G ⊗ G) G
    c.cubeClass = pullback ((x * y) * z).left c * pullback x.left c * pullback y.left c *
      pullback z.left c / (pullback (x * y).left c * pullback (x * z).left c *
        pullback (y * z).left c * pullback (1 : (G ⊗ G) ⊗ G ⟶ G).left c) := by
  dsimp only [cubeClass]
  apply Additive.ofMul.injective
  simp only [pairing_def, ofMul_mul, ofMul_inv, ofMul_div]
  abel

/-- The cube class pulled back along three points measures multiplicativity of the pairing
in the first argument. -/
lemma pullback_cubeClass (c : LineBundleClass G.left) {T : Over S} (x y z : T ⟶ G) :
    pullback (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift x y) z).left
      c.cubeClass =
      pairing c (x * y) z / (pairing c x z * pairing c y z) := by
  simp only [cubeClass, div_eq_mul_inv, pullback_mul, pullback_inv, pullback_pairing,
    MonObj.comp_mul, lift_fst_assoc, lift_fst, lift_snd]

/-- The cube class is trivial exactly when the pairing is multiplicative in its first argument
on every test scheme. -/
lemma cubeClass_eq_one_iff (c : LineBundleClass G.left) :
    c.cubeClass = 1 ↔ ∀ (T : Over S) (x y z : T ⟶ G),
      pairing c (x * y) z = pairing c x z * pairing c y z := by
  constructor
  · intro h T x y z
    exact div_eq_one.mp (by simpa only [h, pullback_one] using (pullback_cubeClass c x y z).symm)
  · intro h
    simp only [cubeClass, div_eq_one]
    exact h _ _ _ _

/-- A trivial cube class makes the pairing multiplicative in its first argument. -/
lemma pairing_mul_left_of_cubeClass_eq_one {c : LineBundleClass G.left} (h : c.cubeClass = 1)
    {T : Over S} (x y z : T ⟶ G) :
    pairing c (x * y) z = pairing c x z * pairing c y z :=
  (cubeClass_eq_one_iff c).mp h T x y z

/-- A trivial cube class makes the pairing multiplicative in its second argument. -/
lemma pairing_mul_right_of_cubeClass_eq_one {c : LineBundleClass G.left} (h : c.cubeClass = 1)
    {T : Over S} (x y z : T ⟶ G) :
    pairing c x (y * z) = pairing c x y * pairing c x z := by
  -- The pairing is the coboundary of the function sending a point to its pullback of `c`.
  have hAssoc : pairing c x y * pairing c (x * y) z =
      pairing c x (y * z) * pairing c y z := by
    apply Additive.ofMul.injective
    simp only [pairing_def, mul_assoc, ofMul_mul, ofMul_inv]
    abel
  rw [pairing_mul_left_of_cubeClass_eq_one h, ← mul_assoc] at hAssoc
  exact (mul_right_cancel hAssoc).symm

/-- The pairing of a class with trivial cube is a monoid homomorphism in each point variable. -/
noncomputable def pairingHom {c : LineBundleClass G.left} (hc : cubeClass c = 1) (T : Over S) :
    (T ⟶ G) →* ((T ⟶ G) →* LineBundleClass T.left) where
  toFun x :=
    { toFun := pairing c x
      map_one' := pairing_one_right c x
      map_mul' := pairing_mul_right_of_cubeClass_eq_one hc x }
  map_one' := MonoidHom.ext (pairing_one_left c)
  map_mul' x y := MonoidHom.ext (pairing_mul_left_of_cubeClass_eq_one hc x y)

/-- Evaluating the two homomorphisms of the pairing recovers its value at the given points. -/
@[simp]
lemma pairingHom_apply {c : LineBundleClass G.left} (hc : cubeClass c = 1) {T : Over S}
    (x y : T ⟶ G) : pairingHom hc T x y = pairing c x y := (rfl)

/-- Tensoring with a line bundle pulled back from the base does not change the cube class.
In particular the cube class can be computed after normalizing the bundle at the unit. -/
@[simp]
lemma cubeClass_mul_pullback (c : LineBundleClass G.left) (d : LineBundleClass S) :
    cubeClass (c * pullback G.hom d) = c.cubeClass := by
  have hbase {T : Over S} (x y : T ⟶ G) : pairing (pullback G.hom d) x y = 1 := by
    simp only [pairing_def, pullback_comp, Over.w, mul_inv_cancel, one_mul, inv_mul_cancel]
  simp only [cubeClass, pairing_mul, hbase, mul_one]

end Monoid

/-- A line-bundle class with trivial cube still has trivial cube after arbitrary base change
of its group scheme. -/
lemma cubeClass_pullback_fst_eq_one {S' : AlgebraicGeometry.Scheme.{u}} (s : S' ⟶ S)
    (G : Grp (Over S)) {c : LineBundleClass G.X.left} (hc : cubeClass c = 1) :
    cubeClass (G := ((Over.pullback s).mapGrp.obj G).X)
      (pullback (Limits.pullback.fst G.X.hom s) c) = 1 := by
  rw [cubeClass_eq_one_iff]
  intro T x y z
  let e := GroupScheme.baseChangePointMulEquiv s G T
  have he (a b : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
      pairing (pullback (Limits.pullback.fst G.X.hom s) c) a b = pairing c (e a) (e b) := by
    simp only [pairing_def, ← map_mul e, ← map_one e, e,
      GroupScheme.baseChangePointMulEquiv_apply_left]
    -- Specialize functoriality to the first projection. The base-changed group object
    -- and the pullback scheme agree definitionally, through the forgetful functors.
    have hp (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :=
      pullback_comp p.left (Limits.pullback.fst G.X.hom s) c
    rw [hp (a * b), hp a, hp b, hp 1]
  simpa only [he, map_mul] using pairing_mul_left_of_cubeClass_eq_one hc (e x) (e y) (e z)

end TauCeti.AlgebraicGeometry.LineBundleClass
