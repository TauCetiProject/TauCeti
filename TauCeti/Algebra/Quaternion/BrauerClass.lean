/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.Group
public import TauCeti.Algebra.Quaternion.CentralSimple
public import TauCeti.FieldTheory.SquareClassGroup.Basic
import TauCeti.Algebra.BrauerGroup.Splitting
import TauCeti.Algebra.BrauerGroup.Division
import TauCeti.Algebra.Quaternion.TensorProduct
import TauCeti.Algebra.Quaternion.Steinberg
import TauCeti.Algebra.Quaternion.Binary

/-!
# Brauer classes of quaternion symbols

For a field `K` with `2` invertible, this file bundles the quaternion symbol with unit parameters
`a b : Kˣ` as a central simple algebra and defines its Brauer class `[(a,b)]`, the **quaternion
symbol** in `BrauerGroup K`. The general centrality and simplicity results used here are in
`TauCeti.Algebra.Quaternion.CentralSimple`.

The symbol satisfies the classical relations (Lam III.2.11, Gille–Szamuely 1.5.2):

* it is symmetric, `[(a,b)] = [(b,a)]`, and invariant under multiplying either argument by a
  square, so it factors through square classes; these follow from isomorphisms of quaternion
  algebras through `TauCeti.BrauerGroup.mk_eq_mk_of_algEquiv`;
* it is `2`-torsion, `[(a,b)]² = 1`, because quaternion conjugation identifies `ℍ[K,a,b]` with its
  opposite algebra, which `TauCeti.BrauerGroup.inv_mk_eq_mk_of_algEquiv_op` turns into
  `[(a,b)]⁻¹ = [(a,b)]`;
* it vanishes on `(1,b)`, `(a,-a)` and on the Steinberg pair `(a,1-a)`, whose quaternion algebras
  are isomorphic to `M₂(K)`, and hence by square-class invariance on `(a,b²)` and `(a²,b)`;
* it is **bilinear**, `[(a,bc)] = [(a,b)] · [(a,c)]`, from the common slot equivalence
  `ℍ[K,a,b] ⊗[K] ℍ[K,a,c] ≃ₐ[K] ℍ[K,a,bc] ⊗[K] M₂(K)` of
  `TauCeti.QuaternionAlgebra.tensorAlgEquivTensorMatrix`, read in the Brauer group through the
  tensor product of central simple algebras;
* it is invariant under isometry of the binary form `⟨a,b⟩`, from the binary quaternion lemma.

Equality of two symbols is exactly an isomorphism of the underlying quaternion algebras, and a
symbol is trivial exactly when its algebra is split, which the four-fold splitting criterion
translates into the solvability of the norm equation `b = x² - ay²` and into the isotropy of
`⟨1, -a, -b⟩`.

## Main results

* `TauCeti.BrauerGroup.quaternionCSA`: the bundled central simple algebra of a quaternion symbol
  with unit parameters.
* `TauCeti.BrauerGroup.quaternionClass`: the Brauer class of that symbol.
* `TauCeti.BrauerGroup.quaternionClass_eq_iff`: two symbols have the same class exactly when their
  algebras are isomorphic, and `TauCeti.BrauerGroup.quaternionClass_eq_one_iff`: a symbol is
  trivial exactly when its algebra is split.
* `TauCeti.BrauerGroup.quaternionClass_comm`, `TauCeti.BrauerGroup.quaternionClass_sq`,
  `TauCeti.BrauerGroup.quaternionClass_mul_sq_right`, `TauCeti.BrauerGroup.quaternionClass_one_sub`:
  symmetry, `2`-torsion, square-class invariance and the Steinberg relation.
* `TauCeti.BrauerGroup.quaternionClass_mul`, `TauCeti.BrauerGroup.quaternionClass_mul_left`:
  **bilinearity of the quaternion symbol**.
* `TauCeti.BrauerGroup.quaternionClassOnSquareClasses`: the symbol as a pairing of square classes.
* `TauCeti.BrauerGroup.quaternionClass_congr`: isometric binary forms `⟨a,b⟩ ≅ ⟨c,d⟩`
  have equal symbols `[(a,b)] = [(c,d)]`.

## References

The classical central-simple background is in T. Y. Lam, *Introduction to Quadratic Forms over
Fields* (2005), Chapter III, §2, in particular Theorem 2.11 for the symbol relations, and
P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §1.1 and
Lemma 1.5.2.
-/

public section

open scoped Quaternion TensorProduct

open QuadraticMap

namespace TauCeti

namespace BrauerGroup

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The bundled central simple algebra underlying the quaternion symbol `(a,b)`. -/
noncomputable def quaternionCSA (a b : Kˣ) : CSA K :=
  CSA.of K ℍ[K,(a : K),(b : K)]

/-- The bundled algebra underlying `quaternionCSA` is the corresponding quaternion symbol. -/
@[simp] theorem quaternionCSA_def (a b : Kˣ) :
    quaternionCSA a b = CSA.of K ℍ[K,(a : K),(b : K)] := (rfl)

/-- The Brauer class of the quaternion symbol `(a,b)` for unit parameters `a b : Kˣ`. -/
noncomputable def quaternionClass (a b : Kˣ) : BrauerGroup K :=
  BrauerGroup.mk (quaternionCSA a b)

/-- The defining equation for `quaternionClass`. Not a `simp` lemma: the symbol is the normal
form the relations below are stated in, and unfolding it to a bare Brauer class would defeat
them. -/
theorem quaternionClass_def (a b : Kˣ) :
    quaternionClass a b = BrauerGroup.mk (CSA.of K ℍ[K,(a : K),(b : K)]) := (rfl)

/-! ### Transporting along algebra isomorphisms -/

/-- An isomorphism of quaternion algebras identifies the two symbols. -/
theorem quaternionClass_eq_of_algEquiv {a b c d : Kˣ}
    (e : ℍ[K,(a : K),(b : K)] ≃ₐ[K] ℍ[K,(c : K),(d : K)]) :
    quaternionClass a b = quaternionClass c d :=
  mk_eq_mk_of_algEquiv (A := quaternionCSA a b) (B := quaternionCSA c d) e

/-- A split quaternion symbol has trivial class. -/
theorem quaternionClass_eq_one_of_algEquiv_matrix {a b : Kˣ}
    (e : ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    quaternionClass a b = 1 :=
  (mk_eq_mk_of_algEquiv (A := quaternionCSA a b) (B := CSA.of K (Matrix (Fin 2) (Fin 2) K))
    e).trans (mk_eq_one_iff.2 (isBrauerTrivial_matrix K 2))

/-- **A quaternion symbol is trivial in the Brauer group exactly when its algebra is split.** -/
theorem quaternionClass_eq_one_iff (a b : Kˣ) :
    quaternionClass a b = 1 ↔ Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => quaternionClass_eq_one_of_algEquiv_matrix e⟩
  rw [quaternionClass_def, mk_eq_one_iff_isSplittingField,
    Algebra.isSplittingField_self_iff] at h
  obtain ⟨n, ⟨e⟩⟩ := h
  have hn : 4 = n * n := by
    have := e.toLinearEquiv.finrank_eq
    rwa [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one,
      _root_.QuaternionAlgebra.finrank_eq_four] at this
  obtain rfl : n = 2 := Nat.mul_self_inj.1 hn.symm
  exact ⟨e⟩

/-- **A quaternion symbol is trivial exactly when the norm equation `b = x² - ay²` is solvable**
(the four-fold splitting criterion, read in the Brauer group). -/
theorem quaternionClass_eq_one_iff_exists_eq_sq_sub_mul_sq (a b : Kˣ) :
    quaternionClass a b = 1 ↔ ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 :=
  (quaternionClass_eq_one_iff a b).trans
    (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq a b)

/-- **A quaternion symbol is trivial exactly when `⟨1, -a, -b⟩` is isotropic** (the four-fold
splitting criterion, read in the Brauer group). -/
theorem quaternionClass_eq_one_iff_not_anisotropic_weightedSumSquares (a b : Kˣ) :
    quaternionClass a b = 1 ↔ ¬(weightedSumSquares K ![1, -(a : K), -(b : K)]).Anisotropic :=
  (quaternionClass_eq_one_iff a b).trans
    (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_anisotropic_weightedSumSquares a b)

/-- **Two quaternion symbols have the same Brauer class exactly when their algebras are
isomorphic.** Both algebras are division algebras or both are split, since the class detects
splitting; in the division case this is the uniqueness of the division-algebra representative of a
Brauer class. -/
theorem quaternionClass_eq_iff (a b c d : Kˣ) :
    quaternionClass a b = quaternionClass c d ↔
      Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] ℍ[K,(c : K),(d : K)]) := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => quaternionClass_eq_of_algEquiv e⟩
  rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix a b with hab | hab
  · rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix c d with hcd | hcd
    · let _ : DivisionRing ℍ[K,(a : K),(b : K)] :=
        DivisionRing.ofIsUnitOrEqZero fun x => or_iff_not_imp_right.2 (hab x)
      let _ : DivisionRing ℍ[K,(c : K),(d : K)] :=
        DivisionRing.ofIsUnitOrEqZero fun x => or_iff_not_imp_right.2 (hcd x)
      exact nonempty_algEquiv_of_mk_eq_mk h
    · obtain ⟨e⟩ := hcd
      obtain ⟨e'⟩ := (quaternionClass_eq_one_iff a b).1
        (h.trans (quaternionClass_eq_one_of_algEquiv_matrix e))
      exact ⟨e'.trans e.symm⟩
  · obtain ⟨e⟩ := hab
    obtain ⟨e'⟩ := (quaternionClass_eq_one_iff c d).1
      (h.symm.trans (quaternionClass_eq_one_of_algEquiv_matrix e))
    exact ⟨e.trans e'.symm⟩

/-! ### Symmetry, square classes and two-torsion -/

/-- **Symmetry of the quaternion symbol**: `[(a,b)] = [(b,a)]`. -/
theorem quaternionClass_comm (a b : Kˣ) : quaternionClass a b = quaternionClass b a :=
  quaternionClass_eq_of_algEquiv (_root_.QuaternionAlgebra.swapEquiv (a : K) (b : K))

/-- The quaternion symbol is invariant under multiplying its second argument by a square. -/
theorem quaternionClass_mul_sq_right (a b c : Kˣ) :
    quaternionClass a (b * c ^ 2) = quaternionClass a b := by
  rw [mul_comm b (c ^ 2)]
  exact quaternionClass_eq_of_algEquiv (QuaternionAlgebra.rescaleJEquiv (a : K) (b : K) c)

/-- The quaternion symbol is invariant under multiplying its first argument by a square. -/
theorem quaternionClass_mul_sq_left (a b c : Kˣ) :
    quaternionClass (a * c ^ 2) b = quaternionClass a b := by
  rw [mul_comm a (c ^ 2)]
  exact quaternionClass_eq_of_algEquiv (QuaternionAlgebra.rescaleIEquiv (a : K) (b : K) c)

/-- **The quaternion symbol is its own inverse**: quaternion conjugation is an isomorphism of
`ℍ[K,a,b]` with its opposite algebra. -/
@[simp]
theorem inv_quaternionClass (a b : Kˣ) : (quaternionClass a b)⁻¹ = quaternionClass a b :=
  inv_mk_eq_mk_of_algEquiv_op (A := quaternionCSA a b) _root_.QuaternionAlgebra.starAe

/-- **The quaternion symbol is `2`-torsion**: `[(a,b)]² = 1`. -/
@[simp]
theorem quaternionClass_sq (a b : Kˣ) : quaternionClass a b ^ 2 = 1 := by
  rw [pow_two]
  exact inv_eq_iff_mul_eq_one.1 (inv_quaternionClass a b)

/-! ### The split symbols -/

/-- `[(1,b)] = 1`. -/
@[simp]
theorem quaternionClass_one_left (b : Kˣ) : quaternionClass 1 b = 1 :=
  quaternionClass_eq_one_of_algEquiv_matrix (QuaternionAlgebra.oneEquivMatrix b)

/-- `[(a,1)] = 1`. -/
@[simp]
theorem quaternionClass_one_right (a : Kˣ) : quaternionClass a 1 = 1 := by
  rw [quaternionClass_comm, quaternionClass_one_left]

/-- `[(a,-a)] = 1`. -/
@[simp]
theorem quaternionClass_neg_self (a : Kˣ) : quaternionClass a (-a) = 1 :=
  quaternionClass_eq_one_of_algEquiv_matrix (QuaternionAlgebra.aNegAEquivMatrix a)

/-- `[(a,c²)] = 1`: square-class invariance at `[(a,1)] = 1`. -/
@[simp]
theorem quaternionClass_sq_right (a c : Kˣ) : quaternionClass a (c ^ 2) = 1 := by
  rw [← one_mul (c ^ 2), quaternionClass_mul_sq_right, quaternionClass_one_right]

/-- `[(c²,b)] = 1`: square-class invariance at `[(1,b)] = 1`. -/
@[simp]
theorem quaternionClass_sq_left (b c : Kˣ) : quaternionClass (c ^ 2) b = 1 := by
  rw [← one_mul (c ^ 2), quaternionClass_mul_sq_left, quaternionClass_one_left]

/-- **The Steinberg relation** `[(a,1-a)] = 1`, for a unit `a` with `1 - a ≠ 0`. -/
theorem quaternionClass_one_sub (a : Kˣ) (h : (1 : K) - a ≠ 0) :
    quaternionClass a (Units.mk0 ((1 : K) - a) h) = 1 :=
  letI : Invertible ((1 : K) - a) := invertibleOfNonzero h
  quaternionClass_eq_one_of_algEquiv_matrix (QuaternionAlgebra.steinbergEquivMatrix (a : K))

/-! ### Bilinearity -/

/-- **Bilinearity of the quaternion symbol in the second argument**:
`[(a,bc)] = [(a,b)] · [(a,c)]`. This is the common slot lemma
`ℍ[K,a,b] ⊗[K] ℍ[K,a,c] ≃ₐ[K] ℍ[K,a,bc] ⊗[K] M₂(K)` read in the Brauer group. -/
@[simp]
theorem quaternionClass_mul (a b c : Kˣ) :
    quaternionClass a (b * c) = quaternionClass a b * quaternionClass a c :=
  calc quaternionClass a (b * c)
      = quaternionClass a (b * c) * mk (CSA.of K (Matrix (Fin 2) (Fin 2) K)) := by
        rw [mk_eq_one_iff.2 (isBrauerTrivial_matrix K 2), mul_one]
    _ = mk (CSA.tensorProduct (quaternionCSA a (b * c)) (CSA.of K (Matrix (Fin 2) (Fin 2) K))) :=
        (mk_tensorProduct _ _).symm
    _ = mk (CSA.tensorProduct (quaternionCSA a b) (quaternionCSA a c)) :=
        (mk_eq_mk_of_algEquiv (A := CSA.tensorProduct (quaternionCSA a b) (quaternionCSA a c))
          (B := CSA.tensorProduct (quaternionCSA a (b * c)) (CSA.of K (Matrix (Fin 2) (Fin 2) K)))
          (QuaternionAlgebra.tensorAlgEquivTensorMatrix a b c)).symm
    _ = quaternionClass a b * quaternionClass a c := mk_tensorProduct _ _

/-- **Bilinearity of the quaternion symbol in the first argument**:
`[(ab,c)] = [(a,c)] · [(b,c)]`. -/
@[simp]
theorem quaternionClass_mul_left (a b c : Kˣ) :
    quaternionClass (a * b) c = quaternionClass a c * quaternionClass b c := by
  rw [quaternionClass_comm, quaternionClass_mul, quaternionClass_comm a,
    quaternionClass_comm b]

/-- `[(a,a)] = [(a,-1)]`, since `a = (-1) · (-a)` and `[(a,-a)] = 1`. -/
theorem quaternionClass_self (a : Kˣ) : quaternionClass a a = quaternionClass a (-1) :=
  calc quaternionClass a a = quaternionClass a (-1 * -a) := by rw [neg_one_mul, neg_neg]
    _ = quaternionClass a (-1) * quaternionClass a (-a) := quaternionClass_mul a (-1) (-a)
    _ = quaternionClass a (-1) := by rw [quaternionClass_neg_self, mul_one]

/-! ### The symbol on square classes -/

private theorem quaternionClass_congr_squareClass_left {a b c : Kˣ}
    (h : squareClass a = squareClass b) : quaternionClass a c = quaternionClass b c := by
  obtain ⟨t, ht⟩ := (squareClass_eq_iff_isSquare_mul a b).mp h
  have hab : a = b * (t * b⁻¹) ^ 2 := by
    calc
      a = (a * b) * b⁻¹ := by group
      _ = t ^ 2 * b⁻¹ := by rw [ht, pow_two]
      _ = b * (t * b⁻¹) ^ 2 := by
        calc
          t ^ 2 * b⁻¹ = t ^ 2 * (b * (b⁻¹) ^ 2) := by congr 1; group
          _ = b * (t * b⁻¹) ^ 2 := by rw [mul_pow]; ac_rfl
  rw [hab, quaternionClass_mul_sq_left]

private theorem quaternionClass_congr_squareClass_right {a b c : Kˣ}
    (h : squareClass b = squareClass c) : quaternionClass a b = quaternionClass a c := by
  rw [quaternionClass_comm a b, quaternionClass_comm a c]
  exact quaternionClass_congr_squareClass_left h

/-- The quaternion symbol factored through the square classes of its two parameters. -/
noncomputable def quaternionClassOnSquareClasses (x y : SquareClassGroup K) : BrauerGroup K :=
  quaternionClass (Additive.toMul (Quotient.out x)) (Additive.toMul (Quotient.out y))

/-- The square-class pairing agrees with the quaternion symbol on representatives. -/
@[simp]
theorem quaternionClassOnSquareClasses_squareClass (a b : Kˣ) :
    quaternionClassOnSquareClasses (squareClass a) (squareClass b) = quaternionClass a b := by
  have hout (x : SquareClassGroup K) :
      squareClass (Additive.toMul (Quotient.out x)) = x := by
    rw [squareClass_def, ofMul_toMul]
    exact Quotient.out_eq x
  unfold quaternionClassOnSquareClasses
  rw [quaternionClass_congr_squareClass_left (hout (squareClass a)),
    quaternionClass_congr_squareClass_right (hout (squareClass b))]

/-! ### Invariance under isometry of binary forms -/

/-- **The quaternion symbol is an invariant of the binary form `⟨a,b⟩`**: isometric binary forms
have equal symbols. This is the binary quaternion lemma read in the Brauer group, and it is what
makes the Hasse invariant well defined on isometry classes. -/
theorem quaternionClass_congr {a b c d : Kˣ}
    (h : (weightedSumSquares K ![(a : K), b]).Equivalent (weightedSumSquares K ![(c : K), d])) :
    quaternionClass a b = quaternionClass c d :=
  let ⟨e⟩ := QuaternionAlgebra.nonempty_algEquiv_of_equivalent_binary (a : K) b c d h
  quaternionClass_eq_of_algEquiv e

end BrauerGroup

end TauCeti
