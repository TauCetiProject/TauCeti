/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Chern
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

/-!
# The equivariant circle-algebra presentation

For a commutative ring `R`, the coefficient ring is `R[e₁, …, e_N]`. The algebra of an
`a`-labelled circle has two families of elementary generators `c₁, …, c_a` and
`b₁, …, b_(N-a)`, with the relations `c(t)b(t) = e(t)`, where all three constant
coefficients are one. These are algebraic presentations; no foam evaluation or geometric
cohomology is used here.

`CircleAlgebra.homEquiv` characterizes maps from the presentation by factorizations of the
coefficient polynomial. `CircleAlgebra.polynomialEquiv` eliminates the parameters `e_i`:
as an `R`-algebra, the quotient is a polynomial ring in the `c_i` and `b_j`. The action of
the equivariant coefficient ring is retained explicitly by the convolution formula
`CircleAlgebra.polynomialEquiv_e`. Thus this equivalence does not assert freeness over the
equivariant coefficient ring; that requires a separate rectangular Schur-basis theorem.

The elementary-generator presentation is the algebraic presentation of equivariant
Grassmannian cohomology, used for circle state spaces in H. Wu, *Equivariant colored
sl(N)-homology for links*, arXiv:1002.2662v2, §2.3.
-/

public section

noncomputable section

open MvPolynomial

namespace TauCeti

/-- The coefficient polynomial in the two elementary-generator families of a circle. -/
abbrev CirclePolynomial (R : Type*) [CommRing R] (N a : ℕ) :=
  MvPolynomial (Fin a ⊕ Fin (N - a)) (MvPolynomial (Fin N) R)

/-- The coefficient of degree `r+1` in `c(t)b(t) - e(t)`. -/
def circleRelation (R : Type*) [CommRing R] (N a : ℕ) (r : Fin N) : CirclePolynomial R N a :=
  (chernPolynomial (fun i : Fin a ↦ X (Sum.inl i)) *
    chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j))).coeff (r.val + 1) - C (X r)

/-- The defining ideal of the equivariant circle algebra, generated in degrees one to `N`. -/
def circleIdeal (R : Type*) [CommRing R] (N a : ℕ) : Ideal (CirclePolynomial R N a) :=
  Ideal.span (Set.range (circleRelation R N a))

/-- The elementary-generator presentation of the equivariant `a`-labelled circle algebra.
The coefficient ring is `MvPolynomial (Fin N) R`; the intended range is `a ≤ N`. -/
abbrev CircleAlgebra (R : Type*) [CommRing R] (N a : ℕ) :=
  CirclePolynomial R N a ⧸ circleIdeal R N a

namespace CircleAlgebra

variable {R : Type*} [CommRing R] {N a : ℕ}

/-- The class `c_(i+1)` of the first elementary-generator family. -/
def c (i : Fin a) : CircleAlgebra R N a := Ideal.Quotient.mk _ (X (Sum.inl i))

/-- The class `b_(j+1)` of the complementary elementary-generator family. -/
def b (j : Fin (N - a)) : CircleAlgebra R N a := Ideal.Quotient.mk _ (X (Sum.inr j))

/-- The equivariant parameter `e_(r+1)` acting on the circle algebra. -/
def e (r : Fin N) : CircleAlgebra R N a :=
  algebraMap (MvPolynomial (Fin N) R) _ (X r)

/-- The equivariant parameter is represented by its constant polynomial. -/
theorem e_eq_mk (r : Fin N) : e (R := R) (a := a) r =
    Ideal.Quotient.mk (circleIdeal R N a) (C (X r)) := (rfl)

/-- The defining convolution relation in the quotient. -/
theorem coeff_mul_chernPolynomial (r : Fin N) :
    (chernPolynomial (c (R := R) (N := N) (a := a)) * chernPolynomial b).coeff (r.val + 1) =
      e r := by
  let q := Ideal.Quotient.mk (circleIdeal R N a)
  have hrel : q (circleRelation R N a r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self r))
  have he : q (C (X r)) = e (R := R) (a := a) r := rfl
  have hmap := Polynomial.coeff_map (p :=
    chernPolynomial (fun i : Fin a ↦ X (Sum.inl i) : Fin a → CirclePolynomial R N a) *
      chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j))) (f := q) (r.val + 1)
  simp only [Polynomial.map_mul, RingHom.map_chernPolynomial] at hmap
  rw [circleRelation, map_sub, sub_eq_zero, he] at hrel
  exact hmap.trans hrel

/-- In the admissible range the defining relations are the full polynomial factorization. -/
theorem chernPolynomial_mul (ha : a ≤ N) :
    chernPolynomial (c (R := R) (N := N) (a := a)) * chernPolynomial b = chernPolynomial e := by
  ext i
  rcases i with _ | i
  · simp [Polynomial.mul_coeff_zero]
  · by_cases hi : i < N
    · rw [chernPolynomial_coeff_succ e ⟨i, hi⟩]
      exact coeff_mul_chernPolynomial ⟨i, hi⟩
    · rw [chernPolynomial_coeff_eq_zero _ (by omega : N < i + 1)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (le_trans (Polynomial.natDegree_mul_le ..)
          (Nat.add_le_add (natDegree_chernPolynomial_le _) (natDegree_chernPolynomial_le _)))
          (by omega))

/-- Maps over the equivariant coefficient ring are determined by the two Chern families. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra (MvPolynomial (Fin N) R) S]
    {f g : CircleAlgebra R N a →ₐ[MvPolynomial (Fin N) R] S}
    (hc : ∀ i, f (c i) = g (c i)) (hb : ∀ j, f (b j) = g (b j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro (i | j)
  · exact hc i
  · exact hb j

/-- Evaluate the circle presentation at two Chern families satisfying the factorization. -/
def lift {S : Type*} [CommRing S] [Algebra (MvPolynomial (Fin N) R) S]
    (x : Fin a → S) (y : Fin (N - a) → S)
    (h : chernPolynomial x * chernPolynomial y =
      chernPolynomial (fun r ↦ algebraMap (MvPolynomial (Fin N) R) S (X r))) :
    CircleAlgebra R N a →ₐ[MvPolynomial (Fin N) R] S :=
  Ideal.Quotient.liftₐ _ (aeval (Sum.elim x y)) (by
    intro p hp
    apply RingHom.mem_ker.mp
    apply (Ideal.span_le.mpr ?_ : circleIdeal R N a ≤ RingHom.ker (aeval (Sum.elim x y))) hp
    rintro _ ⟨r, rfl⟩
    apply RingHom.mem_ker.mpr
    have hr := congrArg (fun p : Polynomial S ↦ p.coeff (r.val + 1)) h
    simp only [chernPolynomial_coeff_succ] at hr
    rw [circleRelation, map_sub, aeval_C, sub_eq_zero]
    have hm := Polynomial.coeff_map (p :=
      chernPolynomial (fun i : Fin a ↦ X (Sum.inl i) : Fin a → CirclePolynomial R N a) *
        chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j)))
      (f := (aeval (Sum.elim x y)).toRingHom) (r.val + 1)
    simp only [Polynomial.map_mul, RingHom.map_chernPolynomial, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, aeval_X, Sum.elim_inl, Sum.elim_inr] at hm
    exact hm.symm.trans hr)

/-- Evaluation of a polynomial representative under the universal factorization map. -/
@[simp] theorem lift_mk {S : Type*} [CommRing S] [Algebra (MvPolynomial (Fin N) R) S]
    (x : Fin a → S) (y : Fin (N - a) → S) (h) (p : CirclePolynomial R N a) :
    lift (R := R) x y h (Ideal.Quotient.mk (circleIdeal R N a) p) =
      aeval (Sum.elim x y) p := (rfl)

@[simp] theorem lift_c {S : Type*} [CommRing S] [Algebra (MvPolynomial (Fin N) R) S]
    (x : Fin a → S) (y : Fin (N - a) → S) (h) (i : Fin a) : lift (R := R) x y h (c i) = x i := by
  rw [c, lift_mk]
  simp

@[simp] theorem lift_b {S : Type*} [CommRing S] [Algebra (MvPolynomial (Fin N) R) S]
    (x : Fin a → S) (y : Fin (N - a) → S) (h) (i : Fin (N - a)) :
    lift (R := R) x y h (b i) = y i := by
  rw [b, lift_mk]
  simp

/-- The universal property: coefficient-algebra maps are precisely factorizations with the
specified numbers of Chern coefficients and with constant terms one. -/
def homEquiv (ha : a ≤ N) (S : Type*) [CommRing S] [Algebra (MvPolynomial (Fin N) R) S] :
    (CircleAlgebra R N a →ₐ[MvPolynomial (Fin N) R] S) ≃
      {p : (Fin a → S) × (Fin (N - a) → S) //
        chernPolynomial p.1 * chernPolynomial p.2 =
          chernPolynomial (fun r ↦ algebraMap (MvPolynomial (Fin N) R) S (X r))} where
  toFun f := ⟨(fun i ↦ f (c i), fun j ↦ f (b j)), by
    have h := congrArg (Polynomial.map f.toRingHom) (chernPolynomial_mul (R := R) ha)
    simpa only [Polynomial.map_mul, RingHom.map_chernPolynomial, e,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] using h⟩
  invFun p := lift p.val.1 p.val.2 p.property
  left_inv f := by ext <;> simp
  right_inv p := by apply Subtype.ext; ext <;> simp

/-- The forward universal-property equivalence reads off the two Chern families. -/
@[simp] theorem homEquiv_apply_val (ha : a ≤ N) {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin N) R) S]
    (f : CircleAlgebra R N a →ₐ[MvPolynomial (Fin N) R] S) :
    (homEquiv ha S f).val = (fun i ↦ f (c i), fun j ↦ f (b j)) := (rfl)

/-- The inverse universal-property equivalence is evaluation at a factorization. -/
@[simp] theorem homEquiv_symm_apply (ha : a ≤ N) {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin N) R) S] (p) :
    (homEquiv (R := R) ha S).symm p = lift p.val.1 p.val.2 p.property := (rfl)

variable (R N a)

/-- Substitution for the equivariant parameters by the coefficients of the product of the
two universal Chern polynomials. This is the coefficient-ring action after elimination. -/
def parameterMap : MvPolynomial (Fin N) R →ₐ[R] MvPolynomial (Fin a ⊕ Fin (N - a)) R :=
  aeval fun r ↦
    (chernPolynomial (fun i : Fin a ↦ X (Sum.inl i)) *
      chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j))).coeff (r.val + 1)

@[simp] theorem parameterMap_X (r : Fin N) :
    parameterMap R N a (X r) =
      (chernPolynomial (fun i : Fin a ↦ X (Sum.inl i)) *
        chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j))).coeff (r.val + 1) := by
  simp [parameterMap]

/-- Substitute for the `e_i` in the polynomial presentation, leaving `c_i` and `b_j` free. -/
private def eliminatePolynomial :
    CirclePolynomial R N a →ₐ[R] MvPolynomial (Fin a ⊕ Fin (N - a)) R :=
  aevalTower (parameterMap R N a) X

private theorem eliminatePolynomial_relation (r : Fin N) :
    eliminatePolynomial R N a (circleRelation R N a r) = 0 := by
  have hm := Polynomial.coeff_map (p :=
    chernPolynomial (fun i : Fin a ↦ X (Sum.inl i) : Fin a → CirclePolynomial R N a) *
      chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j)))
    (f := (eliminatePolynomial R N a).toRingHom) (r.val + 1)
  simp only [Polynomial.map_mul, RingHom.map_chernPolynomial, eliminatePolynomial,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aevalTower_X] at hm
  rw [circleRelation, map_sub, sub_eq_zero]
  exact hm.symm.trans (by simp [eliminatePolynomial])

/-- The parameter-elimination map on the circle quotient. -/
private def eliminate : CircleAlgebra R N a →ₐ[R] MvPolynomial (Fin a ⊕ Fin (N - a)) R :=
  Ideal.Quotient.liftₐ _ (eliminatePolynomial R N a) (by
    intro p hp
    exact RingHom.mem_ker.mp ((Ideal.span_le.mpr (by
      rintro _ ⟨r, rfl⟩
      exact RingHom.mem_ker.mpr (eliminatePolynomial_relation R N a r))) hp))

/-- Parameter elimination on a polynomial representative is substitution in its coefficients. -/
@[simp] private theorem eliminate_mk (p : CirclePolynomial R N a) :
    eliminate R N a (Ideal.Quotient.mk (circleIdeal R N a) p) =
      aevalTower (parameterMap R N a) X p := (rfl)

/-- Include the polynomial ring in the two Chern families into the circle quotient. -/
private def includeChern : MvPolynomial (Fin a ⊕ Fin (N - a)) R →ₐ[R] CircleAlgebra R N a :=
  aeval (Sum.elim c b)

private theorem includeChern_parameterMap (r : Fin N) :
    includeChern R N a (parameterMap R N a (X r)) = e r := by
  have hm := Polynomial.coeff_map (p :=
    chernPolynomial (fun i : Fin a ↦ X (Sum.inl i)) *
      chernPolynomial (fun j : Fin (N - a) ↦ X (Sum.inr j)))
    (f := (includeChern R N a).toRingHom) (r.val + 1)
  simp only [Polynomial.map_mul, RingHom.map_chernPolynomial, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, includeChern, aeval_X, Sum.elim_inl, Sum.elim_inr] at hm
  rw [parameterMap_X]
  exact hm.symm.trans (coeff_mul_chernPolynomial r)

/-- Eliminating the equivariant parameters gives a polynomial algebra in the two Chern
families over `R`. The equivariant coefficient action is `parameterMap`, not scalar inclusion. -/
def polynomialEquiv : CircleAlgebra R N a ≃ₐ[R] MvPolynomial (Fin a ⊕ Fin (N - a)) R :=
  AlgEquiv.ofAlgHom (eliminate R N a) (includeChern R N a)
    (by ext (i | j) <;> simp [includeChern, c, b])
    (by
      apply Ideal.Quotient.algHom_ext
      refine MvPolynomial.algHom_ext' (R := R) (A := MvPolynomial (Fin N) R)
        (B := CircleAlgebra R N a) (σ := Fin a ⊕ Fin (N - a)) ?_ ?_
      · ext r
        simpa only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
          MvPolynomial.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk, eliminate_mk,
          aevalTower_C, AlgHom.id_apply, e_eq_mk] using
            includeChern_parameterMap R N a r
      · rintro (i | j) <;> simp [AlgHom.comp_apply, c, b, includeChern])

/-- On polynomial representatives the equivalence substitutes the convolution coefficients
for the equivariant parameters and leaves both Chern families unchanged. -/
theorem polynomialEquiv_mk (p : CirclePolynomial R N a) :
    polynomialEquiv R N a (Ideal.Quotient.mk (circleIdeal R N a) p) =
      aevalTower (parameterMap R N a) X p := eliminate_mk R N a p

@[simp] theorem polynomialEquiv_c (i : Fin a) :
    polynomialEquiv R N a (c i) = X (Sum.inl i) := by
  rw [c, polynomialEquiv_mk]
  simp

@[simp] theorem polynomialEquiv_b (i : Fin (N - a)) :
    polynomialEquiv R N a (b i) = X (Sum.inr i) := by
  rw [b, polynomialEquiv_mk]
  simp

/-- The `e_i` act as convolution polynomials after the parameter elimination. -/
@[simp] theorem polynomialEquiv_e (r : Fin N) :
    polynomialEquiv R N a (e r) = parameterMap R N a (X r) := by
  rw [e_eq_mk, polynomialEquiv_mk]
  simp

@[simp] theorem polynomialEquiv_symm_X_inl (i : Fin a) :
    (polynomialEquiv R N a).symm (X (Sum.inl i)) = c i := by
  simp [polynomialEquiv, includeChern]

@[simp] theorem polynomialEquiv_symm_X_inr (i : Fin (N - a)) :
    (polynomialEquiv R N a).symm (X (Sum.inr i)) = b i := by
  simp [polynomialEquiv, includeChern]

/-- The universal equivariant circle algebra is nontrivial over any nontrivial base ring. -/
instance [Nontrivial R] : Nontrivial (CircleAlgebra R N a) :=
  (polynomialEquiv R N a).toEquiv.nontrivial

/-- Over a domain, the universal equivariant circle algebra is a domain. This concerns the
universal parameters; specialized circle algebras may have nilpotents. -/
instance [IsDomain R] : IsDomain (CircleAlgebra R N a) :=
  (polynomialEquiv R N a).injective.isDomain (polynomialEquiv R N a)

end CircleAlgebra

end TauCeti
