/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.BrauerClass
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Induction
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Descent
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.TensorProduct
import TauCeti.Algebra.BrauerGroup.Quaternion

/-!
# The Hasse invariant of a regular quadratic form

Over a field `K` in which two is invertible, a regular quadratic form `q` is diagonalizable,
`q ≅ ⟨a₁, …, aₙ⟩`, and its **Hasse invariant** is the product of quaternion symbols
`s(q) = ∏_{i<j} [(aᵢ, aⱼ)]` in the Brauer group of `K`, with the empty product in ranks `0`
and `1`. This is the convention of Lam (V.3.17) and of Serre's `ε` (*A Course in Arithmetic*,
IV.2.1); O'Meara's Hasse symbol `∏_{i≤j} (aᵢ, aⱼ)` differs from it by a correction term.

The invariant is defined on `TauCeti.RegularFormClass`, so it depends only on the isometry class
of the form. That the product does not depend on the chosen diagonalization is Witt's chain
theorem, through the descent principle `TauCeti.RegularFormClass.liftDiagonal`: the product is
unchanged by permuting the coefficients because the symbol is symmetric, and by replacing two
coefficients with those of an isometric binary form because the symbol is bilinear and takes
equal values on isometric binary forms (Lam V.3.18).

Every symbol is `2`-torsion, so the Hasse invariant takes values in the `2`-torsion of the Brauer
group. It is a genuine invariant beyond rank and discriminant: over `ℝ` the forms `⟨1, 1⟩` and
`⟨-1, -1⟩` have the same rank and the same discriminant, and different Hasse invariants.

## Main definitions

* `TauCeti.RegularFormClass.hasseInvariant`: the Hasse invariant of an isometry class of regular
  quadratic forms.

## Main results

* `TauCeti.RegularFormClass.hasseInvariant_mk`: its value `∏_{i<j} [(aᵢ, aⱼ)]` on a diagonal
  presentation `⟨a₁, …, aₙ⟩`.
* `TauCeti.RegularFormClass.hasseInvariant_formClass`: the same value on the class of any regular
  form isometric to `⟨a₁, …, aₙ⟩`.
* `TauCeti.RegularFormClass.hasseInvariant_eq_one_of_rank_le_one`: the invariant is trivial in
  ranks `0` and `1`, in particular on `0`, on `1` and on every `⟨a⟩`.
* `TauCeti.RegularFormClass.hasseInvariant_mk_binary`: `s⟨a, b⟩ = [(a, b)]`.
* `TauCeti.RegularFormClass.hasseInvariant_add_mk`: the orthogonal-sum formula on diagonal
  presentations.
* `TauCeti.RegularFormClass.hasseInvariant_add`: the formula for arbitrary classes, with its
  cross term expressed through their discriminants.
* `TauCeti.RegularFormClass.hasseInvariant_mk_scale`: the formula for scaling a diagonal
  presentation by a unit.
* `TauCeti.RegularFormClass.hasseInvariant_mk_rankOne_mul_mk`: the same scaling formula for
  multiplication by the rank-one class.
* `TauCeti.RegularFormClass.hasseInvariant_mk_rankOne_mul`: the scaling formula for any class.
* `TauCeti.RegularFormClass.hasseInvariant_hyperbolicClass`: the hyperbolic plane has trivial
  Hasse invariant.
* `TauCeti.RegularFormClass.hasseInvariant_sq`: the invariant is `2`-torsion.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, Definition 3.17 and Proposition 3.18.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer (1973),
  Chapter IV, §2.1.
-/

public section

open Finset QuadraticMap

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

namespace RegularFormClass

open BrauerGroup

private theorem hasseProd_eq_of_permutationStep {n : ℕ} {w w' : Fin n → Kˣ}
    (h : PermutationStep w w') :
    ∏ i, ∏ j ∈ Ioi i, quaternionClass (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, quaternionClass (w' i) (w' j) :=
  h.prod_prod_Ioi_eq quaternionClass_comm

private theorem hasseProd_eq_of_binaryStep {n : ℕ} {w w' : Fin n → Kˣ} (h : BinaryStep w w') :
    ∏ i, ∏ j ∈ Ioi i, quaternionClass (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, quaternionClass (w' i) (w' j) :=
  h.prod_prod_Ioi_eq quaternionClass_mul_left fun _ _ _ _ => quaternionClass_congr

private theorem hasseProd_rankOne (a b : Kˣ) :
    ∏ i : Fin 1, ∏ _j ∈ Ioi i, quaternionClass a a =
      ∏ i : Fin 1, ∏ _j ∈ Ioi i, quaternionClass b b := by
  simp

/-- The pairwise identity behind the scaling formula: scaling both parameters of a symbol by `a`
gives `[(ab, ac)] = [(b, c)] · [(a, -1)] · [(a, b)] · [(a, c)]`, by bilinearity and
`[(a, a)] = [(a, -1)]`. -/
private theorem quaternionClass_mul_mul (a b c : Kˣ) :
    quaternionClass (a * b) (a * c) =
      quaternionClass b c * quaternionClass a (-1) * quaternionClass a b * quaternionClass a c := by
  rw [quaternionClass_mul_left, quaternionClass_mul, quaternionClass_mul, quaternionClass_self,
    quaternionClass_comm b a]
  ac_rfl

/-- Scaling every coefficient by `a` multiplies the pair product by one `[(a, -1)]` per pair and,
since each coefficient lies in `n - 1` pairs, by `[(a, ∏ wᵢ)] ^ (n - 1)`. The induction appends a
last coefficient `b` to `w₀ : Fin n → Kˣ`: by `quaternionClass_mul_mul`, the `n` new pairs
contribute `[(a, -1)] ^ n · [(a, ∏ w₀ᵢ)] · [(a, b)] ^ n`, which is exactly the change in both
correction terms. -/
private theorem hasseProd_scale (a : Kˣ) {n : ℕ} (w : Fin n → Kˣ) :
    (∏ i, ∏ j ∈ Ioi i, quaternionClass (a * w i) (a * w j)) =
      (∏ i, ∏ j ∈ Ioi i, quaternionClass (w i) (w j)) *
        quaternionClass a (-1) ^ n.choose 2 *
        quaternionClass a (∏ i, w i) ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let w₀ := Fin.init w
    let b := w (Fin.last n)
    have hw : w = Fin.snoc w₀ b := (Fin.snoc_init_self w).symm
    rw [hw]
    have hs (i : Fin (n + 1)) :
        a * Fin.snoc (α := fun _ => Kˣ) w₀ b i =
          Fin.snoc (α := fun _ => Kˣ) (fun j => a * w₀ j) (a * b) i := by
      rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl <;> simp
    simp_rw [hs]
    let h₁ : Kˣ →* BrauerGroup K := {
      toFun := quaternionClass a
      map_one' := quaternionClass_one_right a
      map_mul' := quaternionClass_mul a }
    have hprod : (∏ i, quaternionClass a (w₀ i)) = quaternionClass a (∏ i, w₀ i) :=
      (map_prod h₁ w₀ Finset.univ).symm
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    rw [prod_prod_Ioi_snoc quaternionClass (fun j => a * w₀ j) (a * b),
      prod_prod_Ioi_snoc quaternionClass w₀ b, ih w₀, Fin.prod_snoc, Nat.add_sub_cancel]
    simp_rw [quaternionClass_mul_mul]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hprod, quaternionClass_mul, mul_pow, hchoose, pow_add]
    -- It remains to merge `[(a, ∏ w₀ᵢ)] ^ (n - 1)` from the induction hypothesis with the single
    -- `[(a, ∏ w₀ᵢ)]` from the new pairs; for `n = 0` that symbol is trivial.
    cases n with
    | zero => simp
    | succ n =>
      rw [Nat.add_sub_cancel, pow_succ (quaternionClass a (∏ i, w₀ i)) n]
      ac_nf
      rw [mul_left_comm (quaternionClass a (-1) ^ (n + 1))]

/-- **The Hasse invariant of an isometry class of regular quadratic forms**: for a diagonal
presentation `⟨a₁, …, aₙ⟩` of the class, the product `∏_{i<j} [(aᵢ, aⱼ)]` of quaternion symbols in
the Brauer group, which is `1` in ranks `0` and `1`. It does not depend on the presentation. -/
noncomputable def hasseInvariant : RegularFormClass K → BrauerGroup K :=
  liftDiagonal (fun p => ∏ i, ∏ j ∈ Ioi i, quaternionClass (p.2 i) (p.2 j))
    hasseProd_eq_of_permutationStep hasseProd_eq_of_binaryStep fun a b _ => hasseProd_rankOne a b

/-- The Hasse invariant of the class of a diagonal presentation `⟨a₁, …, aₙ⟩` is
`∏_{i<j} [(aᵢ, aⱼ)]`. -/
@[simp]
theorem hasseInvariant_mk (p : RegularFormPresentation K) :
    hasseInvariant (Quotient.mk (regularFormSetoid K) p) =
      ∏ i, ∏ j ∈ Ioi i, quaternionClass (p.2 i) (p.2 j) :=
  liftDiagonal_mk _ hasseProd_eq_of_permutationStep hasseProd_eq_of_binaryStep
    (fun a b _ => hasseProd_rankOne a b) p

/-- The Hasse invariant of a regular form isometric to `⟨a₁, …, aₙ⟩` is `∏_{i<j} [(aᵢ, aⱼ)]`. -/
theorem hasseInvariant_formClass {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {n : ℕ}
    (w : Fin n → Kˣ) (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    hasseInvariant (formClass Q hQ) = ∏ i, ∏ j ∈ Ioi i, quaternionClass (w i) (w j) := by
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]),
    hasseInvariant_mk]

/-- The Hasse invariant is trivial in ranks `0` and `1`. -/
theorem hasseInvariant_eq_one_of_rank_le_one {x : RegularFormClass K} (hx : x.rank ≤ 1) :
    hasseInvariant x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    rw [hasseInvariant_mk]
    refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
    have hij := Fin.lt_def.mp (mem_Ioi.mp hj)
    have hj := j.isLt
    omega

/-- The zero class has trivial Hasse invariant. -/
@[simp]
theorem hasseInvariant_zero : hasseInvariant (0 : RegularFormClass K) = 1 :=
  hasseInvariant_eq_one_of_rank_le_one (by simp)

/-- The unit class `⟨1⟩` has trivial Hasse invariant. -/
@[simp]
theorem hasseInvariant_one : hasseInvariant (1 : RegularFormClass K) = 1 :=
  hasseInvariant_eq_one_of_rank_le_one rank_one.le

/-- A rank-one form `⟨a⟩` has trivial Hasse invariant. -/
theorem hasseInvariant_mk_rankOne (a : Kˣ) :
    hasseInvariant (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = 1 :=
  hasseInvariant_eq_one_of_rank_le_one (by rw [rank_mk])

/-- The Hasse invariant of a binary form `⟨a, b⟩` is the quaternion symbol `[(a, b)]`. This takes
priority over `hasseInvariant_mk`, whose product the simplifier does not evaluate on `Fin 2`. -/
@[simp high]
theorem hasseInvariant_mk_binary (a b : Kˣ) :
    hasseInvariant (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) = quaternionClass a b := by
  rw [hasseInvariant_mk]
  simp [Fin.prod_univ_succ]

/-- **Orthogonal-sum formula** on diagonal presentations: the cross term is the quaternion
symbol of their coefficient products, which represent their discriminants. -/
theorem hasseInvariant_add_mk (p q : RegularFormPresentation K) :
    hasseInvariant (Quotient.mk (regularFormSetoid K) p +
      Quotient.mk (regularFormSetoid K) q) =
      hasseInvariant (Quotient.mk (regularFormSetoid K) p) *
        hasseInvariant (Quotient.mk (regularFormSetoid K) q) *
        quaternionClass (∏ i, p.2 i) (∏ j, q.2 j) := by
  let h₁ (a : Kˣ) : Kˣ →* BrauerGroup K := {
    toFun := quaternionClass a
    map_one' := quaternionClass_one_right a
    map_mul' := quaternionClass_mul a }
  let h₂ (b : Kˣ) : Kˣ →* BrauerGroup K := {
    toFun := fun a => quaternionClass a b
    map_one' := quaternionClass_one_left b
    map_mul' := fun a c => quaternionClass_mul_left a c b }
  have happend : p.append q = ⟨p.1 + q.1, Fin.append p.2 q.2⟩ := by
    let hfst := RegularFormPresentation.fst_append p q
    have hw : (p.append q).2 ∘ Fin.cast hfst.symm = Fin.append p.2 q.2 := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro k
        simpa only [Function.comp_apply, Fin.append_left] using
          RegularFormPresentation.append_apply_castAdd p q k
      · intro k
        simpa only [Function.comp_apply, Fin.append_right] using
          RegularFormPresentation.append_apply_natAdd p q k
    apply RegularFormPresentation.ext hfst
    intro i
    let j := Fin.cast hfst i
    have hi : i = Fin.cast hfst.symm j := Fin.ext rfl
    rw [hi]
    exact congrFun hw j
  rw [mk_add_mk, happend, hasseInvariant_mk, hasseInvariant_mk, hasseInvariant_mk]
  rw [prod_prod_Ioi_append]
  congr 1
  calc
    (∏ i, ∏ j, quaternionClass (p.2 i) (q.2 j)) =
        ∏ i, quaternionClass (p.2 i) (∏ j, q.2 j) := by
          apply Finset.prod_congr rfl
          intro i _
          exact (map_prod (h₁ (p.2 i)) q.2 Finset.univ).symm
    _ = quaternionClass (∏ i, p.2 i) (∏ j, q.2 j) :=
      (map_prod (h₂ (∏ j, q.2 j)) p.2 Finset.univ).symm

/-- **Scaling formula** on a diagonal presentation: the first correction counts coefficient
pairs, and the second uses the product of coefficients representing the discriminant. -/
theorem hasseInvariant_mk_scale (a : Kˣ) (p : RegularFormPresentation K) :
    hasseInvariant (Quotient.mk (regularFormSetoid K)
      ⟨p.1, fun i => a * p.2 i⟩) =
      hasseInvariant (Quotient.mk (regularFormSetoid K) p) *
        quaternionClass a (-1) ^ p.1.choose 2 *
        quaternionClass a (∏ i, p.2 i) ^ (p.1 - 1) := by
  rw [hasseInvariant_mk, hasseInvariant_mk]
  exact hasseProd_scale a p.2

/-- **Scaling by a rank-one class** is coefficientwise scaling of a diagonal presentation.
The Hasse-invariant correction is expressed through the presentation's rank and coefficient
product. -/
theorem hasseInvariant_mk_rankOne_mul_mk (a : Kˣ) (p : RegularFormPresentation K) :
    hasseInvariant (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ *
      Quotient.mk (regularFormSetoid K) p) =
      hasseInvariant (Quotient.mk (regularFormSetoid K) p) *
        quaternionClass a (-1) ^ p.1.choose 2 *
        quaternionClass a (∏ i, p.2 i) ^ (p.1 - 1) := by
  let r : RegularFormPresentation K := ⟨1, fun _ => a⟩
  have hrank : (r.tmul p).1 = p.1 := by simp [r]
  have hscale : r.tmul p = ⟨p.1, fun i => a * p.2 i⟩ := by
    refine RegularFormPresentation.ext (q := ⟨p.1, fun i => a * p.2 i⟩) hrank ?_
    intro i
    let j := Fin.cast hrank i
    have happly := RegularFormPresentation.tmul_apply r p (0 : Fin r.1) j
    have hi : Fin.cast (RegularFormPresentation.fst_tmul r p).symm
        (finProdFinEquiv (0, j)) = i := by
      apply Fin.ext
      simp [r, j, finProdFinEquiv]
    rw [hi] at happly
    simpa [r, j] using happly
  rw [mk_mul_mk, hscale, hasseInvariant_mk_scale]

/-- **Orthogonal-sum formula** for regular-form classes: the cross term is the quaternion
symbol of their discriminants. -/
theorem hasseInvariant_add (x y : RegularFormClass K) :
    hasseInvariant (x + y) = hasseInvariant x * hasseInvariant y *
      quaternionClassOnSquareClasses (discr x) (discr y) := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      simpa only [discr_mk, quaternionClassOnSquareClasses_squareClass] using
        hasseInvariant_add_mk p q

/-- **Scaling formula** for any regular-form class: multiplying by `⟨a⟩` changes the Hasse
invariant by a rank-dependent sign symbol and a symbol with its discriminant. -/
theorem hasseInvariant_mk_rankOne_mul (a : Kˣ) (x : RegularFormClass K) :
    hasseInvariant (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
      hasseInvariant x * quaternionClass a (-1) ^ (rank x).choose 2 *
        quaternionClassOnSquareClasses (squareClass a) (discr x) ^ (rank x - 1) := by
  induction x using Quotient.inductionOn with
  | h p =>
    simpa only [rank_mk, discr_mk, quaternionClassOnSquareClasses_squareClass] using
      hasseInvariant_mk_rankOne_mul_mk a p

/-- The hyperbolic plane `⟨1, -1⟩` has trivial Hasse invariant. -/
@[simp]
theorem hasseInvariant_hyperbolicClass : hasseInvariant (hyperbolicClass K) = 1 := by
  rw [hyperbolicClass_def, hasseInvariant_mk_binary, quaternionClass_one_left]

/-- The Hasse invariant is `2`-torsion: it lies in the `2`-torsion of the Brauer group. -/
@[simp]
theorem hasseInvariant_sq (x : RegularFormClass K) : hasseInvariant x ^ 2 = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [hasseInvariant_mk, ← prod_pow]
    refine prod_eq_one fun i _ => ?_
    rw [← prod_pow]
    exact prod_eq_one fun j _ => quaternionClass_sq _ _

end RegularFormClass

/-- **Worked example.** Over `ℝ` the binary forms `⟨1, 1⟩` and `⟨-1, -1⟩` have the same rank and
the same discriminant, and they are told apart by their Hasse invariants: `[(1, 1)]` is trivial,
while `[(-1, -1)]` is the class of Hamilton's quaternions, which is not. -/
example : RegularFormClass.hasseInvariant
      (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![(-1 : ℝˣ), -1]⟩) ≠
    RegularFormClass.hasseInvariant (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![(1 : ℝˣ), 1]⟩) := by
  rw [RegularFormClass.hasseInvariant_mk_binary, RegularFormClass.hasseInvariant_mk_binary,
    BrauerGroup.quaternionClass_one_left]
  simpa [BrauerGroup.quaternionClass_def] using Quaternion.mk_ne_one

end TauCeti
