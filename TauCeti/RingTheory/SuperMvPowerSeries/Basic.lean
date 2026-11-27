/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Formal power series in supercommuting variables

Let `Γ` be a linearly ordered set of labels, each with a parity `par γ : ZMod 2`, and let `Q` be an
`R`-algebra with an `R`-algebra endomorphism `σ`, typically the parity involution of a
superalgebra, which is `1` on even and `-1` on odd elements (for a `ℤ`-graded algebra this is
`TauCeti.InternalGrading.koszulTwistAlgEquiv 𝒜 1`). This file constructs the ring
`TauCeti.SuperMvPowerSeries par σ` of formal power series `∑_J a_J p^J` in variables `p_γ`,
`γ ∈ Γ`, with coefficients `a_J ∈ Q` written to the left of the normal-ordered monomials `p^J`.
The variables supercommute: `p_γ p_η = (-1) ^ (par γ * par η) p_η p_γ`, so odd variables square to
zero and only *odd-squarefree* monomials `J` (`TauCeti.OddSquarefree`) carry coefficients. A
variable passes a coefficient on its right through the twist `σ`: `p_γ a = σ a p_γ` for odd `γ`.

Concretely, an element is a coefficient function on all monomials `J : Γ →₀ ℕ`, with arbitrary
(possibly infinite) support among the odd-squarefree monomials and zero elsewhere. The product is
the twisted Cauchy product

`(f * g)_J = ∑_{K + L = J} (-1) ^ ε(K, L) • f_K * σ ^ |K|₁ (g_L)`

over the finite antidiagonal of `J`, where `ε(K, L)` (`TauCeti.koszulExponent`) counts the pairs of
an odd variable of `K` and a smaller odd variable of `L`, the swaps needed to normal-order
`p^K p^L`, and `|K|₁` (`TauCeti.oddDegree`) is the number of odd variables in `K`. Every
coefficient of a product is thus a finite sum, even with infinitely many labels and series with
infinitely many monomials of each word length; the coefficients in word length below `m + n` of a
product vanish when those of the factors vanish below `m` and `n`
(`TauCeti.SuperMvPowerSeries.coeff_mul_eq_zero_of_degree_lt`), so the word-length filtration is
multiplicative; the word-length topology itself is not introduced here. Only the variables are
completed: the coefficients `a_J` are arbitrary elements of `Q`.

In rational symplectic field theory, with `Γ` the good Reeb orbits, `p_γ` the variables of the
positive ends and `Q` the supercommutative algebra of polynomials in the variables `q_γ`, this is
the normal-ordered carrier of formal `p`-series with polynomial `q`-coefficients on which the
Poisson and Weyl formalisms are built (Eliashberg–Givental–Hofer, §2.2; Latschev, §2.1). The
formal power series in `ℏ` over it are Mathlib's `PowerSeries (SuperMvPowerSeries par σ)`.

## Main definitions

* `TauCeti.OddSquarefree par J`: every odd variable occurs in the monomial `J` at most once.
* `TauCeti.oddDegree par`, `TauCeti.koszulExponent par`: the number of odd variables of a
  monomial, and the Koszul exponent of a pair of monomials.
* `TauCeti.SuperMvPowerSeries par σ`: the ring of power series, an `R`-algebra.
* `TauCeti.SuperMvPowerSeries.monomial J`, `TauCeti.SuperMvPowerSeries.C`,
  `TauCeti.SuperMvPowerSeries.X γ`: monomials, constants and variables.

## Main results

* `TauCeti.SuperMvPowerSeries.coeff_mul`: the coefficients of a product are finite sums.
* `TauCeti.SuperMvPowerSeries.monomial_mul_monomial`: the signed product of monomials.
* `TauCeti.SuperMvPowerSeries.X_mul_X`: the variables supercommute, and
  `TauCeti.SuperMvPowerSeries.X_mul_self` odd variables square to zero.
* `TauCeti.SuperMvPowerSeries.X_mul_C_of_odd`, `TauCeti.SuperMvPowerSeries.commute_X_C_of_even`:
  moving a coefficient past a variable.
* `TauCeti.SuperMvPowerSeries.coeff_mul_eq_zero_of_degree_lt`: the word-length filtration is
  multiplicative.

## References

* Y. Eliashberg, A. Givental and H. Hofer, *Introduction to symplectic field theory*, Geom. Funct.
  Anal. (2000), Special Volume, Part II, 560–673, §2.2.
* J. Latschev, *Remarks on the rational SFT formalism*, arXiv:2212.01814, §2.1.
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {Γ : Type*} (par : Γ → ZMod 2)

/-! ### Odd-squarefree monomials and Koszul exponents -/

/-- A monomial `J` is *odd-squarefree* for the parity `par` when every odd variable occurs in it at
most once. These are the monomials whose normal-ordered product of supercommuting variables does
not vanish. -/
def OddSquarefree (J : Γ →₀ ℕ) : Prop :=
  ∀ γ, par γ = 1 → J γ ≤ 1

variable {par}

theorem oddSquarefree_iff {J : Γ →₀ ℕ} : OddSquarefree par J ↔ ∀ γ, par γ = 1 → J γ ≤ 1 :=
  Iff.rfl

theorem OddSquarefree.mono {J K : Γ →₀ ℕ} (hJ : OddSquarefree par J) (hK : K ≤ J) :
    OddSquarefree par K :=
  fun γ hγ => (hK γ).trans (hJ γ hγ)

variable (par)

@[simp]
theorem oddSquarefree_zero : OddSquarefree par (0 : Γ →₀ ℕ) :=
  fun _ _ => by simp

theorem oddSquarefree_single_one (γ : Γ) : OddSquarefree par (Finsupp.single γ 1) :=
  fun η _ => by classical rw [Finsupp.single_apply]; split_ifs <;> simp

/-- An odd variable squared is not odd-squarefree. -/
theorem not_oddSquarefree_single_add_single {γ : Γ} (hγ : par γ = 1) :
    ¬OddSquarefree par (Finsupp.single γ 1 + Finsupp.single γ 1) :=
  fun h => by simpa using h γ hγ

/-- The number of odd variables in a monomial, counted with multiplicity. -/
def oddDegree : (Γ →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun γ => if par γ = 1 then 1 else 0

theorem oddDegree_apply (J : Γ →₀ ℕ) :
    oddDegree par J = J.sum fun γ n => if par γ = 1 then n else 0 := by
  simp [oddDegree, Finsupp.weight_apply]

@[simp]
theorem oddDegree_single (γ : Γ) (n : ℕ) :
    oddDegree par (Finsupp.single γ n) = if par γ = 1 then n else 0 := by
  simp [oddDegree, Finsupp.weight_single]

section koszulExponent

variable [LinearOrder Γ]

/-- The Koszul exponent of a pair of monomials `K` and `L`: the number of pairs of an odd variable
of `K` and a strictly smaller odd variable of `L`, counted with multiplicity. It is the number of
transpositions of odd variables needed to normal-order `p^K p^L`, so that
`p^K p^L = (-1) ^ koszulExponent par K L • p^(K + L)`. -/
def koszulExponent : (Γ →₀ ℕ) →+ (Γ →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom fun γ => (Finsupp.liftAddHom fun η =>
    if η < γ ∧ par γ = 1 ∧ par η = 1 then AddMonoidHom.mul else 0).flip

theorem koszulExponent_apply (K L : Γ →₀ ℕ) :
    koszulExponent par K L = K.sum fun γ m => L.sum fun η n =>
      if η < γ ∧ par γ = 1 ∧ par η = 1 then n * m else 0 := by
  simp only [koszulExponent, Finsupp.liftAddHom_apply, AddMonoidHom.flip_apply, Finsupp.sum,
    AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun η _ => ?_
  split_ifs <;> simp

@[simp]
theorem koszulExponent_single_single (γ η : Γ) (m n : ℕ) :
    koszulExponent par (Finsupp.single γ m) (Finsupp.single η n) =
      if η < γ ∧ par γ = 1 ∧ par η = 1 then n * m else 0 := by
  simp only [koszulExponent, Finsupp.liftAddHom_apply_single, AddMonoidHom.flip_apply]
  split_ifs <;> simp

end koszulExponent

/-! ### The ring of power series -/

variable {R Q : Type*} [CommSemiring R] [Ring Q] [Algebra R Q]

/-- Formal power series `∑_J a_J p^J` in supercommuting variables `p_γ` of parity `par γ`, with
coefficients `a_J` in `Q` written to the left of the normal-ordered monomials `p^J`. A variable
passes a coefficient on its right through `σ`: `p_γ a = σ a p_γ` for odd `γ`.

The coefficient function `coeff` is arbitrary on odd-squarefree monomials and zero on the others,
where the corresponding monomial vanishes. -/
@[ext]
structure SuperMvPowerSeries (σ : Q →ₐ[R] Q) where
  /-- The coefficient of the monomial `p^J`. -/
  coeff : (Γ →₀ ℕ) → Q
  /-- A coefficient at a monomial that is not odd-squarefree vanishes. -/
  coeff_eq_zero_of_not_oddSquarefree {J : Γ →₀ ℕ} : ¬OddSquarefree par J → coeff J = 0

namespace SuperMvPowerSeries

variable {par} {σ : Q →ₐ[R] Q}

theorem coeff_injective : Function.Injective (coeff (Q := Q) (par := par) (σ := σ)) :=
  fun _ _ => SuperMvPowerSeries.ext

/-- Two power series agree once their coefficients agree on the odd-squarefree monomials, since
both vanish on the others. -/
theorem ext_of_oddSquarefree {x y : SuperMvPowerSeries par σ}
    (h : ∀ J, OddSquarefree par J → x.coeff J = y.coeff J) : x = y := by
  ext J
  by_cases hJ : OddSquarefree par J
  · exact h J hJ
  · rw [x.coeff_eq_zero_of_not_oddSquarefree hJ, y.coeff_eq_zero_of_not_oddSquarefree hJ]

/-! #### Additive structure -/

instance : Zero (SuperMvPowerSeries par σ) :=
  ⟨⟨0, fun _ => rfl⟩⟩

instance : Add (SuperMvPowerSeries par σ) :=
  ⟨fun x y => ⟨x.coeff + y.coeff, fun hJ => by
    simp [x.coeff_eq_zero_of_not_oddSquarefree hJ, y.coeff_eq_zero_of_not_oddSquarefree hJ]⟩⟩

instance : Neg (SuperMvPowerSeries par σ) :=
  ⟨fun x => ⟨-x.coeff, fun hJ => by simp [x.coeff_eq_zero_of_not_oddSquarefree hJ]⟩⟩

instance : Sub (SuperMvPowerSeries par σ) :=
  ⟨fun x y => ⟨x.coeff - y.coeff, fun hJ => by
    simp [x.coeff_eq_zero_of_not_oddSquarefree hJ, y.coeff_eq_zero_of_not_oddSquarefree hJ]⟩⟩

instance {S : Type*} [SMulZeroClass S Q] : SMul S (SuperMvPowerSeries par σ) :=
  ⟨fun s x => ⟨s • x.coeff, fun hJ => by simp [x.coeff_eq_zero_of_not_oddSquarefree hJ]⟩⟩

@[simp]
theorem coeff_zero (J : Γ →₀ ℕ) : (0 : SuperMvPowerSeries par σ).coeff J = 0 := (rfl)

@[simp]
theorem coeff_add (x y : SuperMvPowerSeries par σ) (J : Γ →₀ ℕ) :
    (x + y).coeff J = x.coeff J + y.coeff J := (rfl)

@[simp]
theorem coeff_neg (x : SuperMvPowerSeries par σ) (J : Γ →₀ ℕ) :
    (-x).coeff J = -x.coeff J := (rfl)

@[simp]
theorem coeff_sub (x y : SuperMvPowerSeries par σ) (J : Γ →₀ ℕ) :
    (x - y).coeff J = x.coeff J - y.coeff J := (rfl)

@[simp]
theorem coeff_smul {S : Type*} [SMulZeroClass S Q] (s : S) (x : SuperMvPowerSeries par σ)
    (J : Γ →₀ ℕ) : (s • x).coeff J = s • x.coeff J := (rfl)

instance : AddCommGroup (SuperMvPowerSeries par σ) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module R (SuperMvPowerSeries par σ) :=
  coeff_injective.module R ⟨⟨coeff, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

/-! #### Monomials -/

variable (par σ) in
/-- The monomial `a p^J`, which is zero when `J` is not odd-squarefree. -/
def monomial (J : Γ →₀ ℕ) : Q →ₗ[R] SuperMvPowerSeries par σ where
  toFun a := by
    classical
    exact ⟨fun K => if OddSquarefree par K ∧ K = J then a else 0,
      fun hK => ite_eq_right fun h => hK h.1⟩
  map_add' a b := by
    ext K
    simp only [coeff_add]
    split_ifs <;> simp
  map_smul' r a := by
    ext K
    simp only [coeff_smul, RingHom.id_apply]
    split_ifs <;> simp

@[simp]
theorem coeff_monomial_same {J : Γ →₀ ℕ} (hJ : OddSquarefree par J) (a : Q) :
    (monomial par σ J a).coeff J = a :=
  ite_eq_left ⟨hJ, rfl⟩

theorem coeff_monomial_ne {J K : Γ →₀ ℕ} (h : K ≠ J) (a : Q) :
    (monomial par σ J a).coeff K = 0 :=
  ite_eq_right fun h' => h h'.2

theorem coeff_monomial [DecidableEq Γ] {K : Γ →₀ ℕ} (hK : OddSquarefree par K) (J : Γ →₀ ℕ)
    (a : Q) : (monomial par σ J a).coeff K = if K = J then a else 0 := by
  split_ifs with h
  · exact h ▸ coeff_monomial_same hK a
  · exact coeff_monomial_ne h a

theorem monomial_eq_zero_of_not_oddSquarefree {J : Γ →₀ ℕ} (hJ : ¬OddSquarefree par J) (a : Q) :
    monomial par σ J a = 0 := by
  ext K
  by_cases hK : K = J
  · exact coeff_eq_zero_of_not_oddSquarefree _ (hK ▸ hJ)
  · exact coeff_monomial_ne hK a

variable (par σ) in
/-- The variable `p_γ`. -/
def X (γ : Γ) : SuperMvPowerSeries par σ :=
  monomial par σ (Finsupp.single γ 1) 1

theorem X_def (γ : Γ) : X par σ γ = monomial par σ (Finsupp.single γ 1) 1 := (rfl)

@[simp]
theorem coeff_X_same (γ : Γ) : (X par σ γ).coeff (Finsupp.single γ 1) = 1 :=
  coeff_monomial_same (oddSquarefree_single_one par γ) 1

theorem coeff_X_ne {γ : Γ} {J : Γ →₀ ℕ} (hJ : J ≠ Finsupp.single γ 1) :
    (X par σ γ).coeff J = 0 :=
  coeff_monomial_ne hJ 1

theorem coeff_X [DecidableEq Γ] (γ : Γ) (J : Γ →₀ ℕ) :
    (X par σ γ).coeff J = if J = Finsupp.single γ 1 then 1 else 0 := by
  split_ifs with h
  · exact h ▸ coeff_X_same γ
  · exact coeff_X_ne h

instance : One (SuperMvPowerSeries par σ) :=
  ⟨monomial par σ 0 1⟩

theorem one_def : (1 : SuperMvPowerSeries par σ) = monomial par σ 0 1 := (rfl)

@[simp]
theorem coeff_one [DecidableEq Γ] (J : Γ →₀ ℕ) :
    (1 : SuperMvPowerSeries par σ).coeff J = if J = 0 then 1 else 0 := by
  split_ifs with h
  · exact h ▸ coeff_monomial_same (oddSquarefree_zero par) 1
  · exact coeff_monomial_ne h 1

/-! #### Multiplication -/

variable [LinearOrder Γ]

/-- The twisted Cauchy product of two coefficient functions at the monomial `J`. -/
private def mulCoeff (f g : (Γ →₀ ℕ) → Q) (J : Γ →₀ ℕ) : Q :=
  ∑ p ∈ antidiagonal J,
    ((-1 : ℤˣ) ^ koszulExponent par p.1 p.2) • (f p.1 * (σ ^ oddDegree par p.1) (g p.2))

/-- The twisted Cauchy product at `J` only depends on the coefficients below `J`. -/
private theorem mulCoeff_congr {f f' g g' : (Γ →₀ ℕ) → Q} {J : Γ →₀ ℕ}
    (hf : ∀ K ≤ J, f K = f' K) (hg : ∀ K ≤ J, g K = g' K) :
    mulCoeff (par := par) (σ := σ) f g J = mulCoeff (par := par) (σ := σ) f' g' J :=
  sum_congr rfl fun p hp => by
    rw [hf _ (HasAntidiagonal.antidiagonal.fst_le hp),
      hg _ (HasAntidiagonal.antidiagonal.snd_le hp)]

/-- The summands of the two bracketings of a triple twisted product agree. -/
private theorem mulCoeff_assoc_summand (f g h : (Γ →₀ ℕ) → Q) (i j k : Γ →₀ ℕ) :
    ((-1 : ℤˣ) ^ koszulExponent par (i + j) k) •
        (((-1 : ℤˣ) ^ koszulExponent par i j) • (f i * (σ ^ oddDegree par i) (g j)) *
          (σ ^ oddDegree par (i + j)) (h k)) =
      ((-1 : ℤˣ) ^ koszulExponent par i (j + k)) •
        (f i * (σ ^ oddDegree par i) (((-1 : ℤˣ) ^ koszulExponent par j k) •
          (g j * (σ ^ oddDegree par j) (h k)))) := by
  simp only [map_zsmul_unit, map_mul, map_add, AddMonoidHom.add_apply, pow_add, AlgHom.mul_apply,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  simp only [mul_comm, mul_left_comm]

/-- Associativity of the twisted Cauchy product. The reindexing of the double antidiagonal is
adapted from the proof of `MvPowerSeries.mul_assoc` in Mathlib. -/
private theorem mulCoeff_assoc (f g h : (Γ →₀ ℕ) → Q) (J : Γ →₀ ℕ) :
    mulCoeff (par := par) (σ := σ) (mulCoeff (par := par) (σ := σ) f g) h J =
      mulCoeff (par := par) (σ := σ) f (mulCoeff (par := par) (σ := σ) g h) J := by
  simp only [mulCoeff, sum_mul, smul_sum, map_sum, mul_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨k, _m⟩, ⟨l, j⟩⟩ ↦ ⟨(k + l, j), (k, l)⟩)
  · aesop (add simp [add_assoc])
  · aesop (add simp [add_assoc])
  · aesop
  · aesop
  · rintro ⟨⟨_, j⟩, ⟨k, l⟩⟩ hp
    obtain ⟨-, rfl⟩ : _ ∧ k + l = _ := by simpa using hp
    exact mulCoeff_assoc_summand f g h k l j

open scoped Classical in
instance : Mul (SuperMvPowerSeries par σ) :=
  ⟨fun x y => ⟨fun J => if OddSquarefree par J then ∑ p ∈ antidiagonal J,
      ((-1 : ℤˣ) ^ koszulExponent par p.1 p.2) •
        (x.coeff p.1 * (σ ^ oddDegree par p.1) (y.coeff p.2))
    else 0, fun hJ => ite_eq_right hJ⟩⟩

/-- **The coefficients of a product are finite sums.** At an odd-squarefree monomial `J`, the
coefficient of `x * y` is the signed, twisted sum over the finitely many ways of writing `J` as a
sum `K + L`. -/
theorem coeff_mul (x y : SuperMvPowerSeries par σ) {J : Γ →₀ ℕ} (hJ : OddSquarefree par J) :
    (x * y).coeff J = ∑ p ∈ antidiagonal J, ((-1 : ℤˣ) ^ koszulExponent par p.1 p.2) •
      (x.coeff p.1 * (σ ^ oddDegree par p.1) (y.coeff p.2)) :=
  ite_eq_left hJ

private theorem coeff_monomial_zero_mul (a : Q) (x : SuperMvPowerSeries par σ) (J : Γ →₀ ℕ) :
    (monomial par σ 0 a * x).coeff J = a * x.coeff J := by
  by_cases hJ : OddSquarefree par J
  · rw [coeff_mul _ _ hJ, sum_eq_single (0, J)]
    · simp
    · rintro ⟨i, j⟩ hp hne
      have hi : i ≠ 0 := by
        rintro rfl
        exact hne (by simpa using hp)
      simp [coeff_monomial_ne hi]
    · simp
  · simp [coeff_eq_zero_of_not_oddSquarefree _ hJ]

private theorem coeff_mul_monomial_zero (x : SuperMvPowerSeries par σ) (a : Q) (J : Γ →₀ ℕ) :
    (x * monomial par σ 0 a).coeff J = x.coeff J * (σ ^ oddDegree par J) a := by
  by_cases hJ : OddSquarefree par J
  · rw [coeff_mul _ _ hJ, sum_eq_single (J, 0)]
    · simp
    · rintro ⟨i, j⟩ hp hne
      have hj : j ≠ 0 := by
        rintro rfl
        exact hne (by simpa using hp)
      simp [coeff_monomial_ne hj]
    · simp
  · simp [coeff_eq_zero_of_not_oddSquarefree _ hJ]

instance : Ring (SuperMvPowerSeries par σ) where
  __ := (inferInstance : AddCommGroup (SuperMvPowerSeries par σ))
  mul_assoc x y z := ext_of_oddSquarefree fun J hJ => by
    rw [coeff_mul _ _ hJ, coeff_mul _ _ hJ]
    -- The sums produced by `coeff_mul` are `mulCoeff` unfolded.
    change mulCoeff (par := par) (σ := σ) (x * y).coeff z.coeff J =
      mulCoeff (par := par) (σ := σ) x.coeff (y * z).coeff J
    rw [mulCoeff_congr (f' := mulCoeff (par := par) (σ := σ) x.coeff y.coeff)
        (fun K hK => coeff_mul x y (hJ.mono hK)) fun _ _ => rfl, mulCoeff_assoc,
      mulCoeff_congr (g := mulCoeff (par := par) (σ := σ) y.coeff z.coeff) (fun _ _ => rfl)
        fun K hK => (coeff_mul y z (hJ.mono hK)).symm]
  one_mul x := by
    ext J
    exact (coeff_monomial_zero_mul 1 x J).trans (one_mul _)
  mul_one x := by
    ext J
    exact (coeff_mul_monomial_zero x 1 J).trans (by rw [map_one, mul_one])
  left_distrib x y z := ext_of_oddSquarefree fun J hJ => by
    simp only [coeff_mul _ _ hJ, coeff_add, map_add, mul_add, smul_add, sum_add_distrib]
  right_distrib x y z := ext_of_oddSquarefree fun J hJ => by
    simp only [coeff_mul _ _ hJ, coeff_add, add_mul, smul_add, sum_add_distrib]
  zero_mul x := ext_of_oddSquarefree fun J hJ => by simp [coeff_mul _ _ hJ]
  mul_zero x := ext_of_oddSquarefree fun J hJ => by simp [coeff_mul _ _ hJ]

instance : Algebra R (SuperMvPowerSeries par σ) :=
  Algebra.ofModule
    (fun r x y => ext_of_oddSquarefree fun J hJ => by
      simp only [coeff_mul _ _ hJ, coeff_smul, smul_mul_assoc, smul_sum]
      exact sum_congr rfl fun _ _ => smul_comm _ _ _)
    (fun r x y => ext_of_oddSquarefree fun J hJ => by
      simp only [coeff_mul _ _ hJ, coeff_smul, map_smul, mul_smul_comm, smul_sum]
      exact sum_congr rfl fun _ _ => smul_comm _ _ _)

/-- **The product of two monomials.** `a p^J * b p^K = (-1) ^ ε(J, K) • (a σ^|J|₁(b)) p^(J + K)`,
which vanishes when `J + K` is not odd-squarefree. -/
theorem monomial_mul_monomial (J K : Γ →₀ ℕ) (a b : Q) :
    monomial par σ J a * monomial par σ K b =
      ((-1 : ℤˣ) ^ koszulExponent par J K) •
        monomial par σ (J + K) (a * (σ ^ oddDegree par J) b) := by
  refine ext_of_oddSquarefree fun L hL => ?_
  rw [coeff_mul _ _ hL, coeff_smul]
  by_cases hJK : L = J + K
  · subst hJK
    rw [sum_eq_single (J, K), coeff_monomial_same hL,
      coeff_monomial_same (hL.mono le_self_add), coeff_monomial_same (hL.mono le_add_self)]
    · rintro ⟨i, j⟩ hp hne
      rcases eq_or_ne i J with rfl | hi
      · have hj : j ≠ K := fun hj => hne (by rw [hj])
        simp [coeff_monomial_ne hj]
      · simp [coeff_monomial_ne hi]
    · simp
  · rw [coeff_monomial_ne hJK, smul_zero]
    refine sum_eq_zero fun ⟨i, j⟩ hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rcases eq_or_ne i J with rfl | hi
    · have hj : j ≠ K := by rintro rfl; exact hJK hp.symm
      simp [coeff_monomial_ne hj]
    · simp [coeff_monomial_ne hi]

/-! #### Constants and variables -/

variable (par σ) in
/-- The constant power series `a = a p^0`. -/
def C : Q →+* SuperMvPowerSeries par σ where
  toFun := monomial par σ 0
  map_one' := rfl
  map_mul' a b := by simp [monomial_mul_monomial]
  map_zero' := map_zero _
  map_add' := map_add _

theorem C_apply (a : Q) : C par σ a = monomial par σ 0 a := (rfl)

@[simp]
theorem coeff_zero_C (a : Q) : (C par σ a).coeff 0 = a :=
  coeff_monomial_same (oddSquarefree_zero par) a

theorem coeff_C_of_ne_zero {J : Γ →₀ ℕ} (hJ : J ≠ 0) (a : Q) : (C par σ a).coeff J = 0 :=
  coeff_monomial_ne hJ a

theorem coeff_C [DecidableEq Γ] (J : Γ →₀ ℕ) (a : Q) :
    (C par σ a).coeff J = if J = 0 then a else 0 := by
  split_ifs with h
  · exact h ▸ coeff_zero_C a
  · exact coeff_C_of_ne_zero h a

/-- Left multiplication by a constant `a` multiplies every coefficient on the left by `a`. -/
@[simp]
theorem coeff_C_mul (a : Q) (x : SuperMvPowerSeries par σ) (J : Γ →₀ ℕ) :
    (C par σ a * x).coeff J = a * x.coeff J :=
  coeff_monomial_zero_mul a x J

/-- Right multiplication by a constant `a` multiplies the coefficient of `p^J` on the right by the
twist of `a` by the odd variables of `J`. -/
@[simp]
theorem coeff_mul_C (x : SuperMvPowerSeries par σ) (a : Q) (J : Γ →₀ ℕ) :
    (x * C par σ a).coeff J = x.coeff J * (σ ^ oddDegree par J) a :=
  coeff_mul_monomial_zero x a J

theorem algebraMap_apply (r : R) :
    algebraMap R (SuperMvPowerSeries par σ) r = C par σ (algebraMap R Q r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, C_apply, map_smul, one_def]

theorem C_mul_monomial (a b : Q) (J : Γ →₀ ℕ) :
    C par σ a * monomial par σ J b = monomial par σ J (a * b) := by
  simp [C_apply, monomial_mul_monomial]

theorem monomial_mul_C (J : Γ →₀ ℕ) (a b : Q) :
    monomial par σ J a * C par σ b = monomial par σ J (a * (σ ^ oddDegree par J) b) := by
  simp [C_apply, monomial_mul_monomial]

theorem C_mul_X (a : Q) (γ : Γ) :
    C par σ a * X par σ γ = monomial par σ (Finsupp.single γ 1) a := by
  rw [X_def, C_mul_monomial, mul_one]

/-- An odd variable moves past a coefficient on its right by applying `σ` to it. -/
theorem X_mul_C_of_odd {γ : Γ} (hγ : par γ = 1) (a : Q) :
    X par σ γ * C par σ a = C par σ (σ a) * X par σ γ := by
  rw [C_mul_X, X_def, monomial_mul_C, one_mul]
  simp [hγ]

/-- An even variable commutes with every coefficient. -/
theorem commute_X_C_of_even {γ : Γ} (hγ : par γ = 0) (a : Q) :
    Commute (X par σ γ) (C par σ a) := by
  rw [Commute, SemiconjBy, C_mul_X, X_def, monomial_mul_C, one_mul]
  simp [hγ]

/-- **Odd variables square to zero.** -/
theorem X_mul_self {γ : Γ} (hγ : par γ = 1) : X par σ γ * X par σ γ = 0 := by
  rw [X_def, monomial_mul_monomial,
    monomial_eq_zero_of_not_oddSquarefree (not_oddSquarefree_single_add_single par hγ), smul_zero]

/-- **The variables supercommute**: `p_γ p_η = (-1) ^ (par γ * par η) p_η p_γ`. -/
theorem X_mul_X (γ η : Γ) :
    X par σ γ * X par σ η = ((-1 : ℤˣ) ^ (par γ * par η)) • (X par σ η * X par σ γ) := by
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases eq_or_ne γ η with rfl | hne
  · rcases h2 (par γ) with hγ | hγ
    · simp [hγ]
    · simp [X_mul_self hγ]
  · simp only [X_def, monomial_mul_monomial, one_mul, map_one, smul_smul,
      add_comm (Finsupp.single η 1), koszulExponent_single_single]
    congr 1
    rcases hne.lt_or_gt with h | h <;> rcases h2 (par γ) with hγ | hγ <;>
      rcases h2 (par η) with hη | hη <;> simp [h, h.not_gt, hγ, hη]

/-! #### The word-length filtration -/

/-- **The word-length filtration is multiplicative.** If the coefficients of `x` vanish on the
monomials of degree less than `m`, and those of `y` on the monomials of degree less than `n`, then
those of `x * y` vanish on the monomials of degree less than `m + n`. This is what makes the
product continuous for the word-length topology, once that topology is introduced; that each
coefficient of a product is a finite sum is `coeff_mul`. -/
theorem coeff_mul_eq_zero_of_degree_lt {x y : SuperMvPowerSeries par σ} {m n : ℕ}
    (hx : ∀ K, K.degree < m → x.coeff K = 0) (hy : ∀ K, K.degree < n → y.coeff K = 0)
    {J : Γ →₀ ℕ} (hJ : J.degree < m + n) : (x * y).coeff J = 0 := by
  by_cases hsq : OddSquarefree par J
  · rw [coeff_mul _ _ hsq]
    refine sum_eq_zero fun ⟨i, j⟩ hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : i.degree + j.degree < m + n := by rwa [← map_add, hp]
    rcases lt_or_ge i.degree m with hi | hi
    · simp [hx i hi]
    · simp [hy j (by omega)]
  · exact coeff_eq_zero_of_not_oddSquarefree _ hsq

end SuperMvPowerSeries

end TauCeti
