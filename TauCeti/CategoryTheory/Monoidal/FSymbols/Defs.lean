/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod

/-!
# Fusion rules, F-symbols and R-symbols

A linear monoidal category whose objects are finite direct sums of simple objects `S_a`, each with
endomorphisms the base ring, can be described by finite data. Fix a finite index set `ι` of simple
objects with a unit index `u`, the multiplicities `N_{ab}^c` of `S_c` in `S_a ⊗ S_b`, and bases
`φ^{ab→c}_i`, `i : Fin N_{ab}^c`, of the fusion spaces `Hom(S_a ⊗ S_b, S_c)`. Then:

* the **F-symbols** `F^{abc}_d` are the matrices expressing the basis
  `(φ^{ab→e}_i ▷ S_c) ≫ φ^{ec→d}_j` of `Hom((S_a ⊗ S_b) ⊗ S_c, S_d)` in the basis
  `(α_ S_a S_b S_c).hom ≫ (S_a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l`, coming from
  `Hom(S_a ⊗ (S_b ⊗ S_c), S_d)`;
  the pentagon axiom of the associator becomes the *pentagon equation* between their entries, and
  the triangle axiom becomes the *triangle equation*;
* given a braiding, the **R-symbols** `R^{ab}_c` are the matrices expressing the basis
  `φ^{ab→c}_i` in the basis `(β_ S_a S_b).hom ≫ φ^{ba→c}_j`, and the two hexagon axioms become the
  two *hexagon equations*.

This file defines the three structures carrying this data, as purely algebraic objects over a
commutative semiring `R`: no category appears. Commutativity of `R` is not used by the
definitions; it is the setting in which this data describes linear monoidal categories, since the
endomorphisms of the tensor unit of a monoidal category commute.

## Main definitions

* `TauCeti.FusionRules ι`: a unit index `unit : ι` and multiplicities `N : ι → ι → ι → ℕ`
  satisfying the unit laws `N_{ua}^b = N_{au}^b = [a = b]`.
* `TauCeti.FusionRules.Left` and `TauCeti.FusionRules.Right`: the row and column index types
  `Σ e, Fin N_{ab}^e × Fin N_{ec}^d` and `Σ f, Fin N_{bc}^f × Fin N_{af}^d` of `F^{abc}_d`.
* `TauCeti.FSymbols R N`: matrices `F^{abc}_d` with two-sided inverses `(F^{abc}_d)⁻¹`,
  satisfying the pentagon and triangle equations.
* `TauCeti.RSymbols P`: for F-symbols `P`, matrices `R^{ab}_c` with two-sided inverses, satisfying
  the two hexagon equations.

## Main results

* `TauCeti.FSymbols.ext` and `TauCeti.RSymbols.ext`: since a matrix has at most one two-sided
  inverse, F-symbols are determined by `F`, and R-symbols by `R`.

## Conventions

The matrix `F^{abc}_d` has rows indexed by `Left a b c d` and columns by `Right a b c d`, and is
defined by
`(φ^{ab→e}_i ▷ S_c) ≫ φ^{ec→d}_j =`
`∑_{(f,k,l)} F^{abc}_d[(e,i,j),(f,k,l)] • ((α_ S_a S_b S_c).hom ≫ (S_a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l)`.
The matrix `R^{ab}_c` points in the same direction:
`φ^{ab→c}_i = ∑_j R^{ab}_c[i,j] • (β.hom ≫ φ^{ba→c}_j)`.
Only the triangle equation is imposed among the unit conditions; it normalizes the fusion bases
through the left and right unitors.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E: §E.1, eq. (177) and Fig. 17a (F-symbols and the pentagon), and §E.3, eq. (207) and
  Fig. 20 (R-symbols and the hexagons).
* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS (2015), §4.9.
-/

public section

namespace TauCeti

universe u v

/-- **Fusion rules** on an index type `ι` of simple objects: a unit index `unit` and the
multiplicity `N a b c = N_{ab}^c` of the simple object `c` in the tensor product of `a` and `b`,
satisfying the unit laws `N_{ua}^b = N_{au}^b = [a = b]`. The unit laws are stated as four fields so
that no decidable equality on `ι` is built in; `TauCeti.FusionRules.N_unit_left` and
`TauCeti.FusionRules.N_unit_right` restate them with `if`. -/
@[ext]
structure FusionRules (ι : Type u) where
  /-- The index of the tensor unit. -/
  unit : ι
  /-- The multiplicity `N_{ab}^c` of `c` in the tensor product of `a` and `b`. -/
  N : ι → ι → ι → ℕ
  /-- The unit is a left unit: `N_{ua}^a = 1`. -/
  N_unit_left_self : ∀ a, N unit a a = 1
  /-- The unit is a left unit: `N_{ua}^b = 0` for `a ≠ b`. -/
  N_unit_left_of_ne : ∀ a b, a ≠ b → N unit a b = 0
  /-- The unit is a right unit: `N_{au}^a = 1`. -/
  N_unit_right_self : ∀ a, N a unit a = 1
  /-- The unit is a right unit: `N_{au}^b = 0` for `a ≠ b`. -/
  N_unit_right_of_ne : ∀ a b, a ≠ b → N a unit b = 0

namespace FusionRules

variable {ι : Type u} (N : FusionRules ι)

attribute [simp] N_unit_left_self N_unit_right_self

/-- The left unit law in the form `N_{ua}^b = [a = b]`. -/
theorem N_unit_left [DecidableEq ι] (a b : ι) : N.N N.unit a b = if a = b then 1 else 0 := by
  split_ifs with h
  · exact h ▸ N.N_unit_left_self a
  · exact N.N_unit_left_of_ne a b h

/-- The right unit law in the form `N_{au}^b = [a = b]`. -/
theorem N_unit_right [DecidableEq ι] (a b : ι) : N.N a N.unit b = if a = b then 1 else 0 := by
  split_ifs with h
  · exact h ▸ N.N_unit_right_self a
  · exact N.N_unit_right_of_ne a b h

/-- Row indices of `F^{abc}_d`: the triples `(e, i, j)` with `i : Fin N_{ab}^e` and
`j : Fin N_{ec}^d`, indexing the left basis `(φ^{ab→e}_i ▷ c) ≫ φ^{ec→d}_j` of
`Hom((a ⊗ b) ⊗ c, d)`. -/
abbrev Left (a b c d : ι) : Type u := Σ e : ι, Fin (N.N a b e) × Fin (N.N e c d)

/-- Column indices of `F^{abc}_d`: the triples `(f, k, l)` with `k : Fin N_{bc}^f` and
`l : Fin N_{af}^d`, indexing the right basis `(a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l` of
`Hom(a ⊗ (b ⊗ c), d)`. -/
abbrev Right (a b c d : ι) : Type u := Σ f : ι, Fin (N.N b c f) × Fin (N.N a f d)

/-- The unique index of `Hom(u ⊗ a, a)`, whose basis vector is normalized to the left unitor. -/
def unitLeft (a : ι) : Fin (N.N N.unit a a) := ⟨0, by simp⟩

/-- The unique index of `Hom(a ⊗ u, a)`, whose basis vector is normalized to the right unitor. -/
def unitRight (a : ι) : Fin (N.N a N.unit a) := ⟨0, by simp⟩

@[simp]
theorem unitLeft_val (a : ι) : (N.unitLeft a : ℕ) = 0 := (rfl)

@[simp]
theorem unitRight_val (a : ι) : (N.unitRight a : ℕ) = 0 := (rfl)

/-- `TauCeti.FusionRules.unitLeft a` is the only index of `Hom(u ⊗ a, a)`. -/
instance (a : ι) : Unique (Fin (N.N N.unit a a)) where
  default := N.unitLeft a
  uniq i := Fin.ext <| by simpa using i.isLt

/-- `TauCeti.FusionRules.unitRight a` is the only index of `Hom(a ⊗ u, a)`. -/
instance (a : ι) : Unique (Fin (N.N a N.unit a)) where
  default := N.unitRight a
  uniq i := Fin.ext <| by simpa using i.isLt

end FusionRules

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **F-symbols** over a commutative semiring `R` for fusion rules `N`: matrices `F^{abc}_d`, with
rows `N.Left a b c d` and columns `N.Right a b c d`, and two-sided inverses `(F^{abc}_d)⁻¹`,
satisfying the pentagon and triangle equations.

The pentagon equation compares the two composites `α_{AB,C,D} ≫ α_{A,B,CD}` (left side) and
`(α_{A,B,C} ▷ D) ≫ α_{A,BC,D} ≫ (A ◁ α_{B,C,D})` (right side) on the left basis of
`Hom(((A ⊗ B) ⊗ C) ⊗ D, E)`, through the intermediate objects `p, q` (from `A ⊗ B`, then
`p ⊗ C`) and `r, s` (from `C ⊗ D`, then `B ⊗ r`). The inverse is part of the data because rows
and columns are indexed by different types; it is determined by `F` (`TauCeti.FSymbols.ext`). -/
structure FSymbols (R : Type v) [CommSemiring R] (N : FusionRules ι) where
  /-- The F-matrix `F^{abc}_d`, rows `Left`, columns `Right`. -/
  F : ∀ a b c d : ι, Matrix (N.Left a b c d) (N.Right a b c d) R
  /-- The inverse F-matrix `(F^{abc}_d)⁻¹`, rows `Right`, columns `Left`. -/
  Finv : ∀ a b c d : ι, Matrix (N.Right a b c d) (N.Left a b c d) R
  /-- `(F^{abc}_d)⁻¹` is a right inverse of `F^{abc}_d`. -/
  F_mul_Finv : ∀ a b c d, F a b c d * Finv a b c d = 1
  /-- `(F^{abc}_d)⁻¹` is a left inverse of `F^{abc}_d`. -/
  Finv_mul_F : ∀ a b c d, Finv a b c d * F a b c d = 1
  /-- The pentagon equation (Kitaev, Fig. 17a). -/
  pentagon : ∀ (A B C D E p q r s : ι) (i₁ : Fin (N.N A B p)) (i₂ : Fin (N.N p C q))
    (i₃ : Fin (N.N q D E)) (k : Fin (N.N C D r)) (m : Fin (N.N B r s)) (n : Fin (N.N A s E)),
    ∑ l : Fin (N.N p r E), F p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * F A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      ∑ t : ι, ∑ x : Fin (N.N B C t), ∑ y : Fin (N.N A t q), ∑ z : Fin (N.N t D s),
        F A B C q ⟨p, i₁, i₂⟩ ⟨t, x, y⟩ * F A t D E ⟨q, y, i₃⟩ ⟨s, z, n⟩ *
          F B C D s ⟨t, x, z⟩ ⟨r, k, m⟩
  /-- The triangle equation: `F^{auc}_d[(a,0,j),(c,0,l)] = [j = l]`. -/
  triangle : ∀ (a c d : ι) (j l : Fin (N.N a c d)),
    F a N.unit c d ⟨a, N.unitRight a, j⟩ ⟨c, N.unitLeft c, l⟩ = if j = l then 1 else 0

namespace FSymbols

variable {R : Type v} [CommSemiring R] {N : FusionRules ι}

/-- The inverse F-matrix is the only left inverse of the F-matrix. -/
theorem Finv_eq_of_mul_eq_one (P : FSymbols R N) {a b c d : ι}
    {M : Matrix (N.Right a b c d) (N.Left a b c d) R} (h : M * P.F a b c d = 1) :
    P.Finv a b c d = M := by
  rw [← Matrix.one_mul (P.Finv a b c d), ← h, Matrix.mul_assoc, P.F_mul_Finv, Matrix.mul_one]

/-- F-symbols are determined by their F-matrices. -/
@[ext]
theorem ext {P Q : FSymbols R N} (h : P.F = Q.F) : P = Q := by
  have hinv : Q.Finv = P.Finv := by
    funext a b c d
    exact Q.Finv_eq_of_mul_eq_one (by rw [← h, P.Finv_mul_F])
  cases P
  cases Q
  cases h
  cases hinv
  rfl

end FSymbols

/-- **R-symbols** for F-symbols `P`: matrices `R^{ab}_c`, with rows `Fin N_{ab}^c` and columns
`Fin N_{ba}^c`, and two-sided inverses, satisfying the two hexagon equations relating them to the
F-matrices `F^{abc}_d` and their inverses. -/
structure RSymbols {K : Type v} [CommSemiring K] {N : FusionRules ι} (P : FSymbols K N) where
  /-- The R-matrix `R^{ab}_c`, in the same direction as the F-matrices. -/
  R : ∀ a b c : ι, Matrix (Fin (N.N a b c)) (Fin (N.N b a c)) K
  /-- The inverse of `R^{ab}_c`. -/
  Rinv : ∀ a b c : ι, Matrix (Fin (N.N b a c)) (Fin (N.N a b c)) K
  /-- `Rinv a b c` is a right inverse of `R a b c`. -/
  R_mul_Rinv : ∀ a b c, R a b c * Rinv a b c = 1
  /-- `Rinv a b c` is a left inverse of `R a b c`. -/
  Rinv_mul_R : ∀ a b c, Rinv a b c * R a b c = 1
  /-- The forward hexagon equation (Kitaev, eq. (207)), for `(e,i,j) : Left a b c d`,
  `n : Fin N_{ca}^g` and `o : Fin N_{bg}^d`. -/
  hexagon_forward : ∀ (a b c d e g : ι) (i : Fin (N.N a b e)) (j : Fin (N.N e c d))
    (n : Fin (N.N c a g)) (o : Fin (N.N b g d)),
    ∑ f : ι, ∑ k : Fin (N.N b c f), ∑ l : Fin (N.N a f d), ∑ m : Fin (N.N f a d),
        P.F a b c d ⟨e, i, j⟩ ⟨f, k, l⟩ * R a f d l m * P.F b c a d ⟨f, k, m⟩ ⟨g, n, o⟩ =
      ∑ p : Fin (N.N b a e), ∑ q : Fin (N.N a c g),
        R a b e i p * P.F b a c d ⟨e, p, j⟩ ⟨g, q, o⟩ * R a c g q n
  /-- The reverse hexagon equation (Kitaev, Fig. 20), for `(f,k,l) : Right a b c d`,
  `n : Fin N_{ca}^g` and `o : Fin N_{gb}^d`. -/
  hexagon_reverse : ∀ (a b c d f g : ι) (k : Fin (N.N b c f)) (l : Fin (N.N a f d))
    (n : Fin (N.N c a g)) (o : Fin (N.N g b d)),
    ∑ e : ι, ∑ i : Fin (N.N a b e), ∑ j : Fin (N.N e c d), ∑ m : Fin (N.N c e d),
        P.Finv a b c d ⟨f, k, l⟩ ⟨e, i, j⟩ * R e c d j m * P.Finv c a b d ⟨e, i, m⟩ ⟨g, n, o⟩ =
      ∑ p : Fin (N.N c b f), ∑ q : Fin (N.N a c g),
        R b c f k p * P.Finv a c b d ⟨f, p, l⟩ ⟨g, q, o⟩ * R a c g q n

namespace RSymbols

variable {K : Type v} [CommSemiring K] {N : FusionRules ι} {P : FSymbols K N}

/-- The inverse R-matrix is the only left inverse of the R-matrix. -/
theorem Rinv_eq_of_mul_eq_one (Q : RSymbols P) {a b c : ι}
    {M : Matrix (Fin (N.N b a c)) (Fin (N.N a b c)) K} (h : M * Q.R a b c = 1) :
    Q.Rinv a b c = M := by
  rw [← Matrix.one_mul (Q.Rinv a b c), ← h, Matrix.mul_assoc, Q.R_mul_Rinv, Matrix.mul_one]

/-- R-symbols are determined by their R-matrices. -/
@[ext]
theorem ext {Q Q' : RSymbols P} (h : Q.R = Q'.R) : Q = Q' := by
  have hinv : Q'.Rinv = Q.Rinv := by
    funext a b c
    exact Q'.Rinv_eq_of_mul_eq_one (by rw [← h, Q.Rinv_mul_R])
  cases Q
  cases Q'
  cases h
  cases hinv
  rfl

end RSymbols

end TauCeti
