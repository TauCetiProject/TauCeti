/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Sigma

/-!
# Fusion rules, F-symbols and R-symbols

A linear monoidal category whose objects are finite direct sums of simple objects `S_a`, each with
endomorphism ring the base ring, is determined by finite matrix data. This file defines that data.

* `TauCeti.FusionRules ι`: a unit index `u : ι` and multiplicities `N_{ab}^c` (the rank of the
  space of morphisms `S_a ⊗ S_b ⟶ S_c`), with `N_{ua}^b = N_{au}^b = δ_{ab}`.
* `TauCeti.FSymbols R N`: the F-matrices `F^{abc}_d`, which express the left basis
  `(φ^{ab→e}_i ▷ c) ≫ φ^{ec→d}_j` of `Hom((a ⊗ b) ⊗ c, d)` in the right basis
  `(a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l` of `Hom(a ⊗ (b ⊗ c), d)` across the associator, together with
  their inverses, subject to the pentagon and triangle equations.
* `TauCeti.RSymbols P`: the R-matrices `R^{ab}_c`, which express the fusion basis of
  `Hom(a ⊗ b, c)` in the braided basis `β_{a,b} ≫ φ^{ba→c}_j`, together with their inverses,
  subject to the two hexagon equations.

The row and column index types of `F^{abc}_d` are `FusionRules.Left a b c d` and
`FusionRules.Right a b c d`; they differ, so the inverse matrices are carried as data. Inverses are
unique, so `FSymbols.ext` and `RSymbols.ext` show that the data is determined by `F`, respectively
by `R`.

Over a one-point index set there is exactly one choice of each, with every entry `1`
(`FSymbols.F_apply_of_subsingleton`, `RSymbols.R_apply_of_subsingleton`).

The base ring is only required to be a commutative semiring: the equations are polynomial
identities in the entries.

## References

* [A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E], eq. (177) and Fig. 17a (F-symbols, pentagon), eq. (207) and Fig. 20 (R-symbols,
  hexagons).
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*], §4.9.
-/

public section

namespace TauCeti

universe u v

/-- **Fusion rules** on an index type `ι`: a unit index `unit` and multiplicities
`N a b c = N_{ab}^c`, with the unit laws `N_{ua}^b = N_{au}^b = if a = b then 1 else 0`. -/
structure FusionRules (ι : Type u) [DecidableEq ι] where
  /-- The index of the tensor unit. -/
  unit : ι
  /-- The multiplicity `N_{ab}^c` of `S_c` in `S_a ⊗ S_b`. -/
  N : ι → ι → ι → ℕ
  /-- The left unit law `N_{ua}^b = δ_{ab}`. -/
  N_unit_left : ∀ a b, N unit a b = if a = b then 1 else 0
  /-- The right unit law `N_{au}^b = δ_{ab}`. -/
  N_unit_right : ∀ a b, N a unit b = if a = b then 1 else 0

namespace FusionRules

attribute [simp] N_unit_left N_unit_right

variable {ι : Type u} [DecidableEq ι] (N : FusionRules ι)

/-- The unit index of fusion rules is determined by the multiplicities. -/
theorem unit_eq_of_N_eq {N₁ N₂ : FusionRules ι} (h : N₁.N = N₂.N) : N₁.unit = N₂.unit := by
  have h1 := N₁.N_unit_left N₂.unit N₂.unit
  rw [h, N₂.N_unit_right] at h1
  simpa using h1

/-- Fusion rules are determined by their multiplicities. -/
@[ext]
theorem ext {N₁ N₂ : FusionRules ι} (h : N₁.N = N₂.N) : N₁ = N₂ := by
  have hu := unit_eq_of_N_eq h
  cases N₁
  cases N₂
  congr

/-- Row indices of `F^{abc}_d`: `Σ e, Fin N_{ab}^e × Fin N_{ec}^d`, indexing the left basis
`(φ^{ab→e}_i ▷ c) ≫ φ^{ec→d}_j` of `Hom((a ⊗ b) ⊗ c, d)`. -/
abbrev Left (a b c d : ι) : Type u := Σ e : ι, Fin (N.N a b e) × Fin (N.N e c d)

/-- Column indices of `F^{abc}_d`: `Σ f, Fin N_{bc}^f × Fin N_{af}^d`, indexing the right basis
`(a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l` of `Hom(a ⊗ (b ⊗ c), d)`. -/
abbrev Right (a b c d : ι) : Type u := Σ f : ι, Fin (N.N b c f) × Fin (N.N a f d)

/-- The unique basis vector of `Hom(u ⊗ a, a)`, the left unitor. -/
def unitLeft (a : ι) : Fin (N.N N.unit a a) := ⟨0, by simp⟩

/-- The unique basis vector of `Hom(a ⊗ u, a)`, the right unitor. -/
def unitRight (a : ι) : Fin (N.N a N.unit a) := ⟨0, by simp⟩

@[simp]
theorem val_unitLeft (a : ι) : (N.unitLeft a : ℕ) = 0 := (rfl)

@[simp]
theorem val_unitRight (a : ι) : (N.unitRight a : ℕ) = 0 := (rfl)

/-- `Hom(u ⊗ a, b)` has at most one basis vector. -/
instance (a b : ι) : Subsingleton (Fin (N.N N.unit a b)) :=
  Fin.subsingleton_iff_le_one.2 (by rw [N_unit_left]; split_ifs <;> simp)

/-- `Hom(a ⊗ u, b)` has at most one basis vector. -/
instance (a b : ι) : Subsingleton (Fin (N.N a N.unit b)) :=
  Fin.subsingleton_iff_le_one.2 (by rw [N_unit_right]; split_ifs <;> simp)

section Subsingleton

variable [Subsingleton ι]

/-- Over a one-point index set every multiplicity is `1`. -/
theorem N_eq_one_of_subsingleton (a b c : ι) : N.N a b c = 1 := by
  obtain rfl := Subsingleton.elim a N.unit
  simp [Subsingleton.elim b c]

private instance uniqueFin (a b c : ι) : Unique (Fin (N.N a b c)) :=
  have := Fin.subsingleton_iff_le_one.2 (N.N_eq_one_of_subsingleton a b c).le
  uniqueOfSubsingleton ⟨0, by simp [N.N_eq_one_of_subsingleton]⟩

private instance uniqueLeft (a b c d : ι) : Unique (N.Left a b c d) where
  default := ⟨a, default, default⟩
  uniq := fun ⟨e, i, j⟩ ↦ by
    obtain rfl := Subsingleton.elim e a
    rw [Subsingleton.elim i default, Subsingleton.elim j default]

private instance uniqueRight (a b c d : ι) : Unique (N.Right a b c d) where
  default := ⟨a, default, default⟩
  uniq := fun ⟨f, k, l⟩ ↦ by
    obtain rfl := Subsingleton.elim f a
    rw [Subsingleton.elim k default, Subsingleton.elim l default]

end Subsingleton

end FusionRules

/-- **F-symbols** over a commutative semiring `R` for fusion rules `N`: the matrices
`F^{abc}_d`, with rows `N.Left a b c d` and columns `N.Right a b c d`, defined by
`(φ^{ab→e}_i ▷ c) ≫ φ^{ec→d}_j = Σ_{(f,k,l)} F^{abc}_d[(e,i,j),(f,k,l)] •
(α_{a,b,c} ≫ (a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l)`, with two-sided inverses `F̄^{abc}_d`, satisfying
the pentagon and the triangle equations.

The inverse is data because rows and columns are indexed by different types; it is unique, so
two F-symbols with equal `F` are equal (`FSymbols.ext`). -/
structure FSymbols (R : Type v) [CommSemiring R] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (N : FusionRules ι) where
  /-- `F^{abc}_d`, with rows `Left` and columns `Right`. -/
  F : ∀ a b c d : ι, Matrix (N.Left a b c d) (N.Right a b c d) R
  /-- `F̄^{abc}_d`, the inverse of `F^{abc}_d`, with rows `Right` and columns `Left`. -/
  Finv : ∀ a b c d : ι, Matrix (N.Right a b c d) (N.Left a b c d) R
  /-- `F̄^{abc}_d` is a right inverse of `F^{abc}_d`. -/
  F_mul_Finv : ∀ a b c d, F a b c d * Finv a b c d = 1
  /-- `F̄^{abc}_d` is a left inverse of `F^{abc}_d`. -/
  Finv_mul_F : ∀ a b c d, Finv a b c d * F a b c d = 1
  /-- The pentagon equation. Its left side is the symbol of `α_{AB,C,D} ≫ α_{A,B,CD}`, and its
  right side that of `(α_{A,B,C} ▷ D) ≫ α_{A,BC,D} ≫ (A ◁ α_{B,C,D})`. -/
  pentagon : ∀ (A B C D E p q r s : ι) (i₁ : Fin (N.N A B p)) (i₂ : Fin (N.N p C q))
    (i₃ : Fin (N.N q D E)) (k : Fin (N.N C D r)) (m : Fin (N.N B r s)) (n : Fin (N.N A s E)),
    ∑ l : Fin (N.N p r E), F p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * F A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      ∑ t : ι, ∑ x : Fin (N.N B C t), ∑ y : Fin (N.N A t q), ∑ z : Fin (N.N t D s),
        F A B C q ⟨p, i₁, i₂⟩ ⟨t, x, y⟩ * F A t D E ⟨q, y, i₃⟩ ⟨s, z, n⟩ *
          F B C D s ⟨t, x, z⟩ ⟨r, k, m⟩
  /-- The triangle equation `F^{auc}_d[(a,0,j),(c,0,l)] = δ_{jl}`. -/
  triangle : ∀ (a c d : ι) (j l : Fin (N.N a c d)),
    F a N.unit c d ⟨a, N.unitRight a, j⟩ ⟨c, N.unitLeft c, l⟩ = if j = l then 1 else 0

namespace FSymbols

variable {R : Type v} [CommSemiring R] {ι : Type u} [Fintype ι] [DecidableEq ι]
  {N : FusionRules ι} (P : FSymbols R N)

/-- A left inverse of `F^{abc}_d` is `F̄^{abc}_d`. -/
theorem Finv_eq_of_mul_F_eq_one {a b c d : ι} {M : Matrix (N.Right a b c d) (N.Left a b c d) R}
    (h : M * P.F a b c d = 1) : P.Finv a b c d = M := by
  rw [← Matrix.one_mul (P.Finv a b c d), ← h, Matrix.mul_assoc, P.F_mul_Finv, Matrix.mul_one]

/-- A right inverse of `F^{abc}_d` is `F̄^{abc}_d`. -/
theorem Finv_eq_of_F_mul_eq_one {a b c d : ι} {M : Matrix (N.Right a b c d) (N.Left a b c d) R}
    (h : P.F a b c d * M = 1) : P.Finv a b c d = M := by
  rw [← Matrix.mul_one (P.Finv a b c d), ← h, ← Matrix.mul_assoc, P.Finv_mul_F, Matrix.one_mul]

/-- F-symbols are determined by their matrices `F^{abc}_d`. -/
@[ext]
theorem ext {P Q : FSymbols R N} (h : P.F = Q.F) : P = Q := by
  have hinv : P.Finv = Q.Finv := by
    funext a b c d
    exact P.Finv_eq_of_F_mul_eq_one (h ▸ Q.F_mul_Finv a b c d)
  cases P
  cases Q
  congr

section Subsingleton

variable [Subsingleton ι]

/-- Over a one-point index set every entry of `F^{abc}_d` is `1`, by the triangle equation. -/
@[simp]
theorem F_apply_of_subsingleton (a b c d : ι) (x : N.Left a b c d) (y : N.Right a b c d) :
    P.F a b c d x y = 1 := by
  obtain rfl := Subsingleton.elim a N.unit
  obtain rfl := Subsingleton.elim b N.unit
  obtain rfl := Subsingleton.elim c N.unit
  obtain rfl := Subsingleton.elim d N.unit
  rw [Subsingleton.elim x ⟨N.unit, N.unitRight _, N.unitLeft _⟩,
    Subsingleton.elim y ⟨N.unit, N.unitLeft _, N.unitLeft _⟩, P.triangle]
  simp

/-- Over a one-point index set every entry of `F̄^{abc}_d` is `1`. -/
@[simp]
theorem Finv_apply_of_subsingleton (a b c d : ι) (y : N.Right a b c d) (x : N.Left a b c d) :
    P.Finv a b c d y x = 1 := by
  rw [P.Finv_eq_of_F_mul_eq_one (M := Matrix.of fun _ _ ↦ 1) ?_]
  · simp
  · ext x x'
    obtain rfl := Subsingleton.elim x x'
    simp [Matrix.mul_apply]

/-- Over a one-point index set there is exactly one choice of F-symbols, with every entry `1`. -/
instance : Unique (FSymbols R N) where
  default :=
    { F := fun _ _ _ _ ↦ Matrix.of fun _ _ ↦ 1
      Finv := fun _ _ _ _ ↦ Matrix.of fun _ _ ↦ 1
      F_mul_Finv := fun _ _ _ _ ↦ by
        ext x y
        obtain rfl := Subsingleton.elim x y
        simp [Matrix.mul_apply]
      Finv_mul_F := fun _ _ _ _ ↦ by
        ext x y
        obtain rfl := Subsingleton.elim x y
        simp [Matrix.mul_apply]
      pentagon := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦ by
        simp [Fintype.sum_subsingleton _ N.unit]
      triangle := fun _ _ _ j l ↦ by simp [Subsingleton.elim j l] }
  uniq P := by
    ext a b c d x y
    simp

end Subsingleton

end FSymbols

/-- **R-symbols** for F-symbols `P` over a commutative semiring `K`: the matrices
`R^{ab}_c : Matrix (Fin N_{ab}^c) (Fin N_{ba}^c) K`, defined by
`φ^{ab→c}_i = Σ_j R^{ab}_c[i,j] • (β_{a,b} ≫ φ^{ba→c}_j)`, with two-sided inverses, satisfying
the two hexagon equations.

As for `FSymbols`, the inverse is data and is unique, so two R-symbols with equal `R` are equal
(`RSymbols.ext`). -/
structure RSymbols {K : Type v} [CommSemiring K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {N : FusionRules ι} (P : FSymbols K N) where
  /-- `R^{ab}_c`, in the same direction as `F`. -/
  R : ∀ a b c : ι, Matrix (Fin (N.N a b c)) (Fin (N.N b a c)) K
  /-- The inverse of `R^{ab}_c`. -/
  Rinv : ∀ a b c : ι, Matrix (Fin (N.N b a c)) (Fin (N.N a b c)) K
  /-- `Rinv a b c` is a right inverse of `R^{ab}_c`. -/
  R_mul_Rinv : ∀ a b c, R a b c * Rinv a b c = 1
  /-- `Rinv a b c` is a left inverse of `R^{ab}_c`. -/
  Rinv_mul_R : ∀ a b c, Rinv a b c * R a b c = 1
  /-- The hexagon equation of `BraidedCategory.hexagon_forward`, for `(e,i,j) : Left a b c d`,
  `n : N_{ca}^g` and `o : N_{bg}^d`. -/
  hexagon_forward : ∀ (a b c d e g : ι) (i : Fin (N.N a b e)) (j : Fin (N.N e c d))
    (n : Fin (N.N c a g)) (o : Fin (N.N b g d)),
    ∑ f : ι, ∑ k : Fin (N.N b c f), ∑ l : Fin (N.N a f d), ∑ m : Fin (N.N f a d),
        P.F a b c d ⟨e, i, j⟩ ⟨f, k, l⟩ * R a f d l m * P.F b c a d ⟨f, k, m⟩ ⟨g, n, o⟩ =
      ∑ p : Fin (N.N b a e), ∑ q : Fin (N.N a c g),
        R a b e i p * P.F b a c d ⟨e, p, j⟩ ⟨g, q, o⟩ * R a c g q n
  /-- The hexagon equation of `BraidedCategory.hexagon_reverse`, for `(f,k,l) : Right a b c d`,
  `n : N_{ca}^g` and `o : N_{gb}^d`. -/
  hexagon_reverse : ∀ (a b c d f g : ι) (k : Fin (N.N b c f)) (l : Fin (N.N a f d))
    (n : Fin (N.N c a g)) (o : Fin (N.N g b d)),
    ∑ e : ι, ∑ i : Fin (N.N a b e), ∑ j : Fin (N.N e c d), ∑ m : Fin (N.N c e d),
        P.Finv a b c d ⟨f, k, l⟩ ⟨e, i, j⟩ * R e c d j m * P.Finv c a b d ⟨e, i, m⟩ ⟨g, n, o⟩ =
      ∑ p : Fin (N.N c b f), ∑ q : Fin (N.N a c g),
        R b c f k p * P.Finv a c b d ⟨f, p, l⟩ ⟨g, q, o⟩ * R a c g q n

namespace RSymbols

variable {K : Type v} [CommSemiring K] {ι : Type u} [Fintype ι] [DecidableEq ι]
  {N : FusionRules ι} {P : FSymbols K N} (Q : RSymbols P)

/-- A left inverse of `R^{ab}_c` is `Rinv a b c`. -/
theorem Rinv_eq_of_mul_R_eq_one {a b c : ι} {M : Matrix (Fin (N.N b a c)) (Fin (N.N a b c)) K}
    (h : M * Q.R a b c = 1) : Q.Rinv a b c = M := by
  rw [← Matrix.one_mul (Q.Rinv a b c), ← h, Matrix.mul_assoc, Q.R_mul_Rinv, Matrix.mul_one]

/-- A right inverse of `R^{ab}_c` is `Rinv a b c`. -/
theorem Rinv_eq_of_R_mul_eq_one {a b c : ι} {M : Matrix (Fin (N.N b a c)) (Fin (N.N a b c)) K}
    (h : Q.R a b c * M = 1) : Q.Rinv a b c = M := by
  rw [← Matrix.mul_one (Q.Rinv a b c), ← h, ← Matrix.mul_assoc, Q.Rinv_mul_R, Matrix.one_mul]

/-- R-symbols are determined by their matrices `R^{ab}_c`. -/
@[ext]
theorem ext {Q Q' : RSymbols P} (h : Q.R = Q'.R) : Q = Q' := by
  have hinv : Q.Rinv = Q'.Rinv := by
    funext a b c
    exact Q.Rinv_eq_of_R_mul_eq_one (h ▸ Q'.R_mul_Rinv a b c)
  cases Q
  cases Q'
  congr

section Subsingleton

variable [Subsingleton ι]

/-- Over a one-point index set every entry of `R^{ab}_c` is `1`: the forward hexagon says that
the single entry `r` satisfies `r = r * r`, and `r` is invertible. -/
@[simp]
theorem R_apply_of_subsingleton (a b c : ι) (i : Fin (N.N a b c)) (j : Fin (N.N b a c)) :
    Q.R a b c i j = 1 := by
  obtain rfl := Subsingleton.elim a N.unit
  obtain rfl := Subsingleton.elim b N.unit
  obtain rfl := Subsingleton.elim c N.unit
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have hex := Q.hexagon_forward N.unit N.unit N.unit N.unit N.unit N.unit default default
    default default
  simp only [Fintype.sum_subsingleton _ N.unit, Fintype.sum_unique,
    P.F_apply_of_subsingleton, one_mul, mul_one] at hex
  have hinv := congrFun (congrFun (Q.R_mul_Rinv N.unit N.unit N.unit) default) default
  simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq] at hinv
  calc Q.R N.unit N.unit N.unit default default
      = Q.R N.unit N.unit N.unit default default *
          (Q.R N.unit N.unit N.unit default default *
            Q.Rinv N.unit N.unit N.unit default default) := by rw [hinv, mul_one]
    _ = Q.R N.unit N.unit N.unit default default *
          Q.Rinv N.unit N.unit N.unit default default := by rw [← mul_assoc, ← hex]
    _ = 1 := hinv

/-- Over a one-point index set there is exactly one choice of R-symbols, with every entry `1`. -/
instance : Unique (RSymbols P) where
  default :=
    { R := fun _ _ _ ↦ Matrix.of fun _ _ ↦ 1
      Rinv := fun _ _ _ ↦ Matrix.of fun _ _ ↦ 1
      R_mul_Rinv := fun _ _ _ ↦ by
        ext x y
        obtain rfl := Subsingleton.elim x y
        simp [Matrix.mul_apply]
      Rinv_mul_R := fun _ _ _ ↦ by
        ext x y
        obtain rfl := Subsingleton.elim x y
        simp [Matrix.mul_apply]
      hexagon_forward := fun _ _ _ _ _ _ _ _ _ _ ↦ by
        simp [Fintype.sum_subsingleton _ N.unit]
      hexagon_reverse := fun _ _ _ _ _ _ _ _ _ _ ↦ by
        simp [Fintype.sum_subsingleton _ N.unit] }
  uniq Q := by
    ext a b c i j
    simp

end Subsingleton

end RSymbols

end TauCeti
