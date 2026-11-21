/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Defs

/-!
# First consequences of F-symbols and R-symbols

This file derives what the invertibility of the F- and R-matrices says about the fusion rules, and
computes F- and R-symbols in the degenerate cases.

* **Invertibility.** Over a nontrivial commutative semiring, an invertible rectangular matrix is
  square. Applied to `F^{abc}_d`, whose rows are indexed by `Σ e, Fin N_{ab}^e × Fin N_{ec}^d` and
  columns by `Σ f, Fin N_{bc}^f × Fin N_{af}^d`, this gives associativity of the fusion rules,
  `∑ e, N_{ab}^e N_{ec}^d = ∑ f, N_{bc}^f N_{af}^d` (`TauCeti.FSymbols.N_assoc`). Applied to
  `R^{ab}_c`, it gives commutativity, `N_{ab}^c = N_{ba}^c` (`TauCeti.RSymbols.N_comm`).
* **Group fusion rules.** `TauCeti.FusionRules.ofMul M` has `N_{gh}^l = [g * h = l]`, for a type
  with a multiplication and a unit; for a group `G` these are the fusion rules of the category of
  `G`-graded modules. For a finite monoid, `TauCeti.FSymbols.ofMul R M` are the F-symbols with all
  entries `1`, describing the standard associator of graded modules. R-symbols for them exist over
  a nontrivial commutative semiring exactly when the multiplication is commutative
  (`TauCeti.RSymbols.nonempty_ofMul_iff`): `TauCeti.RSymbols.ofMul` with all entries `1`, the
  symmetric braiding, is one for a commutative monoid, while for any F-symbols of the group fusion
  rules `TauCeti.RSymbols.mul_comm` shows that R-symbols force commutativity. In `S₃`, with
  `a = (12)` and `b = (23)`, the R-matrix `R^{ab}_{ab}` would be an invertible `1 × 0` matrix.
* **One simple object.** If `ι` is a subsingleton, every fusion multiplicity is `1`, and over any
  commutative semiring there are exactly one F-symbols and, for it, exactly one R-symbols, all of
  whose entries are `1` (`TauCeti.FSymbols.F_apply_of_subsingleton`,
  `TauCeti.RSymbols.R_apply_of_subsingleton`). The hexagon equation at the unit forces
  `r = r * r` for the single R-entry `r`, and `r` is invertible.
* **The zero ring.** Over a subsingleton semiring all fusion rules carry exactly one F-symbols, and
  all F-symbols exactly one R-symbols, since every matrix identity holds there. So the hypotheses
  `[Nontrivial R]` above are needed: over the zero ring the group fusion rules of every finite
  monoid, commutative or not, carry R-symbols.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E, §E.1, eq. (177), and §E.3, eq. (207): the matrices `F` and `R` are matrices of
  isomorphisms between Hom spaces, whose dimensions are the two sides of the identities above.
-/

public section

namespace TauCeti

universe u v

variable {ι : Type u}

namespace FusionRules

variable (N : FusionRules ι)

/-- If there is only one simple object, all fusion multiplicities are `1`. -/
@[simp]
theorem N_eq_one_of_subsingleton [Subsingleton ι] (a b c : ι) : N.N a b c = 1 := by
  obtain rfl := Subsingleton.elim a N.unit
  obtain rfl := Subsingleton.elim b N.unit
  obtain rfl := Subsingleton.elim c N.unit
  exact N.N_unit_left_self N.unit

/-- The **group fusion rules** `N_{gh}^l = [g * h = l]` of a type with a multiplication and a unit,
with unit index `1`. For a group `G`, these are the fusion rules of the category of `G`-graded
modules, whose simple objects are the free modules of rank one concentrated in one degree. -/
def ofMul (M : Type u) [MulOneClass M] [DecidableEq M] : FusionRules M where
  unit := 1
  N g h l := if g * h = l then 1 else 0
  N_unit_left_self _ := by simp
  N_unit_left_of_ne _ _ h := by simpa using h
  N_unit_right_self _ := by simp
  N_unit_right_of_ne _ _ h := by simpa using h

variable {M : Type u} [MulOneClass M] [DecidableEq M]

@[simp]
theorem ofMul_unit : (ofMul M).unit = 1 := (rfl)

@[simp]
theorem ofMul_N (g h l : M) : (ofMul M).N g h l = if g * h = l then 1 else 0 := (rfl)

/-- A fusion channel `g ⊗ h → l` of the group fusion rules exists only for `l = g * h`. -/
theorem mul_eq_of_ofMul {g h l : M} (i : Fin ((ofMul M).N g h l)) : g * h = l := by
  by_contra hne
  simpa [ofMul_N, hne] using i.isLt

/-- There is no fusion channel `g ⊗ h → l` of the group fusion rules for `l ≠ g * h`. -/
theorem isEmpty_fin_ofMul_N {g h l : M} (hl : g * h ≠ l) : IsEmpty (Fin ((ofMul M).N g h l)) :=
  ⟨fun i ↦ hl (mul_eq_of_ofMul i)⟩

/-- A sum over the fusion channels `g ⊗ h → f` of the group fusion rules is the sum over the
channels `g ⊗ h → g * h`. -/
theorem sum_sum_ofMul [Fintype M] {β : Type*} [AddCommMonoid β] (g h : M)
    (φ : ∀ f, Fin ((ofMul M).N g h f) → β) : ∑ f, ∑ k, φ f k = ∑ k, φ (g * h) k :=
  Fintype.sum_eq_single (g * h) fun _ hf ↦
    have := isEmpty_fin_ofMul_N (Ne.symm hf); Fintype.sum_empty _

instance (g h l : M) : Subsingleton (Fin ((ofMul M).N g h l)) :=
  Fin.subsingleton_iff_le_one.mpr <| by rw [ofMul_N]; split_ifs <;> simp

instance (a b c d : M) : Subsingleton ((ofMul M).Left a b c d) :=
  ⟨by
    rintro ⟨e, i, j⟩ ⟨e', i', j'⟩
    obtain rfl := mul_eq_of_ofMul i
    obtain rfl := mul_eq_of_ofMul i'
    rw [Subsingleton.elim i i', Subsingleton.elim j j']⟩

instance (a b c d : M) : Subsingleton ((ofMul M).Right a b c d) :=
  ⟨by
    rintro ⟨f, k, l⟩ ⟨f', k', l'⟩
    obtain rfl := mul_eq_of_ofMul k
    obtain rfl := mul_eq_of_ofMul k'
    rw [Subsingleton.elim k k', Subsingleton.elim l l']⟩

section Subsingleton

variable [Subsingleton ι]

instance (a b c : ι) : Subsingleton (Fin (N.N a b c)) :=
  Fin.subsingleton_iff_le_one.mpr (N.N_eq_one_of_subsingleton a b c).le

instance (a b c d : ι) : Subsingleton (N.Left a b c d) :=
  ⟨by
    rintro ⟨e, i, j⟩ ⟨e', i', j'⟩
    obtain rfl := Subsingleton.elim e e'
    rw [Subsingleton.elim i i', Subsingleton.elim j j']⟩

instance (a b c d : ι) : Subsingleton (N.Right a b c d) :=
  ⟨by
    rintro ⟨f, k, l⟩ ⟨f', k', l'⟩
    obtain rfl := Subsingleton.elim f f'
    rw [Subsingleton.elim k k', Subsingleton.elim l l']⟩

end Subsingleton

end FusionRules

namespace FSymbols

variable [Fintype ι] [DecidableEq ι] {R : Type v} [CommSemiring R] {N : FusionRules ι}

/-- **Associativity of the fusion rules.** Over a nontrivial commutative semiring, the existence
of F-symbols forces `∑ e, N_{ab}^e N_{ec}^d = ∑ f, N_{bc}^f N_{af}^d`: the two sides count the
rows and the columns of the invertible matrix `F^{abc}_d`. -/
theorem N_assoc [Nontrivial R] (P : FSymbols R N) (a b c d : ι) :
    ∑ e, N.N a b e * N.N e c d = ∑ f, N.N b c f * N.N a f d := by
  simpa using Matrix.square_of_invertible _ _ (P.F_mul_Finv a b c d) (P.Finv_mul_F a b c d)

section Subsingleton

variable [Subsingleton ι]

/-- With a single simple object, every entry of every F-matrix is `1`: the triangle equation
computes the single entry. -/
@[simp]
theorem F_apply_of_subsingleton (P : FSymbols R N) {a b c d : ι} (x : N.Left a b c d)
    (y : N.Right a b c d) : P.F a b c d x y = 1 := by
  obtain rfl := Subsingleton.elim a N.unit
  obtain rfl := Subsingleton.elim b N.unit
  obtain rfl := Subsingleton.elim c N.unit
  obtain rfl := Subsingleton.elim d N.unit
  obtain rfl := Subsingleton.elim x ⟨N.unit, N.unitRight N.unit, N.unitRight N.unit⟩
  obtain rfl := Subsingleton.elim y ⟨N.unit, N.unitLeft N.unit, N.unitRight N.unit⟩
  simpa using P.triangle N.unit N.unit N.unit (N.unitRight N.unit) (N.unitRight N.unit)

/-- With a single simple object, there is exactly one F-symbols over any commutative semiring,
the one with all entries `1`. -/
instance : Unique (FSymbols R N) where
  default :=
    { F _ _ _ _ := Matrix.of fun _ _ ↦ 1
      Finv _ _ _ _ := Matrix.of fun _ _ ↦ 1
      F_mul_Finv _ _ _ _ := by
        ext x y
        simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim x y,
          Fintype.sum_subsingleton _ N.unit]
      Finv_mul_F _ _ _ _ := by
        ext x y
        simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim x y,
          Fintype.sum_subsingleton _ N.unit]
      pentagon := by
        intros
        simp [Fintype.sum_subsingleton _ N.unit]
      triangle _ _ _ j l := by simp [Subsingleton.elim j l] }
  uniq P := by
    ext a b c d x y
    exact P.F_apply_of_subsingleton x y

/-- With a single simple object, every entry of every inverse F-matrix is `1`. -/
@[simp]
theorem Finv_apply_of_subsingleton (P : FSymbols R N) {a b c d : ι} (y : N.Right a b c d)
    (x : N.Left a b c d) : P.Finv a b c d y x = 1 := by
  simpa [Matrix.mul_apply, Fintype.sum_subsingleton _ x] using
    congr_fun₂ (P.Finv_mul_F a b c d) y y

end Subsingleton

/-- Over the zero ring, F-symbols are unique. -/
instance [Subsingleton R] : Subsingleton (FSymbols R N) :=
  ⟨fun _ _ ↦ by ext; exact Subsingleton.elim _ _⟩

/-- Over the zero ring, every fusion rules carry F-symbols: every matrix identity holds there. -/
instance [Subsingleton R] : Nonempty (FSymbols R N) :=
  ⟨{ F _ _ _ _ := 0
     Finv _ _ _ _ := 0
     F_mul_Finv _ _ _ _ := by ext; exact Subsingleton.elim _ _
     Finv_mul_F _ _ _ _ := by ext; exact Subsingleton.elim _ _
     pentagon := by intros; exact Subsingleton.elim _ _
     triangle := by intros; exact Subsingleton.elim _ _ }⟩

section ofMul

variable (R) (M : Type u) [Monoid M] [Fintype M] [DecidableEq M]

/-- The F-symbols of the group fusion rules of a monoid with all entries `1`. For a group `G`,
these describe the category of `G`-graded modules with its standard associator. -/
def ofMul : FSymbols R (FusionRules.ofMul M) where
  F _ _ _ _ := Matrix.of fun _ _ ↦ 1
  Finv _ _ _ _ := Matrix.of fun _ _ ↦ 1
  F_mul_Finv a b c d := by
    ext ⟨e, i, j⟩ y
    obtain rfl := FusionRules.mul_eq_of_ofMul i
    obtain rfl := FusionRules.mul_eq_of_ofMul j
    simp only [Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type,
      FusionRules.sum_sum_ofMul]
    simp [Matrix.one_apply, Subsingleton.elim _ y, mul_assoc]
  Finv_mul_F a b c d := by
    ext ⟨f, k, l⟩ y
    obtain rfl := FusionRules.mul_eq_of_ofMul k
    obtain rfl := FusionRules.mul_eq_of_ofMul l
    simp only [Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type,
      FusionRules.sum_sum_ofMul]
    simp [Matrix.one_apply, Subsingleton.elim _ y, mul_assoc]
  pentagon A B C D E p q r s i₁ i₂ i₃ k m n := by
    obtain rfl := FusionRules.mul_eq_of_ofMul i₁
    obtain rfl := FusionRules.mul_eq_of_ofMul i₂
    obtain rfl := FusionRules.mul_eq_of_ofMul i₃
    obtain rfl := FusionRules.mul_eq_of_ofMul k
    obtain rfl := FusionRules.mul_eq_of_ofMul m
    rw [FusionRules.sum_sum_ofMul]
    simp [FusionRules.ofMul_N, mul_assoc]
  triangle _ _ _ j l := by simp [Subsingleton.elim j l]

@[simp]
theorem ofMul_F {a b c d : M} (x : (FusionRules.ofMul M).Left a b c d)
    (y : (FusionRules.ofMul M).Right a b c d) : (ofMul R M).F a b c d x y = 1 := (rfl)

@[simp]
theorem ofMul_Finv {a b c d : M} (y : (FusionRules.ofMul M).Right a b c d)
    (x : (FusionRules.ofMul M).Left a b c d) : (ofMul R M).Finv a b c d y x = 1 := (rfl)

end ofMul

end FSymbols

namespace RSymbols

variable [Fintype ι] [DecidableEq ι] {K : Type v} [CommSemiring K] {N : FusionRules ι}
  {P : FSymbols K N}

/-- **Commutativity of the fusion rules.** Over a nontrivial commutative semiring, the existence
of R-symbols forces `N_{ab}^c = N_{ba}^c`: the two sides count the rows and the columns of the
invertible matrix `R^{ab}_c`. -/
theorem N_comm [Nontrivial K] (Q : RSymbols P) (a b c : ι) : N.N a b c = N.N b a c := by
  simpa using Matrix.square_of_invertible _ _ (Q.R_mul_Rinv a b c) (Q.Rinv_mul_R a b c)

section Subsingleton

variable [Subsingleton ι]

/-- With a single simple object, every entry of every R-matrix is `1`: the forward hexagon
equation at the unit says that the single entry `r` satisfies `r = r * r`, and `r` is
invertible. -/
@[simp]
theorem R_apply_of_subsingleton (Q : RSymbols P) {a b c : ι} (i : Fin (N.N a b c))
    (j : Fin (N.N b a c)) : Q.R a b c i j = 1 := by
  obtain rfl := Subsingleton.elim a N.unit
  obtain rfl := Subsingleton.elim b N.unit
  obtain rfl := Subsingleton.elim c N.unit
  rw [Subsingleton.elim j i]
  have hex := Q.hexagon_forward N.unit N.unit N.unit N.unit N.unit N.unit i i i i
  have hinv := congr_fun₂ (Q.R_mul_Rinv N.unit N.unit N.unit) i i
  simp only [Fintype.sum_subsingleton _ N.unit, Fintype.sum_subsingleton _ i,
    FSymbols.F_apply_of_subsingleton, mul_one, one_mul] at hex
  simp only [Matrix.mul_apply, Fintype.sum_subsingleton _ i, Matrix.one_apply_eq] at hinv
  set r := Q.R N.unit N.unit N.unit i i
  calc r = r * (r * Q.Rinv N.unit N.unit N.unit i i) := by rw [hinv, mul_one]
    _ = 1 := by rw [← mul_assoc, ← hex, hinv]

/-- With a single simple object, there is exactly one R-symbols for the F-symbols over any
commutative semiring, the one with all entries `1`. -/
instance : Unique (RSymbols P) where
  default :=
    { R _ _ _ := Matrix.of fun _ _ ↦ 1
      Rinv _ _ _ := Matrix.of fun _ _ ↦ 1
      R_mul_Rinv _ _ _ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j]
      Rinv_mul_R _ _ _ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j]
      hexagon_forward := by
        intros
        simp [Fintype.sum_subsingleton _ N.unit]
      hexagon_reverse := by
        intros
        simp [Fintype.sum_subsingleton _ N.unit] }
  uniq Q := by
    ext a b c i j
    exact Q.R_apply_of_subsingleton i j

end Subsingleton

/-- Over the zero ring, R-symbols are unique. -/
instance [Subsingleton K] : Subsingleton (RSymbols P) :=
  ⟨fun _ _ ↦ by ext; exact Subsingleton.elim _ _⟩

/-- Over the zero ring, all F-symbols carry R-symbols: every matrix identity holds there. -/
instance [Subsingleton K] : Nonempty (RSymbols P) :=
  ⟨{ R _ _ _ := 0
     Rinv _ _ _ := 0
     R_mul_Rinv _ _ _ := by ext; exact Subsingleton.elim _ _
     Rinv_mul_R _ _ _ := by ext; exact Subsingleton.elim _ _
     hexagon_forward := by intros; exact Subsingleton.elim _ _
     hexagon_reverse := by intros; exact Subsingleton.elim _ _ }⟩

section ofMul

variable (K) (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M]

/-- The R-symbols with all entries `1` for the F-symbols `TauCeti.FSymbols.ofMul` of a
commutative monoid. For an abelian group `G`, these describe the symmetric braiding of the
category of `G`-graded modules that exchanges the tensor factors without signs. -/
def ofMul : RSymbols (FSymbols.ofMul K M) where
  R _ _ _ := Matrix.of fun _ _ ↦ 1
  Rinv _ _ _ := Matrix.of fun _ _ ↦ 1
  R_mul_Rinv a b c := by
    ext i j
    obtain rfl := FusionRules.mul_eq_of_ofMul i
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j, FusionRules.ofMul_N,
      mul_comm b a]
  Rinv_mul_R a b c := by
    ext i j
    obtain rfl := FusionRules.mul_eq_of_ofMul i
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j, FusionRules.ofMul_N,
      mul_comm b a]
  hexagon_forward a b c d e g i j n o := by
    obtain rfl := FusionRules.mul_eq_of_ofMul i
    obtain rfl := FusionRules.mul_eq_of_ofMul j
    obtain rfl := FusionRules.mul_eq_of_ofMul n
    rw [FusionRules.sum_sum_ofMul]
    simp [FusionRules.ofMul_N, mul_comm, mul_left_comm]
  hexagon_reverse a b c d f g k l n o := by
    obtain rfl := FusionRules.mul_eq_of_ofMul k
    obtain rfl := FusionRules.mul_eq_of_ofMul l
    obtain rfl := FusionRules.mul_eq_of_ofMul n
    rw [FusionRules.sum_sum_ofMul]
    simp [FusionRules.ofMul_N, mul_comm, mul_left_comm]

@[simp]
theorem ofMul_R {a b c : M} (i : Fin ((FusionRules.ofMul M).N a b c))
    (j : Fin ((FusionRules.ofMul M).N b a c)) : (ofMul K M).R a b c i j = 1 := (rfl)

@[simp]
theorem ofMul_Rinv {a b c : M} (j : Fin ((FusionRules.ofMul M).N b a c))
    (i : Fin ((FusionRules.ofMul M).N a b c)) : (ofMul K M).Rinv a b c j i = 1 := (rfl)

end ofMul

/-- Over a nontrivial commutative semiring, the group fusion rules of a noncommutative
multiplication carry no R-symbols: for `a * b ≠ b * a`, the matrix `R^{ab}_{ab}` would be an
invertible matrix with one row and no columns. -/
protected theorem mul_comm [Nontrivial K] {M : Type u} [MulOneClass M] [Fintype M] [DecidableEq M]
    {P : FSymbols K (FusionRules.ofMul M)} (Q : RSymbols P) (a b : M) : a * b = b * a := by
  have h := Q.N_comm a b (a * b)
  simp only [FusionRules.ofMul_N, ite_true] at h
  split_ifs at h with hba
  exact hba.symm

/-- Over a nontrivial commutative semiring, the F-symbols with all entries `1` of the group fusion
rules of a finite monoid carry R-symbols exactly when the monoid is commutative. -/
theorem nonempty_ofMul_iff [Nontrivial K] {M : Type u} [Monoid M] [Fintype M] [DecidableEq M] :
    Nonempty (RSymbols (FSymbols.ofMul K M)) ↔ ∀ a b : M, a * b = b * a := by
  refine ⟨fun ⟨Q⟩ ↦ Q.mul_comm, fun h ↦ ?_⟩
  let : CommMonoid M := { ‹Monoid M› with mul_comm := h }
  exact ⟨ofMul K M⟩

end RSymbols

end TauCeti
