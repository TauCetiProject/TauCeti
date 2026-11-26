/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Data.Matrix.Mul

/-!
# First consequences of F-symbols and R-symbols

This file derives what the invertibility, pentagon, triangle and hexagon equations of the F- and
R-matrices force on the fusion rules and on unit-indexed blocks, and computes F- and R-symbols in
the degenerate cases.

* **Invertibility.** Over a nontrivial commutative semiring, an invertible rectangular matrix is
  square. Applied to `F^{abc}_d`, whose rows are indexed by `Σ e, Fin N_{ab}^e × Fin N_{ec}^d` and
  columns by `Σ f, Fin N_{bc}^f × Fin N_{af}^d`, this gives associativity of the fusion rules,
  `∑ e, N_{ab}^e N_{ec}^d = ∑ f, N_{bc}^f N_{af}^d` (`TauCeti.FSymbols.N_assoc`). Applied to
  `R^{ab}_c`, it gives commutativity, `N_{ab}^c = N_{ba}^c` (`TauCeti.RSymbols.N_comm`).
* **Derived unit triangles and unit braidings.** Only the middle-unit triangle `F^{auc}_d = 1` is
  imposed in `TauCeti.FSymbols`. Specializing the pentagon at the unit and using invertibility
  yields the outer unit triangles `F^{ubc}_d = 1` (`TauCeti.FSymbols.F_unit_left`) and
  `F^{abu}_d = 1` (`TauCeti.FSymbols.F_unit_right`), together with their `Finv` counterparts;
  specializing the hexagons at the unit yields `R^{au}_c = 1` (`TauCeti.RSymbols.R_unit_right`) and
  `R^{ua}_c = 1` (`TauCeti.RSymbols.R_unit_left`).
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
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §2.2
  (Proposition 2.2.4, outer unit triangles from the pentagon and middle triangle).
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

/-! ### Unit specializations, derived unit triangles, and unit braidings -/

namespace FusionRules

variable (N : FusionRules ι)

/-- An index in `Fin N_{ua}^b` forces `a = b`. -/
theorem eq_of_fin_unit_left {a b : ι} (i : Fin (N.N N.unit a b)) : a = b := by
  by_contra h
  exact Nat.not_lt_zero i.val (N.N_unit_left_of_ne a b h ▸ i.isLt)

/-- An index in `Fin N_{au}^b` forces `a = b`. -/
theorem eq_of_fin_unit_right {a b : ι} (i : Fin (N.N a N.unit b)) : a = b := by
  by_contra h
  exact Nat.not_lt_zero i.val (N.N_unit_right_of_ne a b h ▸ i.isLt)

@[simp]
theorem default_fin_unit_left (a : ι) : (default : Fin (N.N N.unit a a)) = N.unitLeft a :=
  Subsingleton.elim _ _

@[simp]
theorem default_fin_unit_right (a : ι) : (default : Fin (N.N a N.unit a)) = N.unitRight a :=
  Subsingleton.elim _ _

theorem fin_unit_left_eq (a : ι) (i : Fin (N.N N.unit a a)) : i = N.unitLeft a :=
  Subsingleton.elim i (N.unitLeft a)

theorem fin_unit_right_eq (a : ι) (i : Fin (N.N a N.unit a)) : i = N.unitRight a :=
  Subsingleton.elim i (N.unitRight a)

section UnitSums

variable {M : Type*} [AddCommMonoid M]

theorem sum_fin_unit_left_self (a : ι) (f : Fin (N.N N.unit a a) → M) :
    ∑ i, f i = f (N.unitLeft a) :=
  (Fintype.sum_unique f).trans (congrArg f (Subsingleton.elim _ _))

theorem sum_fin_unit_right_self (a : ι) (f : Fin (N.N a N.unit a) → M) :
    ∑ i, f i = f (N.unitRight a) :=
  (Fintype.sum_unique f).trans (congrArg f (Subsingleton.elim _ _))

theorem sum_fin_unit_left_of_ne {a b : ι} (h : a ≠ b) (f : Fin (N.N N.unit a b) → M) :
    ∑ i, f i = 0 :=
  have : IsEmpty (Fin (N.N N.unit a b)) := ⟨fun i ↦ h (N.eq_of_fin_unit_left i)⟩
  Fintype.sum_empty f

theorem sum_fin_unit_right_of_ne {a b : ι} (h : a ≠ b) (f : Fin (N.N a N.unit b) → M) :
    ∑ i, f i = 0 :=
  have : IsEmpty (Fin (N.N a N.unit b)) := ⟨fun i ↦ h (N.eq_of_fin_unit_right i)⟩
  Fintype.sum_empty f

variable [Fintype ι]

/-- Summing over `(e, i)` with `i : Fin N_{ua}^e` collapses to `e = a` and `i = unitLeft a`. -/
theorem sum_fin_unit_left_fst (a : ι) (f : ∀ e : ι, Fin (N.N N.unit a e) → M) :
    ∑ e : ι, ∑ i : Fin (N.N N.unit a e), f e i = f a (N.unitLeft a) := by
  classical
  rw [Fintype.sum_eq_single a fun e he ↦ N.sum_fin_unit_left_of_ne he.symm (f e),
    N.sum_fin_unit_left_self]

/-- Summing over `(e, i)` with `i : Fin N_{ue}^b` collapses to `e = b` and `i = unitLeft b`. -/
theorem sum_fin_unit_left_snd (b : ι) (f : ∀ e : ι, Fin (N.N N.unit e b) → M) :
    ∑ e : ι, ∑ i : Fin (N.N N.unit e b), f e i = f b (N.unitLeft b) := by
  classical
  rw [Fintype.sum_eq_single b fun e he ↦ N.sum_fin_unit_left_of_ne he (f e),
    N.sum_fin_unit_left_self]

/-- Summing over `(e, i)` with `i : Fin N_{au}^e` collapses to `e = a` and `i = unitRight a`. -/
theorem sum_fin_unit_right_fst (a : ι) (f : ∀ e : ι, Fin (N.N a N.unit e) → M) :
    ∑ e : ι, ∑ i : Fin (N.N a N.unit e), f e i = f a (N.unitRight a) := by
  classical
  rw [Fintype.sum_eq_single a fun e he ↦ N.sum_fin_unit_right_of_ne he.symm (f e),
    N.sum_fin_unit_right_self]

/-- Summing over `(e, i)` with `i : Fin N_{eu}^b` collapses to `e = b` and `i = unitRight b`. -/
theorem sum_fin_unit_right_snd (b : ι) (f : ∀ e : ι, Fin (N.N e N.unit b) → M) :
    ∑ e : ι, ∑ i : Fin (N.N e N.unit b), f e i = f b (N.unitRight b) := by
  classical
  rw [Fintype.sum_eq_single b fun e he ↦ N.sum_fin_unit_right_of_ne he (f e),
    N.sum_fin_unit_right_self]

end UnitSums

/-- `Left a u c d` is equivalent to `Fin N_{ac}^d`, with inverse `j ↦ ⟨a, unitRight a, j⟩`. -/
def leftUnitMidEquiv (a c d : ι) : N.Left a N.unit c d ≃ Fin (N.N a c d) where
  toFun x := N.eq_of_fin_unit_right x.snd.fst ▸ x.snd.snd
  invFun j := ⟨a, N.unitRight a, j⟩
  left_inv := by rintro ⟨_, i, _⟩; obtain rfl := N.eq_of_fin_unit_right i; simp [fin_unit_right_eq]
  right_inv _ := rfl

@[simp]
theorem leftUnitMidEquiv_symm_apply (a c d : ι) (j : Fin (N.N a c d)) :
    (N.leftUnitMidEquiv a c d).symm j = ⟨a, N.unitRight a, j⟩ := (rfl)

@[simp]
theorem leftUnitMidEquiv_mk (a c d : ι) (j : Fin (N.N a c d)) :
    N.leftUnitMidEquiv a c d ⟨a, N.unitRight a, j⟩ = j :=
  (N.leftUnitMidEquiv a c d).apply_symm_apply j

/-- `Right a u c d` is equivalent to `Fin N_{ac}^d`, with inverse `l ↦ ⟨c, unitLeft c, l⟩`. -/
def rightUnitMidEquiv (a c d : ι) : N.Right a N.unit c d ≃ Fin (N.N a c d) where
  toFun y := N.eq_of_fin_unit_left y.snd.fst ▸ y.snd.snd
  invFun l := ⟨c, N.unitLeft c, l⟩
  left_inv := by rintro ⟨_, k, _⟩; obtain rfl := N.eq_of_fin_unit_left k; simp [fin_unit_left_eq]
  right_inv _ := rfl

@[simp]
theorem rightUnitMidEquiv_symm_apply (a c d : ι) (l : Fin (N.N a c d)) :
    (N.rightUnitMidEquiv a c d).symm l = ⟨c, N.unitLeft c, l⟩ := (rfl)

@[simp]
theorem rightUnitMidEquiv_mk (a c d : ι) (l : Fin (N.N a c d)) :
    N.rightUnitMidEquiv a c d ⟨c, N.unitLeft c, l⟩ = l :=
  (N.rightUnitMidEquiv a c d).apply_symm_apply l

/-- `Left u b c d` is equivalent to `Fin N_{bc}^d`, with inverse `j ↦ ⟨b, unitLeft b, j⟩`. -/
def leftUnitLeftEquiv (b c d : ι) : N.Left N.unit b c d ≃ Fin (N.N b c d) where
  toFun x := N.eq_of_fin_unit_left x.snd.fst ▸ x.snd.snd
  invFun j := ⟨b, N.unitLeft b, j⟩
  left_inv := by rintro ⟨_, i, _⟩; obtain rfl := N.eq_of_fin_unit_left i; simp [fin_unit_left_eq]
  right_inv _ := rfl

@[simp]
theorem leftUnitLeftEquiv_symm_apply (b c d : ι) (j : Fin (N.N b c d)) :
    (N.leftUnitLeftEquiv b c d).symm j = ⟨b, N.unitLeft b, j⟩ := (rfl)

@[simp]
theorem leftUnitLeftEquiv_mk (b c d : ι) (j : Fin (N.N b c d)) :
    N.leftUnitLeftEquiv b c d ⟨b, N.unitLeft b, j⟩ = j :=
  (N.leftUnitLeftEquiv b c d).apply_symm_apply j

/-- `Right u b c d` is equivalent to `Fin N_{bc}^d`, with inverse `k ↦ ⟨d, k, unitLeft d⟩`. -/
def rightUnitLeftEquiv (b c d : ι) : N.Right N.unit b c d ≃ Fin (N.N b c d) where
  toFun y := (N.eq_of_fin_unit_left y.snd.snd).symm ▸ y.snd.fst
  invFun k := ⟨d, k, N.unitLeft d⟩
  left_inv := by rintro ⟨_, _, l⟩; obtain rfl := N.eq_of_fin_unit_left l; simp [fin_unit_left_eq]
  right_inv _ := rfl

@[simp]
theorem rightUnitLeftEquiv_symm_apply (b c d : ι) (k : Fin (N.N b c d)) :
    (N.rightUnitLeftEquiv b c d).symm k = ⟨d, k, N.unitLeft d⟩ := (rfl)

@[simp]
theorem rightUnitLeftEquiv_mk (b c d : ι) (k : Fin (N.N b c d)) :
    N.rightUnitLeftEquiv b c d ⟨d, k, N.unitLeft d⟩ = k :=
  (N.rightUnitLeftEquiv b c d).apply_symm_apply k

/-- `Left a b u d` is equivalent to `Fin N_{ab}^d`, with inverse `i ↦ ⟨d, i, unitRight d⟩`. -/
def leftUnitRightEquiv (a b d : ι) : N.Left a b N.unit d ≃ Fin (N.N a b d) where
  toFun x := (N.eq_of_fin_unit_right x.snd.snd).symm ▸ x.snd.fst
  invFun i := ⟨d, i, N.unitRight d⟩
  left_inv := by rintro ⟨_, _, j⟩; obtain rfl := N.eq_of_fin_unit_right j; simp [fin_unit_right_eq]
  right_inv _ := rfl

@[simp]
theorem leftUnitRightEquiv_symm_apply (a b d : ι) (i : Fin (N.N a b d)) :
    (N.leftUnitRightEquiv a b d).symm i = ⟨d, i, N.unitRight d⟩ := (rfl)

@[simp]
theorem leftUnitRightEquiv_mk (a b d : ι) (i : Fin (N.N a b d)) :
    N.leftUnitRightEquiv a b d ⟨d, i, N.unitRight d⟩ = i :=
  (N.leftUnitRightEquiv a b d).apply_symm_apply i

/-- `Right a b u d` is equivalent to `Fin N_{ab}^d`, with inverse `l ↦ ⟨b, unitRight b, l⟩`. -/
def rightUnitRightEquiv (a b d : ι) : N.Right a b N.unit d ≃ Fin (N.N a b d) where
  toFun y := N.eq_of_fin_unit_right y.snd.fst ▸ y.snd.snd
  invFun l := ⟨b, N.unitRight b, l⟩
  left_inv := by rintro ⟨_, k, _⟩; obtain rfl := N.eq_of_fin_unit_right k; simp [fin_unit_right_eq]
  right_inv _ := rfl

@[simp]
theorem rightUnitRightEquiv_symm_apply (a b d : ι) (l : Fin (N.N a b d)) :
    (N.rightUnitRightEquiv a b d).symm l = ⟨b, N.unitRight b, l⟩ := (rfl)

@[simp]
theorem rightUnitRightEquiv_mk (a b d : ι) (l : Fin (N.N a b d)) :
    N.rightUnitRightEquiv a b d ⟨b, N.unitRight b, l⟩ = l :=
  (N.rightUnitRightEquiv a b d).apply_symm_apply l

end FusionRules

namespace FSymbols

variable [Fintype ι] [DecidableEq ι] {R : Type v} [CommSemiring R] {N : FusionRules ι}

theorem F_injective : Function.Injective (FSymbols.F (R := R) (N := N)) :=
  fun _ _ ↦ ext

/-- Two `FSymbols` with equal `Finv`-matrices are also equal. -/
theorem ext_of_Finv {P Q : FSymbols R N} (h : P.Finv = Q.Finv) : P = Q := by
  ext a b c d x y
  refine congr_fun₂ (Matrix.right_inv_eq_left_inv (Q.Finv_mul_F a b c d) ?_).symm x y
  rw [← h, P.F_mul_Finv]

theorem Finv_injective : Function.Injective (FSymbols.Finv (R := R) (N := N)) :=
  fun _ _ ↦ ext_of_Finv

/-- Entrywise form of `F * Finv = 1`. -/
theorem sum_F_mul_Finv (P : FSymbols R N) (a b c d : ι) (x x' : N.Left a b c d) :
    ∑ y : N.Right a b c d, P.F a b c d x y * P.Finv a b c d y x' = if x = x' then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun₂ (P.F_mul_Finv a b c d) x x'

/-- Entrywise form of `Finv * F = 1`. -/
theorem sum_Finv_mul_F (P : FSymbols R N) (a b c d : ι) (y y' : N.Right a b c d) :
    ∑ x : N.Left a b c d, P.Finv a b c d y x * P.F a b c d x y' = if y = y' then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun₂ (P.Finv_mul_F a b c d) y y'

@[simp]
theorem triangle_self (P : FSymbols R N) (a c d : ι) (j : Fin (N.N a c d)) :
    P.F a N.unit c d ⟨a, N.unitRight a, j⟩ ⟨c, N.unitLeft c, j⟩ = 1 := by
  simp [P.triangle]

theorem triangle_of_ne (P : FSymbols R N) {a c d : ι} {j l : Fin (N.N a c d)} (h : j ≠ l) :
    P.F a N.unit c d ⟨a, N.unitRight a, j⟩ ⟨c, N.unitLeft c, l⟩ = 0 := by
  simp [P.triangle, h]

/-- Left-unit triangle: `F^{ubc}_d[(b,0,j),(d,k,0)] = [j = k]` (EGNO, Proposition 2.2.4). -/
theorem F_unit_left (P : FSymbols R N) (b c d : ι) (j k : Fin (N.N b c d)) :
    P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, k, N.unitLeft d⟩ = if j = k then 1 else 0 := by
  have hu := Matrix.isUnit_submatrix_equiv_of_mul_eq_one (P.F_mul_Finv N.unit b c d)
    (P.Finv_mul_F N.unit b c d) (N.leftUnitLeftEquiv b c d).symm (N.rightUnitLeftEquiv b c d).symm
  have hidem : IsIdempotentElem ((P.F N.unit b c d).submatrix
      (N.leftUnitLeftEquiv b c d).symm (N.rightUnitLeftEquiv b c d).symm) := by
    ext m n
    have hpm := P.pentagon N.unit N.unit b c d N.unit b d d
      (N.unitRight N.unit) (N.unitLeft b) m n (N.unitLeft d) (N.unitLeft d)
    rw [N.sum_fin_unit_left_self, P.triangle_self, mul_one,
      N.sum_fin_unit_left_fst b, N.sum_fin_unit_left_self] at hpm
    simp_rw [P.triangle_self, one_mul] at hpm
    simpa [Matrix.mul_apply] using hpm.symm
  simpa [Matrix.one_apply] using
    congr_fun₂ ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hidem) j k

@[simp]
theorem F_unit_left_self (P : FSymbols R N) (b c d : ι) (j : Fin (N.N b c d)) :
    P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, j, N.unitLeft d⟩ = 1 := by
  simp [P.F_unit_left]

theorem F_unit_left_of_ne (P : FSymbols R N) {b c d : ι} {j k : Fin (N.N b c d)} (h : j ≠ k) :
    P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, k, N.unitLeft d⟩ = 0 := by
  simp [P.F_unit_left, h]

/-- Right-unit triangle: `F^{abu}_d[(d,i,0),(b,0,l)] = [i = l]` (EGNO, Proposition 2.2.4). -/
theorem F_unit_right (P : FSymbols R N) (a b d : ι) (i l : Fin (N.N a b d)) :
    P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, l⟩ = if i = l then 1 else 0 := by
  have hu := Matrix.isUnit_submatrix_equiv_of_mul_eq_one (P.F_mul_Finv a b N.unit d)
    (P.Finv_mul_F a b N.unit d)
    (N.leftUnitRightEquiv a b d).symm (N.rightUnitRightEquiv a b d).symm
  have hidem : IsIdempotentElem ((P.F a b N.unit d).submatrix
      (N.leftUnitRightEquiv a b d).symm (N.rightUnitRightEquiv a b d).symm) := by
    ext m n
    have hpm := P.pentagon a b N.unit N.unit d d d N.unit b
      m (N.unitRight d) (N.unitRight d) (N.unitLeft N.unit) (N.unitRight b) n
    rw [N.sum_fin_unit_right_self, P.triangle_self, one_mul, N.sum_fin_unit_right_fst b] at hpm
    simp_rw [N.sum_fin_unit_right_self, P.triangle_self, mul_one] at hpm
    simpa [Matrix.mul_apply] using hpm.symm
  simpa [Matrix.one_apply] using
    congr_fun₂ ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hidem) i l

@[simp]
theorem F_unit_right_self (P : FSymbols R N) (a b d : ι) (i : Fin (N.N a b d)) :
    P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, i⟩ = 1 := by
  simp [P.F_unit_right]

theorem F_unit_right_of_ne (P : FSymbols R N) {a b d : ι} {i l : Fin (N.N a b d)} (h : i ≠ l) :
    P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, l⟩ = 0 := by
  simp [P.F_unit_right, h]

/-- Inverse middle-unit triangle: `Finv^{auc}_d[(c,0,l),(a,0,j)] = [l = j]`. -/
theorem Finv_triangle (P : FSymbols R N) (a c d : ι) (l j : Fin (N.N a c d)) :
    P.Finv a N.unit c d ⟨c, N.unitLeft c, l⟩ ⟨a, N.unitRight a, j⟩ = if l = j then 1 else 0 := by
  have h := P.sum_Finv_mul_F a N.unit c d ⟨c, N.unitLeft c, l⟩ ⟨c, N.unitLeft c, j⟩
  rw [← (N.leftUnitMidEquiv a c d).symm.sum_comp] at h
  simpa [P.triangle] using h

@[simp]
theorem Finv_triangle_self (P : FSymbols R N) (a c d : ι) (j : Fin (N.N a c d)) :
    P.Finv a N.unit c d ⟨c, N.unitLeft c, j⟩ ⟨a, N.unitRight a, j⟩ = 1 := by
  simp [P.Finv_triangle]

theorem Finv_triangle_of_ne (P : FSymbols R N) {a c d : ι} {l j : Fin (N.N a c d)} (h : l ≠ j) :
    P.Finv a N.unit c d ⟨c, N.unitLeft c, l⟩ ⟨a, N.unitRight a, j⟩ = 0 := by
  simp [P.Finv_triangle, h]

/-- Inverse left-unit triangle: `Finv^{ubc}_d[(d,k,0),(b,0,j)] = [k = j]`. -/
theorem Finv_unit_left (P : FSymbols R N) (b c d : ι) (k j : Fin (N.N b c d)) :
    P.Finv N.unit b c d ⟨d, k, N.unitLeft d⟩ ⟨b, N.unitLeft b, j⟩ = if k = j then 1 else 0 := by
  have h := P.sum_Finv_mul_F N.unit b c d ⟨d, k, N.unitLeft d⟩ ⟨d, j, N.unitLeft d⟩
  rw [← (N.leftUnitLeftEquiv b c d).symm.sum_comp] at h
  simpa [P.F_unit_left] using h

@[simp]
theorem Finv_unit_left_self (P : FSymbols R N) (b c d : ι) (j : Fin (N.N b c d)) :
    P.Finv N.unit b c d ⟨d, j, N.unitLeft d⟩ ⟨b, N.unitLeft b, j⟩ = 1 := by
  simp [P.Finv_unit_left]

theorem Finv_unit_left_of_ne (P : FSymbols R N) {b c d : ι} {k j : Fin (N.N b c d)} (h : k ≠ j) :
    P.Finv N.unit b c d ⟨d, k, N.unitLeft d⟩ ⟨b, N.unitLeft b, j⟩ = 0 := by
  simp [P.Finv_unit_left, h]

/-- Inverse right-unit triangle: `Finv^{abu}_d[(b,0,l),(d,i,0)] = [l = i]`. -/
theorem Finv_unit_right (P : FSymbols R N) (a b d : ι) (l i : Fin (N.N a b d)) :
    P.Finv a b N.unit d ⟨b, N.unitRight b, l⟩ ⟨d, i, N.unitRight d⟩ = if l = i then 1 else 0 := by
  have h := P.sum_Finv_mul_F a b N.unit d ⟨b, N.unitRight b, l⟩ ⟨b, N.unitRight b, i⟩
  rw [← (N.leftUnitRightEquiv a b d).symm.sum_comp] at h
  simpa [P.F_unit_right] using h

@[simp]
theorem Finv_unit_right_self (P : FSymbols R N) (a b d : ι) (i : Fin (N.N a b d)) :
    P.Finv a b N.unit d ⟨b, N.unitRight b, i⟩ ⟨d, i, N.unitRight d⟩ = 1 := by
  simp [P.Finv_unit_right]

theorem Finv_unit_right_of_ne (P : FSymbols R N) {a b d : ι} {l i : Fin (N.N a b d)} (h : l ≠ i) :
    P.Finv a b N.unit d ⟨b, N.unitRight b, l⟩ ⟨d, i, N.unitRight d⟩ = 0 := by
  simp [P.Finv_unit_right, h]

end FSymbols

namespace RSymbols

variable [Fintype ι] [DecidableEq ι] {K : Type v} [CommSemiring K] {N : FusionRules ι}
  {P : FSymbols K N}

theorem R_injective : Function.Injective (RSymbols.R (P := P)) :=
  fun _ _ ↦ ext

/-- Two `RSymbols` for `P` with equal `Rinv`-matrices are also equal. -/
theorem ext_of_Rinv {Q₁ Q₂ : RSymbols P} (h : Q₁.Rinv = Q₂.Rinv) : Q₁ = Q₂ := by
  ext a b c i j
  refine congr_fun₂ (Matrix.right_inv_eq_left_inv (Q₂.Rinv_mul_R a b c) ?_).symm i j
  rw [← h, Q₁.R_mul_Rinv]

theorem Rinv_injective : Function.Injective (RSymbols.Rinv (P := P)) :=
  fun _ _ ↦ ext_of_Rinv

/-- Entrywise form of `R * Rinv = 1`. -/
theorem sum_R_mul_Rinv (Q : RSymbols P) (a b c : ι) (i i' : Fin (N.N a b c)) :
    ∑ j : Fin (N.N b a c), Q.R a b c i j * Q.Rinv a b c j i' = if i = i' then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun₂ (Q.R_mul_Rinv a b c) i i'

/-- Entrywise form of `Rinv * R = 1`. -/
theorem sum_Rinv_mul_R (Q : RSymbols P) (a b c : ι) (j j' : Fin (N.N b a c)) :
    ∑ i : Fin (N.N a b c), Q.Rinv a b c j i * Q.R a b c i j' = if j = j' then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun₂ (Q.Rinv_mul_R a b c) j j'

/-- Transport `RSymbols` along an equality of the underlying `FSymbols`. -/
def cast {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) : RSymbols P₂ := h ▸ Q

@[simp]
theorem cast_R {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) :
    (Q.cast h).R = Q.R := by cases h; rfl

@[simp]
theorem cast_Rinv {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) :
    (Q.cast h).Rinv = Q.Rinv := by cases h; rfl

@[simp]
theorem cast_rfl (Q : RSymbols P) : Q.cast rfl = Q := (rfl)

@[simp]
theorem cast_cast {P₁ P₂ P₃ : FSymbols K N} (h₁ : P₁ = P₂) (h₂ : P₂ = P₃) (Q : RSymbols P₁) :
    (Q.cast h₁).cast h₂ = Q.cast (h₁.trans h₂) := by cases h₁; cases h₂; rfl

/-- Equivalence between `RSymbols P₁` and `RSymbols P₂` induced by `h : P₁ = P₂`. -/
def castEquiv {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) : RSymbols P₁ ≃ RSymbols P₂ where
  toFun := cast h
  invFun := cast h.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
theorem castEquiv_apply {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) :
    castEquiv h Q = Q.cast h := (rfl)

@[simp]
theorem castEquiv_symm_apply {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₂) :
    (castEquiv h).symm Q = Q.cast h.symm := (rfl)

/-- Right-unit braiding law: `R^{au}_c = 1` on every unit-indexed entry. -/
@[simp]
theorem R_unit_right (Q : RSymbols P) (a c : ι) (i : Fin (N.N a N.unit c))
    (j : Fin (N.N N.unit a c)) : Q.R a N.unit c i j = 1 := by
  obtain rfl := N.eq_of_fin_unit_right i
  rw [N.fin_unit_right_eq a i, N.fin_unit_left_eq a j]
  have hhex := Q.hexagon_forward a N.unit N.unit a a a
    (N.unitRight a) (N.unitRight a) (N.unitLeft a) (N.unitLeft a)
  rw [N.sum_fin_unit_left_fst N.unit] at hhex
  simp only [FusionRules.sum_fin_unit_right_self, FusionRules.sum_fin_unit_left_self,
    P.triangle_self, P.F_unit_left_self, one_mul, mul_one] at hhex
  have hinv : Q.R a N.unit a (N.unitRight a) (N.unitLeft a) *
      Q.Rinv a N.unit a (N.unitLeft a) (N.unitRight a) = 1 := by
    simpa using Q.sum_R_mul_Rinv a N.unit a (N.unitRight a) (N.unitRight a)
  exact (IsIdempotentElem.iff_eq_one_of_isUnit (.of_mul_eq_one _ hinv)).mp hhex.symm

/-- Inverse right-unit braiding law: `Rinv^{au}_c = 1` on every unit-indexed entry. -/
@[simp]
theorem Rinv_unit_right (Q : RSymbols P) (a c : ι) (j : Fin (N.N N.unit a c))
    (i : Fin (N.N a N.unit c)) : Q.Rinv a N.unit c j i = 1 := by
  obtain rfl := N.eq_of_fin_unit_right i
  rw [N.fin_unit_left_eq a j, N.fin_unit_right_eq a i]
  simpa using Q.sum_R_mul_Rinv a N.unit a (N.unitRight a) (N.unitRight a)

/-- Left-unit braiding law: `R^{ua}_c = 1` on every unit-indexed entry. -/
@[simp]
theorem R_unit_left (Q : RSymbols P) (a c : ι) (i : Fin (N.N N.unit a c))
    (j : Fin (N.N a N.unit c)) : Q.R N.unit a c i j = 1 := by
  obtain rfl := N.eq_of_fin_unit_left i
  rw [N.fin_unit_left_eq a i, N.fin_unit_right_eq a j]
  have hhex := Q.hexagon_reverse N.unit N.unit a a a a
    (N.unitLeft a) (N.unitLeft a) (N.unitRight a) (N.unitRight a)
  rw [N.sum_fin_unit_left_fst N.unit] at hhex
  simp only [FusionRules.sum_fin_unit_left_self, FusionRules.sum_fin_unit_right_self,
    P.Finv_unit_left_self, P.Finv_triangle_self, one_mul, mul_one] at hhex
  have hinv : Q.R N.unit a a (N.unitLeft a) (N.unitRight a) *
      Q.Rinv N.unit a a (N.unitRight a) (N.unitLeft a) = 1 := by
    simpa using Q.sum_R_mul_Rinv N.unit a a (N.unitLeft a) (N.unitLeft a)
  exact (IsIdempotentElem.iff_eq_one_of_isUnit (.of_mul_eq_one _ hinv)).mp hhex.symm

/-- Inverse left-unit braiding law: `Rinv^{ua}_c = 1` on every unit-indexed entry. -/
@[simp]
theorem Rinv_unit_left (Q : RSymbols P) (a c : ι) (j : Fin (N.N a N.unit c))
    (i : Fin (N.N N.unit a c)) : Q.Rinv N.unit a c j i = 1 := by
  obtain rfl := N.eq_of_fin_unit_left i
  rw [N.fin_unit_right_eq a j, N.fin_unit_left_eq a i]
  simpa using Q.sum_R_mul_Rinv N.unit a a (N.unitLeft a) (N.unitLeft a)

end RSymbols

end TauCeti
