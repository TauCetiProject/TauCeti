/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
# Fusion rules, F-symbols, and R-symbols

A split semisimple linear monoidal category with finitely many simple objects `S_a` (`a : ι`) and
scalar endomorphism rings `End(S_a) = R` is determined up to linear monoidal equivalence by its
fusion multiplicities `N_{ab}^c` and its F-matrices `F^{abc}_d` relating the left- and
right-associated fusion bases across the associator. A braiding on such a category is similarly
determined by its R-matrices `R^{ab}_c` relating each fusion basis to the braided one.

This file defines these matrix-level presentation data over a commutative ring `R` and develops
their basic structural consequences:

* `TauCeti.FusionRules ι`: a distinguished unit index `u : ι` and fusion multiplicities
  `N : ι → ι → ι → ℕ` satisfying the left and right unit laws
  `N_{ua}^b = N_{au}^b = δ_{ab}`, along with the composite basis index types `FusionRules.Left`
  and `FusionRules.Right` and their canonical specializations when one factor is the unit.
* `TauCeti.FSymbols R N`: families of matrices `F^{abc}_d` and two-sided inverses `Finv^{abc}_d`
  satisfying the pentagon and middle-unit triangle identities, extensional in `F`
  (`TauCeti.FSymbols.ext`). From the pentagon, middle triangle, and invertibility we derive the
  outer unit triangles `F^{ubc}_d = 1` (`TauCeti.FSymbols.F_unit_left`) and `F^{abu}_d = 1`
  (`TauCeti.FSymbols.F_unit_right`), and over a nontrivial commutative ring the associativity of
  fusion multiplicities (`TauCeti.FSymbols.N_assoc`).
* `TauCeti.RSymbols P`: families of matrices `R^{ab}_c` and two-sided inverses `Rinv^{ab}_c` for
  given F-symbols `P`, satisfying the forward and reverse hexagon identities and extensional in `R`
  (`TauCeti.RSymbols.ext`). From the hexagons we derive the unit braiding laws `R^{ua}_a = 1` and
  `R^{au}_a = 1`, and over a nontrivial commutative ring the commutativity of fusion multiplicities
  (`TauCeti.RSymbols.N_comm`).

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §2.2 (Prop. 2.2.4)
  and §4.9 ((4.12)–(4.13), p. 77).
* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics **321** (2006),
  Appendix E, §E.1 (eq. (177), Fig. 17a) and §E.3 (eq. (207), Fig. 20).
-/

public section

namespace TauCeti

universe u v

/-! ### Fusion rules and composite basis indices -/

/-- **Fusion rules** on an index type `ι` with decidable equality: a unit index `unit : ι` and
multiplicities `N a b c = N_{ab}^c`, satisfying the left and right unit laws
`N_{ua}^b = N_{au}^b = if a = b then 1 else 0`. -/
@[ext]
structure FusionRules (ι : Type u) [DecidableEq ι] where
  /-- The index of the tensor unit. -/
  unit : ι
  /-- The multiplicity `N_{ab}^c` of `S_c` in `S_a ⊗ S_b`. -/
  N : ι → ι → ι → ℕ
  /-- Left unit law: tensoring on the left with `unit` preserves each simple index with
  multiplicity one. -/
  N_unit_left : ∀ a b, N unit a b = if a = b then 1 else 0
  /-- Right unit law: tensoring on the right with `unit` preserves each simple index with
  multiplicity one. -/
  N_unit_right : ∀ a b, N a unit b = if a = b then 1 else 0

namespace FusionRules

variable {ι : Type u} [DecidableEq ι] (N : FusionRules ι)

@[simp]
theorem N_unit_left_self (a : ι) : N.N N.unit a a = 1 := by
  simp [N.N_unit_left]

@[simp]
theorem N_unit_left_of_ne {a b : ι} (h : a ≠ b) : N.N N.unit a b = 0 := by
  simp [N.N_unit_left, h]

@[simp]
theorem N_unit_right_self (a : ι) : N.N a N.unit a = 1 := by
  simp [N.N_unit_right]

@[simp]
theorem N_unit_right_of_ne {a b : ι} (h : a ≠ b) : N.N a N.unit b = 0 := by
  simp [N.N_unit_right, h]

/-- Row indices of `F^{abc}_d`: `Σ e, Fin N_{ab}^e × Fin N_{ec}^d`, indexing the left-associated
fusion basis `(φ^{ab→e}_i ▷ c) ≫ φ^{ec→d}_j` of `Hom((S_a ⊗ S_b) ⊗ S_c, S_d)`. -/
abbrev Left (a b c d : ι) : Type u :=
  Σ e : ι, Fin (N.N a b e) × Fin (N.N e c d)

/-- Column indices of `F^{abc}_d`: `Σ f, Fin N_{bc}^f × Fin N_{af}^d`, indexing the
right-associated fusion basis `(a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l` of
`Hom(S_a ⊗ (S_b ⊗ S_c), S_d)`. -/
abbrev Right (a b c d : ι) : Type u :=
  Σ f : ι, Fin (N.N b c f) × Fin (N.N a f d)

/-- The unique basis index in `Fin N_{au}^a`. -/
def unitRight (a : ι) : Fin (N.N a N.unit a) :=
  ⟨0, by simp⟩

/-- The unique basis index in `Fin N_{ua}^a`. -/
def unitLeft (a : ι) : Fin (N.N N.unit a a) :=
  ⟨0, by simp⟩

@[simp]
theorem val_unitRight (a : ι) : (N.unitRight a).val = 0 :=
  (rfl)

@[simp]
theorem val_unitLeft (a : ι) : (N.unitLeft a).val = 0 :=
  (rfl)

/-- An index in `Fin N_{ua}^b` forces `a = b`. -/
theorem eq_of_fin_unit_left {a b : ι} (i : Fin (N.N N.unit a b)) : a = b := by
  by_contra h
  exact Nat.not_lt_zero i.val (N.N_unit_left_of_ne h ▸ i.isLt)

/-- An index in `Fin N_{au}^b` forces `a = b`. -/
theorem eq_of_fin_unit_right {a b : ι} (i : Fin (N.N a N.unit b)) : a = b := by
  by_contra h
  exact Nat.not_lt_zero i.val (N.N_unit_right_of_ne h ▸ i.isLt)

instance instUniqueFinUnitLeft (a : ι) : Unique (Fin (N.N N.unit a a)) where
  default := N.unitLeft a
  uniq i := Fin.ext (by simpa using i.isLt)

instance instUniqueFinUnitRight (a : ι) : Unique (Fin (N.N a N.unit a)) where
  default := N.unitRight a
  uniq i := Fin.ext (by simpa using i.isLt)

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
    ∑ i, f i = 0 := by
  have : IsEmpty (Fin (N.N N.unit a b)) := ⟨fun i ↦ h (N.eq_of_fin_unit_left i)⟩
  exact Fintype.sum_empty f

theorem sum_fin_unit_right_of_ne {a b : ι} (h : a ≠ b) (f : Fin (N.N a N.unit b) → M) :
    ∑ i, f i = 0 := by
  have : IsEmpty (Fin (N.N a N.unit b)) := ⟨fun i ↦ h (N.eq_of_fin_unit_right i)⟩
  exact Fintype.sum_empty f

variable [Fintype ι]

/-- Summing over `(e, i)` with `i : Fin N_{ua}^e` collapses to `e = a` and `i = unitLeft a`. -/
theorem sum_fin_unit_left_fst (a : ι) (f : ∀ e : ι, Fin (N.N N.unit a e) → M) :
    ∑ e : ι, ∑ i : Fin (N.N N.unit a e), f e i = f a (N.unitLeft a) := by
  rw [Fintype.sum_eq_single a (fun e he ↦ N.sum_fin_unit_left_of_ne he.symm (f e)),
    N.sum_fin_unit_left_self]

/-- Summing over `(e, i)` with `i : Fin N_{ue}^b` collapses to `e = b` and `i = unitLeft b`. -/
theorem sum_fin_unit_left_snd (b : ι) (f : ∀ e : ι, Fin (N.N N.unit e b) → M) :
    ∑ e : ι, ∑ i : Fin (N.N N.unit e b), f e i = f b (N.unitLeft b) := by
  rw [Fintype.sum_eq_single b (fun e he ↦ N.sum_fin_unit_left_of_ne he (f e)),
    N.sum_fin_unit_left_self]

/-- Summing over `(e, i)` with `i : Fin N_{au}^e` collapses to `e = a` and `i = unitRight a`. -/
theorem sum_fin_unit_right_fst (a : ι) (f : ∀ e : ι, Fin (N.N a N.unit e) → M) :
    ∑ e : ι, ∑ i : Fin (N.N a N.unit e), f e i = f a (N.unitRight a) := by
  rw [Fintype.sum_eq_single a (fun e he ↦ N.sum_fin_unit_right_of_ne he.symm (f e)),
    N.sum_fin_unit_right_self]

/-- Summing over `(e, i)` with `i : Fin N_{eu}^b` collapses to `e = b` and `i = unitRight b`. -/
theorem sum_fin_unit_right_snd (b : ι) (f : ∀ e : ι, Fin (N.N e N.unit b) → M) :
    ∑ e : ι, ∑ i : Fin (N.N e N.unit b), f e i = f b (N.unitRight b) := by
  rw [Fintype.sum_eq_single b (fun e he ↦ N.sum_fin_unit_right_of_ne he (f e)),
    N.sum_fin_unit_right_self]

end UnitSums

/-! #### Unit specializations of `Left` and `Right` -/

/-- `Left a u c d` is canonically equivalent to `Fin N_{ac}^d` via
`j ↦ ⟨a, unitRight a, j⟩`. -/
def leftUnitMidEquiv (a c d : ι) : N.Left a N.unit c d ≃ Fin (N.N a c d) where
  toFun x := N.eq_of_fin_unit_right x.2.1 ▸ x.2.2
  invFun j := ⟨a, N.unitRight a, j⟩
  left_inv := by
    rintro ⟨e, i, j⟩
    obtain rfl : a = e := N.eq_of_fin_unit_right i
    simp [N.fin_unit_right_eq a i]
  right_inv _ := rfl

@[simp]
theorem leftUnitMidEquiv_symm_apply (a c d : ι) (j : Fin (N.N a c d)) :
    (N.leftUnitMidEquiv a c d).symm j = ⟨a, N.unitRight a, j⟩ :=
  (rfl)

@[simp]
theorem leftUnitMidEquiv_mk (a c d : ι) (j : Fin (N.N a c d)) :
    N.leftUnitMidEquiv a c d ⟨a, N.unitRight a, j⟩ = j :=
  (N.leftUnitMidEquiv a c d).apply_symm_apply j

/-- `Right a u c d` is canonically equivalent to `Fin N_{ac}^d` via
`l ↦ ⟨c, unitLeft c, l⟩`. -/
def rightUnitMidEquiv (a c d : ι) : N.Right a N.unit c d ≃ Fin (N.N a c d) where
  toFun y := N.eq_of_fin_unit_left y.2.1 ▸ y.2.2
  invFun l := ⟨c, N.unitLeft c, l⟩
  left_inv := by
    rintro ⟨f, k, l⟩
    obtain rfl : c = f := N.eq_of_fin_unit_left k
    simp [N.fin_unit_left_eq c k]
  right_inv _ := rfl

@[simp]
theorem rightUnitMidEquiv_symm_apply (a c d : ι) (l : Fin (N.N a c d)) :
    (N.rightUnitMidEquiv a c d).symm l = ⟨c, N.unitLeft c, l⟩ :=
  (rfl)

@[simp]
theorem rightUnitMidEquiv_mk (a c d : ι) (l : Fin (N.N a c d)) :
    N.rightUnitMidEquiv a c d ⟨c, N.unitLeft c, l⟩ = l :=
  (N.rightUnitMidEquiv a c d).apply_symm_apply l

/-- `Left u b c d` is canonically equivalent to `Fin N_{bc}^d` via
`j ↦ ⟨b, unitLeft b, j⟩`. -/
def leftUnitLeftEquiv (b c d : ι) : N.Left N.unit b c d ≃ Fin (N.N b c d) where
  toFun x := N.eq_of_fin_unit_left x.2.1 ▸ x.2.2
  invFun j := ⟨b, N.unitLeft b, j⟩
  left_inv := by
    rintro ⟨e, i, j⟩
    obtain rfl : b = e := N.eq_of_fin_unit_left i
    simp [N.fin_unit_left_eq b i]
  right_inv _ := rfl

@[simp]
theorem leftUnitLeftEquiv_symm_apply (b c d : ι) (j : Fin (N.N b c d)) :
    (N.leftUnitLeftEquiv b c d).symm j = ⟨b, N.unitLeft b, j⟩ :=
  (rfl)

@[simp]
theorem leftUnitLeftEquiv_mk (b c d : ι) (j : Fin (N.N b c d)) :
    N.leftUnitLeftEquiv b c d ⟨b, N.unitLeft b, j⟩ = j :=
  (N.leftUnitLeftEquiv b c d).apply_symm_apply j

/-- `Right u b c d` is canonically equivalent to `Fin N_{bc}^d` via
`k ↦ ⟨d, k, unitLeft d⟩`. -/
def rightUnitLeftEquiv (b c d : ι) : N.Right N.unit b c d ≃ Fin (N.N b c d) where
  toFun y := (N.eq_of_fin_unit_left y.2.2).symm ▸ y.2.1
  invFun k := ⟨d, k, N.unitLeft d⟩
  left_inv := by
    rintro ⟨f, k, l⟩
    obtain rfl : f = d := N.eq_of_fin_unit_left l
    simp [N.fin_unit_left_eq f l]
  right_inv _ := rfl

@[simp]
theorem rightUnitLeftEquiv_symm_apply (b c d : ι) (k : Fin (N.N b c d)) :
    (N.rightUnitLeftEquiv b c d).symm k = ⟨d, k, N.unitLeft d⟩ :=
  (rfl)

@[simp]
theorem rightUnitLeftEquiv_mk (b c d : ι) (k : Fin (N.N b c d)) :
    N.rightUnitLeftEquiv b c d ⟨d, k, N.unitLeft d⟩ = k :=
  (N.rightUnitLeftEquiv b c d).apply_symm_apply k

/-- `Left a b u d` is canonically equivalent to `Fin N_{ab}^d` via
`i ↦ ⟨d, i, unitRight d⟩`. -/
def leftUnitRightEquiv (a b d : ι) : N.Left a b N.unit d ≃ Fin (N.N a b d) where
  toFun x := (N.eq_of_fin_unit_right x.2.2).symm ▸ x.2.1
  invFun i := ⟨d, i, N.unitRight d⟩
  left_inv := by
    rintro ⟨e, i, j⟩
    obtain rfl : e = d := N.eq_of_fin_unit_right j
    simp [N.fin_unit_right_eq e j]
  right_inv _ := rfl

@[simp]
theorem leftUnitRightEquiv_symm_apply (a b d : ι) (i : Fin (N.N a b d)) :
    (N.leftUnitRightEquiv a b d).symm i = ⟨d, i, N.unitRight d⟩ :=
  (rfl)

@[simp]
theorem leftUnitRightEquiv_mk (a b d : ι) (i : Fin (N.N a b d)) :
    N.leftUnitRightEquiv a b d ⟨d, i, N.unitRight d⟩ = i :=
  (N.leftUnitRightEquiv a b d).apply_symm_apply i

/-- `Right a b u d` is canonically equivalent to `Fin N_{ab}^d` via
`l ↦ ⟨b, unitRight b, l⟩`. -/
def rightUnitRightEquiv (a b d : ι) : N.Right a b N.unit d ≃ Fin (N.N a b d) where
  toFun y := N.eq_of_fin_unit_right y.2.1 ▸ y.2.2
  invFun l := ⟨b, N.unitRight b, l⟩
  left_inv := by
    rintro ⟨f, k, l⟩
    obtain rfl : b = f := N.eq_of_fin_unit_right k
    simp [N.fin_unit_right_eq b k]
  right_inv _ := rfl

@[simp]
theorem rightUnitRightEquiv_symm_apply (a b d : ι) (l : Fin (N.N a b d)) :
    (N.rightUnitRightEquiv a b d).symm l = ⟨b, N.unitRight b, l⟩ :=
  (rfl)

@[simp]
theorem rightUnitRightEquiv_mk (a b d : ι) (l : Fin (N.N a b d)) :
    N.rightUnitRightEquiv a b d ⟨b, N.unitRight b, l⟩ = l :=
  (N.rightUnitRightEquiv a b d).apply_symm_apply l

end FusionRules

/-! ### F-symbols -/

/-- **F-symbols** over a commutative ring `R` for fusion rules `N` on a finite index type `ι`:
families of matrices `F^{abc}_d` with two-sided inverses `Finv^{abc}_d`, satisfying the pentagon
and middle-unit triangle identities.

Because rows (`FusionRules.Left`) and columns (`FusionRules.Right`) are distinct types, the
two-sided inverse `Finv` is carried as a field, but it is uniquely determined by `F`
(`TauCeti.FSymbols.ext`). -/
structure FSymbols (R : Type v) [CommRing R] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (N : FusionRules ι) where
  /-- `F^{abc}_d`, with rows `N.Left a b c d` and columns `N.Right a b c d`. -/
  F : ∀ a b c d : ι, Matrix (N.Left a b c d) (N.Right a b c d) R
  /-- `Finv^{abc}_d`, the two-sided inverse of `F^{abc}_d`, with rows `N.Right a b c d` and
  columns `N.Left a b c d`. -/
  Finv : ∀ a b c d : ι, Matrix (N.Right a b c d) (N.Left a b c d) R
  /-- Right inverse law `F^{abc}_d * Finv^{abc}_d = 1`. -/
  F_mul_Finv : ∀ a b c d, F a b c d * Finv a b c d = 1
  /-- Left inverse law `Finv^{abc}_d * F^{abc}_d = 1`. -/
  Finv_mul_F : ∀ a b c d, Finv a b c d * F a b c d = 1
  /-- The pentagon identity equating the matrix coordinates of `α_{AB,C,D} ≫ α_{A,B,CD}` and
  `(α_{A,B,C} ▷ D) ≫ α_{A,BC,D} ≫ (A ◁ α_{B,C,D})`. -/
  pentagon : ∀ (A B C D E p q r s : ι) (i₁ : Fin (N.N A B p)) (i₂ : Fin (N.N p C q))
    (i₃ : Fin (N.N q D E)) (k : Fin (N.N C D r)) (m : Fin (N.N B r s)) (n : Fin (N.N A s E)),
    ∑ l : Fin (N.N p r E),
        F p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * F A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      ∑ t : ι, ∑ x : Fin (N.N B C t), ∑ y : Fin (N.N A t q), ∑ z : Fin (N.N t D s),
        F A B C q ⟨p, i₁, i₂⟩ ⟨t, x, y⟩ * F A t D E ⟨q, y, i₃⟩ ⟨s, z, n⟩ *
          F B C D s ⟨t, x, z⟩ ⟨r, k, m⟩
  /-- The middle-unit triangle identity `F^{auc}_d[(a,0,j),(c,0,l)] = δ_{jl}`. -/
  triangle : ∀ (a c d : ι) (j l : Fin (N.N a c d)),
    F a N.unit c d ⟨a, N.unitRight a, j⟩ ⟨c, N.unitLeft c, l⟩ = if j = l then 1 else 0

namespace FSymbols

variable {R : Type v} [CommRing R] {ι : Type u} [Fintype ι] [DecidableEq ι] {N : FusionRules ι}

attribute [simp] F_mul_Finv Finv_mul_F

/-- Two `FSymbols` with equal `F`-matrices are equal, since two-sided matrix inverses are unique. -/
@[ext]
theorem ext {P Q : FSymbols R N}
    (h : ∀ a b c d x y, P.F a b c d x y = Q.F a b c d x y) : P = Q := by
  have hF : P.F = Q.F := by
    funext a b c d
    exact Matrix.ext (h a b c d)
  have hFinv : P.Finv = Q.Finv := by
    funext a b c d
    have hF' : P.F a b c d = Q.F a b c d := Matrix.ext (h a b c d)
    calc P.Finv a b c d
      _ = P.Finv a b c d * (1 : Matrix _ _ R) := (Matrix.mul_one _).symm
      _ = P.Finv a b c d * (Q.F a b c d * Q.Finv a b c d) := by rw [Q.F_mul_Finv]
      _ = (P.Finv a b c d * P.F a b c d) * Q.Finv a b c d := by rw [← hF', Matrix.mul_assoc]
      _ = (1 : Matrix _ _ R) * Q.Finv a b c d := by rw [P.Finv_mul_F]
      _ = Q.Finv a b c d := Matrix.one_mul _
  cases P
  cases Q
  simp only [mk.injEq]
  exact ⟨hF, hFinv⟩

theorem F_injective : Function.Injective (FSymbols.F (R := R) (N := N)) :=
  fun _ _ h ↦ ext fun a b c d x y ↦ congrArg (fun M ↦ M a b c d x y) h

/-- Two `FSymbols` with equal `Finv`-matrices are also equal. -/
theorem ext_of_Finv {P Q : FSymbols R N}
    (h : ∀ a b c d y x, P.Finv a b c d y x = Q.Finv a b c d y x) : P = Q := by
  ext a b c d x y
  have hFinv : P.Finv a b c d = Q.Finv a b c d := Matrix.ext (h a b c d)
  have hF : P.F a b c d = Q.F a b c d := by
    calc P.F a b c d
      _ = P.F a b c d * (1 : Matrix _ _ R) := (Matrix.mul_one _).symm
      _ = P.F a b c d * (Q.Finv a b c d * Q.F a b c d) := by rw [Q.Finv_mul_F]
      _ = (P.F a b c d * P.Finv a b c d) * Q.F a b c d := by rw [← hFinv, Matrix.mul_assoc]
      _ = (1 : Matrix _ _ R) * Q.F a b c d := by rw [P.F_mul_Finv]
      _ = Q.F a b c d := Matrix.one_mul _
  exact congr_fun₂ hF x y

theorem Finv_injective : Function.Injective (FSymbols.Finv (R := R) (N := N)) :=
  fun _ _ h ↦ ext_of_Finv fun a b c d y x ↦ congrArg (fun M ↦ M a b c d y x) h

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

/-! #### Derived outer unit triangles -/

/-- Left-unit triangle: the pentagon and middle-unit triangle force `F^{ubc}_d = 1` on the
unit-indexed basis blocks (Etingof–Gelaki–Nikshych–Ostrik, Proposition 2.2.4). -/
theorem F_unit_left (P : FSymbols R N) (b c d : ι) (j k : Fin (N.N b c d)) :
    P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, k, N.unitLeft d⟩ =
      if j = k then 1 else 0 := by
  have hmat : ∀ m : Fin (N.N b c d),
      P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, k, N.unitLeft d⟩ =
        ∑ z : Fin (N.N b c d),
          P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, z, N.unitLeft d⟩ *
            P.F N.unit b c d ⟨b, N.unitLeft b, z⟩ ⟨d, k, N.unitLeft d⟩ := by
    intro m
    have hpm := P.pentagon N.unit N.unit b c d N.unit b d d
      (N.unitRight N.unit) (N.unitLeft b) m k (N.unitLeft d) (N.unitLeft d)
    rw [N.sum_fin_unit_left_self, P.triangle_self, mul_one,
      N.sum_fin_unit_left_fst b, N.sum_fin_unit_left_self] at hpm
    simp_rw [P.triangle_self, one_mul] at hpm
    exact hpm
  have hinv_row : ∀ j' k' : Fin (N.N b c d),
      ∑ m : Fin (N.N b c d),
        P.Finv N.unit b c d ⟨d, j', N.unitLeft d⟩ ⟨b, N.unitLeft b, m⟩ *
          P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, k', N.unitLeft d⟩ =
        if j' = k' then 1 else 0 := by
    intro j' k'
    have h := P.sum_Finv_mul_F N.unit b c d ((N.rightUnitLeftEquiv b c d).symm j')
      ((N.rightUnitLeftEquiv b c d).symm k')
    rw [← (N.leftUnitLeftEquiv b c d).symm.sum_comp] at h
    simpa [(N.rightUnitLeftEquiv b c d).symm.injective.eq_iff] using h
  have hmul :
      ∑ m : Fin (N.N b c d),
          P.Finv N.unit b c d ⟨d, j, N.unitLeft d⟩ ⟨b, N.unitLeft b, m⟩ *
            P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, k, N.unitLeft d⟩ =
        P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, k, N.unitLeft d⟩ := by
    calc ∑ m : Fin (N.N b c d),
          P.Finv N.unit b c d ⟨d, j, N.unitLeft d⟩ ⟨b, N.unitLeft b, m⟩ *
            P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, k, N.unitLeft d⟩
      _ = ∑ m : Fin (N.N b c d),
            P.Finv N.unit b c d ⟨d, j, N.unitLeft d⟩ ⟨b, N.unitLeft b, m⟩ *
              ∑ z : Fin (N.N b c d),
                P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, z, N.unitLeft d⟩ *
                  P.F N.unit b c d ⟨b, N.unitLeft b, z⟩ ⟨d, k, N.unitLeft d⟩ := by
        refine Finset.sum_congr rfl fun m _ ↦ by rw [← hmat m]
      _ = ∑ z : Fin (N.N b c d),
            (∑ m : Fin (N.N b c d),
              P.Finv N.unit b c d ⟨d, j, N.unitLeft d⟩ ⟨b, N.unitLeft b, m⟩ *
                P.F N.unit b c d ⟨b, N.unitLeft b, m⟩ ⟨d, z, N.unitLeft d⟩) *
              P.F N.unit b c d ⟨b, N.unitLeft b, z⟩ ⟨d, k, N.unitLeft d⟩ := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ = ∑ z : Fin (N.N b c d),
            (if j = z then (1 : R) else 0) *
              P.F N.unit b c d ⟨b, N.unitLeft b, z⟩ ⟨d, k, N.unitLeft d⟩ := by
        refine Finset.sum_congr rfl fun z _ ↦ by rw [hinv_row j z]
      _ = P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, k, N.unitLeft d⟩ := by
        simp
  exact hmul.symm.trans (hinv_row j k)

@[simp]
theorem F_unit_left_self (P : FSymbols R N) (b c d : ι) (j : Fin (N.N b c d)) :
    P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, j, N.unitLeft d⟩ = 1 := by
  simp [P.F_unit_left]

theorem F_unit_left_of_ne (P : FSymbols R N) {b c d : ι} {j k : Fin (N.N b c d)} (h : j ≠ k) :
    P.F N.unit b c d ⟨b, N.unitLeft b, j⟩ ⟨d, k, N.unitLeft d⟩ = 0 := by
  simp [P.F_unit_left, h]

/-- Right-unit triangle: the pentagon and middle-unit triangle force `F^{abu}_d = 1` on the
unit-indexed basis blocks (Etingof–Gelaki–Nikshych–Ostrik, Proposition 2.2.4). -/
theorem F_unit_right (P : FSymbols R N) (a b d : ι) (i l : Fin (N.N a b d)) :
    P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, l⟩ =
      if i = l then 1 else 0 := by
  have hmat : ∀ m : Fin (N.N a b d),
      P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, m⟩ =
        ∑ y : Fin (N.N a b d),
          P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, y⟩ *
            P.F a b N.unit d ⟨d, y, N.unitRight d⟩ ⟨b, N.unitRight b, m⟩ := by
    intro m
    have hpm := P.pentagon a b N.unit N.unit d d d N.unit b
      i (N.unitRight d) (N.unitRight d) (N.unitLeft N.unit) (N.unitRight b) m
    rw [N.sum_fin_unit_right_self, P.triangle_self, one_mul,
      N.sum_fin_unit_right_fst b] at hpm
    simp_rw [N.sum_fin_unit_right_self, P.triangle_self, mul_one] at hpm
    exact hpm
  have hinv_row : ∀ i' l' : Fin (N.N a b d),
      ∑ m : Fin (N.N a b d),
        P.F a b N.unit d ⟨d, i', N.unitRight d⟩ ⟨b, N.unitRight b, m⟩ *
          P.Finv a b N.unit d ⟨b, N.unitRight b, m⟩ ⟨d, l', N.unitRight d⟩ =
        if i' = l' then 1 else 0 := by
    intro i' l'
    have h := P.sum_F_mul_Finv a b N.unit d ((N.leftUnitRightEquiv a b d).symm i')
      ((N.leftUnitRightEquiv a b d).symm l')
    rw [← (N.rightUnitRightEquiv a b d).symm.sum_comp] at h
    simpa [(N.leftUnitRightEquiv a b d).symm.injective.eq_iff] using h
  have hmul :
      ∑ m : Fin (N.N a b d),
          P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, m⟩ *
            P.Finv a b N.unit d ⟨b, N.unitRight b, m⟩ ⟨d, l, N.unitRight d⟩ =
        P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, l⟩ := by
    calc ∑ m : Fin (N.N a b d),
          P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, m⟩ *
            P.Finv a b N.unit d ⟨b, N.unitRight b, m⟩ ⟨d, l, N.unitRight d⟩
      _ = ∑ m : Fin (N.N a b d),
            (∑ y : Fin (N.N a b d),
              P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, y⟩ *
                P.F a b N.unit d ⟨d, y, N.unitRight d⟩ ⟨b, N.unitRight b, m⟩) *
              P.Finv a b N.unit d ⟨b, N.unitRight b, m⟩ ⟨d, l, N.unitRight d⟩ := by
        refine Finset.sum_congr rfl fun m _ ↦ by rw [← hmat m]
      _ = ∑ y : Fin (N.N a b d),
            P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, y⟩ *
               (∑ m : Fin (N.N a b d),
                P.F a b N.unit d ⟨d, y, N.unitRight d⟩ ⟨b, N.unitRight b, m⟩ *
                  P.Finv a b N.unit d ⟨b, N.unitRight b, m⟩ ⟨d, l, N.unitRight d⟩) := by
        simp_rw [Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ = ∑ y : Fin (N.N a b d),
            P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, y⟩ *
              (if y = l then (1 : R) else 0) := by
        refine Finset.sum_congr rfl fun y _ ↦ by rw [hinv_row y l]
      _ = P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, l⟩ := by
        simp
  exact hmul.symm.trans (hinv_row i l)

@[simp]
theorem F_unit_right_self (P : FSymbols R N) (a b d : ι) (i : Fin (N.N a b d)) :
    P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, i⟩ = 1 := by
  simp [P.F_unit_right]

theorem F_unit_right_of_ne (P : FSymbols R N) {a b d : ι} {i l : Fin (N.N a b d)} (h : i ≠ l) :
    P.F a b N.unit d ⟨d, i, N.unitRight d⟩ ⟨b, N.unitRight b, l⟩ = 0 := by
  simp [P.F_unit_right, h]

/-- Inverse middle-unit triangle: `Finv^{auc}_d[(c,0,l),(a,0,j)] = δ_{lj}`. -/
theorem Finv_triangle (P : FSymbols R N) (a c d : ι) (l j : Fin (N.N a c d)) :
    P.Finv a N.unit c d ⟨c, N.unitLeft c, l⟩ ⟨a, N.unitRight a, j⟩ =
      if l = j then 1 else 0 := by
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

/-- Inverse left-unit triangle: `Finv^{ubc}_d[(d,k,0),(b,0,j)] = δ_{kj}`. -/
theorem Finv_unit_left (P : FSymbols R N) (b c d : ι) (k j : Fin (N.N b c d)) :
    P.Finv N.unit b c d ⟨d, k, N.unitLeft d⟩ ⟨b, N.unitLeft b, j⟩ =
      if k = j then 1 else 0 := by
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

/-- Inverse right-unit triangle: `Finv^{abu}_d[(b,0,l),(d,i,0)] = δ_{li}`. -/
theorem Finv_unit_right (P : FSymbols R N) (a b d : ι) (l i : Fin (N.N a b d)) :
    P.Finv a b N.unit d ⟨b, N.unitRight b, l⟩ ⟨d, i, N.unitRight d⟩ =
      if l = i then 1 else 0 := by
  have h := P.sum_Finv_mul_F a b N.unit d ⟨b, N.unitRight b, l⟩ ⟨b, N.unitRight b, i⟩
  rw [← (N.leftUnitRightEquiv a b d).symm.sum_comp] at h
  simpa [P.F_unit_right] using h

@[simp]
theorem Finv_unit_right_self (P : FSymbols R N) (a b d : ι) (i : Fin (N.N a b d)) :
    P.Finv a b N.unit d ⟨b, N.unitRight b, i⟩ ⟨d, i, N.unitRight d⟩ = 1 := by
  simp [P.Finv_unit_right]

theorem Finv_unit_right_of_ne (P : FSymbols R N) {a b d : ι} {l i : Fin (N.N a b d)}
    (h : l ≠ i) :
    P.Finv a b N.unit d ⟨b, N.unitRight b, l⟩ ⟨d, i, N.unitRight d⟩ = 0 := by
  simp [P.Finv_unit_right, h]

/-- Over a subsingleton ring (such as the zero ring), every `FusionRules` carries a unique
`FSymbols`. -/
instance instUniqueOfSubsingleton [Subsingleton R] : Unique (FSymbols R N) where
  default :=
    { F := fun _ _ _ _ ↦ 0
      Finv := fun _ _ _ _ ↦ 0
      F_mul_Finv := fun _ _ _ _ ↦ Subsingleton.elim _ _
      Finv_mul_F := fun _ _ _ _ ↦ Subsingleton.elim _ _
      pentagon := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _
      triangle := fun _ _ _ _ _ ↦ Subsingleton.elim _ _ }
  uniq _ := ext fun _ _ _ _ _ _ ↦ Subsingleton.elim _ _

/-! #### Rank consequences of invertibility -/

section Nontrivial

variable [Nontrivial R]

/-- Over a nontrivial commutative ring, the invertibility of `F^{abc}_d` forces its row and column
index types to have the same cardinality. -/
theorem card_left_eq_card_right (P : FSymbols R N) (a b c d : ι) :
    Fintype.card (N.Left a b c d) = Fintype.card (N.Right a b c d) :=
  Matrix.square_of_invertible (P.F a b c d) (P.Finv a b c d) (P.F_mul_Finv a b c d)
    (P.Finv_mul_F a b c d)

/-- Over a nontrivial commutative ring, `N.Left a b c d` and `N.Right a b c d` are equivalent. -/
theorem nonempty_leftEquivRight (P : FSymbols R N) (a b c d : ι) :
    Nonempty (N.Left a b c d ≃ N.Right a b c d) :=
  ⟨Fintype.equivOfCardEq (P.card_left_eq_card_right a b c d)⟩

/-- Over a nontrivial commutative ring, the existence of F-symbols forces the fusion multiplicities
to be associative: `∑ e, N_{ab}^e N_{ec}^d = ∑ f, N_{bc}^f N_{af}^d`. -/
theorem N_assoc (P : FSymbols R N) (a b c d : ι) :
    ∑ e : ι, N.N a b e * N.N e c d = ∑ f : ι, N.N b c f * N.N a f d := by
  simpa [FusionRules.Left, FusionRules.Right] using P.card_left_eq_card_right a b c d

end Nontrivial

end FSymbols

/-! ### R-symbols -/

/-- **R-symbols** for F-symbols `P` over a commutative ring `K`: families of matrices
`R^{ab}_c : Matrix (Fin N_{ab}^c) (Fin N_{ba}^c) K` with two-sided inverses `Rinv^{ab}_c`,
satisfying the forward and reverse hexagon identities. -/
structure RSymbols {K : Type v} [CommRing K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {N : FusionRules ι} (P : FSymbols K N) where
  /-- `R^{ab}_c`, expressing the fusion basis of `Hom(S_a ⊗ S_b, S_c)` in the braided basis. -/
  R : ∀ a b c : ι, Matrix (Fin (N.N a b c)) (Fin (N.N b a c)) K
  /-- The two-sided inverse of `R^{ab}_c`. -/
  Rinv : ∀ a b c : ι, Matrix (Fin (N.N b a c)) (Fin (N.N a b c)) K
  /-- Right inverse law `R^{ab}_c * Rinv^{ab}_c = 1`. -/
  R_mul_Rinv : ∀ a b c, R a b c * Rinv a b c = 1
  /-- Left inverse law `Rinv^{ab}_c * R^{ab}_c = 1`. -/
  Rinv_mul_R : ∀ a b c, Rinv a b c * R a b c = 1
  /-- Forward hexagon identity, corresponding to `BraidedCategory.hexagon_forward`. -/
  hexagon_forward : ∀ (a b c d e g : ι) (i : Fin (N.N a b e)) (j : Fin (N.N e c d))
    (n : Fin (N.N c a g)) (o : Fin (N.N b g d)),
    ∑ f : ι, ∑ k : Fin (N.N b c f), ∑ l : Fin (N.N a f d), ∑ m : Fin (N.N f a d),
        P.F a b c d ⟨e, i, j⟩ ⟨f, k, l⟩ * R a f d l m *
          P.F b c a d ⟨f, k, m⟩ ⟨g, n, o⟩ =
      ∑ p : Fin (N.N b a e), ∑ q : Fin (N.N a c g),
        R a b e i p * P.F b a c d ⟨e, p, j⟩ ⟨g, q, o⟩ * R a c g q n
  /-- Reverse hexagon identity, corresponding to `BraidedCategory.hexagon_reverse`. -/
  hexagon_reverse : ∀ (a b c d f g : ι) (k : Fin (N.N b c f)) (l : Fin (N.N a f d))
    (n : Fin (N.N c a g)) (o : Fin (N.N g b d)),
    ∑ e : ι, ∑ i : Fin (N.N a b e), ∑ j : Fin (N.N e c d), ∑ m : Fin (N.N c e d),
        P.Finv a b c d ⟨f, k, l⟩ ⟨e, i, j⟩ * R e c d j m *
          P.Finv c a b d ⟨e, i, m⟩ ⟨g, n, o⟩ =
      ∑ p : Fin (N.N c b f), ∑ q : Fin (N.N a c g),
        R b c f k p * P.Finv a c b d ⟨f, p, l⟩ ⟨g, q, o⟩ * R a c g q n

namespace RSymbols

variable {K : Type v} [CommRing K] {ι : Type u} [Fintype ι] [DecidableEq ι]
  {N : FusionRules ι} {P : FSymbols K N}

attribute [simp] R_mul_Rinv Rinv_mul_R

/-- Two `RSymbols` for `P` with equal `R`-matrices are equal, since two-sided matrix inverses are
unique. -/
@[ext]
theorem ext {Q₁ Q₂ : RSymbols P}
    (h : ∀ a b c i j, Q₁.R a b c i j = Q₂.R a b c i j) : Q₁ = Q₂ := by
  have hR : Q₁.R = Q₂.R := by
    funext a b c
    exact Matrix.ext (h a b c)
  have hRinv : Q₁.Rinv = Q₂.Rinv := by
    funext a b c
    have hR' : Q₁.R a b c = Q₂.R a b c := Matrix.ext (h a b c)
    calc Q₁.Rinv a b c
      _ = Q₁.Rinv a b c * (1 : Matrix _ _ K) := (Matrix.mul_one _).symm
      _ = Q₁.Rinv a b c * (Q₂.R a b c * Q₂.Rinv a b c) := by rw [Q₂.R_mul_Rinv]
      _ = (Q₁.Rinv a b c * Q₁.R a b c) * Q₂.Rinv a b c := by rw [← hR', Matrix.mul_assoc]
      _ = (1 : Matrix _ _ K) * Q₂.Rinv a b c := by rw [Q₁.Rinv_mul_R]
      _ = Q₂.Rinv a b c := Matrix.one_mul _
  cases Q₁
  cases Q₂
  simp only [mk.injEq]
  exact ⟨hR, hRinv⟩

theorem R_injective : Function.Injective (RSymbols.R (P := P)) :=
  fun _ _ h ↦ ext fun a b c i j ↦ congrArg (fun M ↦ M a b c i j) h

/-- Two `RSymbols` for `P` with equal `Rinv`-matrices are also equal. -/
theorem ext_of_Rinv {Q₁ Q₂ : RSymbols P}
    (h : ∀ a b c j i, Q₁.Rinv a b c j i = Q₂.Rinv a b c j i) : Q₁ = Q₂ := by
  ext a b c i j
  have hRinv : Q₁.Rinv a b c = Q₂.Rinv a b c := Matrix.ext (h a b c)
  have hR : Q₁.R a b c = Q₂.R a b c := by
    calc Q₁.R a b c
      _ = Q₁.R a b c * (1 : Matrix _ _ K) := (Matrix.mul_one _).symm
      _ = Q₁.R a b c * (Q₂.Rinv a b c * Q₂.R a b c) := by rw [Q₂.Rinv_mul_R]
      _ = (Q₁.R a b c * Q₁.Rinv a b c) * Q₂.R a b c := by rw [← hRinv, Matrix.mul_assoc]
      _ = (1 : Matrix _ _ K) * Q₂.R a b c := by rw [Q₁.R_mul_Rinv]
      _ = Q₂.R a b c := Matrix.one_mul _
  exact congr_fun₂ hR i j

theorem Rinv_injective : Function.Injective (RSymbols.Rinv (P := P)) :=
  fun _ _ h ↦ ext_of_Rinv fun a b c j i ↦ congrArg (fun M ↦ M a b c j i) h

/-- Entrywise form of `R * Rinv = 1`. -/
theorem sum_R_mul_Rinv (Q : RSymbols P) (a b c : ι) (i i' : Fin (N.N a b c)) :
    ∑ j : Fin (N.N b a c), Q.R a b c i j * Q.Rinv a b c j i' = if i = i' then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun₂ (Q.R_mul_Rinv a b c) i i'

/-- Entrywise form of `Rinv * R = 1`. -/
theorem sum_Rinv_mul_R (Q : RSymbols P) (a b c : ι) (j j' : Fin (N.N b a c)) :
    ∑ i : Fin (N.N a b c), Q.Rinv a b c j i * Q.R a b c i j' = if j = j' then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun₂ (Q.Rinv_mul_R a b c) j j'

/-- Transport `RSymbols` along an equality of the underlying `FSymbols`. -/
def cast {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) : RSymbols P₂ :=
  h ▸ Q

@[simp]
theorem cast_R {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) :
    (Q.cast h).R = Q.R := by
  cases h
  rfl

@[simp]
theorem cast_Rinv {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) :
    (Q.cast h).Rinv = Q.Rinv := by
  cases h
  rfl

@[simp]
theorem cast_R_apply {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁)
    (a b c : ι) (i : Fin (N.N a b c)) (j : Fin (N.N b a c)) :
    (Q.cast h).R a b c i j = Q.R a b c i j := by
  cases h
  rfl

@[simp]
theorem cast_Rinv_apply {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁)
    (a b c : ι) (j : Fin (N.N b a c)) (i : Fin (N.N a b c)) :
    (Q.cast h).Rinv a b c j i = Q.Rinv a b c j i := by
  cases h
  rfl

@[simp]
theorem cast_rfl (Q : RSymbols P) : Q.cast rfl = Q :=
  (rfl)

@[simp]
theorem cast_cast {P₁ P₂ P₃ : FSymbols K N} (h₁ : P₁ = P₂) (h₂ : P₂ = P₃)
    (Q : RSymbols P₁) :
    (Q.cast h₁).cast h₂ = Q.cast (h₁.trans h₂) := by
  cases h₁
  cases h₂
  rfl

/-! #### Derived unit braiding laws -/

/-- Right-unit braiding law: the forward hexagon and unit triangles force `R^{au}_a = 1`. -/
@[simp]
theorem R_unit_right (Q : RSymbols P) (a : ι) :
    Q.R a N.unit a (N.unitRight a) (N.unitLeft a) = 1 := by
  have hhex := Q.hexagon_forward a N.unit N.unit a a a
    (N.unitRight a) (N.unitRight a) (N.unitLeft a) (N.unitLeft a)
  rw [N.sum_fin_unit_left_fst N.unit] at hhex
  simp only [FusionRules.sum_fin_unit_right_self, FusionRules.sum_fin_unit_left_self,
    P.triangle_self, P.F_unit_left_self, one_mul, mul_one] at hhex
  have hinv :
      Q.R a N.unit a (N.unitRight a) (N.unitLeft a) *
        Q.Rinv a N.unit a (N.unitLeft a) (N.unitRight a) = 1 := by
    simpa using Q.sum_R_mul_Rinv a N.unit a (N.unitRight a) (N.unitRight a)
  set r := Q.R a N.unit a (N.unitRight a) (N.unitLeft a)
  set rinv := Q.Rinv a N.unit a (N.unitLeft a) (N.unitRight a)
  calc r
    _ = r * 1 := (mul_one r).symm
    _ = r * (r * rinv) := by rw [hinv]
    _ = (r * r) * rinv := (mul_assoc r r rinv).symm
    _ = r * rinv := by rw [← hhex]
    _ = 1 := hinv

/-- Inverse right-unit braiding law: `Rinv^{au}_a = 1`. -/
@[simp]
theorem Rinv_unit_right (Q : RSymbols P) (a : ι) :
    Q.Rinv a N.unit a (N.unitLeft a) (N.unitRight a) = 1 := by
  have hinv := Q.sum_R_mul_Rinv a N.unit a (N.unitRight a) (N.unitRight a)
  simpa using hinv

/-- Left-unit braiding law: the reverse hexagon and inverse unit triangles force `R^{ua}_a = 1`. -/
@[simp]
theorem R_unit_left (Q : RSymbols P) (a : ι) :
    Q.R N.unit a a (N.unitLeft a) (N.unitRight a) = 1 := by
  have hhex := Q.hexagon_reverse N.unit N.unit a a a a
    (N.unitLeft a) (N.unitLeft a) (N.unitRight a) (N.unitRight a)
  rw [N.sum_fin_unit_left_fst N.unit] at hhex
  simp only [FusionRules.sum_fin_unit_left_self, FusionRules.sum_fin_unit_right_self,
    P.Finv_unit_left_self, P.Finv_triangle_self, one_mul, mul_one] at hhex
  have hinv :
      Q.R N.unit a a (N.unitLeft a) (N.unitRight a) *
        Q.Rinv N.unit a a (N.unitRight a) (N.unitLeft a) = 1 := by
    simpa using Q.sum_R_mul_Rinv N.unit a a (N.unitLeft a) (N.unitLeft a)
  set r := Q.R N.unit a a (N.unitLeft a) (N.unitRight a)
  set rinv := Q.Rinv N.unit a a (N.unitRight a) (N.unitLeft a)
  calc r
    _ = r * 1 := (mul_one r).symm
    _ = r * (r * rinv) := by rw [hinv]
    _ = (r * r) * rinv := (mul_assoc r r rinv).symm
    _ = r * rinv := by rw [← hhex]
    _ = 1 := hinv

/-- Inverse left-unit braiding law: `Rinv^{ua}_a = 1`. -/
@[simp]
theorem Rinv_unit_left (Q : RSymbols P) (a : ι) :
    Q.Rinv N.unit a a (N.unitRight a) (N.unitLeft a) = 1 := by
  have hinv := Q.sum_R_mul_Rinv N.unit a a (N.unitLeft a) (N.unitLeft a)
  simpa using hinv

/-- Over a subsingleton ring, every `FSymbols` carries a unique `RSymbols`. -/
instance instUniqueOfSubsingleton [Subsingleton K] : Unique (RSymbols P) where
  default :=
    { R := fun _ _ _ ↦ 0
      Rinv := fun _ _ _ ↦ 0
      R_mul_Rinv := fun _ _ _ ↦ Subsingleton.elim _ _
      Rinv_mul_R := fun _ _ _ ↦ Subsingleton.elim _ _
      hexagon_forward := fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _
      hexagon_reverse := fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _ }
  uniq _ := ext fun _ _ _ _ _ ↦ Subsingleton.elim _ _

/-- Over a nontrivial commutative ring, the existence of R-symbols forces the fusion multiplicities
to be commutative: `N_{ab}^c = N_{ba}^c`. -/
theorem N_comm [Nontrivial K] (Q : RSymbols P) (a b c : ι) : N.N a b c = N.N b a c := by
  simpa using Matrix.square_of_invertible (Q.R a b c) (Q.Rinv a b c) (Q.R_mul_Rinv a b c)
    (Q.Rinv_mul_R a b c)

end RSymbols

end TauCeti
