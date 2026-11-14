/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Binary symplectic planes, Gauss sums, and the Arf invariant over `ZMod 2`

Over a commutative ring `R` of characteristic two, the polarization `polar q` of a quadratic form
`q : QuadraticForm R V` is alternating (`QuadraticMap.isAlt_polarBilin`), so a quadratic form
whose polar bilinear form is nondegenerate is a quadratic refinement of a symplectic pairing rather
than the quadratic form of a symmetric bilinear form.

When `V` has a symplectic basis `b : Module.Basis (ι ⊕ ι) R V` for `q.polarBilin` (meaning
`toMatrix b q.polarBilin = Matrix.J ι R`), `V` decomposes as an orthogonal sum of two-dimensional
planes `symplecticPlane R a b` (`x ↦ a x₀² + x₀ x₁ + b x₁²`), one for each index `i : ι` with
coefficients `a = q (b (inl i))` and `b = q (b (inr i))`.

Specializing to `R = ZMod 2`, the integer Gauss sum
`q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (q v).val` is manifestly basis-independent and multiplicative
under orthogonal sums. On `symplecticPlane (ZMod 2) a b` it evaluates to `(-1) ^ (a * b).val * 2`,
so on any symplectic basis `b` of `V` it equals
`(-1) ^ (∑ i, q (b (inl i)) * q (b (inr i))).val * 2 ^ card ι`. Comparing two symplectic bases
through `q.gaussSum` shows without matrix calculations that the sum
`∑ i, q (b (inl i)) * q (b (inr i)) ∈ ZMod 2` is independent of the choice of symplectic basis.

This common value is the *Arf invariant* `QuadraticMap.arf q : ZMod 2`, defined as a total function
returning `0` when `V` is infinite-dimensional or `q.polarBilin` is degenerate.

## Main definitions

* `TauCeti.symplecticPlane R a b`: the binary quadratic form `x ↦ a x₀² + x₀ x₁ + b x₁²` on
  `Fin 2 → R`.
* `TauCeti.symplecticPlaneBasis R`: the standard symplectic basis of `Fin 2 → R` indexed by
  `Fin 1 ⊕ Fin 1`.
* `QuadraticMap.isometryEquivPiSymplecticPlane`: explicit isometry from `q` to the orthogonal sum
  of binary symplectic planes determined by a symplectic basis of `q.polarBilin`.
* `QuadraticMap.gaussSum`: the integer Gauss sum `∑ v : V, (-1 : ℤ) ^ (q v).val` of a quadratic
  form over `ZMod 2` on a finite space.
* `QuadraticMap.arf`: the Arf invariant in `ZMod 2` of a quadratic form over `ZMod 2`.

## Main results

* `QuadraticMap.toMatrix_polarBilin_eq_J_iff`: in characteristic two, `toMatrix b q.polarBilin`
  equals `Matrix.J ι R` if and only if each half of `b` is polar-isotropic and the cross pairings
  are Kronecker deltas.
* `QuadraticMap.gaussSum_eq_card_mul_gaussSum_lift` and
  `QuadraticMap.gaussSum_eq_zero_of_exists_mem_ker_polarBilin`: radical dichotomy for Gauss sums
  of possibly degenerate forms.
* `QuadraticMap.sum_mul_eq_of_toMatrix_eq_J`: basis-independence of
  `∑ i, q (b (inl i)) * q (b (inr i))` across symplectic bases over `ZMod 2`.
* `QuadraticMap.arf_eq_sum_of_toMatrix_eq_J` and `QuadraticMap.arf_eq_sum_of_polar_eq`: formula for
  `q.arf` on any symplectic basis.
* `QuadraticMap.IsometryEquiv.arf_eq` and `QuadraticMap.Equivalent.arf_eq`: isometry invariance of
  the Arf invariant.
* `QuadraticMap.arf_prod`, `QuadraticMap.arf_pi`, and
  `QuadraticMap.arf_eq_arf_restrict_add_arf_restrict_orthogonal`: additivity under orthogonal sums
  and orthogonal decompositions.
* `QuadraticMap.gaussSum_eq`: the Gauss sum identity
  `q.gaussSum = (-1) ^ q.arf.val * 2 ^ (finrank (ZMod 2) V / 2)`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. **183** (1941), 148--167.
* M. F. Atiyah, *Riemann surfaces and spin structures*, Ann. Sci. École Norm. Sup. (4) **4**
  (1971), 47--62.
* A. Pyronneau, *Arf invariant* (2024), §2.1, Lemmas 2.11--2.13.
-/

public section

open scoped CharTwo

namespace TauCeti

section SymplecticPlane

/-- The binary quadratic form `x ↦ a * (x 0 * x 0) + x 0 * x 1 + b * (x 1 * x 1)` on `Fin 2 → R`
whose polar form in characteristic two is the standard alternating pairing on the plane. -/
def symplecticPlane (R : Type*) [CommSemiring R] (a b : R) : QuadraticForm R (Fin 2 → R) :=
  a • QuadraticMap.proj 0 0 + QuadraticMap.proj 0 1 + b • QuadraticMap.proj 1 1

/-- Explicit evaluation formula for `TauCeti.symplecticPlane`. -/
@[simp]
theorem symplecticPlane_apply {R : Type*} [CommSemiring R] (a b : R) (x : Fin 2 → R) :
    symplecticPlane R a b x = a * (x 0 * x 0) + x 0 * x 1 + b * (x 1 * x 1) := by
  simp [symplecticPlane, smul_eq_mul]

/-- With zero diagonal coefficients, `TauCeti.symplecticPlane` is the hyperbolic plane `x₀ x₁`. -/
theorem symplecticPlane_zero_zero {R : Type*} [CommSemiring R] (x : Fin 2 → R) :
    symplecticPlane R 0 0 x = x 0 * x 1 := by
  simp

/-- In characteristic two, the polar form of `TauCeti.symplecticPlane` is `x₀ y₁ + x₁ y₀`,
independent of the diagonal coefficients `a` and `b`. -/
@[simp]
theorem polar_symplecticPlane {R : Type*} [CommRing R] [CharP R 2] (a b : R) (x y : Fin 2 → R) :
    QuadraticMap.polar (symplecticPlane R a b) x y = x 0 * y 1 + x 1 * y 0 := by
  calc
    QuadraticMap.polar (symplecticPlane R a b) x y
      = a * ((2 : R) * (x 0 * y 0)) + (x 0 * y 1 + x 1 * y 0) +
          b * ((2 : R) * (x 1 * y 1)) := by
        simp only [QuadraticMap.polar, symplecticPlane_apply, Pi.add_apply]
        ring
    _ = x 0 * y 1 + x 1 * y 0 := by simp

/-- In characteristic two, the polar bilinear form of `TauCeti.symplecticPlane` is nondegenerate. -/
@[simp]
theorem nondegenerate_polarBilin_symplecticPlane {R : Type*} [CommRing R] [CharP R 2] (a b : R) :
    (symplecticPlane R a b).polarBilin.Nondegenerate := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (symplecticPlane R a b).isSymm_polarBilin.isRefl]
  intro x hx
  have hx0 : x 0 = 0 := by simpa using hx ![0, 1]
  have hx1 : x 1 = 0 := by simpa using hx ![1, 0]
  exact funext (Fin.forall_fin_two.mpr ⟨hx0, hx1⟩)

/-- The standard basis of `Fin 2 → R` indexed by `Fin 1 ⊕ Fin 1`, sending `inl 0` to `![1, 0]` and
`inr 0` to `![0, 1]`. -/
noncomputable def symplecticPlaneBasis (R : Type*) [CommSemiring R] :
    Module.Basis (Fin 1 ⊕ Fin 1) R (Fin 2 → R) :=
  (Pi.basisFun R (Fin 2)).reindex (@finSumFinEquiv 1 1).symm

/-- The `inl 0` vector of `TauCeti.symplecticPlaneBasis` is `![1, 0]`. -/
@[simp]
theorem symplecticPlaneBasis_inl (R : Type*) [CommSemiring R] (i : Fin 1) :
    symplecticPlaneBasis R (Sum.inl i) = ![1, 0] := by
  have h0 : (@finSumFinEquiv 1 1) (Sum.inl 0) = 0 := rfl
  rw [Subsingleton.elim i 0]
  ext j
  fin_cases j <;> simp [symplecticPlaneBasis, h0]

/-- The `inr 0` vector of `TauCeti.symplecticPlaneBasis` is `![0, 1]`. -/
@[simp]
theorem symplecticPlaneBasis_inr (R : Type*) [CommSemiring R] (i : Fin 1) :
    symplecticPlaneBasis R (Sum.inr i) = ![0, 1] := by
  have h1 : (@finSumFinEquiv 1 1) (Sum.inr 0) = 1 := rfl
  rw [Subsingleton.elim i 0]
  ext j
  fin_cases j <;> simp [symplecticPlaneBasis, h1]

/-- In characteristic two, the polar form of `TauCeti.symplecticPlane` has matrix `Matrix.J` in
`TauCeti.symplecticPlaneBasis`. -/
@[simp]
theorem toMatrix_polarBilin_symplecticPlane {R : Type*} [CommRing R] [CharP R 2] (a b : R) :
    LinearMap.BilinForm.toMatrix (symplecticPlaneBasis R) (symplecticPlane R a b).polarBilin =
      Matrix.J (Fin 1) R := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.J, Matrix.fromBlocks]

end SymplecticPlane

end TauCeti

namespace QuadraticMap

open TauCeti

section SymplecticDecomposition

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- In characteristic two, a basis `b : Module.Basis (ι ⊕ ι) R V` puts `q.polarBilin` into the
standard symplectic matrix `Matrix.J ι R` if and only if each half is polar-isotropic and the cross
pairings are Kronecker deltas. -/
theorem toMatrix_polarBilin_eq_J_iff [CharP R 2] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm R V) (b : Module.Basis (ι ⊕ ι) R V) :
    LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J ι R ↔
      (∀ i j, polar q (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, polar q (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, polar q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) := by
  constructor
  · intro hb
    have entry (x y : ι ⊕ ι) : polar q (b x) (b y) = Matrix.J ι R x y := by
      simpa only [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply] using
        congrFun (congrFun hb x) y
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simpa [Matrix.J, Matrix.fromBlocks] using entry (Sum.inl i) (Sum.inl j)
    · simpa [Matrix.J, Matrix.fromBlocks] using entry (Sum.inr i) (Sum.inr j)
    · simpa [Matrix.J, Matrix.fromBlocks, Matrix.one_apply] using entry (Sum.inl i) (Sum.inr j)
  · rintro ⟨hll, hrr, hlr⟩
    ext x y
    rw [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply]
    rcases x with i | i <;> rcases y with j | j
    · simpa [Matrix.J, Matrix.fromBlocks] using hll i j
    · simpa [Matrix.J, Matrix.fromBlocks, Matrix.one_apply] using hlr i j
    · rw [polar_comm]
      simpa [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, eq_comm] using hlr j i
    · simpa [Matrix.J, Matrix.fromBlocks] using hrr i j

/-- Grouping coordinates along a basis `b : Module.Basis (ι ⊕ ι) R V` into pairs in `Fin 2 → R`. -/
private noncomputable def symplecticCoordsLinearEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis (ι ⊕ ι) R V) : V ≃ₗ[R] (ι → Fin 2 → R) :=
  b.equivFun.trans
    { toFun := fun f i ↦ ![f (Sum.inl i), f (Sum.inr i)]
      invFun := fun g ↦ Sum.elim (fun i ↦ g i 0) (fun i ↦ g i 1)
      map_add' := fun f₁ f₂ ↦ by ext i j; fin_cases j <;> simp
      map_smul' := fun r f ↦ by ext i j; fin_cases j <;> simp
      left_inv := fun f ↦ by ext x; rcases x with i | i <;> simp
      right_inv := fun g ↦ by ext i j; fin_cases j <;> simp }

private theorem piSymplecticPlane_map_app {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm R V) (b : Module.Basis (ι ⊕ ι) R V)
    (hb : LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J ι R) (v : V) :
    (QuadraticMap.pi fun i : ι ↦ symplecticPlane R (q (b (Sum.inl i))) (q (b (Sum.inr i))))
      (symplecticCoordsLinearEquiv b v) = q v := by
  have entry (x y : ι ⊕ ι) : polar q (b x) (b y) = Matrix.J ι R x y := by
    simpa only [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply] using
      congrFun (congrFun hb x) y
  have hll (i j : ι) : polar q (b (Sum.inl i)) (b (Sum.inl j)) = 0 := by
    simpa [Matrix.J, Matrix.fromBlocks] using entry (Sum.inl i) (Sum.inl j)
  have hrr (i j : ι) : polar q (b (Sum.inr i)) (b (Sum.inr j)) = 0 := by
    simpa [Matrix.J, Matrix.fromBlocks] using entry (Sum.inr i) (Sum.inr j)
  have hlr (i j : ι) : polar q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0 := by
    rw [polar_comm]
    simpa [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, eq_comm] using
      entry (Sum.inr j) (Sum.inl i)
  let p : ι → V := fun i ↦
    b.repr v (Sum.inl i) • b (Sum.inl i) + b.repr v (Sum.inr i) • b (Sum.inr i)
  have hv : ∑ i : ι, p i = v := by
    rw [← b.sum_repr v, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have horth {i j : ι} (hij : i ≠ j) : polar q (p i) (p j) = 0 := by
    simp only [p, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      hll, hrr, hlr i j, hij, ite_false]
    rw [polar_comm q (b (Sum.inr i)) (b (Sum.inl j)), hlr j i]; simp [hij.symm]
  have hp (i : ι) : q (p i) = symplecticPlane R (q (b (Sum.inl i))) (q (b (Sum.inr i)))
      ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)] := by
    simp only [p, QuadraticMap.map_add, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
      hlr i i, ite_true, smul_eq_mul, symplecticPlane_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
  have hsym2 : ∑ s ∈ Finset.univ.sym2 with ¬ s.IsDiag, polarSym2 q (s.map p) = 0 :=
    Finset.sum_eq_zero (Sym2.ind fun _ _ hs ↦
      horth (Sym2.mk_isDiag_iff.not.mp (Finset.mem_filter.mp hs).2))
  nth_rw 2 [← hv]
  rw [QuadraticMap.pi_apply, q.map_sum, hsym2, add_zero]
  exact Finset.sum_congr rfl fun i _ ↦ (hp i).symm

/-- Any symplectic basis `b` for `q.polarBilin` gives an explicit isometry between `q` and the
orthogonal sum of the binary symplectic planes
`symplecticPlane R (q (b (inl i))) (q (b (inr i)))`. -/
noncomputable def isometryEquivPiSymplecticPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm R V) (b : Module.Basis (ι ⊕ ι) R V)
    (hb : LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J ι R) :
    q.IsometryEquiv
      (QuadraticMap.pi fun i : ι ↦
        symplecticPlane R (q (b (Sum.inl i))) (q (b (Sum.inr i)))) where
  toLinearEquiv := symplecticCoordsLinearEquiv b
  map_app' := piSymplecticPlane_map_app q b hb

/-- Coordinates of `QuadraticMap.isometryEquivPiSymplecticPlane` are the symplectic basis
coefficients of `v`. -/
@[simp]
theorem isometryEquivPiSymplecticPlane_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm R V) (b : Module.Basis (ι ⊕ ι) R V)
    (hb : LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J ι R) (v : V) (i : ι) :
    q.isometryEquivPiSymplecticPlane b hb v i = ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)] :=
  -- The parentheses keep the proof opaque, so the definition need not be exposed.
  (rfl)

end SymplecticDecomposition

section GaussSumSemiring

variable {V : Type*} [AddCommMonoid V] [Module (ZMod 2) V] [Fintype V]

/-- The integer Gauss sum `∑ v : V, (-1 : ℤ) ^ (q v).val` of a quadratic form over `ZMod 2` on a
finite module. -/
def gaussSum (q : QuadraticForm (ZMod 2) V) : ℤ :=
  ∑ v : V, (-1 : ℤ) ^ (q v).val

/-- Explicit sum definition of `QuadraticMap.gaussSum`. -/
theorem gaussSum_def (q : QuadraticForm (ZMod 2) V) :
    q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (q v).val :=
  -- The parentheses keep the proof opaque, so the definition need not be exposed.
  (rfl)

/-- On a subsingleton module, every quadratic form has Gauss sum `1`. -/
@[simp]
theorem gaussSum_subsingleton [Subsingleton V] (q : QuadraticForm (ZMod 2) V) :
    q.gaussSum = 1 := by
  let _ : Unique V := uniqueOfSubsingleton (0 : V)
  rw [gaussSum, Finset.univ_unique, Finset.sum_singleton, Subsingleton.elim (default : V) 0]
  simp

/-- The zero quadratic form on `V` has Gauss sum `Fintype.card V`. -/
@[simp]
theorem gaussSum_zero : (0 : QuadraticForm (ZMod 2) V).gaussSum = Fintype.card V := by
  simp [gaussSum]

/-- Isometric quadratic forms over `ZMod 2` have equal Gauss sums. -/
theorem IsometryEquiv.gaussSum_eq {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W] [Fintype W]
    {q₁ : QuadraticForm (ZMod 2) V} {q₂ : QuadraticForm (ZMod 2) W}
    (e : q₁.IsometryEquiv q₂) : q₁.gaussSum = q₂.gaussSum := by
  rw [gaussSum, gaussSum, ← e.toEquiv.sum_comp (fun w ↦ (-1 : ℤ) ^ (q₂ w).val)]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- `e.toEquiv` is definitionally `e` on vectors.
  change (-1 : ℤ) ^ (q₁ v).val = (-1 : ℤ) ^ (q₂ (e v)).val
  rw [e.map_app]

/-- Equivalent quadratic forms over `ZMod 2` have equal Gauss sums. -/
theorem Equivalent.gaussSum_eq {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W] [Fintype W]
    {q₁ : QuadraticForm (ZMod 2) V} {q₂ : QuadraticForm (ZMod 2) W}
    (h : q₁.Equivalent q₂) : q₁.gaussSum = q₂.gaussSum :=
  let ⟨e⟩ := h
  e.gaussSum_eq

/-- The Gauss sum is multiplicative under orthogonal products of quadratic forms. -/
@[simp]
theorem gaussSum_prod {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W] [Fintype W]
    (q₁ : QuadraticForm (ZMod 2) V) (q₂ : QuadraticForm (ZMod 2) W) :
    (q₁.prod q₂).gaussSum = q₁.gaussSum * q₂.gaussSum := by
  have hadd (x y : ZMod 2) : (-1 : ℤ) ^ (x + y).val = (-1 : ℤ) ^ x.val * (-1 : ℤ) ^ y.val := by
    revert x y; decide
  simp only [gaussSum, Fintype.sum_prod_type, prod_apply, hadd, Finset.sum_mul_sum]

omit [AddCommMonoid V] [Module (ZMod 2) V] [Fintype V] in
/-- The Gauss sum of a finite orthogonal sum is the product of the Gauss sums of the summands. -/
@[simp]
theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, Fintype (M i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (M i)) :
    (QuadraticMap.pi Q).gaussSum = ∏ i : ι, (Q i).gaussSum := by
  have hsum : ∀ (s : Finset ι) (f : ι → ZMod 2),
      (-1 : ℤ) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1 : ℤ) ^ (f i).val := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      have hadd (x y : ZMod 2) : (-1 : ℤ) ^ (x + y).val = (-1 : ℤ) ^ x.val * (-1 : ℤ) ^ y.val := by
        revert x y; decide
      rw [Finset.sum_cons, Finset.prod_cons, hadd, ih]
  rw [gaussSum, Finset.sum_congr rfl fun x _ ↦ ?_, ← Fintype.prod_sum]
  · rfl
  · rw [QuadraticMap.pi_apply, hsum]

omit [AddCommMonoid V] [Module (ZMod 2) V] [Fintype V] in
/-- On `symplecticPlane (ZMod 2) a b`, the Gauss sum equals `(-1) ^ (a * b).val * 2`:
`+2` when `a * b = 0` and `-2` when `a = b = 1`. -/
@[simp]
theorem gaussSum_symplecticPlane (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).gaussSum = (-1 : ℤ) ^ (a * b).val * 2 := by
  revert a b; decide

end GaussSumSemiring

section GaussSumGroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Descending a quadratic form over `ZMod 2` along a submodule `N` of its radical multiplies the
Gauss sum by `Nat.card N`. -/
theorem gaussSum_eq_card_mul_gaussSum_lift [Fintype V] (q : QuadraticForm (ZMod 2) V)
    (N : Submodule (ZMod 2) V) [Fintype (V ⧸ N)] (hN : N ≤ q.radical) :
    q.gaussSum = Nat.card N * (q.lift N hN).gaussSum := by
  classical
  let _ : Fintype N := Fintype.ofFinite N
  obtain ⟨W, hW⟩ := N.exists_isCompl
  let e : ((0 : QuadraticForm (ZMod 2) N).prod (q.lift N hN)).IsometryEquiv q :=
    { toLinearEquiv :=
        (LinearEquiv.prodComm (ZMod 2) N (V ⧸ N)).trans
          (((N.quotientEquivOfIsCompl W hW).prodCongr (LinearEquiv.refl (ZMod 2) N)).trans
            (W.prodEquivOfIsCompl N hW.symm))
      map_app' := fun x ↦ by
        -- Expose the direct-sum equivalence as addition of the complement representative and `x.1`.
        change q ((N.quotientEquivOfIsCompl W hW x.2 : V) + x.1) = _
        have hmk : (Submodule.Quotient.mk (N.quotientEquivOfIsCompl W hW x.2 : V) : V ⧸ N) = x.2 :=
          Submodule.mk_quotientEquivOfIsCompl_apply hW x.2
        rw [add_comm, (mem_radical_iff'.mp (hN x.1.2)).2, prod_apply, zero_apply, zero_add,
          ← hmk, lift_mk, hmk] }
  rw [← e.gaussSum_eq, gaussSum_prod, gaussSum_zero, Nat.card_eq_fintype_card]

/-- If the polar kernel of `q` contains a vector `r` with `q r ≠ 0`, then translation by `r` flips
the sign of `(-1) ^ (q v).val` across `V`, so `q.gaussSum = 0`. -/
theorem gaussSum_eq_zero_of_exists_mem_ker_polarBilin [Fintype V] (q : QuadraticForm (ZMod 2) V)
    {r : V} (hr : r ∈ q.polarBilin.ker) (hqr : q r ≠ 0) :
    q.gaussSum = 0 := by
  have hr1 : q r = 1 := by revert hqr; generalize q r = c; revert c; decide
  have hpol (v : V) : polar q v r = 0 := by
    rw [polar_comm, ← polarBilin_apply_apply, LinearMap.mem_ker.mp hr, LinearMap.zero_apply]
  have hflip (x : ZMod 2) : (-1 : ℤ) ^ (x + 1).val = -((-1 : ℤ) ^ x.val) := by
    revert x; decide
  have hneg : q.gaussSum = -q.gaussSum := by
    calc
      q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (q (v + r)).val := by
        rw [gaussSum, ← Equiv.sum_comp (Equiv.addRight r) (fun w ↦ (-1 : ℤ) ^ (q w).val)]
        rfl
      _ = ∑ v : V, -((-1 : ℤ) ^ (q v).val) := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [QuadraticMap.map_add q v r, hpol v, add_zero, hr1, hflip]
      _ = -q.gaussSum := by rw [Finset.sum_neg_distrib, gaussSum]
  omega

/-- Evaluated on a symplectic basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` for `q.polarBilin`, the
Gauss sum of `q` equals `(-1) ^ (∑ i, q (b (inl i)) * q (b (inr i))).val * 2 ^ card ι`. -/
theorem gaussSum_of_toMatrix_eq_J [Fintype V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm (ZMod 2) V) (b : Module.Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J ι (ZMod 2)) :
    q.gaussSum =
      (-1 : ℤ) ^ (∑ i : ι, q (b (Sum.inl i)) * q (b (Sum.inr i))).val *
        (2 : ℤ) ^ Fintype.card ι := by
  rw [(q.isometryEquivPiSymplecticPlane b hb).gaussSum_eq, gaussSum_pi]
  simp only [gaussSum_symplecticPlane, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hadd (x y : ZMod 2) : (-1 : ℤ) ^ (x + y).val = (-1 : ℤ) ^ x.val * (-1 : ℤ) ^ y.val := by
      revert x y; decide
    rw [Finset.prod_cons, Finset.sum_cons, hadd, ih]

/-- **Basis-independence of the Arf sum.** Any two symplectic bases of `q.polarBilin` over `ZMod 2`
yield the same sum `∑ i, q (b (inl i)) * q (b (inr i))`. -/
theorem sum_mul_eq_of_toMatrix_eq_J {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] {q : QuadraticForm (ZMod 2) V}
    (b₁ : Module.Basis (ι₁ ⊕ ι₁) (ZMod 2) V) (b₂ : Module.Basis (ι₂ ⊕ ι₂) (ZMod 2) V)
    (hb₁ : LinearMap.BilinForm.toMatrix b₁ q.polarBilin = Matrix.J ι₁ (ZMod 2))
    (hb₂ : LinearMap.BilinForm.toMatrix b₂ q.polarBilin = Matrix.J ι₂ (ZMod 2)) :
    ∑ i : ι₁, q (b₁ (Sum.inl i)) * q (b₁ (Sum.inr i)) =
      ∑ i : ι₂, q (b₂ (Sum.inl i)) * q (b₂ (Sum.inr i)) := by
  let _ : Fintype V := Fintype.ofEquiv _ b₁.equivFun.symm.toEquiv
  have hcard : Fintype.card ι₁ = Fintype.card ι₂ := by
    have h1 := Module.finrank_eq_card_basis b₁
    have h2 := Module.finrank_eq_card_basis b₂
    simp only [Fintype.card_sum] at h1 h2
    omega
  have hg := (q.gaussSum_of_toMatrix_eq_J b₁ hb₁).symm.trans (q.gaussSum_of_toMatrix_eq_J b₂ hb₂)
  rw [← hcard] at hg
  have hpow : (2 : ℤ) ^ Fintype.card ι₁ ≠ 0 := pow_ne_zero _ (by decide)
  have hsign := mul_right_cancel₀ hpow hg
  generalize ∑ i : ι₁, q (b₁ (Sum.inl i)) * q (b₁ (Sum.inr i)) = s₁ at hsign ⊢
  generalize ∑ i : ι₂, q (b₂ (Sum.inl i)) * q (b₂ (Sum.inr i)) = s₂ at hsign ⊢
  revert s₁ s₂ hsign; decide

end GaussSumGroup

section Arf

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The *Arf invariant* in `ZMod 2` of a quadratic form `q` over `ZMod 2`.

When `V` is finite-dimensional and `q.polarBilin` is nondegenerate, `q.arf` is the sum
`∑ i, q (b (inl i)) * q (b (inr i))` in any symplectic basis `b` of `q.polarBilin`. When `V` is
infinite-dimensional or `q.polarBilin` is degenerate, `q.arf` takes the junk value `0`. -/
noncomputable def arf (q : QuadraticForm (ZMod 2) V) : ZMod 2 := by
  classical
  exact if h : FiniteDimensional (ZMod 2) V ∧ q.polarBilin.Nondegenerate then
    let hex := (haveI := h.1; LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J
      q.isAlt_polarBilin h.2)
    let b := hex.choose_spec.choose
    ∑ i, q (b (Sum.inl i)) * q (b (Sum.inr i))
  else 0

/-- On an infinite-dimensional module, `QuadraticMap.arf` takes the junk value `0`. -/
theorem arf_of_not_finiteDimensional {q : QuadraticForm (ZMod 2) V}
    (h : ¬ FiniteDimensional (ZMod 2) V) : q.arf = 0 := by
  simp only [arf, h, false_and, ↓reduceDIte]

/-- When `q.polarBilin` is degenerate, `QuadraticMap.arf` takes the junk value `0`. -/
theorem arf_of_not_nondegenerate_polarBilin {q : QuadraticForm (ZMod 2) V}
    (h : ¬ q.polarBilin.Nondegenerate) : q.arf = 0 := by
  simp only [arf, h, and_false, ↓reduceDIte]

/-- In any symplectic basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` for `q.polarBilin`, the Arf
invariant equals `∑ i, q (b (inl i)) * q (b (inr i))`. Both finite-dimensionality of `V` and
nondegeneracy of `q.polarBilin` follow automatically from the existence of `b`. -/
theorem arf_eq_sum_of_toMatrix_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm (ZMod 2) V) (b : Module.Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J ι (ZMod 2)) :
    q.arf = ∑ i : ι, q (b (Sum.inl i)) * q (b (Sum.inr i)) := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis b
  have hnd : q.polarBilin.Nondegenerate := by
    rw [(q.isometryEquivPiSymplecticPlane b hb).nondegenerate_polarBilin_iff,
      nondegenerate_polarBilin_pi_iff]
    exact fun i ↦ nondegenerate_polarBilin_symplecticPlane _ _
  have hex := (have := hfin; LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J
    q.isAlt_polarBilin hnd)
  have harf : q.arf =
      ∑ i, q (hex.choose_spec.choose (Sum.inl i)) * q (hex.choose_spec.choose (Sum.inr i)) := by
    simp only [arf, hfin, hnd, and_self, ↓reduceDIte]
  exact harf.trans
    (sum_mul_eq_of_toMatrix_eq_J hex.choose_spec.choose b hex.choose_spec.choose_spec hb)

/-- Matrix-free symplectic basis formula for `QuadraticMap.arf`: if each half of `b` is
polar-isotropic and `polar q (b (inl i)) (b (inr j)) = δᵢⱼ`, then
`q.arf = ∑ i, q (b (inl i)) * q (b (inr i))`. -/
theorem arf_eq_sum_of_polar_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticForm (ZMod 2) V) (b : Module.Basis (ι ⊕ ι) (ZMod 2) V)
    (hll : ∀ i j, polar q (b (Sum.inl i)) (b (Sum.inl j)) = 0)
    (hrr : ∀ i j, polar q (b (Sum.inr i)) (b (Sum.inr j)) = 0)
    (hlr : ∀ i j, polar q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) :
    q.arf = ∑ i : ι, q (b (Sum.inl i)) * q (b (Sum.inr i)) :=
  q.arf_eq_sum_of_toMatrix_eq_J b ((q.toMatrix_polarBilin_eq_J_iff b).mpr ⟨hll, hrr, hlr⟩)

/-- On a subsingleton module, every quadratic form has Arf invariant `0`. -/
@[simp]
theorem arf_subsingleton [Subsingleton V] (q : QuadraticForm (ZMod 2) V) : q.arf = 0 := by
  let b : Module.Basis (Fin 0 ⊕ Fin 0) (ZMod 2) V := Module.Basis.empty V
  have hb : LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin 0) (ZMod 2) := by
    ext x
    exact isEmptyElim x
  simpa using q.arf_eq_sum_of_toMatrix_eq_J b hb

/-- The zero quadratic form on any module has Arf invariant `0`. -/
@[simp]
theorem arf_zero : (0 : QuadraticForm (ZMod 2) V).arf = 0 := by
  unfold arf
  split_ifs <;> simp

/-- Isometric quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem IsometryEquiv.arf_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {q₁ : QuadraticForm (ZMod 2) V} {q₂ : QuadraticForm (ZMod 2) W}
    (e : q₁.IsometryEquiv q₂) : q₁.arf = q₂.arf := by
  by_cases hfin₁ : FiniteDimensional (ZMod 2) V
  · by_cases hnd₁ : q₁.polarBilin.Nondegenerate
    · obtain ⟨m, b, hb⟩ :=
        LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J q₁.isAlt_polarBilin hnd₁
      have hb₂ : LinearMap.BilinForm.toMatrix (b.map e.toLinearEquiv) q₂.polarBilin =
          Matrix.J (Fin m) (ZMod 2) := by
        rw [← hb]
        ext x y
        simp [LinearMap.BilinForm.toMatrix_apply]
      rw [q₁.arf_eq_sum_of_toMatrix_eq_J b hb,
        q₂.arf_eq_sum_of_toMatrix_eq_J (b.map e.toLinearEquiv) hb₂]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Module.Basis.map_apply, IsometryEquiv.coe_toLinearEquiv, e.map_app]
    · have hnd₂ : ¬ q₂.polarBilin.Nondegenerate := mt e.nondegenerate_polarBilin_iff.mpr hnd₁
      rw [arf_of_not_nondegenerate_polarBilin hnd₁, arf_of_not_nondegenerate_polarBilin hnd₂]
  · have hfin₂ : ¬ FiniteDimensional (ZMod 2) W := fun hW ↦
      hfin₁ (have := hW; e.symm.toLinearEquiv.finiteDimensional)
    rw [arf_of_not_finiteDimensional hfin₁, arf_of_not_finiteDimensional hfin₂]

/-- Equivalent quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem Equivalent.arf_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {q₁ : QuadraticForm (ZMod 2) V} {q₂ : QuadraticForm (ZMod 2) W}
    (h : q₁.Equivalent q₂) : q₁.arf = q₂.arf :=
  let ⟨e⟩ := h
  e.arf_eq

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The Arf invariant of `symplecticPlane (ZMod 2) a b` is `a * b`: `0` when at least one
coefficient vanishes, and `1` on the anisotropic plane `x₀² + x₀ x₁ + x₁²`. -/
@[simp]
theorem arf_symplecticPlane (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).arf = a * b := by
  rw [(symplecticPlane (ZMod 2) a b).arf_eq_sum_of_toMatrix_eq_J
    (symplecticPlaneBasis (ZMod 2)) (toMatrix_polarBilin_symplecticPlane a b)]
  simp

/-- **Gauss sum formula for the Arf invariant.** For a quadratic form `q` on a finite space `V`
over `ZMod 2` with nondegenerate polar form,
`q.gaussSum = (-1) ^ q.arf.val * 2 ^ (finrank (ZMod 2) V / 2)`. -/
theorem gaussSum_eq [Fintype V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) :
    q.gaussSum = (-1 : ℤ) ^ q.arf.val * (2 : ℤ) ^ (Module.finrank (ZMod 2) V / 2) := by
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J q.isAlt_polarBilin hq
  have hdim : Module.finrank (ZMod 2) V / 2 = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [q.arf_eq_sum_of_toMatrix_eq_J b hb, q.gaussSum_of_toMatrix_eq_J b hb,
    Fintype.card_fin, hdim]

/-- Gauss sum formula in terms of the half-dimension `m` when `finrank (ZMod 2) V = 2 * m`. -/
theorem gaussSum_eq_of_finrank_eq_two_mul [Fintype V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m) :
    q.gaussSum = (-1 : ℤ) ^ q.arf.val * (2 : ℤ) ^ m := by
  rw [q.gaussSum_eq hq, hm, Nat.mul_div_right _ (by omega)]

/-- The Arf invariant is additive under orthogonal products of finite-dimensional quadratic spaces
with nondegenerate polar forms. -/
theorem arf_prod {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {q₁ : QuadraticForm (ZMod 2) V} {q₂ : QuadraticForm (ZMod 2) W}
    (hq₁ : q₁.polarBilin.Nondegenerate) (hq₂ : q₂.polarBilin.Nondegenerate) :
    (q₁.prod q₂).arf = q₁.arf + q₂.arf := by
  let _ : Fintype V := Fintype.ofEquiv _ (Module.finBasis (ZMod 2) V).equivFun.symm.toEquiv
  let _ : Fintype W := Fintype.ofEquiv _ (Module.finBasis (ZMod 2) W).equivFun.symm.toEquiv
  obtain ⟨m₁, hm₁⟩ := LinearMap.BilinForm.IsAlt.even_finrank q₁.isAlt_polarBilin hq₁
  obtain ⟨m₂, hm₂⟩ := LinearMap.BilinForm.IsAlt.even_finrank q₂.isAlt_polarBilin hq₂
  have hdim₁ : Module.finrank (ZMod 2) V = 2 * m₁ := by omega
  have hdim₂ : Module.finrank (ZMod 2) W = 2 * m₂ := by omega
  have hdim : Module.finrank (ZMod 2) (V × W) = 2 * (m₁ + m₂) := by
    rw [Module.finrank_prod, hdim₁, hdim₂]
    omega
  have hg := gaussSum_prod q₁ q₂
  rw [q₁.gaussSum_eq_of_finrank_eq_two_mul hq₁ hdim₁,
    q₂.gaussSum_eq_of_finrank_eq_two_mul hq₂ hdim₂,
    (q₁.prod q₂).gaussSum_eq_of_finrank_eq_two_mul
      (nondegenerate_polarBilin_prod_iff.mpr ⟨hq₁, hq₂⟩) hdim] at hg
  have hadd (x y : ZMod 2) : (-1 : ℤ) ^ (x + y).val = (-1 : ℤ) ^ x.val * (-1 : ℤ) ^ y.val := by
    revert x y; decide
  have hmul :
      (-1 : ℤ) ^ (q₁.prod q₂).arf.val * (2 : ℤ) ^ (m₁ + m₂) =
        (-1 : ℤ) ^ (q₁.arf + q₂.arf).val * (2 : ℤ) ^ (m₁ + m₂) := by
    rw [hg, hadd, pow_add]
    ring
  have hsign := mul_right_cancel₀ (pow_ne_zero (m₁ + m₂) (by decide : (2 : ℤ) ≠ 0)) hmul
  generalize (q₁.prod q₂).arf = c₁ at hsign ⊢
  generalize q₁.arf + q₂.arf = c₂ at hsign ⊢
  revert c₁ c₂ hsign; decide

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The Arf invariant of a finite orthogonal sum of finite-dimensional quadratic spaces with
nondegenerate polar forms is the sum of their Arf invariants. -/
theorem arf_pi.{u} {ι : Type*} [Fintype ι] {M : ι → Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    [∀ i, FiniteDimensional (ZMod 2) (M i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (M i)}
    (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i : ι, (Q i).arf := by
  have key : ∀ (n : ℕ) {M' : Fin n → Type u}
      [∀ i, AddCommGroup (M' i)] [∀ i, Module (ZMod 2) (M' i)]
      [∀ i, FiniteDimensional (ZMod 2) (M' i)]
      {Q' : ∀ i, QuadraticForm (ZMod 2) (M' i)},
      (∀ i, (Q' i).polarBilin.Nondegenerate) →
      (QuadraticMap.pi Q').arf = ∑ i : Fin n, (Q' i).arf := by
    intro n
    induction n with
    | zero =>
      intro M' _ _ _ Q' _
      simp
    | succ n ih =>
      intro M' _ _ _ Q' hQn
      rw [← (IsometryEquiv.consPi Q').arf_eq,
        arf_prod (hQn 0) (nondegenerate_polarBilin_pi_iff.mpr fun i ↦ hQn i.succ),
        ih (fun i ↦ hQn i.succ), Fin.sum_univ_succ]
  let e := Fintype.equivFin ι
  rw [← (IsometryEquiv.piCongrLeft Q e.symm).arf_eq, key (Fintype.card ι) (fun j ↦ hQ (e.symm j)),
    ← e.symm.sum_comp (fun i ↦ (Q i).arf)]

/-- For a subspace `W` of a finite-dimensional space `V` on which `q.restrict W` and `q` have
nondegenerate polar forms, `q.arf` splits as the sum of the Arf invariants on `W` and on its polar
orthogonal complement. -/
theorem arf_eq_arf_restrict_add_arf_restrict_orthogonal [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate)
    (W : Submodule (ZMod 2) V) (hW : (q.restrict W).polarBilin.Nondegenerate) :
    q.arf =
      (q.restrict W).arf + (q.restrict (LinearMap.BilinForm.orthogonal q.polarBilin W)).arf := by
  have hB : LinearMap.BilinForm.Nondegenerate (LinearMap.BilinForm.restrict q.polarBilin W) := by
    rw [LinearMap.BilinForm.restrict, ← polarBilin_restrict]
    exact hW
  have hcomp : IsCompl W (LinearMap.BilinForm.orthogonal q.polarBilin W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      q.isSymm_polarBilin.isRefl hB
  have hprod :
      ((q.restrict W).prod
        (q.restrict (LinearMap.BilinForm.orthogonal q.polarBilin W))).polarBilin.Nondegenerate :=
    (IsometryEquiv.prodRestrictOrthogonal q W hcomp).symm.nondegenerate_polarBilin_iff.mp hq
  rw [← (IsometryEquiv.prodRestrictOrthogonal q W hcomp).arf_eq,
    arf_prod hW (nondegenerate_polarBilin_prod_iff.mp hprod).2]

end Arf

end QuadraticMap
