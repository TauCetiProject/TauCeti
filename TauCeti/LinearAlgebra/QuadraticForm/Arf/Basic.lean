/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Trace
public import TauCeti.LinearAlgebra.QuadraticForm.CharTwo
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.Data.ZMod.Two
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The Gauss sum and Arf invariant of a quadratic form over `𝔽₂`

Over an arbitrary field `K` of characteristic two, the Arf invariant of a finite-dimensional
quadratic form with nondegenerate polar form takes values in the Artin--Schreier additive quotient
`K / {t ^ 2 + t | t ∈ K}`. Over `ZMod 2`, every scalar satisfies `t ^ 2 + t = 0`, so the
Artin--Schreier subgroup vanishes and the Arf invariant is an element of `ZMod 2` itself: in any
symplectic basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` of `Q.polarBilin`, it is given by
`∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`.

Following Brown and Browder, we establish basis independence through the integer Gauss sum
`Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val`:

1. `Q.gaussSum` is manifestly independent of coordinates, invariant under isometry, and
   multiplicative under `QuadraticMap.prod` and `QuadraticMap.pi`.
2. On a binary quadratic form `TauCeti.binaryQuadraticForm (ZMod 2) a b`, it evaluates to
   `(-1) ^ (a * b).val * 2`.
3. Decomposing `(V, Q)` along any symplectic basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` via
   `QuadraticMap.isometryEquivPiBinaryQuadraticForm` therefore evaluates `Q.gaussSum` to
   `(-1) ^ (∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι`. Since
   `2 ^ Fintype.card ι ≠ 0` in `ℤ`, the symplectic-basis sum depends only on `Q`.

These steps are the case `k = ZMod 2` of the absolute-trace Gauss sum `QuadraticMap.traceGaussSum`
and Arf invariant `QuadraticMap.traceArf` over a finite field `k` of characteristic two
(`TauCeti.LinearAlgebra.QuadraticForm.Arf.Trace`): the absolute trace of `ZMod 2` over itself is the
identity, so `Q.traceGaussSum = Q.gaussSum` (`QuadraticMap.traceGaussSum_eq_gaussSum`) and
`Q.traceArf = Q.arf` (`QuadraticMap.traceArf_eq_arf`), and the results above are specializations
of their trace versions.

From the Gauss-sum identity we deduce isometry invariance and orthogonal-sum additivity of
`QuadraticMap.arf`, the exact cardinality formulas for `{v : V // Q v = 0}` and
`{v : V // Q v = 1}`, the *majority-vote* characterization (`Q.arf = 0` if and only if `Q` vanishes
on strictly more vectors than it takes the value `1`), and the Gauss-sum descent and vanishing
criteria across submodules of `Q.radical` and `Q.polarBilin.ker`.

## Main definitions

* `QuadraticMap.gaussSum`: the integer sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of
  `Q : QuadraticForm (ZMod 2) V`.
* `QuadraticMap.arf`: the `ZMod 2`-valued Arf invariant of `Q : QuadraticForm (ZMod 2) V` (defined
  as `0` when `V` is infinite-dimensional or `Q.polarBilin` is degenerate).

## Main results

* `QuadraticMap.traceGaussSum_eq_gaussSum`, `QuadraticMap.traceArf_eq_arf`: over `ZMod 2` the
  absolute-trace Gauss sum and Arf invariant are `Q.gaussSum` and `Q.arf`.
* `QuadraticMap.gaussSum_eq_of_toMatrix_polarBilin_eq_J`: evaluation of `Q.gaussSum` in any
  symplectic basis.
* `QuadraticMap.sum_mul_eq_of_toMatrix_polarBilin_eq_J`: independence of
  `∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` from the choice of symplectic basis `b`.
* `QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`: `Q.arf` equals the symplectic-basis sum in
  every symplectic basis of `Q.polarBilin`.
* `QuadraticMap.gaussSum_eq_of_finrank_eq`, `QuadraticMap.arf_eq_of_gaussSum_eq`,
  `QuadraticMap.gaussSum_ne_zero_of_nondegenerate_polarBilin`:
  `Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ m` when `Module.finrank (ZMod 2) V = 2 * m`, determining
  `Q.arf` and showing `Q.gaussSum ≠ 0`.
* `QuadraticMap.IsometryEquiv.arf_eq`, `QuadraticMap.Equivalent.arf_eq`, `QuadraticMap.arf_prod`,
  `QuadraticMap.arf_pi`, `QuadraticMap.arf_of_isCompl_orthogonal`: isometry invariance and
  orthogonal-sum additivity of `Q.arf`.
* `QuadraticMap.arf_eq_mul_of_polar_eq_one`, `QuadraticMap.arf_linMulLin_fst_snd`,
  `QuadraticMap.arf_sq_comp_fst_add_linMulLin_fst_snd_add_sq_comp_snd`: the Arf invariant of a
  binary form on `ZMod 2 × ZMod 2`, and of the hyperbolic plane `x * y` and the anisotropic plane
  `x ^ 2 + x * y + y ^ 2`.
* `QuadraticMap.two_mul_card_subtype_apply_eq_zero_of_finrank_eq`,
  `QuadraticMap.card_subtype_apply_eq_zero_of_pos_of_finrank_eq`,
  `QuadraticMap.arf_eq_zero_iff_card_subtype_apply_eq_one_lt_card_subtype_apply_eq_zero`: zero-locus
  counts and majority-vote criterion.
* `QuadraticMap.gaussSum_eq_card_mul_gaussSum_lift`, `QuadraticMap.gaussSum_eq_zero_iff`: quotient
  factorization of `Q.gaussSum` along `N ≤ Q.radical` and vanishing when
  `¬Q.polarBilin.ker ≤ Q.radical`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 65, Springer (1972), Chapter III, §1.
* E. H. Brown Jr., *Generalizations of the Kervaire invariant*, Ann. of Math. (2) **95** (1972),
  368--383.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §13.
* A. Pyronneau, *The Arf and Rohklin's invariant* (January 2024), §2.1, Lemmas 2.11--2.12 and
  Corollary 2.14, pp. 4--5.
-/

public section

open TauCeti

/-! ### The Gauss sum of a quadratic form over `ZMod 2` -/

namespace QuadraticMap

section GaussSum

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- The integer Gauss sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of a quadratic form `Q` on a finite
`ZMod 2`-module `V`, counting `Q`-zeros with weight `+1` and `Q`-ones with weight `-1`. -/
def gaussSum [Fintype V] (Q : QuadraticForm (ZMod 2) V) : ℤ :=
  ∑ v : V, (-1 : ℤ) ^ (Q v).val

/-- Unfolds `QuadraticMap.gaussSum`. -/
theorem gaussSum_def [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val :=
  (rfl)

/-- Over `ZMod 2` the trace Gauss sum `QuadraticMap.traceGaussSum` is the Gauss sum
`QuadraticMap.gaussSum`, the absolute trace of `ZMod 2` over itself being the identity. -/
@[simp]
theorem traceGaussSum_eq_gaussSum [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    Q.traceGaussSum = Q.gaussSum := by
  simp [traceGaussSum_def, gaussSum_def]

/-- The Gauss sum is independent of the `Fintype` instance on `V`. -/
@[congr]
theorem gaussSum_congr (Q : QuadraticForm (ZMod 2) V)
    (inst₁ inst₂ : Fintype V) :
    @gaussSum V _ _ inst₁ Q = @gaussSum V _ _ inst₂ Q := by
  rw [Subsingleton.elim inst₁ inst₂]

/-- Isometric quadratic forms over `ZMod 2` have equal Gauss sums. -/
theorem IsometryEquiv.gaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.gaussSum = Q₂.gaussSum := by
  simpa only [traceGaussSum_eq_gaussSum] using e.traceGaussSum_eq

/-- Equivalent quadratic forms over `ZMod 2` have equal Gauss sums. -/
theorem Equivalent.gaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.gaussSum = Q₂.gaussSum := by
  simpa only [traceGaussSum_eq_gaussSum] using h.traceGaussSum_eq

/-- The Gauss sum of the zero quadratic form on `V` is `Fintype.card V`. -/
@[simp]
theorem gaussSum_zero [Fintype V] : (0 : QuadraticForm (ZMod 2) V).gaussSum = Fintype.card V := by
  simpa only [traceGaussSum_eq_gaussSum] using traceGaussSum_zero (k := ZMod 2) (V := V)

/-- On a subsingleton `ZMod 2`-space, every quadratic form has Gauss sum `1`. -/
@[simp]
theorem gaussSum_subsingleton [Fintype V] [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = 1 := by
  simpa only [traceGaussSum_eq_gaussSum] using Q.traceGaussSum_subsingleton

/-- The Gauss sum is multiplicative on orthogonal products. -/
@[simp]
theorem gaussSum_prod [Fintype V₁] [Fintype V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂) :
    (Q₁.prod Q₂).gaussSum = Q₁.gaussSum * Q₂.gaussSum := by
  simpa only [traceGaussSum_eq_gaussSum] using traceGaussSum_prod Q₁ Q₂

/-- The Gauss sum is multiplicative on finite orthogonal sums `QuadraticMap.pi`. -/
@[simp]
theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, Fintype (M i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (M i)) :
    (QuadraticMap.pi Q).gaussSum = ∏ i, (Q i).gaussSum := by
  simpa only [traceGaussSum_eq_gaussSum] using traceGaussSum_pi Q

end GaussSum

end QuadraticMap

namespace TauCeti

/-- Over `ZMod 2`, the binary quadratic form `binaryQuadraticForm (ZMod 2) 1 1`
(`x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2`) is anisotropic. -/
theorem anisotropic_binaryQuadraticForm_one : (binaryQuadraticForm (ZMod 2) 1 1).Anisotropic := by
  rw [anisotropic_binaryQuadraticForm_one_iff]
  intro t
  rcases t.eq_zero_or_eq_one with rfl | rfl <;> decide

/-- On `binaryQuadraticForm (ZMod 2) a b`, the Gauss sum equals `(-1) ^ (a * b).val * 2`. -/
@[simp]
theorem gaussSum_binaryQuadraticForm (a b : ZMod 2) :
    (binaryQuadraticForm (ZMod 2) a b).gaussSum = (-1 : ℤ) ^ (a * b).val * 2 := by
  simpa only [QuadraticMap.traceGaussSum_eq_gaussSum, Algebra.trace_self_apply, ZMod.card,
    Nat.cast_ofNat] using traceGaussSum_binaryQuadraticForm a b

end TauCeti

namespace QuadraticMap

section SymplecticGaussSum

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- In any basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` in which `Q.polarBilin` has matrix
`Matrix.J ι (ZMod 2)`, the Gauss sum of `Q` evaluates to
`(-1) ^ (∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι`. -/
theorem gaussSum_eq_of_toMatrix_polarBilin_eq_J [Fintype V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm (ZMod 2) V)
    {b : Module.Basis (ι ⊕ ι) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.gaussSum =
      (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι := by
  simpa only [traceGaussSum_eq_gaussSum, Algebra.trace_self_apply, ZMod.card, Nat.cast_ofNat] using
    Q.traceGaussSum_eq_of_toMatrix_polarBilin_eq_J hb

/-- **Basis independence of the symplectic-basis Arf sum.** Any two symplectic bases of
`Q.polarBilin` yield the same sum `∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` in `ZMod 2`. -/
theorem sum_mul_eq_of_toMatrix_polarBilin_eq_J
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q : QuadraticForm (ZMod 2) V)
    {b : Module.Basis (ι ⊕ ι) (ZMod 2) V} {c : Module.Basis (κ ⊕ κ) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2))
    (hc : LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J κ (ZMod 2)) :
    ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) =
      ∑ j : κ, Q (c (Sum.inl j)) * Q (c (Sum.inr j)) := by
  simpa only [Algebra.trace_self_apply] using Q.trace_sum_mul_eq_of_toMatrix_polarBilin_eq_J hb hc

end SymplecticGaussSum

/-! ### The Arf invariant -/

section Arf

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- The **Arf invariant** of a quadratic form `Q : QuadraticForm (ZMod 2) V`, taking values in
`ZMod 2`.

When `V` is finite-dimensional and `Q.polarBilin` is nondegenerate, `Q.arf` is the sum
`∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` in any symplectic basis `b` of `Q.polarBilin`
(`QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`). Outside that regime it defaults to `0`. -/
noncomputable def arf (Q : QuadraticForm (ZMod 2) V) : ZMod 2 :=
  open scoped Classical in
  if h : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate then
    letI : FiniteDimensional (ZMod 2) V := h.1
    let spec := Q.exists_basis_toMatrix_polarBilin_eq_J h.2
    let b := spec.choose_spec.choose
    ∑ i : Fin spec.choose, Q (b (Sum.inl i)) * Q (b (Sum.inr i))
  else 0

/-- Over `ZMod 2` the absolute-trace Arf invariant `QuadraticMap.traceArf` is the Arf invariant
`QuadraticMap.arf`, the absolute trace of `ZMod 2` over itself being the identity. -/
@[simp]
theorem traceArf_eq_arf (Q : QuadraticForm (ZMod 2) V) : Q.traceArf = Q.arf := by
  by_cases h : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate
  · obtain ⟨hfd, hnd⟩ := h
    simp only [arf, hfd, hnd, and_self, ↓reduceDIte]
    rw [Q.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J
      (Q.exists_basis_toMatrix_polarBilin_eq_J hnd).choose_spec.choose_spec,
      Algebra.trace_self_apply]
  · rcases not_and_or.mp h with h | h <;> simp [arf, h]

/-- Outside finite dimension, `Q.arf` takes the default value `0`. -/
@[simp]
theorem arf_of_not_finiteDimensional (Q : QuadraticForm (ZMod 2) V)
    (h : ¬FiniteDimensional (ZMod 2) V) : Q.arf = 0 := by
  simpa only [traceArf_eq_arf] using Q.traceArf_of_not_finiteDimensional h

/-- When `Q.polarBilin` is degenerate, `Q.arf` takes the default value `0`. -/
@[simp]
theorem arf_of_not_nondegenerate_polarBilin (Q : QuadraticForm (ZMod 2) V)
    (h : ¬Q.polarBilin.Nondegenerate) : Q.arf = 0 := by
  simpa only [traceArf_eq_arf] using Q.traceArf_of_not_nondegenerate_polarBilin h

/-- If `Q.arf ≠ 0`, then the ambient space `V` is finite-dimensional. -/
theorem finiteDimensional_of_arf_ne_zero {Q : QuadraticForm (ZMod 2) V} (h : Q.arf ≠ 0) :
    FiniteDimensional (ZMod 2) V := by
  by_contra hfd
  exact h (Q.arf_of_not_finiteDimensional hfd)

/-- If `Q.arf ≠ 0`, then `Q.polarBilin` is nondegenerate. -/
theorem nondegenerate_polarBilin_of_arf_ne_zero {Q : QuadraticForm (ZMod 2) V} (h : Q.arf ≠ 0) :
    Q.polarBilin.Nondegenerate := by
  by_contra hnd
  exact h (Q.arf_of_not_nondegenerate_polarBilin hnd)

/-- In any finite basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` putting `Q.polarBilin` in standard
symplectic form `Matrix.J ι (ZMod 2)`, `Q.arf` equals
`∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. -/
theorem arf_eq_sum_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) V) {b : Module.Basis (ι ⊕ ι) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.arf = ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) := by
  simpa only [traceArf_eq_arf, Algebra.trace_self_apply] using
    Q.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb

/-- **Gauss-sum formula for the Arf invariant.** For a quadratic form `Q` on a finite `ZMod 2`-space
`V` of dimension `2 * m` with nondegenerate polar form, `Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem gaussSum_eq_of_finrank_eq [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  simpa only [traceGaussSum_eq_gaussSum, traceArf_eq_arf, ZMod.card, Nat.cast_ofNat] using
    Q.traceGaussSum_eq_of_finrank_eq hQ hdim

/-- **Extracting the Arf invariant from a Gauss sum.** For a quadratic form `Q` on a finite
`ZMod 2`-space `V` of dimension `2 * m` with nondegenerate polar form, if
`Q.gaussSum = (-1) ^ a.val * 2 ^ m`, then `Q.arf = a`. -/
theorem arf_eq_of_gaussSum_eq [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m)
    {a : ZMod 2} (hg : Q.gaussSum = (-1 : ℤ) ^ a.val * 2 ^ m) :
    Q.arf = a := by
  simpa only [traceArf_eq_arf] using Q.traceArf_eq_of_traceGaussSum_eq hQ hdim
    (by simpa only [traceGaussSum_eq_gaussSum, ZMod.card, Nat.cast_ofNat] using hg)

/-- On a subsingleton `ZMod 2`-space, `Q.arf = 0`. -/
@[simp]
theorem arf_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) : Q.arf = 0 := by
  simpa only [traceArf_eq_arf] using Q.traceArf_subsingleton

/-- The Arf invariant of the zero quadratic form vanishes. -/
@[simp]
theorem arf_zero : (0 : QuadraticForm (ZMod 2) V).arf = 0 := by
  simpa only [traceArf_eq_arf] using traceArf_zero (k := ZMod 2) (V := V)

/-- Isometric quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem IsometryEquiv.arf_eq {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.arf = Q₂.arf := by
  simpa only [traceArf_eq_arf] using e.traceArf_eq

/-- Equivalent quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem Equivalent.arf_eq {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.arf = Q₂.arf := by
  simpa only [traceArf_eq_arf] using h.traceArf_eq

/-- **Additivity of the Arf invariant on orthogonal products.** -/
@[simp]
theorem arf_prod [FiniteDimensional (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf := by
  simpa only [traceArf_eq_arf] using traceArf_prod hQ₁ hQ₂

/-- The Arf invariant of `Q.prod Q` vanishes for every quadratic form `Q` over `ZMod 2`. -/
@[simp]
theorem arf_prod_self (Q : QuadraticForm (ZMod 2) V) : (Q.prod Q).arf = 0 := by
  simpa only [traceArf_eq_arf] using Q.traceArf_prod_self

/-- **Additivity of the Arf invariant on finite orthogonal sums.** -/
@[simp]
theorem arf_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    [∀ i, FiniteDimensional (ZMod 2) (M i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i, (Q i).arf := by
  simpa only [traceArf_eq_arf] using traceArf_pi hQ

/-- **Additivity of the Arf invariant across an internal polar-orthogonal decomposition.** -/
theorem arf_of_isCompl_orthogonal [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (W : Submodule (ZMod 2) V)
    (hW : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W)) :
    Q.arf =
      (Q.restrict W).arf + (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).arf := by
  have he := IsometryEquiv.prodRestrictOrthogonal Q W hW
  have hnd_prod :
      ((Q.restrict W).prod
        (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))).polarBilin.Nondegenerate :=
    he.nondegenerate_polarBilin_iff.mpr hQ
  obtain ⟨hndW, hndW'⟩ := nondegenerate_polarBilin_prod_iff.mp hnd_prod
  rw [← he.arf_eq, arf_prod hndW hndW']

end Arf

end QuadraticMap

namespace TauCeti

/-- The Arf invariant of `binaryQuadraticForm (ZMod 2) a b` is `a * b`. -/
@[simp]
theorem arf_binaryQuadraticForm (a b : ZMod 2) :
    (binaryQuadraticForm (ZMod 2) a b).arf = a * b := by
  simpa only [QuadraticMap.traceArf_eq_arf, Algebra.trace_self_apply] using
    traceArf_binaryQuadraticForm a b

end TauCeti

/-! ### Binary forms on `ZMod 2 × ZMod 2` -/

namespace QuadraticMap

/-- **The Arf invariant of a binary form.** A quadratic form on `ZMod 2 × ZMod 2` whose polar form
pairs the standard basis vectors to `1` has Arf invariant `Q (1, 0) * Q (0, 1)`. -/
theorem arf_eq_mul_of_polar_eq_one {Q : QuadraticForm (ZMod 2) (ZMod 2 × ZMod 2)}
    (hQ : polar Q (1, 0) (0, 1) = 1) : Q.arf = Q (1, 0) * Q (0, 1) := by
  let b := (Module.Basis.singleton (Fin 1) (ZMod 2)).prod
    (Module.Basis.singleton (Fin 1) (ZMod 2))
  have hb₁ : b (.inl 0) = (1, 0) := by simp [b]
  have hb₂ : b (.inr 0) = (0, 1) := by simp [b]
  have hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin 1) (ZMod 2) := by
    ext x y
    rw [LinearMap.BilinForm.toMatrix_apply]
    rcases x with x | x <;> rcases y with y | y <;> obtain rfl := Subsingleton.elim x 0 <;>
      obtain rfl := Subsingleton.elim y 0 <;>
      simp [hb₁, hb₂, polar_self, polar_comm Q (0, 1), hQ, Matrix.J,
        (by decide : (2 : ZMod 2) = 0)]
  rw [Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, Fin.sum_univ_one, hb₁, hb₂]

/-- The **hyperbolic plane** `Q (x, y) = x * y` over `ZMod 2` has Arf invariant `0`. -/
@[simp]
theorem arf_linMulLin_fst_snd :
    (linMulLin (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2))
      (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2))).arf = 0 := by
  rw [arf_eq_mul_of_polar_eq_one] <;> simp [polar]

/-- The **anisotropic plane** `Q (x, y) = x ^ 2 + x * y + y ^ 2` over `ZMod 2` has Arf
invariant `1`. -/
@[simp]
theorem arf_sq_comp_fst_add_linMulLin_fst_snd_add_sq_comp_snd :
    (sq.comp (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)) +
      linMulLin (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2))
        (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)) +
      sq.comp (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2))).arf = 1 := by
  rw [arf_eq_mul_of_polar_eq_one] <;> simp [polar]

end QuadraticMap

/-! ### Zero-locus counts, majority vote, and radical/polar-kernel descent of the Gauss sum -/

namespace QuadraticMap

section ZeroCountAndDescent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- On a subsingleton `ZMod 2`-space, `0` is the unique zero of `Q`, so `{v : V // Q v = 0}` has
cardinality `1`. -/
@[simp]
theorem card_subtype_apply_eq_zero_eq_one_of_subsingleton [Subsingleton V]
    (Q : QuadraticForm (ZMod 2) V) :
    Fintype.card {v : V // Q v = 0} = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨0, map_zero Q⟩, fun ⟨v, _⟩ ↦ Subtype.ext (Subsingleton.elim v 0)⟩

private theorem filter_apply_eq_one (Q : QuadraticForm (ZMod 2) V) :
    Finset.filter (fun v : V ↦ Q v = 1) Finset.univ =
      Finset.filter (fun v : V ↦ ¬Q v = 0) Finset.univ := by
  ext v
  simp [ZMod.ne_zero_iff_eq_one]

/-- Every vector of `V` satisfies either `Q v = 0` or `Q v = 1`, partitioning `V`. -/
theorem card_subtype_apply_eq_zero_add_card_subtype_apply_eq_one (Q : QuadraticForm (ZMod 2) V) :
    Fintype.card {v : V // Q v = 0} + Fintype.card {v : V // Q v = 1} = Fintype.card V := by
  rw [Fintype.card_subtype, Fintype.card_subtype, filter_apply_eq_one,
    Finset.card_filter_add_card_filter_not]
  exact Finset.card_univ

private theorem card_subtype_apply_eq_zero_add_card_subtype_apply_eq_one_int
    (Q : QuadraticForm (ZMod 2) V) :
    (Fintype.card {v : V // Q v = 0} : ℤ) + Fintype.card {v : V // Q v = 1} = Fintype.card V := by
  exact_mod_cast Q.card_subtype_apply_eq_zero_add_card_subtype_apply_eq_one

/-- The Gauss sum of `Q` is the difference between the number of `Q`-zeros and `Q`-ones. -/
theorem gaussSum_eq_card_subtype_apply_eq_zero_sub_card_subtype_apply_eq_one
    (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = (Fintype.card {v : V // Q v = 0} : ℤ) - Fintype.card {v : V // Q v = 1} := by
  rw [gaussSum_def, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V ↦ Q v = 0)]
  have h0 : ∑ v ∈ Finset.univ with Q v = 0, (-1 : ℤ) ^ (Q v).val =
      Fintype.card {v : V // Q v = 0} := by
    rw [Fintype.card_subtype]
    have hconst : ∑ v ∈ Finset.univ with Q v = 0, (-1 : ℤ) ^ (Q v).val =
        ∑ _v ∈ Finset.filter (fun v : V ↦ Q v = 0) Finset.univ, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      rw [(Finset.mem_filter.mp hv).2, ZMod.val_zero, pow_zero]
    rw [hconst, Finset.sum_const, nsmul_one]
  have h1 : ∑ v ∈ Finset.univ with ¬Q v = 0, (-1 : ℤ) ^ (Q v).val =
      -(Fintype.card {v : V // Q v = 1} : ℤ) := by
    rw [← filter_apply_eq_one, Fintype.card_subtype]
    have hconst : ∑ v ∈ Finset.univ with Q v = 1, (-1 : ℤ) ^ (Q v).val =
        ∑ _v ∈ Finset.filter (fun v : V ↦ Q v = 1) Finset.univ, (-1 : ℤ) := by
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      rw [(Finset.mem_filter.mp hv).2, ZMod.val_one, pow_one]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  rw [h0, h1, sub_eq_add_neg]

/-- Twice the number of `Q`-zeros equals `Fintype.card V + Q.gaussSum`. -/
theorem two_mul_card_subtype_apply_eq_zero_eq_card_add_gaussSum (Q : QuadraticForm (ZMod 2) V) :
    2 * (Fintype.card {v : V // Q v = 0} : ℤ) = Fintype.card V + Q.gaussSum := by
  have hpart := Q.card_subtype_apply_eq_zero_add_card_subtype_apply_eq_one_int
  have hg := Q.gaussSum_eq_card_subtype_apply_eq_zero_sub_card_subtype_apply_eq_one
  omega

/-- Twice the number of `Q`-ones equals `Fintype.card V - Q.gaussSum`. -/
theorem two_mul_card_subtype_apply_eq_one_eq_card_sub_gaussSum (Q : QuadraticForm (ZMod 2) V) :
    2 * (Fintype.card {v : V // Q v = 1} : ℤ) = Fintype.card V - Q.gaussSum := by
  have hpart := Q.card_subtype_apply_eq_zero_add_card_subtype_apply_eq_one_int
  have h0 := Q.two_mul_card_subtype_apply_eq_zero_eq_card_add_gaussSum
  omega

/-- For `Q` with nondegenerate polar form and `Module.finrank (ZMod 2) V = 2 * m` (`m = 0`
included), `2 * #{v : V | Q v = 0} = 2 ^ (2 * m) + (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem two_mul_card_subtype_apply_eq_zero_of_finrank_eq {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    2 * (Fintype.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m) + (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  rw [Q.two_mul_card_subtype_apply_eq_zero_eq_card_add_gaussSum,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hdim,
    Q.gaussSum_eq_of_finrank_eq hQ hdim, Nat.cast_pow, Nat.cast_ofNat]

/-- For `Q` with nondegenerate polar form and `Module.finrank (ZMod 2) V = 2 * m` (`m = 0`
included), `2 * #{v : V | Q v = 1} = 2 ^ (2 * m) - (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem two_mul_card_subtype_apply_eq_one_of_finrank_eq {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    2 * (Fintype.card {v : V // Q v = 1} : ℤ) =
      2 ^ (2 * m) - (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  have h0 := Q.two_mul_card_subtype_apply_eq_zero_of_finrank_eq hQ hdim
  have hadd := Q.two_mul_card_subtype_apply_eq_zero_eq_card_add_gaussSum
  have hsub := Q.two_mul_card_subtype_apply_eq_one_eq_card_sub_gaussSum
  have hg := Q.gaussSum_eq_of_finrank_eq hQ hdim
  omega

/-- For `0 < m` and `Module.finrank (ZMod 2) V = 2 * m` with `Q.polarBilin` nondegenerate,
`#{v : V | Q v = 0} = 2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)`. -/
theorem card_subtype_apply_eq_zero_of_pos_of_finrank_eq {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 0 < m)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    (Fintype.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  have h2 := Q.two_mul_card_subtype_apply_eq_zero_of_finrank_eq hQ hdim
  rw [← mul_pow_sub_one (by omega : 2 * m ≠ 0) (2 : ℤ),
    ← mul_pow_sub_one hm.ne' (2 : ℤ)] at h2
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  linear_combination h2

/-- For `0 < m` and `Module.finrank (ZMod 2) V = 2 * m` with `Q.polarBilin` nondegenerate,
`#{v : V | Q v = 1} = 2 ^ (2 * m - 1) - (-1) ^ Q.arf.val * 2 ^ (m - 1)`. -/
theorem card_subtype_apply_eq_one_of_pos_of_finrank_eq {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 0 < m)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    (Fintype.card {v : V // Q v = 1} : ℤ) =
      2 ^ (2 * m - 1) - (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  have h0 := Q.card_subtype_apply_eq_zero_of_pos_of_finrank_eq hQ hm hdim
  have h20 := Q.two_mul_card_subtype_apply_eq_zero_of_finrank_eq hQ hdim
  have h21 := Q.two_mul_card_subtype_apply_eq_one_of_finrank_eq hQ hdim
  have hpow : (2 : ℤ) * 2 ^ (2 * m - 1) = 2 ^ (2 * m) :=
    mul_pow_sub_one (by omega : 2 * m ≠ 0) (2 : ℤ)
  omega

/-- A quadratic form over `ZMod 2` with nondegenerate polar form has nonzero Gauss sum. -/
theorem gaussSum_ne_zero_of_nondegenerate_polarBilin {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) : Q.gaussSum ≠ 0 := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  rw [Q.gaussSum_eq_of_finrank_eq hQ (by omega : Module.finrank (ZMod 2) V = 2 * m)]
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))

/-- For `Q` with nondegenerate polar form on a finite `ZMod 2`-space, `Q.arf = 0` if and only if
`0 < Q.gaussSum`. This holds in dimension zero as well. -/
theorem arf_eq_zero_iff_gaussSum_pos {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔ 0 < Q.gaussSum := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  rw [Q.gaussSum_eq_of_finrank_eq hQ (by omega : Module.finrank (ZMod 2) V = 2 * m)]
  have hpow : (0 : ℤ) < 2 ^ m := pow_pos (by decide : (0 : ℤ) < 2) m
  rcases Q.arf.eq_zero_or_eq_one with h0 | h1
  · rw [h0, ZMod.val_zero, pow_zero, one_mul]
    exact ⟨fun _ ↦ hpow, fun _ ↦ rfl⟩
  · rw [h1, ZMod.val_one, pow_one]
    exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h (by omega)⟩

/-- For `Q` with nondegenerate polar form on a finite `ZMod 2`-space, `Q.arf = 1` if and only if
`Q.gaussSum < 0`. -/
theorem arf_eq_one_iff_gaussSum_neg {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 1 ↔ Q.gaussSum < 0 := by
  rw [← ZMod.ne_zero_iff_eq_one, ne_eq, Q.arf_eq_zero_iff_gaussSum_pos hQ, not_lt]
  have hne := Q.gaussSum_ne_zero_of_nondegenerate_polarBilin hQ
  omega

/-- **Majority-vote characterization of `Q.arf = 0`.** A quadratic form `Q` with nondegenerate
polar form on a finite `ZMod 2`-space has `Q.arf = 0` if and only if `Q` vanishes on strictly more
vectors than it takes the value `1`. -/
theorem arf_eq_zero_iff_card_subtype_apply_eq_one_lt_card_subtype_apply_eq_zero
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔ Fintype.card {v : V // Q v = 1} < Fintype.card {v : V // Q v = 0} := by
  rw [Q.arf_eq_zero_iff_gaussSum_pos hQ,
    Q.gaussSum_eq_card_subtype_apply_eq_zero_sub_card_subtype_apply_eq_one]
  omega

/-- **Majority-vote characterization of `Q.arf = 1`.** A quadratic form `Q` with nondegenerate
polar form on a finite `ZMod 2`-space has `Q.arf = 1` if and only if `Q` takes the value `1` on
strictly more vectors than it vanishes on. -/
theorem arf_eq_one_iff_card_subtype_apply_eq_zero_lt_card_subtype_apply_eq_one
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 1 ↔ Fintype.card {v : V // Q v = 0} < Fintype.card {v : V // Q v = 1} := by
  rw [← ZMod.ne_zero_iff_eq_one, ne_eq,
    Q.arf_eq_zero_iff_card_subtype_apply_eq_one_lt_card_subtype_apply_eq_zero hQ, not_lt]
  have hne := Q.gaussSum_ne_zero_of_nondegenerate_polarBilin hQ
  rw [Q.gaussSum_eq_card_subtype_apply_eq_zero_sub_card_subtype_apply_eq_one] at hne
  omega

/-- **Gauss-sum descent across any `N ≤ Q.radical`.** For any submodule `N ≤ Q.radical`, the Gauss
sum of `Q` factors as `Fintype.card N` times the Gauss sum of `Q.lift N hN`. -/
theorem gaussSum_eq_card_mul_gaussSum_lift (Q : QuadraticForm (ZMod 2) V)
    {N : Submodule (ZMod 2) V} (hN : N ≤ Q.radical) [Fintype N] [Fintype (V ⧸ N)] :
    Q.gaussSum = Fintype.card N * (Q.lift N hN).gaussSum := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl N
  let e : N × (V ⧸ N) ≃ V :=
    ((Equiv.refl N).prodCongr (N.quotientEquivOfIsCompl W hW).toEquiv).trans
      (N.prodEquivOfIsCompl W hW).toEquiv
  have he (p : N × (V ⧸ N)) : Q (e p) = Q.lift N hN p.2 := by
    let w : W := N.quotientEquivOfIsCompl W hW p.2
    have hep : e p = (p.1 : V) + (w : V) :=
      Submodule.coe_prodEquivOfIsCompl' (p := N) (q := W) hW (p.1, w)
    have hmk : (Submodule.Quotient.mk (w : V) : V ⧸ N) = p.2 := by simp [w]
    rw [hep, (QuadraticMap.mem_radical_iff'.mp (hN p.1.property)).2, ← hmk, QuadraticMap.lift_mk]
  rw [gaussSum_def, ← Fintype.sum_equiv e (fun p ↦ (-1 : ℤ) ^ (Q.lift N hN p.2).val)
    (fun v ↦ (-1 : ℤ) ^ (Q v).val) (fun p ↦ by rw [he p]),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← gaussSum_def]

/-- **Polar-kernel vanishing of the Gauss sum.** When `Q` does not vanish on `Q.polarBilin.ker`
(equivalently, `¬Q.polarBilin.ker ≤ Q.radical`), `Q.gaussSum = 0`. -/
theorem gaussSum_eq_zero_of_not_ker_polarBilin_le_radical {Q : QuadraticForm (ZMod 2) V}
    (h : ¬Q.polarBilin.ker ≤ Q.radical) : Q.gaussSum = 0 := by
  simp only [ker_polarBilin_le_radical_iff, isTotallyIsotropic_iff, not_forall] at h
  obtain ⟨u, hu, hQu⟩ := h
  have hQu1 : Q u = 1 := ZMod.ne_zero_iff_eq_one.mp hQu
  have hpol (v : V) : polar Q v u = 0 := by
    rw [polar_comm]
    simpa [polarBilin_apply_apply] using LinearMap.congr_fun (LinearMap.mem_ker.mp hu) v
  have hneg : Q.gaussSum = -Q.gaussSum := by
    conv_lhs =>
      rw [gaussSum_def, ← Fintype.sum_equiv (Equiv.addRight u)
        (fun v ↦ (-1 : ℤ) ^ (Q (v + u)).val) (fun v ↦ (-1 : ℤ) ^ (Q v).val) (fun _ ↦ rfl)]
    have hterm (v : V) : (-1 : ℤ) ^ (Q (v + u)).val = -((-1 : ℤ) ^ (Q v).val) := by
      rw [QuadraticMap.map_add Q, hpol v, add_zero, hQu1, ← coe_hilbertSign, hilbertSign_add,
        Units.val_mul, coe_hilbertSign, coe_hilbertSign, ZMod.val_one, pow_one, mul_neg_one]
    simp_rw [hterm, Finset.sum_neg_distrib, ← gaussSum_def]
  omega

/-- The Gauss sum of `Q` vanishes if and only if `¬Q.polarBilin.ker ≤ Q.radical`. -/
theorem gaussSum_eq_zero_iff {Q : QuadraticForm (ZMod 2) V} :
    Q.gaussSum = 0 ↔ ¬Q.polarBilin.ker ≤ Q.radical := by
  refine ⟨fun hg hle ↦ ?_, Q.gaussSum_eq_zero_of_not_ker_polarBilin_le_radical⟩
  let _ : Fintype Q.polarBilin.ker := Fintype.ofFinite _
  let _ : Fintype (V ⧸ Q.polarBilin.ker) := Fintype.ofFinite _
  have hne := (Q.lift Q.polarBilin.ker hle).gaussSum_ne_zero_of_nondegenerate_polarBilin
    (nondegenerate_polarBilin_lift_ker_polarBilin hle)
  rw [Q.gaussSum_eq_card_mul_gaussSum_lift hle] at hg
  exact mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hne hg

end ZeroCountAndDescent

end QuadraticMap
