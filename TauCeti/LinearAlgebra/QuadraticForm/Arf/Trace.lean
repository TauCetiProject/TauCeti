/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.CharTwo
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.AddCharacter.Trace
import TauCeti.Algebra.CharP.Two
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Dimension.Basis
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# The absolute-trace Gauss sum and Arf invariant over a finite field of characteristic two

Let `k` be a finite field of characteristic two, viewed as an algebra over `ZMod 2`. A
finite-dimensional quadratic form `Q` over `k` whose polar form is nondegenerate has a symplectic
basis `(eᵢ, fᵢ)`, and its Arf invariant is the class of `∑ i, Q eᵢ * Q fᵢ` modulo the
Artin--Schreier subgroup `{z ^ 2 + z}` of `k`. Over a finite field this subgroup is exactly the
kernel of the absolute trace `Algebra.trace (ZMod 2) k`, so the Arf invariant is the element
`QuadraticMap.traceArf Q = Tr (∑ i, Q eᵢ * Q fᵢ)` of `ZMod 2`.

Basis independence comes from a Gauss sum, the integer sum
`QuadraticMap.traceGaussSum Q = ∑ v, (-1) ^ Tr (Q v)` of the additive character
`AddChar.traceChar` along `Q`. It is invariant under isometry and multiplicative on orthogonal
sums. On a binary form `a x ^ 2 + x y + b y ^ 2` it evaluates to `(-1) ^ Tr (a b) * #k`: writing
`b = β ^ 2`, the Frobenius invariance of the trace turns the sum over `y` into a character sum
that vanishes unless `x = β`. Decomposing `Q` along a symplectic basis then gives
`Q.traceGaussSum = (-1) ^ Q.traceArf.val * #k ^ m` in dimension `2 * m`, so the invariant is read
off from the Gauss sum.

Over `k = ZMod 2` the trace is the identity, and this development specializes to the Gauss sum
`QuadraticMap.gaussSum` and Arf invariant `QuadraticMap.arf` of
`TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic`, whose basic API is derived from the one here.

## Main definitions

* `QuadraticMap.traceGaussSum`: the integer Gauss sum `∑ v, (-1) ^ (Tr (Q v)).val` of a quadratic
  form over a commutative `ZMod 2`-algebra.
* `QuadraticMap.traceArf`: the absolute-trace Arf invariant in `ZMod 2` (defined as `0` when `V`
  is infinite-dimensional or `Q.polarBilin` is degenerate).

## Main results

* `TauCeti.traceGaussSum_binaryQuadraticForm`: the Gauss sum of `[a, b]` is
  `(-1) ^ (Tr (a * b)).val * #k`.
* `QuadraticMap.trace_sum_mul_eq_of_toMatrix_polarBilin_eq_J`: the absolute trace of the
  symplectic-basis sum is independent of the symplectic basis.
* `QuadraticMap.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J`: `Q.traceArf` is that trace in
  every symplectic basis.
* `QuadraticMap.traceGaussSum_eq_of_finrank_eq`, `QuadraticMap.traceArf_eq_of_traceGaussSum_eq`:
  `Q.traceGaussSum = (-1) ^ Q.traceArf.val * #k ^ m` in dimension `2 * m`, which determines
  `Q.traceArf`.
* `QuadraticMap.IsometryEquiv.traceArf_eq`, `QuadraticMap.traceArf_prod`,
  `QuadraticMap.traceArf_pi`, `TauCeti.traceArf_binaryQuadraticForm`: isometry invariance,
  additivity on orthogonal sums, and the value on binary forms.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* E. H. Brown Jr., *Generalizations of the Kervaire invariant*, Ann. of Math. (2) **95** (1972),
  368--383.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §13.
* B. Calmès, E. Dotto, Y. Harpaz, F. Hebestreit, M. Land, K. Moi, D. Nardin, T. Nikolaus and
  W. Steimle, *Hermitian K-theory for stable ∞-categories III: Grothendieck--Witt groups of
  rings*, arXiv:2009.07225v4, Corollary 2.3.10 and Examples 2.3.13--2.3.14.
-/

public section

open TauCeti

attribute [local instance] charP_two_of_algebra_zmod_two

/-! ### The trace Gauss sum -/

namespace QuadraticMap

section TraceGaussSum

variable {k : Type*} [CommRing k] [Algebra (ZMod 2) k]
  {V V₁ V₂ : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

/-- The integer Gauss sum `∑ v : V, (-1) ^ (Tr (Q v)).val` of a quadratic form `Q` on a finite
module over a commutative `ZMod 2`-algebra `k`, where `Tr` is the absolute trace
`Algebra.trace (ZMod 2) k`. Over `k = ZMod 2` it is `QuadraticMap.gaussSum`. -/
noncomputable def traceGaussSum [Fintype V] (Q : QuadraticForm k V) : ℤ :=
  ∑ v : V, (-1 : ℤ) ^ (Algebra.trace (ZMod 2) k (Q v)).val

/-- Unfolds `QuadraticMap.traceGaussSum`. -/
theorem traceGaussSum_def [Fintype V] (Q : QuadraticForm k V) :
    Q.traceGaussSum = ∑ v : V, (-1 : ℤ) ^ (Algebra.trace (ZMod 2) k (Q v)).val :=
  (rfl)

/-- The trace Gauss sum is independent of the `Fintype` instance on `V`. -/
@[congr]
theorem traceGaussSum_congr (Q : QuadraticForm k V) (inst₁ inst₂ : Fintype V) :
    @traceGaussSum k _ _ V _ _ inst₁ Q = @traceGaussSum k _ _ V _ _ inst₂ Q := by
  rw [Subsingleton.elim inst₁ inst₂]

/-- The trace Gauss sum of the zero quadratic form on `V` is `Fintype.card V`. -/
@[simp]
theorem traceGaussSum_zero [Fintype V] :
    (0 : QuadraticForm k V).traceGaussSum = Fintype.card V := by
  simp [traceGaussSum_def]

/-- On a subsingleton space, every quadratic form has trace Gauss sum `1`. -/
@[simp]
theorem traceGaussSum_subsingleton [Fintype V] [Subsingleton V] (Q : QuadraticForm k V) :
    Q.traceGaussSum = 1 := by
  rw [traceGaussSum_def, Fintype.sum_subsingleton _ (0 : V), map_zero, map_zero, ZMod.val_zero,
    pow_zero]

/-- Isometric quadratic forms have equal trace Gauss sums. -/
theorem IsometryEquiv.traceGaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂} (e : Q₁.IsometryEquiv Q₂) :
    Q₁.traceGaussSum = Q₂.traceGaussSum := by
  rw [traceGaussSum_def, traceGaussSum_def]
  exact Fintype.sum_equiv e.toEquiv _ _ fun v ↦
    congrArg (fun a : k ↦ (-1 : ℤ) ^ (Algebra.trace (ZMod 2) k a).val) (e.map_app v).symm

/-- Equivalent quadratic forms have equal trace Gauss sums. -/
theorem Equivalent.traceGaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂} (h : Q₁.Equivalent Q₂) :
    Q₁.traceGaussSum = Q₂.traceGaussSum := by
  obtain ⟨e⟩ := h
  exact e.traceGaussSum_eq

/-- The trace Gauss sum is multiplicative on orthogonal products. -/
@[simp]
theorem traceGaussSum_prod [Fintype V₁] [Fintype V₂]
    (Q₁ : QuadraticForm k V₁) (Q₂ : QuadraticForm k V₂) :
    (Q₁.prod Q₂).traceGaussSum = Q₁.traceGaussSum * Q₂.traceGaussSum := by
  simp only [traceGaussSum_def, Fintype.sum_prod_type, QuadraticMap.prod_apply, map_add,
    ← coe_hilbertSign, hilbertSign_add, Units.val_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]

/-- The trace Gauss sum is multiplicative on finite orthogonal sums `QuadraticMap.pi`. -/
@[simp]
theorem traceGaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Fintype (M i)]
    (Q : ∀ i, QuadraticForm k (M i)) :
    (QuadraticMap.pi Q).traceGaussSum = ∏ i, (Q i).traceGaussSum := by
  simp_rw [traceGaussSum_def, pi_apply, map_sum, ← coe_hilbertSign, hilbertSign_sum,
    Units.coe_prod]
  exact (Fintype.prod_sum fun i v ↦
    (hilbertSign (Algebra.trace (ZMod 2) k (Q i v)) : ℤ)).symm

end TraceGaussSum

end QuadraticMap

namespace TauCeti

variable {k : Type*} [Field k] [Algebra (ZMod 2) k]

/-- Over a finite field `k` of characteristic two, the trace Gauss sum of the binary form
`binaryQuadraticForm k a b` (`a x ^ 2 + x y + b y ^ 2`) is `(-1) ^ (Tr (a * b)).val * #k`. -/
@[simp]
theorem traceGaussSum_binaryQuadraticForm [Fintype k] (a b : k) :
    (binaryQuadraticForm k a b).traceGaussSum =
      (-1 : ℤ) ^ (Algebra.trace (ZMod 2) k (a * b)).val * Fintype.card k := by
  classical
  let ψ := AddChar.traceChar k (IsPrimitiveRoot.neg_one (R := ℤ) 0 (by decide))
  have hψ (x : k) : (-1 : ℤ) ^ (Algebra.trace (ZMod 2) k x).val = ψ x :=
    (AddChar.traceChar_apply _ x).symm
  -- Write `b = β ^ 2`; then `ψ (b y ^ 2) = ψ (β y)` by Frobenius invariance of the trace.
  set β := (frobeniusEquiv k 2).symm b
  have hβ : β ^ 2 = b := frobeniusEquiv_symm_pow_p k 2 b
  have hterm (x y : k) :
      ψ (a * x ^ 2 + x * y + b * y ^ 2) = ψ (a * x ^ 2) * ψ (y * (x + β)) := by
    rw [← hβ, show β ^ 2 * y ^ 2 = (β * y) ^ 2 by ring, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, AddChar.traceChar_apply_pow, mul_assoc,
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have hinner (x : k) : ∑ y : k, ψ (y * (x + β)) = if x = β then (Fintype.card k : ℤ) else 0 := by
    rw [AddChar.sum_mulShift _ (AddChar.isPrimitive_traceChar _), add_eq_zero_iff_eq_neg,
      CharTwo.neg_eq]
    split_ifs <;> simp
  let e : (Fin 2 → k) ≃ k × k := (LinearEquiv.finTwoArrow k k).toEquiv
  rw [QuadraticMap.traceGaussSum_def,
    Fintype.sum_equiv e _ (fun p : k × k ↦ ψ (a * p.1 ^ 2 + p.1 * p.2 + b * p.2 ^ 2))
      (fun x ↦ by rw [hψ]; congr 1; simp [e, binaryQuadraticForm_apply]),
    Fintype.sum_prod_type]
  simp_rw [hterm, ← Finset.mul_sum, hinner, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, hψ, ← hβ]

end TauCeti

namespace QuadraticMap

section SymplecticTraceGaussSum

variable {k : Type*} [Field k] [Algebra (ZMod 2) k] {V : Type*} [AddCommGroup V] [Module k V]

/-- In any basis `b : Module.Basis (ι ⊕ ι) k V` in which `Q.polarBilin` has matrix `Matrix.J ι k`,
the trace Gauss sum of `Q` is `(-1) ^ (Tr (∑ i, Q (b (inl i)) * Q (b (inr i)))).val` times
`#k ^ Fintype.card ι`. -/
theorem traceGaussSum_eq_of_toMatrix_polarBilin_eq_J [Fintype k] [Fintype V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm k V)
    {b : Module.Basis (ι ⊕ ι) k V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι k) :
    Q.traceGaussSum =
      (-1 : ℤ) ^ (Algebra.trace (ZMod 2) k (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)))).val *
        (Fintype.card k : ℤ) ^ Fintype.card ι := by
  rw [(Q.isometryEquivPiBinaryQuadraticForm b hb).traceGaussSum_eq, traceGaussSum_pi]
  simp only [traceGaussSum_binaryQuadraticForm, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, map_sum, ← coe_hilbertSign, ← Units.coe_prod, hilbertSign_sum]

/-- **Basis independence of the absolute trace of the symplectic-basis sum.** Over a finite field
`k` of characteristic two, any two symplectic bases of `Q.polarBilin` give sums
`∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` with the same absolute trace. The sums themselves
can differ by an element `z ^ 2 + z`. -/
theorem trace_sum_mul_eq_of_toMatrix_polarBilin_eq_J [Finite k]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q : QuadraticForm k V)
    {b : Module.Basis (ι ⊕ ι) k V} {c : Module.Basis (κ ⊕ κ) k V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι k)
    (hc : LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J κ k) :
    Algebra.trace (ZMod 2) k (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))) =
      Algebra.trace (ZMod 2) k (∑ j : κ, Q (c (Sum.inl j)) * Q (c (Sum.inr j))) := by
  let _ : Fintype k := Fintype.ofFinite k
  let _ : Fintype V := Fintype.ofEquiv _ b.equivFun.toEquiv.symm
  have hcard : Fintype.card ι = Fintype.card κ := by
    have hbdim := Module.finrank_eq_two_mul_card_of_basis_sum b
    have hcdim := Module.finrank_eq_two_mul_card_of_basis_sum c
    omega
  refine eq_of_neg_one_pow_val_mul_eq (pow_ne_zero (Fintype.card κ)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card k : ℤ) ≠ 0)) ?_
  conv_lhs => rw [← hcard]
  rw [← Q.traceGaussSum_eq_of_toMatrix_polarBilin_eq_J hb,
    Q.traceGaussSum_eq_of_toMatrix_polarBilin_eq_J hc]

end SymplecticTraceGaussSum

/-! ### The absolute-trace Arf invariant -/

section TraceArf

variable {k : Type*} [Field k] [Algebra (ZMod 2) k]
  {V V₁ V₂ : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

/-- The **absolute-trace Arf invariant** of a quadratic form `Q` over a field `k` of characteristic
two, in `ZMod 2`.

When `V` is finite-dimensional and `Q.polarBilin` is nondegenerate, it is the absolute trace
`Algebra.trace (ZMod 2) k (∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i)))` of the symplectic-basis
sum in a chosen symplectic basis `b` of `Q.polarBilin`; for finite `k` this does not depend on the
choice (`QuadraticMap.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J`). Outside that regime it
is `0`. -/
noncomputable def traceArf (Q : QuadraticForm k V) : ZMod 2 :=
  open scoped Classical in
  if h : FiniteDimensional k V ∧ Q.polarBilin.Nondegenerate then
    letI : FiniteDimensional k V := h.1
    let spec := Q.exists_basis_toMatrix_polarBilin_eq_J h.2
    let b := spec.choose_spec.choose
    Algebra.trace (ZMod 2) k (∑ i : Fin spec.choose, Q (b (Sum.inl i)) * Q (b (Sum.inr i)))
  else 0

/-- Outside finite dimension, `Q.traceArf` takes the default value `0`. -/
@[simp]
theorem traceArf_of_not_finiteDimensional (Q : QuadraticForm k V)
    (h : ¬FiniteDimensional k V) : Q.traceArf = 0 := by
  simp [traceArf, h]

/-- When `Q.polarBilin` is degenerate, `Q.traceArf` takes the default value `0`. -/
@[simp]
theorem traceArf_of_not_nondegenerate_polarBilin (Q : QuadraticForm k V)
    (h : ¬Q.polarBilin.Nondegenerate) : Q.traceArf = 0 := by
  simp [traceArf, h]

/-- On a subsingleton space, `Q.traceArf = 0`. -/
@[simp]
theorem traceArf_subsingleton [Subsingleton V] (Q : QuadraticForm k V) : Q.traceArf = 0 := by
  simp [traceArf, Subsingleton.elim _ (0 : V)]

/-- The absolute-trace Arf invariant of the zero quadratic form vanishes. -/
@[simp]
theorem traceArf_zero : (0 : QuadraticForm k V).traceArf = 0 := by
  simp [traceArf]

/-- Over a finite field `k` of characteristic two, in any finite basis
`b : Module.Basis (ι ⊕ ι) k V` putting `Q.polarBilin` in standard symplectic form, `Q.traceArf`
is the absolute trace of `∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. -/
theorem traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J [Finite k]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm k V)
    {b : Module.Basis (ι ⊕ ι) k V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι k) :
    Q.traceArf = Algebra.trace (ZMod 2) k (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))) := by
  have hfd : FiniteDimensional k V := Module.Finite.of_basis b
  have hnd : Q.polarBilin.Nondegenerate := LinearMap.BilinForm.nondegenerate_of_toMatrix_eq_J hb
  simp only [traceArf, hfd, hnd, and_self, ↓reduceDIte]
  exact Q.trace_sum_mul_eq_of_toMatrix_polarBilin_eq_J
    (Q.exists_basis_toMatrix_polarBilin_eq_J hnd).choose_spec.choose_spec hb

/-- **Gauss-sum formula for the absolute-trace Arf invariant.** For a quadratic form `Q` on a
space `V` of dimension `2 * m` over a finite field `k` of characteristic two, with nondegenerate
polar form, `Q.traceGaussSum = (-1) ^ Q.traceArf.val * #k ^ m`. -/
theorem traceGaussSum_eq_of_finrank_eq [Fintype k] [Fintype V] {Q : QuadraticForm k V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank k V = 2 * m) :
    Q.traceGaussSum = (-1 : ℤ) ^ Q.traceArf.val * (Fintype.card k : ℤ) ^ m := by
  have : FiniteDimensional k V := Module.Finite.of_finite
  obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq hQ hdim
  rw [Q.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb,
    Q.traceGaussSum_eq_of_toMatrix_polarBilin_eq_J hb, Fintype.card_fin]

/-- **Extracting the absolute-trace Arf invariant from a Gauss sum.** For a quadratic form `Q` on a
space `V` of dimension `2 * m` over a finite field `k` of characteristic two, with nondegenerate
polar form, if `Q.traceGaussSum = (-1) ^ a.val * #k ^ m`, then `Q.traceArf = a`. -/
theorem traceArf_eq_of_traceGaussSum_eq [Fintype k] [Fintype V] {Q : QuadraticForm k V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank k V = 2 * m)
    {a : ZMod 2} (hg : Q.traceGaussSum = (-1 : ℤ) ^ a.val * (Fintype.card k : ℤ) ^ m) :
    Q.traceArf = a := by
  rw [Q.traceGaussSum_eq_of_finrank_eq hQ hdim] at hg
  exact eq_of_neg_one_pow_val_mul_eq
    (pow_ne_zero m (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) hg

/-- The sign of the trace Gauss sum is `(-1) ^ Q.traceArf.val`: over a finite field, the trace
Gauss sum of a form with nondegenerate polar form is nonzero and equals `(-1) ^ Q.traceArf.val`
times its absolute value. -/
private theorem traceGaussSum_eq_neg_one_pow_mul_abs [Finite k] [Fintype V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.traceGaussSum ≠ 0 ∧ Q.traceGaussSum = (-1 : ℤ) ^ Q.traceArf.val * |Q.traceGaussSum| := by
  let _ : Fintype k := Fintype.ofFinite k
  have : FiniteDimensional k V := Module.Finite.of_finite
  obtain ⟨m, hdim⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).two_dvd
  rw [Q.traceGaussSum_eq_of_finrank_eq hQ hdim]
  refine ⟨mul_ne_zero (pow_ne_zero _ (by decide))
    (pow_ne_zero m (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)), ?_⟩
  simp [abs_mul, abs_pow]

/-- `Q.traceArf = a` as soon as the trace Gauss sum is `(-1) ^ a.val` times its absolute value. -/
private theorem traceArf_eq_of_traceGaussSum_eq_neg_one_pow_mul_abs [Finite k] [Fintype V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) {a : ZMod 2}
    (hg : Q.traceGaussSum = (-1 : ℤ) ^ a.val * |Q.traceGaussSum|) : Q.traceArf = a :=
  have h := traceGaussSum_eq_neg_one_pow_mul_abs hQ
  eq_of_neg_one_pow_val_mul_eq (abs_ne_zero.mpr h.1) (h.2.symm.trans hg)

/-- Isometric quadratic forms over a finite field of characteristic two have the same
absolute-trace Arf invariant. -/
theorem IsometryEquiv.traceArf_eq [Finite k] {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.traceArf = Q₂.traceArf := by
  by_cases h₁ : FiniteDimensional k V₁ ∧ Q₁.polarBilin.Nondegenerate
  · obtain ⟨_, hnd₁⟩ := h₁
    have : FiniteDimensional k V₂ := Module.Finite.equiv e.toLinearEquiv
    let _ : Fintype V₁ := @Fintype.ofFinite V₁ (Module.finite_of_finite k)
    let _ : Fintype V₂ := @Fintype.ofFinite V₂ (Module.finite_of_finite k)
    refine traceArf_eq_of_traceGaussSum_eq_neg_one_pow_mul_abs hnd₁ ?_
    rw [e.traceGaussSum_eq]
    exact (traceGaussSum_eq_neg_one_pow_mul_abs (e.nondegenerate_polarBilin_iff.mp hnd₁)).2
  · have h₂ : ¬(FiniteDimensional k V₂ ∧ Q₂.polarBilin.Nondegenerate) := by
      rintro ⟨_, hnd₂⟩
      exact h₁ ⟨Module.Finite.equiv e.symm.toLinearEquiv, e.nondegenerate_polarBilin_iff.mpr hnd₂⟩
    simp only [traceArf, h₁, h₂, ↓reduceDIte]

/-- Equivalent quadratic forms over a finite field of characteristic two have the same
absolute-trace Arf invariant. -/
theorem Equivalent.traceArf_eq [Finite k] {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.traceArf = Q₂.traceArf := by
  obtain ⟨e⟩ := h
  exact e.traceArf_eq

/-- **Additivity of the absolute-trace Arf invariant on orthogonal products.** -/
@[simp]
theorem traceArf_prod [Finite k] [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).traceArf = Q₁.traceArf + Q₂.traceArf := by
  let _ : Fintype V₁ := @Fintype.ofFinite V₁ (Module.finite_of_finite k)
  let _ : Fintype V₂ := @Fintype.ofFinite V₂ (Module.finite_of_finite k)
  refine traceArf_eq_of_traceGaussSum_eq_neg_one_pow_mul_abs
    (nondegenerate_polarBilin_prod_iff.mpr ⟨hQ₁, hQ₂⟩) ?_
  have h₁ := (traceGaussSum_eq_neg_one_pow_mul_abs hQ₁).2
  have h₂ := (traceGaussSum_eq_neg_one_pow_mul_abs hQ₂).2
  rw [traceGaussSum_prod, abs_mul, ← coe_hilbertSign, hilbertSign_add, Units.val_mul,
    coe_hilbertSign, coe_hilbertSign]
  linear_combination Q₂.traceGaussSum * h₁ + (-1 : ℤ) ^ Q₁.traceArf.val * |Q₁.traceGaussSum| * h₂

/-- The absolute-trace Arf invariant of `Q.prod Q` vanishes for every quadratic form `Q` over a
finite field of characteristic two. -/
@[simp]
theorem traceArf_prod_self [Finite k] (Q : QuadraticForm k V) : (Q.prod Q).traceArf = 0 := by
  by_cases h : FiniteDimensional k V ∧ Q.polarBilin.Nondegenerate
  · obtain ⟨_, hQ⟩ := h
    rw [traceArf_prod hQ hQ, CharTwo.add_self_eq_zero]
  · have hprod : ¬(FiniteDimensional k (V × V) ∧ (Q.prod Q).polarBilin.Nondegenerate) := by
      rintro ⟨_, hnd⟩
      exact h ⟨Module.Finite.of_surjective (LinearMap.fst k V V) Prod.fst_surjective,
        (nondegenerate_polarBilin_prod_iff.mp hnd).1⟩
    simp only [traceArf, hprod, ↓reduceDIte]

/-- **Additivity of the absolute-trace Arf invariant on finite orthogonal sums.** -/
@[simp]
theorem traceArf_pi [Finite k] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, FiniteDimensional k (M i)]
    {Q : ∀ i, QuadraticForm k (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).traceArf = ∑ i, (Q i).traceArf := by
  classical
  let _ (i : ι) : Fintype (M i) := @Fintype.ofFinite (M i) (Module.finite_of_finite k)
  refine traceArf_eq_of_traceGaussSum_eq_neg_one_pow_mul_abs
    (nondegenerate_polarBilin_pi_iff.mpr hQ) ?_
  rw [traceGaussSum_pi, Finset.abs_prod, ← coe_hilbertSign, hilbertSign_sum, Units.coe_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [coe_hilbertSign]
  exact (traceGaussSum_eq_neg_one_pow_mul_abs (hQ i)).2

end TraceArf

end QuadraticMap

namespace TauCeti

variable {k : Type*} [Field k] [Algebra (ZMod 2) k]

/-- Over a finite field `k` of characteristic two, the absolute-trace Arf invariant of the binary
form `binaryQuadraticForm k a b` is `Tr (a * b)`. In particular the hyperbolic plane
`binaryQuadraticForm k 0 0` has invariant `0`. -/
@[simp]
theorem traceArf_binaryQuadraticForm [Finite k] (a b : k) :
    (binaryQuadraticForm k a b).traceArf = Algebra.trace (ZMod 2) k (a * b) := by
  let _ : Fintype k := Fintype.ofFinite k
  exact (binaryQuadraticForm k a b).traceArf_eq_of_traceGaussSum_eq
    (nondegenerate_polarBilin_binaryQuadraticForm a b) (m := 1) (by simp) (by simp)

end TauCeti
