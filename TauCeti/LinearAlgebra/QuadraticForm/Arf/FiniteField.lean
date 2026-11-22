/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.AddCharacter.Trace
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Dimension.Basis
import TauCeti.RingTheory.Finite.ArtinSchreier

/-!
# The absolute-trace Arf invariant over a finite field of characteristic two

Let `k` be a finite field of characteristic two, viewed as an algebra over `ZMod 2`. A
finite-dimensional quadratic form `Q` over `k` whose polar form is nondegenerate has a symplectic
basis `(eᵢ, fᵢ)`, and its Arf invariant is the class of `∑ i, Q eᵢ * Q fᵢ` modulo the
Artin--Schreier subgroup `{z ^ 2 + z}` of `k`. Over a finite field this subgroup is exactly the
kernel of the absolute trace `Algebra.trace (ZMod 2) k`, so the Arf invariant is the element
`QuadraticMap.traceArf Q = Tr (∑ i, Q eᵢ * Q fᵢ)` of `ZMod 2`. Over `k = ZMod 2` it is the Arf
invariant `QuadraticMap.arf` (`QuadraticMap.traceArf_eq_arf`).

As for `QuadraticMap.arf`, basis independence comes from a Gauss sum, here the integer sum
`QuadraticMap.traceGaussSum Q = ∑ v, (-1) ^ Tr (Q v)` of the additive character
`AddChar.traceChar` along `Q`. On a binary form `a x ^ 2 + x y + b y ^ 2` it evaluates to
`(-1) ^ Tr (a b) * #k`: writing `b = β ^ 2`, the Frobenius invariance of the trace turns the sum
over `y` into a character sum that vanishes unless `x = β`.

The invariant detects quadratic Lagrangians: `Q` vanishes on a subspace of half the dimension of `V`
exactly when `Q.traceArf = 0`. One direction is the Gauss-sum computation for a sum of hyperbolic
planes. For the other, if `aᵢ = Q eᵢ` and `bᵢ = Q fᵢ` with some `a₀ = Q e₀ ≠ 0`, write
`aᵢ = a₀ μᵢ ^ 2` and choose `z ^ 2 + z = ∑ aᵢ bᵢ` by the Artin--Schreier criterion
`TauCeti.exists_sq_add_self_eq_iff_trace_eq_zero`; then the vectors
`∑ Eᵢ eᵢ + t ∑ μᵢ fᵢ` with `∑ μᵢ Eᵢ = t z / a₀` form such a subspace. Applied to an orthogonal
sum, two forms have equal invariants exactly when their orthogonal sum has such a quadratic
Lagrangian.

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
* `QuadraticMap.IsometryEquiv.traceArf_eq`, `QuadraticMap.traceArf_prod`,
  `QuadraticMap.traceArf_pi`, `TauCeti.traceArf_binaryQuadraticForm`: isometry invariance,
  additivity on orthogonal sums, and the value on binary forms.
* `QuadraticMap.traceArf_eq_zero_iff_exists_isTotallyIsotropic`: `Q.traceArf = 0` exactly when
  `Q` vanishes on a subspace of half the dimension.
* `QuadraticMap.traceArf_eq_traceArf_iff_exists_isTotallyIsotropic_prod`,
  `QuadraticMap.trace_sum_mul_eq_iff_exists_isTotallyIsotropic_prod`: two forms have equal
  invariants, equivalently equal absolute traces of their symplectic-basis sums, exactly when
  `Q₁.prod Q₂` vanishes on a subspace of half the dimension of `V₁ × V₂`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §13.
* B. Calmès, E. Dotto, Y. Harpaz, F. Hebestreit, M. Land, K. Moi, D. Nardin, T. Nikolaus and
  W. Steimle, *Hermitian K-theory for stable ∞-categories III: Grothendieck--Witt groups of
  rings*, arXiv:2009.07225v4, Corollary 2.3.10 and Examples 2.3.13--2.3.14.
-/

public section

open TauCeti

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

/-- Over `ZMod 2` the trace Gauss sum is the Gauss sum `QuadraticMap.gaussSum`. -/
@[simp]
theorem traceGaussSum_eq_gaussSum {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    (Q : QuadraticForm (ZMod 2) W) : Q.traceGaussSum = Q.gaussSum := by
  simp [traceGaussSum_def, gaussSum_def]

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
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
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
    haveI : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
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

/-- Over a finite field `k` of characteristic two, in any finite basis
`b : Module.Basis (ι ⊕ ι) k V` putting `Q.polarBilin` in standard symplectic form, `Q.traceArf`
is the absolute trace of `∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. -/
theorem traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J [Finite k]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm k V)
    {b : Module.Basis (ι ⊕ ι) k V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι k) :
    Q.traceArf = Algebra.trace (ZMod 2) k (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))) := by
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  have hfd : FiniteDimensional k V := Module.Finite.of_basis b
  have hnd : Q.polarBilin.Nondegenerate := LinearMap.BilinForm.nondegenerate_of_toMatrix_eq_J hb
  simp only [traceArf, hfd, hnd, and_self, ↓reduceDIte]
  exact Q.trace_sum_mul_eq_of_toMatrix_polarBilin_eq_J
    (Q.exists_basis_toMatrix_polarBilin_eq_J hnd).choose_spec.choose_spec hb

/-- Over `ZMod 2` the absolute-trace Arf invariant is the Arf invariant `QuadraticMap.arf`. -/
@[simp]
theorem traceArf_eq_arf {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W) : Q.traceArf = Q.arf := by
  by_cases h : FiniteDimensional (ZMod 2) W ∧ Q.polarBilin.Nondegenerate
  · obtain ⟨_, hnd⟩ := h
    obtain ⟨m, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hnd
    rw [Q.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb,
      Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, Algebra.trace_self_apply]
  · rcases not_and_or.mp h with h | h <;> simp [h]

/-- **Gauss-sum formula for the absolute-trace Arf invariant.** For a quadratic form `Q` on a
space `V` of dimension `2 * m` over a finite field `k` of characteristic two, with nondegenerate
polar form, `Q.traceGaussSum = (-1) ^ Q.traceArf.val * #k ^ m`. -/
theorem traceGaussSum_eq_of_finrank_eq [Fintype k] [Fintype V] {Q : QuadraticForm k V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank k V = 2 * m) :
    Q.traceGaussSum = (-1 : ℤ) ^ Q.traceArf.val * (Fintype.card k : ℤ) ^ m := by
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
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

/-- Isometric quadratic forms over a finite field of characteristic two have the same
absolute-trace Arf invariant. -/
theorem IsometryEquiv.traceArf_eq [Finite k] {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.traceArf = Q₂.traceArf := by
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  by_cases h₁ : FiniteDimensional k V₁ ∧ Q₁.polarBilin.Nondegenerate
  · obtain ⟨_, hnd₁⟩ := h₁
    have : FiniteDimensional k V₂ := Module.Finite.equiv e.toLinearEquiv
    have hnd₂ : Q₂.polarBilin.Nondegenerate := e.nondegenerate_polarBilin_iff.mp hnd₁
    let _ : Fintype k := Fintype.ofFinite k
    have : Finite V₁ := Module.finite_of_finite k
    have : Finite V₂ := Module.finite_of_finite k
    let _ : Fintype V₁ := Fintype.ofFinite V₁
    let _ : Fintype V₂ := Fintype.ofFinite V₂
    obtain ⟨m, hm⟩ := Q₁.even_finrank_of_nondegenerate_polarBilin hnd₁
    have hdim₁ : Module.finrank k V₁ = 2 * m := by omega
    have hdim₂ : Module.finrank k V₂ = 2 * m := e.toLinearEquiv.finrank_eq.symm.trans hdim₁
    exact Q₁.traceArf_eq_of_traceGaussSum_eq hnd₁ hdim₁
      (e.traceGaussSum_eq.trans (Q₂.traceGaussSum_eq_of_finrank_eq hnd₂ hdim₂))
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
theorem traceArf_prod [Finite k] [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).traceArf = Q₁.traceArf + Q₂.traceArf := by
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  let _ : Fintype k := Fintype.ofFinite k
  have : Finite V₁ := Module.finite_of_finite k
  have : Finite V₂ := Module.finite_of_finite k
  let _ : Fintype V₁ := Fintype.ofFinite V₁
  let _ : Fintype V₂ := Fintype.ofFinite V₂
  obtain ⟨m₁, hm₁⟩ := Q₁.even_finrank_of_nondegenerate_polarBilin hQ₁
  obtain ⟨m₂, hm₂⟩ := Q₂.even_finrank_of_nondegenerate_polarBilin hQ₂
  have hdim₁ : Module.finrank k V₁ = 2 * m₁ := by omega
  have hdim₂ : Module.finrank k V₂ = 2 * m₂ := by omega
  refine (Q₁.prod Q₂).traceArf_eq_of_traceGaussSum_eq
    (nondegenerate_polarBilin_prod_iff.mpr ⟨hQ₁, hQ₂⟩)
    (by rw [Module.finrank_prod, hdim₁, hdim₂, mul_add]) ?_
  rw [traceGaussSum_prod, Q₁.traceGaussSum_eq_of_finrank_eq hQ₁ hdim₁,
    Q₂.traceGaussSum_eq_of_finrank_eq hQ₂ hdim₂]
  simp only [← coe_hilbertSign, hilbertSign_add, Units.val_mul, pow_add]
  ring

/-- **Additivity of the absolute-trace Arf invariant on finite orthogonal sums.** -/
theorem traceArf_pi [Finite k] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, FiniteDimensional k (M i)]
    {Q : ∀ i, QuadraticForm k (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).traceArf = ∑ i, (Q i).traceArf := by
  classical
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  let _ : Fintype k := Fintype.ofFinite k
  have : ∀ i, Finite (M i) := fun i ↦ Module.finite_of_finite k
  let _ : ∀ i, Fintype (M i) := fun i ↦ Fintype.ofFinite (M i)
  have heven (i : ι) : ∃ m : ℕ, Module.finrank k (M i) = 2 * m := by
    obtain ⟨m, hm⟩ := (Q i).even_finrank_of_nondegenerate_polarBilin (hQ i)
    exact ⟨m, by omega⟩
  choose m hdim using heven
  refine (QuadraticMap.pi Q).traceArf_eq_of_traceGaussSum_eq
    (nondegenerate_polarBilin_pi_iff.mpr hQ)
    (by
      rw [Module.finrank_pi_fintype, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ hdim i) ?_
  rw [traceGaussSum_pi]
  calc
    ∏ i, (Q i).traceGaussSum =
        ∏ i, ((-1 : ℤ) ^ ((Q i).traceArf).val * (Fintype.card k : ℤ) ^ m i) :=
      Finset.prod_congr rfl fun i _ ↦ (Q i).traceGaussSum_eq_of_finrank_eq (hQ i) (hdim i)
    _ = (∏ i, (-1 : ℤ) ^ ((Q i).traceArf).val) * ∏ i, (Fintype.card k : ℤ) ^ m i :=
      Finset.prod_mul_distrib
    _ = (-1 : ℤ) ^ (∑ i, (Q i).traceArf).val * (Fintype.card k : ℤ) ^ ∑ i, m i := by
      simp only [← coe_hilbertSign, ← Units.coe_prod, hilbertSign_sum,
        Finset.prod_pow_eq_pow_sum]

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
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  let _ : Fintype k := Fintype.ofFinite k
  exact (binaryQuadraticForm k a b).traceArf_eq_of_traceGaussSum_eq
    (nondegenerate_polarBilin_binaryQuadraticForm a b) (m := 1) (by simp) (by simp)

omit [Algebra (ZMod 2) k] in
/-- The vanishing behind the quadratic Lagrangian of
`TauCeti.exists_isTotallyIsotropic_pi_binaryQuadraticForm_of_trace_eq_zero`: if `a i = a₀ μ i ^ 2`
and `z ^ 2 + z = ∑ i, a i * b i`, then the binary forms `[a i, b i]` vanish in total on the
coordinates `(E i, t μ i)` whenever `∑ i, μ i * E i = t z / a₀`. -/
private theorem sum_binaryQuadraticForm_eq_zero [CharP k 2] {ι : Type*} [Fintype ι]
    {a b μ E : ι → k} {a₀ t z : k} (ha₀ : a₀ ≠ 0) (hμ : ∀ i, a i = a₀ * μ i ^ 2)
    (hz : z ^ 2 + z = ∑ i, a i * b i) (hS : ∑ i, μ i * E i = t * (z / a₀)) :
    ∑ i, (a i * E i ^ 2 + E i * (t * μ i) + b i * (t * μ i) ^ 2) = 0 := by
  have hsq : ∑ i, (μ i * E i) ^ 2 = (t * (z / a₀)) ^ 2 := by
    rw [← CharTwo.sum_sq, hS]
  have hb : ∑ i, b i * μ i ^ 2 = (z ^ 2 + z) / a₀ := by
    rw [hz, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hμ i]
    field_simp
  calc ∑ i, (a i * E i ^ 2 + E i * (t * μ i) + b i * (t * μ i) ^ 2)
      = a₀ * ∑ i, (μ i * E i) ^ 2 + t * ∑ i, μ i * E i + t ^ 2 * ∑ i, b i * μ i ^ 2 := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hμ i]
        ring
    _ = 0 := by
        rw [hsq, hS, hb]
        field_simp
        linear_combination (t ^ 2 * (z ^ 2 + z)) * CharTwo.two_eq_zero (R := k)

/-- The case `a i₀ ≠ 0` of
`TauCeti.exists_isTotallyIsotropic_pi_binaryQuadraticForm_of_trace_eq_zero`. Writing
`a i = a i₀ * μ i ^ 2` and `z ^ 2 + z = ∑ i, a i * b i`, the Lagrangian consists of the vectors
with coordinates `(E i, t μ i)` such that `∑ i, μ i * E i = t z / a i₀`. -/
private theorem exists_isTotallyIsotropic_pi_binaryQuadraticForm_of_ne_zero [Finite k]
    {ι : Type*} [Fintype ι] (a b : ι → k)
    (h : Algebra.trace (ZMod 2) k (∑ i, a i * b i) = 0) {i₀ : ι} (ha₀ : a i₀ ≠ 0) :
    ∃ U : Submodule k (ι → Fin 2 → k),
      (QuadraticMap.pi fun i ↦ binaryQuadraticForm k (a i) (b i)).IsTotallyIsotropic U ∧
        Module.finrank k U = Fintype.card ι := by
  classical
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  set μ : ι → k := fun i ↦ (frobeniusEquiv k 2).symm (a i / a i₀)
  have hμ (i : ι) : a i = a i₀ * μ i ^ 2 := by
    rw [frobeniusEquiv_symm_pow_p]
    field_simp
  have hμ₀ : μ i₀ = 1 := by simp [μ, ha₀]
  obtain ⟨z, hz⟩ := exists_sq_add_self_eq_iff_trace_eq_zero.mpr h
  let g : (ι → k) × k →ₗ[k] (ι → Fin 2 → k) :=
    { toFun := fun p i ↦ ![p.1 i, p.2 * μ i]
      map_add' := fun x y ↦ by ext i j; fin_cases j <;> simp [add_mul]
      map_smul' := fun r x ↦ by ext i j; fin_cases j <;> simp [mul_assoc] }
  let P : (ι → k) × k →ₗ[k] k :=
    (∑ i, μ i • LinearMap.proj i) ∘ₗ LinearMap.fst k (ι → k) k +
      (z / a i₀) • LinearMap.snd k (ι → k) k
  have hP (p : (ι → k) × k) : P p = ∑ i, μ i * p.1 i + z / a i₀ * p.2 := by
    simp [P]
  have hg : Function.Injective g := by
    rintro ⟨E, t⟩ ⟨E', t'⟩ hEt
    have h0 (i : ι) : E i = E' i := by simpa [g] using congrFun (congrFun hEt i) 0
    have h1 : t = t' := by simpa [g, hμ₀] using congrFun (congrFun hEt i₀) 1
    rw [funext h0, h1]
  refine ⟨(LinearMap.ker P).map g, ?_, ?_⟩
  · rw [QuadraticMap.isTotallyIsotropic_iff]
    rintro _ ⟨⟨E, t⟩, hEt, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hP] at hEt
    have hS : ∑ i, μ i * E i = t * (z / a i₀) := by
      linear_combination hEt - t * (z / a i₀) * CharTwo.two_eq_zero (R := k)
    simpa [g, QuadraticMap.pi_apply, binaryQuadraticForm_apply] using
      sum_binaryQuadraticForm_eq_zero ha₀ hμ hz hS
  · -- `P` is onto `k`, so its kernel has codimension one in `(ι → k) × k`.
    have hPsurj : LinearMap.range P = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun c ↦ ⟨(Pi.single i₀ c, 0), ?_⟩
      simp [hP, hμ₀, Pi.single_apply]
    have hrank := P.finrank_range_add_finrank_ker
    rw [hPsurj, finrank_top, Module.finrank_self, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_self] at hrank
    rw [(Submodule.equivMapOfInjective g hg _).symm.finrank_eq]
    omega

/-- **Quadratic Lagrangians of a sum of binary forms.** Over a finite field `k` of characteristic
two, if the absolute trace of `∑ i, a i * b i` vanishes, then the orthogonal sum of the binary
forms `binaryQuadraticForm k (a i) (b i)` vanishes on a subspace of dimension `Fintype.card ι`. -/
theorem exists_isTotallyIsotropic_pi_binaryQuadraticForm_of_trace_eq_zero [Finite k]
    {ι : Type*} [Fintype ι] (a b : ι → k)
    (h : Algebra.trace (ZMod 2) k (∑ i, a i * b i) = 0) :
    ∃ U : Submodule k (ι → Fin 2 → k),
      (QuadraticMap.pi fun i ↦ binaryQuadraticForm k (a i) (b i)).IsTotallyIsotropic U ∧
        Module.finrank k U = Fintype.card ι := by
  by_cases ha : ∃ i₀, a i₀ ≠ 0
  · obtain ⟨i₀, ha₀⟩ := ha
    exact exists_isTotallyIsotropic_pi_binaryQuadraticForm_of_ne_zero a b h ha₀
  -- If every `a i` vanishes, the first coordinates span a quadratic Lagrangian.
  push Not at ha
  let f : (ι → k) →ₗ[k] (ι → Fin 2 → k) :=
    { toFun := fun c i ↦ ![c i, 0]
      map_add' := fun x y ↦ by ext i j; fin_cases j <;> simp
      map_smul' := fun r x ↦ by ext i j; fin_cases j <;> simp }
  have hf : Function.Injective f := fun x y hxy ↦ funext fun i ↦ by
    simpa [f] using congrFun (congrFun hxy i) 0
  refine ⟨LinearMap.range f, ?_, ?_⟩
  · rw [QuadraticMap.isTotallyIsotropic_iff]
    rintro _ ⟨c, rfl⟩
    simp [f, QuadraticMap.pi_apply, binaryQuadraticForm_apply, ha]
  · rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fintype_fun_eq_card]

end TauCeti

namespace QuadraticMap

section Classification

variable {k : Type*} [Field k] [Finite k] [Algebra (ZMod 2) k]
  {V V₁ V₂ : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

/-- **The absolute-trace Arf invariant detects quadratic Lagrangians.** Over a finite field `k` of
characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate polar form has
`Q.traceArf = 0` if and only if `Q` vanishes on a subspace of half the dimension of `V`. -/
theorem traceArf_eq_zero_iff_exists_isTotallyIsotropic [FiniteDimensional k V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.traceArf = 0 ↔
      ∃ U : Submodule k V, Q.IsTotallyIsotropic U ∧
        2 * Module.finrank k U = Module.finrank k V := by
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  obtain ⟨m, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hdim : Module.finrank k V = 2 * m := by
    simpa using Module.finrank_eq_two_mul_card_of_basis_sum b
  constructor
  · intro h
    rw [Q.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb] at h
    obtain ⟨U, hU, hUm⟩ := exists_isTotallyIsotropic_pi_binaryQuadraticForm_of_trace_eq_zero _ _ h
    let e := Q.isometryEquivPiBinaryQuadraticForm b hb
    refine ⟨U.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [isTotallyIsotropic_iff]
      rintro _ ⟨u, hu, rfl⟩
      rw [LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, e.symm.map_app]
      exact hU.apply_eq_zero hu
    · rw [e.symm.toLinearEquiv.finrank_map_eq, hUm, Fintype.card_fin, hdim]
  · rintro ⟨U, hU, hU2⟩
    obtain hequiv :=
      (equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
        hQ hdim).mpr ⟨U, hU, hU2⟩
    have h0 : (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm k 0 0).traceArf = 0 := by
      rw [traceArf_pi fun _ ↦ nondegenerate_polarBilin_binaryQuadraticForm (0 : k) 0]
      simp
    exact hequiv.traceArf_eq.trans h0

/-- **Classification by the absolute-trace Arf invariant.** Over a finite field `k` of
characteristic two, two finite-dimensional quadratic forms with nondegenerate polar forms have the
same absolute-trace Arf invariant if and only if their orthogonal sum `Q₁.prod Q₂` vanishes on a
subspace of half the dimension of `V₁ × V₂`. -/
theorem traceArf_eq_traceArf_iff_exists_isTotallyIsotropic_prod
    [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.traceArf = Q₂.traceArf ↔
      ∃ L : Submodule k (V₁ × V₂), (Q₁.prod Q₂).IsTotallyIsotropic L ∧
        2 * Module.finrank k L = Module.finrank k (V₁ × V₂) := by
  rw [← traceArf_eq_zero_iff_exists_isTotallyIsotropic
      (nondegenerate_polarBilin_prod_iff.mpr ⟨hQ₁, hQ₂⟩),
    traceArf_prod hQ₁ hQ₂, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- **Arf trace classification in symplectic bases.** Let `k` be a finite field of characteristic
two, and let `Q₁`, `Q₂` be quadratic forms with symplectic bases `b₁`, `b₂` of their polar forms,
of `Fintype.card ι` and `Fintype.card κ` pairs. The absolute traces of the symplectic-basis sums
`∑ i, Q₁ (b₁ (Sum.inl i)) * Q₁ (b₁ (Sum.inr i))` and
`∑ j, Q₂ (b₂ (Sum.inl j)) * Q₂ (b₂ (Sum.inr j))` agree if and only if `Q₁.prod Q₂` vanishes on
a subspace `L` with
`2 * Module.finrank k L = Module.finrank k (V₁ × V₂)`. -/
theorem trace_sum_mul_eq_iff_exists_isTotallyIsotropic_prod
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q₁ : QuadraticForm k V₁) (Q₂ : QuadraticForm k V₂)
    {b₁ : Module.Basis (ι ⊕ ι) k V₁} {b₂ : Module.Basis (κ ⊕ κ) k V₂}
    (hb₁ : LinearMap.BilinForm.toMatrix b₁ Q₁.polarBilin = Matrix.J ι k)
    (hb₂ : LinearMap.BilinForm.toMatrix b₂ Q₂.polarBilin = Matrix.J κ k) :
    Algebra.trace (ZMod 2) k (∑ i : ι, Q₁ (b₁ (Sum.inl i)) * Q₁ (b₁ (Sum.inr i))) =
        Algebra.trace (ZMod 2) k (∑ j : κ, Q₂ (b₂ (Sum.inl j)) * Q₂ (b₂ (Sum.inr j))) ↔
      ∃ L : Submodule k (V₁ × V₂), (Q₁.prod Q₂).IsTotallyIsotropic L ∧
        2 * Module.finrank k L = Module.finrank k (V₁ × V₂) := by
  have : FiniteDimensional k V₁ := Module.Finite.of_basis b₁
  have : FiniteDimensional k V₂ := Module.Finite.of_basis b₂
  rw [← Q₁.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb₁,
    ← Q₂.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb₂]
  exact traceArf_eq_traceArf_iff_exists_isTotallyIsotropic_prod
    (LinearMap.BilinForm.nondegenerate_of_toMatrix_eq_J hb₁)
    (LinearMap.BilinForm.nondegenerate_of_toMatrix_eq_J hb₂)

end Classification

end QuadraticMap
