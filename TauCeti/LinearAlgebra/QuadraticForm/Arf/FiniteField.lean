/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Trace
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.Perfect
import TauCeti.Algebra.CharP.Two
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Dimension.Basis
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.RingTheory.Finite.ArtinSchreier

/-!
# Quadratic Lagrangians and the absolute-trace Arf invariant over a finite field

Let `k` be a finite field of characteristic two, viewed as an algebra over `ZMod 2`, and let `Q` be
a finite-dimensional quadratic form over `k` with nondegenerate polar form. The absolute-trace Arf
invariant `QuadraticMap.traceArf` detects quadratic Lagrangians: `Q` vanishes on a subspace of half
the dimension of `V` exactly when `Q.traceArf = 0`. One direction is the Gauss-sum computation for
a sum of hyperbolic planes. For the other, if `aᵢ = Q eᵢ` and `bᵢ = Q fᵢ` in a symplectic basis
with some `a₀ = Q e₀ ≠ 0`, write `aᵢ = a₀ μᵢ ^ 2` and choose `z ^ 2 + z = ∑ aᵢ bᵢ` by the
Artin--Schreier criterion `TauCeti.exists_sq_add_self_eq_iff_trace_eq_zero`; then the vectors
`∑ Eᵢ eᵢ + t ∑ μᵢ fᵢ` with `∑ μᵢ Eᵢ = t z / a₀` form such a subspace. Applied to an orthogonal
sum, two forms have equal invariants exactly when their orthogonal sum has such a quadratic
Lagrangian.

## Main results

* `TauCeti.exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_trace_eq_zero`: an
  orthogonal sum of binary forms `[aᵢ, bᵢ]` with `Tr (∑ aᵢ bᵢ) = 0` has a quadratic Lagrangian.
* `QuadraticMap.traceArf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq`:
  `Q.traceArf = 0` exactly when `Q` vanishes on a subspace of half the dimension.
* `QuadraticMap.traceArf_eq_zero_iff_equivalent_pi_binaryQuadraticForm_zero`,
  `QuadraticMap.traceArf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq`,
  `QuadraticMap.traceArf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq`: equivalently, `Q`
  is a sum of hyperbolic planes, or has a totally isotropic subspace of dimension `m` in dimension
  `2 * m`, or one equal to its own polar orthogonal complement.
* `QuadraticMap.traceArf_eq_traceArf_iff_exists_isTotallyIsotropic_two_mul_finrank_eq_prod`,
  `QuadraticMap.trace_sum_mul_eq_iff_exists_isTotallyIsotropic_two_mul_finrank_eq_prod`: two forms
  have equal invariants, equivalently equal absolute traces of their symplectic-basis sums, exactly
  when `Q₁.prod Q₂` vanishes on a subspace of half the dimension of `V₁ × V₂`.

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

attribute [local instance] charP_two_of_algebra_zmod_two

namespace TauCeti

variable {k : Type*} [Field k] [Algebra (ZMod 2) k]

omit [Algebra (ZMod 2) k] in
/-- The vanishing behind the quadratic Lagrangian of
`TauCeti.exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_trace_eq_zero`: if
`a i = a₀ μ i ^ 2` and `z ^ 2 + z = ∑ i, a i * b i`, then the binary forms `[a i, b i]` vanish in
total on the coordinates `(E i, t μ i)` whenever `∑ i, μ i * E i = t z / a₀`. -/
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
        linear_combination (t ^ 2 * z ^ 2 * a₀⁻¹) * mul_inv_cancel₀ ha₀ +
          (t ^ 2 * (z ^ 2 + z) * a₀⁻¹) * CharTwo.two_eq_zero (R := k)

/-- The case `a i₀ ≠ 0` of
`TauCeti.exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_trace_eq_zero`. Writing
`a i = a i₀ * μ i ^ 2` and `z ^ 2 + z = ∑ i, a i * b i`, the Lagrangian consists of the vectors
with coordinates `(E i, t μ i)` such that `∑ i, μ i * E i = t z / a i₀`. -/
private theorem exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_ne_zero [Finite k]
    {ι : Type*} [Fintype ι] (a b : ι → k)
    (h : Algebra.trace (ZMod 2) k (∑ i, a i * b i) = 0) {i₀ : ι} (ha₀ : a i₀ ≠ 0) :
    ∃ U : Submodule k (ι → Fin 2 → k),
      (QuadraticMap.pi fun i ↦ binaryQuadraticForm k (a i) (b i)).IsTotallyIsotropic U ∧
        Module.finrank k U = Fintype.card ι := by
  classical
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
theorem exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_trace_eq_zero [Finite k]
    {ι : Type*} [Fintype ι] (a b : ι → k)
    (h : Algebra.trace (ZMod 2) k (∑ i, a i * b i) = 0) :
    ∃ U : Submodule k (ι → Fin 2 → k),
      (QuadraticMap.pi fun i ↦ binaryQuadraticForm k (a i) (b i)).IsTotallyIsotropic U ∧
        Module.finrank k U = Fintype.card ι := by
  by_cases ha : ∃ i₀, a i₀ ≠ 0
  · obtain ⟨i₀, ha₀⟩ := ha
    exact exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_ne_zero a b h ha₀
  -- If every `a i` vanishes, the first coordinates span a quadratic Lagrangian.
  push Not at ha
  obtain rfl : a = fun _ ↦ 0 := funext ha
  exact exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_zero_left b

end TauCeti

namespace QuadraticMap

section Classification

variable {k : Type*} [Field k] [Finite k] [Algebra (ZMod 2) k]
  {V V₁ V₂ : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

/-- **The absolute-trace Arf invariant detects quadratic Lagrangians.** Over a finite field `k` of
characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate polar form has
`Q.traceArf = 0` if and only if `Q` vanishes on a subspace of half the dimension of `V`. -/
theorem traceArf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq [FiniteDimensional k V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.traceArf = 0 ↔
      ∃ U : Submodule k V, Q.IsTotallyIsotropic U ∧
        2 * Module.finrank k U = Module.finrank k V := by
  obtain ⟨m, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hdim : Module.finrank k V = 2 * m := by
    simpa using Module.finrank_eq_two_mul_card_of_basis_sum b
  constructor
  · intro h
    rw [Q.traceArf_eq_trace_sum_of_toMatrix_polarBilin_eq_J hb] at h
    obtain ⟨U, hU, hUm⟩ :=
      exists_isTotallyIsotropic_finrank_eq_pi_binaryQuadraticForm_of_trace_eq_zero _ _ h
    let e := Q.isometryEquivPiBinaryQuadraticForm b hb
    exact ⟨_, hU.map_isometryEquiv e.symm, by
      rw [e.symm.toLinearEquiv.finrank_map_eq, hUm, Fintype.card_fin, hdim]⟩
  · rintro ⟨U, hU, hU2⟩
    obtain hequiv :=
      (equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
        hQ hdim).mpr ⟨U, hU, hU2⟩
    have h0 : (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm k 0 0).traceArf = 0 := by
      rw [traceArf_pi fun _ ↦ nondegenerate_polarBilin_binaryQuadraticForm (0 : k) 0]
      simp
    exact hequiv.traceArf_eq.trans h0

/-- **Hyperbolic normal form (`Q.traceArf = 0`).** Over a finite field `k` of characteristic two,
a finite-dimensional quadratic form `Q` of dimension `2 * m` with nondegenerate polar form has
`Q.traceArf = 0` if and only if it is isometric to the orthogonal sum of `m` hyperbolic planes
`binaryQuadraticForm k 0 0`. -/
theorem traceArf_eq_zero_iff_equivalent_pi_binaryQuadraticForm_zero [FiniteDimensional k V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank k V = 2 * m) :
    Q.traceArf = 0 ↔
      Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm k 0 0) := by
  rw [traceArf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq hQ,
    equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq hQ
      hdim]

/-- **Quadratic Lagrangian criterion for `Q.traceArf = 0` (fixed half-dimension `m`).** Over a
finite field `k` of characteristic two, a finite-dimensional quadratic form `Q` of dimension
`2 * m` with nondegenerate polar form has `Q.traceArf = 0` if and only if `V` contains an
`m`-dimensional `Q`-totally-isotropic subspace. -/
theorem traceArf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq [FiniteDimensional k V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank k V = 2 * m) :
    Q.traceArf = 0 ↔
      ∃ U : Submodule k V, Q.IsTotallyIsotropic U ∧ Module.finrank k U = m := by
  rw [traceArf_eq_zero_iff_equivalent_pi_binaryQuadraticForm_zero hQ hdim,
    equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ hdim]

/-- **Quadratic Lagrangian criterion for `Q.traceArf = 0` (self-orthogonal form).** Over a finite
field `k` of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate polar
form has `Q.traceArf = 0` if and only if `V` contains a `Q`-totally-isotropic subspace equal to its
own `Q.polarBilin`-orthogonal complement. -/
theorem traceArf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq [FiniteDimensional k V]
    {Q : QuadraticForm k V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.traceArf = 0 ↔
      ∃ U : Submodule k V,
        Q.IsTotallyIsotropic U ∧ LinearMap.BilinForm.orthogonal Q.polarBilin U = U := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  have hdim : Module.finrank k V = 2 * m := by omega
  rw [traceArf_eq_zero_iff_equivalent_pi_binaryQuadraticForm_zero hQ hdim,
    equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_orthogonal_eq hQ hdim]

/-- **Classification by the absolute-trace Arf invariant.** Over a finite field `k` of
characteristic two, two finite-dimensional quadratic forms with nondegenerate polar forms have the
same absolute-trace Arf invariant if and only if their orthogonal sum `Q₁.prod Q₂` vanishes on a
subspace of half the dimension of `V₁ × V₂`. -/
theorem traceArf_eq_traceArf_iff_exists_isTotallyIsotropic_two_mul_finrank_eq_prod
    [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    {Q₁ : QuadraticForm k V₁} {Q₂ : QuadraticForm k V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.traceArf = Q₂.traceArf ↔
      ∃ L : Submodule k (V₁ × V₂), (Q₁.prod Q₂).IsTotallyIsotropic L ∧
        2 * Module.finrank k L = Module.finrank k (V₁ × V₂) := by
  rw [← traceArf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
      (nondegenerate_polarBilin_prod_iff.mpr ⟨hQ₁, hQ₂⟩),
    traceArf_prod hQ₁ hQ₂, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- **Arf trace classification in symplectic bases.** Let `k` be a finite field of characteristic
two, and let `Q₁`, `Q₂` be quadratic forms with symplectic bases `b₁`, `b₂` of their polar forms,
of `Fintype.card ι` and `Fintype.card κ` pairs. The absolute traces of the symplectic-basis sums
`∑ i, Q₁ (b₁ (Sum.inl i)) * Q₁ (b₁ (Sum.inr i))` and
`∑ j, Q₂ (b₂ (Sum.inl j)) * Q₂ (b₂ (Sum.inr j))` agree if and only if `Q₁.prod Q₂` vanishes on
a subspace `L` with
`2 * Module.finrank k L = Module.finrank k (V₁ × V₂)`. -/
theorem trace_sum_mul_eq_iff_exists_isTotallyIsotropic_two_mul_finrank_eq_prod
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
  exact traceArf_eq_traceArf_iff_exists_isTotallyIsotropic_two_mul_finrank_eq_prod
    (LinearMap.BilinForm.nondegenerate_of_toMatrix_eq_J hb₁)
    (LinearMap.BilinForm.nondegenerate_of_toMatrix_eq_J hb₂)

end Classification

end QuadraticMap
