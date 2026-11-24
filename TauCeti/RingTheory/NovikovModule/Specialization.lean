/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.GradedMatrix
public import TauCeti.RingTheory.NovikovModule.KernelMap

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The cyclic specialization of invariant kernels

Let the generators be a disjoint union `Σ i, P i` of torsors `P i` under a group `H` of periods.
A finite combination of generators is a finitely supported coefficient function `a`. In the lift
coordinates of `TauCeti.NovikovModule.coordinates` it is a vector of Laurent polynomials in the
periods, one for each orbit `i`. Its *orbit sums* `∑ᶠ p : P i, a ⟨i, p⟩`
(`TauCeti.NovikovModule.orbitSum`) add up the coefficients over each orbit. In coordinates this
sends every period monomial `e^h` to `1`. It is the specialization `t ↦ 1` of the finite Laurent
model: it forgets the periods and keeps one coefficient for each orbit.

A kernel `m` from `Σ i, P₁ i` to `Σ k, P₀ k` that is invariant under translating the input and the
output by the same period specializes to a finite matrix, its *cyclic matrix*
(`TauCeti.NovikovModule.cyclicMatrix`). Its `(i, k)` entry is the orbit sum over `P₀ k` of the
output of `m` at any generator of `P₁ i`, which by invariance does not depend on the generator
(`TauCeti.NovikovModule.cyclicMatrix_apply`). When the outputs of `m` are finite combinations,
specialization commutes with the map of `m`: the orbit sums of the image `∑ₚ a(p) m(p, ·)` of a
finite combination `a` are the orbit sums of `a` multiplied by the cyclic matrix
(`TauCeti.NovikovModule.orbitSum_finsum_mul`). Consequently the composite of two kernels
(`TauCeti.NovikovModule.kernelComp`) specializes to the product of their cyclic matrices
(`TauCeti.NovikovModule.cyclicMatrix_kernelComp`), the identity kernel specializes to the identity
matrix, and sums and differences of kernels specialize to sums and differences of matrices.

Gradings descend to the orbits. A degree `d` on generators that is invariant under the periods,
for instance an integer degree read modulo a common multiple of its period shifts, has a value on
each orbit (`TauCeti.NovikovModule.orbitDegree`). A kernel of degree `c`, one with
`m p q ≠ 0 → d₀ q = d₁ p + c`, has a cyclic matrix of degree `c` for these orbit degrees
(`TauCeti.NovikovModule.orbitDegree_eq_of_cyclicMatrix_ne_zero`).

Specialization turns kernel identities into matrix identities. A kernel commuting with two
differentials specializes to a matrix commuting with their cyclic matrices
(`TauCeti.NovikovModule.cyclicMatrix_mul_cyclicMatrix_of_kernelComp_eq`), a kernel homotopy
`m - m' = k δ₀ + δ₁ k` specializes to a matrix homotopy
(`TauCeti.NovikovModule.cyclicMatrix_sub_cyclicMatrix`), in particular kernels inverse to each
other up to homotopy specialize to matrices inverse to each other up to homotopy
(`TauCeti.NovikovModule.cyclicMatrix_mul_cyclicMatrix_sub_one`), and a differential with
`δ ∘ δ = 0` specializes to a matrix squaring to zero
(`TauCeti.NovikovModule.cyclicMatrix_mul_self_eq_zero`).

The invariant kernels with finite outputs and a fixed degree
(`TauCeti.NovikovModule.IsLaurentKernel`) are the homogeneous matrices of the finite Laurent model.
A Laurent differential of degree `1` with `δ ∘ δ = 0` specializes to the *cyclic complex*
(`TauCeti.NovikovModule.cyclicComplex`), with one generator for each orbit, graded by the orbit
degrees, for instance modulo `n` (`TauCeti.NovikovModule.cyclicComplexBasis`,
`TauCeti.NovikovModule.finrank_cyclicComplex_X`), whose differential is given by the rows of the
cyclic matrix of `δ` (`TauCeti.NovikovModule.cyclicComplex_d_basis`). Laurent chain maps
`Φ`, `Ψ` inverse to each other up to Laurent homotopies of degree `-1` specialize to a homotopy
equivalence of cyclic complexes (`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv`), whose maps
are given by the rows of the cyclic matrices of `Φ` and `Ψ`
(`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv_hom_f_basis`,
`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv_inv_f_basis`). Over a field
and with finitely many degrees, the number of orbits on one side is then at least the total
dimension of the homology of the cyclic complex on the other side
(`TauCeti.NovikovModule.sum_finrank_homology_cyclicComplex_le_card`).

In capped Hamiltonian Floer theory on a monotone target the generators are the capped
contractible periodic orbits, `H` is the period group and recapping by `h` shifts the
Conley–Zehnder grading by twice the first Chern number of `h`, so the grading modulo twice the
minimal Chern number `N` is an orbit degree. The differential, continuation maps, PSS maps and their
homotopies are invariant kernels of degrees `1`, `0` and `-1`, with finite outputs because twice the
first Chern number is injective on the period group
(`TauCeti.NovikovModule.finite_support_kernel_of_eq_add`). Their specializations are the finite
cyclic Floer complex graded modulo `2N`, with one generator for each periodic orbit, and its PSS
comparison with the cyclic Morse complex. The rank bound then says that the number of periodic
orbits is at least the total dimension of the homology of the cyclic Morse complex, which the
argument for the Arnold conjecture identifies with the total Betti number of the manifold.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progr. Math. 133 (1995), 483–524.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*,
  IAS/Park City Math. Ser. 7 (1999), 143–229.
-/

public section

noncomputable section

open Function Matrix CategoryTheory

namespace TauCeti

namespace NovikovModule

section OrbitSum

variable {R ι : Type*} [AddCommMonoid R] {P : ι → Type*}

/-- The orbit sums of a coefficient function on a disjoint union `Σ i, P i`: the coefficient of
the index `i` is the sum of the coefficients over `P i`. On finite combinations of the generators
of a disjoint union of torsors, this is the specialization sending every period monomial to `1`. -/
def orbitSum (a : (Σ i, P i) → R) (i : ι) : R :=
  ∑ᶠ p : P i, a ⟨i, p⟩

theorem orbitSum_apply (a : (Σ i, P i) → R) (i : ι) : orbitSum a i = ∑ᶠ p : P i, a ⟨i, p⟩ :=
  (rfl)

/-- The orbit sums of a finite combination add up to the sum of its coefficients. -/
theorem finsum_orbitSum {a : (Σ i, P i) → R} (ha : (support a).Finite) :
    ∑ᶠ i, orbitSum a i = ∑ᶠ x, a x :=
  (finsum_sigma a ha).symm

/-- The orbit sums of a sum of finite combinations are the sums of their orbit sums. -/
theorem orbitSum_add {a b : (Σ i, P i) → R} (ha : (support a).Finite) (hb : (support b).Finite)
    (i : ι) : orbitSum (a + b) i = orbitSum a i + orbitSum b i :=
  finsum_add_distrib (ha.preimage sigma_mk_injective.injOn) (hb.preimage sigma_mk_injective.injOn)

end OrbitSum

section OrbitSumSub

variable {R ι : Type*} [AddCommGroup R] {P : ι → Type*}

/-- The orbit sums of a difference of finite combinations are the differences of their orbit
sums. -/
theorem orbitSum_sub {a b : (Σ i, P i) → R} (ha : (support a).Finite) (hb : (support b).Finite)
    (i : ι) : orbitSum (a - b) i = orbitSum a i - orbitSum b i :=
  finsum_sub_distrib (ha.preimage sigma_mk_injective.injOn) (hb.preimage sigma_mk_injective.injOn)

end OrbitSumSub

section Coordinates

variable {R H ι : Type*} [Semiring R] [AddGroup H] [Finite ι] {P : ι → Type*}
  [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}

/-- **Orbit sums are the specialization `t ↦ 1`.** In lift coordinates, the orbit sum of a
completed combination over `P i` is the sum of all the coefficients of its Novikov series in the
orbit `i`. For a finite combination the series is a Laurent polynomial and this is its value at
`t = 1`. -/
theorem orbitSum_val_eq_finsum_coeff_coordinates
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h) (r : ∀ i, P i)
    (a : NovikovModule R F) (i : ι) :
    orbitSum a.val i = ∑ᶠ h, (coordinates hF r a i).coeff h := by
  rw [orbitSum_apply, ← finsum_comp_equiv (Equiv.vaddConst (r i))]
  simp

end Coordinates

section CyclicMatrix

variable {R ι₁ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*} [∀ i, Nonempty (P₁ i)]

/-- The cyclic matrix of a kernel `m` from `Σ i, P₁ i` to `Σ k, P₀ k`: its `(i, k)` entry is the
orbit sum over `P₀ k` of the output of `m` at a chosen generator of `P₁ i`. For a kernel invariant
under the periods the choice does not matter (`TauCeti.NovikovModule.cyclicMatrix_apply`), and the
cyclic matrix is the specialization `t ↦ 1` of the kernel. -/
def cyclicMatrix [AddCommMonoid R] (m : (Σ i, P₁ i) → (Σ k, P₀ k) → R) : Matrix ι₁ ι₀ R :=
  Matrix.of fun i k ↦ orbitSum (m ⟨i, Classical.arbitrary (P₁ i)⟩) k

@[simp]
theorem cyclicMatrix_zero [AddCommMonoid R] :
    cyclicMatrix (0 : (Σ i, P₁ i) → (Σ k, P₀ k) → R) = 0 := by
  ext i k
  simp [cyclicMatrix, orbitSum]

/-- The cyclic matrix of a sum of kernels with finite outputs is the sum of their cyclic
matrices. -/
theorem cyclicMatrix_add [AddCommMonoid R] {m m' : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
    (hm : ∀ p, (support (m p)).Finite) (hm' : ∀ p, (support (m' p)).Finite) :
    cyclicMatrix (m + m') = cyclicMatrix m + cyclicMatrix m' := by
  ext i k
  exact orbitSum_add (hm _) (hm' _) k

/-- The cyclic matrix of a difference of kernels with finite outputs is the difference of their
cyclic matrices. -/
theorem cyclicMatrix_sub [AddCommGroup R] {m m' : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
    (hm : ∀ p, (support (m p)).Finite) (hm' : ∀ p, (support (m' p)).Finite) :
    cyclicMatrix (m - m') = cyclicMatrix m - cyclicMatrix m' := by
  ext i k
  exact orbitSum_sub (hm _) (hm' _) k

/-- The identity kernel specializes to the identity matrix. -/
@[simp]
theorem cyclicMatrix_one [AddCommMonoidWithOne R] [DecidableEq ι₁] [DecidableEq (Σ i, P₁ i)] :
    cyclicMatrix (fun p q : Σ i, P₁ i ↦ if p = q then (1 : R) else 0) = 1 := by
  ext i k
  rw [cyclicMatrix, of_apply, orbitSum, Matrix.one_apply]
  split_ifs with hik
  · subst hik
    rw [finsum_eq_single _ (Classical.arbitrary (P₁ i)) fun q hq ↦ by simp [Ne.symm hq]]
    simp
  · exact finsum_eq_zero_of_forall_eq_zero fun q ↦ by simp [hik]

end CyclicMatrix

section Invariant

variable {R H ι₁ ι₀ : Type*} [AddCommMonoid R] [AddGroup H] {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]

/-- For a kernel invariant under the periods, the entry `(i, k)` of the cyclic matrix is the
orbit sum over `P₀ k` of the output of `m` at any generator `p` of `P₁ i`. -/
theorem cyclicMatrix_apply {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
    (hminv : ∀ (g : H) i (p : P₁ i) k (q : P₀ k), m ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = m ⟨i, p⟩ ⟨k, q⟩)
    {i : ι₁} (p : P₁ i) (k : ι₀) : cyclicMatrix m i k = orbitSum (m ⟨i, p⟩) k := by
  -- The chosen generator is a translate `g +ᵥ p`; translating the summation over `P₀ k` by `g`
  -- matches the two orbit sums term by term.
  rw [cyclicMatrix, of_apply, orbitSum, orbitSum, ← vsub_vadd (Classical.arbitrary (P₁ i)) p]
  set g := Classical.arbitrary (P₁ i) -ᵥ p
  calc ∑ᶠ q, m ⟨i, g +ᵥ p⟩ ⟨k, q⟩ = ∑ᶠ q, m ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ :=
        (finsum_comp_equiv (AddAction.toPerm g) (f := fun q ↦ m ⟨i, g +ᵥ p⟩ ⟨k, q⟩)).symm
    _ = ∑ᶠ q, m ⟨i, p⟩ ⟨k, q⟩ := finsum_congr fun q ↦ hminv g i p k q

end Invariant

section Torsor

variable {R H ι₁ ι₀ ι₂ : Type*} [Semiring R] [AddGroup H] {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  {P₂ : ι₂ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)] [∀ l, AddTorsor H (P₂ l)]

/-- **Specialization commutes with invariant kernels.** For an invariant kernel `m` with finite
outputs and a finite combination `a`, the orbit sums of the image `∑ₚ a(p) m(p, ·)` are the orbit
sums of `a` multiplied by the cyclic matrix of `m`. -/
theorem orbitSum_finsum_mul {m : (Σ k, P₀ k) → (Σ l, P₂ l) → R}
    (hminv : ∀ (g : H) k (q : P₀ k) l (s : P₂ l), m ⟨k, g +ᵥ q⟩ ⟨l, g +ᵥ s⟩ = m ⟨k, q⟩ ⟨l, s⟩)
    (hmfin : ∀ q, (support (m q)).Finite) {a : (Σ k, P₀ k) → R} (ha : (support a).Finite)
    (l : ι₂) :
    orbitSum (fun s ↦ ∑ᶠ q, a q * m q s) l = ∑ᶠ k, orbitSum a k * cyclicMatrix m k l := by
  have hrow (q : Σ k, P₀ k) : (support fun s : P₂ l ↦ m q ⟨l, s⟩).Finite :=
    (hmfin q).preimage sigma_mk_injective.injOn
  -- Only the finitely many pairs of a generator in the support of `a` and an output of `m` there
  -- contribute.
  have hpair : (support (uncurry fun (s : P₂ l) q ↦ a q * m q ⟨l, s⟩)).Finite :=
    (ha.biUnion fun q _ ↦ (hrow q).image fun s ↦ (s, q)).subset fun ⟨s, q⟩ h ↦
      Set.mem_biUnion (left_ne_zero_of_mul h) ⟨s, right_ne_zero_of_mul h, rfl⟩
  have hfib : (support fun q ↦ a q * cyclicMatrix m q.1 l).Finite :=
    ha.subset fun q h ↦ left_ne_zero_of_mul h
  calc ∑ᶠ s : P₂ l, ∑ᶠ q, a q * m q ⟨l, s⟩
      = ∑ᶠ q, ∑ᶠ s : P₂ l, a q * m q ⟨l, s⟩ := finsum_comm hpair
    _ = ∑ᶠ q, a q * cyclicMatrix m q.1 l := finsum_congr fun q ↦ by
        rw [← mul_finsum' _ _ (hrow q), cyclicMatrix_apply hminv q.2, orbitSum]
    _ = ∑ᶠ k, ∑ᶠ q : P₀ k, a ⟨k, q⟩ * cyclicMatrix m k l := finsum_sigma _ hfib
    _ = ∑ᶠ k, orbitSum a k * cyclicMatrix m k l := finsum_congr fun k ↦
        (finsum_mul' _ _ (ha.preimage sigma_mk_injective.injOn)).symm

/-- **The composite of two kernels specializes to the product of their cyclic matrices**, when
the outputs of both are finite combinations and the second is invariant. -/
theorem cyclicMatrix_kernelComp [Fintype ι₀] {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
    {m' : (Σ k, P₀ k) → (Σ l, P₂ l) → R} (hmfin : ∀ p, (support (m p)).Finite)
    (hm'inv : ∀ (g : H) k (q : P₀ k) l (s : P₂ l), m' ⟨k, g +ᵥ q⟩ ⟨l, g +ᵥ s⟩ = m' ⟨k, q⟩ ⟨l, s⟩)
    (hm'fin : ∀ q, (support (m' q)).Finite) :
    cyclicMatrix (kernelComp m m') = cyclicMatrix m * cyclicMatrix m' := by
  ext i l
  have h := orbitSum_finsum_mul hm'inv hm'fin (hmfin ⟨i, Classical.arbitrary (P₁ i)⟩) l
  simp only [← kernelComp_apply] at h
  rw [Matrix.mul_apply, ← finsum_eq_sum_of_fintype]
  exact h

end Torsor

section Degree

variable {A ι : Type*} {P : ι → Type*}

/-- The degree of the orbit `i` for a degree `d` on generators: its value at a chosen generator of
`P i`. For a degree invariant under the periods the choice does not matter
(`TauCeti.NovikovModule.orbitDegree_apply`). -/
def orbitDegree [∀ i, Nonempty (P i)] (d : (Σ i, P i) → A) (i : ι) : A :=
  d ⟨i, Classical.arbitrary (P i)⟩

variable {H : Type*} [AddGroup H] [∀ i, AddTorsor H (P i)]

/-- An invariant degree takes the value `orbitDegree d i` at every generator of `P i`. -/
theorem orbitDegree_apply {d : (Σ i, P i) → A}
    (hd : ∀ i (g : H) (p : P i), d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩) {i : ι} (p : P i) :
    orbitDegree d i = d ⟨i, p⟩ := by
  rw [orbitDegree, ← vsub_vadd (Classical.arbitrary (P i)) p, hd]

end Degree

section LaurentKernel

variable {R H A ι₁ ι₀ : Type*} [AddGroup H] {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]

/-- A kernel `m` from `Σ i, P₁ i` to `Σ k, P₀ k` is a *Laurent kernel of degree `c`* for degrees
`d₁` and `d₀` on the generators if it is invariant under translating input and output by the same
period, its outputs are finite combinations, and it raises degrees by `c`. These are the
homogeneous matrices of the finite Laurent model. -/
structure IsLaurentKernel [Zero R] [Add A] (d₁ : (Σ i, P₁ i) → A) (d₀ : (Σ k, P₀ k) → A) (c : A)
    (m : (Σ i, P₁ i) → (Σ k, P₀ k) → R) : Prop where
  /-- The kernel is invariant under translating input and output by the same period. -/
  apply_vadd_vadd :
    ∀ (g : H) i (p : P₁ i) k (q : P₀ k), m ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = m ⟨i, p⟩ ⟨k, q⟩
  /-- The outputs of the kernel are finite combinations. -/
  finite_support : ∀ p, (support (m p)).Finite
  /-- The kernel raises degrees by `c`. -/
  degree_eq : ∀ p q, m p q ≠ 0 → d₀ q = d₁ p + c

/-- The identity kernel is a Laurent kernel of degree `0` for every degree on the generators. -/
theorem isLaurentKernel_diagonal_one [Zero R] [One R] [AddZeroClass A] [DecidableEq (Σ i, P₁ i)]
    (d : (Σ i, P₁ i) → A) :
    IsLaurentKernel (H := H) d d 0 fun p q : Σ i, P₁ i ↦ if p = q then (1 : R) else 0 where
  apply_vadd_vadd g i p k q := by
    by_cases hik : i = k
    · subst hik
      have h : ((⟨i, g +ᵥ p⟩ : Σ i, P₁ i) = ⟨i, g +ᵥ q⟩) ↔ ((⟨i, p⟩ : Σ i, P₁ i) = ⟨i, q⟩) := by
        rw [sigma_mk_injective.eq_iff, sigma_mk_injective.eq_iff, vadd_left_cancel_iff]
      simp only [h]
    · have h₁ : (⟨i, g +ᵥ p⟩ : Σ i, P₁ i) ≠ ⟨k, g +ᵥ q⟩ := fun h ↦ hik (congrArg Sigma.fst h)
      have h₂ : (⟨i, p⟩ : Σ i, P₁ i) ≠ ⟨k, q⟩ := fun h ↦ hik (congrArg Sigma.fst h)
      simp [h₁, h₂]
  finite_support := finite_support_diagonal fun _ ↦ 1
  degree_eq p q h := by
    obtain rfl : p = q := by
      by_contra hpq
      simp [hpq] at h
    exact (add_zero _).symm

/-- The cyclic matrix of a Laurent kernel of degree `c` raises the orbit degrees by `c`. -/
theorem orbitDegree_eq_of_cyclicMatrix_ne_zero [AddCommMonoid R] [Add A] {d₁ : (Σ i, P₁ i) → A}
    {d₀ : (Σ k, P₀ k) → A} (hd₀ : ∀ k (g : H) (q : P₀ k), d₀ ⟨k, g +ᵥ q⟩ = d₀ ⟨k, q⟩) {c : A}
    {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R} (hm : ∀ p q, m p q ≠ 0 → d₀ q = d₁ p + c) {i : ι₁}
    {k : ι₀} (h : cyclicMatrix m i k ≠ 0) : orbitDegree d₀ k = orbitDegree d₁ i + c := by
  obtain ⟨q, hq⟩ : ∃ q : P₀ k, m ⟨i, Classical.arbitrary (P₁ i)⟩ ⟨k, q⟩ ≠ 0 :=
    exists_ne_zero_of_finsum_ne_zero h
  rw [orbitDegree_apply hd₀ q, hm _ _ hq, orbitDegree]

end LaurentKernel

section KernelIdentity

variable {R H ι₁ ι₀ : Type*} [AddGroup H] {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)] [Fintype ι₁] [Fintype ι₀]

/-- **Specialization of differentials.** An invariant kernel `δ` with finite outputs and
`δ ∘ δ = 0` as a composite kernel has a cyclic matrix squaring to zero. -/
theorem cyclicMatrix_mul_self_eq_zero [Semiring R] {δ : (Σ i, P₁ i) → (Σ i, P₁ i) → R}
    (hδinv : ∀ (g : H) i (p : P₁ i) k (q : P₁ k), δ ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = δ ⟨i, p⟩ ⟨k, q⟩)
    (hδfin : ∀ p, (support (δ p)).Finite) (hδδ : ∀ p q, kernelComp δ δ p q = 0) :
    cyclicMatrix δ * cyclicMatrix δ = 0 := by
  rw [← cyclicMatrix_kernelComp hδfin hδinv hδfin,
    show kernelComp δ δ = 0 from funext fun p ↦ funext (hδδ p), cyclicMatrix_zero]

/-- **Specialization of chain maps.** If a kernel `Φ` commutes with kernels `δ₁` and `δ₀` as
composite kernels, `δ₁ Φ = Φ δ₀`, then its cyclic matrix commutes with theirs. The outputs of all
three kernels are finite combinations, and `Φ` and `δ₀` are invariant. -/
theorem cyclicMatrix_mul_cyclicMatrix_of_kernelComp_eq [Semiring R]
    {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} {δ₀ : (Σ k, P₀ k) → (Σ k, P₀ k) → R}
    {Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R} (hδ₁fin : ∀ p, (support (δ₁ p)).Finite)
    (hΦinv : ∀ (g : H) i (p : P₁ i) k (q : P₀ k), Φ ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = Φ ⟨i, p⟩ ⟨k, q⟩)
    (hΦfin : ∀ p, (support (Φ p)).Finite)
    (hδ₀inv : ∀ (g : H) k (p : P₀ k) l (q : P₀ l), δ₀ ⟨k, g +ᵥ p⟩ ⟨l, g +ᵥ q⟩ = δ₀ ⟨k, p⟩ ⟨l, q⟩)
    (hδ₀fin : ∀ p, (support (δ₀ p)).Finite)
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q) :
    cyclicMatrix δ₁ * cyclicMatrix Φ = cyclicMatrix Φ * cyclicMatrix δ₀ := by
  rw [← cyclicMatrix_kernelComp hδ₁fin hΦinv hΦfin, ← cyclicMatrix_kernelComp hΦfin hδ₀inv hδ₀fin,
    show kernelComp δ₁ Φ = kernelComp Φ δ₀ from funext fun p ↦ funext (hΦδ p)]

/-- **Specialization of chain homotopies.** If a kernel `k` is a kernel homotopy between kernels
`m` and `m'`, `m - m' = k δ₀ + δ₁ k` as composite kernels, then its cyclic matrix is a homotopy
between their cyclic matrices. The outputs of all five kernels are finite combinations, and `k` and
`δ₀` are invariant. This is the cyclic specialization of
`TauCeti.NovikovModule.kernelMap_sub_kernelMap`. -/
theorem cyclicMatrix_sub_cyclicMatrix [Ring R] {m m' k : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
    {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} {δ₀ : (Σ k, P₀ k) → (Σ k, P₀ k) → R}
    (hmfin : ∀ p, (support (m p)).Finite) (hm'fin : ∀ p, (support (m' p)).Finite)
    (hkinv : ∀ (g : H) i (p : P₁ i) j (q : P₀ j), k ⟨i, g +ᵥ p⟩ ⟨j, g +ᵥ q⟩ = k ⟨i, p⟩ ⟨j, q⟩)
    (hkfin : ∀ p, (support (k p)).Finite) (hδ₁fin : ∀ p, (support (δ₁ p)).Finite)
    (hδ₀inv : ∀ (g : H) k (p : P₀ k) l (q : P₀ l), δ₀ ⟨k, g +ᵥ p⟩ ⟨l, g +ᵥ q⟩ = δ₀ ⟨k, p⟩ ⟨l, q⟩)
    (hδ₀fin : ∀ p, (support (δ₀ p)).Finite)
    (hmk : ∀ p q, m p q - m' p q = kernelComp k δ₀ p q + kernelComp δ₁ k p q) :
    cyclicMatrix m - cyclicMatrix m' =
      cyclicMatrix k * cyclicMatrix δ₀ + cyclicMatrix δ₁ * cyclicMatrix k := by
  rw [← cyclicMatrix_kernelComp hkfin hδ₀inv hδ₀fin, ← cyclicMatrix_kernelComp hδ₁fin hkinv hkfin,
    ← cyclicMatrix_sub hmfin hm'fin,
    ← cyclicMatrix_add (fun p ↦ finite_support_kernelComp (hkfin p) hδ₀fin)
      (fun p ↦ finite_support_kernelComp (hδ₁fin p) hkfin)]
  exact congrArg cyclicMatrix (funext fun p ↦ funext (hmk p))

/-- **Specialization of homotopy inverses.** If kernels `Φ` and `Ψ` are inverse to each other up
to a kernel homotopy `K` for a differential `δ`, `Φ Ψ - 1 = K δ + δ K` as composite kernels, then
their cyclic matrices are inverse to each other up to the homotopy given by the cyclic matrix of
`K`. The outputs of all four kernels are finite combinations, and `Ψ`, `K` and `δ` are
invariant. -/
theorem cyclicMatrix_mul_cyclicMatrix_sub_one [Ring R] [DecidableEq ι₁] [DecidableEq (Σ i, P₁ i)]
    {Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R} {Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R}
    {K δ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} (hΦfin : ∀ p, (support (Φ p)).Finite)
    (hΨinv : ∀ (g : H) k (q : P₀ k) i (p : P₁ i), Ψ ⟨k, g +ᵥ q⟩ ⟨i, g +ᵥ p⟩ = Ψ ⟨k, q⟩ ⟨i, p⟩)
    (hΨfin : ∀ q, (support (Ψ q)).Finite)
    (hKinv : ∀ (g : H) i (p : P₁ i) k (q : P₁ k), K ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = K ⟨i, p⟩ ⟨k, q⟩)
    (hKfin : ∀ p, (support (K p)).Finite)
    (hδinv : ∀ (g : H) i (p : P₁ i) k (q : P₁ k), δ ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = δ ⟨i, p⟩ ⟨k, q⟩)
    (hδfin : ∀ p, (support (δ p)).Finite)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ p q + kernelComp δ K p q) :
    cyclicMatrix Φ * cyclicMatrix Ψ - 1 =
      cyclicMatrix δ * cyclicMatrix K + cyclicMatrix K * cyclicMatrix δ := by
  rw [← cyclicMatrix_kernelComp hΦfin hΨinv hΨfin, ← cyclicMatrix_one (P₁ := P₁), add_comm]
  exact cyclicMatrix_sub_cyclicMatrix (fun p ↦ finite_support_kernelComp (hΦfin p) hΨfin)
    (finite_support_diagonal fun _ ↦ 1) hKinv hKfin hδfin hδinv hδfin hΦΨ

end KernelIdentity

section CyclicComplex

universe u v

variable {R : Type u} [CommRing R] {H A : Type*} [AddGroup H] [AddRightCancelSemigroup A] [One A]
  [DecidableEq A] {ι₁ ι₀ : Type v} [Fintype ι₁] [Fintype ι₀] {P₁ : ι₁ → Type*}
  {P₀ : ι₀ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]

variable (R) in
/-- The *cyclic complex* of a Laurent differential `δ` of degree `1` with `δ ∘ δ = 0`, for a degree
`d` invariant under the periods: the complex of free `R`-modules with one generator for each orbit,
graded by the orbit degrees (`TauCeti.NovikovModule.cyclicComplexBasis`), whose differential is the
cyclic matrix of `δ` (`TauCeti.NovikovModule.cyclicComplex_d_basis`). It is the specialization
`t ↦ 1` of the finite Laurent complex of `δ`. -/
def cyclicComplex (d : (Σ i, P₁ i) → A)
    (hd : ∀ i (g : H) (p : P₁ i), d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩)
    (δ : (Σ i, P₁ i) → (Σ i, P₁ i) → R) (hδ : IsLaurentKernel d d 1 δ)
    (hδδ : ∀ p q, kernelComp δ δ p q = 0) :
    HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.up A) :=
  gradedMatrixComplex (orbitDegree d) (cyclicMatrix δ)
    (fun _ _ h ↦ orbitDegree_eq_of_cyclicMatrix_ne_zero hd hδ.degree_eq h)
    (cyclicMatrix_mul_self_eq_zero hδ.apply_vadd_vadd hδ.finite_support hδδ)

variable {d : (Σ i, P₁ i) → A} {hd : ∀ i (g : H) (p : P₁ i), d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩}
  {δ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} {hδ : IsLaurentKernel d d 1 δ}
  {hδδ : ∀ p q, kernelComp δ δ p q = 0}

variable (R d hd δ hδ hδδ) in
/-- The basis of the term of degree `a` of the cyclic complex given by the orbits of degree `a`. -/
def cyclicComplexBasis (a : A) :
    Module.Basis {i // orbitDegree d i = a} R ((cyclicComplex R d hd δ hδ hδδ).X a) :=
  gradedMatrixComplexBasis _ _ _ _ a

instance (a : A) : Module.Free R ((cyclicComplex R d hd δ hδ hδδ).X a) :=
  Module.Free.of_basis (cyclicComplexBasis R d hd δ hδ hδδ a)

instance (a : A) : Module.Finite R ((cyclicComplex R d hd δ hδ hδδ).X a) :=
  Module.Finite.of_basis (cyclicComplexBasis R d hd δ hδ hδδ a)

/-- The differential of the cyclic complex sends the orbit `i` to `∑ₖ cyclicMatrix δ i k • k`. -/
@[simp]
theorem cyclicComplex_d_basis (a b : A) (i : {i // orbitDegree d i = a}) :
    ((cyclicComplex R d hd δ hδ hδδ).d a b).hom (cyclicComplexBasis R d hd δ hδ hδδ a i) =
      ∑ k : {k // orbitDegree d k = b},
        cyclicMatrix δ i k • cyclicComplexBasis R d hd δ hδ hδδ b k :=
  gradedMatrixComplex_d_basis a b i

/-- The term of degree `a` of the cyclic complex is free on the orbits of degree `a`. -/
theorem finrank_cyclicComplex_X [Nontrivial R] (a : A) :
    Module.finrank R ((cyclicComplex R d hd δ hδ hδδ).X a) =
      Fintype.card {i // orbitDegree d i = a} :=
  Module.finrank_eq_card_basis (cyclicComplexBasis R d hd δ hδ hδδ a)

end CyclicComplex

section CyclicComplexHomotopyEquiv

universe u v

variable {R : Type u} [CommRing R] {H A : Type*} [AddGroup H] [AddGroup A] [One A]
  [DecidableEq A] {ι₁ ι₀ : Type v} [Fintype ι₁] [Fintype ι₀] {P₁ : ι₁ → Type*}
  {P₀ : ι₀ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  [DecidableEq (Σ i, P₁ i)] [DecidableEq (Σ k, P₀ k)] [DecidableEq ι₁] [DecidableEq ι₀]
  {d₁ : (Σ i, P₁ i) → A} {hd₁ : ∀ i (g : H) (p : P₁ i), d₁ ⟨i, g +ᵥ p⟩ = d₁ ⟨i, p⟩}
  {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} {hδ₁ : IsLaurentKernel d₁ d₁ 1 δ₁}
  {hδδ₁ : ∀ p q, kernelComp δ₁ δ₁ p q = 0} {d₀ : (Σ k, P₀ k) → A}
  {hd₀ : ∀ k (g : H) (q : P₀ k), d₀ ⟨k, g +ᵥ q⟩ = d₀ ⟨k, q⟩}
  {δ₀ : (Σ k, P₀ k) → (Σ k, P₀ k) → R} {hδ₀ : IsLaurentKernel d₀ d₀ 1 δ₀}
  {hδδ₀ : ∀ p q, kernelComp δ₀ δ₀ p q = 0}

/-- **The cyclic specialization of a Laurent homotopy equivalence.** Laurent chain maps `Φ` and
`Ψ` of degree `0` between Laurent differentials `δ₁` and `δ₀`, inverse to each other up to Laurent
homotopies `K` and `K'` of degree `-1`, specialize to a homotopy equivalence between the cyclic
complexes of `δ₁` and `δ₀`. Its maps are the chain maps of the cyclic matrices of `Φ` and `Ψ`
(`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv_hom_f_basis`,
`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv_inv_f_basis`). -/
def cyclicComplexHomotopyEquiv (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R)
    (Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R) (K : (Σ i, P₁ i) → (Σ i, P₁ i) → R)
    (K' : (Σ k, P₀ k) → (Σ k, P₀ k) → R) (hΦ : IsLaurentKernel d₁ d₀ 0 Φ)
    (hΨ : IsLaurentKernel d₀ d₁ 0 Ψ) (hK : IsLaurentKernel d₁ d₁ (-1) K)
    (hK' : IsLaurentKernel d₀ d₀ (-1) K')
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q)
    (hΨΦ : ∀ p q, kernelComp Ψ Φ p q - (if p = q then 1 else 0) =
      kernelComp K' δ₀ p q + kernelComp δ₀ K' p q) :
    HomotopyEquiv (cyclicComplex R d₁ hd₁ δ₁ hδ₁ hδδ₁) (cyclicComplex R d₀ hd₀ δ₀ hδ₀ hδδ₀) :=
  gradedMatrixComplexHomotopyEquiv (cyclicMatrix Φ) (cyclicMatrix Ψ)
    (fun _ _ h ↦ (orbitDegree_eq_of_cyclicMatrix_ne_zero hd₀ hΦ.degree_eq h).trans (add_zero _))
    (cyclicMatrix_mul_cyclicMatrix_of_kernelComp_eq hδ₁.finite_support hΦ.apply_vadd_vadd
      hΦ.finite_support hδ₀.apply_vadd_vadd hδ₀.finite_support hΦδ)
    (fun _ _ h ↦ (orbitDegree_eq_of_cyclicMatrix_ne_zero hd₁ hΨ.degree_eq h).trans (add_zero _))
    (cyclicMatrix_mul_cyclicMatrix_of_kernelComp_eq hδ₀.finite_support hΨ.apply_vadd_vadd
      hΨ.finite_support hδ₁.apply_vadd_vadd hδ₁.finite_support hΨδ)
    (cyclicMatrix K)
    (fun _ _ h ↦ by
      rw [orbitDegree_eq_of_cyclicMatrix_ne_zero hd₁ hK.degree_eq h, neg_add_cancel_right])
    (cyclicMatrix_mul_cyclicMatrix_sub_one hΦ.finite_support hΨ.apply_vadd_vadd
      hΨ.finite_support hK.apply_vadd_vadd hK.finite_support hδ₁.apply_vadd_vadd
      hδ₁.finite_support hΦΨ)
    (cyclicMatrix K')
    (fun _ _ h ↦ by
      rw [orbitDegree_eq_of_cyclicMatrix_ne_zero hd₀ hK'.degree_eq h, neg_add_cancel_right])
    (cyclicMatrix_mul_cyclicMatrix_sub_one hΨ.finite_support hΦ.apply_vadd_vadd
      hΦ.finite_support hK'.apply_vadd_vadd hK'.finite_support hδ₀.apply_vadd_vadd
      hδ₀.finite_support hΨΦ)

section Maps

variable {Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R} {Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R}
  {K : (Σ i, P₁ i) → (Σ i, P₁ i) → R} {K' : (Σ k, P₀ k) → (Σ k, P₀ k) → R}
  {hΦ : IsLaurentKernel d₁ d₀ 0 Φ} {hΨ : IsLaurentKernel d₀ d₁ 0 Ψ}
  {hK : IsLaurentKernel d₁ d₁ (-1) K} {hK' : IsLaurentKernel d₀ d₀ (-1) K'}
  {hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q}
  {hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q}
  {hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
    kernelComp K δ₁ p q + kernelComp δ₁ K p q}
  {hΨΦ : ∀ p q, kernelComp Ψ Φ p q - (if p = q then 1 else 0) =
    kernelComp K' δ₀ p q + kernelComp δ₀ K' p q}

/-- The forward map of the cyclic specialization of a Laurent homotopy equivalence sends the orbit
`i` to `∑ₖ cyclicMatrix Φ i k • k`. -/
@[simp]
theorem cyclicComplexHomotopyEquiv_hom_f_basis (a : A) (i : {i // orbitDegree d₁ i = a}) :
    ((cyclicComplexHomotopyEquiv (hδδ₁ := hδδ₁) (hδδ₀ := hδδ₀) Φ Ψ K K' hΦ hΨ hK hK' hΦδ hΨδ hΦΨ
        hΨΦ).hom.f a).hom (cyclicComplexBasis R d₁ hd₁ δ₁ hδ₁ hδδ₁ a i) =
      ∑ k : {k // orbitDegree d₀ k = a},
        cyclicMatrix Φ i k • cyclicComplexBasis R d₀ hd₀ δ₀ hδ₀ hδδ₀ a k := by
  rw [cyclicComplexHomotopyEquiv, gradedMatrixComplexHomotopyEquiv_hom]
  exact gradedMatrixComplexHom_f_basis a i

/-- The backward map of the cyclic specialization of a Laurent homotopy equivalence sends the orbit
`k` to `∑ᵢ cyclicMatrix Ψ k i • i`. -/
@[simp]
theorem cyclicComplexHomotopyEquiv_inv_f_basis (a : A) (k : {k // orbitDegree d₀ k = a}) :
    ((cyclicComplexHomotopyEquiv (hδδ₁ := hδδ₁) (hδδ₀ := hδδ₀) Φ Ψ K K' hΦ hΨ hK hK' hΦδ hΨδ hΦΨ
        hΨΦ).inv.f a).hom (cyclicComplexBasis R d₀ hd₀ δ₀ hδ₀ hδδ₀ a k) =
      ∑ i : {i // orbitDegree d₁ i = a},
        cyclicMatrix Ψ k i • cyclicComplexBasis R d₁ hd₁ δ₁ hδ₁ hδδ₁ a i := by
  rw [cyclicComplexHomotopyEquiv, gradedMatrixComplexHomotopyEquiv_inv]
  exact gradedMatrixComplexHom_f_basis a k

end Maps

end CyclicComplexHomotopyEquiv

section Finrank

universe u v

variable {𝕜 : Type u} [Field 𝕜] {H A : Type*} [AddGroup H] [AddGroup A] [One A] [DecidableEq A]
  [Fintype A] {ι₁ ι₀ : Type v} [Fintype ι₁] [Fintype ι₀] {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)] [DecidableEq (Σ i, P₁ i)]
  [DecidableEq (Σ k, P₀ k)]
  {d₁ : (Σ i, P₁ i) → A} {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → 𝕜} {d₀ : (Σ k, P₀ k) → A}
  {hd₀ : ∀ k (g : H) (q : P₀ k), d₀ ⟨k, g +ᵥ q⟩ = d₀ ⟨k, q⟩}
  {δ₀ : (Σ k, P₀ k) → (Σ k, P₀ k) → 𝕜} {hδ₀ : IsLaurentKernel d₀ d₀ 1 δ₀}
  {hδδ₀ : ∀ p q, kernelComp δ₀ δ₀ p q = 0}

/-- **Counting orbits by the cyclic specialization.** Over a field, with finitely many degrees,
if the finite Laurent complexes of `δ₁` and `δ₀` are homotopy equivalent through Laurent chain maps
and homotopies, then the number of orbits of generators of `δ₁` is at least the total dimension of
the homology of the cyclic complex of `δ₀`. -/
theorem sum_finrank_homology_cyclicComplex_le_card
    (hd₁ : ∀ i (g : H) (p : P₁ i), d₁ ⟨i, g +ᵥ p⟩ = d₁ ⟨i, p⟩) (hδ₁ : IsLaurentKernel d₁ d₁ 1 δ₁)
    (hδδ₁ : ∀ p q, kernelComp δ₁ δ₁ p q = 0) (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → 𝕜)
    (Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → 𝕜) (K : (Σ i, P₁ i) → (Σ i, P₁ i) → 𝕜)
    (K' : (Σ k, P₀ k) → (Σ k, P₀ k) → 𝕜) (hΦ : IsLaurentKernel d₁ d₀ 0 Φ)
    (hΨ : IsLaurentKernel d₀ d₁ 0 Ψ) (hK : IsLaurentKernel d₁ d₁ (-1) K)
    (hK' : IsLaurentKernel d₀ d₀ (-1) K')
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q)
    (hΨΦ : ∀ p q, kernelComp Ψ Φ p q - (if p = q then 1 else 0) =
      kernelComp K' δ₀ p q + kernelComp δ₀ K' p q) :
    ∑ a, Module.finrank 𝕜 ((cyclicComplex 𝕜 d₀ hd₀ δ₀ hδ₀ hδδ₀).homology a) ≤ Fintype.card ι₁ := by
  classical
  exact sum_finrank_homology_le_card_of_homotopyEquiv
    (cyclicComplexHomotopyEquiv (hd₁ := hd₁) (hδ₁ := hδ₁) (hδδ₁ := hδδ₁) Φ Ψ K K' hΦ hΨ hK hK'
      hΦδ hΨδ hΦΨ hΨΦ)

end Finrank

end NovikovModule

end TauCeti
