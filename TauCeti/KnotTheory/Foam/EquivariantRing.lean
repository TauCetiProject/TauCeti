/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.PositiveWeight
public import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FinCases
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The equivariant coefficient ring of `gl(N)` foams and integral graded freeness

In symmetric `gl(N)` foam evaluation and equivariant Khovanov–Rozansky link homology, the ground
ring is the `GL(N)`-equivariant cohomology of a point, realized algebraically as the polynomial
ring `Λ_N = ℤ[e₁, …, e_N]` in `N` elementary symmetric generators where `e_{i+1} = X i` sits in
quantum degree `2(i + 1)`.

This file defines `TauCeti.EquivariantRing N` and its `ℤ`-grading
`TauCeti.EquivariantRing.grading N`:

* `EquivariantRing.grading N` equips `EquivariantRing N` with a `GradedAlgebra` structure
  concentrated in nonnegative even degrees whose degree-zero piece is `ℤ`.
* Under Mathlib's fundamental theorem of symmetric polynomials (`MvPolynomial.esymmAlgEquiv`), a
  symmetric polynomial in `N` variables homogeneous of polynomial degree `m` corresponds to an
  element of `EquivariantRing.grading N (2 * m)`
  (`EquivariantRing.esymmAlgEquiv_symm_mem_grading_iff`).
* Because `ℤ` is a principal ideal domain and every generator of `EquivariantRing N` has strictly
  positive degree, every degree-zero idempotent endomorphism on a finite shifted free module over
  `EquivariantRing N` splits homogeneously
  (`EquivariantRing.exists_homogeneous_splitting_of_idempotent`), its image admits a finite
  homogeneous `EquivariantRing N`-basis (`TauCeti.exists_homogeneous_basis_range_idempotent`), and
  the multiset of basis shifts is uniquely determined
  (`EquivariantRing.multiset_map_eq_of_homogeneous_basis_range_idempotent`).

## Main definitions

* `TauCeti.EquivariantRing`: the polynomial ring `MvPolynomial (Fin N) ℤ`, with `X i` representing
  the `(i + 1)`st elementary symmetric generator `e_{i + 1}`.
* `TauCeti.EquivariantRing.weight`: the integer weight `i ↦ 2 * (i + 1)` on `Fin N`.
* `TauCeti.EquivariantRing.grading`: the `ℤ`-grading on `EquivariantRing N` placing `X i` in degree
  `2 * (i + 1)`.

## Main results

* `TauCeti.EquivariantRing.grading_eq_bot_of_lt_zero`,
  `TauCeti.EquivariantRing.grading_eq_bot_of_odd`,
  `TauCeti.EquivariantRing.grading_zero_eq_range`: `EquivariantRing N` is concentrated in
  nonnegative even degrees and connected over `ℤ`.
* `TauCeti.EquivariantRing.esymmAlgEquiv_symm_mem_grading_iff`: degree-doubling correspondence with
  homogeneous symmetric polynomials in `N` variables.
* `TauCeti.exists_homogeneous_basis_range_idempotent`: the image of any degree-zero idempotent on a
  finite sum of shifted copies of `EquivariantRing N` has a finite homogeneous basis.
* `TauCeti.EquivariantRing.exists_homogeneous_splitting_of_idempotent`: explicit homogeneous
  splitting `π ∘ₗ ι = id`, `ι ∘ₗ π = p` of a degree-zero idempotent over `EquivariantRing N`.
* `TauCeti.EquivariantRing.multiset_map_eq_of_homogeneous_basis_range_idempotent`: uniqueness of the
  multiset of basis shifts.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), 573–651, Section 2.1 and Lemma 3.30.
* M. Khovanov and L.-H. Robert, *Foam evaluation and Kronheimer–Mrowka theories*, Adv. Math. 376
  (2021), 107433.
-/

public section

namespace TauCeti

/-- The `gl(N)` equivariant coefficient ring `Λ_N = ℤ[e₁, …, e_N]`, realized as
`MvPolynomial (Fin N) ℤ` with `MvPolynomial.X i` representing `e_{i + 1}`. -/
abbrev EquivariantRing (N : ℕ) : Type := _root_.MvPolynomial (Fin N) ℤ

namespace EquivariantRing

/-- The quantum degree `2 * (i + 1)` assigned to the generator `X i = e_{i + 1}` of
`EquivariantRing N`. -/
def weight (N : ℕ) (i : Fin N) : ℤ := 2 * ((i : ℕ) + 1 : ℤ)

/-- `weight N i` is `2 * (i + 1)`. -/
@[simp]
theorem weight_apply (N : ℕ) (i : Fin N) : weight N i = 2 * ((i : ℕ) + 1 : ℤ) :=
  (rfl)

/-- Every generator of `EquivariantRing N` has strictly positive quantum degree. -/
theorem weight_pos (N : ℕ) (i : Fin N) : 0 < weight N i := by
  rw [weight_apply]
  omega

/-- Every generator of `EquivariantRing N` has nonnegative quantum degree. -/
theorem weight_nonneg (N : ℕ) (i : Fin N) : 0 ≤ weight N i :=
  (weight_pos N i).le

/-- Every generator of `EquivariantRing N` has even quantum degree. -/
theorem even_weight (N : ℕ) (i : Fin N) : Even (weight N i) :=
  ⟨(i : ℕ) + 1, by rw [weight_apply]; ring⟩

/-- The integral quantum grading on `EquivariantRing N` placing `X i = e_{i + 1}` in degree
`2 * (i + 1)`. -/
def grading (N : ℕ) : ℤ → Submodule ℤ (EquivariantRing N) :=
  _root_.MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N)

/-- `grading N` is the weighted homogeneous submodule family for `weight N`. -/
theorem grading_def (N : ℕ) :
    grading N = _root_.MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N) :=
  (rfl)

/-- Membership in `grading N d` is weighted homogeneity of weight `d` with respect to `weight N`. -/
theorem mem_grading_iff {N : ℕ} {d : ℤ} {f : EquivariantRing N} :
    f ∈ grading N d ↔ f.IsWeightedHomogeneous (weight N) d := by
  rw [grading_def, _root_.MvPolynomial.mem_weightedHomogeneousSubmodule]

/-- The `ℤ`-graded algebra structure on `EquivariantRing N` induced by `grading N`. -/
@[instance_reducible]
noncomputable def gradedAlgebra (N : ℕ) : GradedAlgebra (grading N) :=
  _root_.MvPolynomial.weightedGradedAlgebra ℤ (weight N)

attribute [instance] gradedAlgebra

/-- The degree-`d` component of `f : EquivariantRing N` under `grading N` is its weighted
homogeneous component for `weight N`. -/
@[simp]
theorem coe_decompose_grading (N : ℕ) (f : EquivariantRing N) (d : ℤ) :
    (DirectSum.decompose (grading N) f d : EquivariantRing N) =
      _root_.MvPolynomial.weightedHomogeneousComponent (weight N) d f :=
  _root_.MvPolynomial.weightedDecomposition.decompose'_apply ℤ (weight N) f d

/-- Integer constants lie in degree zero of `EquivariantRing.grading N`. -/
theorem C_mem_grading_zero (N : ℕ) (c : ℤ) : _root_.MvPolynomial.C c ∈ grading N 0 := by
  rw [mem_grading_iff]
  exact _root_.MvPolynomial.isWeightedHomogeneous_C (weight N) c

/-- The variable `X i = e_{i + 1}` is homogeneous of degree `2 * (i + 1)` in `EquivariantRing N`. -/
theorem X_mem_grading (N : ℕ) (i : Fin N) :
    _root_.MvPolynomial.X i ∈ grading N (2 * ((i : ℕ) + 1 : ℤ)) := by
  rw [mem_grading_iff, ← weight_apply]
  exact _root_.MvPolynomial.isWeightedHomogeneous_X ℤ (weight N) i

/-- `EquivariantRing N` vanishes in strictly negative degrees. -/
theorem grading_eq_bot_of_lt_zero (N : ℕ) {d : ℤ} (hd : d < 0) : grading N d = ⊥ := by
  rw [grading_def]
  exact TauCeti.MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_lt_zero ℤ (weight_nonneg N) hd

/-- Every monomial exponent vector `c : Fin N →₀ ℕ` has even quantum weight in `EquivariantRing N`.
-/
theorem even_finsupp_weight (N : ℕ) (c : Fin N →₀ ℕ) : Even (Finsupp.weight (weight N) c) := by
  refine ⟨∑ i ∈ c.support, (c i : ℤ) * ((i : ℕ) + 1 : ℤ), ?_⟩
  simp only [Finsupp.weight_apply, Finsupp.sum, weight_apply, nsmul_eq_mul, ← two_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

/-- Every odd-degree homogeneous piece of `EquivariantRing N` vanishes. -/
theorem grading_eq_bot_of_odd (N : ℕ) {d : ℤ} (hd : Odd d) : grading N d = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hf ↦
    _root_.MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials (mem_grading_iff.mp hf)
      fun c hc ↦ by
        obtain ⟨k, hk⟩ := even_finsupp_weight N c
        obtain ⟨l, hl⟩ := hd
        omega

/-- The degree-zero piece of `EquivariantRing N` is the image of `ℤ`. -/
theorem grading_zero_eq_range (N : ℕ) :
    grading N 0 = LinearMap.range (Algebra.linearMap ℤ (EquivariantRing N)) := by
  rw [grading_def]
  exact TauCeti.MvPolynomial.weightedHomogeneousSubmodule_zero_eq_range ℤ (weight_pos N)

/-- Membership in `grading N (2 * m)` (`m : ℕ`) is equivalent to `ℕ`-weighted homogeneity of weight
`m` for the standard elementary-symmetric weights `i ↦ i + 1`. -/
theorem mem_grading_two_mul_iff {N : ℕ} {m : ℕ} {f : EquivariantRing N} :
    f ∈ grading N (2 * (m : ℤ)) ↔ f.IsWeightedHomogeneous (fun i : Fin N ↦ (i : ℕ) + 1) m := by
  rw [mem_grading_iff]
  have hw_eq : ∀ c : Fin N →₀ ℕ,
      Finsupp.weight (weight N) c = 2 * (Finsupp.weight (fun i : Fin N ↦ (i : ℕ) + 1) c : ℤ) := by
    intro c
    simp only [Finsupp.weight_apply, Finsupp.sum, weight_apply, nsmul_eq_mul, Nat.cast_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    push_cast
    ring
  refine forall_congr' fun c ↦ imp_congr_right fun _ ↦ ?_
  rw [hw_eq c]
  omega

/-- Under the elementary-symmetric algebra equivalence `MvPolynomial.esymmAlgEquiv`, a symmetric
polynomial in `N` variables is homogeneous of polynomial degree `m` if and only if its coordinate
polynomial in `EquivariantRing N` lies in quantum degree `2 * m`. -/
theorem esymmAlgEquiv_symm_mem_grading_iff {σ : Type*} [Fintype σ] {N : ℕ}
    (hn : Fintype.card σ = N) (p : _root_.MvPolynomial.symmetricSubalgebra σ ℤ) (m : ℕ) :
    (_root_.MvPolynomial.esymmAlgEquiv σ ℤ hn).symm p ∈ grading N (2 * (m : ℤ)) ↔
      (p : _root_.MvPolynomial σ ℤ).IsHomogeneous m := by
  rw [mem_grading_two_mul_iff]
  refine ⟨fun hq ↦ ?_, _root_.MvPolynomial.isWeightedHomogeneous_esymmAlgEquiv_symm hn⟩
  have hp_eq : _root_.MvPolynomial.aeval
      (fun i : Fin N ↦ _root_.MvPolynomial.esymm σ ℤ ((i : ℕ) + 1))
      ((_root_.MvPolynomial.esymmAlgEquiv σ ℤ hn).symm p) = (p : _root_.MvPolynomial σ ℤ) := by
    rw [← _root_.MvPolynomial.esymmAlgHom_apply, ← _root_.MvPolynomial.esymmAlgEquiv_apply σ ℤ hn,
      AlgEquiv.apply_symm_apply]
  rw [← hp_eq]
  exact hq.aeval fun i ↦ _root_.MvPolynomial.isHomogeneous_esymm ((i : ℕ) + 1)

/-- Any degree-zero idempotent on a finite shifted free module `I → EquivariantRing N` splits
homogeneously through some `Fin n → EquivariantRing N` via maps `ι` and `π` satisfying
`π ∘ₗ ι = id` and `ι ∘ₗ π = p`. -/
theorem exists_homogeneous_splitting_of_idempotent (N : ℕ) {I : Type*} [Finite I] (s : I → ℤ)
    (p : (I → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → EquivariantRing N),
      (∀ j, v j ∈ grading N (d - s j)) → ∀ j, p v j ∈ grading N (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N))
      (π : (I → EquivariantRing N) →ₗ[EquivariantRing N] (Fin n → EquivariantRing N)),
      π.comp ι = LinearMap.id ∧
      ι.comp π = p ∧
      (∀ (q : ℤ) (u : Fin n → EquivariantRing N),
        (∀ i, u i ∈ grading N (q - d i)) → ∀ j, ι u j ∈ grading N (q - s j)) ∧
      (∀ (q : ℤ) (v : I → EquivariantRing N),
        (∀ j, v j ∈ grading N (q - s j)) → ∀ i, π v i ∈ grading N (q - d i)) := by
  simp only [grading_def] at hhom ⊢
  exact TauCeti.MvPolynomial.exists_weightedHomogeneous_splitting_of_idempotent
    (weight_pos N) s p hp hhom

/-- Any two finite homogeneous bases of the range of a degree-zero endomorphism on
`I → EquivariantRing N` (`[Finite I]`) have the same multiset of basis shifts. -/
theorem multiset_map_eq_of_homogeneous_basis_range_idempotent (N : ℕ) {I : Type*} [Finite I]
    (s : I → ℤ)
    (p : (I → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N))
    (hhom : ∀ (d : ℤ) (v : I → EquivariantRing N),
      (∀ j, v j ∈ grading N (d - s j)) → ∀ j, p v j ∈ grading N (d - s j))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) (EquivariantRing N) (LinearMap.range p)) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ grading N (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) (EquivariantRing N) (LinearMap.range p)) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ grading N (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val := by
  simp only [grading_def] at hhom hb₁ hb₂
  exact TauCeti.MvPolynomial.multiset_map_eq_of_weightedHomogeneous_basis_range_idempotent
    (weight_pos N) s p hhom b₁ d₁ hb₁ b₂ d₂ hb₂

/-- Any finite homogeneous basis of the range of a rank-one homogeneous projection
`p v = v i₀ • w` (`w i₀ = 1`, `∀ j, w j ∈ grading N (s i₀ - s j)`) on `I → EquivariantRing N` has
degree multiset `{s i₀}`. -/
theorem multiset_map_eq_singleton_of_homogeneous_basis_range
    (N : ℕ) {I : Type*} [Finite I] (s : I → ℤ)
    {p : (I → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N)}
    (i₀ : I) {w : I → EquivariantRing N}
    (hp : ∀ v, p v = v i₀ • w) (hw₀ : w i₀ = 1) (hw : ∀ j, w j ∈ grading N (s i₀ - s j))
    {n : ℕ} (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
    (d : Fin n → ℤ) (hb : ∀ i j, (b i).val j ∈ grading N (d i - s j)) :
    Multiset.map d Finset.univ.val = {s i₀} :=
  TauCeti.multiset_map_eq_singleton_of_homogeneous_basis_range
    (fun _ hm ↦ grading_eq_bot_of_lt_zero N hm)
    (fun _ ha ↦ grading_zero_eq_range N ▸ ha) s i₀ hp hw₀ hw b d hb

end EquivariantRing

/-- **Integral homogeneous basis of an idempotent image over `EquivariantRing N`.**
Every degree-zero idempotent `EquivariantRing N`-linear endomorphism `p` on a finite sum of shifted
copies of `EquivariantRing N` (where the `j`th summand has shift `s j`) has a finite
`EquivariantRing N`-basis `b` of `LinearMap.range p` consisting of homogeneous vectors of degrees
`d i`, meaning `(b i).val j ∈ EquivariantRing.grading N (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
      (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  simp only [EquivariantRing.grading_def] at hhom ⊢
  exact TauCeti.MvPolynomial.exists_weightedHomogeneous_basis_range_idempotent
    (EquivariantRing.weight_pos N) s p hp hhom

section ConcreteVerifications

-- Zero idempotent: the homogeneous basis produced has rank 0.
private theorem exists_homogeneous_basis_zero_rank (N m : ℕ) (s : Fin m → ℤ) :
    ∃ (b : Module.Basis (Fin 0) (EquivariantRing N)
        (LinearMap.range
          (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))))
      (d : Fin 0 → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N m s 0 (by ext; simp)
    (fun _ _ _ _ ↦ Submodule.zero_mem _)
  obtain rfl : n = 0 := eq_zero_of_basis_range_zero b
  exact ⟨b, d, hb⟩

-- Identity on a single summand of shift 3: every homogeneous basis has degree multiset {3}.
private theorem id_shift_three_degree (N : ℕ) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (LinearMap.id :
          (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 1 → EquivariantRing N))))
      (d : Fin n → ℤ),
      (∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - (fun _ ↦ 3) j)) ∧
      Multiset.map d Finset.univ.val = {3} := by
  have hw : ∀ j : Fin 1, (fun _ : Fin 1 ↦ (1 : EquivariantRing N)) j ∈
      EquivariantRing.grading N (3 - 3) := fun _ ↦ by
    simpa using EquivariantRing.C_mem_grading_zero N 1
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 1 (fun _ ↦ 3) LinearMap.id
    (LinearMap.comp_id _) (fun _ _ hv j ↦ hv j)
  refine ⟨n, b, d, hb, EquivariantRing.multiset_map_eq_singleton_of_homogeneous_basis_range
    N (fun _ ↦ 3) 0 (w := fun _ ↦ 1) (fun v ↦ funext fun j ↦ ?_) rfl hw b d hb⟩
  rw [Fin.eq_zero j]
  simp

-- Diagonal projection diag(1, 0) on shifts ![a, b]: degree multiset is {a}, independent of b.
private theorem diag_one_zero_degree (N : ℕ) (a b : ℤ) :
    let proj₀ : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] EquivariantRing N :=
      LinearMap.proj 0
    let p := (LinearMap.toSpanSingleton (EquivariantRing N)
      (Fin 2 → EquivariantRing N) ![1, 0]).comp proj₀
    ∃ (n : ℕ) (basis : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      (∀ i j, (basis i).val j ∈ EquivariantRing.grading N (d i - ![a, b] j)) ∧
      Multiset.map d Finset.univ.val = {a} := by
  let proj₀ : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] EquivariantRing N :=
    LinearMap.proj 0
  let p := (LinearMap.toSpanSingleton (EquivariantRing N)
    (Fin 2 → EquivariantRing N) ![1, 0]).comp proj₀
  have hw : ∀ j : Fin 2, (![1, 0] : Fin 2 → EquivariantRing N) j ∈
      EquivariantRing.grading N (![a, b] 0 - ![a, b] j) := by
    intro j
    fin_cases j
    · simpa using EquivariantRing.C_mem_grading_zero N 1
    · simp
  obtain ⟨n, basis, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 2 ![a, b] p
    (idempotent_of_apply_eq_smul 0 (fun _ ↦ rfl) rfl)
    (homogeneous_of_apply_eq_smul ![a, b] 0 (fun _ ↦ rfl) hw)
  exact ⟨n, basis, d, hb, EquivariantRing.multiset_map_eq_singleton_of_homogeneous_basis_range
    N ![a, b] 0 (fun _ ↦ rfl) rfl hw basis d hb⟩

-- Off-diagonal projection p(x, y) = (x, e₁ x) on shifts ![2, 0] for N + 1 ≥ 1: idempotent of
-- degree 0 whose image has degree multiset {2}, exercising the shift sign 2 - 0 = 2.
private theorem e1_offDiag_degree (N : ℕ) :
    let proj₀ : (Fin 2 → EquivariantRing (N + 1)) →ₗ[EquivariantRing (N + 1)]
      EquivariantRing (N + 1) := LinearMap.proj 0
    let w : Fin 2 → EquivariantRing (N + 1) := ![1, _root_.MvPolynomial.X 0]
    let p := (LinearMap.toSpanSingleton (EquivariantRing (N + 1))
      (Fin 2 → EquivariantRing (N + 1)) w).comp proj₀
    p.comp p = p ∧
    (∃ (n : ℕ) (basis : Module.Basis (Fin n) (EquivariantRing (N + 1)) (LinearMap.range p))
      (d : Fin n → ℤ),
      (∀ i j, (basis i).val j ∈ EquivariantRing.grading (N + 1) (d i - ![2, 0] j)) ∧
      Multiset.map d Finset.univ.val = {2}) := by
  let proj₀ : (Fin 2 → EquivariantRing (N + 1)) →ₗ[EquivariantRing (N + 1)]
    EquivariantRing (N + 1) := LinearMap.proj 0
  let w : Fin 2 → EquivariantRing (N + 1) := ![1, _root_.MvPolynomial.X 0]
  let p := (LinearMap.toSpanSingleton (EquivariantRing (N + 1))
    (Fin 2 → EquivariantRing (N + 1)) w).comp proj₀
  have hw : ∀ j : Fin 2, w j ∈ EquivariantRing.grading (N + 1) (![2, 0] 0 - ![2, 0] j) := by
    intro j
    fin_cases j
    · simpa [w] using EquivariantRing.C_mem_grading_zero (N + 1) 1
    · simpa [w] using EquivariantRing.X_mem_grading (N + 1) 0
  have hp : p.comp p = p := idempotent_of_apply_eq_smul (0 : Fin 2) (w := w) (fun _ ↦ rfl) rfl
  obtain ⟨n, basis, d, hb⟩ := exists_homogeneous_basis_range_idempotent (N + 1) 2 ![2, 0] p hp
    (homogeneous_of_apply_eq_smul ![2, 0] 0 (fun _ ↦ rfl) hw)
  exact ⟨hp, n, basis, d, hb,
    EquivariantRing.multiset_map_eq_singleton_of_homogeneous_basis_range
      (N + 1) ![2, 0] 0 (fun _ ↦ rfl) rfl hw basis d hb⟩

end ConcreteVerifications

end TauCeti
