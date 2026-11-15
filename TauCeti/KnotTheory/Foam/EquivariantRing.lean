/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.Category.GradedModuleCat.Connected
import Mathlib.Tactic.FinCases

/-!
# The equivariant `gl(N)` foam coefficient ring and homogeneous idempotent bases

In equivariant `gl(N)` link and foam homology, closed foams evaluate in the integral polynomial
ring `Λ_N = ℤ[e₁, …, e_N]` in `N` elementary symmetric parameters, graded with `deg(e_{i+1}) =
2(i + 1)`. We model `Λ_N` as `TauCeti.EquivariantRing N := MvPolynomial (Fin N) ℤ`, where the
variable `MvPolynomial.X i` represents `e_{i+1}` in degree `2 * (i + 1)`.

Because every generator has strictly positive even degree, `EquivariantRing.grading N` makes
`EquivariantRing N` a connected nonnegatively `ℤ`-graded algebra over the principal ideal domain
`ℤ` supported purely in even nonnegative degrees (`grading_eq_bot_of_neg`, `grading_eq_bot_of_odd`,
`grading_zero_eq_range`), including the degenerate case `N = 0` (`grading_zero_ring_eq_bot_of_ne`).

Combining connectedness over `ℤ` with the graded Nakayama freeness theorems of
`TauCeti.Algebra.Category.GradedModuleCat.Connected` yields:

* **Graded freeness of retracts and projectives** (`EquivariantRing.exists_fin_free_iso_of_retract`,
  `EquivariantRing.exists_biproduct_shift_regular_iso_of_retract`,
  `EquivariantRing.exists_fin_free_iso_of_finite_projective`): every graded retract of a finite
  direct sum of shifted copies of `Λ_N` is isomorphic in `GradedModuleCat (grading N)` to a finite
  direct sum of shifted copies of `Λ_N`.
* **Explicit homogeneous idempotent splitting** (`EquivariantRing.exists_split_idempotent`): every
  degree-zero homogeneous idempotent `p` on `Fin m → EquivariantRing N` (with summand shifts
  `s : Fin m → ℤ`) factors through `Fin n → EquivariantRing N` via degree-preserving `Λ_N`-linear
  maps `ι` and `π` satisfying `π ∘ₗ ι = id` and `ι ∘ₗ π = p`.
* **Homogeneous bases and shift uniqueness** (`TauCeti.exists_homogeneous_basis_range_idempotent`,
  `EquivariantRing.multiset_map_eq_of_homogeneous_basis_submodule`): the image `LinearMap.range p`
  of any degree-zero homogeneous idempotent `p` admits a finite `Λ_N`-basis of homogeneous vectors,
  and both the rank `n` and the multiset of basis shifts of any submodule are uniquely determined.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech. Math.
  7 (2020), 573–651, Theorem 3.30, for integral graded freeness and decomposition into shifted
  empty webs over `ℤ[e₁, …, e_N]`.
* D. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

/-- The equivariant `gl(N)` coefficient ring `Λ_N = ℤ[e₁, …, e_N]`. The variable
`MvPolynomial.X i` (`i : Fin N`) represents the `(i + 1)`-st elementary parameter `e_{i+1}` of
degree `2(i + 1)`. -/
abbrev EquivariantRing (N : ℕ) : Type := MvPolynomial (Fin N) ℤ

namespace EquivariantRing

/-- The degree assignment `i ↦ 2(i + 1)` on the `N` polynomial generators of `EquivariantRing N`. -/
@[expose]
def weight (N : ℕ) (i : Fin N) : ℤ :=
  2 * ((i : ℕ) + 1 : ℤ)

/-- Unfolding lemma for `EquivariantRing.weight`. -/
theorem weight_def (N : ℕ) (i : Fin N) :
    weight N i = 2 * ((i : ℕ) + 1 : ℤ) :=
  (rfl)

/-- The integral `ℤ`-grading on `EquivariantRing N` placing `MvPolynomial.X i` in degree
`2(i + 1)`. -/
@[expose]
def grading (N : ℕ) : ℤ → Submodule ℤ (EquivariantRing N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N)

/-- Unfolding lemma for `EquivariantRing.grading`. -/
theorem grading_def (N : ℕ) :
    grading N = MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N) :=
  (rfl)

/-- `EquivariantRing N` is internally `ℤ`-graded by `grading N`. -/
noncomputable instance gradedAlgebra (N : ℕ) : GradedAlgebra (grading N) :=
  MvPolynomial.weightedGradedAlgebra ℤ (weight N)

/-- Every polynomial generator `MvPolynomial.X i` has strictly positive degree `2(i + 1) ≥ 2`. -/
theorem weight_pos (N : ℕ) (i : Fin N) : 0 < weight N i := by
  rw [weight_def]
  omega

/-- Every polynomial generator `MvPolynomial.X i` has even degree. -/
theorem even_weight (N : ℕ) (i : Fin N) : Even (weight N i) :=
  ⟨(i : ℕ) + 1, by rw [weight_def]; ring⟩

/-- Every monomial exponent `c : Fin N →₀ ℕ` has nonnegative weighted degree. -/
theorem weight_monomial_nonneg {N : ℕ} (c : Fin N →₀ ℕ) :
    0 ≤ Finsupp.weight (weight N) c := by
  rw [Finsupp.weight_eq_sum]
  exact Finset.sum_nonneg fun i _ => nsmul_nonneg (weight_pos N i).le _

/-- Every monomial exponent `c : Fin N →₀ ℕ` has even weighted degree. -/
theorem even_weight_monomial {N : ℕ} (c : Fin N →₀ ℕ) :
    Even (Finsupp.weight (weight N) c) := by
  rw [Finsupp.weight_eq_sum]
  refine ⟨∑ i : Fin N, (c i : ℤ) * ((i : ℕ) + 1 : ℤ), ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weight_def]
  ring

/-- A monomial exponent `c : Fin N →₀ ℕ` has weighted degree `0` if and only if `c = 0`. -/
@[simp]
theorem weight_monomial_eq_zero_iff {N : ℕ} (c : Fin N →₀ ℕ) :
    Finsupp.weight (weight N) c = 0 ↔ c = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  ext i
  by_contra hi
  have hle := Finsupp.le_weight_of_ne_zero (fun j => (weight_pos N j).le) hi
  linarith [weight_pos N i]

/-- Membership in `grading N d` is weighted homogeneity of degree `d` with respect to `weight N`. -/
theorem mem_grading_iff {N : ℕ} {d : ℤ} {f : EquivariantRing N} :
    f ∈ grading N d ↔ MvPolynomial.IsWeightedHomogeneous (weight N) f d :=
  Iff.rfl

/-- The multiplicative identity `1 : EquivariantRing N` has homogeneous degree `0`. -/
theorem one_mem_grading_zero (N : ℕ) : (1 : EquivariantRing N) ∈ grading N 0 :=
  SetLike.one_mem_graded (grading N)

/-- Homogeneous elements of `EquivariantRing N` multiply by adding their degrees. -/
theorem mul_mem_grading {N : ℕ} {d₁ d₂ : ℤ} {f g : EquivariantRing N}
    (hf : f ∈ grading N d₁) (hg : g ∈ grading N d₂) :
    f * g ∈ grading N (d₁ + d₂) :=
  SetLike.mul_mem_graded hf hg

/-- The `i`-th elementary generator `MvPolynomial.X i` lies in `grading N (2 * (i + 1))`. -/
theorem X_mem_grading (N : ℕ) (i : Fin N) :
    (MvPolynomial.X i : EquivariantRing N) ∈ grading N (2 * ((i : ℕ) + 1 : ℤ)) :=
  MvPolynomial.isWeightedHomogeneous_X ℤ (weight N) i

/-- Every constant polynomial `MvPolynomial.C z` has homogeneous degree `0`. -/
theorem C_mem_grading_zero (N : ℕ) (z : ℤ) :
    (MvPolynomial.C z : EquivariantRing N) ∈ grading N 0 :=
  MvPolynomial.isWeightedHomogeneous_C (weight N) z

/-- Every integer scalar `algebraMap ℤ (EquivariantRing N) z` has homogeneous degree `0`. -/
theorem algebraMap_mem_grading_zero (N : ℕ) (z : ℤ) :
    algebraMap ℤ (EquivariantRing N) z ∈ grading N 0 := by
  rw [MvPolynomial.algebraMap_eq]
  exact C_mem_grading_zero N z

/-- All negative-degree homogeneous pieces of `EquivariantRing N` vanish. -/
theorem grading_eq_bot_of_neg (N : ℕ) {d : ℤ} (hd : d < 0) :
    grading N d = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  exact hf.eq_zero_of_no_monomials fun c hc => by linarith [weight_monomial_nonneg c]

/-- All odd-degree homogeneous pieces of `EquivariantRing N` vanish. -/
theorem grading_eq_bot_of_odd (N : ℕ) {d : ℤ} (hd : Odd d) :
    grading N d = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  refine hf.eq_zero_of_no_monomials fun c hc => ?_
  rcases even_weight_monomial c with ⟨k, hk⟩
  rcases hd with ⟨m, hm⟩
  omega

/-- At `N = 0`, `EquivariantRing 0` is concentrated in degree `0`. -/
theorem grading_zero_ring_eq_bot_of_ne {d : ℤ} (hd : d ≠ 0) :
    grading 0 d = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  refine hf.eq_zero_of_no_monomials fun c hc => hd ?_
  rw [← hc, Subsingleton.elim c 0, map_zero]

/-- An element of `EquivariantRing N` has degree `0` if and only if it is an integer constant. -/
theorem mem_grading_zero_iff (N : ℕ) (f : EquivariantRing N) :
    f ∈ grading N 0 ↔ ∃ z : ℤ, algebraMap ℤ (EquivariantRing N) z = f := by
  refine ⟨fun hf => ?_, fun ⟨z, hz⟩ => hz ▸ algebraMap_mem_grading_zero N z⟩
  refine ⟨MvPolynomial.constantCoeff f, ?_⟩
  have hmono := hf.eq_monomial_of_unique_weight (d₀ := 0) fun c hc =>
    (weight_monomial_eq_zero_iff c).mp hc
  rw [MvPolynomial.monomial_zero'] at hmono
  exact hmono.symm

/-- `EquivariantRing N` is connected over `ℤ`: its degree-zero piece is the image of `ℤ`. -/
theorem grading_zero_eq_range (N : ℕ) :
    grading N 0 = LinearMap.range (Algebra.linearMap ℤ (EquivariantRing N)) := by
  ext f
  exact mem_grading_zero_iff N f

/-- The constant-term augmentation `MvPolynomial.constantCoeff` vanishes on every nonzero-degree
homogeneous piece of `EquivariantRing N`. -/
theorem constantCoeff_eq_zero_of_mem_grading {N : ℕ} {d : ℤ} (hd : d ≠ 0)
    {f : EquivariantRing N} (hf : f ∈ grading N d) :
    MvPolynomial.constantCoeff f = 0 := by
  rw [MvPolynomial.constantCoeff_eq]
  exact hf.coeff_eq_zero 0 (by simpa using hd.symm)

/-- On degree-zero elements, `algebraMap ℤ (EquivariantRing N) ∘ MvPolynomial.constantCoeff` is the
identity. -/
theorem algebraMap_constantCoeff_of_mem_grading_zero {N : ℕ} {f : EquivariantRing N}
    (hf : f ∈ grading N 0) :
    algebraMap ℤ (EquivariantRing N) (MvPolynomial.constantCoeff f) = f := by
  obtain ⟨z, rfl⟩ := (mem_grading_zero_iff N f).mp hf
  simp

/-- The units of `EquivariantRing N` are precisely `1` and `-1`. -/
theorem isUnit_iff {N : ℕ} {f : EquivariantRing N} :
    IsUnit f ↔ f = 1 ∨ f = -1 := by
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases Int.isUnit_iff.mp hr with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, isUnit_one, by simp⟩
    · exact ⟨-1, Int.isUnit_iff.mpr (Or.inr rfl), by simp⟩

/-- Every unit of `EquivariantRing N` is homogeneous of degree `0`. -/
theorem mem_grading_zero_of_isUnit {N : ℕ} {f : EquivariantRing N} (hf : IsUnit f) :
    f ∈ grading N 0 := by
  rcases isUnit_iff.mp hf with rfl | rfl
  · exact one_mem_grading_zero N
  · exact (grading N 0).neg_mem (one_mem_grading_zero N)

/-- Every graded retract of a finite shifted free module `GradedModuleCat.free (grading N) s` over
`EquivariantRing N` is isomorphic in `GradedModuleCat (grading N)` to a finite shifted free module.
-/
theorem exists_fin_free_iso_of_retract (N : ℕ) {J : Type} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{0} (grading N)}
    (i : P ⟶ GradedModuleCat.free (grading N) s)
    (r : GradedModuleCat.free (grading N) s ⟶ P) (hir : i ≫ r = 𝟙 P) :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (GradedModuleCat.free (grading N) d ≅ P) :=
  GradedModuleCat.exists_fin_free_iso_of_retract (grading N)
    (fun _ hi => grading_eq_bot_of_neg N hi) (grading_zero_eq_range N).le s i r hir

/-- Every graded retract of a finite categorical biproduct of shifted copies of `EquivariantRing N`
is isomorphic in `GradedModuleCat (grading N)` to a finite biproduct of shifted copies of
`EquivariantRing N`. -/
theorem exists_biproduct_shift_regular_iso_of_retract (N : ℕ)
    [HasFiniteBiproducts (GradedModuleCat.{0} (grading N))]
    {J : Type} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{0} (grading N)}
    (i : P ⟶ biproduct fun j : J =>
      (GradedModuleCat.shiftFunctor (𝒜 := grading N) (s j)).obj
        (GradedModuleCat.regular (𝒜 := grading N)))
    (r : (biproduct fun j : J =>
      (GradedModuleCat.shiftFunctor (𝒜 := grading N) (s j)).obj
        (GradedModuleCat.regular (𝒜 := grading N))) ⟶ P)
    (hir : i ≫ r = 𝟙 P) :
    ∃ (n : ℕ) (d : Fin n → ℤ),
      Nonempty ((biproduct fun idx : Fin n =>
        (GradedModuleCat.shiftFunctor (𝒜 := grading N) (d idx)).obj
          (GradedModuleCat.regular (𝒜 := grading N))) ≅ P) :=
  GradedModuleCat.exists_biproduct_shift_regular_iso_of_retract (grading N)
    (fun _ hi => grading_eq_bot_of_neg N hi) (grading_zero_eq_range N).le s i r hir

/-- Every finitely generated projective graded `EquivariantRing N`-module is isomorphic in
`GradedModuleCat (grading N)` to a finite shifted free module. -/
theorem exists_fin_free_iso_of_finite_projective (N : ℕ)
    (P : GradedModuleCat.{0} (grading N))
    [Module.Finite (EquivariantRing N) P] [Module.Projective (EquivariantRing N) P] :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (GradedModuleCat.free (grading N) d ≅ P) :=
  GradedModuleCat.exists_fin_free_iso_of_finite_projective (grading N)
    (fun _ hi => grading_eq_bot_of_neg N hi) (grading_zero_eq_range N).le P

/-- **Homogeneous splitting of degree-zero idempotents over `EquivariantRing N`.** Any degree-zero
idempotent `p` on `Fin m → EquivariantRing N` (with summand shifts `s : Fin m → ℤ`) splits through
`Fin n → EquivariantRing N` (with shifts `d : Fin n → ℤ`) via homogeneous `EquivariantRing N`-linear
maps `ι` and `π` satisfying `π ∘ₗ ι = id` and `ι ∘ₗ π = p`. -/
theorem exists_split_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ grading N (d - s j)) → ∀ j, p v j ∈ grading N (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
      (π : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin n → EquivariantRing N)),
      π.comp ι = LinearMap.id ∧
      ι.comp π = p ∧
      (∀ (q : ℤ) (w : Fin n → EquivariantRing N),
        (∀ i, w i ∈ grading N (q - d i)) → ∀ j, ι w j ∈ grading N (q - s j)) ∧
      (∀ (q : ℤ) (v : Fin m → EquivariantRing N),
        (∀ j, v j ∈ grading N (q - s j)) → ∀ i, π v i ∈ grading N (q - d i)) :=
  GradedModuleCat.exists_split_pi_of_idempotent (grading N)
    (fun _ hi => grading_eq_bot_of_neg N hi) (grading_zero_eq_range N).le s p hp hhom

/-- Any two finite homogeneous `EquivariantRing N`-bases of a submodule `S` of
`Fin m → EquivariantRing N` (with ambient summand shifts `s : Fin m → ℤ`) have the same multiset of
shifts. -/
theorem multiset_map_eq_of_homogeneous_basis_submodule (N m : ℕ) (s : Fin m → ℤ)
    (S : Submodule (EquivariantRing N) (Fin m → EquivariantRing N))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) (EquivariantRing N) S) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ grading N (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) (EquivariantRing N) S) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ grading N (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val :=
  GradedModuleCat.multiset_map_eq_of_homogeneous_basis_submodule (grading N)
    (fun _ hi => grading_eq_bot_of_neg N hi) (grading_zero_eq_range N).le s S
    b₁ d₁ hb₁ b₂ d₂ hb₂

/-- Any two finite homogeneous `EquivariantRing N`-bases of a submodule `S` of
`Fin m → EquivariantRing N` have equal rank. -/
theorem rank_eq_of_homogeneous_basis_submodule (N m : ℕ) (s : Fin m → ℤ)
    (S : Submodule (EquivariantRing N) (Fin m → EquivariantRing N))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) (EquivariantRing N) S) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ grading N (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) (EquivariantRing N) S) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ grading N (d₂ i - s j)) :
    n₁ = n₂ := by
  have h := congrArg Multiset.card
    (multiset_map_eq_of_homogeneous_basis_submodule N m s S b₁ d₁ hb₁ b₂ d₂ hb₂)
  simpa using h

end EquivariantRing

/-- The image of a degree-zero idempotent on a finite sum of shifted copies of `EquivariantRing N`
has a finite homogeneous `EquivariantRing N`-basis. Here the `j`-th summand has shift `s j`, so a
homogeneous element of degree `d` has `j`-th coordinate in `EquivariantRing.grading N (d - s j)`. -/
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
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) :=
  GradedModuleCat.exists_homogeneous_basis_range_idempotent (EquivariantRing.grading N)
    (fun _ hi => EquivariantRing.grading_eq_bot_of_neg N hi)
    (EquivariantRing.grading_zero_eq_range N).le s p hp hhom

section Examples

/-! ### Explicit examples of shifted homogeneous idempotent bases -/

private abbrev rankOneProj {R : Type*} [CommRing R] {m : ℕ} (u : Fin (m + 1) → R) :
    (Fin (m + 1) → R) →ₗ[R] (Fin (m + 1) → R) :=
  (LinearMap.proj (R := R) (φ := fun _ : Fin (m + 1) => R) 0).smulRight u

private theorem rankOneProj_idem {R : Type*} [CommRing R] {m : ℕ}
    (u : Fin (m + 1) → R) (hu : u 0 = 1) :
    (rankOneProj u).comp (rankOneProj u) = rankOneProj u := by
  apply LinearMap.ext
  intro v
  ext j
  simp [rankOneProj, hu]

private noncomputable def rankOneProjBasis {R : Type*} [CommRing R] {m : ℕ}
    (u : Fin (m + 1) → R) (hu : u 0 = 1) :
    Module.Basis (Fin 1) R (LinearMap.range (rankOneProj u)) :=
  (Module.Basis.singleton (Fin 1) R).map <|
    LinearEquiv.ofLinearMap
      { toFun := fun r => ⟨r • u, Pi.single 0 r, by simp [rankOneProj]⟩
        map_add' := fun x y => Subtype.ext (add_smul x y u)
        map_smul' := fun c x => Subtype.ext (by simp [mul_smul]) }
      ((LinearMap.proj (R := R) (φ := fun _ : Fin (m + 1) => R) 0).comp (Submodule.subtype _))
      (by
        apply LinearMap.ext
        rintro ⟨_, v, rfl⟩
        exact Subtype.ext (by simp [rankOneProj, hu]))
      (by
        apply LinearMap.ext
        intro r
        simp [hu])

private theorem rankOneProjBasis_val {R : Type*} [CommRing R] {m : ℕ}
    (u : Fin (m + 1) → R) (hu : u 0 = 1) :
    (rankOneProjBasis u hu 0).val = u := by
  ext j
  simp [rankOneProjBasis]

-- For `p = 0`, any homogeneous basis of `LinearMap.range p` is empty (`n = 0`).
example (N m : ℕ) (s : Fin m → ℤ)
    (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing N)
      (LinearMap.range (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
        (Fin m → EquivariantRing N))))
    (d : Fin n → ℤ)
    (hb : ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j)) :
    n = 0 := by
  have : Subsingleton (LinearMap.range
      (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
        (Fin m → EquivariantRing N))) := by
    rw [LinearMap.range_zero]
    infer_instance
  exact EquivariantRing.rank_eq_of_homogeneous_basis_submodule N m s _
    b d hb (Module.Basis.empty _) Fin.elim0 (fun i => i.elim0)

-- For `p = id` on a rank-one summand of shift `3`, any homogeneous basis has `n = 1` and shift `3`.
example (N : ℕ) (n : ℕ)
    (b : Module.Basis (Fin n) (EquivariantRing N)
      (LinearMap.range (LinearMap.id : (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N]
        (Fin 1 → EquivariantRing N))))
    (d : Fin n → ℤ)
    (hb : ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - (![3] : Fin 1 → ℤ) j)) :
    ∃ hn : n = 1, d (hn ▸ 0) = 3 := by
  let eTop : (Fin 1 → EquivariantRing N) ≃ₗ[EquivariantRing N]
      LinearMap.range (LinearMap.id :
        (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 1 → EquivariantRing N)) :=
    LinearEquiv.ofLinearMap
      { toFun := fun v => ⟨v, v, rfl⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      (Submodule.subtype _) (by ext; rfl) (by ext; rfl)
  let b₀ := (Pi.basisFun (EquivariantRing N) (Fin 1)).map eTop
  have hb₀ : ∀ i j, (b₀ i).val j ∈
      EquivariantRing.grading N ((fun _ : Fin 1 => (3 : ℤ)) i - (![3] : Fin 1 → ℤ) j) := by
    intro i j
    fin_cases i
    fin_cases j
    simpa [b₀, eTop] using EquivariantRing.one_mem_grading_zero N
  have hmult := EquivariantRing.multiset_map_eq_of_homogeneous_basis_submodule N 1 ![3] _
    b d hb b₀ (fun _ => 3) hb₀
  have hn : n = 1 := by simpa using congrArg Multiset.card hmult
  subst hn
  exact ⟨rfl, by simpa using hmult⟩

-- For `p = diag(1, 0)` on shifts `![a, b]`, `(1, 0)` has degree `a` and every homogeneous basis of
-- `LinearMap.range p` has `n = 1` and shift `a`, independently of `b`.
example (N : ℕ) (a b : ℤ) :
    let s : Fin 2 → ℤ := ![a, b]
    let p : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 2 → EquivariantRing N) :=
      rankOneProj ![1, 0]
    (∀ v, p v = ![v 0, 0]) ∧ p.comp p = p ∧
      (∀ (n : ℕ) (b' : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
        (d : Fin n → ℤ),
        (∀ i j, (b' i).val j ∈ EquivariantRing.grading N (d i - s j)) →
        ∃ hn : n = 1, d (hn ▸ 0) = a) := by
  intro s p
  have hu : (![1, 0] : Fin 2 → EquivariantRing N) 0 = 1 := by simp
  refine ⟨fun v => by ext j; fin_cases j <;> simp [p, rankOneProj],
    rankOneProj_idem ![1, 0] hu, ?_⟩
  intro n b' d hb'
  have hb₀ : ∀ i j,
      (rankOneProjBasis (![1, 0] : Fin 2 → EquivariantRing N) hu i).val j ∈
        EquivariantRing.grading N ((fun _ => a) i - s j) := by
    intro i j
    rw [Subsingleton.elim i 0, rankOneProjBasis_val]
    fin_cases j
    · simpa [s] using EquivariantRing.one_mem_grading_zero N
    · simp
  have hmult := EquivariantRing.multiset_map_eq_of_homogeneous_basis_submodule N 2 s _
    b' d hb' (rankOneProjBasis ![1, 0] hu) (fun _ => a) hb₀
  have hn : n = 1 := by simpa using congrArg Multiset.card hmult
  subst hn
  exact ⟨rfl, by simpa using hmult⟩

-- For `N ≥ 1`, shifts `![2, 0]`, and `p(x, y) = (x, e₁ * x)` (`e₁ = X 0`), we have `p² = p`, `p`
-- is homogeneous of degree `0`, `(1, e₁)` has degree `2` (with second coordinate in degree `2`),
-- and every homogeneous basis of `LinearMap.range p` has `n = 1` and `d 0 = 2`.
example (N : ℕ) :
    let s : Fin 2 → ℤ := ![2, 0]
    let e₁ : EquivariantRing (N + 1) := MvPolynomial.X 0
    let p : (Fin 2 → EquivariantRing (N + 1)) →ₗ[EquivariantRing (N + 1)]
        (Fin 2 → EquivariantRing (N + 1)) :=
      rankOneProj ![1, e₁]
    (∀ v, p v = ![v 0, e₁ * v 0]) ∧ p.comp p = p ∧
      (∀ (q : ℤ) (v : Fin 2 → EquivariantRing (N + 1)),
        (∀ j, v j ∈ EquivariantRing.grading (N + 1) (q - s j)) →
        ∀ j, p v j ∈ EquivariantRing.grading (N + 1) (q - s j)) ∧
      (∀ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing (N + 1)) (LinearMap.range p))
        (d : Fin n → ℤ),
        (∀ i j, (b i).val j ∈ EquivariantRing.grading (N + 1) (d i - s j)) →
        ∃ hn : n = 1, d (hn ▸ 0) = 2) := by
  intro s e₁ p
  have he₁ : e₁ ∈ EquivariantRing.grading (N + 1) 2 := EquivariantRing.X_mem_grading (N + 1) 0
  have hu : (![1, e₁] : Fin 2 → EquivariantRing (N + 1)) 0 = 1 := by simp
  refine ⟨fun v => by ext j; fin_cases j <;> simp [p, rankOneProj, mul_comm],
    rankOneProj_idem ![1, e₁] hu, ?_, ?_⟩
  · intro q v hv j
    fin_cases j
    · simpa [p, rankOneProj, s] using hv 0
    · have hv0 : v 0 ∈ EquivariantRing.grading (N + 1) (q - 2) := by simpa [s] using hv 0
      have hmul := EquivariantRing.mul_mem_grading hv0 he₁
      have heq : q - 2 + 2 = q - s 1 := by simp [s]
      simpa [p, rankOneProj, heq] using hmul
  · intro n b d hb
    have hb₀ : ∀ i j,
        (rankOneProjBasis (![1, e₁] : Fin 2 → EquivariantRing (N + 1)) hu i).val j ∈
          EquivariantRing.grading (N + 1) ((fun _ => (2 : ℤ)) i - s j) := by
      intro i j
      rw [Subsingleton.elim i 0, rankOneProjBasis_val]
      fin_cases j
      · simpa [s] using EquivariantRing.one_mem_grading_zero (N + 1)
      · simpa [s] using he₁
    have hmult := EquivariantRing.multiset_map_eq_of_homogeneous_basis_submodule (N + 1) 2 s _
      b d hb (rankOneProjBasis ![1, e₁] hu) (fun _ => 2) hb₀
    have hn : n = 1 := by simpa using congrArg Multiset.card hmult
    subst hn
    exact ⟨rfl, by simpa using hmult⟩

end Examples

end TauCeti
