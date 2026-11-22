/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Singular.Torus.AddCircle
public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Polynomial
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Geometry.Manifold.Morse.Torus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Perfect Morse functions

A Morse function `f` on a manifold `M` is **perfect** with coefficients in a division ring `k`
(`TauCeti.IsPerfectMorse`) if, in every degree `n`, its number `cₙ` of critical points of index `n`
equals the dimension `bₙ` of the singular homology `Hₙ(M; k)`. By the weak Morse inequalities
`bₙ ≤ cₙ`, a perfect Morse function has the fewest critical points of each index among all Morse
functions on a compact manifold (`TauCeti.IsPerfectMorse.criticalCount_le`), and so the fewest
critical points altogether (`TauCeti.IsPerfectMorse.totalCriticalCount_le`). In terms of the
Morse polynomial identity `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)` of a Morse function on a compact
manifold (`TauCeti.morse_inequalities`), the function is perfect exactly when `Q = 0`
(`TauCeti.IsMorse.isPerfectMorse_iff_eq_zero`). Whether a perfect Morse function exists depends on
the coefficients, as projective spaces show.

* **Spheres.** The height function on `Sⁿ` has one critical point of index `0` and one of index
  `n`, matching the homology of `Sⁿ`, so it is perfect over every division ring
  (`TauCeti.isPerfectMorse_sphereHeight`): `1 + tⁿ = 1 + tⁿ + (1 + t) · 0`. For `n ≠ 1` this is
  also an instance of the lacunary principle below, but not for `n = 1`, where the indices `0` and
  `1` are adjacent.
* **The lacunary principle.** A Morse function on a compact manifold no two of whose critical
  points have indices differing by one is perfect for every choice of coefficients
  (`TauCeti.IsMorse.isPerfectMorse_of_forall_ne_add_one`). On `ℂℙⁿ` the moment function
  `[z] ↦ (∑ⱼ wⱼ |zⱼ|²) / ∑ⱼ |zⱼ|²` with pairwise distinct weights has only even indices, so it is
  perfect for every division ring of coefficients
  (`TauCeti.isPerfectMorse_projectiveMomentFunction_complex`).
* **Real projective space in characteristic two.** On `ℝPᴺ` the same moment function has one
  critical point of each index `0, …, N`, and `Hⱼ(ℝPᴺ; k)` is one-dimensional for `j ≤ N` when
  `2 = 0` in `k`. So the moment function is perfect over `ℤ/2`
  (`TauCeti.isPerfectMorse_projectiveMomentFunction_real`).
* **No perfect Morse function over `ℚ`.** Every Morse function on a nonempty compact manifold of
  dimension `m` has a critical point of index `m`, at a point of maximum
  (`TauCeti.IsMorse.criticalCount_finrank_ne_zero`), so a perfect Morse function forces the top
  homology to be nonzero (`TauCeti.IsPerfectMorse.finrank_singularHomology_finrank_ne_zero`).
  For even `N ≥ 2` the top homology `H_N(ℝPᴺ; k)` vanishes as soon as `2 ≠ 0` in `k`. So no
  Morse function on `ℝPᴺ`, for instance on `ℝP²`, is perfect over `ℚ`, or over any division ring
  of characteristic other than `2` (`TauCeti.not_isPerfectMorse_projectivization_real`). On `ℝP²`
  the moment function with three distinct weights has three critical points, of indices `0`, `1`
  and `2`; the Betti numbers are `1, 1, 1` over `ℤ/2` but `1, 0, 0` over `ℚ`. Over `ℚ` its Morse
  polynomial is `Q = t`: `1 + t + t² = 1 + (1 + t) t`. On `ℝPⁿ`, away from characteristic two, it
  is the sum of the `tⁱ` over the odd `i < n`
  (`TauCeti.forall_criticalCount_projectiveMomentFunction_real_eq_bettiNumber_add_coeff_iff`). Its
  coefficients are the ranks of the cellular differentials of the standard cell structure of
  `ℝPⁿ`, which has one cell in each dimension
  (`TauCeti.RealProjectiveSpace.finrank_range_cellularChainComplex_d_of_two_ne_zero`).
* **Dimension zero and the empty manifold.** On a manifold modelled on a zero-dimensional space
  every point is a critical point of index `0` of every function, and the manifold is discrete. So
  every function is perfect exactly when the manifold is finite
  (`TauCeti.isPerfectMorse_iff_finite_of_subsingleton`): `r` points give critical counts and Betti
  numbers `r, 0, 0, …`, while on an infinite discrete manifold such as `ℕ` the count of index `0`
  is `⊤` and `H₀` is infinite-dimensional. On the empty manifold every function is perfect, with
  all counts and Betti numbers `0` (`TauCeti.isPerfectMorse_of_isEmpty`).
* **Tori.** On the torus `Tᵐ = ∀ i, AddCircle (p i)` the cosine function
  `x ↦ ∑ᵢ cos (2π xᵢ / pᵢ)` has `(m choose j)` critical points of index `j`, which is the dimension
  of `Hⱼ(Tᵐ; k)`. So it is perfect over every field (`TauCeti.isPerfectMorse_torusCos`), although
  its indices take every value from `0` to `m` and the lacunary principle does not apply. Hence
  every Morse function on `Tᵐ` has at least `(m choose j)` critical points of index `j`
  (`TauCeti.IsMorse.choose_card_le_criticalCount_torus`), and at least `2ᵐ` critical points
  altogether (`TauCeti.IsMorse.two_pow_card_le_totalCriticalCount_torus`).

## References

* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. (N.S.) 7 (1982),
  331–358, §1 (perfect Morse functions and the lacunary principle).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §5 (the Morse inequalities) and §4 (the example of `ℂℙⁿ`).
-/

public section

open CategoryTheory Limits Module Set
open Polynomial (X)
open scoped ContDiff Manifold LinearAlgebra.Projectivization Polynomial

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ}

/-! ### Perfect Morse functions -/

variable (I) in
/-- A **perfect Morse function** with coefficients in a division ring `k`: a Morse function `f`
on `M` such that, in every degree `n`, the singular homology `Hₙ(M; k)` is finite-dimensional and
its dimension is the number of critical points of `f` of index `n`. -/
structure IsPerfectMorse (k : Type u) [DivisionRing k] (f : M → ℝ) : Prop where
  /-- A perfect Morse function is a Morse function. -/
  isMorse : IsMorse I f
  /-- The singular homology of `M` with coefficients in `k` is finite-dimensional. -/
  finite_singularHomology (n : ℕ) : Module.Finite k
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
      (TopCat.of M))
  /-- The number of critical points of index `n` is the dimension of `Hₙ(M; k)`. -/
  criticalCount_eq (n : ℕ) : criticalCount I f n =
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of M))

section Compact

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {k : Type u} [DivisionRing k]

/-- On a compact manifold, a perfect Morse function is a Morse function whose number of critical
points of each index `n` is the dimension of `Hₙ(M; k)`; the finite-dimensionality of homology is
then automatic. -/
theorem isPerfectMorse_iff : IsPerfectMorse I k f ↔ IsMorse I f ∧ ∀ n, criticalCount I f n =
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) :=
  ⟨fun h ↦ ⟨h.isMorse, h.criticalCount_eq⟩,
    fun h ↦ ⟨h.1, h.1.finite_singularHomology (ModuleCat.of k k), h.2⟩⟩

/-- **A perfect Morse function has the fewest critical points of each index.** If `f` is a perfect
Morse function on a compact manifold, every Morse function `g` has at least as many critical
points of each index as `f`. -/
theorem IsPerfectMorse.criticalCount_le (hf : IsPerfectMorse I k f) (hg : IsMorse I g) (n : ℕ) :
    criticalCount I f n ≤ criticalCount I g n := by
  have h := hg.finrank_singularHomology_le (ModuleCat.of k k) n
  rw [ModuleCat.finrank_of_self, mul_one] at h
  rw [hf.criticalCount_eq]
  exact (Nat.cast_le.2 h).trans (ENat.natCast_toNat_le_self _)

/-- **A perfect Morse function has the fewest critical points.** If `f` is a perfect Morse
function on a compact manifold, every Morse function `g` has at least as many critical points
as `f`. -/
theorem IsPerfectMorse.totalCriticalCount_le (hf : IsPerfectMorse I k f) (hg : IsMorse I g) :
    totalCriticalCount I f ≤ totalCriticalCount I g := by
  rw [← sum_criticalCount_eq_totalCriticalCount, ← sum_criticalCount_eq_totalCriticalCount]
  exact Finset.sum_le_sum fun n _ ↦ hf.criticalCount_le hg n

/-- **The lacunary principle.** A Morse function on a compact manifold such that no two critical
points have indices differing by one is perfect, for every division ring of coefficients. -/
theorem IsMorse.isPerfectMorse_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) :
    IsPerfectMorse I k f := by
  refine isPerfectMorse_iff.2 ⟨hf, fun n ↦ ?_⟩
  rw [hf.finrank_singularHomology_eq_of_forall_ne_add_one (ModuleCat.of k k) hind n,
    ModuleCat.finrank_of_self, mul_one,
    ENat.natCast_toNat_eq_self.2 (hf.criticalCount_ne_top n)]

/-- **A Morse function is perfect exactly when its Morse polynomial vanishes.** If `Q` is the
polynomial of the Morse polynomial identity `cⱼ = bⱼ + coeff ((1 + X) * Q) j` of a Morse function
on a compact manifold, then the function is perfect if and only if `Q = 0`. -/
theorem IsMorse.isPerfectMorse_iff_eq_zero (hf : IsMorse I f) {Q : ℕ[X]}
    (hQ : ∀ j : ℕ, criticalCount I f j =
      ((bettiNumber k M j + ((1 + X) * Q).coeff j : ℕ) : ℕ∞)) :
    IsPerfectMorse I k f ↔ Q = 0 := by
  rw [eq_comm, ← forall_criticalCount_eq_bettiNumber_add_coeff_iff hQ, isPerfectMorse_iff]
  simp [hf, bettiNumber_def]

end Compact

variable [I.Boundaryless] [CompactSpace M] {k : Type u} [DivisionRing k] in
/-- **A perfect Morse function forces nonzero top homology.** If a nonempty compact manifold of
dimension `m` carries a perfect Morse function with coefficients in `k`, then `Hₘ(M; k) ≠ 0`:
the maximum is a critical point of index `m`. -/
theorem IsPerfectMorse.finrank_singularHomology_finrank_ne_zero [Nonempty M]
    (hf : IsPerfectMorse I k f) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) (finrank ℝ E)).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) ≠ 0 := by
  have h := hf.isMorse.criticalCount_finrank_ne_zero
  rw [hf.criticalCount_eq] at h
  exact_mod_cast h

/-! ### Zero-dimensional and empty manifolds -/

section Discrete

variable {k : Type u} [DivisionRing k]

/-- On a finite discrete space the homology is free on the points in degree `0` and vanishes in
positive degrees, so a Morse function is perfect as soon as its critical points of index `0` are
counted by the points and it has none of positive index. -/
private theorem isPerfectMorse_of_discreteTopology [DiscreteTopology M] [Finite M]
    (hf : IsMorse I f) (h₀ : criticalCount I f 0 = Nat.card M)
    (hpos : ∀ j ≠ 0, criticalCount I f j = 0) : IsPerfectMorse I k f := by
  refine ⟨hf, fun n ↦ ?_, fun n ↦ ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · exact (finite_singularHomology_zero_iff_of_totallyDisconnectedSpace k M).2 ‹_›
    · have := subsingleton_singularHomology_of_totallyDisconnectedSpace k M hn
      infer_instance
  · rw [← bettiNumber_def]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [h₀, bettiNumber_zero_of_totallyDisconnectedSpace]
    · rw [hpos n hn, bettiNumber_eq_zero_of_totallyDisconnectedSpace k M hn, Nat.cast_zero]

/-- **Perfect Morse functions in dimension zero.** On a manifold modelled on a zero-dimensional
space, every function is a Morse function whose critical points are all the points, each of
index `0`. The manifold is discrete, so its homology is free on its points in degree `0` and
vanishes in positive degrees. Hence, for every division ring `k`, every function is perfect when
the manifold is finite: with `r` points, the critical counts and the Betti numbers are both
`r, 0, 0, …`. No function is perfect on an infinite such manifold, such as `ℕ`: there `H₀(M; k)`
is infinite-dimensional. -/
theorem isPerfectMorse_iff_finite_of_subsingleton [Subsingleton E] :
    IsPerfectMorse I k f ↔ Finite M := by
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := ChartedSpace.discreteTopology H M
  refine ⟨fun h ↦ (finite_singularHomology_zero_iff_of_totallyDisconnectedSpace k M).1
    (h.finite_singularHomology 0), fun _ ↦ isPerfectMorse_of_discreteTopology
      isMorse_of_subsingleton ?_ fun _ ↦ criticalCount_eq_zero_of_subsingleton⟩
  rw [criticalCount_zero_of_subsingleton, ENat.card_eq_coe_natCard]

/-- **Every function on the empty manifold is a perfect Morse function.** It has no critical
points and the empty space has no homology, so the critical counts and the Betti numbers all
vanish. -/
theorem isPerfectMorse_of_isEmpty [IsEmpty M] : IsPerfectMorse I k f := by
  have : DiscreteTopology M := ⟨Subsingleton.elim _ _⟩
  have hcount (j : ℕ) : criticalCount I f j = 0 := by
    rw [criticalCount_def, Set.eq_empty_of_isEmpty {x ∈ _ | _}, encard_empty]
  exact isPerfectMorse_of_discreteTopology (isMorse_iff.2 ⟨isEmptyElim, isEmptyElim⟩)
    (by rw [hcount, Nat.card_of_isEmpty, Nat.cast_zero]) fun j _ ↦ hcount j

end Discrete

/-! ### Projective spaces -/

section Projective

variable {n : ℕ} {w : Fin (n + 1) → ℝ}

/-- **The moment function on `ℂℙⁿ` is perfect.** For pairwise distinct weights, the moment
function on `ℂℙⁿ` is a perfect Morse function for every division ring of coefficients: its
critical points all have even index. -/
theorem isPerfectMorse_projectiveMomentFunction_complex (hw : Function.Injective w) (k : Type)
    [DivisionRing k] :
    IsPerfectMorse 𝓘(ℝ, Fin n → ℂ) k (projectiveMomentFunction ℂ w) := by
  refine (isMorse_projectiveMomentFunction hw).isPerfectMorse_of_forall_ne_add_one ?_
  rw [criticalPoints_projectiveMomentFunction hw]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [manifoldMorseIndex_projectiveMomentFunction, manifoldMorseIndex_projectiveMomentFunction,
    Complex.finrank_real_complex]
  omega

/-- **The moment function on `ℝPⁿ` is perfect in characteristic two.** For pairwise distinct
weights, the moment function on `ℝPⁿ` has one critical point of each index `0, …, n`, and it is a
perfect Morse function with coefficients in every division ring in which `2 = 0`, such as
`ZMod 2`. -/
theorem isPerfectMorse_projectiveMomentFunction_real (hw : Function.Injective w) {k : Type}
    [DivisionRing k] (h2 : (2 : k) = 0) :
    IsPerfectMorse 𝓘(ℝ, Fin n → ℝ) k (projectiveMomentFunction ℝ w) := by
  refine isPerfectMorse_iff.2 ⟨isMorse_projectiveMomentFunction hw, fun j ↦ ?_⟩
  rw [criticalCount_projectiveMomentFunction_real hw,
    RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_eq_zero h2 j]
  simp

/-- **No perfect Morse function on `ℝPᴺ` outside characteristic two.** For even `N ≥ 2`, no Morse
function on `ℝPᴺ` is perfect with coefficients in a division ring in which `2 ≠ 0`, such as `ℚ`:
its maximum is a critical point of index `N`, while `H_N(ℝPᴺ; k) = 0`. In particular `ℝP²`
admits no perfect Morse function over `ℚ`. -/
theorem not_isPerfectMorse_projectivization_real (hn : Even n) (hn0 : n ≠ 0) {k : Type}
    [DivisionRing k] (h2 : (2 : k) ≠ 0) (f : ℙ ℝ (Fin (n + 1) → ℝ) → ℝ) :
    ¬ IsPerfectMorse 𝓘(ℝ, Fin n → ℝ) k f := by
  intro hf
  have h := hf.finrank_singularHomology_finrank_ne_zero
  rw [finrank_fin_fun, ModuleCat.finrank_eq_zero_of_isZero
    (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even k
      (isRegular_iff_ne_zero.2 h2).right hn hn0)] at h
  exact h rfl

/-- **The Morse polynomial of the moment function on `ℝPⁿ` away from characteristic two.** For
pairwise distinct weights and a division ring `k` in which `2 ≠ 0`, such as `ℚ`, the moment
function on `ℝPⁿ` has one critical point of each index `0, …, n`, while `Hⱼ(ℝPⁿ; k)` is
one-dimensional in degree `0` and, for odd `n`, in degree `n`, and vanishes otherwise. Its Morse
polynomial is the sum of the `Xⁱ` over the odd `i < n`: the identity
`cⱼ = bⱼ + coeff ((1 + X) * Q) j` holds in every degree exactly for this `Q`. For `ℝP²` it reads
`1 + t + t² = 1 + (1 + t) t`. -/
theorem forall_criticalCount_projectiveMomentFunction_real_eq_bettiNumber_add_coeff_iff
    (hw : Function.Injective w) {k : Type} [DivisionRing k] (h2 : (2 : k) ≠ 0) {Q : ℕ[X]} :
    (∀ j : ℕ, criticalCount 𝓘(ℝ, Fin n → ℝ) (projectiveMomentFunction ℝ w) j =
      ((bettiNumber k (ℙ ℝ (Fin (n + 1) → ℝ)) j + ((1 + X) * Q).coeff j : ℕ) : ℕ∞)) ↔
      Q = ∑ i ∈ Finset.range n with Odd i, X ^ i := by
  refine forall_criticalCount_eq_bettiNumber_add_coeff_iff fun j ↦ ?_
  have hsum (m : ℕ) : (∑ i ∈ Finset.range n with Odd i, (X : ℕ[X]) ^ i).coeff m =
      if m < n ∧ Odd m then 1 else 0 := by
    simp [Polynomial.coeff_X_pow]
  rw [criticalCount_projectiveMomentFunction_real hw, bettiNumber_def,
    RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_ne_zero h2, add_mul,
    one_mul, Polynomial.coeff_add, hsum]
  rcases j with _ | j
  · simp
  · rw [Polynomial.coeff_X_mul, hsum]
    simp only [Nat.odd_iff, Nat.add_one_ne_zero, false_or]
    split_ifs <;> simp <;> omega

end Projective

/-! ### Spheres -/

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The height function on a sphere is perfect.** For every division ring `k`, the height
function on the sphere `Sⁿ` is a perfect Morse function: it has one critical point of index `0`
and one of index `n`, and `Hⱼ(Sⁿ; k)` is one-dimensional in degrees `0` and `n` and vanishes
otherwise, two-dimensional in degree `0` when `n = 0`. So its Morse polynomial is `0`
(`TauCeti.IsMorse.isPerfectMorse_iff_eq_zero`). -/
theorem isPerfectMorse_sphereHeight (v : Metric.sphere (0 : E) 1) (k : Type u) [DivisionRing k] :
    IsPerfectMorse (𝓡 n) k (sphereHeight v) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine isPerfectMorse_iff.2 ⟨isMorse_sphereHeight v, fun j ↦ ?_⟩
  rw [criticalCount_sphereHeight, ← bettiNumber_def,
    bettiNumber_sphere k (Fact.out : finrank ℝ E = n + 1)]
  norm_cast

end Sphere

/-! ### Tori -/

section Torus

variable {ι : Type} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- **The cosine function on a torus is perfect.** For every field `k`, the cosine function
`TauCeti.torusCos` on the torus `Tᵐ = ∀ i, AddCircle (p i)` is a perfect Morse function: it has
`(m choose j)` critical points of index `j`, and this is the dimension of `Hⱼ(Tᵐ; k)`. -/
theorem isPerfectMorse_torusCos (k : Type) [Field k] :
    IsPerfectMorse (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) k (torusCos p) := by
  have (i : ι) : NeZero (p i) := ⟨(Fact.out : 0 < p i).ne'⟩
  refine ⟨isMorse_torusCos p, fun _ ↦ inferInstance, fun j ↦ ?_⟩
  rw [criticalCount_torusCos, ModuleCat.finrank_singularHomology_pi_addCircle,
    ModuleCat.finrank_of_self, mul_one, Nat.card_eq_fintype_card]

variable {p}

/-- **Morse functions on a torus have binomially many critical points of each index.** Every
Morse function on the torus `Tᵐ = ∀ i, AddCircle (p i)` has at least `(m choose j)` critical
points of index `j`, the number attained by the cosine function `TauCeti.torusCos`. -/
theorem IsMorse.choose_card_le_criticalCount_torus {f : (∀ i, AddCircle (p i)) → ℝ}
    (hf : IsMorse (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f) (j : ℕ) :
    ((Fintype.card ι).choose j : ℕ∞) ≤
      criticalCount (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f j := by
  rw [← criticalCount_torusCos p]
  exact (isPerfectMorse_torusCos p ℚ).criticalCount_le hf j

/-- **Morse functions on a torus have at least `2ᵐ` critical points.** Every Morse function on the
torus `Tᵐ = ∀ i, AddCircle (p i)` has at least `2ᵐ` critical points, the number attained by the
cosine function `TauCeti.torusCos`. -/
theorem IsMorse.two_pow_card_le_totalCriticalCount_torus {f : (∀ i, AddCircle (p i)) → ℝ}
    (hf : IsMorse (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f) :
    (2 ^ Fintype.card ι : ℕ∞) ≤ totalCriticalCount (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f := by
  rw [← totalCriticalCount_torusCos p]
  exact (isPerfectMorse_torusCos p ℚ).totalCriticalCount_le hf

end Torus

end TauCeti
