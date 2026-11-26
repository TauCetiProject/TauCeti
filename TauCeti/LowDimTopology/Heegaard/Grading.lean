/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.LowDimTopology.Heegaard.FlavorExactSequence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Maslov gradings of the generators and of the flavor complexes

The relative Maslov grading of a Heegaard diagram
(`TauCeti.LowDimTopology.Heegaard.RelativeGrading`) assigns to generators `x`, `y` joined by a
domain `D` the number `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)`. This file lifts it to a grading of the generators
and of the chain groups of all the flavors, and shows that the differentials have degree `-1` and
that `U` has degree `-2`.

A **Maslov grading** (`TauCeti.HeegaardRegionSystem.IsMaslovGrading`) is a function
`gr : Generator → ℚ` with `gr(x) - gr(y) = μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for every domain `D` from `x` to
`y`. It computes the relative grading (`IsMaslovGrading.relativeGrading_eq`), and two Maslov
gradings differ by a constant on each class of generators joined by domains
(`IsMaslovGrading.sub_eq_sub`, `IsMaslovGrading.exists_eq_add`). One
exists exactly when every domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`
(`TauCeti.HeegaardRegionSystem.exists_isMaslovGrading_iff`); when the domains from a generator to
itself are normalized as in a singly pointed diagram of a closed surface, this says that every
periodic domain has Maslov index zero
(`exists_isMaslovGrading_iff_forall_periodicMaslovIndices_eq_bot`). On a geometric diagram the
Maslov index of a periodic domain is the evaluation of `c₁` of the spin^c structure of the
generator (not formalized here), so this is the case of torsion spin^c structures, the case in
which Ozsváth and Szabó grade the generators by integers. The grading is
`ℚ`-valued here because the combinatorial Maslov index is a rational number; the Maslov component
of a knot grading is an integer-valued example
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.isMaslovGrading`). When a periodic domain has nonzero
Maslov index there is no Maslov grading, as for the genus-one diagram of `S¹ × S²` with its
basepoint in a bigon, where two domains from one generator to the other give `μ(D) - 2 n_z(D)`
the values `-1` and `1`
(`TauCeti.HeegaardRegionSystem.maslovIndex_sub_two_mul_circleTimesSphere_one`).

A grading `gr` of the generators grades the chain groups over `𝔽₂ = ZMod 2`:

* `CF̂`, by `gr` (`TauCeti.HeegaardRegionSystem.hatGrading`);
* `CF⁻` and `CF^∞`, in which `U ^ k x` has degree `gr(x) - 2 k`
  (`TauCeti.HeegaardRegionSystem.minusGrading`, `TauCeti.HeegaardRegionSystem.infinityGrading`).
  Each is the grading of the `𝔽₂`-basis of the chains `U ^ k x` by these degrees;
* `CF⁺ = CF^∞ / CF⁻`, by the images of the pieces of `CF^∞`
  (`TauCeti.HeegaardRegionSystem.plusGrading`). This is a grading because `CF⁻` is a homogeneous
  submodule of `CF^∞`.

In the notation `[x, i] = U ^ (-i) x` of Ozsváth and Szabó this is their grading
`gr([x, i]) = gr(x) + 2 i`, and `U` lowers it by two (`X_smul_mem_minusGradedPiece`,
`X_smul_mem_infinityGradedPiece`, `X_smul_mem_plusGrading_piece`). For a Maslov grading, the hat,
minus, infinity and plus differentials have degree `-1`
(`IsMaslovGrading.isHomogeneous_hatDifferential`, `IsMaslovGrading.isHomogeneous_minusDifferential`,
`IsMaslovGrading.isHomogeneous_infinityDifferential`,
`IsMaslovGrading.isHomogeneous_plusDifferential`): a counted domain from `x` to `y` with
`n_z(D) = k` has Maslov index one, so it joins `U ^ j x`, of degree `gr(x) - 2 j`, to
`U ^ (j + k) y`, of degree `gr(y) - 2 (j + k) = gr(x) - 2 j - 1`.

The maps of the short exact sequences relating the flavors
(`TauCeti.LowDimTopology.Heegaard.FlavorExactSequence`) are homogeneous: the inclusion of `CF⁻`
into `CF^∞` (`mapRange_toLaurent_mem_infinityGradedPiece`), the quotient map onto `CF⁺`
(`TauCeti.InternalGrading.isHomogeneous_mkQ`) and setting `U = 0`
(`mapRange_constantCoeff_mem_hatGradedPiece`) have degree `0`, and the inclusion of `CF̂` into
`CF⁺` has degree `2` (`isHomogeneous_hatToPlus`), since it sends `x` to the class of `U⁻¹ x`. Our
`CF⁻` is spanned by the `U ^ k x` with `k ≥ 0` rather than `k > 0`, which is why this map, of degree
`0` in the conventions of Ozsváth and Szabó, has degree `2` here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsMaslovGrading`: a rational grading of the generators lifting the
  relative Maslov grading.
* `TauCeti.HeegaardRegionSystem.hatGradedPiece`, `TauCeti.HeegaardRegionSystem.minusGradedPiece`,
  `TauCeti.HeegaardRegionSystem.infinityGradedPiece`: the homogeneous pieces of `CF̂`, `CF⁻` and
  `CF^∞`.
* `TauCeti.HeegaardRegionSystem.hatGrading`, `TauCeti.HeegaardRegionSystem.minusGrading`,
  `TauCeti.HeegaardRegionSystem.infinityGrading`, `TauCeti.HeegaardRegionSystem.plusGrading`: the
  internal gradings of `CF̂`, `CF⁻`, `CF^∞` and `CF⁺`.

## Main results

* `TauCeti.HeegaardRegionSystem.exists_isMaslovGrading_iff`: existence of Maslov gradings.
* `TauCeti.HeegaardRegionSystem.IsMaslovGrading.exists_eq_add`: their uniqueness up to a shift.
* `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_hatDifferential`,
  `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_minusDifferential`,
  `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_infinityDifferential` and
  `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_plusDifferential`: the differentials
  have degree `-1`.
* `TauCeti.HeegaardRegionSystem.X_smul_mem_minusGradedPiece`,
  `TauCeti.HeegaardRegionSystem.X_smul_mem_infinityGradedPiece` and
  `TauCeti.HeegaardRegionSystem.X_smul_mem_plusGrading_piece`: `U` has degree `-2`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.1 (the complexes `CF^∞`, `CF⁻`,
  `CF⁺`, and the grading `gr([x, i]) = gr(x) + 2 i` for torsion spin^c structures).
-/

public section

open Polynomial LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section MaslovGrading

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint]

variable (H) in
/-- A **Maslov grading** of the generators: a rational grading `gr` whose differences are given by
every domain, `gr(x) - gr(y) = μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for each domain `D` from `x` to `y`, where
`μ` is the combinatorial Maslov index with region Euler characteristics `χ`. With a single
basepoint `z` this is `gr(x) - gr(y) = μ(D) - 2 n_z(D)`. Such a grading exists exactly when every
domain from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`
(`TauCeti.HeegaardRegionSystem.exists_isMaslovGrading_iff`), and it is then unique up to a
constant on each class of generators joined by domains. -/
structure IsMaslovGrading (χ : Region → ℤ) (gr : H.Generator → ℚ) : Prop where
  /-- The grading drops by `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` along every domain `D`. -/
  sub_eq {x y : H.Generator} {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    gr x - gr y = H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ)

variable {χ : Region → ℤ} {gr gr' : H.Generator → ℚ} {x y : H.Generator} {D E : Region → ℤ}

/-- If every domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`, the normalization
of the relative grading holds. -/
private theorem maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_forall
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ))
    (x : H.Generator) (E : Region → ℤ) (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x := by
  rw [hself x E hE, sub_self]
  exact zero_mem _

namespace IsMaslovGrading

/-- Shifting a Maslov grading by a constant gives a Maslov grading. -/
theorem add_const (h : H.IsMaslovGrading χ gr) (c : ℚ) :
    H.IsMaslovGrading χ fun x => gr x + c where
  sub_eq hD := by
    rw [← h.sub_eq hD]
    ring

/-- Two Maslov gradings differ by the same amount at generators joined by a domain. -/
theorem sub_eq_sub (h : H.IsMaslovGrading χ gr) (h' : H.IsMaslovGrading χ gr')
    (hD : H.IsDomainBetween x y D) : gr' x - gr x = gr' y - gr y := by
  have := (h'.sub_eq hD).trans (h.sub_eq hD).symm
  linarith

/-- **Maslov gradings are unique up to an overall shift.** When every two generators are joined
by a domain, two Maslov gradings differ by a constant. -/
theorem exists_eq_add (h : H.IsMaslovGrading χ gr) (h' : H.IsMaslovGrading χ gr')
    (hconn : ∀ x y : H.Generator, ∃ D, H.IsDomainBetween x y D) :
    ∃ c : ℚ, gr' = fun x => gr x + c := by
  rcases isEmpty_or_nonempty H.Generator with hH | ⟨⟨x₀⟩⟩
  · exact ⟨0, funext isEmptyElim⟩
  refine ⟨gr' x₀ - gr x₀, funext fun x => ?_⟩
  obtain ⟨D, hD⟩ := hconn x x₀
  have := h.sub_eq_sub h' hD
  linarith

/-- In the presence of a Maslov grading, a domain `E` from a generator to itself has Maslov index
`2 ∑ᵢ n_{zᵢ}(E)`. -/
theorem maslovIndex_self (h : H.IsMaslovGrading χ gr) (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ) := by
  have := h.sub_eq hE
  rw [sub_self] at this
  linarith

/-- In the presence of a Maslov grading, every periodic domain has Maslov index zero at every
generator. -/
theorem maslovIndex_eq_zero_of_mem_periodicDomains (h : H.IsMaslovGrading χ gr)
    {P : Region → ℤ} (hP : P ∈ H.periodicDomains) (x : H.Generator) :
    H.maslovIndex χ x x P = 0 := by
  obtain ⟨hxx, hz⟩ := (isDomainBetween_self_iff (x := x)).mpr hP
  simp [h.maslovIndex_self hxx, hz]

/-- In the presence of a Maslov grading, the periodic Maslov indices vanish at every generator, so
the relative grading is well defined in `ℚ` rather than only modulo them. -/
theorem periodicMaslovIndices_eq_bot (h : H.IsMaslovGrading χ gr) (x : H.Generator) :
    H.periodicMaslovIndices χ x = ⊥ :=
  periodicMaslovIndices_eq_bot_iff.mpr fun _ hP => h.maslovIndex_eq_zero_of_mem_periodicDomains hP x

/-- A Maslov grading computes the relative grading of generators joined by a domain:
`gr(x, y) = gr(x) - gr(y)`. -/
theorem relativeGrading_eq (h : H.IsMaslovGrading χ gr) (hD : H.IsDomainBetween x y D) :
    H.relativeGrading χ x y = gr x - gr y := by
  rw [hD.relativeGrading_eq (maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_forall
    fun _ _ => h.maslovIndex_self) (periodicMaslovIndices_eq_bot_iff.mp
      (h.periodicMaslovIndices_eq_bot x)), h.sub_eq hD]

/-- **The minus differential lowers a Maslov grading by one.** A term `U ^ k y` of the minus
differential of `x` has `gr(x) - gr(y) = 1 - 2 k`. -/
theorem sub_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero (h : H.IsMaslovGrading χ gr)
    {k : ℕ} (hc : (H.minusCoefficient χ x y).coeff k ≠ 0) : gr x - gr y = 1 - 2 * k := by
  obtain ⟨D, hD, hk⟩ := exists_mem_minusDomains_of_coeff_minusCoefficient_ne_zero hc
  obtain ⟨hD, -, hμ⟩ := mem_minusDomains_iff.mp hD
  rw [h.sub_eq hD, hμ, ← Int.cast_sum, hk, Int.cast_natCast]

/-- **The hat differential lowers a Maslov grading by one.** A nonzero coefficient of the hat
differential from `x` to `y` forces `gr(x) - gr(y) = 1`. -/
theorem sub_eq_one_of_hatCoefficient_ne_zero (h : H.IsMaslovGrading χ gr)
    (hc : H.hatCoefficient χ x y ≠ 0) : gr x - gr y = 1 := by
  obtain ⟨D, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero hc
  obtain ⟨hD, hz, -, hμ⟩ := mem_hatDomains_iff.mp hD
  simp [h.sub_eq hD, hμ, hz]

end IsMaslovGrading

/-- **Existence of Maslov gradings.** The generators carry a Maslov grading exactly when every
domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`. Such a grading is obtained by
choosing a generator in each class of generators joined by domains and grading the class by the
relative grading from it. -/
theorem exists_isMaslovGrading_iff :
    (∃ gr, H.IsMaslovGrading χ gr) ↔ ∀ (x : H.Generator) (E : Region → ℤ),
      H.IsDomainBetween x x E → H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ) := by
  refine ⟨fun ⟨_, h⟩ _ _ hE => h.maslovIndex_self hE, fun hself => ?_⟩
  -- The hypotheses of the lemmas on the relative grading.
  have hself' := maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_forall hself
  have hP : ∀ x : H.Generator, ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0 :=
    fun x P hP => by
      obtain ⟨hxx, hz⟩ := (isDomainBetween_self_iff (x := x)).mpr hP
      simp [hself x P hxx, hz]
  -- Being joined by a domain is an equivalence relation on generators.
  let s : Setoid H.Generator :=
    { r := fun x y => ∃ D, H.IsDomainBetween x y D
      iseqv := ⟨fun x => ⟨0, isDomainBetween_zero x⟩, fun ⟨D, hD⟩ => ⟨-D, hD.neg⟩,
        fun ⟨D, hD⟩ ⟨E, hE⟩ => ⟨D + E, hD.add hE⟩⟩ }
  refine ⟨fun y => -H.relativeGrading χ (Quotient.mk s y).out y, ⟨fun {x y D} hD => ?_⟩⟩
  have hxy : (Quotient.mk s x).out = (Quotient.mk s y).out :=
    congrArg Quotient.out (Quotient.sound ⟨D, hD⟩)
  obtain ⟨E, hE⟩ := Quotient.mk_out (s := s) x
  rw [← hxy, ← hD.relativeGrading_eq hself' (hP x), ← hE.relativeGrading_add hself' (hP _) hD]
  ring

/-- When every domain from a generator to itself satisfies the normalization of the relative
grading, as in a singly pointed diagram of a closed surface of genus `n`
(`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton`), the generators carry
a Maslov grading exactly when the periodic Maslov indices vanish at every generator. On a
geometric diagram this is the condition that `c₁` of the spin^c structures of the generators is
torsion. -/
theorem exists_isMaslovGrading_iff_forall_periodicMaslovIndices_eq_bot
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x) :
    (∃ gr, H.IsMaslovGrading χ gr) ↔ ∀ x : H.Generator, H.periodicMaslovIndices χ x = ⊥ := by
  rw [exists_isMaslovGrading_iff]
  refine ⟨fun h x => periodicMaslovIndices_eq_bot_iff.mpr fun P hP => ?_, fun h x E hE =>
    hE.maslovIndex_self_eq_two_mul_sum hself (periodicMaslovIndices_eq_bot_iff.mp (h x))⟩
  obtain ⟨hxx, hz⟩ := (isDomainBetween_self_iff (x := x)).mpr hP
  simp [h x P hxx, hz]

end MaslovGrading

section ChainGrading

variable (H) (gr : H.Generator → ℚ)

/-- The degree-`q` piece of `CF̂` for a grading `gr` of the generators: the chains supported on the
generators of degree `q`. -/
noncomputable def hatGradedPiece (q : ℚ) : Submodule (ZMod 2) (H.Generator →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) {x | gr x = q}

/-- The degree-`q` piece of `CF⁻` for a grading `gr` of the generators: the span of the chains
`U ^ k x` with `gr(x) - 2 k = q`. -/
noncomputable def minusGradedPiece (q : ℚ) : Submodule (ZMod 2) (H.Generator →₀ (ZMod 2)[X]) :=
  Submodule.span (ZMod 2)
    (Finsupp.basis (fun _ : H.Generator => basisMonomials (ZMod 2)) ''
      {i | gr i.1 - 2 * i.2 = q})

/-- The degree-`q` piece of `CF^∞` for a grading `gr` of the generators: the span of the chains
`U ^ k x`, `k ∈ ℤ`, with `gr(x) - 2 k = q`. -/
noncomputable def infinityGradedPiece (q : ℚ) :
    Submodule (ZMod 2) (H.Generator →₀ (ZMod 2)[T;T⁻¹]) :=
  Submodule.span (ZMod 2)
    (Finsupp.basis (fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2)) ''
      {i | gr i.1 - 2 * i.2 = q})

variable {H gr}

/-- A chain of `CF̂` has degree `q` exactly when its generators have degree `q`. -/
theorem mem_hatGradedPiece_iff {q : ℚ} {c : H.Generator →₀ ZMod 2} :
    c ∈ H.hatGradedPiece gr q ↔ ∀ x, c x ≠ 0 → gr x = q := by
  rw [hatGradedPiece, Finsupp.mem_supported']
  simp only [Set.mem_ofPred_eq, not_imp_comm]

/-- A chain of `CF⁻` has degree `q` exactly when each of its terms `U ^ k x` has
`gr(x) - 2 k = q`. -/
theorem mem_minusGradedPiece_iff {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]} :
    c ∈ H.minusGradedPiece gr q ↔ ∀ x (k : ℕ), (c x).coeff k ≠ 0 → gr x - 2 * k = q := by
  rw [minusGradedPiece, Module.Basis.mem_span_image]
  simp [Set.subset_def, basisMonomials, Sigma.forall]

/-- A chain of `CF^∞` has degree `q` exactly when each of its terms `U ^ k x` has
`gr(x) - 2 k = q`. -/
theorem mem_infinityGradedPiece_iff {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ H.infinityGradedPiece gr q ↔ ∀ x (k : ℤ), (c x).coeff k ≠ 0 → gr x - 2 * k = q := by
  rw [infinityGradedPiece, Module.Basis.mem_span_image]
  simp [Set.subset_def, AddMonoidAlgebra.basis, Sigma.forall]

variable (H gr) in
/-- The grading of `CF̂` by a grading `gr` of the generators. -/
noncomputable def hatGrading : InternalGrading (ZMod 2) (H.Generator →₀ ZMod 2) ℚ where
  piece := H.hatGradedPiece gr
  isInternal := by
    convert (Finsupp.basisSingleOne (R := ZMod 2) (ι := H.Generator)).isInternal_span_image_fiber
      gr using 1
    funext q
    rw [hatGradedPiece, Finsupp.supported_eq_span_single, Finsupp.coe_basisSingleOne]

variable (H gr) in
/-- The grading of `CF⁻` by a grading `gr` of the generators, in which `U ^ k x` has degree
`gr(x) - 2 k`. -/
noncomputable def minusGrading : InternalGrading (ZMod 2) (H.Generator →₀ (ZMod 2)[X]) ℚ where
  piece := H.minusGradedPiece gr
  isInternal := (Finsupp.basis fun _ : H.Generator => basisMonomials (ZMod 2))
    |>.isInternal_span_image_fiber fun i => gr i.1 - 2 * i.2

variable (H gr) in
/-- The grading of `CF^∞` by a grading `gr` of the generators, in which `U ^ k x` has degree
`gr(x) - 2 k` for every integer `k`. -/
noncomputable def infinityGrading :
    InternalGrading (ZMod 2) (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ℚ where
  piece := H.infinityGradedPiece gr
  isInternal := (Finsupp.basis fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2))
    |>.isInternal_span_image_fiber fun i => gr i.1 - 2 * i.2

@[simp]
theorem hatGrading_piece : (H.hatGrading gr).piece = H.hatGradedPiece gr :=
  (rfl)

@[simp]
theorem minusGrading_piece : (H.minusGrading gr).piece = H.minusGradedPiece gr :=
  (rfl)

@[simp]
theorem infinityGrading_piece : (H.infinityGrading gr).piece = H.infinityGradedPiece gr :=
  (rfl)

/-- A generator `x` of `CF̂` has degree `gr(x)`. -/
theorem single_mem_hatGradedPiece (x : H.Generator) (a : ZMod 2) :
    Finsupp.single x a ∈ H.hatGradedPiece gr (gr x) := by
  rw [mem_hatGradedPiece_iff]
  intro y hy
  rw [Finsupp.single_apply_ne_zero] at hy
  rw [hy.1]

/-- The chain `U ^ k x` of `CF⁻` has degree `gr(x) - 2 k`. -/
theorem single_X_pow_mem_minusGradedPiece (x : H.Generator) (k : ℕ) :
    Finsupp.single x (X ^ k : (ZMod 2)[X]) ∈ H.minusGradedPiece gr (gr x - 2 * k) := by
  rw [mem_minusGradedPiece_iff]
  intro y j hj
  by_cases hy : y = x
  · subst hy
    simp only [Finsupp.single_eq_same, coeff_X_pow, ne_eq, ite_eq_right_iff,
      Classical.not_imp] at hj
    rw [hj.1]
  · simp [Finsupp.single_eq_of_ne hy] at hj

/-- The chain `U ^ k x` of `CF^∞`, for an integer `k`, has degree `gr(x) - 2 k`. -/
theorem single_T_mem_infinityGradedPiece (x : H.Generator) (k : ℤ) :
    Finsupp.single x (T k : (ZMod 2)[T;T⁻¹]) ∈ H.infinityGradedPiece gr (gr x - 2 * k) := by
  rw [mem_infinityGradedPiece_iff]
  intro y j hj
  by_cases hy : y = x
  · subst hy
    simp only [Finsupp.single_eq_same, T_apply, ne_eq, ite_eq_right_iff,
      Classical.not_imp] at hj
    rw [hj.1]
  · simp [Finsupp.single_eq_of_ne hy] at hj

/-- **`U` lowers the degree of `CF⁻` by two.** -/
theorem X_smul_mem_minusGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.minusGradedPiece gr q) : (X : (ZMod 2)[X]) • c ∈ H.minusGradedPiece gr (q - 2) := by
  rw [mem_minusGradedPiece_iff] at hc ⊢
  intro x k hk
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_one X, coeff_X_pow_mul'] at hk
  split_ifs at hk with h1
  · have := hc x (k - 1) hk
    push_cast [h1] at this
    linarith
  · exact absurd rfl hk

/-- **Multiplication by `U ^ m` shifts the degree of `CF^∞` by `-2 m`**, for every integer `m`. -/
theorem T_smul_mem_infinityGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ H.infinityGradedPiece gr q) (m : ℤ) :
    (T m : (ZMod 2)[T;T⁻¹]) • c ∈ H.infinityGradedPiece gr (q - 2 * m) := by
  rw [mem_infinityGradedPiece_iff] at hc ⊢
  intro x k hk
  rw [Finsupp.smul_apply, smul_eq_mul, T_mul, coeff_mul_T] at hk
  have := hc x (k - m) hk
  push_cast at this
  linarith

/-- **`U` lowers the degree of `CF^∞` by two.** -/
theorem X_smul_mem_infinityGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ H.infinityGradedPiece gr q) :
    (X : (ZMod 2)[X]) • c ∈ H.infinityGradedPiece gr (q - 2) := by
  have hX : (X : (ZMod 2)[X]) • c = (T 1 : (ZMod 2)[T;T⁻¹]) • c := by
    ext x
    simp only [Finsupp.smul_apply, X_smul_eq_T_one_mul, smul_eq_mul]
  simpa [hX] using T_smul_mem_infinityGradedPiece hc 1

/-- **The inclusion of `CF⁻` into `CF^∞` preserves the degree.** -/
theorem mapRange_toLaurent_mem_infinityGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.minusGradedPiece gr q) :
    Finsupp.mapRange toLaurent (map_zero _) c ∈ H.infinityGradedPiece gr q := by
  -- Check the degree on the basis `U ^ k x` of `CF⁻`, which spans its pieces.
  have hhom : LinearMap.IsHomogeneous
      (Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹]))
      (H.minusGradedPiece gr) (H.infinityGradedPiece gr) 0 := by
    refine LinearMap.isHomogeneous_span_iff.2 ?_
    rintro p _ ⟨⟨x, k⟩, hi, rfl⟩
    have hb : Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹])
        (Finsupp.basis (fun _ : H.Generator => basisMonomials (ZMod 2)) ⟨x, k⟩) =
        Finsupp.single x (T k) := by
      simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C_mul_T]
    rw [hb, add_zero, ← hi]
    exact single_T_mem_infinityGradedPiece x k
  have heq : Finsupp.mapRange toLaurent (map_zero _) c =
      Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹]) c := by
    ext x
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  simpa [heq] using hhom.map_mem hc

/-- **Setting `U = 0` preserves the degree**: it maps the degree-`q` piece of `CF⁻` to the
degree-`q` piece of `CF̂`. -/
theorem mapRange_constantCoeff_mem_hatGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.minusGradedPiece gr q) :
    Finsupp.mapRange constantCoeff (map_zero _) c ∈ H.hatGradedPiece gr q := by
  rw [mem_minusGradedPiece_iff] at hc
  rw [mem_hatGradedPiece_iff]
  intro x hx
  rw [Finsupp.mapRange_apply, constantCoeff_apply] at hx
  simpa using hc x 0 hx

/-- The chains of `CF^∞` with polynomial coefficients are spanned by the chains `U ^ k x` with
`k ≥ 0`. -/
private theorem mem_minusLattice_iff_mem_span {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ H.minusLattice ↔ c ∈ Submodule.span (ZMod 2)
      (Finsupp.basis (fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2)) ''
        {i | 0 ≤ i.2}) := by
  rw [mem_minusLattice_iff, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.basis_repr,
    Set.mem_ofPred_eq]
  refine ⟨fun h i hi => ?_, fun h x => ?_⟩
  · by_contra hneg
    exact hi (exists_toLaurent_eq_iff.mp (h i.1) i.2 (not_le.mp hneg))
  · rw [Set.mem_range, exists_toLaurent_eq_iff]
    intro k hk
    by_contra hne
    exact absurd (h ⟨x, k⟩ hne) (not_le.mpr hk)

variable (H gr) in
/-- `CF⁻` is a homogeneous submodule of `CF^∞`: it contains the homogeneous components of each of
its chains. -/
theorem isHomogeneous_minusLattice :
    DirectSum.SetLike.IsHomogeneous (H.infinityGrading gr).piece H.minusLattice := by
  intro q c hc
  rw [mem_minusLattice_iff_mem_span] at hc ⊢
  refine InternalGrading.isHomogeneous_span (H.infinityGrading gr) _ ?_ q hc
  rintro _ ⟨i, -, rfl⟩
  exact ⟨gr i.1 - 2 * i.2, Submodule.subset_span ⟨i, rfl, rfl⟩⟩

variable (H gr) in
/-- The grading of `CF⁺ = CF^∞ / CF⁻` by a grading `gr` of the generators: its degree-`q` piece is
the image of that of `CF^∞`, and the class of `U ^ k x`, `k < 0`, has degree `gr(x) - 2 k`. -/
noncomputable def plusGrading :
    InternalGrading (ZMod 2) ((H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice) ℚ :=
  (H.infinityGrading gr).quotient H.minusLattice (isHomogeneous_minusLattice H gr)

/-- The degree-`q` piece of `CF⁺` is the image of the degree-`q` piece of `CF^∞`. -/
theorem plusGrading_piece (q : ℚ) :
    (H.plusGrading gr).piece q =
      (H.infinityGradedPiece gr q).map (H.minusLattice.mkQ.restrictScalars (ZMod 2)) :=
  InternalGrading.quotient_piece _ _ _ q

/-- A class of `CF⁺` has degree `q` exactly when it is the class of a chain of `CF^∞` of
degree `q`. -/
theorem mem_plusGrading_piece_iff {q : ℚ}
    {y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice} :
    y ∈ (H.plusGrading gr).piece q ↔
      ∃ c ∈ H.infinityGradedPiece gr q, Submodule.Quotient.mk c = y :=
  InternalGrading.mem_quotient_piece_iff _ _ _

/-- The class of a chain of `CF^∞` of degree `q` has degree `q` in `CF⁺`. -/
theorem mk_mem_plusGrading_piece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ H.infinityGradedPiece gr q) :
    (Submodule.Quotient.mk c : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice) ∈
      (H.plusGrading gr).piece q :=
  InternalGrading.mk_mem_quotient_piece _ _ _ hc

/-- **`U` lowers the degree of `CF⁺` by two.** -/
theorem X_smul_mem_plusGrading_piece {q : ℚ}
    {y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice} (hy : y ∈ (H.plusGrading gr).piece q) :
    (X : (ZMod 2)[X]) • y ∈ (H.plusGrading gr).piece (q - 2) := by
  obtain ⟨c, hc, rfl⟩ := mem_plusGrading_piece_iff.mp hy
  rw [← Submodule.Quotient.mk_smul]
  exact mk_mem_plusGrading_piece (X_smul_mem_infinityGradedPiece hc)

/-- **The inclusion of `CF̂` into `CF⁺` raises the degree by two.** It sends a generator `x` to the
class of `U⁻¹ x`, of degree `gr(x) + 2`. -/
theorem isHomogeneous_hatToPlus :
    LinearMap.IsHomogeneous H.hatToPlus (H.hatGradedPiece gr) (H.plusGrading gr).piece 2 := by
  have hspan : H.hatGradedPiece gr = fun q => Submodule.span (ZMod 2)
      ((fun x => Finsupp.single x (1 : ZMod 2)) '' {x | gr x = q}) :=
    funext fun q => Finsupp.supported_eq_span_single _ _
  rw [hspan]
  refine LinearMap.isHomogeneous_span_iff.2 ?_
  rintro p _ ⟨x, hx, rfl⟩
  rw [hatToPlus_single, map_one, one_mul]
  refine mk_mem_plusGrading_piece ?_
  convert single_T_mem_infinityGradedPiece (gr := gr) x (-1) using 2
  simp only [Set.mem_ofPred_eq] at hx
  rw [← hx]
  push_cast
  ring

section Differential

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint]
  {χ : Region → ℤ}

namespace IsMaslovGrading

/-- **The hat differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_hatDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.hatDifferential χ) (H.hatGradedPiece gr) (H.hatGradedPiece gr)
      (-1) := by
  refine LinearMap.isHomogeneous_def.2 fun p c hc => ?_
  rw [mem_hatGradedPiece_iff] at hc ⊢
  intro y hy
  rw [hatDifferential_apply, Finsupp.sum] at hy
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have := h.sub_eq_one_of_hatCoefficient_ne_zero (right_ne_zero_of_mul hx)
  rw [← hc x (left_ne_zero_of_mul hx)]
  linarith

/-- **The minus differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_minusDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.minusDifferential χ) (H.minusGradedPiece gr)
      (H.minusGradedPiece gr) (-1) := by
  -- Check the degree on the basis `U ^ k x` of `CF⁻`, which spans its pieces.
  refine LinearMap.isHomogeneous_span_iff.2 ?_
  rintro p _ ⟨⟨x, k⟩, hi, rfl⟩
  rw [mem_minusGradedPiece_iff]
  intro y j hj
  simp only [Finsupp.coe_basis, coe_basisMonomials, ← X_pow_eq_monomial,
    minusDifferential_single_apply, coeff_X_pow_mul'] at hj
  split_ifs at hj with hkj
  · have := h.sub_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero hj
    push_cast [hkj] at this
    simp only [Set.mem_ofPred_eq] at hi
    linarith
  · exact absurd rfl hj

/-- **The infinity differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_infinityDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.infinityDifferential χ) (H.infinityGradedPiece gr)
      (H.infinityGradedPiece gr) (-1) := by
  -- On the basis, `U ^ k x = U ^ k • x` and the infinity differential of `x` is the minus
  -- differential of `x`.
  refine LinearMap.isHomogeneous_span_iff.2 ?_
  rintro p _ ⟨⟨x, k⟩, hi, rfl⟩
  have hb : Finsupp.basis (fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2)) ⟨x, k⟩ =
      (T k : (ZMod 2)[T;T⁻¹]) •
        Finsupp.mapRange toLaurent (map_zero _) (Finsupp.single x (1 : (ZMod 2)[X])) := by
    rw [Finsupp.mapRange_single, map_one, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [Finsupp.coe_basis, AddMonoidAlgebra.basis_apply, single_eq_C_mul_T, map_one,
      one_mul]
  rw [hb, map_smul, infinityDifferential_mapRange_toLaurent]
  have hx := h.isHomogeneous_minusDifferential.map_mem (single_X_pow_mem_minusGradedPiece x 0)
  rw [pow_zero] at hx
  convert T_smul_mem_infinityGradedPiece (mapRange_toLaurent_mem_infinityGradedPiece hx) k using 2
  simp only [Set.mem_ofPred_eq] at hi
  rw [← hi]
  push_cast
  ring

/-- **The plus differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_plusDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.plusDifferential χ) (H.plusGrading gr).piece
      (H.plusGrading gr).piece (-1) := by
  refine LinearMap.isHomogeneous_def.2 fun p y hy => ?_
  obtain ⟨c, hc, rfl⟩ := mem_plusGrading_piece_iff.mp hy
  rw [plusDifferential_mk]
  exact mk_mem_plusGrading_piece (h.isHomogeneous_infinityDifferential.map_mem hc)

end IsMaslovGrading

end Differential

end ChainGrading

end HeegaardRegionSystem

end TauCeti
