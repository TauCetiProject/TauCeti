/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Row-finite twisted free differential graded left modules

For an arbitrary graded set of generators `P`, a row-finite twisting cocycle specifies each
row as an element of `P →₀ A`. Its free left module is `P →₀ A`, with generator `x` in
cohomological degree `-ind x`. The differential on a homogeneous coefficient is
`D (single x a) = single x (d a) + (-1)^|a| • (a • m x)`.

The Maurer–Cartan equation makes this differential square to zero. Row finiteness alone does
not provide a well-founded attaching filtration, a semi-free model, or a resolution. None of
these properties is asserted here. No one-sidedness condition is required by the differential,
as in `twistedDifferential`; the finite `TwistingCocycle` has this extra condition. For finite
generators, the actual finite-support/function equivalence identifies this construction with
the regular-bimodule twisted differential.

An `A`-linear map out of the free module to a differential graded left module is determined by
the images of the generators, and it commutes with the differentials exactly when it does so on
each generator, that is, when it carries each row `m x` to the differential of the image of `x`.
Likewise a map of degree `-1` out of the free module is the signed extension
`rowFiniteSignedMap` of the images of the generators, and the homotopy law `e = dM ∘ H + H ∘ D`
holds exactly when it holds on each generator. Both laws hold on a vector as soon as they hold on
the generators in its support, which is what allows maps out of the free module to be built one
generator at a time. Dually, a single vector is a valid row for a new generator exactly when it
is a cycle.

## Main definitions and results

* `rowFiniteTotalGrading`: the graded free left module, with its graded scalar action
  (`instGradedSMulRowFiniteTotalGrading`), internal decomposition
  (`instDecompositionRowFiniteTotalGrading`), and homogeneity of `A`-linear maps out of it
  (`isHomogeneous_linearCombination`).
* `rowFiniteSignedMap`: the Koszul-signed extension of images of the generators out of the
  free module, with `rowFiniteSignedMap_congr`, `LinearMap.map_rowFiniteSignedMap` and
  `rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading`, which gives it degree `-1` when each
  generator `x` is sent into degree `-ind x - 1`.
* `rowFiniteTwistedDifferential`: the twisted differential on the free module, characterized on
  homogeneous elementary vectors, with `rowFiniteTwistedDifferential_congr`,
  `rowFiniteTwistedDifferential_zero`, `rowFiniteTwistedDifferential_mapDomain`,
  `rowFiniteTwistedDifferential_mem_supported`,
  `mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero`, and
  `forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain`.
* `linearCombination_rowFiniteTwistedDifferential` and
  `forall_linearCombination_rowFiniteTwistedDifferential_iff`: maps out of the free module
  commute with the differentials exactly when they do so on generators.
* `linearCombination_eq_add_rowFiniteSignedMap` and
  `forall_linearCombination_eq_add_rowFiniteSignedMap_iff`: homotopies out of the free module
  are determined on generators.
* `rowFiniteSignedMap_eq_of_forall_mem_support`: even homotopies out of the free module are
  checked on the generators in the support of a vector.
* `RowFiniteTwistingCocycle`: homogeneous finite rows with the Maurer–Cartan equation, its zero
  cocycle, restriction along an injection (`RowFiniteTwistingCocycle.ofComapDomain` and
  `RowFiniteTwistingCocycle.rowFiniteTwistedDifferential_mapDomain_ofComapDomain`), one-sided
  index properties (`RowFiniteTwistingCocycle.wellFounded_mem_support`,
  `RowFiniteTwistingCocycle.d_m_eq_zero_of_eq_add_one`,
  `RowFiniteTwistingCocycle.sum_subtype_m_mul_m_of_eq_add_two`,
  `RowFiniteTwistingCocycle.indexRowSupport`), and the resulting differential graded left module
  (`RowFiniteTwistingCocycle.isDGLeftModule_rowFiniteTwistedDifferential`).
* `TwistingCocycle.toRowFinite` and
  `linearEquivFunOnFinite_rowFiniteTwistedDifferential`: recovery of the finite prototype
  through `Finsupp.linearEquivFunOnFinite`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open DirectSum

namespace TauCeti

universe uR uA uM uP uP' uQ

/-! ### Total grading -/

section Grading

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [Semiring R] [AddCommMonoid A] [Module R A] (𝒜 : ℤ → Submodule R A) (ind : P → ℤ)

/-- The finite-support total grading, in which a generator `x` has degree `-ind x`. -/
def rowFiniteTotalGrading (n : ℤ) : Submodule R (P →₀ A) :=
  Finsupp.submodule fun x ↦ 𝒜 (n + ind x)

@[simp]
theorem mem_rowFiniteTotalGrading_iff {n : ℤ} {f : P →₀ A} :
    f ∈ rowFiniteTotalGrading 𝒜 ind n ↔ ∀ x, f x ∈ 𝒜 (n + ind x) :=
  (Iff.rfl)

/-- Relabelling the generators along an injective map that preserves their indices preserves
total degrees, and so does its inverse. -/
theorem mapDomain_mem_rowFiniteTotalGrading_iff {P' : Type uP'} {ind' : P' → ℤ} {e : P → P'}
    (he : Function.Injective e) (hind : ∀ x, ind' (e x) = ind x) {n : ℤ} {f : P →₀ A} :
    Finsupp.mapDomain e f ∈ rowFiniteTotalGrading 𝒜 ind' n ↔
      f ∈ rowFiniteTotalGrading 𝒜 ind n := by
  simp only [mem_rowFiniteTotalGrading_iff]
  refine ⟨fun h x ↦ by simpa [Finsupp.mapDomain_apply_of_injective he, hind] using h (e x),
    fun h y ↦ ?_⟩
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    simpa [Finsupp.mapDomain_apply_of_injective he, hind] using h x
  · simp [Finsupp.mapDomain_of_notMem_range _ _ hy]

/-- The generator `x`, with unit coefficient, has total degree `-ind x`. -/
theorem single_one_mem_rowFiniteTotalGrading [One A] [SetLike.GradedOne 𝒜] (x : P) :
    Finsupp.single x (1 : A) ∈ rowFiniteTotalGrading 𝒜 ind (-ind x) := by
  classical
  rw [mem_rowFiniteTotalGrading_iff]
  intro y
  by_cases hxy : x = y
  · subst y
    simpa using SetLike.one_mem_graded 𝒜
  · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]

/-- The actual finite direct-sum/function equivalence preserves total degrees. -/
theorem mem_rowFiniteTotalGrading_iff_twistedTotalGrading [Finite P] (n : ℤ) (f : P →₀ A) :
    f ∈ rowFiniteTotalGrading 𝒜 ind n ↔
      Finsupp.linearEquivFunOnFinite R A P f ∈ twistedTotalGrading 𝒜 ind n := by
  simp

variable [DirectSum.Decomposition 𝒜]

/-- The finite-support total-degree pieces are independent. -/
theorem iSupIndep_rowFiniteTotalGrading : iSupIndep (rowFiniteTotalGrading 𝒜 ind) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro f hf hf'
  have hle : (⨆ (k) (_ : k ≠ n), rowFiniteTotalGrading 𝒜 ind k) ≤
      Finsupp.submodule (fun x ↦ ⨆ (j) (_ : j ≠ n + ind x), 𝒜 j) := by
    refine iSup₂_le fun k hk g hg x ↦ ?_
    exact Submodule.mem_iSup_of_mem (k + ind x)
      (Submodule.mem_iSup_of_mem (fun h ↦ hk (add_right_cancel h)) (hg x))
  have hind := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
  rw [iSupIndep_def] at hind
  ext x
  exact Submodule.disjoint_def.mp (hind (n + ind x)) (f x) (hf x) (hle hf' x)

/-- The finite-support total-degree pieces span the free module. -/
theorem iSup_rowFiniteTotalGrading_eq_top :
    (⨆ n, rowFiniteTotalGrading 𝒜 ind n) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  rw [← Finsupp.sum_single f]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hsum : Finsupp.single x (f x) =
      ∑ q ∈ (decompose 𝒜 (f x)).support, Finsupp.single x (decompose 𝒜 (f x) q : A) := by
    simpa only [map_sum, Finsupp.lsingle_apply] using
      congrArg (Finsupp.lsingle x : A →ₗ[R] P →₀ A)
        (DirectSum.sum_support_decompose 𝒜 (f x)).symm
  rw [hsum]
  refine Submodule.sum_mem _ fun q _ ↦ Submodule.mem_iSup_of_mem (q - ind x) ?_
  intro y
  by_cases hy : x = y
  · subst y
    simp
  · simp [Finsupp.single_eq_of_ne (Ne.symm hy)]

end Grading

section GradingSMul

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [Semiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M]
  {𝒜 : ℤ → Submodule R A} {ℳ : ℤ → Submodule R M} {ind : P → ℤ}

/-- The pointwise left action on `P →₀ M` adds degrees in the total grading, as soon as the action
on `M` does. -/
instance instGradedSMulRowFiniteTotalGrading [SMulZeroClass A M] [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul 𝒜 (rowFiniteTotalGrading ℳ ind) where
  smul_mem := by
    intro i n a f ha hf x
    have := SetLike.GradedSMul.smul_mem ha (hf x)
    simpa only [vadd_eq_add, add_assoc, Finsupp.smul_apply] using this

end GradingSMul

section LinearCombinationGrading

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [Semiring R] [Semiring A] [Module R A] [AddCommMonoid M] [Module R M] [Module A M]
  {𝒜 : ℤ → Submodule R A} {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] {ind : P → ℤ}

/-- An `A`-linear map out of the free module, sending each generator `x` in the support of a
vector of total degree `n` to degree `j - ind x`, sends that vector to degree `n + j`. -/
theorem linearCombination_mem_of_forall_mem_support {g : P → M} {j n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hg : ∀ x ∈ f.support, g x ∈ ℳ (j - ind x)) :
    Finsupp.linearCombination A g f ∈ ℳ (n + j) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  have := SetLike.GradedSMul.smul_mem (hf x) (hg x hx)
  convert this using 2
  simp only [vadd_eq_add]
  ring

/-- An `A`-linear map out of the free module sends total degree `n` to degree `n` as soon as
each generator `x` is sent to degree `-ind x`. -/
theorem linearCombination_mem_of_mem_rowFiniteTotalGrading {g : P → M}
    (hg : ∀ x, g x ∈ ℳ (-ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : Finsupp.linearCombination A g f ∈ ℳ n := by
  simpa using linearCombination_mem_of_forall_mem_support (j := 0) hf fun x _ ↦ by
    simpa using hg x

/-- An `A`-linear map out of the free module sending each generator `x` to degree `-ind x` is
homogeneous of degree zero. -/
theorem isHomogeneous_linearCombination {g : P → M} (hg : ∀ x, g x ∈ ℳ (-ind x)) :
    LinearMap.IsHomogeneous (Finsupp.linearCombination A g) (rowFiniteTotalGrading 𝒜 ind) ℳ 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦ by
    simpa using linearCombination_mem_of_mem_rowFiniteTotalGrading hg hf

end LinearCombinationGrading

section GradingDecomposition

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [Ring R] [AddCommGroup A] [Module R A] (𝒜 : ℤ → Submodule R A) (ind : P → ℤ)
  [DirectSum.Decomposition 𝒜]

/-- The total grading decomposes every finite-support vector, for arbitrary generator sets. -/
noncomputable instance instDecompositionRowFiniteTotalGrading :
    DirectSum.Decomposition (rowFiniteTotalGrading 𝒜 ind) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_rowFiniteTotalGrading 𝒜 ind)
    (iSup_rowFiniteTotalGrading_eq_top 𝒜 ind)).chooseDecomposition

end GradingDecomposition

/-! ### Koszul-signed extension -/

section SignedMap

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Semiring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [DirectSum.Decomposition 𝒜]

section AddCommMonoid

variable {M : Type uM} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The Koszul-signed extension of the images `h x` of the generators to an `R`-linear map out of
the free module. On a coefficient of degree `q`, it sends `single x a` to `(-1)^q • (a • h x)`.
With values in a free module it supplies the twisting terms. With values in a graded module and
each `h x` of degree `-ind x - 1`, it is the map of degree `-1` determined by the images of the
generators (`rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading`), the form of a homotopy out of
the free module. -/
noncomputable def rowFiniteSignedMap (h : P → M) : (P →₀ A) →ₗ[R] M :=
  Finsupp.lsum R fun x ↦
    ((LinearMap.toSpanSingleton A M (h x)).restrictScalars R).comp
      ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1)

/-- Signed row substitution is a finite sum over the support of the input vector. -/
theorem rowFiniteSignedMap_apply (h : P → M) (f : P →₀ A) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f =
      f.sum (fun x a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a • h x) := by
  simp [rowFiniteSignedMap, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply,
    Function.comp_def]

/-- The signed extension on a vector only depends on the images of the generators in its
support. -/
theorem rowFiniteSignedMap_congr {h h' : P → M} {f : P →₀ A}
    (hh : ∀ x ∈ f.support, h x = h' x) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f = rowFiniteSignedMap (𝒜 := 𝒜) h' f := by
  simp only [rowFiniteSignedMap_apply]
  exact Finsupp.sum_congr fun x hx ↦ by rw [hh x hx]

/-- An `A`-linear map commutes with the signed extension: applying it after the signed extension
of `h` is the signed extension of its composite with `h`. -/
theorem _root_.LinearMap.map_rowFiniteSignedMap {M' : Type*} [AddCommMonoid M'] [Module R M']
    [Module A M'] [IsScalarTower R A M'] (φ : M →ₗ[A] M') (h : P → M) (f : P →₀ A) :
    φ (rowFiniteSignedMap (𝒜 := 𝒜) h f) = rowFiniteSignedMap (𝒜 := 𝒜) (φ ∘ h) f := by
  simp [rowFiniteSignedMap_apply, Finsupp.sum, map_sum]

/-- The signed extension is additive in the family of images. -/
theorem rowFiniteSignedMap_add (h h' : P → M) :
    rowFiniteSignedMap (𝒜 := 𝒜) (h + h') =
      rowFiniteSignedMap (𝒜 := 𝒜) h + rowFiniteSignedMap (𝒜 := 𝒜) h' := by
  ext x a
  simp [rowFiniteSignedMap_apply, smul_add]

/-- The signed extension of images of degree `j - ind x`, on the generators in the support of a
vector of total degree `n`, sends that vector to degree `n + j`. -/
theorem rowFiniteSignedMap_mem_of_forall_mem_support {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul 𝒜 ℳ] {ind : P → ℤ} {h : P → M} {j n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hh : ∀ x ∈ f.support, h x ∈ ℳ (j - ind x)) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ ℳ (n + j) := by
  rw [rowFiniteSignedMap_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  have := SetLike.GradedSMul.smul_mem
    (InternalGrading.koszulTwist_mem_ofDecomposition 𝒜 (hf x) 1) (hh x hx)
  convert this using 2
  simp only [vadd_eq_add]
  ring

/-- The signed extension of images of degree `j - ind x` raises total degree by `j`. -/
theorem rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul 𝒜 ℳ] {ind : P → ℤ} {h : P → M} {j : ℤ}
    (hh : ∀ x, h x ∈ ℳ (j - ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ ℳ (n + j) :=
  rowFiniteSignedMap_mem_of_forall_mem_support hf fun x _ ↦ hh x

/-- Rows with shifted degree `k` give a signed map of total degree `k`. -/
theorem rowFiniteSignedMap_mem_totalGrading {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ]
    {ind : P → ℤ} {Q : Type uQ} {indQ : Q → ℤ} (h : P → Q →₀ M)
    {k : ℤ} (hh : ∀ x y, h x y ∈ ℳ (indQ y - ind x + k)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ rowFiniteTotalGrading ℳ indQ (n + k) :=
  rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading (fun x y ↦ by
    convert hh x y using 2
    ring) hf

end AddCommMonoid

section AddCommGroup

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The signed extension is compatible with negation of the family of images. -/
theorem rowFiniteSignedMap_neg (h : P → M) :
    rowFiniteSignedMap (𝒜 := 𝒜) (-h) = -rowFiniteSignedMap (𝒜 := 𝒜) h := by
  ext x a
  simp [rowFiniteSignedMap_apply]

/-- The signed extension is compatible with subtraction of the families of images. -/
theorem rowFiniteSignedMap_sub (h h' : P → M) :
    rowFiniteSignedMap (𝒜 := 𝒜) (h - h') =
      rowFiniteSignedMap (𝒜 := 𝒜) h - rowFiniteSignedMap (𝒜 := 𝒜) h' := by
  rw [sub_eq_add_neg, rowFiniteSignedMap_add, rowFiniteSignedMap_neg, sub_eq_add_neg]

/-- The signed extension evaluated on a homogeneous elementary vector. -/
theorem rowFiniteSignedMap_single (h : P → M) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (Finsupp.single x a) = q.negOnePow • (a • h x) := by
  simp [rowFiniteSignedMap, Finsupp.lsum_single,
    (InternalGrading.ofDecomposition 𝒜).koszulTwist_one_smul_eq_negOnePow_smul
      (by rwa [InternalGrading.ofDecomposition_piece])]

/-- A generator maps to its specified image. -/
@[simp]
theorem rowFiniteSignedMap_single_one [SetLike.GradedOne 𝒜] (h : P → M) (x : P) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (Finsupp.single x 1) = h x := by
  rw [rowFiniteSignedMap_single h x (SetLike.one_mem_graded 𝒜)]
  simp

/-- Signed row extension is graded left-linear of odd degree. -/
theorem rowFiniteSignedMap_smul [SetLike.GradedMul 𝒜] (h : P → M) {q : ℤ} {a : A}
    (ha : a ∈ 𝒜 q) (f : P →₀ A) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (a • f) =
      q.negOnePow • (a • rowFiniteSignedMap (𝒜 := 𝒜) h f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]
  | single x b =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous p b =>
      rw [Finsupp.smul_single, smul_eq_mul,
        rowFiniteSignedMap_single h x (SetLike.GradedMul.mul_mem ha b.property),
        rowFiniteSignedMap_single h x b.property]
      simp [Int.negOnePow_add, mul_smul, smul_comm a p.negOnePow]
    | add b c hb hc => simp only [Finsupp.single_add, smul_add, map_add, hb, hc]

/-- Substituting finite rows `ν` and then applying a signed extension is the signed extension of
the images of the rows. -/
theorem rowFiniteSignedMap_linearCombination [SetLike.GradedMul 𝒜] {Q : Type uQ} (k : Q → M)
    (ν : P → Q →₀ A) (f : P →₀ A) :
    rowFiniteSignedMap (𝒜 := 𝒜) (fun x ↦ rowFiniteSignedMap (𝒜 := 𝒜) k (ν x)) f =
      rowFiniteSignedMap (𝒜 := 𝒜) k (Finsupp.linearCombination A ν f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x b =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous p b =>
      rw [rowFiniteSignedMap_single _ x b.property, Finsupp.linearCombination_single,
        rowFiniteSignedMap_smul k b.property]
    | add b c hb hc => simp only [Finsupp.single_add, map_add, hb, hc]

end AddCommGroup

end SignedMap

/-! ### Twisted differential -/

section Differential

section Semiring

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Semiring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}

/-- The differential of the free left module of a row-finite matrix. The Koszul twist applies
the sign to each coefficient before multiplication into the finite row. -/
noncomputable def rowFiniteTwistedDifferential (m : P → P →₀ A) :
    (P →₀ A) →ₗ[R] (P →₀ A) :=
  Finsupp.mapRange.linearMap d + rowFiniteSignedMap (𝒜 := 𝒜) m

/-- The differential on a finite-support vector is the coefficient differential plus the
finite sum of its Koszul-twisted coefficients acting on the twisting rows. -/
theorem rowFiniteTwistedDifferential_apply (m : P → P →₀ A) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f =
      Finsupp.mapRange.linearMap d f +
        f.sum (fun x a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a • m x) := by
  simp only [rowFiniteTwistedDifferential, LinearMap.add_apply, rowFiniteSignedMap_apply]

/-- The differential on a vector depends only on the rows of the generators in its support. -/
theorem rowFiniteTwistedDifferential_congr {m m' : P → P →₀ A} {f : P →₀ A}
    (hm : ∀ x ∈ f.support, m x = m' x) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f =
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m' f := by
  simp only [rowFiniteTwistedDifferential, LinearMap.add_apply, rowFiniteSignedMap_congr hm]

/-- With zero rows, the differential is the coefficient differential alone. -/
@[simp]
theorem rowFiniteTwistedDifferential_zero :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (0 : P → P →₀ A) =
      Finsupp.mapRange.linearMap d := by
  ext x a y
  simp [rowFiniteTwistedDifferential, rowFiniteSignedMap]

/-- The differential evaluated on a single, not necessarily homogeneous, coefficient. -/
theorem rowFiniteTwistedDifferential_single_koszulTwist (m : P → P →₀ A) (x : P) (c : A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x c) =
      Finsupp.single x (d c) + (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 c • m x := by
  rw [rowFiniteTwistedDifferential_apply, Finsupp.sum_single_index (by simp)]
  simp

/-- **Relabelling generators commutes with the twisted differentials.** If a map `e` of
generators carries the row of each `x` to the row of `e x`, then relabelling vectors along `e`
intertwines the two differentials. -/
theorem rowFiniteTwistedDifferential_mapDomain {P' : Type uP'} (e : P → P') (m : P → P →₀ A)
    {m' : P' → P' →₀ A} (hm : ∀ x, m' (e x) = Finsupp.mapDomain e (m x)) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m' (Finsupp.mapDomain e f) =
      Finsupp.mapDomain e (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp only [Finsupp.mapDomain_add, map_add, hf₁, hf₂]
  | single x c =>
    simp only [Finsupp.mapDomain_single, rowFiniteTwistedDifferential_single_koszulTwist, hm,
      Finsupp.mapDomain_add, Finsupp.mapDomain_smul]

/-- **Generators whose rows stay in `s` span a differential submodule.** If the row of every
generator of `s` only involves generators of `s`, then the twisted differential maps the vectors
supported in `s` to vectors supported in `s`. -/
theorem rowFiniteTwistedDifferential_mem_supported {m : P → P →₀ A} {s : Set P}
    (hm : ∀ x ∈ s, m x ∈ Finsupp.supported A A s) {f : P →₀ A}
    (hf : f ∈ Finsupp.supported A A s) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f ∈ Finsupp.supported A A s := by
  rw [rowFiniteTwistedDifferential_apply]
  refine Submodule.add_mem _ ?_
    (Submodule.sum_mem _ fun x hx ↦ Submodule.smul_mem _ _ (hm x (hf hx)))
  rw [Finsupp.mapRange.linearMap_apply, Finsupp.mem_supported]
  exact (Finset.coe_subset.2 Finsupp.support_mapRange).trans ((Finsupp.mem_supported A f).1 hf)

/-- The differential increases total degree by one whenever `d` has degree one and each row entry
`m x y` has degree `ind y - ind x + 1`. -/
theorem rowFiniteTwistedDifferential_mem_totalGrading [SetLike.GradedSMul 𝒜 𝒜] {ind : P → ℤ}
    (m : P → P →₀ A) (hd : LinearMap.IsHomogeneous d 𝒜 𝒜 1)
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    {n : ℤ} {f : P →₀ A} (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f ∈
      rowFiniteTotalGrading 𝒜 ind (n + 1) := by
  rw [rowFiniteTwistedDifferential, LinearMap.add_apply]
  refine add_mem ?_ (rowFiniteSignedMap_mem_totalGrading m hm hf)
  intro y
  simpa only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    add_right_comm] using hd.map_mem (hf y)

/-- **Relative boundaries along a relabelling of generators.** Let an injection `φ : P → P'`
intertwine the differentials of the rows `mP` and `m` and the images `cP` and `c`. Then every
relative cycle of `cP` with target in `N` is a relative boundary with target in `N` exactly when
the same holds for the vectors of `P' →₀ A` supported on the range of `φ`, with primitives
supported there too. -/
theorem forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain
    {M : Type uM} [AddCommMonoid M] [Module A M] {dM : M → M} {P' : Type uP'}
    (φ : P → P') (hφ : Function.Injective φ) {mP : P → P →₀ A} {m : P' → P' →₀ A}
    (hD : ∀ f, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.mapDomain φ f) =
      Finsupp.mapDomain φ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP f))
    {cP : P → M} {c : P' → M} (hc : ∀ x, c (φ x) = cP x) (N : Set M) :
    (∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP u = 0 →
      Finsupp.linearCombination A cP u = dM w → w ∈ N → ∃ (u' : P →₀ A) (w' : M), w' ∈ N ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP u' = u ∧
          Finsupp.linearCombination A cP u' + dM w' = w) ↔
    ∀ (f : P' →₀ A) (w : M), ↑f.support ⊆ Set.range φ →
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f = 0 →
        Finsupp.linearCombination A c f = dM w → w ∈ N → ∃ (f' : P' →₀ A) (w' : M),
          ↑f'.support ⊆ Set.range φ ∧ w' ∈ N ∧
            rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f' = f ∧
              Finsupp.linearCombination A c f' + dM w' = w := by
  classical
  have hsupp (u : P →₀ A) : ↑(Finsupp.mapDomain φ u).support ⊆ Set.range φ := fun y hy ↦ by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact ⟨x, rfl⟩
  have hL (u : P →₀ A) :
      Finsupp.linearCombination A c (Finsupp.mapDomain φ u) = Finsupp.linearCombination A cP u := by
    rw [Finsupp.linearCombination_mapDomain]
    exact congrArg (Finsupp.linearCombination A · u) (funext hc)
  have hD₀ (u : P →₀ A) :
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.mapDomain φ u) = 0 ↔
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP u = 0 := by
    rw [hD, ← Finsupp.mapDomain_zero (f := φ), (Finsupp.mapDomain_injective hφ).eq_iff]
  refine ⟨fun H f w hf hDf hfw hw ↦ ?_, fun H u w hDu huw hw ↦ ?_⟩
  · rw [← Finsupp.mapDomain_comapDomain φ hφ f hf] at hDf hfw ⊢
    obtain ⟨u', w', hw', hDu', huw'⟩ := H _ w ((hD₀ _).1 hDf) (by rwa [← hL]) hw
    exact ⟨Finsupp.mapDomain φ u', w', hsupp u', hw', by rw [hD, hDu'], by rwa [hL]⟩
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ :=
      H (Finsupp.mapDomain φ u) w (hsupp u) ((hD₀ u).2 hDu) (by rwa [hL]) hw
    rw [← Finsupp.mapDomain_comapDomain φ hφ f' hf'] at hDf' hfw'
    exact ⟨_, w', hw', Finsupp.mapDomain_injective hφ (by rw [← hD, hDf']), by rwa [← hL]⟩

end Semiring

section Ring

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}

/-- The differential evaluated on a single homogeneous coefficient. -/
theorem rowFiniteTwistedDifferential_single (m : P → P →₀ A) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x a) =
      Finsupp.single x (d a) + q.negOnePow • (a • m x) := by
  simp [rowFiniteTwistedDifferential, rowFiniteSignedMap_single m x ha]

/-- The differential of a vector whose coefficient at each `y` has degree `deg y` is the
coefficient differential plus the finite sum of the signed coefficients acting on the rows. -/
theorem rowFiniteTwistedDifferential_apply_of_mem (m : P → P →₀ A) {deg : P → ℤ}
    {r : P →₀ A} (hr : ∀ y, r y ∈ 𝒜 (deg y)) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m r =
      Finsupp.mapRange.linearMap d r + r.sum (fun y a ↦ (deg y).negOnePow • (a • m y)) := by
  rw [rowFiniteTwistedDifferential_apply]
  congr 1
  exact Finsupp.sum_congr fun y _ ↦
    (InternalGrading.ofDecomposition 𝒜).koszulTwist_one_smul_eq_negOnePow_smul
      (by rw [InternalGrading.ofDecomposition_piece]; exact hr y) (m y)

/-- The twisting equation of a single row says exactly that the row is a cycle of the twisted
differential: a vector `r` of total degree `1 - k`, read as the prospective row of a generator of
index `k`, satisfies `d r = ∑_y (-1)^(k - ind y) r_y · m_y` exactly when `D r = 0`. -/
theorem mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero {ind : P → ℤ}
    (m : P → P →₀ A) {k : ℤ} {r : P →₀ A} (hr : ∀ y, r y ∈ 𝒜 (ind y - k + 1)) :
    Finsupp.mapRange.linearMap d r = r.sum (fun y a ↦ (k - ind y).negOnePow • (a • m y)) ↔
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m r = 0 := by
  have hD : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m r =
      Finsupp.mapRange.linearMap d r - r.sum (fun y a ↦ (k - ind y).negOnePow • (a • m y)) := by
    rw [rowFiniteTwistedDifferential_apply_of_mem m hr, sub_eq_add_neg, Finsupp.sum,
      Finsupp.sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [show ind y - k + 1 = -(k - ind y) + 1 by ring, Int.negOnePow_succ, Int.negOnePow_neg,
      Units.neg_smul]
  rw [hD, sub_eq_zero]

end Ring

section Algebra

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- The graded Leibniz rule for a homogeneous algebra element and any finite-support vector. -/
theorem rowFiniteTwistedDifferential_smul (m : P → P →₀ A) (h : IsDGAlgebra 𝒜 d)
    {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (a • f) =
      d a • f + p.negOnePow •
        (a • rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  have hd : Finsupp.mapRange.linearMap d (a • f) =
      d a • f + p.negOnePow • (a • Finsupp.mapRange.linearMap d f) := by
    ext x
    simpa only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using h.leibniz ha (f x)
  simp only [rowFiniteTwistedDifferential, LinearMap.add_apply, hd,
    rowFiniteSignedMap_smul m ha, smul_add, add_assoc]

end Algebra

end Differential

/-! ### Maps and homotopies out of the free module -/

section Maps

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

/-- On the elementary vectors of a generator, an `A`-linear map out of the free module commutes
with the differentials as soon as it does so on that generator. -/
private theorem linearCombination_rowFiniteTwistedDifferential_single
    (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A) {g : P → M} {x : P}
    (hg : Finsupp.linearCombination A g (m x) = dM (g x)) (a : A) :
    Finsupp.linearCombination A g
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x a)) =
      dM (Finsupp.linearCombination A g (Finsupp.single x a)) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    rw [rowFiniteTwistedDifferential_single m x a.property, map_add,
      Finsupp.linearCombination_single, Finsupp.linearCombination_single,
      hM.leibniz a.property, ← hg]
    simp only [map_smul, LinearMap.map_smul_of_tower]
  | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

/-- **Maps out of the free module commute with the differentials generator by generator.** If an
`A`-linear map sends the row `m x` of each generator `x` in the support of a vector `f` to the
differential of the image of `x`, then it commutes with the differentials on `f`, by the DG
Leibniz rule. -/
theorem linearCombination_rowFiniteTwistedDifferential_of_forall_mem_support
    (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A) {g : P → M} {f : P →₀ A}
    (hg : ∀ x ∈ f.support, Finsupp.linearCombination A g (m x) = dM (g x)) :
    Finsupp.linearCombination A g (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      dM (Finsupp.linearCombination A g f) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun x hx ↦
    linearCombination_rowFiniteTwistedDifferential_single hM m (hg x hx) (f x)

/-- **Maps out of the free module are determined on generators.** If an `A`-linear map sends
the differential of each generator, its row `m x`, to the differential of the image of the
generator, then it commutes with the differentials on the whole free module, by the DG Leibniz
rule. -/
theorem linearCombination_rowFiniteTwistedDifferential (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) {g : P → M} (hg : ∀ x, Finsupp.linearCombination A g (m x) = dM (g x))
    (f : P →₀ A) :
    Finsupp.linearCombination A g (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      dM (Finsupp.linearCombination A g f) :=
  linearCombination_rowFiniteTwistedDifferential_of_forall_mem_support hM m fun x _ ↦ hg x

/-- An `A`-linear map out of the free module commutes with the differentials exactly when it does
so on the generators. -/
theorem forall_linearCombination_rowFiniteTwistedDifferential_iff (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) (g : P → M) :
    (∀ f, Finsupp.linearCombination A g (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
        dM (Finsupp.linearCombination A g f)) ↔
      ∀ x, Finsupp.linearCombination A g (m x) = dM (g x) := by
  refine ⟨fun H x ↦ ?_, fun hg ↦ linearCombination_rowFiniteTwistedDifferential hM m hg⟩
  simpa [rowFiniteTwistedDifferential_single m x (SetLike.one_mem_graded 𝒜),
    h.map_one_eq_zero] using H (Finsupp.single x 1)

/-- On the elementary vectors of a generator, the homotopy law holds as soon as it holds on
that generator. -/
private theorem linearCombination_single_eq_add_rowFiniteSignedMap
    (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A) {e k : P → M} {x : P}
    (hx : e x = dM (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m x)) (a : A) :
    Finsupp.linearCombination A e (Finsupp.single x a) =
      dM (rowFiniteSignedMap (𝒜 := 𝒜) k (Finsupp.single x a)) +
        rowFiniteSignedMap (𝒜 := 𝒜) k
          (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x a)) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    rw [rowFiniteTwistedDifferential_single m x a.property, map_add,
      rowFiniteSignedMap_single k x a.property,
      rowFiniteSignedMap_single k x (h.map_mem a.property),
      LinearMap.map_smul_of_tower dM,
      LinearMap.map_smul_of_tower (rowFiniteSignedMap (𝒜 := 𝒜) k),
      rowFiniteSignedMap_smul k a.property,
      hM.leibniz a.property, Finsupp.linearCombination_single, hx]
    simp only [smul_add, smul_smul, Int.units_mul_self, one_smul, Int.negOnePow_succ,
      Units.neg_smul]
    abel
  | add a b ha hb =>
    simp only [Finsupp.single_add, map_add, ha, hb]
    abel

/-- **Homotopies out of the free module are checked generator by generator.** Let `k` give the
images of the generators under a map of degree `-1`, extended with the Koszul sign by
`rowFiniteSignedMap`. If `e x = dM (k x) + H (m x)` for each generator `x` in the support of a
vector `f`, then the map `e` out of the free module agrees on `f` with `dM ∘ H + H ∘ D`. -/
theorem linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support
    (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A) {e k : P → M} {f : P →₀ A}
    (hk : ∀ x ∈ f.support, e x = dM (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m x)) :
    Finsupp.linearCombination A e f = dM (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
      rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum, map_sum, map_sum, map_sum, map_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x hx ↦
    linearCombination_single_eq_add_rowFiniteSignedMap hM m (hk x hx) (f x)

/-- **Homotopies out of the free module are determined on generators.** If
`e x = dM (k x) + H (m x)` on every generator, where `H` is the signed extension of `k`, then
`e = dM ∘ H + H ∘ D` on the whole free module. -/
theorem linearCombination_eq_add_rowFiniteSignedMap (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) {e k : P → M}
    (hk : ∀ x, e x = dM (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m x)) (f : P →₀ A) :
    Finsupp.linearCombination A e f = dM (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
      rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) :=
  linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support hM m fun x _ ↦ hk x

/-- A map `e` out of the free module is `dM ∘ H + H ∘ D`, for the signed extension `H` of `k`,
exactly when this holds on the generators. -/
theorem forall_linearCombination_eq_add_rowFiniteSignedMap_iff (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) (e k : P → M) :
    (∀ f, Finsupp.linearCombination A e f = dM (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
        rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f)) ↔
      ∀ x, e x = dM (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m x) := by
  refine ⟨fun H x ↦ ?_, linearCombination_eq_add_rowFiniteSignedMap hM m⟩
  simpa [rowFiniteTwistedDifferential_single m x (SetLike.one_mem_graded 𝒜),
    h.map_one_eq_zero] using H (Finsupp.single x 1)

/-- **Even homotopies out of the free module are checked generator by generator.** For `L` the
`A`-linear extension of `l : P → M`, the map `dM ∘ L - L ∘ D` is graded left-linear of odd degree.
So if it agrees on each generator in the support of `f` with the signed extension of
`θ : P → M`, then it agrees with it on `f`. -/
theorem rowFiniteSignedMap_eq_of_forall_mem_support (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) {l θ : P → M} {f : P →₀ A}
    (hθ : ∀ x ∈ f.support, θ x = dM (l x) - Finsupp.linearCombination A l (m x)) :
    rowFiniteSignedMap (𝒜 := 𝒜) θ f = dM (Finsupp.linearCombination A l f) -
      Finsupp.linearCombination A l (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum]
  simp only [map_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  generalize f x = c
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    rw [rowFiniteSignedMap_single θ x a.property,
      rowFiniteTwistedDifferential_single m x a.property,
      Finsupp.linearCombination_single, hM.leibniz a.property, hθ x hx]
    simp only [map_add, LinearMap.map_smul_of_tower, map_smul, Finsupp.linearCombination_single,
      smul_sub]
    abel
  | add a b ha hb =>
    simp only [Finsupp.single_add, map_add]
    rw [ha, hb]
    abel

end Maps

/-! ### Row-finite twisting cocycles -/

section Cocycle

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A] in
/-- A homogeneous, row-finite matrix satisfying the Maurer–Cartan equation. One-sidedness is
not required to construct its differential graded left module. -/
structure RowFiniteTwistingCocycle (𝒜 : ℤ → Submodule R A) (d : A →ₗ[R] A)
    (P : Type uP) (ind : P → ℤ) where
  /-- The finite row of coefficients issuing from a generator. -/
  m : P → P →₀ A
  /-- The coefficient of `y` in the row of `x` has the shifted degree. -/
  mem_graded : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)
  /-- The Maurer–Cartan identity as an equality of finite-support rows. -/
  twisting : ∀ x, Finsupp.mapRange.linearMap d (m x) =
    (m x).sum fun y a ↦ (ind x - ind y).negOnePow • (a • m y)

namespace RowFiniteTwistingCocycle

section Basic

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A} {ind : P → ℤ}

@[ext]
theorem ext {m₁ m₂ : RowFiniteTwistingCocycle 𝒜 d P ind}
    (h : ∀ x y, m₁.m x y = m₂.m x y) : m₁ = m₂ := by
  cases m₁; cases m₂
  congr
  funext x
  exact Finsupp.ext (h x)

/-- The zero twisting cocycle. Its free module carries the coefficient differential alone, so it
is the direct sum of shifted copies of the algebra, one for each generator. -/
instance : Zero (RowFiniteTwistingCocycle 𝒜 d P ind) where
  zero :=
    { m := 0
      mem_graded := fun _ _ ↦ zero_mem _
      twisting := fun _ ↦ by simp }

@[simp]
theorem zero_m : (0 : RowFiniteTwistingCocycle 𝒜 d P ind).m = 0 :=
  (rfl)

/-- The row of a generator `x`, its differential, lies in total degree `1 - ind x`. -/
theorem m_mem_rowFiniteTotalGrading (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x : P) :
    m.m x ∈ rowFiniteTotalGrading 𝒜 ind (1 - ind x) :=
  (mem_rowFiniteTotalGrading_iff 𝒜 ind).mpr fun y ↦ by
    convert m.mem_graded x y using 2
    ring

/-- A one-sided cocycle, with `m x y = 0` whenever `ind x ≤ ind y`, whose generator indices are
bounded below, is **semi-free**: the relation `y ∈ (m.m x).support`, saying that `y` occurs in the
row of `x`, is well-founded, since it strictly lowers the index. -/
theorem wellFounded_mem_support (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) :
    WellFounded fun y x ↦ y ∈ (m.m x).support :=
  Subrelation.wf (r := InvImage (· < ·) fun x ↦ (ind x - p₀).toNat)
    (fun {y x} hy ↦ by
      have hlt : ind y < ind x := by
        by_contra h
        exact Finsupp.mem_support_iff.mp hy (hm x y (not_lt.mp h))
      have := hp₀ y
      dsimp only [InvImage]
      omega)
    (InvImage.wf _ wellFounded_lt)

/-- The twisting equation evaluated at a generator `z`: the differential of the entry `m x z` is
the signed sum, over the row of `x`, of the products `m x y * m y z`. -/
theorem twisting_apply (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x z : P) :
    d (m.m x z) = (m.m x).sum fun y a ↦ (ind x - ind y).negOnePow • (a * m.m y z) := by
  simpa [Finsupp.sum_apply] using DFunLike.congr_fun (m.twisting x) z

/-- The entries between generators whose indices differ by one have degree zero. -/
theorem m_mem_zero_of_eq_add_one (m : RowFiniteTwistingCocycle 𝒜 d P ind) {x y : P}
    (hxy : ind x = ind y + 1) : m.m x y ∈ 𝒜 0 := by
  have h := m.mem_graded x y
  rwa [show ind y - ind x + 1 = 0 by omega] at h

/-- The entries between generators whose indices differ by two have degree `-1`. -/
theorem m_mem_neg_one_of_eq_add_two (m : RowFiniteTwistingCocycle 𝒜 d P ind) {x y : P}
    (hxy : ind x = ind y + 2) : m.m x y ∈ 𝒜 (-1) := by
  have h := m.mem_graded x y
  rwa [show ind y - ind x + 1 = -1 by omega] at h

/-- For a one-sided cocycle, a product of two consecutive entries vanishes unless the middle
generator has strictly intermediate index. -/
theorem m_mul_m_eq_zero_of_not_lt_lt (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y z : P}
    (h : ¬(ind z < ind y ∧ ind y < ind x)) : m.m x y * m.m y z = 0 := by
  rcases le_or_gt (ind x) (ind y) with hxy | hxy
  · rw [hm x y hxy, zero_mul]
  · rw [hm y z (by omega), mul_zero]

/-- For a one-sided cocycle, the entries between generators whose indices differ by one are
cycles: no generator has an index strictly between theirs. -/
theorem d_m_eq_zero_of_eq_add_one (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y : P} (hxy : ind x = ind y + 1) :
    d (m.m x y) = 0 := by
  rw [m.twisting_apply]
  exact Finset.sum_eq_zero fun z _ ↦ by
    dsimp only
    rw [m.m_mul_m_eq_zero_of_not_lt_lt hm (by omega), smul_zero]

/-- `m_mem_zero_of_eq_add_one` for generators given as elements of the subtypes of index `q + 1`
and `q`. -/
theorem m_mem_zero_of_subtype (m : RowFiniteTwistingCocycle 𝒜 d P ind) {q : ℤ}
    (x : {x : P // ind x = q + 1}) (y : {y : P // ind y = q}) : m.m x y ∈ 𝒜 0 :=
  m.m_mem_zero_of_eq_add_one (by rw [x.property, y.property])

/-- `d_m_eq_zero_of_eq_add_one` for generators given as elements of the subtypes of index `q + 1`
and `q`. -/
theorem d_m_eq_zero_of_subtype (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {q : ℤ} (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q}) : d (m.m x y) = 0 :=
  m.d_m_eq_zero_of_eq_add_one hm (by rw [x.property, y.property])

/-- **The twisting equation at index difference two**, for a one-sided cocycle: between
generators `x` and `z` whose indices differ by two, the sum of the products `m x y * m y z` over
any finite set of generators `y` of the intermediate index containing those occurring in the row
of `x` is minus the differential of `m x z`. -/
theorem sum_subtype_m_mul_m_of_eq_add_two (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x z : P} (q : ℤ) (hx : ind x = q + 1 + 1)
    (hz : ind z = q) (T : Finset {y : P // ind y = q + 1}) (hT : ∀ y ∉ T, m.m x y = 0) :
    ∑ y ∈ T, m.m x y * m.m y z = -d (m.m x z) := by
  classical
  set S := (m.m x).support.filter fun y ↦ ind y = q + 1
  -- Both sums are the sum over the generators of index `q + 1` occurring in the row of `x`.
  have hTS : ∑ y ∈ T, m.m x y * m.m y z = ∑ y ∈ S, m.m x y * m.m y z := by
    have hmap := Finset.sum_map T (Function.Embedding.subtype fun y : P ↦ ind y = q + 1)
      fun y ↦ m.m x y * m.m y z
    simp only [Function.Embedding.coe_subtype] at hmap
    rw [← hmap]
    refine (Finset.sum_subset (fun y hy ↦ ?_) fun y hy hyS ↦ ?_).symm
    · obtain ⟨hy_supp, hy_ind⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_map.mpr ⟨⟨y, hy_ind⟩, ?_, rfl⟩
      by_contra hyT
      exact Finsupp.mem_support_iff.mp hy_supp (hT ⟨y, hy_ind⟩ hyT)
    · obtain ⟨y', -, rfl⟩ := Finset.mem_map.mp hy
      simp only [Function.Embedding.coe_subtype] at hyS ⊢
      have hy' : (y' : P) ∉ (m.m x).support := fun h ↦ hyS (Finset.mem_filter.mpr ⟨h, y'.property⟩)
      rw [Finsupp.notMem_support_iff.mp hy', zero_mul]
  rw [hTS, m.twisting_apply, Finsupp.sum, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs with hy
  · rw [show ind x - ind y = 1 by omega]
    simp
  · rw [m.m_mul_m_eq_zero_of_not_lt_lt hm (by omega), smul_zero, neg_zero]

/-- The finite set of generators `y` of index `q` occurring in the row of a generator `x`. -/
noncomputable def indexRowSupport (m : RowFiniteTwistingCocycle 𝒜 d P ind) (q : ℤ) (x : P) :
    Finset {y : P // ind y = q} :=
  ((m.m x).subtypeDomain fun y ↦ ind y = q).support

@[simp]
theorem mem_indexRowSupport_iff (m : RowFiniteTwistingCocycle 𝒜 d P ind) {q : ℤ} {x : P}
    {y : {y : P // ind y = q}} : y ∈ m.indexRowSupport q x ↔ m.m x y ≠ 0 := by
  simp [indexRowSupport]

end Basic

section Differential

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}

/-- Let an injection `e : P → P'` pick out generators whose rows `m (e x)` only involve generators
in the range of `e`. Then relabelling along `e` intertwines the differential of the rows read back
on `P` with that of the original rows. -/
private theorem rowFiniteTwistedDifferential_mapDomain_comapDomain {P' : Type uP'}
    (m : P' → P' →₀ A) (e : P → P') (he : Function.Injective e)
    (hsupp : ∀ x, ↑(m (e x)).support ⊆ Set.range e) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.mapDomain e f) =
      Finsupp.mapDomain e (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d)
        (fun x ↦ Finsupp.comapDomain e (m (e x)) he.injOn) f) :=
  rowFiniteTwistedDifferential_mapDomain e _
    (fun x ↦ (Finsupp.mapDomain_comapDomain _ he _ (hsupp x)).symm) f

/-- **Restricting rows to a row-closed set of generators.** Let an injection `e : P → P'` pick
out generators whose rows `m (e x)` only involve generators in the range of `e`, are homogeneous
for the indices `ind` on `P`, and are cycles of the differential of `m`. Then the rows read back
on `P` form a row-finite twisting cocycle. The rows of the other generators of `P'` are
irrelevant, and need not form a cocycle. -/
noncomputable def ofComapDomain {P' : Type uP'} (m : P' → P' →₀ A) (e : P → P')
    (he : Function.Injective e) (hsupp : ∀ x, ↑(m (e x)).support ⊆ Set.range e)
    (hgr : ∀ x y, m (e x) (e y) ∈ 𝒜 (ind y - ind x + 1))
    (htw : ∀ x, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (m (e x)) = 0) :
    RowFiniteTwistingCocycle 𝒜 d P ind where
  m x := Finsupp.comapDomain e (m (e x)) he.injOn
  mem_graded x y := hgr x y
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _ fun y ↦ hgr x y).2 ?_
    apply Finsupp.mapDomain_injective he
    rw [← rowFiniteTwistedDifferential_mapDomain_comapDomain m e he hsupp,
      Finsupp.mapDomain_comapDomain _ he _ (hsupp x), Finsupp.mapDomain_zero]
    exact htw x

section OfComapDomain

variable {P' : Type uP'} {m : P' → P' →₀ A} {e : P → P'} {he : Function.Injective e}
  {hsupp : ∀ x, ↑(m (e x)).support ⊆ Set.range e}
  {hgr : ∀ x y, m (e x) (e y) ∈ 𝒜 (ind y - ind x + 1)}
  {htw : ∀ x, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (m (e x)) = 0}

/-- A restricted row is the original row read back along `e`. -/
theorem ofComapDomain_m (x : P) :
    (ofComapDomain m e he hsupp hgr htw).m x = Finsupp.comapDomain e (m (e x)) he.injOn :=
  (rfl)

/-- The coefficients of a restricted row are those of the original row. -/
@[simp]
theorem ofComapDomain_m_apply (x y : P) :
    (ofComapDomain m e he hsupp hgr htw).m x y = m (e x) (e y) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- Relabelling a restricted row along `e` recovers the original row. -/
@[simp]
theorem mapDomain_ofComapDomain_m (x : P) :
    Finsupp.mapDomain e ((ofComapDomain m e he hsupp hgr htw).m x) = m (e x) :=
  Finsupp.mapDomain_comapDomain _ he _ (hsupp x)

/-- Relabelling along `e` intertwines the differential of the restricted cocycle with that of
the original rows. -/
theorem rowFiniteTwistedDifferential_mapDomain_ofComapDomain (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.mapDomain e f) =
      Finsupp.mapDomain e
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (ofComapDomain m e he hsupp hgr htw).m
          f) :=
  rowFiniteTwistedDifferential_mapDomain_comapDomain m e he hsupp f

end OfComapDomain

/-- The Maurer–Cartan equation says that every differential row is a cycle. -/
theorem differential_row (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (m.m x) = 0 :=
  (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero m.m (m.mem_graded x)).mp
    (m.twisting x)

end Differential

section DGModule

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}

/-- A generator has differential equal to its specified finite row. -/
theorem differential_single_one (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (h : IsDGAlgebra 𝒜 d) (x : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (Finsupp.single x 1) = m.m x := by
  rw [rowFiniteTwistedDifferential_single m.m x (SetLike.one_mem_graded 𝒜)]
  simp [h.map_one_eq_zero]

/-- The differential squares to zero, first on generators and then by the DG Leibniz rule. -/
theorem differential_sq_zero (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (h : IsDGAlgebra 𝒜 d) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m
      (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) = 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [← Finsupp.smul_single_one x (a : A),
        rowFiniteTwistedDifferential_smul m.m h a.property, map_add,
        rowFiniteTwistedDifferential_smul m.m h (h.map_mem a.property),
        LinearMap.map_smul_of_tower,
        rowFiniteTwistedDifferential_smul m.m h a.property,
        differential_single_one m h x, differential_row m x, h.sq_zero]
      simp [Int.negOnePow_succ, Units.neg_smul]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb, add_zero]

/-- A row-finite Maurer–Cartan cocycle defines a differential graded free left module. -/
theorem isDGLeftModule_rowFiniteTwistedDifferential (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (h : IsDGAlgebra 𝒜 d) :
    IsDGLeftModule h (rowFiniteTotalGrading 𝒜 ind)
      (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
    rowFiniteTwistedDifferential_mem_totalGrading m.m
      (LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha) m.mem_graded hf
  sq_zero := m.differential_sq_zero h
  leibniz ha f := rowFiniteTwistedDifferential_smul m.m h ha f

end DGModule

end RowFiniteTwistingCocycle

end Cocycle

/-! ### Comparison with finite twisting cocycles -/

section Finite

/-- The actual finite direct-sum/function equivalence intertwines the differentials. On the
function side the existing twisted differential uses the regular bimodule right action. -/
theorem linearEquivFunOnFinite_rowFiniteTwistedDifferential
    {R : Type uR} {A : Type uA} {P : Type uP} [CommRing R] [Semiring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A} [Fintype P]
    (m : P → P →₀ A) (f : P →₀ A) :
    Finsupp.linearEquivFunOnFinite R A P
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      twistedDifferential (fun x y ↦ m x y) 𝒜 d
        (Finsupp.linearEquivFunOnFinite R A P f) := by
  ext y
  simp [rowFiniteTwistedDifferential_apply, Finsupp.sum_fintype, twistedDifferential_apply,
    MulOpposite.smul_eq_mul_unop]

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A} {ind : P → ℤ} [Fintype P]

/-- A finite twisting cocycle, viewed as finite-support Maurer–Cartan rows. Its extra
one-sidedness condition is not needed by the free differential graded module construction. -/
noncomputable def toRowFinite (m : TwistingCocycle 𝒜 d P ind) :
    RowFiniteTwistingCocycle 𝒜 d P ind where
  m x := (Finsupp.linearEquivFunOnFinite R A P).symm (m.m x)
  mem_graded x y := m.mem_graded x y
  twisting x := by
    ext y
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.sum_fintype _ _ (by intro z; simp)]
    exact m.twisting x y

@[simp]
theorem toRowFinite_m (m : TwistingCocycle 𝒜 d P ind) (x y : P) :
    m.toRowFinite.m x y = m.m x y :=
  (rfl)

end TwistingCocycle

end Finite

end TauCeti
