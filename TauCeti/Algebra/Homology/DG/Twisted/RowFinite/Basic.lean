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

* `RowFiniteTwistingCocycle`: homogeneous finite rows with the Maurer–Cartan equation.
* `RowFiniteTwistingCocycle.wellFounded_mem_support_of_lt`: a cocycle whose rows strictly lower
  a well-founded stage of the generators is semi-free, its row relation `y ∈ (m.m x).support`
  being well-founded; `RowFiniteTwistingCocycle.wellFounded_mem_support` is the case of a
  one-sided cocycle with generator indices bounded below.
* `RowFiniteTwistingCocycle.d_m_eq_zero_of_eq_add_one` and
  `RowFiniteTwistingCocycle.sum_subtype_m_mul_m_of_eq_add_two`: for a one-sided cocycle, the
  entries between generators of adjacent indices are cycles of degree zero, and the twisting
  equation at index difference two is a finite sum over the intermediate generators.
* `RowFiniteTwistingCocycle.indexRowSupport`: the finite set of generators of a given index
  occurring in the row of a generator.
* `rowFiniteTotalGrading` and `rowFiniteTwistedDifferential`: the graded free left module
  and its differential, characterized on homogeneous elementary vectors.
* `RowFiniteTwistingCocycle.isDGLeftModule_rowFiniteTwistedDifferential`: the differential
  graded left module laws, with square-zero derived from the row equation and DG Leibniz rule.
* `rowFiniteTwistedDifferential_mapDomain`: relabelling generators compatibly with the rows
  commutes with the differentials.
* `rowFiniteTwistedDifferential_congr`: the differential of a vector depends only on the rows of
  the generators in its support.
* `RowFiniteTwistingCocycle.ofComapDomain`: the restriction of rows to an injectively labelled
  set of generators closed under taking rows, with
  `RowFiniteTwistingCocycle.rowFiniteTwistedDifferential_mapDomain_ofComapDomain` relating the two
  differentials, and its case `RowFiniteTwistingCocycle.comap` for the rows of a cocycle.
* `mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero`: the Maurer–Cartan equation of a
  row is the vanishing of its twisted differential.
* The zero cocycle, whose differential is the coefficient differential alone
  (`rowFiniteTwistedDifferential_zero`).
* `forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain`: relative cycles being
  relative boundaries is invariant under relabelling the generators along an injection.
* `linearCombination_rowFiniteTwistedDifferential` and
  `forall_linearCombination_rowFiniteTwistedDifferential_iff`: maps out of the free module
  commute with the differentials exactly when they do so on generators.
* `isHomogeneous_linearCombination`: a map out of the free module sending each generator to the
  matching degree is homogeneous of degree zero.
* `rowFiniteSignedMap`: the Koszul-signed extension of images of the generators out of the
  free module, with `rowFiniteSignedMap_congr`, `LinearMap.map_rowFiniteSignedMap` and
  `rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading`, which gives it degree `-1` when each
  generator `x` is sent into degree `-ind x - 1`.
* `linearCombination_eq_add_rowFiniteSignedMap` and
  `forall_linearCombination_eq_add_rowFiniteSignedMap_iff`: homotopies out of the free module
  are determined on generators.
* `rowFiniteSignedMap_eq_of_forall_mem_support`: even homotopies out of the free module are
  checked on the generators in the support of a vector.
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

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}

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

omit [GradedAlgebra 𝒜] in
@[ext]
theorem ext {m₁ m₂ : RowFiniteTwistingCocycle 𝒜 d P ind}
    (h : ∀ x y, m₁.m x y = m₂.m x y) : m₁ = m₂ := by
  cases m₁; cases m₂
  congr
  funext x
  exact Finsupp.ext (h x)

omit [GradedAlgebra 𝒜] in
/-- The zero twisting cocycle. Its free module carries the coefficient differential alone, so it
is the direct sum of shifted copies of the algebra, one for each generator. -/
instance : Zero (RowFiniteTwistingCocycle 𝒜 d P ind) where
  zero :=
    { m := 0
      mem_graded := fun _ _ ↦ zero_mem _
      twisting := fun _ ↦ by simp }

omit [GradedAlgebra 𝒜] in
@[simp]
theorem zero_m : (0 : RowFiniteTwistingCocycle 𝒜 d P ind).m = 0 :=
  (rfl)

omit [GradedAlgebra 𝒜] in
/-- The row of a generator `x`, its differential, lies in total degree `1 - ind x`. -/
theorem m_mem_rowFiniteTotalGrading (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x : P) :
    m.m x ∈ rowFiniteTotalGrading 𝒜 ind (1 - ind x) :=
  (mem_rowFiniteTotalGrading_iff 𝒜 ind).mpr fun y ↦ by
    convert m.mem_graded x y using 2
    ring

omit [GradedAlgebra 𝒜] in
/-- A cocycle whose rows strictly lower a well-founded stage of the generators, as when each
generator is attached along a cycle of generators of earlier stages, is **semi-free**: the relation
`y ∈ (m.m x).support`, saying that `y` occurs in the row of `x`, is well-founded. -/
theorem wellFounded_mem_support_of_lt {α : Type*} [LT α] [WellFoundedLT α]
    (m : RowFiniteTwistingCocycle 𝒜 d P ind) (st : P → α)
    (hst : ∀ x y, y ∈ (m.m x).support → st y < st x) :
    WellFounded fun y x ↦ y ∈ (m.m x).support :=
  Subrelation.wf (r := InvImage (· < ·) st) (fun {y x} hy ↦ hst x y hy)
    (InvImage.wf _ wellFounded_lt)

omit [GradedAlgebra 𝒜] in
/-- A one-sided cocycle, with `m x y = 0` whenever `ind x ≤ ind y`, whose generator indices are
bounded below, is **semi-free**: the relation `y ∈ (m.m x).support`, saying that `y` occurs in the
row of `x`, is well-founded, since it strictly lowers the index. -/
theorem wellFounded_mem_support (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) :
    WellFounded fun y x ↦ y ∈ (m.m x).support :=
  m.wellFounded_mem_support_of_lt (fun x ↦ (ind x - p₀).toNat) fun x y hy ↦ by
    have hlt : ind y < ind x := by
      by_contra h
      exact Finsupp.mem_support_iff.mp hy (hm x y (not_lt.mp h))
    have := hp₀ y
    omega

omit [GradedAlgebra 𝒜] in
/-- The twisting equation evaluated at a generator `z`: the differential of the entry `m x z` is
the signed sum, over the row of `x`, of the products `m x y * m y z`. -/
theorem twisting_apply (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x z : P) :
    d (m.m x z) = (m.m x).sum fun y a ↦ (ind x - ind y).negOnePow • (a * m.m y z) := by
  simpa [Finsupp.sum_apply] using DFunLike.congr_fun (m.twisting x) z

omit [GradedAlgebra 𝒜] in
/-- The entries between generators whose indices differ by one have degree zero. -/
theorem m_mem_zero_of_eq_add_one (m : RowFiniteTwistingCocycle 𝒜 d P ind) {x y : P}
    (hxy : ind x = ind y + 1) : m.m x y ∈ 𝒜 0 := by
  have h := m.mem_graded x y
  rwa [show ind y - ind x + 1 = 0 by omega] at h

omit [GradedAlgebra 𝒜] in
/-- The entries between generators whose indices differ by two have degree `-1`. -/
theorem m_mem_neg_one_of_eq_add_two (m : RowFiniteTwistingCocycle 𝒜 d P ind) {x y : P}
    (hxy : ind x = ind y + 2) : m.m x y ∈ 𝒜 (-1) := by
  have h := m.mem_graded x y
  rwa [show ind y - ind x + 1 = -1 by omega] at h

omit [GradedAlgebra 𝒜] in
/-- For a one-sided cocycle, a product of two consecutive entries vanishes unless the middle
generator has strictly intermediate index. -/
theorem m_mul_m_eq_zero_of_not_lt_lt (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y z : P}
    (h : ¬(ind z < ind y ∧ ind y < ind x)) : m.m x y * m.m y z = 0 := by
  rcases le_or_gt (ind x) (ind y) with hxy | hxy
  · rw [hm x y hxy, zero_mul]
  · rw [hm y z (by omega), mul_zero]

omit [GradedAlgebra 𝒜] in
/-- For a one-sided cocycle, the entries between generators whose indices differ by one are
cycles: no generator has an index strictly between theirs. -/
theorem d_m_eq_zero_of_eq_add_one (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y : P} (hxy : ind x = ind y + 1) :
    d (m.m x y) = 0 := by
  rw [m.twisting_apply]
  exact Finset.sum_eq_zero fun z _ ↦ by
    dsimp only
    rw [m.m_mul_m_eq_zero_of_not_lt_lt hm (by omega), smul_zero]

omit [GradedAlgebra 𝒜] in
/-- `m_mem_zero_of_eq_add_one` for generators given as elements of the subtypes of index `q + 1`
and `q`. -/
theorem m_mem_zero_of_subtype (m : RowFiniteTwistingCocycle 𝒜 d P ind) {q : ℤ}
    (x : {x : P // ind x = q + 1}) (y : {y : P // ind y = q}) : m.m x y ∈ 𝒜 0 :=
  m.m_mem_zero_of_eq_add_one (by rw [x.2, y.2])

omit [GradedAlgebra 𝒜] in
/-- `d_m_eq_zero_of_eq_add_one` for generators given as elements of the subtypes of index `q + 1`
and `q`. -/
theorem d_m_eq_zero_of_subtype (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {q : ℤ} (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q}) : d (m.m x y) = 0 :=
  m.d_m_eq_zero_of_eq_add_one hm (by rw [x.2, y.2])

omit [GradedAlgebra 𝒜] in
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
    refine (Finset.sum_subset Finset.subset_union_left ?_).trans
      (Finset.sum_subset Finset.subset_union_right ?_).symm
    · intro y hy hyT
      have hyS : y ∈ S := by simpa [hyT] using hy
      have hy' : ind y = q + 1 := (Finset.mem_filter.1 hyS).2
      rw [hT ⟨y, hy'⟩ fun h ↦ hyT (Finset.mem_map_of_mem _ h), zero_mul]
    · intro y hy hyS
      obtain ⟨y', -, rfl⟩ := Finset.mem_map.1 ((Finset.mem_union.1 hy).resolve_right hyS)
      have hy : (y' : P) ∉ (m.m x).support := fun h ↦ hyS (Finset.mem_filter.2 ⟨h, y'.2⟩)
      simp only [Function.Embedding.coe_subtype]
      rw [Finsupp.notMem_support_iff.1 hy, zero_mul]
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

omit [GradedAlgebra 𝒜] in
@[simp]
theorem mem_indexRowSupport_iff (m : RowFiniteTwistingCocycle 𝒜 d P ind) {q : ℤ} {x : P}
    {y : {y : P // ind y = q}} : y ∈ m.indexRowSupport q x ↔ m.m x y ≠ 0 := by
  simp [indexRowSupport]

end RowFiniteTwistingCocycle

section SignedMap

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

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
  classical
  simp [rowFiniteSignedMap, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply,
    Function.comp_def]

/-- The signed extension evaluated on a homogeneous elementary vector. -/
theorem rowFiniteSignedMap_single (h : P → M) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (Finsupp.single x a) = q.negOnePow • (a • h x) := by
  classical
  simp [rowFiniteSignedMap, Finsupp.lsum_single,
    koszulTwist_one_eq_negOnePow_smul (R := R) ha]

/-- A generator maps to its specified image. -/
@[simp]
theorem rowFiniteSignedMap_single_one (h : P → M) (x : P) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (Finsupp.single x 1) = h x := by
  rw [rowFiniteSignedMap_single h x (SetLike.one_mem_graded 𝒜)]
  simp

/-- Signed row extension is graded left-linear of odd degree. -/
theorem rowFiniteSignedMap_smul (h : P → M) {q : ℤ} {a : A}
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
        rowFiniteSignedMap_single h x (SetLike.GradedMul.mul_mem ha b.2),
        rowFiniteSignedMap_single h x b.2]
      simp [Int.negOnePow_add, mul_smul, smul_comm a p.negOnePow]
    | add b c hb hc => simp only [Finsupp.single_add, smul_add, map_add, hb, hc]

/-- The signed extension on a vector only depends on the images of the generators in its
support. -/
theorem rowFiniteSignedMap_congr {h h' : P → M} {f : P →₀ A}
    (hh : ∀ x ∈ f.support, h x = h' x) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f = rowFiniteSignedMap (𝒜 := 𝒜) h' f := by
  simp only [rowFiniteSignedMap_apply]
  exact Finsupp.sum_congr fun x hx ↦ by rw [hh x hx]

/-- An `A`-linear map commutes with the signed extension: applying it after the signed extension
of `h` is the signed extension of its composite with `h`. -/
theorem _root_.LinearMap.map_rowFiniteSignedMap {M' : Type*} [AddCommGroup M'] [Module R M']
    [Module A M'] [IsScalarTower R A M'] (φ : M →ₗ[A] M') (h : P → M) (f : P →₀ A) :
    φ (rowFiniteSignedMap (𝒜 := 𝒜) h f) = rowFiniteSignedMap (𝒜 := 𝒜) (φ ∘ h) f := by
  simp [rowFiniteSignedMap_apply, Finsupp.sum, map_sum]

/-- The signed extension is additive in the family of images. -/
theorem rowFiniteSignedMap_add (h h' : P → M) :
    rowFiniteSignedMap (𝒜 := 𝒜) (h + h') =
      rowFiniteSignedMap (𝒜 := 𝒜) h + rowFiniteSignedMap (𝒜 := 𝒜) h' := by
  ext x a
  simp [rowFiniteSignedMap_apply, smul_add]

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

/-- Substituting finite rows `ν` and then applying a signed extension is the signed extension of
the images of the rows. -/
theorem rowFiniteSignedMap_linearCombination {Q : Type uQ} (k : Q → M) (ν : P → Q →₀ A)
    (f : P →₀ A) :
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
      rw [rowFiniteSignedMap_single _ x b.2, Finsupp.linearCombination_single,
        rowFiniteSignedMap_smul k b.2]
    | add b c hb hc => simp only [Finsupp.single_add, map_add, hb, hc]

end SignedMap

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

/-- The differential evaluated on a single homogeneous coefficient. -/
theorem rowFiniteTwistedDifferential_single (m : P → P →₀ A) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x a) =
      Finsupp.single x (d a) + q.negOnePow • (a • m x) := by
  classical
  simp [rowFiniteTwistedDifferential, rowFiniteSignedMap_single m x ha]

/-- The differential evaluated on a single, not necessarily homogeneous, coefficient. -/
theorem rowFiniteTwistedDifferential_single_koszulTwist (m : P → P →₀ A) (x : P) (c : A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x c) =
      Finsupp.single x (d c) + (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 c • m x := by
  rw [rowFiniteTwistedDifferential_apply, Finsupp.sum_single_index (by simp)]
  simp

/-- The differential of a vector whose coefficient at each `y` has degree `deg y` is the
coefficient differential plus the finite sum of the signed coefficients acting on the rows. -/
theorem rowFiniteTwistedDifferential_apply_of_mem (m : P → P →₀ A) {deg : P → ℤ}
    {r : P →₀ A} (hr : ∀ y, r y ∈ 𝒜 (deg y)) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m r =
      Finsupp.mapRange.linearMap d r + r.sum (fun y a ↦ (deg y).negOnePow • (a • m y)) := by
  rw [rowFiniteTwistedDifferential_apply]
  congr 1
  exact Finsupp.sum_congr fun y _ ↦ by
    rw [koszulTwist_one_eq_negOnePow_smul (R := R) (hr y), smul_assoc]

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

/-- The finite-support total grading is compatible with the pointwise left algebra action. -/
instance instGradedSMulRowFiniteTotalGrading :
    SetLike.GradedSMul 𝒜 (rowFiniteTotalGrading 𝒜 ind) where
  smul_mem := by
    intro i n a f ha hf x
    have := SetLike.GradedMul.mul_mem ha (hf x)
    simpa only [vadd_eq_add, add_assoc, Finsupp.smul_apply, smul_eq_mul] using this

/-- The twisting equation of a single row says exactly that the row is a cycle of the twisted
differential: a vector `r` of total degree `1 - k`, read as the prospective row of a generator of
index `k`, satisfies `d r = ∑_y (-1)^(k - ind y) r_y · m_y` exactly when `D r = 0`. -/
theorem mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero (m : P → P →₀ A) {k : ℤ}
    {r : P →₀ A} (hr : ∀ y, r y ∈ 𝒜 (ind y - k + 1)) :
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

namespace RowFiniteTwistingCocycle

variable {P' : Type uP'} {ind' : P' → ℤ}

/-- **Restricting rows to a row-closed set of generators.** Let an injection `e : P → P'` pick
out generators whose rows `m (e x)` only involve generators in the range of `e`, are homogeneous
for the indices `ind` on `P`, and are cycles of the differential of `m`. Then the rows read back
on `P` form a row-finite twisting cocycle. The rows of the other generators of `P'` are
irrelevant, and need not form a cocycle; `RowFiniteTwistingCocycle.comap` is the case of the
rows of a cocycle on `P'`. -/
noncomputable def ofComapDomain (m : P' → P' →₀ A) (e : P → P') (he : Function.Injective e)
    (hsupp : ∀ x, ↑(m (e x)).support ⊆ Set.range e)
    (hgr : ∀ x y, m (e x) (e y) ∈ 𝒜 (ind y - ind x + 1))
    (htw : ∀ x, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (m (e x)) = 0) :
    RowFiniteTwistingCocycle 𝒜 d P ind where
  m x := Finsupp.comapDomain e (m (e x)) he.injOn
  mem_graded x y := hgr x y
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _ fun y ↦ hgr x y).2 ?_
    apply Finsupp.mapDomain_injective he
    rw [← rowFiniteTwistedDifferential_mapDomain e _ (m' := m)
        (fun x ↦ (Finsupp.mapDomain_comapDomain _ he _ (hsupp x)).symm),
      Finsupp.mapDomain_comapDomain _ he _ (hsupp x), Finsupp.mapDomain_zero]
    exact htw x

section OfComapDomain

variable {m : P' → P' →₀ A} {e : P → P'} {he : Function.Injective e}
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
  rowFiniteTwistedDifferential_mapDomain e _ (fun x ↦ mapDomain_ofComapDomain_m x |>.symm) f

end OfComapDomain

/-- **Restricting a cocycle to a row-closed set of generators.** For an injection `e : P → P'`
whose range contains the rows of its generators, the rows of `m` on the generators `e x`, read
back on `P`, form a row-finite twisting cocycle. -/
noncomputable def comap (m : RowFiniteTwistingCocycle 𝒜 d P' ind') (e : P → P')
    (he : Function.Injective e) (hsupp : ∀ x, ↑(m.m (e x)).support ⊆ Set.range e) :
    RowFiniteTwistingCocycle 𝒜 d P fun x ↦ ind' (e x) :=
  ofComapDomain m.m e he hsupp (fun x y ↦ m.mem_graded (e x) (e y)) fun x ↦
    (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _ (m.mem_graded (e x))).1
      (m.twisting (e x))

section Comap

variable (m : RowFiniteTwistingCocycle 𝒜 d P' ind') {e : P → P'} {he : Function.Injective e}
  {hsupp : ∀ x, ↑(m.m (e x)).support ⊆ Set.range e}

/-- A restricted row is the original row read back along `e`. -/
theorem comap_m (x : P) :
    (m.comap e he hsupp).m x = Finsupp.comapDomain e (m.m (e x)) he.injOn :=
  (rfl)

/-- The coefficients of a restricted row are those of the original row. -/
@[simp]
theorem comap_m_apply (x y : P) : (m.comap e he hsupp).m x y = m.m (e x) (e y) :=
  ofComapDomain_m_apply x y

/-- Relabelling a restricted row along `e` recovers the original row. -/
@[simp]
theorem mapDomain_comap_m (x : P) :
    Finsupp.mapDomain e ((m.comap e he hsupp).m x) = m.m (e x) :=
  mapDomain_ofComapDomain_m x

/-- Relabelling along `e` intertwines the differential of the restricted cocycle with that of
`m`. -/
theorem rowFiniteTwistedDifferential_mapDomain_comap (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (Finsupp.mapDomain e f) =
      Finsupp.mapDomain e
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.comap e he hsupp).m f) :=
  rowFiniteTwistedDifferential_mapDomain_ofComapDomain f

end Comap

end RowFiniteTwistingCocycle

section Maps

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ]

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- An `A`-linear map out of the free module, sending each generator `x` in the support of a
vector of total degree `n` to degree `j - ind x`, sends that vector to degree `n + j`. -/
theorem linearCombination_mem_of_forall_mem_support {g : P → M} {j n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hg : ∀ x ∈ f.support, g x ∈ ℳ (j - ind x)) :
    Finsupp.linearCombination A g f ∈ ℳ (n + j) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  have := SetLike.GradedSMul.smul_mem (hf x) (hg x hx)
  convert this using 2
  simp only [vadd_eq_add]
  ring

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- An `A`-linear map out of the free module sends total degree `n` to degree `n` as soon as
each generator `x` is sent to degree `-ind x`. -/
theorem linearCombination_mem_of_mem_rowFiniteTotalGrading {g : P → M}
    (hg : ∀ x, g x ∈ ℳ (-ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : Finsupp.linearCombination A g f ∈ ℳ n := by
  simpa using linearCombination_mem_of_forall_mem_support (j := 0) hf fun x _ ↦ by
    simpa using hg x

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- An `A`-linear map out of the free module sending each generator `x` to degree `-ind x` is
homogeneous of degree zero. -/
theorem isHomogeneous_linearCombination {g : P → M} (hg : ∀ x, g x ∈ ℳ (-ind x)) :
    LinearMap.IsHomogeneous (Finsupp.linearCombination A g) (rowFiniteTotalGrading 𝒜 ind) ℳ 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦ by
    simpa using linearCombination_mem_of_mem_rowFiniteTotalGrading hg hf

/-- The signed extension of images of degree `j - ind x`, on the generators in the support of a
vector of total degree `n`, sends that vector to degree `n + j`. -/
theorem rowFiniteSignedMap_mem_of_forall_mem_support {h : P → M} {j n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hh : ∀ x ∈ f.support, h x ∈ ℳ (j - ind x)) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ ℳ (n + j) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  rw [rowFiniteSignedMap_single h x (hf x)]
  apply Submodule.smul_of_tower_mem
  have := SetLike.GradedSMul.smul_mem (hf x) (hh x hx)
  convert this using 2
  simp only [vadd_eq_add]
  ring

/-- The signed extension of images of degree `j - ind x` raises total degree by `j`. -/
theorem rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading {h : P → M} {j : ℤ}
    (hh : ∀ x, h x ∈ ℳ (j - ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ ℳ (n + j) :=
  rowFiniteSignedMap_mem_of_forall_mem_support hf fun x _ ↦ hh x

variable [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

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
    rw [rowFiniteTwistedDifferential_single m x a.2, map_add, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, hM.leibniz a.2, ← hg]
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
    rw [rowFiniteTwistedDifferential_single m x a.2, map_add,
      rowFiniteSignedMap_single k x a.2, rowFiniteSignedMap_single k x (h.map_mem a.2),
      LinearMap.map_smul_of_tower dM,
      LinearMap.map_smul_of_tower (rowFiniteSignedMap (𝒜 := 𝒜) k), rowFiniteSignedMap_smul k a.2,
      hM.leibniz a.2, Finsupp.linearCombination_single, hx]
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
    (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A) {e k : P → M}
    {f : P →₀ A}
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
    rw [rowFiniteSignedMap_single θ x a.2, rowFiniteTwistedDifferential_single m x a.2,
      Finsupp.linearCombination_single, hM.leibniz a.2, hθ x hx]
    simp only [map_add, LinearMap.map_smul_of_tower, map_smul, Finsupp.linearCombination_single,
      smul_sub]
    abel
  | add a b ha hb =>
    simp only [Finsupp.single_add, map_add]
    rw [ha, hb]
    abel

omit [IsScalarTower R A M] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] in
/-- **Relative boundaries along a relabelling of generators.** Let an injection `φ : P → P'`
intertwine the differentials of the rows `mP` and `m` and the images `cP` and `c`. Then every
relative cycle of `cP` with target in `N` is a relative boundary with target in `N` exactly when
the same holds for the vectors of `P' →₀ A` supported on the range of `φ`, with primitives
supported there too. -/
theorem forall_exists_rowFiniteTwistedDifferential_eq_iff_of_mapDomain {P' : Type uP'}
    (φ : P → P') (hφ : Function.Injective φ) {mP : P → P →₀ A} {m : P' → P' →₀ A}
    (hD : ∀ f, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.mapDomain φ f) =
      Finsupp.mapDomain φ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP f))
    {cP : P → M} {c : P' → M} (hc : ∀ x, c (φ x) = cP x) (N : Submodule A M) :
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
  have hrange {f : P' →₀ A} (hf : ↑f.support ⊆ Set.range φ) : ∃ u, Finsupp.mapDomain φ u = f :=
    ⟨Finsupp.comapDomain φ f hφ.injOn, Finsupp.mapDomain_comapDomain _ hφ _ hf⟩
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
  refine ⟨fun H f w hf hDf hfw hw ↦ ?_, fun H u w hu huw hw ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := hrange hf
    obtain ⟨u', w', hw', hDu', huw'⟩ := H u w ((hD₀ u).1 hDf) (by rwa [← hL]) hw
    exact ⟨Finsupp.mapDomain φ u', w', hsupp u', hw', by rw [hD, hDu'], by rwa [hL]⟩
  · obtain ⟨f', w', hf', hw', hDf', hfw'⟩ :=
      H (Finsupp.mapDomain φ u) w (hsupp u) ((hD₀ u).2 hu) (by rwa [hL]) hw
    obtain ⟨u', rfl⟩ := hrange hf'
    exact ⟨u', w', hw', Finsupp.mapDomain_injective hφ (by rw [← hD, hDf']), by rwa [← hL]⟩

end Maps

/-- Rows with shifted degree `k` give a signed map of total degree `k`. -/
theorem rowFiniteSignedMap_mem_totalGrading {Q : Type uQ} {indQ : Q → ℤ} (h : P → Q →₀ A)
    {k : ℤ} (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - ind x + k)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ rowFiniteTotalGrading 𝒜 indQ (n + k) :=
  rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading (fun x y ↦ by
    convert hh x y using 2
    ring) hf

section DifferentialLaws

variable (m : P → P →₀ A) (h : IsDGAlgebra 𝒜 d)

include h

/-- The graded Leibniz rule for a homogeneous algebra element and any finite-support vector. -/
theorem rowFiniteTwistedDifferential_smul {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (a • f) =
      d a • f + p.negOnePow •
        (a • rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  classical
  have hd : Finsupp.mapRange.linearMap d (a • f) =
      d a • f + p.negOnePow • (a • Finsupp.mapRange.linearMap d f) := by
    ext x
    simpa only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using h.leibniz ha (f x)
  simp only [rowFiniteTwistedDifferential, LinearMap.add_apply, hd,
    rowFiniteSignedMap_smul m ha, smul_add, add_assoc]

/-- The differential increases total degree by one. -/
theorem rowFiniteTwistedDifferential_mem_totalGrading
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    {n : ℤ} {f : P →₀ A} (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f ∈
      rowFiniteTotalGrading 𝒜 ind (n + 1) := by
  classical
  rw [rowFiniteTwistedDifferential, LinearMap.add_apply]
  refine add_mem ?_ (rowFiniteSignedMap_mem_totalGrading m hm hf)
  intro y
  simpa only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    add_right_comm] using h.map_mem (hf y)

end DifferentialLaws

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 d P ind) (h : IsDGAlgebra 𝒜 d)

include h

/-- A generator has differential equal to its specified finite row. -/
theorem differential_single_one (x : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (Finsupp.single x 1) = m.m x := by
  rw [rowFiniteTwistedDifferential_single m.m x (SetLike.one_mem_graded 𝒜)]
  simp [h.map_one_eq_zero]

omit h in
/-- The Maurer–Cartan equation says that every differential row is a cycle. -/
theorem differential_row (x : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (m.m x) = 0 :=
  (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero m.m (m.mem_graded x)).mp
    (m.twisting x)

/-- The differential squares to zero, first on generators and then by the DG Leibniz rule. -/
theorem differential_sq_zero (f : P →₀ A) :
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
        rowFiniteTwistedDifferential_smul m.m h a.2, map_add,
        rowFiniteTwistedDifferential_smul m.m h (h.map_mem a.2),
        LinearMap.map_smul_of_tower,
        rowFiniteTwistedDifferential_smul m.m h a.2,
        differential_single_one m h x, differential_row m x, h.sq_zero]
      simp [Int.negOnePow_succ, Units.neg_smul]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb, add_zero]

/-- A row-finite Maurer–Cartan cocycle defines a differential graded free left module. -/
theorem isDGLeftModule_rowFiniteTwistedDifferential :
    IsDGLeftModule h (rowFiniteTotalGrading 𝒜 ind)
      (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
    rowFiniteTwistedDifferential_mem_totalGrading m.m h m.mem_graded hf
  sq_zero := m.differential_sq_zero h
  leibniz ha f := rowFiniteTwistedDifferential_smul m.m h ha f

end RowFiniteTwistingCocycle

section Finite

variable [Fintype P]

/-- The actual finite direct-sum/function equivalence intertwines the differentials. On the
function side the existing twisted differential uses the regular bimodule right action. -/
theorem linearEquivFunOnFinite_rowFiniteTwistedDifferential (m : P → P →₀ A) (f : P →₀ A) :
    Finsupp.linearEquivFunOnFinite R A P
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      twistedDifferential (fun x y ↦ m x y) 𝒜 d
        (Finsupp.linearEquivFunOnFinite R A P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [rowFiniteTwistedDifferential_single m x a.2,
        Finsupp.linearEquivFunOnFinite_single,
        twistedDifferential_single (fun x y ↦ m x y) d x a.2]
      ext y
      simp [Finsupp.single_apply, Pi.single_apply, MulOpposite.smul_eq_mul_unop, eq_comm]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

namespace TwistingCocycle

omit [GradedAlgebra 𝒜] in
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

omit [GradedAlgebra 𝒜] in
@[simp]
theorem toRowFinite_m (m : TwistingCocycle 𝒜 d P ind) (x y : P) :
    m.toRowFinite.m x y = m.m x y :=
  (rfl)

end TwistingCocycle

end Finite

end TauCeti
