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
Likewise a homotopy out of the free module is the signed extension `rowFiniteSignedMap` of the
images of the generators, and the homotopy identity holds as soon as it holds on generators.
Both extensions are local: on a given vector they only need the identity on the generators in
its support, which is what allows maps to be built one generator at a time.
Dually, a single vector is a valid row for a new generator exactly when it is a cycle.

## Main definitions and results

* `RowFiniteTwistingCocycle`: homogeneous finite rows with the Maurer–Cartan equation.
* `rowFiniteTotalGrading` and `rowFiniteTwistedDifferential`: the graded free left module
  and its differential, characterized on homogeneous elementary vectors.
* `RowFiniteTwistingCocycle.isDGLeftModule_rowFiniteTwistedDifferential`: the differential
  graded left module laws, with square-zero derived from the row equation and DG Leibniz rule.
* `rowFiniteTwistedDifferential_mapDomain`: relabelling generators compatibly with the rows
  commutes with the differentials.
* `mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero`: the Maurer–Cartan equation of a
  row is the vanishing of its twisted differential.
* The zero cocycle, whose differential is the coefficient differential alone
  (`rowFiniteTwistedDifferential_zero`).
* `linearCombination_rowFiniteTwistedDifferential` and
  `forall_linearCombination_rowFiniteTwistedDifferential_iff`: maps out of the free module
  commute with the differentials exactly when they do so on generators.
* `linearCombination_rowFiniteTwistedDifferential_of_mem_support`,
  `rowFiniteSignedMap_differential_of_mem_support` and `rowFiniteSignedMap_eq_of_mem_support`:
  the chain-map, odd homotopy and even homotopy identities on a vector, from the identities on
  the generators in its support.
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

universe uR uA uM uN uP uP' uQ

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

end RowFiniteTwistingCocycle

section SignedMap

variable {Q : Type uQ} {indQ : Q → ℤ}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- The signed extension of a family of images of the generators. On a coefficient of degree `q`,
it sends `single x a` to `(-1)^q • (a • h x)`. It supplies both twisting terms, with values in the
free module itself, and homotopy terms, with values in any left module. -/
noncomputable def rowFiniteSignedMap (h : P → N) : (P →₀ A) →ₗ[R] N :=
  Finsupp.lsum R fun x ↦
    ((LinearMap.toSpanSingleton A N (h x)).restrictScalars R).comp
      ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1)

/-- Signed row substitution is a finite sum over the support of the input vector. -/
theorem rowFiniteSignedMap_apply (h : P → N) (f : P →₀ A) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f =
      f.sum (fun x a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a • h x) := by
  classical
  simp [rowFiniteSignedMap, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply,
    Function.comp_def]

/-- The signed extension only depends on the images of the generators in the support of its
argument. -/
theorem rowFiniteSignedMap_congr {h h' : P → N} {f : P →₀ A}
    (hh : ∀ x ∈ f.support, h x = h' x) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f = rowFiniteSignedMap (𝒜 := 𝒜) h' f := by
  rw [rowFiniteSignedMap_apply, rowFiniteSignedMap_apply]
  exact Finsupp.sum_congr fun x hx ↦ by rw [hh x hx]

/-- The signed extension evaluated on a homogeneous elementary vector. -/
theorem rowFiniteSignedMap_single (h : P → N) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (Finsupp.single x a) = q.negOnePow • (a • h x) := by
  classical
  simp [rowFiniteSignedMap, Finsupp.lsum_single,
    koszulTwist_one_eq_negOnePow_smul (R := R) ha]

/-- A generator maps to its specified image. -/
@[simp]
theorem rowFiniteSignedMap_single_one (h : P → N) (x : P) :
    rowFiniteSignedMap (𝒜 := 𝒜) h (Finsupp.single x 1) = h x := by
  rw [rowFiniteSignedMap_single h x (SetLike.one_mem_graded 𝒜)]
  simp

/-- The signed extension is additive in the family of images. -/
theorem rowFiniteSignedMap_add (h h' : P → N) :
    rowFiniteSignedMap (𝒜 := 𝒜) (h + h') =
      rowFiniteSignedMap (𝒜 := 𝒜) h + rowFiniteSignedMap (𝒜 := 𝒜) h' := by
  ext x a
  simp [rowFiniteSignedMap_apply, smul_add]

/-- The signed extension is compatible with negation of the family of images. -/
theorem rowFiniteSignedMap_neg (h : P → N) :
    rowFiniteSignedMap (𝒜 := 𝒜) (-h) = -rowFiniteSignedMap (𝒜 := 𝒜) h := by
  ext x a
  simp [rowFiniteSignedMap_apply]

/-- The signed extension is compatible with subtraction of the families of images. -/
theorem rowFiniteSignedMap_sub (h h' : P → N) :
    rowFiniteSignedMap (𝒜 := 𝒜) (h - h') =
      rowFiniteSignedMap (𝒜 := 𝒜) h - rowFiniteSignedMap (𝒜 := 𝒜) h' := by
  rw [sub_eq_add_neg, rowFiniteSignedMap_add, rowFiniteSignedMap_neg, sub_eq_add_neg]

/-- An `A`-linear map commutes with the signed extension. -/
theorem rowFiniteSignedMap_comp {N' : Type*} [AddCommGroup N'] [Module R N'] [Module A N']
    [IsScalarTower R A N'] (φ : N →ₗ[A] N') (h : P → N) (f : P →₀ A) :
    φ (rowFiniteSignedMap (𝒜 := 𝒜) h f) = rowFiniteSignedMap (𝒜 := 𝒜) (φ ∘ h) f := by
  simp [rowFiniteSignedMap_apply, Finsupp.sum, map_sum]

/-- Signed row extension is graded left-linear of odd degree. -/
theorem rowFiniteSignedMap_smul (h : P → N) {q : ℤ} {a : A}
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

/-- Substituting finite rows `ν` and then applying a signed extension is the signed extension of
the images of the rows. -/
theorem rowFiniteSignedMap_linearCombination (k : Q → N) (ν : P → Q →₀ A) (f : P →₀ A) :
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

/-- Rows with shifted degree `k` give a signed map of total degree `k`. -/
theorem rowFiniteSignedMap_mem_totalGrading (h : P → Q →₀ A) {k : ℤ}
    (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - ind x + k)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ rowFiniteTotalGrading 𝒜 indQ (n + k) := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  rw [rowFiniteSignedMap_single h x (hf x), mem_rowFiniteTotalGrading_iff]
  intro y
  simp only [Finsupp.smul_apply, smul_eq_mul]
  apply Submodule.smul_of_tower_mem
  have := SetLike.GradedMul.mul_mem (hf x) (hh x y)
  convert this using 2; ring

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

section Maps

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ]

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- An `A`-linear map out of the free module, sending each generator `x` in the support of a
vector of total degree `n` to degree `-ind x + j`, sends that vector to degree `n + j`. -/
theorem linearCombination_mem_of_mem_support {g : P → M} {j n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hg : ∀ x ∈ f.support, g x ∈ ℳ (-ind x + j)) :
    Finsupp.linearCombination A g f ∈ ℳ (n + j) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  have := SetLike.GradedSMul.smul_mem (hf x) (hg x hx)
  rwa [vadd_eq_add, show n + ind x + (-ind x + j) = n + j by ring] at this

omit [GradedAlgebra 𝒜] [IsScalarTower R A M] in
/-- An `A`-linear map out of the free module sends total degree `n` to degree `n` as soon as
each generator `x` is sent to degree `-ind x`. -/
theorem linearCombination_mem_of_mem_rowFiniteTotalGrading {g : P → M}
    (hg : ∀ x, g x ∈ ℳ (-ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : Finsupp.linearCombination A g f ∈ ℳ n := by
  simpa using linearCombination_mem_of_mem_support (j := 0) hf fun x _ ↦ by simpa using hg x

/-- The signed extension of images of degree `-ind x + j` sends a vector of total degree `n` to
degree `n + j`; only the generators in its support matter. -/
theorem rowFiniteSignedMap_mem_of_mem_support {k : P → M} {j n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) (hk : ∀ x ∈ f.support, k x ∈ ℳ (-ind x + j)) :
    rowFiniteSignedMap (𝒜 := 𝒜) k f ∈ ℳ (n + j) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  rw [rowFiniteSignedMap_single k x (hf x)]
  apply Submodule.smul_of_tower_mem
  have := SetLike.GradedSMul.smul_mem (hf x) (hk x hx)
  rwa [vadd_eq_add, show n + ind x + (-ind x + j) = n + j by ring] at this

variable [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

/-- **Maps out of the free module are determined on generators**, one vector at a time. If an
`A`-linear map sends the differential of each generator in the support of `f`, its row `m x`, to
the differential of the image of the generator, then it commutes with the differentials on `f`,
by the DG Leibniz rule. -/
theorem linearCombination_rowFiniteTwistedDifferential_of_mem_support
    (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A) {g : P → M} {f : P →₀ A}
    (hg : ∀ x ∈ f.support, Finsupp.linearCombination A g (m x) = dM (g x)) :
    Finsupp.linearCombination A g (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      dM (Finsupp.linearCombination A g f) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  generalize f x = c
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    rw [rowFiniteTwistedDifferential_single m x a.2, map_add, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, hM.leibniz a.2, ← hg x hx]
    simp only [map_smul, LinearMap.map_smul_of_tower]
  | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

/-- **Maps out of the free module are determined on generators.** If an `A`-linear map sends
the differential of each generator, its row `m x`, to the differential of the image of the
generator, then it commutes with the differentials on the whole free module, by the DG Leibniz
rule. -/
theorem linearCombination_rowFiniteTwistedDifferential (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) {g : P → M} (hg : ∀ x, Finsupp.linearCombination A g (m x) = dM (g x))
    (f : P →₀ A) :
    Finsupp.linearCombination A g (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      dM (Finsupp.linearCombination A g f) :=
  linearCombination_rowFiniteTwistedDifferential_of_mem_support hM m fun x _ ↦ hg x

/-- **Homotopies out of the free module are determined on generators**, one vector at a time.
Let `Φ` be an `A`-linear map out of the free module, typically a difference of two chain maps.
If the signed extension of `k : P → M` satisfies `dM (k x) + K (m x) = Φ x` on each generator in
the support of `f`, then `dM (K f) + K (D f) = Φ f`, by the DG Leibniz rule. -/
theorem rowFiniteSignedMap_differential_of_mem_support (hM : IsDGLeftModule h ℳ dM)
    (m : P → P →₀ A) {k : P → M} {Φ : (P →₀ A) →ₗ[A] M} {f : P →₀ A}
    (hk : ∀ x ∈ f.support, dM (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m x) =
      Φ (Finsupp.single x 1)) :
    dM (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
        rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) =
      Φ f := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum]
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  generalize f x = c
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    -- The two terms involving `d a` cancel; the rest is `a` times the generator equation.
    rw [rowFiniteSignedMap_single k x a.2, rowFiniteTwistedDifferential_single m x a.2, map_add,
      rowFiniteSignedMap_single k x (h.map_mem a.2)]
    simp only [LinearMap.map_smul_of_tower]
    rw [hM.leibniz a.2, rowFiniteSignedMap_smul k a.2, ← Finsupp.smul_single_one x (a : A),
      map_smul, ← hk x hx]
    simp only [smul_add, smul_smul, Int.units_mul_self, one_smul, Int.negOnePow_succ,
      Units.neg_smul]
    abel
  | add a b ha hb =>
    simp only [Finsupp.single_add, map_add]
    rw [add_add_add_comm, ha, hb]

/-- **Even homotopies out of the free module are determined on generators**, one vector at a
time. For `L` the `A`-linear extension of `l : P → M`, the map `dM ∘ L - L ∘ D` is graded
left-linear of odd degree. So if it agrees on each generator in the support of `f` with the
signed extension of `θ : P → M`, then it agrees with it on `f`. -/
theorem rowFiniteSignedMap_eq_of_mem_support (hM : IsDGLeftModule h ℳ dM) (m : P → P →₀ A)
    {l θ : P → M} {f : P →₀ A}
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

end Maps

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
