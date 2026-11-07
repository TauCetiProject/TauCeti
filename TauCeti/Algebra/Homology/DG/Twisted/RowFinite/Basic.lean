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
* `rowFiniteTotalGrading` and `rowFiniteTwistedDifferential`: the graded free left module
  and its differential, characterized on homogeneous elementary vectors.
* `RowFiniteTwistingCocycle.isDGLeftModule_rowFiniteTwistedDifferential`: the differential
  graded left module laws, with square-zero derived from the row equation and DG Leibniz rule.
* `rowFiniteTwistedDifferential_mapDomain`: relabelling generators compatibly with the rows
  commutes with the differentials.
* `mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero`: the Maurer–Cartan equation of a
  row is the vanishing of its twisted differential.
* `linearCombination_rowFiniteTwistedDifferential` and
  `forall_linearCombination_rowFiniteTwistedDifferential_iff`: maps out of the free module
  commute with the differentials exactly when they do so on generators.
* `rowFiniteSignedMap`: the Koszul-signed extension of images of the generators out of the
  free module, with `rowFiniteSignedMap_congr`, `LinearMap.map_rowFiniteSignedMap` and
  `rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading`, which gives it degree `-1` when each
  generator `x` is sent into degree `-ind x - 1`.
* `linearCombination_eq_add_rowFiniteSignedMap` and
  `forall_linearCombination_eq_add_rowFiniteSignedMap_iff`: homotopies out of the free module
  are determined on generators.
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
/-- The row of a generator `x`, its differential, lies in total degree `1 - ind x`. -/
theorem m_mem_rowFiniteTotalGrading (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x : P) :
    m.m x ∈ rowFiniteTotalGrading 𝒜 ind (1 - ind x) :=
  (mem_rowFiniteTotalGrading_iff 𝒜 ind).mpr fun y ↦ by
    convert m.mem_graded x y using 2
    ring

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
/-- An `A`-linear map out of the free module sends total degree `n` to degree `n` as soon as
each generator `x` is sent to degree `-ind x`. -/
theorem linearCombination_mem_of_mem_rowFiniteTotalGrading {g : P → M}
    (hg : ∀ x, g x ∈ ℳ (-ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : Finsupp.linearCombination A g f ∈ ℳ n := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have := SetLike.GradedSMul.smul_mem (hf x) (hg x)
  simpa only [vadd_eq_add, add_neg_cancel_right] using this

/-- The signed extension of images of degree `j - ind x` raises total degree by `j`. -/
theorem rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading {h : P → M} {j : ℤ}
    (hh : ∀ x, h x ∈ ℳ (j - ind x)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) : rowFiniteSignedMap (𝒜 := 𝒜) h f ∈ ℳ (n + j) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  rw [rowFiniteSignedMap_single h x (hf x)]
  apply Submodule.smul_of_tower_mem
  have := SetLike.GradedSMul.smul_mem (hf x) (hh x)
  convert this using 2
  simp only [vadd_eq_add]
  ring

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
