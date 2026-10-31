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

## Main definitions and results

* `RowFiniteTwistingCocycle`: homogeneous finite rows with the Maurer–Cartan equation.
* `rowFiniteTotalGrading` and `rowFiniteTwistedDifferential`: the graded free left module
  and its differential, characterized on homogeneous elementary vectors.
* `RowFiniteTwistingCocycle.isDGLeftModule_rowFiniteTwistedDifferential`: the differential
  graded left module laws, with square-zero derived from the row equation and DG Leibniz rule.
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

universe uR uA uP

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

end RowFiniteTwistingCocycle

/-- The differential of the free left module of a row-finite matrix. The Koszul twist applies
the sign to each coefficient before multiplication into the finite row. -/
noncomputable def rowFiniteTwistedDifferential (m : P → P →₀ A) :
    (P →₀ A) →ₗ[R] (P →₀ A) :=
  Finsupp.mapRange.linearMap d + Finsupp.lsum R (fun x ↦
    ((LinearMap.toSpanSingleton A (P →₀ A) (m x)).restrictScalars R).comp
      ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1))

/-- The differential evaluated on a single homogeneous coefficient. -/
theorem rowFiniteTwistedDifferential_single (m : P → P →₀ A) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (Finsupp.single x a) =
      Finsupp.single x (d a) + q.negOnePow • (a • m x) := by
  classical
  simp [rowFiniteTwistedDifferential, Finsupp.lsum_single,
    koszulTwist_one_eq_negOnePow_smul (R := R) ha]

/-- The finite-support total grading is compatible with the pointwise left algebra action. -/
instance instGradedSMulRowFiniteTotalGrading :
    SetLike.GradedSMul 𝒜 (rowFiniteTotalGrading 𝒜 ind) where
  smul_mem := by
    intro i n a f ha hf x
    have := SetLike.GradedMul.mul_mem ha (hf x)
    simpa only [vadd_eq_add, add_assoc, Finsupp.smul_apply, smul_eq_mul] using this

section DifferentialLaws

variable (m : P → P →₀ A) (h : IsDGAlgebra 𝒜 d)

include h

/-- The graded Leibniz rule on a homogeneous elementary vector. -/
theorem rowFiniteTwistedDifferential_smul_single {p q : ℤ} {a b : A}
    (ha : a ∈ 𝒜 p) (hb : b ∈ 𝒜 q) (x : P) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (a • Finsupp.single x b) =
      d a • Finsupp.single x b +
        p.negOnePow • (a • rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m
          (Finsupp.single x b)) := by
  rw [Finsupp.smul_single, smul_eq_mul,
    rowFiniteTwistedDifferential_single m x (SetLike.GradedMul.mul_mem ha hb),
    rowFiniteTwistedDifferential_single m x hb, h.leibniz ha b]
  simp only [Finsupp.single_add, smul_add, Finsupp.smul_single,
    Int.negOnePow_add, mul_smul, smul_eq_mul]
  rw [add_assoc, smul_comm a q.negOnePow]

/-- The graded Leibniz rule for a homogeneous algebra element and any finite-support vector. -/
theorem rowFiniteTwistedDifferential_smul {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m (a • f) =
      d a • f + p.negOnePow •
        (a • rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]; abel
  | single x b =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q b => exact rowFiniteTwistedDifferential_smul_single m h ha b.2 x
    | add b c hb hc =>
      simp only [Finsupp.single_add, smul_add, map_add, hb, hc]
      abel

/-- The differential increases total degree by one. -/
theorem rowFiniteTwistedDifferential_mem_totalGrading
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    {n : ℤ} {f : P →₀ A} (hf : f ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f ∈
      rowFiniteTotalGrading 𝒜 ind (n + 1) := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  rw [rowFiniteTwistedDifferential_single m x (hf x)]
  intro y
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
  · by_cases hy : x = y
    · subst y
      simpa only [Finsupp.single_eq_same, add_right_comm] using h.map_mem (hf x)
    · simp [Finsupp.single_eq_of_ne (Ne.symm hy)]
  · have := SetLike.GradedMul.mul_mem (hf x) (hm x y)
    convert this using 2; ring

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
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (m.m x) = 0 := by
  classical
  have hd : (∑ y ∈ (m.m x).support, Finsupp.single y (d (m.m x y))) =
      Finsupp.mapRange.linearMap d (m.m x) := by
    conv_rhs => rw [← Finsupp.sum_single (m.m x), Finsupp.sum]
    rw [map_sum]
    simp
  rw [← Finsupp.sum_single (m.m x), Finsupp.sum, map_sum]
  simp_rw [rowFiniteTwistedDifferential_single m.m _ (m.mem_graded x _)]
  rw [Finset.sum_add_distrib, hd, m.twisting x]
  simp only [Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  have hsign : (ind y - ind x + 1).negOnePow = -(ind x - ind y).negOnePow := by
    rw [Int.negOnePow_succ, ← Int.negOnePow_neg (ind x - ind y)]
    congr 2
    omega
  rw [hsign, Units.neg_smul, add_neg_cancel]

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
