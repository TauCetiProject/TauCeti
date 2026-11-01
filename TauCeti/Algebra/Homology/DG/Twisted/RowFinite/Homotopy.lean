/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Continuation
public import TauCeti.Algebra.Homology.DG.Twisted.Homotopy
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Homotopies of row-finite twisted free modules

A finite row for each generator extends to a graded left-linear map of degree minus one
by applying the Koszul sign to its coefficient. A parametrized cocycle specifies that the
boundary of this map on generators is the difference of two continuation rows. The DG
Leibniz rule extends this equation to a chain homotopy on the entire free left module,
without any finiteness restriction on the generator sets.

This is the free-module homotopy needed to compare choices of attaching cycles in cellular
DG resolutions. It does not assert that the twisted modules are resolutions. For finite
bases, the signed map and parametrized equation recover `homotopyMap` and
`ParametrizedCocycle`, with the regular algebra as coefficients.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4, Definition 1.11.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

open DirectSum

namespace TauCeti

universe uR uA uP uQ

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {P : Type uP} {Q : Type uQ} {indP : P → ℤ} {indQ : Q → ℤ}

/-- The signed extension of finite rows to the free left module. On a coefficient of degree
`q`, it sends `single x a` to `(-1)^q • (a • h x)`. -/
def rowFiniteHomotopyMap (h : P → Q →₀ A) : (P →₀ A) →ₗ[R] (Q →₀ A) :=
  Finsupp.lsum R fun x ↦
    ((LinearMap.toSpanSingleton A (Q →₀ A) (h x)).restrictScalars R).comp
      ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1)

/-- Signed row substitution is a finite sum over the support of the input vector. -/
theorem rowFiniteHomotopyMap_apply (h : P → Q →₀ A) (f : P →₀ A) :
    rowFiniteHomotopyMap (𝒜 := 𝒜) h f =
      f.sum (fun x a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a • h x) := by
  classical
  simp [rowFiniteHomotopyMap, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply,
    Function.comp_def]

/-- The signed extension evaluated on a homogeneous elementary vector. -/
theorem rowFiniteHomotopyMap_single (h : P → Q →₀ A) (x : P)
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) :
    rowFiniteHomotopyMap (𝒜 := 𝒜) h (Finsupp.single x a) = q.negOnePow • (a • h x) := by
  classical
  simp [rowFiniteHomotopyMap, Finsupp.lsum_single,
    koszulTwist_one_eq_negOnePow_smul (R := R) ha]

/-- A generator maps to its specified finite homotopy row. -/
@[simp]
theorem rowFiniteHomotopyMap_single_one (h : P → Q →₀ A) (x : P) :
    rowFiniteHomotopyMap (𝒜 := 𝒜) h (Finsupp.single x 1) = h x := by
  rw [rowFiniteHomotopyMap_single h x (SetLike.one_mem_graded 𝒜)]
  simp

/-- Signed row extension is graded left-linear of odd degree. -/
theorem rowFiniteHomotopyMap_smul (h : P → Q →₀ A) {q : ℤ} {a : A}
    (ha : a ∈ 𝒜 q) (f : P →₀ A) :
    rowFiniteHomotopyMap (𝒜 := 𝒜) h (a • f) =
      q.negOnePow • (a • rowFiniteHomotopyMap (𝒜 := 𝒜) h f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]
  | single x b =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous p b =>
      rw [Finsupp.smul_single, smul_eq_mul,
        rowFiniteHomotopyMap_single h x (SetLike.GradedMul.mul_mem ha b.2),
        rowFiniteHomotopyMap_single h x b.2]
      simp [Int.negOnePow_add, mul_smul, smul_comm a p.negOnePow]
    | add b c hb hc => simp only [Finsupp.single_add, smul_add, map_add, hb, hc]

/-- Homogeneous rows of degree `indQ y - indP x - 1` give a map of total degree minus one. -/
theorem rowFiniteHomotopyMap_mem_totalGrading (h : P → Q →₀ A)
    (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - indP x - 1)) {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 indP n) :
    rowFiniteHomotopyMap (𝒜 := 𝒜) h f ∈ rowFiniteTotalGrading 𝒜 indQ (n - 1) := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  rw [rowFiniteHomotopyMap_single h x (hf x), mem_rowFiniteTotalGrading_iff]
  intro y
  simp only [Finsupp.smul_apply, smul_eq_mul]
  apply Submodule.smul_of_tower_mem
  have := SetLike.GradedMul.mul_mem (hf x) (hh x y)
  convert this using 2; ring

/-- A row-finite parametrized cocycle between continuation cocycles. Its generator equation
uses the signed extension, so the full chain-homotopy identity is a consequence, not a field. -/
structure RowFiniteParametrizedCocycle
    {mP : RowFiniteTwistingCocycle 𝒜 d P indP}
    {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
    (ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ) where
  /-- The finite homotopy row at each source generator. -/
  h : P → Q →₀ A
  /-- Each entry has the degree of a homotopy between shifted free generators. -/
  mem_graded : ∀ x y, h x y ∈ 𝒜 (indQ y - indP x - 1)
  /-- The boundary equation on source generators. -/
  parametrized : ∀ x,
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (h x) +
      rowFiniteHomotopyMap (𝒜 := 𝒜) h (mP.m x) = ν₁.ν x - ν₀.ν x

namespace RowFiniteParametrizedCocycle

variable {mP : RowFiniteTwistingCocycle 𝒜 d P indP}
  {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}

@[ext]
theorem ext {η θ : RowFiniteParametrizedCocycle ν₀ ν₁}
    (hh : ∀ x y, η.h x y = θ.h x y) : η = θ := by
  cases η
  cases θ
  congr
  funext x
  exact Finsupp.ext (hh x)

variable (η : RowFiniteParametrizedCocycle ν₀ ν₁)

/-- The generator equation extends to the entire free left module: the signed row map is a
chain homotopy between the two continuation substitutions. -/
theorem homotopyMap_differential (hA : IsDGAlgebra 𝒜 d) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m
        (rowFiniteHomotopyMap (𝒜 := 𝒜) η.h f) +
      rowFiniteHomotopyMap (𝒜 := 𝒜) η.h
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m f) =
      Finsupp.linearCombination A ν₁.ν f - Finsupp.linearCombination A ν₀.ν f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_add_add_comm, hf, hg]
    abel
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      -- The two terms involving d(a) cancel; the remaining terms are a times the row equation.
      rw [rowFiniteHomotopyMap_single η.h x a.2,
        LinearMap.map_smul_of_tower,
        rowFiniteTwistedDifferential_smul mQ.m hA a.2,
        rowFiniteTwistedDifferential_single mP.m x a.2, map_add,
        rowFiniteHomotopyMap_single η.h x (hA.map_mem a.2),
        LinearMap.map_smul_of_tower, rowFiniteHomotopyMap_smul η.h a.2]
      simp only [smul_add, smul_smul, Int.units_mul_self, one_smul,
        Int.negOnePow_succ, Units.neg_smul, Finsupp.linearCombination_single]
      rw [add_assoc, add_left_comm, add_neg_cancel_left, ← smul_add, η.parametrized]
      simp [smul_sub]
    | add a b ha hb =>
      simp only [Finsupp.single_add, map_add]
      rw [add_add_add_comm, ha, hb]
      abel

/-- The generator equation written in the usual signed Maurer–Cartan row notation. -/
theorem parametrized_iff (h : P → Q →₀ A)
    (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - indP x - 1)) (x : P) :
    (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (h x) +
        rowFiniteHomotopyMap (𝒜 := 𝒜) h (mP.m x) = ν₁.ν x - ν₀.ν x) ↔
      Finsupp.mapRange.linearMap d (h x) = ν₁.ν x - ν₀.ν x +
        (mP.m x).sum (fun z a ↦ (indP x - indP z).negOnePow • (a • h z)) +
        (h x).sum (fun z a ↦ (indP x - indQ z).negOnePow • (a • mQ.m z)) := by
  classical
  -- Both twisting contributions move across the equality with the opposite sign.
  have hD : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (h x) =
      Finsupp.mapRange.linearMap d (h x) -
        (h x).sum (fun z a ↦ (indP x - indQ z).negOnePow • (a • mQ.m z)) := by
    rw [rowFiniteTwistedDifferential_apply, sub_eq_add_neg]
    congr 1
    rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [koszulTwist_one_eq_negOnePow_smul (R := R) (hh x z)]
    have hs : (indQ z - indP x - 1).negOnePow = -(indP x - indQ z).negOnePow := by
      rw [Int.negOnePow_sub_sub_one]
    simp [hs]
  have hH : rowFiniteHomotopyMap (𝒜 := 𝒜) h (mP.m x) =
      -(mP.m x).sum (fun z a ↦ (indP x - indP z).negOnePow • (a • h z)) := by
    conv_lhs => rw [← Finsupp.sum_single (mP.m x), Finsupp.sum, map_sum]
    rw [Finsupp.sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [rowFiniteHomotopyMap_single h z (mP.mem_graded x z)]
    have hs : (indP z - indP x + 1).negOnePow = -(indP x - indP z).negOnePow := by
      rw [Int.negOnePow_succ, ← Int.negOnePow_neg (indP x - indP z)]
      congr 2
      omega
    simp [hs]
  rw [hD, hH]
  constructor
  · intro heq
    rw [← heq]
    abel
  · intro heq
    rw [heq]
    abel

end RowFiniteParametrizedCocycle

/-- For finite bases the signed extension is precisely the original homotopy map, with
regular algebra coefficients, through the actual finite-support/function equivalence. -/
theorem linearEquivFunOnFinite_rowFiniteHomotopyMap [Fintype P] [Finite Q]
    (h : P → Q →₀ A) (f : P →₀ A) :
    Finsupp.linearEquivFunOnFinite R A Q (rowFiniteHomotopyMap (𝒜 := 𝒜) h f) =
      homotopyMap (fun x y ↦ h x y) 𝒜 (Finsupp.linearEquivFunOnFinite R A P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [rowFiniteHomotopyMap_single h x a.2, Finsupp.linearEquivFunOnFinite_single]
      ext y
      simp [homotopyMap_single_apply _ x a.2, MulOpposite.smul_eq_mul_unop]
    | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]

namespace ParametrizedCocycle

variable [Fintype P] [Fintype Q]
  {mP : TwistingCocycle 𝒜 d P indP} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- Regard a finite parametrized cocycle as finite homotopy rows on the row-finite modules. -/
def toRowFinite (η : ParametrizedCocycle ν₀ ν₁) :
    RowFiniteParametrizedCocycle ν₀.toRowFinite ν₁.toRowFinite where
  h x := (Finsupp.linearEquivFunOnFinite R A Q).symm (η.h x)
  mem_graded := η.mem_graded
  parametrized x := by
    apply (RowFiniteParametrizedCocycle.parametrized_iff _ η.mem_graded x).mpr
    ext y
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.sum_fintype _ _ (by intro z; simp),
      Finsupp.sum_fintype _ _ (by intro z; simp)]
    simpa only [ContinuationCocycle.toRowFinite_ν, TwistingCocycle.toRowFinite_m,
      Finsupp.linearEquivFunOnFinite_symm_apply] using η.parametrized x y

@[simp]
theorem toRowFinite_h (η : ParametrizedCocycle ν₀ ν₁) (x : P) (y : Q) :
    η.toRowFinite.h x y = η.h x y := (rfl)

end ParametrizedCocycle

end TauCeti
