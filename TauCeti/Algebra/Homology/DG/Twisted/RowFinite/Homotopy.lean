/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Continuation
public import TauCeti.Algebra.Homology.DG.Twisted.Homotopy

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
      rowFiniteSignedMap (𝒜 := 𝒜) h (mP.m x) = ν₁.ν x - ν₀.ν x

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

/-- The signed map of a parametrized cocycle lowers total degree by one. -/
theorem rowFiniteSignedMap_mem_totalGrading {n : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteTotalGrading 𝒜 indP n) :
    rowFiniteSignedMap (𝒜 := 𝒜) η.h f ∈ rowFiniteTotalGrading 𝒜 indQ (n - 1) := by
  simpa only [sub_eq_add_neg] using
    TauCeti.rowFiniteSignedMap_mem_totalGrading η.h (k := -1)
      (fun x y ↦ by simpa only [sub_eq_add_neg] using η.mem_graded x y) hf

/-- The generator equation extends to the entire free left module: the signed row map is a
chain homotopy between the two continuation substitutions. -/
theorem rowFiniteSignedMap_differential (hA : IsDGAlgebra 𝒜 d) (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m
        (rowFiniteSignedMap (𝒜 := 𝒜) η.h f) +
      rowFiniteSignedMap (𝒜 := 𝒜) η.h
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
      rw [rowFiniteSignedMap_single η.h x a.2,
        LinearMap.map_smul_of_tower,
        rowFiniteTwistedDifferential_smul mQ.m hA a.2,
        rowFiniteTwistedDifferential_single mP.m x a.2, map_add,
        rowFiniteSignedMap_single η.h x (hA.map_mem a.2),
        LinearMap.map_smul_of_tower, rowFiniteSignedMap_smul η.h a.2]
      simp only [smul_add, smul_smul, Int.units_mul_self, one_smul,
        Int.negOnePow_succ, Units.neg_smul, Finsupp.linearCombination_single]
      have hrow := congrArg (fun v ↦ (a : A) • v) (η.parametrized x)
      simp only [smul_add, smul_sub] at hrow
      abel_nf at hrow ⊢
      exact hrow
    | add a b ha hb =>
      simp only [Finsupp.single_add, map_add]
      rw [add_add_add_comm, ha, hb]
      abel

/-- A homogeneous row's Koszul contribution with an odd shifted degree has the opposite sign
from the corresponding index-difference sum. -/
private theorem signedRow_sum_eq_neg {X : Type*} (f : X →₀ A) (g : X → Q →₀ A)
    (i : X → ℤ) {k s : ℤ} (hs : Odd s) (hf : ∀ z, f z ∈ 𝒜 (i z - k + s)) :
    f.sum (fun z a ↦ (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a • g z) =
      -f.sum (fun z a ↦ (k - i z).negOnePow • (a • g z)) := by
  classical
  rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [koszulTwist_one_eq_negOnePow_smul (R := R) (hf z), Int.negOnePow_add,
    Int.negOnePow_odd _ hs, ← Int.negOnePow_neg (k - i z), neg_sub]
  simp

/-- The generator equation expanded into the signed finite-row homotopy equation. -/
theorem parametrized_iff (h : P → Q →₀ A)
    (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - indP x - 1)) (x : P) :
    (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m (h x) +
        rowFiniteSignedMap (𝒜 := 𝒜) h (mP.m x) = ν₁.ν x - ν₀.ν x) ↔
      Finsupp.mapRange.linearMap d (h x) = ν₁.ν x - ν₀.ν x +
        (mP.m x).sum (fun z a ↦ (indP x - indP z).negOnePow • (a • h z)) +
        (h x).sum (fun z a ↦ (indP x - indQ z).negOnePow • (a • mQ.m z)) := by
  classical
  -- Both twisting contributions move across the equality with the opposite sign.
  have hD := signedRow_sum_eq_neg (h x) mQ.m indQ (s := -1) (by decide)
    (fun z ↦ by simpa only [sub_eq_add_neg] using hh x z)
  have hH := signedRow_sum_eq_neg (mP.m x) h indP (by decide : Odd (1 : ℤ))
    (mP.mem_graded x)
  rw [rowFiniteTwistedDifferential_apply, rowFiniteSignedMap_apply, hD, hH]
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
theorem linearEquivFunOnFinite_rowFiniteSignedMap [Fintype P] [Finite Q]
    (h : P → Q →₀ A) (f : P →₀ A) :
    Finsupp.linearEquivFunOnFinite R A Q (rowFiniteSignedMap (𝒜 := 𝒜) h f) =
      homotopyMap (fun x y ↦ h x y) 𝒜 (Finsupp.linearEquivFunOnFinite R A P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q a =>
      rw [rowFiniteSignedMap_single h x a.2, Finsupp.linearEquivFunOnFinite_single]
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
