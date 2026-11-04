/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The cell filtration of a row-finite twisted module

Filter the finite-support free module by the indices of its generators. Unlike a product of
coefficient modules, this filtration is exhaustive even for an infinite generator set with
unbounded indices. If the twisting rows strictly lower generator indices, the twisting part of
the differential lowers the filtration. The successive quotient is therefore the finite-support
module on generators of one index, with the coefficient differential alone.
The same holds for the differential with coefficients in a DG right module
(`TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_sub_mem_indexFiltration`).

The quotient equivalence and its differential comparison are explicit. If generator indices
are bounded below (as for nonnegative-dimensional cells), the filtration starts at zero. These
are the algebraic cell-filtration properties needed for attaching free generators; no resolution
or quasi-isomorphism is asserted for an arbitrary twisting cocycle.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

namespace TauCeti

universe uR uA uM uP

section Filtration

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [Semiring R] [AddCommMonoid A] [Module R A] (ind : P → ℤ)

/-- Finite-support vectors on generators of index at most `p`. -/
def rowFiniteIndexFiltration (p : ℤ) : Submodule R (P →₀ A) :=
  Finsupp.supported A R {x | ind x ≤ p}

@[simp]
theorem mem_rowFiniteIndexFiltration_iff {p : ℤ} {f : P →₀ A} :
    f ∈ rowFiniteIndexFiltration (R := R) ind p ↔ ∀ x, p < ind x → f x = 0 := by
  simpa [rowFiniteIndexFiltration] using
    (Finsupp.mem_supported' R (s := {x | ind x ≤ p}) f)

/-- The cell filtration is increasing. -/
theorem rowFiniteIndexFiltration_mono :
    Monotone (rowFiniteIndexFiltration (R := R) (A := A) ind) :=
  fun _ _ hp ↦ Finsupp.supported_mono fun _ hx ↦ hx.trans hp

/-- Every finite-support vector lies in the cell filtration, without a finite-type hypothesis. -/
theorem iSup_rowFiniteIndexFiltration_eq_top :
    (⨆ p, rowFiniteIndexFiltration (R := R) (A := A) ind p) = ⊤ := by
  have hs : (⋃ p : ℤ, {x | ind x ≤ p}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨ind x, le_rfl⟩
  simpa only [rowFiniteIndexFiltration, hs, Finsupp.supported_univ] using
    (Finsupp.supported_iUnion (M := A) (R := R) fun p : ℤ ↦ {x | ind x ≤ p}).symm

/-- A lower bound on generator indices makes every earlier filtration stage zero. -/
theorem rowFiniteIndexFiltration_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    rowFiniteIndexFiltration (R := R) (A := A) ind p = ⊥ := by
  have hs : {x | ind x ≤ p} = (∅ : Set P) := by ext x; simp [not_le.mpr (hp x)]
  simp [rowFiniteIndexFiltration, hs]

/-- Restriction of a filtration stage to its generators of maximal index. -/
noncomputable def rowFiniteIndexProjection (p : ℤ) :
    rowFiniteIndexFiltration (R := R) (A := A) ind p →ₗ[R] {x // ind x = p} →₀ A :=
  (Finsupp.lsubtypeDomain {x | ind x = p}).comp (rowFiniteIndexFiltration ind p).subtype

@[simp]
theorem rowFiniteIndexProjection_apply (p : ℤ)
    (f : rowFiniteIndexFiltration (R := R) (A := A) ind p) (x : {x // ind x = p}) :
    rowFiniteIndexProjection ind p f x = f.val x := (rfl)

/-- Every finite family on the new generators extends to a vector in the filtration stage. -/
theorem rowFiniteIndexProjection_surjective (p : ℤ) :
    Function.Surjective (rowFiniteIndexProjection (R := R) (A := A) ind p) := by
  intro f
  let g := (Finsupp.supportedEquivFinsupp (R := R) {x | ind x = p}).symm f
  refine ⟨⟨g.val, Finsupp.supported_mono (fun _ hx ↦ le_of_eq hx) g.property⟩, ?_⟩
  ext x
  classical
  simp [g, Finsupp.supportedEquivFinsupp_symm_apply_coe, x.property]

/-- The projection kills exactly the preceding filtration stage. -/
theorem ker_rowFiniteIndexProjection (p : ℤ) :
    LinearMap.ker (rowFiniteIndexProjection (R := R) (A := A) ind p) =
      (rowFiniteIndexFiltration ind (p - 1)).comap (rowFiniteIndexFiltration ind p).subtype := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    mem_rowFiniteIndexFiltration_iff]
  constructor
  · intro hf x hx
    by_cases hxp : p < ind x
    · exact (mem_rowFiniteIndexFiltration_iff ind).mp f.property x hxp
    · have heq : ind x = p := by omega
      exact DFunLike.congr_fun hf ⟨x, heq⟩
  · intro hf
    ext x
    exact hf x (by omega)

/-- On generators of index `p`, total degree `n` means coefficient degree `n + p`. -/
theorem rowFiniteIndexProjection_mem_grading (𝒜 : ℤ → Submodule R A) {p n : ℤ}
    (f : rowFiniteIndexFiltration (R := R) (A := A) ind p)
    (hf : f.val ∈ rowFiniteTotalGrading 𝒜 ind n) :
    rowFiniteIndexProjection ind p f ∈
      Finsupp.submodule (fun _ : {x // ind x = p} ↦ 𝒜 (n + p)) := by
  intro x
  simpa only [rowFiniteIndexProjection_apply, x.property] using
    (mem_rowFiniteTotalGrading_iff 𝒜 ind).mp hf x.val

end Filtration

section Quotient

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [Ring R] [AddCommGroup A] [Module R A] (ind : P → ℤ)

/-- The actual successive quotient is the finite-support module on the new generators. -/
noncomputable def rowFiniteIndexQuotientEquiv (p : ℤ) :
    (rowFiniteIndexFiltration (R := R) (A := A) ind p ⧸
      (rowFiniteIndexFiltration (R := R) (A := A) ind (p - 1)).comap
        (rowFiniteIndexFiltration (R := R) (A := A) ind p).subtype) ≃ₗ[R]
      {x // ind x = p} →₀ A :=
  (Submodule.quotEquivOfEq _ _ (ker_rowFiniteIndexProjection (R := R) (A := A) ind p).symm).trans
    ((rowFiniteIndexProjection (R := R) (A := A) ind p).quotKerEquivOfSurjective
      (rowFiniteIndexProjection_surjective ind p))

@[simp]
theorem rowFiniteIndexQuotientEquiv_mk (p : ℤ)
    (f : rowFiniteIndexFiltration (R := R) (A := A) ind p) :
    rowFiniteIndexQuotientEquiv ind p (Submodule.Quotient.mk f) =
      rowFiniteIndexProjection ind p f := by
  simp [rowFiniteIndexQuotientEquiv]

/-- The coefficient differential transported to the successive quotient. For a strictly
index-lowering twisting matrix this is the induced twisted differential. -/
noncomputable def rowFiniteIndexQuotientDifferential (d : A →ₗ[R] A) (p : ℤ) :
    Module.End R (rowFiniteIndexFiltration (R := R) (A := A) ind p ⧸
      (rowFiniteIndexFiltration (R := R) (A := A) ind (p - 1)).comap
        (rowFiniteIndexFiltration (R := R) (A := A) ind p).subtype) :=
  (rowFiniteIndexQuotientEquiv (R := R) (A := A) ind p).symm.conjRingEquiv
    (Finsupp.mapRange.linearMap d)

@[simp]
theorem rowFiniteIndexQuotientEquiv_differential (d : A →ₗ[R] A) (p : ℤ) (z) :
    rowFiniteIndexQuotientEquiv ind p (rowFiniteIndexQuotientDifferential ind d p z) =
      Finsupp.mapRange.linearMap d (rowFiniteIndexQuotientEquiv ind p z) := by
  simp [rowFiniteIndexQuotientDifferential]

/-- A square-zero coefficient differential gives a square-zero quotient differential. -/
theorem rowFiniteIndexQuotientDifferential_sq_zero (d : A →ₗ[R] A)
    (hd : ∀ a, d (d a) = 0) (p : ℤ) (z) :
    rowFiniteIndexQuotientDifferential ind d p
      (rowFiniteIndexQuotientDifferential ind d p z) = 0 := by
  have hcomp : (Finsupp.mapRange.linearMap d : Module.End R ({x // ind x = p} →₀ A)) *
      (Finsupp.mapRange.linearMap d) = 0 := by
    ext f x
    exact hd _
  -- Express nested evaluation as multiplication in Module.End so that map_mul applies.
  change (((rowFiniteIndexQuotientEquiv ind p).symm.conjRingEquiv
    (Finsupp.mapRange.linearMap d)) *
    ((rowFiniteIndexQuotientEquiv ind p).symm.conjRingEquiv
      (Finsupp.mapRange.linearMap d))) z = 0
  rw [← map_mul, hcomp, map_zero, LinearMap.zero_apply]

end Quotient

section Differential

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}
  (m : P → P →₀ A) (hm : ∀ x y, ind x ≤ ind y → m x y = 0)

include hm

/-- The twisting part of the differential strictly lowers the cell filtration. -/
theorem rowFiniteTwistedDifferential_sub_mem_indexFiltration {p : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f -
      Finsupp.mapRange.linearMap d f ∈ rowFiniteIndexFiltration (R := R) ind (p - 1) := by
  classical
  rw [rowFiniteTwistedDifferential_apply, add_sub_cancel_left, Finsupp.sum]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  have hxp : ind x ≤ p := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hx ((mem_rowFiniteIndexFiltration_iff ind).mp hf x
      (lt_of_not_ge h))
  have hrow : m x ∈ Finsupp.supported A A {y | ind y ≤ p - 1} := by
    rw [Finsupp.mem_supported']
    intro y hy
    exact hm x y (by simp only [Set.mem_ofPred_eq, not_le] at hy; omega)
  exact (Finsupp.mem_supported' R _).mpr fun y hy ↦ by
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [(Finsupp.mem_supported' A _).mp hrow y hy, mul_zero]

/-- The full differential preserves every cell-filtration stage. -/
theorem rowFiniteTwistedDifferential_mem_indexFiltration {p : ℤ} {f : P →₀ A}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f ∈
      rowFiniteIndexFiltration (R := R) ind p := by
  have hcoeff : Finsupp.mapRange.linearMap d f ∈ rowFiniteIndexFiltration (R := R) ind p := by
    rw [Finsupp.mapRange.linearMap_apply]
    exact (Finsupp.mem_supported R _).2
      ((Finset.coe_subset.mpr Finsupp.support_mapRange).trans ((Finsupp.mem_supported R _).1 hf))
  have h := rowFiniteIndexFiltration_mono (R := R) (A := A) ind (by omega : p - 1 ≤ p)
    (rowFiniteTwistedDifferential_sub_mem_indexFiltration (𝒜 := 𝒜) (d := d) m hm hf)
  simpa only [sub_add_cancel] using (rowFiniteIndexFiltration (R := R) ind p).add_mem h hcoeff

/-- On the new generators the induced differential is exactly the coefficient differential. -/
theorem rowFiniteIndexProjection_differential (p : ℤ)
    (f : rowFiniteIndexFiltration (R := R) (A := A) ind p) :
    rowFiniteIndexProjection ind p
      ⟨rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f.val,
        rowFiniteTwistedDifferential_mem_indexFiltration m hm f.property⟩ =
      Finsupp.mapRange.linearMap d (rowFiniteIndexProjection ind p f) := by
  ext x
  have h := (mem_rowFiniteIndexFiltration_iff ind).mp
    (rowFiniteTwistedDifferential_sub_mem_indexFiltration (𝒜 := 𝒜) (d := d) m hm f.property)
    x.val (by omega)
  simpa only [rowFiniteIndexProjection_apply, Finsupp.sub_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, sub_eq_zero] using h

/-- On every representative the quotient differential is induced by the actual twisted
module differential, not merely an abstract isomorphic differential. -/
theorem rowFiniteIndexQuotientDifferential_mk (p : ℤ)
    (f : rowFiniteIndexFiltration (R := R) (A := A) ind p) :
    rowFiniteIndexQuotientDifferential ind d p (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk
        (⟨rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f.val,
          rowFiniteTwistedDifferential_mem_indexFiltration m hm f.property⟩ :
          rowFiniteIndexFiltration (R := R) ind p) := by
  apply (rowFiniteIndexQuotientEquiv ind p).injective
  simp only [rowFiniteIndexQuotientEquiv_differential, rowFiniteIndexQuotientEquiv_mk]
  exact (rowFiniteIndexProjection_differential m hm p f).symm

end Differential

/-! ### The coefficient differential with DG right-module coefficients -/

namespace RowFiniteTwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ} {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)
  (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)

include hm

/-- **The twisting part lowers generator indices.** For a one-sided cocycle, the coefficient
differential of a vector concentrated on `x` differs from the coefficient differential at `x` by a
vector supported on generators of smaller index. -/
theorem coefficientDifferential_single_sub_mem_supported (x : P) (α : M) :
    m.coefficientDifferential hM (Finsupp.single x α) - Finsupp.single x (dM α) ∈
      Finsupp.supported M R {y | ind y < ind x} := by
  classical
  induction α using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q α =>
    rw [m.coefficientDifferential_single hM x α.2, add_sub_cancel_left, Units.smul_def,
      Finsupp.sum]
    refine zsmul_mem (Submodule.sum_mem _ fun y hy ↦ Finsupp.single_mem_supported R _ ?_) _
    rw [Set.mem_ofPred_eq]
    by_contra h
    exact Finsupp.mem_support_iff.mp hy (hm x y (not_lt.mp h))
  | add α β hα hβ =>
    simpa only [Finsupp.single_add, map_add, add_sub_add_comm] using Submodule.add_mem _ hα hβ

/-- **The twisting part lowers the cell filtration.** For a one-sided cocycle, on the `p`th stage
of the cell filtration the coefficient differential agrees with the coordinatewise coefficient
differential up to the `(p - 1)`st stage. -/
theorem coefficientDifferential_sub_mem_indexFiltration {p : ℤ} {g : P →₀ M}
    (hg : g ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM g - Finsupp.mapRange.linearMap dM g ∈
      rowFiniteIndexFiltration (R := R) ind (p - 1) := by
  have hT : ∀ x ∈ g.support, m.coefficientDifferential hM (Finsupp.single x (g x)) -
      Finsupp.mapRange.linearMap dM (Finsupp.single x (g x)) ∈
        rowFiniteIndexFiltration (R := R) ind (p - 1) := by
    intro x hx
    have hxp : ind x ≤ p := by
      by_contra h
      exact Finsupp.mem_support_iff.mp hx
        ((mem_rowFiniteIndexFiltration_iff ind).mp hg x (not_le.mp h))
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      mem_rowFiniteIndexFiltration_iff ind]
    intro y hy
    refine (Finsupp.mem_supported' R _).mp
      (m.coefficientDifferential_single_sub_mem_supported hM hm x (g x)) y ?_
    simp only [Set.mem_ofPred_eq, not_lt]
    omega
  rw [← Finsupp.sum_single g, Finsupp.sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ hT

/-- For a one-sided cocycle, the coefficient differential preserves the cell filtration. -/
theorem coefficientDifferential_mem_indexFiltration {p : ℤ} {g : P →₀ M}
    (hg : g ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM g ∈ rowFiniteIndexFiltration (R := R) ind p := by
  have hd : Finsupp.mapRange.linearMap dM g ∈ rowFiniteIndexFiltration (R := R) ind p := by
    rw [mem_rowFiniteIndexFiltration_iff ind] at hg ⊢
    intro x hx
    simp [hg x hx]
  simpa only [sub_add_cancel] using Submodule.add_mem _
    (rowFiniteIndexFiltration_mono ind (by omega : p - 1 ≤ p)
      (m.coefficientDifferential_sub_mem_indexFiltration hM hm hg)) hd

/-- For a one-sided cocycle, on the generators of top index `p` of a vector in the `p`th stage of
the cell filtration, the coefficient differential is the coefficient differential of `M`. -/
theorem coefficientDifferential_apply_of_ind_eq {p : ℤ} {g : P →₀ M}
    (hg : g ∈ rowFiniteIndexFiltration (R := R) ind p) {x : P} (hx : ind x = p) :
    m.coefficientDifferential hM g x = dM (g x) := by
  have h := (mem_rowFiniteIndexFiltration_iff ind).mp
    (m.coefficientDifferential_sub_mem_indexFiltration hM hm hg) x (by omega)
  simpa only [Finsupp.sub_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    sub_eq_zero] using h

end RowFiniteTwistingCocycle

end TauCeti
