/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
-- Unfold the coefficient complex privately, to include the filtration stages into it.
import all TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import TauCeti.Algebra.Homology.Subobject
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The cell filtration of a row-finite twisted module

Filter the finite-support free module by the indices of its generators. Unlike a product of
coefficient modules, this filtration is exhaustive even for an infinite generator set with
unbounded indices. If the twisting rows strictly lower generator indices, the twisting part of
the differential lowers the filtration. The successive quotient is therefore the finite-support
module on generators of one index, with the coefficient differential alone.

The degree-`n` part of each stage, `rowFiniteIndexGrading`, is its intersection with the
total-degree grading; for cohomologically nonpositive coefficients, total degree `n` forces
index at most `-n`.

The quotient equivalence and its differential comparison are explicit. If generator indices
are bounded below (as for nonnegative-dimensional cells), the filtration starts at zero. These
are the algebraic cell-filtration properties needed for attaching free generators; no resolution
or quasi-isomorphism is asserted for an arbitrary twisting cocycle.

For a DG right module `ℳ` and a one-sided cocycle (`m x y = 0` whenever `ind x ≤ ind y`), the
coefficient differential on `P →₀ M` preserves the filtration, so its stages are subcomplexes
`RowFiniteTwistingCocycle.indexCochainComplex` of the coefficient complex, exhaustive with no
finiteness hypothesis on `P` (`RowFiniteTwistingCocycle.exists_mem_range_indexSubobject_arrow_f`).
The graded piece `F_{p+1} / F_p` is the complex `rowFiniteIndexGradedPieceComplex` of
finite-support families of coefficients on the generators of index `p + 1`, with the coefficient
differential in each coordinate (`RowFiniteTwistingCocycle.indexShortComplex_shortExact`).

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
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

section IndexGrading

variable {R : Type uR} {M : Type uM} {P : Type uP}
  [Semiring R] [AddCommMonoid M] [Module R M] {ℳ : ℤ → Submodule R M} {ind : P → ℤ}

/-- The degree-`n` part of the `p`th stage of the index filtration of finite-support coefficient
vectors: the vectors of total degree `n` carried by generators of index at most `p`. -/
noncomputable def rowFiniteIndexGrading (ℳ : ℤ → Submodule R M) (ind : P → ℤ) (p n : ℤ) :
    Submodule R (P →₀ M) :=
  rowFiniteIndexFiltration ind p ⊓ rowFiniteTotalGrading ℳ ind n

@[simp]
theorem mem_rowFiniteIndexGrading_iff {p n : ℤ} {f : P →₀ M} :
    f ∈ rowFiniteIndexGrading ℳ ind p n ↔
      (∀ x, p < ind x → f x = 0) ∧ ∀ x, f x ∈ ℳ (n + ind x) := by
  simp [rowFiniteIndexGrading]

/-- The index filtration is increasing in each total degree. -/
theorem rowFiniteIndexGrading_mono {p q n : ℤ} (hpq : p ≤ q) :
    rowFiniteIndexGrading ℳ ind p n ≤ rowFiniteIndexGrading ℳ ind q n :=
  inf_le_inf_right _ (rowFiniteIndexFiltration_mono ind hpq)

theorem rowFiniteIndexGrading_le_rowFiniteIndexFiltration (p n : ℤ) :
    rowFiniteIndexGrading ℳ ind p n ≤ rowFiniteIndexFiltration ind p :=
  inf_le_left

theorem rowFiniteIndexGrading_le_rowFiniteTotalGrading (p n : ℤ) :
    rowFiniteIndexGrading ℳ ind p n ≤ rowFiniteTotalGrading ℳ ind n :=
  inf_le_right

/-- For cohomologically nonpositive coefficients, a vector of total degree `n` is carried by
generators of index at most `-n`. -/
theorem rowFiniteTotalGrading_le_rowFiniteIndexFiltration (hℳ : ∀ k, 0 < k → ℳ k = ⊥) (n : ℤ) :
    rowFiniteTotalGrading ℳ ind n ≤ rowFiniteIndexFiltration ind (-n) := by
  intro f hf
  rw [mem_rowFiniteIndexFiltration_iff]
  intro x hx
  have h := (mem_rowFiniteTotalGrading_iff ℳ ind).mp hf x
  rwa [hℳ _ (by omega), Submodule.mem_bot] at h

end IndexGrading

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

section CoefficientComplex

open CategoryTheory Limits

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ} {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}

section GradedPiece

variable (hM : IsDGRightModule hA ℳ dM) (ind) in
/-- The complex of finite-support families of coefficients on the generators of index `p`, with
the coefficient differential in each coordinate. It is the graded piece `F_p / F_{p-1}` of the
index filtration of a row-finite twisted complex
(`RowFiniteTwistingCocycle.indexShortComplex_shortExact`). -/
noncomputable def rowFiniteIndexGradedPieceComplex (p : ℤ) :
    CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteTotalGrading ℳ fun x : {x // ind x = p} ↦ ind x)
    (Finsupp.mapRange.linearMap dM)
    (LinearMap.isHomogeneous_def.mpr fun n f hf ↦ by
      rw [mem_rowFiniteTotalGrading_iff] at hf ⊢
      intro x
      simpa [add_right_comm] using hM.isHomogeneous.map_mem (hf x))
    fun _ f ↦ by ext x; simp [hM.sq_zero]

variable (hM : IsDGRightModule hA ℳ dM)

/-- Identify a term of the graded-piece complex with the families of total degree `n`. -/
noncomputable def rowFiniteIndexGradedPieceComplexXEquiv (p n : ℤ) :
    (rowFiniteIndexGradedPieceComplex ind hM p).X n ≃ₗ[R]
      rowFiniteTotalGrading ℳ (fun x : {x // ind x = p} ↦ ind x) n :=
  gradedCochainComplexXEquiv n

/-- The differential of the graded-piece complex is the coefficient differential in each
coordinate. -/
theorem rowFiniteIndexGradedPieceComplexXEquiv_d (p n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p (n + 1)
        (((rowFiniteIndexGradedPieceComplex ind hM p).d n (n + 1)).hom f) :
          {x // ind x = p} →₀ M) =
      Finsupp.mapRange.linearMap dM (rowFiniteIndexGradedPieceComplexXEquiv hM p n f) :=
  gradedCochainComplexXEquiv_d n f

/-- For cohomologically nonpositive coefficients, the graded piece of index `p` vanishes in each
degree `n` with `0 < n + p`. -/
theorem isZero_rowFiniteIndexGradedPieceComplex_X (hℳ : ∀ k, 0 < k → ℳ k = ⊥) {p n : ℤ}
    (hpn : 0 < n + p) : IsZero ((rowFiniteIndexGradedPieceComplex ind hM p).X n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun f g ↦ (rowFiniteIndexGradedPieceComplexXEquiv hM p n).injective ?_⟩
  ext x
  have hf := (mem_rowFiniteTotalGrading_iff ℳ _).mp
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n f).2 x
  have hg := (mem_rowFiniteTotalGrading_iff ℳ _).mp
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n g).2 x
  rw [x.2, hℳ _ hpn, Submodule.mem_bot] at hf hg
  rw [hf, hg]

end GradedPiece

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)

/-! ### The differential and the index filtration -/

variable {m} (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
include hm

/-- On a single generator `x`, the twisting part of the coefficient differential is carried by
generators of index less than `ind x`. -/
theorem coefficientDifferential_single_sub_mem (x : P) (α : M) :
    m.coefficientDifferential hM (Finsupp.single x α) - Finsupp.single x (dM α) ∈
      rowFiniteIndexFiltration (R := R) ind (ind x - 1) := by
  classical
  induction α using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q α =>
    rw [m.coefficientDifferential_single hM x α.2, add_sub_cancel_left]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.finsuppSum_mem _ _ _ _ fun y hy ↦ ?_)
    have hyx : ind y < ind x := lt_of_not_ge fun h ↦ hy (hm x y h)
    rw [mem_rowFiniteIndexFiltration_iff]
    intro z hz
    exact Finsupp.single_eq_of_ne (by rintro rfl; omega)
  | add α β hα hβ =>
    rw [Finsupp.single_add, map_add, map_add, Finsupp.single_add, add_sub_add_comm]
    exact add_mem hα hβ

/-- On a vector carried by generators of index at most `p`, the twisting part of the coefficient
differential is carried by generators of index at most `p - 1`. -/
theorem coefficientDifferential_sub_mem_rowFiniteIndexFiltration {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM f - Finsupp.mapRange.linearMap dM f ∈
      rowFiniteIndexFiltration (R := R) ind (p - 1) := by
  have h₁ : m.coefficientDifferential hM f =
      f.sum fun x α ↦ m.coefficientDifferential hM (Finsupp.single x α) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [map_finsuppSum]
  have h₂ : Finsupp.mapRange.linearMap dM f = f.sum fun x α ↦ Finsupp.single x (dM α) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [map_finsuppSum]
    simp
  have hsum : m.coefficientDifferential hM f - Finsupp.mapRange.linearMap dM f =
      f.sum fun x α ↦ m.coefficientDifferential hM (Finsupp.single x α) -
        Finsupp.single x (dM α) := by
    rw [h₁, h₂, Finsupp.sum_sub]
  rw [hsum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun x hx ↦ ?_
  have hxp : ind x ≤ p := le_of_not_gt fun h ↦
    hx ((mem_rowFiniteIndexFiltration_iff ind).mp hf x h)
  exact rowFiniteIndexFiltration_mono ind (by omega)
    (m.coefficientDifferential_single_sub_mem hM hm x (f x))

/-- The coefficient differential preserves every stage of the index filtration. -/
theorem coefficientDifferential_mem_rowFiniteIndexFiltration {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM f ∈ rowFiniteIndexFiltration (R := R) ind p := by
  have hd : Finsupp.mapRange.linearMap dM f ∈ rowFiniteIndexFiltration (R := R) ind p := by
    rw [mem_rowFiniteIndexFiltration_iff] at hf ⊢
    intro x hx
    simp [hf x hx]
  simpa using add_mem (rowFiniteIndexFiltration_mono ind (by omega : p - 1 ≤ p)
    (m.coefficientDifferential_sub_mem_rowFiniteIndexFiltration hM hm hf)) hd

/-- On the generators of maximal index `p` of a filtration stage, the coefficient differential is
the coefficient differential of the module. -/
theorem coefficientDifferential_apply_of_eq {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) {x : P} (hx : ind x = p) :
    m.coefficientDifferential hM f x = dM (f x) := by
  have h := (mem_rowFiniteIndexFiltration_iff ind).mp
    (m.coefficientDifferential_sub_mem_rowFiniteIndexFiltration hM hm hf) x (by omega)
  simpa [sub_eq_zero] using h

/-- The coefficient differential carries the degree-`n` part of `F_p` into degree `n + 1`. -/
theorem coefficientDifferential_mem_rowFiniteIndexGrading {p n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexGrading ℳ ind p n) :
    m.coefficientDifferential hM f ∈ rowFiniteIndexGrading ℳ ind p (n + 1) :=
  mem_rowFiniteIndexGrading_iff.mpr ⟨(mem_rowFiniteIndexFiltration_iff ind).mp
      (m.coefficientDifferential_mem_rowFiniteIndexFiltration hM hm
        (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n hf)),
    (mem_rowFiniteTotalGrading_iff ℳ ind).mp ((m.isHomogeneous_coefficientDifferential hM).map_mem
      (rowFiniteIndexGrading_le_rowFiniteTotalGrading p n hf))⟩

/-! ### The filtration stages as subcomplexes -/

variable (m) in
/-- The `p`th stage `F_p` of the index filtration of the row-finite coefficient complex, as a
cochain complex of modules. -/
noncomputable def indexCochainComplex (p : ℤ) : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteIndexGrading ℳ ind p) (m.coefficientDifferential hM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      m.coefficientDifferential_mem_rowFiniteIndexGrading hM hm hf)
    fun _ f ↦ m.coefficientDifferential_sq_zero hM f

variable (m)

/-- Identify a term of `F_p` with the vectors of total degree `n` carried by generators of index
at most `p`. -/
noncomputable def indexCochainComplexXEquiv (p n : ℤ) :
    (m.indexCochainComplex hM hm p).X n ≃ₗ[R] rowFiniteIndexGrading ℳ ind p n :=
  gradedCochainComplexXEquiv n

/-- The differential of `F_p` is the coefficient differential. -/
theorem indexCochainComplexXEquiv_d (p n : ℤ) (f : (m.indexCochainComplex hM hm p).X n) :
    (m.indexCochainComplexXEquiv hM hm p (n + 1)
        (((m.indexCochainComplex hM hm p).d n (n + 1)).hom f) : P →₀ M) =
      m.coefficientDifferential hM (m.indexCochainComplexXEquiv hM hm p n f) :=
  gradedCochainComplexXEquiv_d n f

/-- The inclusion `F_p ⟶ F_q` of filtration stages, for `p ≤ q`. -/
noncomputable def indexCochainComplexMap {p q : ℤ} (hpq : p ≤ q) :
    m.indexCochainComplex hM hm p ⟶ m.indexCochainComplex hM hm q :=
  gradedCochainComplexInclusion fun _ ↦ rowFiniteIndexGrading_mono hpq

@[simp]
theorem indexCochainComplexMap_apply {p q : ℤ} (hpq : p ≤ q) (n : ℤ)
    (f : (m.indexCochainComplex hM hm p).X n) :
    (m.indexCochainComplexXEquiv hM hm q n
      (((m.indexCochainComplexMap hM hm hpq).f n).hom f) : P →₀ M) =
      m.indexCochainComplexXEquiv hM hm p n f :=
  gradedCochainComplexInclusion_apply _ n f

/-- The transition map from a filtration stage to itself is the identity. -/
@[simp]
theorem indexCochainComplexMap_id (p : ℤ) :
    m.indexCochainComplexMap hM hm (le_refl p) = 𝟙 (m.indexCochainComplex hM hm p) :=
  gradedCochainComplexInclusion_refl

/-- The transition maps of the index filtration compose. -/
@[reassoc (attr := simp)]
theorem indexCochainComplexMap_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    m.indexCochainComplexMap hM hm hpq ≫ m.indexCochainComplexMap hM hm hqr =
      m.indexCochainComplexMap hM hm (hpq.trans hqr) :=
  gradedCochainComplexInclusion_comp _ _

theorem injective_indexCochainComplexMap_f {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    Function.Injective ((m.indexCochainComplexMap hM hm hpq).f n) :=
  injective_gradedCochainComplexInclusion_f _ n

/-- The inclusion of the filtration stage `F_p` into the coefficient complex. -/
noncomputable def indexCochainComplexι (p : ℤ) :
    m.indexCochainComplex hM hm p ⟶ m.coefficientCochainComplex hM :=
  gradedCochainComplexInclusion (rowFiniteIndexGrading_le_rowFiniteTotalGrading p)

@[simp]
theorem indexCochainComplexι_apply (p n : ℤ) (f : (m.indexCochainComplex hM hm p).X n) :
    (m.coefficientCochainComplexXEquiv hM n
      (((m.indexCochainComplexι hM hm p).f n).hom f) : P →₀ M) =
      m.indexCochainComplexXEquiv hM hm p n f :=
  gradedCochainComplexInclusion_apply _ n f

instance mono_indexCochainComplexι (p : ℤ) : Mono (m.indexCochainComplexι hM hm p) :=
  mono_gradedCochainComplexInclusion _

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_ι {p q : ℤ} (hpq : p ≤ q) :
    m.indexCochainComplexMap hM hm hpq ≫ m.indexCochainComplexι hM hm q =
      m.indexCochainComplexι hM hm p :=
  gradedCochainComplexInclusion_comp _ _

/-- The index filtration as subobjects of the row-finite coefficient complex. -/
noncomputable def indexSubobject (p : ℤ) : Subobject (m.coefficientCochainComplex hM) :=
  Subobject.mk (m.indexCochainComplexι hM hm p)

/-- The filtration subobject is represented by the inclusion of the filtration stage. -/
theorem indexSubobject_eq_mk (p : ℤ) :
    m.indexSubobject hM hm p = Subobject.mk (m.indexCochainComplexι hM hm p) :=
  (rfl)

theorem indexSubobject_mono : Monotone (m.indexSubobject hM hm) := fun _ _ hpq ↦
  Subobject.mk_le_mk_of_comm (m.indexCochainComplexMap hM hm hpq)
    (m.indexCochainComplexMap_ι hM hm hpq)

/-- In degree `n`, the stage `F_p` consists of the vectors carried by generators of index at
most `p`. -/
theorem mem_range_indexSubobject_arrow_f_iff (p n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    f ∈ LinearMap.range ((m.indexSubobject hM hm p).arrow.f n).hom ↔
      ∀ x, p < ind x → (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) x = 0 := by
  rw [indexSubobject_eq_mk, Subobject.range_mk_arrow_f_hom]
  exact (mem_range_gradedCochainComplexInclusion_f_iff _ n f).trans <|
    mem_rowFiniteIndexGrading_iff.trans <| and_iff_left <|
      (mem_rowFiniteTotalGrading_iff ℳ ind).mp (m.coefficientCochainComplexXEquiv hM n f).2

/-- **The index filtration is exhaustive**, with no finiteness hypothesis on the generators:
every vector lies in some stage. -/
theorem exists_mem_range_indexSubobject_arrow_f (n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    ∃ q, f ∈ LinearMap.range ((m.indexSubobject hM hm q).arrow.f n).hom := by
  have hf : (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) ∈
      ⨆ p, rowFiniteIndexFiltration (R := R) ind p := by
    rw [iSup_rowFiniteIndexFiltration_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hq⟩ :=
    (Submodule.mem_iSup_of_directed _ (rowFiniteIndexFiltration_mono ind).directed_le).mp hf
  exact ⟨q, (m.mem_range_indexSubobject_arrow_f_iff hM hm q n f).mpr
    ((mem_rowFiniteIndexFiltration_iff ind).mp hq)⟩

/-- Below every generator index the index filtration vanishes. -/
theorem indexSubobject_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    m.indexSubobject hM hm p = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.mpr (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)
  ext f : 2
  have hf := rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n
    (m.indexCochainComplexXEquiv hM hm p n f).2
  rw [rowFiniteIndexFiltration_eq_bot ind hp, Submodule.mem_bot] at hf
  apply (m.coefficientCochainComplexXEquiv hM n).injective
  apply Subtype.ext
  simpa using hf

/-! ### The graded pieces of the index filtration -/

/-- The restriction `F_p ⟶ ⊕_{ind x = p} ℳ` from the `p`th stage of the index filtration to the
families of coefficients on the generators of index `p`. -/
noncomputable def indexCochainComplexProj (p : ℤ) :
    m.indexCochainComplex hM hm p ⟶ rowFiniteIndexGradedPieceComplex ind hM p where
  f n := ModuleCat.ofHom
    ((rowFiniteIndexGradedPieceComplexXEquiv hM p n).symm.toLinearMap ∘ₗ
      ((rowFiniteIndexProjection ind p ∘ₗ
          Submodule.inclusion (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n)).codRestrict
        _ fun f ↦ (mem_rowFiniteTotalGrading_iff ℳ _).mpr fun x ↦ by
          simpa only [LinearMap.comp_apply, rowFiniteIndexProjection_apply,
            Submodule.coe_inclusion] using (mem_rowFiniteIndexGrading_iff.mp f.2).2 x) ∘ₗ
        (m.indexCochainComplexXEquiv hM hm p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (rowFiniteIndexGradedPieceComplexXEquiv hM p (i + 1)).injective (Subtype.ext ?_))
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      rowFiniteIndexGradedPieceComplexXEquiv_d, indexCochainComplexXEquiv_d, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, rowFiniteIndexProjection_apply,
      Submodule.coe_inclusion, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    exact (m.coefficientDifferential_apply_of_eq hM hm
      (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p i
        (m.indexCochainComplexXEquiv hM hm p i f).2) x.2).symm

@[simp]
theorem indexCochainComplexProj_f_apply (p n : ℤ) (f : (m.indexCochainComplex hM hm p).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n
        (((m.indexCochainComplexProj hM hm p).f n).hom f) : {x // ind x = p} →₀ M) =
      rowFiniteIndexProjection ind p ⟨_, rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n
        (m.indexCochainComplexXEquiv hM hm p n f).2⟩ := by
  simp only [indexCochainComplexProj, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply,
    Submodule.inclusion_apply]

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_comp_proj (p : ℤ) :
    m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl) ≫
      m.indexCochainComplexProj hM hm (p + 1) = 0 := by
  ext n f : 3
  apply (rowFiniteIndexGradedPieceComplexXEquiv hM (p + 1) n).injective
  apply Subtype.ext
  ext x
  simpa using (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hM hm p n f).2).1 x
    (x.2.symm ▸ lt_add_one p)

/-- The short complex `F_p ⟶ F_{p+1} ⟶ ⊕_{ind x = p + 1} ℳ` of the index filtration, whose second
map restricts to the generators of index `p + 1`. -/
@[expose, simps]
noncomputable def indexShortComplex (p : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk (m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl))
    (m.indexCochainComplexProj hM hm (p + 1)) (m.indexCochainComplexMap_comp_proj hM hm p)

/-- The restriction to the generators of index `p` is surjective in each degree: a family on
those generators extends by zero. -/
theorem surjective_indexCochainComplexProj_f (p n : ℤ) :
    Function.Surjective ((m.indexCochainComplexProj hM hm p).f n) := by
  intro g
  set g' := (rowFiniteIndexGradedPieceComplexXEquiv hM p n g : {x // ind x = p} →₀ M)
  have hg := (mem_rowFiniteTotalGrading_iff ℳ _).mp
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n g).2
  have hf : g'.extendDomain ∈ rowFiniteIndexGrading ℳ ind p n := by
    refine mem_rowFiniteIndexGrading_iff.mpr ⟨fun x hx ↦ ?_, fun x ↦ ?_⟩
    · simp [Finsupp.extendDomain_apply, hx.ne']
    · by_cases hx : ind x = p
      · simpa [Finsupp.extendDomain_apply, hx] using hg ⟨x, hx⟩
      · simp [Finsupp.extendDomain_apply, hx]
  refine ⟨(m.indexCochainComplexXEquiv hM hm p n).symm ⟨_, hf⟩,
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n).injective (Subtype.ext ?_)⟩
  ext x
  simp [g', Finsupp.extendDomain_apply, x.2]

/-- A vector of `F_{p+1}` vanishing on the generators of index `p + 1` comes from `F_p`. -/
theorem exists_indexCochainComplexMap_f_eq (p n : ℤ)
    (g : (m.indexCochainComplex hM hm (p + 1)).X n)
    (hg : ((m.indexCochainComplexProj hM hm (p + 1)).f n) g = 0) :
    ∃ f, ((m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl)).f n) f = g := by
  have h0 := congrArg (fun z ↦ (rowFiniteIndexGradedPieceComplexXEquiv hM (p + 1) n z :
    {x // ind x = p + 1} →₀ M)) hg
  simp only [indexCochainComplexProj_f_apply, map_zero, ZeroMemClass.coe_zero] at h0
  have hker := LinearMap.mem_ker.mpr h0
  rw [ker_rowFiniteIndexProjection, add_sub_cancel_right] at hker
  exact LinearMap.mem_range.mp <| (mem_range_gradedCochainComplexInclusion_f_iff _ n g).mpr
    (mem_rowFiniteIndexGrading_iff.mpr ⟨(mem_rowFiniteIndexFiltration_iff (R := R) ind).mp hker,
      (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hM hm (p + 1) n g).2).2⟩)

/-- **The graded pieces of the index filtration.** The sequence
`F_p ⟶ F_{p+1} ⟶ ⊕_{ind x = p + 1} ℳ` is short exact: the quotient `F_{p+1} / F_p` is the complex
of families of coefficients on the generators of index `p + 1`. -/
theorem indexShortComplex_shortExact (p : ℤ) : (m.indexShortComplex hM hm p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff _).mpr (m.exists_indexCochainComplexMap_f_eq hM hm p n))
      ((ModuleCat.mono_iff_injective _).mpr
        (m.injective_indexCochainComplexMap_f hM hm (Int.le_add_one le_rfl) n))
      ((ModuleCat.epi_iff_surjective _).mpr
        (m.surjective_indexCochainComplexProj_f hM hm (p + 1) n))

/-- Restriction to the generators of index `p + 1` is a cokernel of the inclusion
`F_p ⟶ F_{p+1}`. -/
noncomputable def indexCochainComplexProjIsCokernel (p : ℤ) :
    IsColimit (CokernelCofork.ofπ (m.indexCochainComplexProj hM hm (p + 1))
      (m.indexCochainComplexMap_comp_proj hM hm p)) :=
  (m.indexShortComplex_shortExact hM hm p).gIsCokernel

end RowFiniteTwistingCocycle

end CoefficientComplex

end TauCeti
