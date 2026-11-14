/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cellular.CellModule

import Mathlib.Order.Preorder.Finite

/-!
# Classification of simple modules of a cellular algebra

Over a field `K`, Graham and Lehrer classify the simple left modules of a cellular `K`-algebra `B`
with finite cell poset `Λ`: they are in bijection with `{μ : Λ | d.cellForm μ ≠ 0}`, sending `μ`
to the radical quotient `d.CellModule μ ⧸ d.cellRadical μ`, and every such simple module is
absolutely irreducible (`End_B(L(μ)) ≃ₐ[K] K`).

This file builds the inclusive cell filtration `A(≤μ)` alongside the matrix and nondegeneracy
dictionary for `cellForm` and `cellRadical`, then establishes Graham and Lehrer's classification
and Schur's lemma over a field:

* `A(≤μ)` (`TauCeti.CellularBasis.leSpan`), the span of cellular basis vectors in cells `ν ≤ μ`,
  is an anti-involution-stable two-sided ideal that annihilates `CellModule τ` whenever `¬ τ ≤ μ`;
* `cellForm` has matrix `gramMatrix` in `cellBasis`, and `cellForm` is nondegenerate precisely when
  `cellRadical = ⊥` (over any commutative ring) and when `(gramMatrix μ).det ≠ 0` (over an integral
  domain);
* over a field `K`, when `d.cellForm ν ≠ 0`, `d.CellModule ν` is generated over `d.leSpan ν` by a
  single standard basis vector, so any nonzero `B`-linear map into `d.CellModule μ` or its radical
  quotient forces `μ ≤ ν`;
* consequently, for a partial order `Λ`, the simple quotients `d.CellModule μ ⧸ d.cellRadical μ`
  with `d.cellForm μ ≠ 0` are pairwise non-isomorphic and have scalar endomorphism algebras;
* when `Λ` is a finite partial order, every simple left `B`-module is isomorphic to
  `d.CellModule μ ⧸ d.cellRadical μ` for a unique `μ : Λ`, which automatically satisfies
  `d.cellForm μ ≠ 0`.

## Main definitions

* `TauCeti.CellularBasis.leSpan c μ`: the two-sided ideal `A(≤μ)` spanned by basis vectors in cells
  `ν ≤ μ`.
* `TauCeti.CellularBasis.endCellModuleQuotientAlgEquiv`: the `K`-algebra isomorphism
  `Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K` when `d.cellForm μ ≠ 0`.

## Main results

* `TauCeti.CellularBasis.mul_mem_leSpan`, `TauCeti.CellularBasis.mem_leSpan_mul`: `A(≤μ)` is a
  two-sided ideal.
* `TauCeti.CellularBasis.nondegenerate_cellForm_iff_cellRadical_eq_bot`,
  `TauCeti.CellularBasis.nondegenerate_cellForm_iff_det_gramMatrix_ne_zero`: nondegeneracy of the
  cell form in terms of the cell radical and the Gram determinant.
* `TauCeti.CellularBasis.le_of_cellModule_quotient_linearMap_ne_zero`: a nonzero homomorphism
  between radical quotients from a cell with nonzero form reverses the cell order.
* `TauCeti.CellularBasis.nonempty_cellModule_quotient_linearEquiv_iff`: pairwise non-isomorphism of
  simple cell quotients over a field.
* `TauCeti.CellularBasis.algebraMap_end_bijective`: every endomorphism of a simple cell quotient is
  a scalar multiple of the identity (absolute irreducibility without algebraic closure).
* `TauCeti.CellularBasis.existsUnique_cellModule_quotient_linearEquiv`: completeness and uniqueness
  of the classification of simple modules when `Λ` is finite.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Proposition 2.6, Lemma 3.3, Theorem 3.4 and Corollary 3.5.
-/

public section

open Module Submodule
open scoped Matrix

namespace TauCeti.CellularBasis

section CommRing

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] (c : CellularBasis R A M)

/-- The span `A(≤μ)` of the cellular basis vectors in cells `ν ≤ μ`. -/
noncomputable def leSpan (μ : Λ) : Submodule R A :=
  span R (c.basis '' {i | i.1 ≤ μ})

/-- `A(≤μ)` is the span of the basis vectors `C ν s t` with `ν ≤ μ`. -/
theorem leSpan_def (μ : Λ) : c.leSpan μ = span R (c.basis '' {i | i.1 ≤ μ}) := (rfl)

/-- An element lies in `A(≤μ)` exactly when its coordinates outside `{ν | ν ≤ μ}` vanish. -/
theorem mem_leSpan_iff {μ : Λ} {x : A} :
    x ∈ c.leSpan μ ↔ ∀ i : Σ μ, M μ × M μ, ¬ i.1 ≤ μ → c.basis.repr x i = 0 := by
  rw [leSpan_def, c.basis.mem_span_image]
  exact ⟨fun h i hi => by_contra fun hx => hi (h (Finsupp.mem_support_iff.2 hx)),
    fun h i hi => by_contra fun hx => Finsupp.mem_support_iff.1 hi (h i hx)⟩

/-- The basis vectors of a cell `ν ≤ μ` lie in `A(≤μ)`. -/
theorem basis_mem_leSpan {ν μ : Λ} (h : ν ≤ μ) (s t : M ν) :
    c.basis ⟨ν, s, t⟩ ∈ c.leSpan μ :=
  subset_span ⟨_, h, rfl⟩

/-- The basis vectors of the cell `μ` itself lie in `A(≤μ)`. -/
theorem basis_self_mem_leSpan (μ : Λ) (s t : M μ) :
    c.basis ⟨μ, s, t⟩ ∈ c.leSpan μ :=
  c.basis_mem_leSpan le_rfl s t

/-- The strict lower span `A(<μ)` is contained in `A(≤μ)`. -/
theorem lowerSpan_le_leSpan (μ : Λ) : c.lowerSpan μ ≤ c.leSpan μ := by
  rw [lowerSpan_def, leSpan_def]
  exact span_mono <| Set.image_mono fun _ hi => le_of_lt hi

/-- `A(≤μ)` grows with `μ`. -/
theorem leSpan_mono : Monotone c.leSpan := fun _ _ h =>
  span_mono <| Set.image_mono fun _ hi => le_trans hi h

/-- `A(≤μ)` is a left ideal. -/
theorem mul_mem_leSpan (a : A) {μ : Λ} {x : A} (hx : x ∈ c.leSpan μ) :
    a * x ∈ c.leSpan μ := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨ν, s, t⟩, hν : ν ≤ μ, rfl⟩ := hy
    have hlow : a * c.basis ⟨ν, s, t⟩ - ∑ u, c.cellRep ν a u s • c.basis ⟨ν, u, t⟩ ∈ c.leSpan μ :=
      c.leSpan_mono hν (c.lowerSpan_le_leSpan ν (c.mul_basis_sub_sum_mem a ν s t))
    have hsum : ∑ u, c.cellRep ν a u s • c.basis ⟨ν, u, t⟩ ∈ c.leSpan μ :=
      sum_mem fun u _ => smul_mem _ _ (c.basis_mem_leSpan hν u t)
    simpa using add_mem hlow hsum
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact smul_mem _ r hx

/-- The anti-involution preserves `A(≤μ)`. -/
theorem unop_antiInvolution_mem_leSpan {μ : Λ} {x : A} (hx : x ∈ c.leSpan μ) :
    (c.antiInvolution x).unop ∈ c.leSpan μ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨ν, s, t⟩, hν, rfl⟩ := hy
    simpa using c.basis_mem_leSpan hν t s
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using smul_mem _ r hx

/-- `A(≤μ)` is a right ideal. -/
theorem mem_leSpan_mul (a : A) {μ : Λ} {x : A} (hx : x ∈ c.leSpan μ) :
    x * a ∈ c.leSpan μ := by
  simpa using c.unop_antiInvolution_mem_leSpan
    (c.mul_mem_leSpan (c.antiInvolution a).unop (c.unop_antiInvolution_mem_leSpan hx))

section DecidableEq

variable [∀ μ, DecidableEq (M μ)]

/-- The cell representation of `μ` annihilates `A(≤ν)` whenever `¬ μ ≤ ν`. -/
theorem cellRep_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν) :
    c.cellRep μ x = 0 := by
  ext u s
  rw [cellRep_apply, Matrix.zero_apply]
  exact c.mem_leSpan_iff.1 (c.mem_leSpan_mul _ hx) ⟨μ, u, s⟩ h

/-- A basis vector from cell `ν` acts as zero in the cell representation of `μ` when `¬ μ ≤ ν`. -/
theorem cellRep_basis_of_not_le {ν μ : Λ} (h : ¬ μ ≤ ν) (s t : M ν) :
    c.cellRep μ (c.basis ⟨ν, s, t⟩) = 0 :=
  c.cellRep_eq_zero_of_mem_leSpan h (c.basis_self_mem_leSpan ν s t)

/-- `A(≤ν)` acts as zero on `CellModule μ` whenever `¬ μ ≤ ν`. -/
theorem smul_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν)
    (m : c.CellModule μ) : x • m = 0 := by
  apply (c.cellModuleEquiv μ).injective
  simp [c.cellRep_eq_zero_of_mem_leSpan h hx]

/-- `A(≤ν)` acts as zero on `CellModule μ ⧸ cellRadical μ` whenever `¬ μ ≤ ν`. -/
theorem smul_quotient_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν)
    (m : c.CellModule μ ⧸ c.cellRadical μ) : x • m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | _ y => rw [← Submodule.Quotient.mk_smul, c.smul_eq_zero_of_mem_leSpan h hx,
      Submodule.Quotient.mk_zero]

/-- The matrix of `cellForm μ` in the standard basis `cellBasis μ` is `gramMatrix μ`. -/
@[simp]
theorem toMatrix_cellBasis_cellForm (μ : Λ) :
    LinearMap.BilinForm.toMatrix (c.cellBasis μ) (c.cellForm μ) = c.gramMatrix μ := by
  ext s t
  simp [LinearMap.BilinForm.toMatrix_apply]

/-- The cell form vanishes precisely when the Gram matrix vanishes. -/
@[simp]
theorem cellForm_eq_zero_iff (μ : Λ) : c.cellForm μ = 0 ↔ c.gramMatrix μ = 0 := by
  rw [← (LinearMap.BilinForm.toMatrix (c.cellBasis μ)).map_eq_zero_iff,
    c.toMatrix_cellBasis_cellForm]

/-- The cell radical is the whole cell module precisely when the Gram matrix vanishes. -/
theorem cellRadical_eq_top_iff_gramMatrix_eq_zero (μ : Λ) :
    c.cellRadical μ = ⊤ ↔ c.gramMatrix μ = 0 := by
  rw [c.cellRadical_eq_top_iff, c.cellForm_eq_zero_iff]

/-- The cell form is left-separating precisely when the cell radical is trivial. -/
theorem separatingLeft_cellForm_iff_cellRadical_eq_bot (μ : Λ) :
    (c.cellForm μ).SeparatingLeft ↔ c.cellRadical μ = ⊥ := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, ← c.restrictScalars_cellRadical]
  simp [Submodule.eq_bot_iff]

/-- Because `cellForm μ` is symmetric, it is nondegenerate over any commutative ring precisely when
its radical is trivial. -/
theorem nondegenerate_cellForm_iff_cellRadical_eq_bot (μ : Λ) :
    (c.cellForm μ).Nondegenerate ↔ c.cellRadical μ = ⊥ := by
  refine ⟨fun h => (c.separatingLeft_cellForm_iff_cellRadical_eq_bot μ).mp h.1, fun h => ?_⟩
  have hL := (c.separatingLeft_cellForm_iff_cellRadical_eq_bot μ).mpr h
  refine ⟨hL, fun y hy => hL y fun x => ?_⟩
  rw [(c.isSymm_cellForm μ).eq]
  exact hy x

/-- Over an integral domain, the cell form is nondegenerate precisely when the determinant of the
Gram matrix is nonzero. -/
theorem nondegenerate_cellForm_iff_det_gramMatrix_ne_zero [IsDomain R] (μ : Λ) :
    (c.cellForm μ).Nondegenerate ↔ (c.gramMatrix μ).det ≠ 0 := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (c.cellBasis μ),
    c.toMatrix_cellBasis_cellForm]

/-- Over an integral domain, the cell radical vanishes precisely when the determinant of the Gram
matrix is nonzero. -/
theorem cellRadical_eq_bot_iff_det_gramMatrix_ne_zero [IsDomain R] (μ : Λ) :
    c.cellRadical μ = ⊥ ↔ (c.gramMatrix μ).det ≠ 0 := by
  rw [← c.nondegenerate_cellForm_iff_cellRadical_eq_bot,
    c.nondegenerate_cellForm_iff_det_gramMatrix_ne_zero]

end DecidableEq

end CommRing

section Field

variable {K B Λ : Type*} [Field K] [Ring B] [Algebra K B]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]

section Preorder

variable [Preorder Λ] (d : CellularBasis K B M)

/-- Over a field, a cell module whose form is nonzero is itself simple precisely when its radical is
trivial. -/
theorem isSimpleModule_cellModule_iff_of_cellForm_ne_zero {μ : Λ} (h : d.cellForm μ ≠ 0) :
    IsSimpleModule B (d.CellModule μ) ↔ d.cellRadical μ = ⊥ := by
  have hcoatom : IsCoatom (d.cellRadical μ) := d.isCoatom_cellRadical μ h
  refine ⟨fun _ => (eq_bot_or_eq_top (d.cellRadical μ)).resolve_right hcoatom.1, fun hbot => ?_⟩
  exact (Submodule.quotEquivOfEqBot _ hbot).symm.isSimpleModule_iff.mpr
    ((d.isSimpleModule_cellModule_quotient_iff μ).mpr h)

/-- Over a field, when `d.cellForm ν ≠ 0`, there is a standard basis vector of `d.CellModule ν`
whose `d.leSpan ν`-orbit is the entire cell module. -/
theorem exists_cellBasis_forall_exists_mem_leSpan_smul_eq {ν : Λ} (hν : d.cellForm ν ≠ 0) :
    ∃ s : M ν, ∀ x : d.CellModule ν, ∃ a ∈ d.leSpan ν, a • d.cellBasis ν s = x := by
  have hgram : d.gramMatrix ν ≠ 0 := mt (d.cellForm_eq_zero_iff ν).mpr hν
  obtain ⟨t, s, hts⟩ : ∃ t s : M ν, d.gramMatrix ν t s ≠ 0 := by
    by_contra! h
    exact hgram (Matrix.ext h)
  refine ⟨s, fun x => ?_⟩
  refine ⟨∑ u, ((d.cellBasis ν).repr x u * (d.gramMatrix ν t s)⁻¹) • d.basis ⟨ν, u, t⟩,
    sum_mem fun u _ => smul_mem _ _ (d.basis_self_mem_leSpan ν u t), ?_⟩
  have hstep (u : M ν) :
      (((d.cellBasis ν).repr x u * (d.gramMatrix ν t s)⁻¹) • d.basis ⟨ν, u, t⟩) •
          d.cellBasis ν s = (d.cellBasis ν).repr x u • d.cellBasis ν u := by
    rw [smul_assoc, d.basis_smul, d.cellForm_cellBasis, smul_smul, inv_mul_cancel_right₀ hts]
  rw [Finset.sum_smul]
  simp_rw [hstep]
  exact (d.cellBasis ν).sum_repr x

/-- A nonzero `B`-linear map from a cell module with nonzero form into another cell module reverses
the cell order (Graham–Lehrer, Proposition 2.6). -/
theorem le_of_cellModule_linearMap_ne_zero {ν μ : Λ} (hν : d.cellForm ν ≠ 0)
    {f : d.CellModule ν →ₗ[B] d.CellModule μ} (hf : f ≠ 0) : μ ≤ ν := by
  by_contra hle
  obtain ⟨s, hgen⟩ := d.exists_cellBasis_forall_exists_mem_leSpan_smul_eq hν
  apply hf
  ext x
  obtain ⟨a, ha, rfl⟩ := hgen x
  rw [map_smul, d.smul_eq_zero_of_mem_leSpan hle ha, LinearMap.zero_apply]

/-- A nonzero `B`-linear map between cell-radical quotients whose source has nonzero form reverses
the cell order (Graham–Lehrer, Lemma 3.3). -/
theorem le_of_cellModule_quotient_linearMap_ne_zero {ν μ : Λ} (hν : d.cellForm ν ≠ 0)
    {f : (d.CellModule ν ⧸ d.cellRadical ν) →ₗ[B] (d.CellModule μ ⧸ d.cellRadical μ)}
    (hf : f ≠ 0) : μ ≤ ν := by
  by_contra hle
  obtain ⟨s, hgen⟩ := d.exists_cellBasis_forall_exists_mem_leSpan_smul_eq hν
  apply hf
  ext x
  obtain ⟨a, ha, rfl⟩ := hgen x
  simp [d.smul_quotient_eq_zero_of_mem_leSpan hle ha]

/-- If `d.CellModule μ ⧸ d.cellRadical μ` is isomorphic to a simple `B`-module `S`, then
`d.cellForm μ ≠ 0`. -/
theorem cellForm_ne_zero_of_nonempty_cellModule_quotient_linearEquiv
    {S : Type*} [AddCommGroup S] [Module B S] [IsSimpleModule B S] {μ : Λ}
    (h : Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S)) : d.cellForm μ ≠ 0 := by
  obtain ⟨e⟩ := h
  exact (d.isSimpleModule_cellModule_quotient_iff μ).mp (e.isSimpleModule_iff.mpr ‹_›)

/-- **Schur's lemma for cellular algebras** (Graham–Lehrer, Corollary 3.5): over *any* field `K`,
every `B`-linear endomorphism of the simple quotient `d.CellModule μ ⧸ d.cellRadical μ` (with
`d.cellForm μ ≠ 0`) is multiplication by a scalar in `K`. -/
theorem algebraMap_end_bijective {μ : Λ} (hμ : d.cellForm μ ≠ 0) :
    Function.Bijective (algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ))) := by
  have : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  have : Nontrivial (d.CellModule μ ⧸ d.cellRadical μ) := IsSimpleModule.nontrivial B _
  refine ⟨RingHom.injective _, fun f => ?_⟩
  have hgram : d.gramMatrix μ ≠ 0 := mt (d.cellForm_eq_zero_iff μ).mpr hμ
  obtain ⟨t, s, hts⟩ : ∃ t s : M μ, d.gramMatrix μ t s ≠ 0 := by
    by_contra! h
    exact hgram (Matrix.ext h)
  obtain ⟨y, hy⟩ : ∃ y : d.CellModule μ,
      Submodule.Quotient.mk y = f (Submodule.Quotient.mk (d.cellBasis μ s)) :=
    Submodule.Quotient.mk_surjective _ _
  let r : K := (d.gramMatrix μ t s)⁻¹ * d.cellForm μ (d.cellBasis μ t) y
  refine ⟨r, ?_⟩
  have hbasis (u : M μ) :
      r • (Submodule.Quotient.mk (d.cellBasis μ u) : d.CellModule μ ⧸ d.cellRadical μ) =
        f (Submodule.Quotient.mk (d.cellBasis μ u)) := by
    have hact : d.basis ⟨μ, u, t⟩ •
        (Submodule.Quotient.mk (d.cellBasis μ s) : d.CellModule μ ⧸ d.cellRadical μ) =
          d.gramMatrix μ t s • Submodule.Quotient.mk (d.cellBasis μ u) := by
      rw [← Submodule.Quotient.mk_smul, d.basis_smul, d.cellForm_cellBasis,
        Submodule.Quotient.mk_smul]
    have hfy : d.basis ⟨μ, u, t⟩ • f (Submodule.Quotient.mk (d.cellBasis μ s)) =
        d.cellForm μ (d.cellBasis μ t) y • Submodule.Quotient.mk (d.cellBasis μ u) := by
      rw [← hy, ← Submodule.Quotient.mk_smul, d.basis_smul, Submodule.Quotient.mk_smul]
    have hmap := congrArg ((d.gramMatrix μ t s)⁻¹ • ·)
      (f.map_smul (d.basis ⟨μ, u, t⟩) (Submodule.Quotient.mk (d.cellBasis μ s)))
    rw [hact, f.map_smul_of_tower, smul_smul, inv_mul_cancel₀ hts, one_smul, hfy, smul_smul] at hmap
    exact hmap.symm
  ext x
  rw [← (d.cellBasis μ).sum_repr x]
  simp only [LinearMap.coe_comp, Function.comp_apply, Module.algebraMap_end_apply, map_sum,
    LinearMap.map_smul_of_tower, Submodule.mkQ_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hbasis]

/-- The `K`-algebra isomorphism `Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K` for a
cell `μ` with `d.cellForm μ ≠ 0`. -/
noncomputable def endCellModuleQuotientAlgEquiv {μ : Λ} (hμ : d.cellForm μ ≠ 0) :
    Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K _) (d.algebraMap_end_bijective hμ)).symm

/-- The inverse of `d.endCellModuleQuotientAlgEquiv hμ` is the canonical scalar map `algebraMap`. -/
@[simp]
theorem endCellModuleQuotientAlgEquiv_symm_apply {μ : Λ} (hμ : d.cellForm μ ≠ 0) (k : K) :
    (d.endCellModuleQuotientAlgEquiv hμ).symm k =
      algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) k := (rfl)

end Preorder

section PartialOrder

variable [PartialOrder Λ] (d : CellularBasis K B M)

/-- Distinct cells with nonzero form yield non-isomorphic simple quotients
(Graham–Lehrer, Theorem 3.4(i)). -/
theorem eq_of_nonempty_cellModule_quotient_linearEquiv {μ ν : Λ} (hμ : d.cellForm μ ≠ 0)
    (h : Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B]
      (d.CellModule ν ⧸ d.cellRadical ν))) : μ = ν := by
  obtain ⟨e⟩ := h
  have : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  have : Nontrivial (d.CellModule μ ⧸ d.cellRadical μ) := IsSimpleModule.nontrivial B _
  have hν : d.cellForm ν ≠ 0 :=
    d.cellForm_ne_zero_of_nonempty_cellModule_quotient_linearEquiv ⟨e.symm⟩
  have he : e.toLinearMap ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : d.CellModule μ ⧸ d.cellRadical μ)
    exact hx (e.injective (by simpa using LinearMap.congr_fun h0 x))
  have he' : e.symm.toLinearMap ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : d.CellModule μ ⧸ d.cellRadical μ)
    have hx' : e.symm (e x) = 0 := LinearMap.congr_fun h0 (e x)
    rw [e.symm_apply_apply] at hx'
    exact hx hx'
  exact le_antisymm (d.le_of_cellModule_quotient_linearMap_ne_zero hν he')
    (d.le_of_cellModule_quotient_linearMap_ne_zero hμ he)

/-- Over a field, two radical quotients of a cellular algebra with `d.cellForm μ ≠ 0` are
isomorphic if and only if their cells are equal. -/
theorem nonempty_cellModule_quotient_linearEquiv_iff {μ ν : Λ} (hμ : d.cellForm μ ≠ 0) :
    Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B]
      (d.CellModule ν ⧸ d.cellRadical ν)) ↔ μ = ν :=
  ⟨d.eq_of_nonempty_cellModule_quotient_linearEquiv hμ,
    fun h => h ▸ ⟨LinearEquiv.refl _ _⟩⟩

/-- **Completeness of cellular simple modules** (Graham–Lehrer, Theorem 3.4(ii)): when the cell
poset `Λ` is finite, every simple left `B`-module is isomorphic to
`d.CellModule μ ⧸ d.cellRadical μ` for some cell `μ` with `d.cellForm μ ≠ 0`. -/
theorem exists_cellModule_quotient_linearEquiv [Finite Λ]
    (S : Type*) [AddCommGroup S] [Module B S] [IsSimpleModule B S] :
    ∃ μ : Λ, d.cellForm μ ≠ 0 ∧ Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  have : Nontrivial S := IsSimpleModule.nontrivial B S
  have : Fintype Λ := Fintype.ofFinite Λ
  let P : Set Λ := {ν | ∃ (s t : M ν) (x : S), d.basis ⟨ν, s, t⟩ • x ≠ 0}
  have hP : P.Nonempty := by
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : S)
    rw [Set.nonempty_def]
    by_contra! hP0
    have hall (i : Σ ν, M ν × M ν) : d.basis i • v₀ = 0 := by
      by_contra hne
      exact hP0 i.1 ⟨i.2.1, i.2.2, v₀, hne⟩
    have h1 : (1 : B) • v₀ = 0 := by
      rw [← d.basis.sum_repr (1 : B), Finset.sum_smul]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.smul_def, mul_smul, hall i, smul_zero]
    exact hv₀ (by simpa using h1)
  obtain ⟨μ, ⟨s₀, t₀, x₀, hx₀⟩, hmin⟩ := (Set.toFinite P).exists_minimal hP
  have hlower {z : B} (hz : z ∈ d.lowerSpan μ) (x : S) : z • x = 0 := by
    rw [d.lowerSpan_def] at hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨ν, s, t⟩, hν : ν < μ, rfl⟩ := hy
      by_contra hne
      exact not_le_of_gt hν (hmin ⟨s, t, x, hne⟩ hν.le)
    | zero => exact zero_smul B x
    | add y₁ y₂ _ _ ih₁ ih₂ => rw [add_smul, ih₁, ih₂, add_zero]
    | smul r y _ ih => rw [Algebra.smul_def, mul_smul, ih, smul_zero]
  let φ : d.CellModule μ →ₗ[B] S :=
    { toFun := fun y =>
        ∑ s : M μ, algebraMap K B ((d.cellBasis μ).repr y s) • (d.basis ⟨μ, s, t₀⟩ • x₀)
      map_add' := fun y₁ y₂ => by
        simp [map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun b y => by
        have hmul (u : M μ) : b • (d.basis ⟨μ, u, t₀⟩ • x₀) =
            ∑ s : M μ, algebraMap K B (d.cellRep μ b s u) • (d.basis ⟨μ, s, t₀⟩ • x₀) := by
          have hsub := hlower (d.mul_basis_sub_sum_mem b μ u t₀) x₀
          rw [sub_smul, sub_eq_zero, mul_smul, Finset.sum_smul] at hsub
          rw [hsub]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Algebra.smul_def, mul_smul]
        simp only [RingHom.id_apply, cellBasis_repr_apply, cellModuleEquiv_smul, Matrix.mulVec,
          dotProduct, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum]
        conv_rhs =>
          arg 2
          ext u
          rw [← mul_smul, ← Algebra.commutes, mul_smul, hmul u, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
        rw [← map_mul, mul_comm, map_mul, mul_smul] }
  have hφ_basis : φ (d.cellBasis μ s₀) = d.basis ⟨μ, s₀, t₀⟩ • x₀ := by
    simp [φ, cellModuleEquiv_cellBasis, Pi.single_apply]
  have hφ_ne : φ ≠ 0 := by
    intro h0
    apply hx₀
    rw [← hφ_basis, h0, LinearMap.zero_apply]
  have hsurj : Function.Surjective φ := LinearMap.surjective_of_ne_zero hφ_ne
  have hcoatom : IsCoatom (LinearMap.ker φ) := LinearMap.isCoatom_ker_of_surjective hsurj
  have hle : LinearMap.ker φ ≤ d.cellRadical μ := d.le_cellRadical_of_ne_top μ _ hcoatom.1
  obtain ⟨y₀, hy₀_eq⟩ := hsurj x₀
  have hy₀ : d.basis ⟨μ, s₀, t₀⟩ • y₀ ≠ 0 := by
    intro h0
    apply hx₀
    rw [← hy₀_eq, ← φ.map_smul, h0, map_zero]
  have hform : d.cellForm μ ≠ 0 := by
    intro h0
    apply hy₀
    rw [d.basis_smul, h0]
    simp
  have hrad_ne_top : d.cellRadical μ ≠ ⊤ := mt (d.cellRadical_eq_top_iff μ).mp hform
  have hker : LinearMap.ker φ = d.cellRadical μ :=
    le_antisymm hle (by
      by_contra hlt
      exact hrad_ne_top (hcoatom.2 _ (lt_of_le_of_ne hle fun h => hlt (le_of_eq h.symm))))
  exact ⟨μ, hform, ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    (φ.quotKerEquivOfSurjective hsurj)⟩⟩

/-- **Classification of simple modules of a cellular algebra** (Graham–Lehrer, Theorem 3.4): when
`Λ` is a finite partial order, every simple left `B`-module is isomorphic to
`d.CellModule μ ⧸ d.cellRadical μ` for a unique cell `μ : Λ`. -/
theorem existsUnique_cellModule_quotient_linearEquiv [Finite Λ]
    (S : Type*) [AddCommGroup S] [Module B S] [IsSimpleModule B S] :
    ∃! μ : Λ, Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  obtain ⟨μ, hμ, ⟨e⟩⟩ := d.exists_cellModule_quotient_linearEquiv S
  refine ⟨μ, ⟨e⟩, fun ν ⟨e'⟩ => ?_⟩
  exact (d.eq_of_nonempty_cellModule_quotient_linearEquiv hμ ⟨e.trans e'.symm⟩).symm

end PartialOrder

end Field

end TauCeti.CellularBasis
