/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Algebra.Cellular.CellModule
import TauCeti.RingTheory.Semisimple.Schur

/-!
# Classification of simple modules of a cellular algebra

Over a commutative ring `R`, the inclusive cell spans `A(≤μ)` (`TauCeti.CellularBasis.leSpan`)
assemble into an anti-involution-stable two-sided ideal filtration of a cellular `R`-algebra `A`
whose stages annihilate `c.CellModule τ` and `c.CellModule τ ⧸ c.cellRadical τ` whenever
`¬ τ ≤ μ`.

Over a field `K`, Graham and Lehrer classify the simple left modules of a cellular `K`-algebra `B`
in terms of its cell modules `d.CellModule μ` and the radicals `d.cellRadical μ` of their canonical
bilinear forms `d.cellForm μ`:

* **Inclusive cell filtration and cyclic generation (Lemma 2.5):** whenever `d.cellForm ν ≠ 0`,
  `d.CellModule ν` is generated over `d.leSpan ν` by a single standard basis vector
  (`TauCeti.CellularBasis.exists_cellBasis_forall_exists_mem_leSpan_smul_eq`), so any nonzero
  `B`-linear map `d.CellModule ν →ₗ[B] d.CellModule μ` forces `μ ≤ ν`
  (`TauCeti.CellularBasis.le_of_cellModule_linearMap_ne_zero`).
* **Scalar endomorphisms (Proposition 2.6):** whenever `d.cellForm μ ≠ 0`, every `B`-linear
  endomorphism of the simple quotient `L(μ) = d.CellModule μ ⧸ d.cellRadical μ` is given by scalar
  multiplication from `K` (`TauCeti.CellularBasis.endCellModuleQuotientAlgEquiv`), without assuming
  that `K` is algebraically closed.
* **Triangularity of homomorphisms (Proposition 3.2):** a nonzero `B`-linear map from
  `d.CellModule ν` into `d.CellModule μ ⧸ d.cellRadical μ` forces `ν = μ ∨ ν < μ`
  (`TauCeti.CellularBasis.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero`), and hence `ν ≤ μ`
  (`TauCeti.CellularBasis.le_of_linearMap_cellModule_quotient_ne_zero`).
* **Pairwise non-isomorphism (Theorem 3.4(i)):** for cells with nonzero form, `L(μ)` and `L(ν)` are
  `B`-linearly equivalent if and only if `μ = ν`
  (`TauCeti.CellularBasis.nonempty_cellModule_quotient_linearEquiv_iff`), and for any `ν ≠ μ` the
  hom space between `d.CellModule ν ⧸ d.cellRadical ν` and `d.CellModule μ ⧸ d.cellRadical μ` is a
  subsingleton (`TauCeti.CellularBasis.subsingleton_linearMap_cellModule_quotient_of_ne`).
* **Exhaustiveness (Theorem 3.4(ii)):** when `<` on `Λ` is well-founded (in particular for any
  finite cell preorder), every simple `B`-module is `B`-linearly equivalent to `L(μ)` for a unique
  cell `μ`, which automatically satisfies `d.cellForm μ ≠ 0`
  (`TauCeti.CellularBasis.existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv`,
  `TauCeti.CellularBasis.existsUnique_cellModule_quotient_linearEquiv`), and its `B`-endomorphism
  algebra is isomorphic to `K` (`TauCeti.CellularBasis.endAlgEquivOfIsSimpleModule`).

## Main definitions

* `TauCeti.CellularBasis.leSpan`: the inclusive two-sided ideal `A(≤μ)` spanned by basis vectors in
  cells `ν ≤ μ`.
* `TauCeti.CellularBasis.endCellModuleQuotientAlgEquiv`: the `K`-algebra isomorphism
  `Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K` for a cell with `d.cellForm μ ≠ 0`.
* `TauCeti.CellularBasis.endAlgEquivOfIsSimpleModule`: the `K`-algebra isomorphism
  `Module.End B S ≃ₐ[K] K` for any simple `B`-module `S` when `[WellFoundedLT Λ]`.

## Main results

* `TauCeti.CellularBasis.mul_mem_leSpan`, `TauCeti.CellularBasis.mem_leSpan_mul`: `A(≤μ)` is a
  two-sided ideal annihilating `CellModule τ` when `¬ τ ≤ μ`
  (`TauCeti.CellularBasis.smul_eq_zero_of_mem_leSpan`).
* `TauCeti.CellularBasis.le_of_cellModule_linearMap_ne_zero`: when `d.cellForm ν ≠ 0`, a nonzero
  map `d.CellModule ν →ₗ[B] d.CellModule μ` implies `μ ≤ ν`.
* `TauCeti.CellularBasis.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero`,
  `TauCeti.CellularBasis.le_of_linearMap_cellModule_quotient_ne_zero`: a nonzero map
  `d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ` implies `ν = μ ∨ ν < μ` (and `ν ≤ μ`).
* `TauCeti.CellularBasis.nonempty_cellModule_quotient_linearEquiv_iff`: simple cell quotients at
  `μ` and `ν` are isomorphic if and only if `μ = ν`.
* `TauCeti.CellularBasis.existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv`,
  `TauCeti.CellularBasis.existsUnique_cellModule_quotient_linearEquiv`: every simple `B`-module is
  isomorphic to a unique `d.CellModule μ ⧸ d.cellRadical μ` (with `d.cellForm μ ≠ 0`).
* `TauCeti.CellularBasis.finrank_end_eq_one_of_isSimpleModule`: every simple `B`-module has
  one-dimensional endomorphism algebra over `K`.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Lemma 2.5, Proposition 2.6, Proposition 3.2, and Theorem 3.4.
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
theorem leSpan_def (μ : Λ) : c.leSpan μ = span R (c.basis '' {i | i.1 ≤ μ}) :=
  (rfl)

/-- An element lies in `A(≤μ)` exactly when its coordinates outside `{ν | ν ≤ μ}` vanish. -/
theorem mem_leSpan_iff {μ : Λ} {x : A} :
    x ∈ c.leSpan μ ↔ ∀ i : Σ μ, M μ × M μ, ¬ i.1 ≤ μ → c.basis.repr x i = 0 := by
  rw [leSpan_def, c.basis.mem_span_image]
  exact ⟨fun h i hi ↦ by_contra fun hx ↦ hi (h (Finsupp.mem_support_iff.2 hx)),
    fun h i hi ↦ by_contra fun hx ↦ Finsupp.mem_support_iff.1 hi (h i hx)⟩

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
  exact span_mono <| Set.image_mono fun _ hi ↦ le_of_lt hi

/-- `A(≤μ)` grows with `μ`. -/
theorem leSpan_mono : Monotone c.leSpan := fun _ _ h ↦
  span_mono <| Set.image_mono fun _ hi ↦ le_trans hi h

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
      sum_mem fun u _ ↦ smul_mem _ _ (c.basis_mem_leSpan hν u t)
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

/-- `A(≤ν)` acts as zero on `CellModule μ` whenever `¬ μ ≤ ν`. -/
theorem smul_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν)
    (m : c.CellModule μ) : x • m = 0 := by
  apply (c.cellModuleEquiv μ).injective
  simp [c.cellRep_eq_zero_of_mem_leSpan h hx]

/-- `A(≤ν)` acts as zero on `CellModule μ ⧸ cellRadical μ` whenever `¬ μ ≤ ν`. -/
theorem smul_quotient_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν)
    (m : c.CellModule μ ⧸ c.cellRadical μ) : x • m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | _ y =>
    rw [← Submodule.Quotient.mk_smul, c.smul_eq_zero_of_mem_leSpan h hx, Submodule.Quotient.mk_zero]

/-- The cell radical is the whole cell module precisely when the Gram matrix vanishes. -/
theorem cellRadical_eq_top_iff_gramMatrix_eq_zero (μ : Λ) :
    c.cellRadical μ = ⊤ ↔ c.gramMatrix μ = 0 := by
  rw [c.cellRadical_eq_top_iff, c.cellForm_eq_zero_iff]

end DecidableEq

end CommRing

section Field

variable {K B Λ : Type*} [Field K] [Ring B] [Algebra K B] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (d : CellularBasis K B M)

/-- Over a field, a cell module whose form is nonzero is itself simple precisely when its radical is
trivial. -/
theorem isSimpleModule_cellModule_iff_of_cellForm_ne_zero {μ : Λ} (h : d.cellForm μ ≠ 0) :
    IsSimpleModule B (d.CellModule μ) ↔ d.cellRadical μ = ⊥ := by
  have hcoatom : IsCoatom (d.cellRadical μ) := d.isCoatom_cellRadical μ h
  refine ⟨fun _ ↦ (eq_bot_or_eq_top (d.cellRadical μ)).resolve_right hcoatom.1, fun hbot ↦ ?_⟩
  exact (Submodule.quotEquivOfEqBot _ hbot).symm.isSimpleModule_iff.mpr
    ((d.isSimpleModule_cellModule_quotient_iff μ).mpr h)

/-- Over a field, when `d.cellForm ν ≠ 0`, there is a standard basis vector of `d.CellModule ν`
whose `d.leSpan ν`-orbit is the entire cell module (Graham–Lehrer, Lemma 2.5). -/
theorem exists_cellBasis_forall_exists_mem_leSpan_smul_eq {ν : Λ} (hν : d.cellForm ν ≠ 0) :
    ∃ s : M ν, ∀ x : d.CellModule ν, ∃ a ∈ d.leSpan ν, a • d.cellBasis ν s = x := by
  obtain ⟨t, s, hts⟩ := d.exists_gramMatrix_ne_zero hν
  refine ⟨s, fun x ↦ ?_⟩
  refine ⟨∑ u, ((d.cellBasis ν).repr x u * (d.gramMatrix ν t s)⁻¹) • d.basis ⟨ν, u, t⟩,
    sum_mem fun u _ ↦ smul_mem _ _ (d.basis_self_mem_leSpan ν u t), ?_⟩
  have hstep (u : M ν) :
      (((d.cellBasis ν).repr x u * (d.gramMatrix ν t s)⁻¹) • d.basis ⟨ν, u, t⟩) •
          d.cellBasis ν s = (d.cellBasis ν).repr x u • d.cellBasis ν u := by
    rw [smul_assoc, d.basis_smul, d.cellForm_cellBasis, smul_smul, inv_mul_cancel_right₀ hts]
  rw [Finset.sum_smul]
  simp_rw [hstep]
  exact (d.cellBasis ν).sum_repr x

/-- A nonzero `B`-linear map from a cell module with nonzero form into another cell module reverses
the cell order (Graham–Lehrer, Lemma 2.5 / Proposition 2.6). -/
theorem le_of_cellModule_linearMap_ne_zero {ν μ : Λ} (hν : d.cellForm ν ≠ 0)
    {f : d.CellModule ν →ₗ[B] d.CellModule μ} (hf : f ≠ 0) : μ ≤ ν := by
  by_contra hle
  obtain ⟨s, hgen⟩ := d.exists_cellBasis_forall_exists_mem_leSpan_smul_eq hν
  apply hf
  ext x
  obtain ⟨a, ha, rfl⟩ := hgen x
  rw [map_smul, d.smul_eq_zero_of_mem_leSpan hle ha, LinearMap.zero_apply]

/-- If `d.CellModule μ ⧸ d.cellRadical μ` is isomorphic to a simple `B`-module `S`, then
`d.cellForm μ ≠ 0`. -/
theorem cellForm_ne_zero_of_nonempty_cellModule_quotient_linearEquiv
    {S : Type*} [AddCommGroup S] [Module B S] [IsSimpleModule B S] {μ : Λ}
    (h : Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S)) : d.cellForm μ ≠ 0 := by
  obtain ⟨e⟩ := h
  exact (d.isSimpleModule_cellModule_quotient_iff μ).mp (e.isSimpleModule_iff.mpr ‹_›)

/-- A cell with nonzero form admits indices `s t : M μ` such that `d.gramMatrix μ s t ≠ 0` and the
image of `d.cellBasis μ t` in `d.CellModule μ ⧸ d.cellRadical μ` is nonzero. -/
private theorem exists_gramMatrix_ne_zero_and_mk_ne_zero {μ : Λ} (h : d.cellForm μ ≠ 0) :
    ∃ s t : M μ, d.gramMatrix μ s t ≠ 0 ∧
      (Submodule.Quotient.mk (d.cellBasis μ t) : d.CellModule μ ⧸ d.cellRadical μ) ≠ 0 := by
  obtain ⟨s, t, hst⟩ := d.exists_gramMatrix_ne_zero h
  have ht : d.cellBasis μ t ∉ d.cellRadical μ := fun hrad ↦
    hst (by rw [← d.cellForm_cellBasis, (d.isSymm_cellForm μ).eq, (d.mem_cellRadical μ _).mp hrad])
  exact ⟨s, t, hst, mt (Submodule.Quotient.mk_eq_zero (d.cellRadical μ)).mp ht⟩

/-- **Graham–Lehrer Proposition 2.6 (scalar endomorphisms).** Over any field `K`, if
`d.cellForm μ ≠ 0`, the structure map `K → Module.End B (d.CellModule μ ⧸ d.cellRadical μ)` is
bijective: every `B`-linear endomorphism of the simple cell quotient is scalar multiplication. -/
theorem algebraMap_end_cellModule_quotient_bijective {μ : Λ} (h : d.cellForm μ ≠ 0) :
    Function.Bijective (algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ))) := by
  let Q := d.CellModule μ ⧸ d.cellRadical μ
  have hsimple : IsSimpleModule B Q := (d.isSimpleModule_cellModule_quotient_iff μ).mpr h
  have : Nontrivial Q := IsSimpleModule.nontrivial B Q
  refine ⟨(algebraMap K (Module.End B Q)).injective, fun f ↦ ?_⟩
  obtain ⟨s, t, hst, hq⟩ := d.exists_gramMatrix_ne_zero_and_mk_ne_zero h
  let q : Q := Submodule.Quotient.mk (d.cellBasis μ t)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (d.cellRadical μ) (f q)
  let r : K := (d.gramMatrix μ s t)⁻¹ * d.cellForm μ (d.cellBasis μ s) y
  have hfq : f q = r • q := by
    have hact : d.basis ⟨μ, t, s⟩ • f q = d.basis ⟨μ, t, s⟩ • Submodule.Quotient.mk y :=
      congrArg (d.basis ⟨μ, t, s⟩ • ·) hy.symm
    rw [← map_smul, ← Submodule.Quotient.mk_smul, d.basis_smul, d.cellForm_cellBasis,
      Submodule.Quotient.mk_smul, LinearMap.map_smul_of_tower, ← Submodule.Quotient.mk_smul,
      d.basis_smul, Submodule.Quotient.mk_smul] at hact
    simpa [r, q, smul_smul, hst] using congrArg ((d.gramMatrix μ s t)⁻¹ • ·) hact
  refine ⟨r, ?_⟩
  have hker : ¬ Function.Injective (f - algebraMap K (Module.End B Q) r) := fun hinj ↦
    hq (hinj (by simp [q, hfq, Algebra.algebraMap_eq_smul_one]))
  rcases (f - algebraMap K (Module.End B Q) r).bijective_or_eq_zero with ⟨hinj, -⟩ | hzero
  · exact (hker hinj).elim
  · exact (sub_eq_zero.mp hzero).symm

/-- The `K`-algebra equivalence `Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K` given by
`algebraMap_end_cellModule_quotient_bijective` when `d.cellForm μ ≠ 0`. -/
noncomputable def endCellModuleQuotientAlgEquiv {μ : Λ} (h : d.cellForm μ ≠ 0) :
    Module.End B (d.CellModule μ ⧸ d.cellRadical μ) ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)))
    (d.algebraMap_end_cellModule_quotient_bijective h)).symm

/-- The inverse of `endCellModuleQuotientAlgEquiv` is `algebraMap`. -/
@[simp]
theorem endCellModuleQuotientAlgEquiv_symm_apply {μ : Λ} (h : d.cellForm μ ≠ 0) (k : K) :
    (d.endCellModuleQuotientAlgEquiv h).symm k =
      algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) k :=
  (rfl)

/-- Every `B`-linear endomorphism of `d.CellModule μ ⧸ d.cellRadical μ` acts by its image under
`endCellModuleQuotientAlgEquiv`. -/
@[simp]
theorem endCellModuleQuotientAlgEquiv_smul {μ : Λ} (h : d.cellForm μ ≠ 0)
    (f : Module.End B (d.CellModule μ ⧸ d.cellRadical μ))
    (x : d.CellModule μ ⧸ d.cellRadical μ) :
    d.endCellModuleQuotientAlgEquiv h f • x = f x := by
  conv_rhs => rw [← (d.endCellModuleQuotientAlgEquiv h).symm_apply_apply f]
  rw [endCellModuleQuotientAlgEquiv_symm_apply, Module.algebraMap_end_apply]

/-- Over a field `K`, the `B`-endomorphism algebra of `d.CellModule μ ⧸ d.cellRadical μ` has
dimension `1` whenever `d.cellForm μ ≠ 0`. -/
theorem finrank_end_cellModule_quotient {μ : Λ} (h : d.cellForm μ ≠ 0) :
    Module.finrank K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) = 1 := by
  rw [(d.endCellModuleQuotientAlgEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **Graham–Lehrer Proposition 3.2 (ordering of homomorphisms).** If
`f : d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ` is nonzero, then `ν = μ ∨ ν < μ`. -/
theorem eq_or_lt_of_linearMap_cellModule_quotient_ne_zero {μ ν : Λ}
    {f : d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ} (hf : f ≠ 0) :
    ν = μ ∨ ν < μ := by
  have hμ : d.cellForm μ ≠ 0 := fun h0 ↦ hf <| by
    have : Subsingleton (d.CellModule μ ⧸ d.cellRadical μ) :=
      Submodule.Quotient.subsingleton_iff.mpr ((d.cellRadical_eq_top_iff μ).mpr h0)
    exact Subsingleton.elim f 0
  have : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  obtain ⟨s, t, hst, hq⟩ := d.exists_gramMatrix_ne_zero_and_mk_ne_zero hμ
  let q : d.CellModule μ ⧸ d.cellRadical μ := Submodule.Quotient.mk (d.cellBasis μ t)
  obtain ⟨w, hw⟩ := f.surjective_of_ne_zero hf q
  by_contra! h
  have hact : f (d.basis ⟨μ, t, s⟩ • w) = d.gramMatrix μ s t • q := by
    rw [map_smul, hw, ← Submodule.Quotient.mk_smul, d.basis_smul, d.cellForm_cellBasis,
      Submodule.Quotient.mk_smul]
  rw [d.basis_smul_eq_zero_of_ne_of_not_lt h.1 h.2, map_zero] at hact
  exact (smul_ne_zero hst hq) hact.symm

/-- Order form of `eq_or_lt_of_linearMap_cellModule_quotient_ne_zero`: a nonzero `B`-linear map
`d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ` implies `ν ≤ μ`. -/
theorem le_of_linearMap_cellModule_quotient_ne_zero {μ ν : Λ}
    {f : d.CellModule ν →ₗ[B] d.CellModule μ ⧸ d.cellRadical μ} (hf : f ≠ 0) :
    ν ≤ μ :=
  le_of_eq_or_lt (d.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero hf)

/-- There is no `B`-linear equivalence between `d.CellModule μ ⧸ d.cellRadical μ` and
`d.CellModule ν ⧸ d.cellRadical ν` when `d.cellForm μ ≠ 0` and `μ ≠ ν`. -/
theorem isEmpty_cellModule_quotient_linearEquiv_of_ne {μ ν : Λ} (hμ : d.cellForm μ ≠ 0)
    (hne : μ ≠ ν) :
    IsEmpty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] (d.CellModule ν ⧸ d.cellRadical ν)) := by
  refine ⟨fun e ↦ ?_⟩
  have hsm : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  have hsn : IsSimpleModule B (d.CellModule ν ⧸ d.cellRadical ν) := IsSimpleModule.congr e.symm
  have hf₁ : e.toLinearMap ∘ₗ (d.cellRadical μ).mkQ ≠ 0 := by
    have : Nontrivial (d.CellModule ν ⧸ d.cellRadical ν) := IsSimpleModule.nontrivial B _
    exact LinearMap.ne_zero_of_surjective (e.surjective.comp (Submodule.Quotient.mk_surjective _))
  have hf₂ : e.symm.toLinearMap ∘ₗ (d.cellRadical ν).mkQ ≠ 0 := by
    have : Nontrivial (d.CellModule μ ⧸ d.cellRadical μ) := IsSimpleModule.nontrivial B _
    exact LinearMap.ne_zero_of_surjective
      (e.symm.surjective.comp (Submodule.Quotient.mk_surjective _))
  have h₁ := (d.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero hf₁).resolve_left hne
  have h₂ := (d.eq_or_lt_of_linearMap_cellModule_quotient_ne_zero hf₂).resolve_left hne.symm
  exact lt_asymm h₁ h₂

/-- **Graham–Lehrer Theorem 3.4(i) (pairwise non-isomorphism).** For `d.cellForm μ ≠ 0`, the simple
quotient `d.CellModule μ ⧸ d.cellRadical μ` is `B`-linearly equivalent to
`d.CellModule ν ⧸ d.cellRadical ν` if and only if `μ = ν`. -/
theorem nonempty_cellModule_quotient_linearEquiv_iff {μ ν : Λ} (hμ : d.cellForm μ ≠ 0) :
    Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] (d.CellModule ν ⧸ d.cellRadical ν)) ↔
      μ = ν := by
  refine ⟨fun ⟨e⟩ ↦ by_contra fun hne ↦
    (d.isEmpty_cellModule_quotient_linearEquiv_of_ne hμ hne).false e, ?_⟩
  rintro rfl
  exact ⟨LinearEquiv.refl B _⟩

/-- For distinct cells `ν ≠ μ`, the space of `B`-linear maps from `d.CellModule ν ⧸ d.cellRadical ν`
to `d.CellModule μ ⧸ d.cellRadical μ` is a subsingleton. -/
theorem subsingleton_linearMap_cellModule_quotient_of_ne {μ ν : Λ} (hne : ν ≠ μ) :
    Subsingleton ((d.CellModule ν ⧸ d.cellRadical ν) →ₗ[B] (d.CellModule μ ⧸ d.cellRadical μ)) := by
  by_cases hν : d.cellForm ν = 0
  · have : Subsingleton (d.CellModule ν ⧸ d.cellRadical ν) :=
      Submodule.Quotient.subsingleton_iff.mpr ((d.cellRadical_eq_top_iff ν).mpr hν)
    infer_instance
  by_cases hμ : d.cellForm μ = 0
  · have : Subsingleton (d.CellModule μ ⧸ d.cellRadical μ) :=
      Submodule.Quotient.subsingleton_iff.mpr ((d.cellRadical_eq_top_iff μ).mpr hμ)
    infer_instance
  have : IsSimpleModule B (d.CellModule ν ⧸ d.cellRadical ν) :=
    (d.isSimpleModule_cellModule_quotient_iff ν).mpr hν
  have : IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) :=
    (d.isSimpleModule_cellModule_quotient_iff μ).mpr hμ
  exact subsingleton_linearMap_of_isEmpty_linearEquiv
    (d.isEmpty_cellModule_quotient_linearEquiv_of_ne hν hne)

section WellFounded

variable [WellFoundedLT Λ]

omit [∀ μ, DecidableEq (M μ)] in
/-- In a cellular algebra with well-founded cell order, any nontrivial `B`-module `S` admits a
minimal cell acting nontrivially on `S`, whose lower span `d.lowerSpan μ` annihilates `S`. -/
private theorem exists_minimal_basis_smul_ne_zero (S : Type*) [AddCommGroup S] [Module B S]
    [Nontrivial S] :
    ∃ (μ : Λ) (s t : M μ) (x : S), d.basis ⟨μ, s, t⟩ • x ≠ 0 ∧
      ∀ z ∈ d.lowerSpan μ, ∀ y : S, z • y = 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  have hex : ∃ μ : Λ, ∃ (s t : M μ) (y : S), d.basis ⟨μ, s, t⟩ • y ≠ 0 := by
    by_contra! h0
    apply hx
    calc x = (1 : B) • x := (one_smul B x).symm
      _ = (Finsupp.linearCombination K d.basis (d.basis.repr 1)) • x := by
          rw [d.basis.linearCombination_repr]
      _ = 0 := by
          rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_smul]
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          rw [Algebra.smul_def, mul_smul, h0 i.1 i.2.1 i.2.2 x, smul_zero]
  obtain ⟨μ, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun μ ↦ ∃ (s t : M μ) (y : S), d.basis ⟨μ, s, t⟩ • y ≠ 0) hex
  obtain ⟨s, t, x₀, hx₀⟩ := hmin.prop
  refine ⟨μ, s, t, x₀, hx₀, fun z hz y ↦ ?_⟩
  rw [lowerSpan_def] at hz
  induction hz using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨⟨ν, u, v⟩, hν : ν < μ, rfl⟩ := hb
    by_contra hne
    exact hmin.not_prop_of_lt hν ⟨u, v, y, hne⟩
  | zero => exact zero_smul B y
  | add b₁ b₂ _ _ ih₁ ih₂ => rw [add_smul, ih₁, ih₂, add_zero]
  | smul r b _ ih => rw [Algebra.smul_def, mul_smul, ih, smul_zero]

/-- **Graham–Lehrer Theorem 3.4(ii) (exhaustiveness).** Over a field `K`, when `<` on `Λ` is
well-founded (in particular when `Λ` is finite), every simple `B`-module is `B`-linearly equivalent
to `d.CellModule μ ⧸ d.cellRadical μ` for some cell `μ` with `d.cellForm μ ≠ 0`. -/
theorem exists_cellForm_ne_zero_and_nonempty_linearEquiv (S : Type*) [AddCommGroup S]
    [Module B S] [IsSimpleModule B S] :
    ∃ μ : Λ, d.cellForm μ ≠ 0 ∧ Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  have : Nontrivial S := IsSimpleModule.nontrivial B S
  obtain ⟨μ, s₀, t₀, x₀, hx₀, hlow⟩ := d.exists_minimal_basis_smul_ne_zero S
  let f : d.CellModule μ →ₗ[B] S := d.cellModuleHom t₀ x₀ fun z hz ↦ hlow z hz x₀
  have hf_ne : f ≠ 0 := fun h0 ↦ hx₀ <| by
    simpa [f] using LinearMap.congr_fun h0 (d.cellBasis μ s₀)
  have hsurj : Function.Surjective f := f.surjective_of_ne_zero hf_ne
  obtain ⟨w₀, hw₀⟩ := hsurj x₀
  have hform : d.cellForm μ ≠ 0 := fun h0 ↦ hx₀ <| by
    rw [← hw₀, ← map_smul, d.basis_smul, h0, LinearMap.zero_apply, LinearMap.zero_apply,
      zero_smul, map_zero]
  have hcoatom : IsCoatom (LinearMap.ker f) := f.isCoatom_ker_of_surjective hsurj
  have hle : LinearMap.ker f ≤ d.cellRadical μ :=
    d.le_cellRadical_of_ne_top μ (LinearMap.ker f) hcoatom.1
  have hrad_ne : d.cellRadical μ ≠ ⊤ := mt (d.cellRadical_eq_top_iff μ).mp hform
  have hker_eq : LinearMap.ker f = d.cellRadical μ :=
    hle.eq_of_not_lt fun hlt ↦ hrad_ne (hcoatom.2 _ hlt)
  exact ⟨μ, hform, ⟨((d.cellRadical μ).quotEquivOfEq (LinearMap.ker f) hker_eq.symm).trans
    (f.quotKerEquivOfSurjective hsurj)⟩⟩

/-- **Graham–Lehrer Theorem 3.4 (classification of simple modules).** Over a field `K`, when `<` on
`Λ` is well-founded, every simple `B`-module is `B`-linearly equivalent to
`d.CellModule μ ⧸ d.cellRadical μ` for a unique cell `μ` with `d.cellForm μ ≠ 0`. -/
theorem existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv (S : Type*) [AddCommGroup S]
    [Module B S] [IsSimpleModule B S] :
    ∃! μ : Λ, d.cellForm μ ≠ 0 ∧ Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  obtain ⟨μ, hμ, ⟨e⟩⟩ := d.exists_cellForm_ne_zero_and_nonempty_linearEquiv S
  refine ⟨μ, ⟨hμ, ⟨e⟩⟩, fun ν ⟨hν, ⟨e'⟩⟩ ↦ ?_⟩
  exact (d.nonempty_cellModule_quotient_linearEquiv_iff hν).1 ⟨e'.trans e.symm⟩

/-- Over a field `K`, when `<` on `Λ` is well-founded, every simple left `B`-module is `B`-linearly
equivalent to `d.CellModule μ ⧸ d.cellRadical μ` for a unique cell `μ : Λ`. -/
theorem existsUnique_cellModule_quotient_linearEquiv (S : Type*) [AddCommGroup S]
    [Module B S] [IsSimpleModule B S] :
    ∃! μ : Λ, Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
  obtain ⟨μ, ⟨-, ⟨e⟩⟩, huniq⟩ := d.existsUnique_cellForm_ne_zero_and_nonempty_linearEquiv S
  exact ⟨μ, ⟨e⟩, fun ν hν ↦
    huniq ν ⟨d.cellForm_ne_zero_of_nonempty_cellModule_quotient_linearEquiv hν, hν⟩⟩

omit [∀ μ, DecidableEq (M μ)] in
/-- Every simple module over a cellular `K`-algebra (with well-founded cell order) is absolutely
simple: the structure map `K → Module.End B S` is bijective, without any algebraic-closure
assumption on `K`. -/
theorem algebraMap_end_bijective_of_isSimpleModule (d : CellularBasis K B M) (S : Type*)
    [AddCommGroup S] [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] :
    Function.Bijective (algebraMap K (Module.End B S)) := by
  classical
  obtain ⟨μ, hμ, ⟨e⟩⟩ := d.exists_cellForm_ne_zero_and_nonempty_linearEquiv S
  have hcomp : algebraMap K (Module.End B S) =
      (e.conjAlgEquiv K) ∘ algebraMap K (Module.End B (d.CellModule μ ⧸ d.cellRadical μ)) :=
    funext fun k ↦ by rw [Function.comp_apply, AlgEquiv.commutes]
  rw [hcomp]
  exact (e.conjAlgEquiv K).bijective.comp (d.algebraMap_end_cellModule_quotient_bijective hμ)

omit [∀ μ, DecidableEq (M μ)] in
/-- The canonical `K`-algebra equivalence `Module.End B S ≃ₐ[K] K` for any simple module `S` over a
cellular `K`-algebra with well-founded cell order. -/
noncomputable def endAlgEquivOfIsSimpleModule (d : CellularBasis K B M) (S : Type*)
    [AddCommGroup S] [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] :
    Module.End B S ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (Module.End B S))
    (d.algebraMap_end_bijective_of_isSimpleModule S)).symm

omit [∀ μ, DecidableEq (M μ)] in
/-- The inverse of `endAlgEquivOfIsSimpleModule` is `algebraMap`. -/
@[simp]
theorem endAlgEquivOfIsSimpleModule_symm_apply (d : CellularBasis K B M) {S : Type*}
    [AddCommGroup S] [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] (k : K) :
    (d.endAlgEquivOfIsSimpleModule S).symm k = algebraMap K (Module.End B S) k :=
  (rfl)

omit [∀ μ, DecidableEq (M μ)] in
/-- Every `B`-linear endomorphism of `S` acts as scalar multiplication by its image under
`endAlgEquivOfIsSimpleModule`. -/
@[simp]
theorem endAlgEquivOfIsSimpleModule_smul (d : CellularBasis K B M) {S : Type*} [AddCommGroup S]
    [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S]
    (f : Module.End B S) (s : S) :
    d.endAlgEquivOfIsSimpleModule S f • s = f s := by
  conv_rhs => rw [← (d.endAlgEquivOfIsSimpleModule S).symm_apply_apply f]
  rw [endAlgEquivOfIsSimpleModule_symm_apply, Module.algebraMap_end_apply]

omit [∀ μ, DecidableEq (M μ)] in
/-- Every simple module `S` over a cellular `K`-algebra (with well-founded cell order) satisfies
`Module.finrank K (Module.End B S) = 1`. -/
theorem finrank_end_eq_one_of_isSimpleModule (d : CellularBasis K B M) (S : Type*) [AddCommGroup S]
    [Module K S] [Module B S] [IsScalarTower K B S] [IsSimpleModule B S] :
    Module.finrank K (Module.End B S) = 1 := by
  rw [(d.endAlgEquivOfIsSimpleModule S).toLinearEquiv.finrank_eq, Module.finrank_self]

end WellFounded

end Field

end TauCeti.CellularBasis
