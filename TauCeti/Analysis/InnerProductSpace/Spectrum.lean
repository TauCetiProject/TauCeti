/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Spectral decompositions of self-adjoint operators

Mathlib's spectral theorem for a compact self-adjoint operator `T` on a Hilbert space `E` says
that the eigenspaces of `T` have trivial mutual orthogonal complement
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) and that the eigenspaces at
nonzero eigenvalues are finite dimensional
(`ContinuousLinearMap.finite_dimensional_eigenspace`).  This file turns the first statement into
the form the applications want: **`E` has an orthonormal basis consisting of eigenvectors of
`T`**.

The construction is the classical one.  Each eigenspace is closed, hence a Hilbert space in its
own right, so it has a Hilbert basis; the eigenspaces are mutually orthogonal, so the union of
those bases is an orthonormal family; and a vector orthogonal to the whole family is orthogonal
to every eigenspace, hence zero.  `HilbertBasis.mkOfOrthogonalEqBot` then assembles the family
into a Hilbert basis of `E`.

In finite dimensions, this file also packages Mathlib's ordered eigenbasis into spectral
subspaces spanned by any chosen set of eigenvector indices. In particular, the negative and
positive spectral subspaces are disjoint, invariant under the operator, and together span the
whole space when the operator is injective.

No separability is assumed anywhere: the basis is indexed by a set of vectors of `E`, exactly as
in Mathlib's `exists_hilbertBasis`, and the eigenvalue `0` may well carry an infinite-dimensional
eigenspace.  When `T` is injective that eigenspace is trivial and every basis vector has a
nonzero eigenvalue, which is the form the eigenvalue problem of an elliptic operator uses.

## Main declarations

* `ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces`:
  a symmetric operator whose eigenspaces have dense span admits a Hilbert basis of eigenvectors.
* `ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector`: the compact symmetric
  specialization of the preceding result.
* `ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero`: for an injective compact
  symmetric operator, every vector of that basis has a nonzero eigenvalue.
* `ContinuousLinearMap.hasSum_smul_repr_of_apply_eq_smul`: an operator diagonal in a Hilbert
  basis is the sum of its eigencomponents, the spectral expansion such a basis is for.
* `LinearMap.IsSymmetric.spectralSubspace`: the span of the eigenvectors whose indices lie in a
  specified set.
* `LinearMap.IsSymmetric.negativeSpectralSubspace` and
  `LinearMap.IsSymmetric.positiveSpectralSubspace`: the negative and positive halves of the
  finite-dimensional spectral splitting.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Theorem 6.11 (the Hilbert--Schmidt spectral decomposition); L. C. Evans, *Partial Differential
Equations*, Appendix D.6.
-/

public section

open Module.End
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

variable [CompleteSpace E] {T : E →L[𝕜] E}

/-- **A symmetric operator whose eigenspaces have dense span has an orthonormal basis of
eigenvectors.**  The basis is indexed by a set of vectors of `E`, as in `exists_hilbertBasis`,
and no separability is assumed. -/
theorem exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hspan : (⨆ mu, eigenspace (T : Module.End 𝕜 E) mu)ᗮ = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (nu : s → 𝕜), ⇑b = ((↑) : s → E) ∧
      ∀ x : s, HasEigenvector (T : Module.End 𝕜 E) (nu x) (x : E) := by
  classical
  have hbasis : ∀ mu : 𝕜, ∃ (w : Set (eigenspace (T : Module.End 𝕜 E) mu))
      (b : HilbertBasis w 𝕜 (eigenspace (T : Module.End 𝕜 E) mu)),
      ⇑b = ((↑) : w → eigenspace (T : Module.End 𝕜 E) mu) := by
    intro mu
    have : CompleteSpace (eigenspace (T : Module.End 𝕜 E) mu) :=
      (isClosed_eigenspace T mu).completeSpace_coe
    exact exists_hilbertBasis 𝕜 _
  choose w bw _ using hbasis
  set v : (Σ mu : 𝕜, w mu) → E := fun p =>
    (eigenspace (T : Module.End 𝕜 E) p.1).subtypeₗᵢ (bw p.1 p.2)
  have hv : Orthonormal 𝕜 v :=
    hT'.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun mu => (bw mu).orthonormal
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hmem : ∀ p, v p ∈ eigenspace (T : Module.End 𝕜 E) p.1 := fun p => (bw p.1 p.2).2
  have hvspan : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← hspan, ← Submodule.iInf_orthogonal]
    intro x hx
    have hx' : ∀ p, ⟪x, v p⟫_𝕜 = 0 := fun p =>
      (Submodule.mem_orthogonal' _ x).mp hx _ (Submodule.subset_span ⟨p, rfl⟩)
    simp only [Submodule.mem_iInf]
    intro mu
    rw [Submodule.mem_orthogonal']
    exact fun y hy =>
      (bw mu).inner_eq_zero_of_forall_inner_eq_zero (fun i => hx' ⟨mu, i⟩) hy
  have key : ∀ x : Set.range v, ∃ mu : 𝕜, HasEigenvector (T : Module.End 𝕜 E) mu (x : E) := by
    rintro ⟨-, p, rfl⟩
    refine ⟨p.1, hmem p, fun hzero => ?_⟩
    have hzero' : v p = 0 := hzero
    have hnorm : ‖v p‖ = 1 := hv.1 p
    rw [hzero', norm_zero] at hnorm
    exact zero_ne_one hnorm
  choose nu hnu using key
  exact ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot ((orthonormal_subtype_range hinj).2 hv)
    (by rwa [Subtype.range_coe]), nu, HilbertBasis.coe_mkOfOrthogonalEqBot _ _, hnu⟩

/-- **A compact self-adjoint operator has an orthonormal basis of eigenvectors.** -/
theorem exists_hilbertBasis_forall_hasEigenvector (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (nu : s → 𝕜), ⇑b = ((↑) : s → E) ∧
      ∀ x : s, HasEigenvector (T : Module.End 𝕜 E) (nu x) (x : E) :=
  exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces hT'
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT')

/-- **An injective symmetric operator whose eigenspaces have dense span has an orthonormal basis
of eigenvectors with nonzero eigenvalues.** -/
theorem exists_hilbertBasis_forall_hasEigenvector_ne_zero_of_dense_eigenspaces
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hspan : (⨆ mu, eigenspace (T : Module.End 𝕜 E) mu)ᗮ = ⊥)
    (hker : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (nu : s → 𝕜), ⇑b = ((↑) : s → E) ∧
      (∀ x : s, nu x ≠ 0) ∧ ∀ x : s, HasEigenvector (T : Module.End 𝕜 E) (nu x) (x : E) := by
  obtain ⟨s, b, nu, hb, hev⟩ :=
    exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces hT' hspan
  refine ⟨s, b, nu, hb, fun x hx => ?_, hev⟩
  have hx0 : (x : E) ∈ LinearMap.ker (T : E →ₗ[𝕜] E) := by
    rw [← eigenspace_zero, ← hx]
    exact (hev x).1
  rw [hker, Submodule.mem_bot] at hx0
  exact (hev x).2 hx0

/-- **An injective compact self-adjoint operator has an orthonormal basis of eigenvectors with
nonzero eigenvalues.**  Injectivity excludes the eigenvalue `0`. -/
theorem exists_hilbertBasis_forall_hasEigenvector_ne_zero (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hker : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (nu : s → 𝕜), ⇑b = ((↑) : s → E) ∧
      (∀ x : s, nu x ≠ 0) ∧ ∀ x : s, HasEigenvector (T : Module.End 𝕜 E) (nu x) (x : E) :=
  exists_hilbertBasis_forall_hasEigenvector_ne_zero_of_dense_eigenspaces
    hT' (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT') hker

omit [CompleteSpace E] in
/-- **The spectral expansion of an operator diagonal in a Hilbert basis.**  Applying `T` term by
term to the expansion of `y` writes `T y` as the sum of its eigencomponents; combined with
`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector` this diagonalizes a compact
self-adjoint operator. -/
theorem hasSum_smul_repr_of_apply_eq_smul (T : E →L[𝕜] E) {iota : Type*}
    (b : HilbertBasis iota 𝕜 E)
    (nu : iota → 𝕜) (hb : ∀ i, T (b i) = nu i • b i) (y : E) :
    HasSum (fun i => nu i • b.repr y i • b i) (T y) := by
  have key : ∀ i, T (b.repr y i • b i) = nu i • b.repr y i • b i := fun i => by
    rw [map_smul, hb, smul_comm]
  simpa only [key] using T.hasSum (b.hasSum_repr y)

end ContinuousLinearMap

namespace LinearMap.IsSymmetric

variable {n : ℕ} [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

/-! ### Finite-dimensional spectral subspaces -/

/-- The spectral subspace spanned by the eigenvectors whose indices belong to `s`.

The eigenvectors are those of Mathlib's decreasingly ordered eigenbasis. This definition is
particularly useful with subsets cut out by inequalities on the corresponding eigenvalues. -/
noncomputable def spectralSubspace (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (s : Set (Fin n)) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (hT.eigenvectorBasis hn '' s)

/-- A vector belongs to a spectral subspace exactly when its eigenbasis representation is
supported on the selected indices. -/
theorem mem_spectralSubspace_iff (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {s : Set (Fin n)} {v : E} :
    v ∈ hT.spectralSubspace hn s ↔
      ↑((hT.eigenvectorBasis hn).toBasis.repr v).support ⊆ s := by
  rw [spectralSubspace, ← OrthonormalBasis.coe_toBasis]
  exact Module.Basis.mem_span_image (b := (hT.eigenvectorBasis hn).toBasis)

/-- An eigenvector from the ordered eigenbasis belongs to a spectral subspace exactly when its
index is selected. -/
@[simp]
theorem eigenvectorBasis_mem_spectralSubspace_iff (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {s : Set (Fin n)} (i : Fin n) :
    hT.eigenvectorBasis hn i ∈ hT.spectralSubspace hn s ↔ i ∈ s := by
  rw [spectralSubspace, ← OrthonormalBasis.coe_toBasis]
  exact Module.Basis.self_mem_span_image (b := (hT.eigenvectorBasis hn).toBasis)

/-- Enlarging the set of eigenvector indices enlarges its spectral subspace. -/
theorem spectralSubspace_mono (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {s t : Set (Fin n)} (hst : s ⊆ t) :
    hT.spectralSubspace hn s ≤ hT.spectralSubspace hn t :=
  Submodule.span_mono (Set.image_mono hst)

/-- The spectral subspace of a union is the sum of the two spectral subspaces. -/
@[simp]
theorem spectralSubspace_union (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (s t : Set (Fin n)) :
    hT.spectralSubspace hn (s ∪ t) = hT.spectralSubspace hn s ⊔ hT.spectralSubspace hn t := by
  rw [spectralSubspace, spectralSubspace, spectralSubspace, Set.image_union,
    Submodule.span_union]

/-- The spectral subspace of the empty set is zero. -/
@[simp]
theorem spectralSubspace_empty (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    hT.spectralSubspace hn ∅ = ⊥ := by
  simp [spectralSubspace]

/-- All eigenvectors together span the whole finite-dimensional inner product space. -/
@[simp]
theorem spectralSubspace_univ (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    hT.spectralSubspace hn Set.univ = ⊤ := by
  rw [spectralSubspace, ← OrthonormalBasis.coe_toBasis, Set.image_univ]
  exact (hT.eigenvectorBasis hn).toBasis.span_eq

/-- Spectral subspaces indexed by disjoint sets are disjoint. -/
theorem disjoint_spectralSubspace (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {s t : Set (Fin n)} (hst : Disjoint s t) :
    Disjoint (hT.spectralSubspace hn s) (hT.spectralSubspace hn t) :=
  (hT.eigenvectorBasis hn).toBasis.linearIndependent.disjoint_span_image hst

/-- The dimension of a spectral subspace is the number of eigenvectors selected. -/
@[simp]
theorem finrank_spectralSubspace (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (s : Set (Fin n)) :
    Module.finrank 𝕜 (hT.spectralSubspace hn s) = s.ncard := by
  classical
  rw [spectralSubspace, ← OrthonormalBasis.coe_toBasis, finrank_span_set_eq_card
    ((hT.eigenvectorBasis hn).toBasis.linearIndependent.linearIndepOn _ |>.id_image)]
  calc
    ((hT.eigenvectorBasis hn).toBasis '' s).toFinset.card =
        ((hT.eigenvectorBasis hn).toBasis '' s).ncard :=
      (Set.ncard_eq_toFinset_card' _).symm
    _ = s.ncard :=
      Set.ncard_image_of_injective s (hT.eigenvectorBasis hn).toBasis.injective

/-- A symmetric operator preserves each of its spectral subspaces. -/
theorem map_spectralSubspace_le (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (s : Set (Fin n)) :
    Submodule.map T (hT.spectralSubspace hn s) ≤ hT.spectralSubspace hn s := by
  rw [spectralSubspace, Submodule.map_span_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [hT.apply_eigenvectorBasis hn i]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- The negative spectral subspace of a finite-dimensional symmetric operator. -/
noncomputable def negativeSpectralSubspace (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) : Submodule 𝕜 E :=
  hT.spectralSubspace hn {i | hT.eigenvalues hn i < 0}

/-- The positive spectral subspace of a finite-dimensional symmetric operator. -/
noncomputable def positiveSpectralSubspace (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) : Submodule 𝕜 E :=
  hT.spectralSubspace hn {i | 0 < hT.eigenvalues hn i}

/-- The negative spectral subspace is the spectral subspace of the negative eigenvalue
indices. -/
theorem negativeSpectralSubspace_def (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    hT.negativeSpectralSubspace hn = hT.spectralSubspace hn {i | hT.eigenvalues hn i < 0} := by
  rw [negativeSpectralSubspace]

/-- The positive spectral subspace is the spectral subspace of the positive eigenvalue
indices. -/
theorem positiveSpectralSubspace_def (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    hT.positiveSpectralSubspace hn = hT.spectralSubspace hn {i | 0 < hT.eigenvalues hn i} := by
  rw [positiveSpectralSubspace]

/-- A vector belongs to the negative spectral subspace exactly when its eigenbasis representation
is supported on the negative eigenvalues. -/
theorem mem_negativeSpectralSubspace_iff (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {v : E} :
    v ∈ hT.negativeSpectralSubspace hn ↔
      ∀ i ∈ ((hT.eigenvectorBasis hn).toBasis.repr v).support, hT.eigenvalues hn i < 0 := by
  rw [negativeSpectralSubspace_def, mem_spectralSubspace_iff]
  exact Iff.rfl

/-- A vector belongs to the positive spectral subspace exactly when its eigenbasis representation
is supported on the positive eigenvalues. -/
theorem mem_positiveSpectralSubspace_iff (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {v : E} :
    v ∈ hT.positiveSpectralSubspace hn ↔
      ∀ i ∈ ((hT.eigenvectorBasis hn).toBasis.repr v).support, 0 < hT.eigenvalues hn i := by
  rw [positiveSpectralSubspace_def, mem_spectralSubspace_iff]
  exact Iff.rfl

/-- The dimension of the negative spectral subspace counts the negative eigenvalues, with
multiplicity. -/
@[simp]
theorem finrank_negativeSpectralSubspace (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) :
    Module.finrank 𝕜 (hT.negativeSpectralSubspace hn) =
      {i | hT.eigenvalues hn i < 0}.ncard := by
  exact hT.finrank_spectralSubspace hn _

/-- The dimension of the positive spectral subspace counts the positive eigenvalues, with
multiplicity. -/
@[simp]
theorem finrank_positiveSpectralSubspace (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) :
    Module.finrank 𝕜 (hT.positiveSpectralSubspace hn) =
      {i | 0 < hT.eigenvalues hn i}.ncard := by
  exact hT.finrank_spectralSubspace hn _

/-- A symmetric operator preserves its negative spectral subspace. -/
theorem map_negativeSpectralSubspace_le (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) :
    Submodule.map T (hT.negativeSpectralSubspace hn) ≤ hT.negativeSpectralSubspace hn := by
  rw [negativeSpectralSubspace_def]
  exact hT.map_spectralSubspace_le hn _

/-- A symmetric operator preserves its positive spectral subspace. -/
theorem map_positiveSpectralSubspace_le (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) :
    Submodule.map T (hT.positiveSpectralSubspace hn) ≤ hT.positiveSpectralSubspace hn := by
  rw [positiveSpectralSubspace_def]
  exact hT.map_spectralSubspace_le hn _

/-- The negative and positive spectral subspaces are disjoint. -/
theorem disjoint_negativeSpectralSubspace_positiveSpectralSubspace
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Disjoint (hT.negativeSpectralSubspace hn) (hT.positiveSpectralSubspace hn) := by
  rw [negativeSpectralSubspace_def, positiveSpectralSubspace_def]
  exact hT.disjoint_spectralSubspace hn
    (Set.disjoint_left.2 fun i (hneg : hT.eigenvalues hn i < 0)
      (hpos : 0 < hT.eigenvalues hn i) ↦ (not_lt_of_ge hpos.le) hneg)

/-- An injective symmetric operator has no zero eigenvalue in its ordered eigenvalue family. -/
theorem eigenvalues_ne_zero_of_ker_eq_bot (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (hker : LinearMap.ker T = ⊥) (i : Fin n) :
    hT.eigenvalues hn i ≠ 0 := by
  intro hi
  have hev := hT.hasEigenvalue_eigenvalues hn i
  rw [hi, RCLike.ofReal_zero, Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero,
    hker] at hev
  exact hev rfl

/-- For an injective symmetric operator, its negative and positive spectral subspaces are
complementary: they are disjoint and together span the whole space. -/
theorem isCompl_negativeSpectralSubspace_positiveSpectralSubspace_of_ker_eq_bot
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (hker : LinearMap.ker T = ⊥) :
    IsCompl (hT.negativeSpectralSubspace hn) (hT.positiveSpectralSubspace hn) := by
  refine ⟨hT.disjoint_negativeSpectralSubspace_positiveSpectralSubspace hn, codisjoint_iff.2 ?_⟩
  rw [negativeSpectralSubspace_def, positiveSpectralSubspace_def, ← hT.spectralSubspace_union hn]
  have hindices : {i | hT.eigenvalues hn i < 0} ∪
      {i | 0 < hT.eigenvalues hn i} = Set.univ := by
    ext i
    simp only [Set.mem_union, Set.mem_ofPred, Set.mem_univ, iff_true]
    exact lt_or_gt_of_ne (hT.eigenvalues_ne_zero_of_ker_eq_bot hn hker i)
  rw [hindices, hT.spectralSubspace_univ hn]

end LinearMap.IsSymmetric
