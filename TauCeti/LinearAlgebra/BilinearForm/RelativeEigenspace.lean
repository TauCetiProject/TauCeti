/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Relative eigenspaces of a pair of bilinear forms

Let `g` and `q` be bilinear forms on a module `V`. A vector `v` is an eigenvector of `q` relative
to `g`, with eigenvalue `μ`, when `q v w = μ * g v w` for every `w`. When `g` is an inner product
this is the eigenvalue problem of the operator representing `q`, but the relative notion needs no
inner product structure on `V`: the eigenspace `g.relativeEigenspace q μ` is the kernel of
`q - μ • g`, and the spectral subspace `g.relativeSpectralSubspace q Ω` is the sum of the
eigenspaces at the eigenvalues in `Ω`.

Over a field, symmetric `g` and `q` make relative eigenspaces for distinct eigenvalues orthogonal
for both forms, so spectral subspaces selected by disjoint sets are orthogonal for both
(`LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace`), and when `g` is positive
definite they meet only in `0`. The spectral theory over finite-dimensional real spaces is in
`TauCeti.Analysis.InnerProductSpace.Spectral.Relative`.

## Main declarations

* `LinearMap.BilinForm.relativeEigenspace`: the eigenspace of `q` relative to `g` at `μ`.
* `LinearMap.BilinForm.relativeSpectralSubspace`: the sum of the relative eigenspaces at the
  eigenvalues in `Ω`.
* `LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂`: naturality under linear
  equivalences.
* `LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace`: spectral subspaces for
  disjoint sets are orthogonal for `g` and for `q`;
  `LinearMap.BilinForm.disjoint_relativeSpectralSubspace`: for anisotropic `g` they meet only
  in `0`, in particular for positive definite `g`
  (`LinearMap.BilinForm.disjoint_relativeSpectralSubspace_of_pos`).
-/

public section

open Set

namespace LinearMap.BilinForm

section CommRing

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {g q : LinearMap.BilinForm R V} {μ : R} {Ω Ω' : Set R}

/-- The eigenspace of `q` relative to `g` at `μ`: the vectors `v` with `q v = μ • g v`, that is,
the kernel of `q - μ • g`. -/
def relativeEigenspace (g q : LinearMap.BilinForm R V) (μ : R) : Submodule R V :=
  LinearMap.ker (q - μ • g)

/-- A vector is a relative eigenvector at `μ` exactly when `q v w = μ * g v w` for every `w`. -/
theorem mem_relativeEigenspace_iff {v : V} :
    v ∈ g.relativeEigenspace q μ ↔ ∀ w, q v w = μ * g v w := by
  simp [relativeEigenspace, LinearMap.ext_iff, sub_eq_zero]

/-- The relative spectral subspace of `q` relative to `g` selected by `Ω`: the sum of the
eigenspaces of `q` relative to `g` at the eigenvalues in `Ω`. -/
def relativeSpectralSubspace (g q : LinearMap.BilinForm R V) (Ω : Set R) : Submodule R V :=
  ⨆ μ ∈ Ω, g.relativeEigenspace q μ

/-- The relative spectral subspace selected by `Ω` is the supremum of the relative eigenspaces at
the eigenvalues in `Ω`. -/
theorem relativeSpectralSubspace_def :
    g.relativeSpectralSubspace q Ω = ⨆ μ ∈ Ω, g.relativeEigenspace q μ :=
  (rfl)

/-- The relative eigenspace at an eigenvalue in `Ω` lies in the spectral subspace selected by
`Ω`. -/
theorem relativeEigenspace_le_relativeSpectralSubspace (hμ : μ ∈ Ω) :
    g.relativeEigenspace q μ ≤ g.relativeSpectralSubspace q Ω :=
  le_biSup (fun μ ↦ g.relativeEigenspace q μ) hμ

/-- The spectral subspace selected by `Ω` lies in `U` exactly when every relative eigenspace at an
eigenvalue in `Ω` does. -/
theorem relativeSpectralSubspace_le_iff {U : Submodule R V} :
    g.relativeSpectralSubspace q Ω ≤ U ↔ ∀ μ ∈ Ω, g.relativeEigenspace q μ ≤ U :=
  iSup₂_le_iff

/-- Relative spectral subspaces are monotone in the selected set. -/
theorem relativeSpectralSubspace_mono (h : Ω ⊆ Ω') :
    g.relativeSpectralSubspace q Ω ≤ g.relativeSpectralSubspace q Ω' :=
  relativeSpectralSubspace_le_iff.mpr fun _ hμ ↦ relativeEigenspace_le_relativeSpectralSubspace
    (h hμ)

@[simp]
theorem relativeSpectralSubspace_empty : g.relativeSpectralSubspace q ∅ = ⊥ := by
  simp [relativeSpectralSubspace]

theorem relativeSpectralSubspace_union :
    g.relativeSpectralSubspace q (Ω ∪ Ω') =
      g.relativeSpectralSubspace q Ω ⊔ g.relativeSpectralSubspace q Ω' :=
  iSup_union

@[simp]
theorem relativeSpectralSubspace_singleton :
    g.relativeSpectralSubspace q {μ} = g.relativeEigenspace q μ := by
  simp [relativeSpectralSubspace]

/-- The relative eigenspace at `0` is the kernel of `q`. -/
@[simp]
theorem relativeEigenspace_zero : g.relativeEigenspace q 0 = LinearMap.ker q := by
  ext v
  simp [mem_relativeEigenspace_iff, LinearMap.ext_iff]

/-- The eigenspace of `-q` at `μ` is the eigenspace of `q` at `-μ`. -/
@[simp]
theorem relativeEigenspace_neg : g.relativeEigenspace (-q) μ = g.relativeEigenspace q (-μ) := by
  ext v
  simp only [mem_relativeEigenspace_iff, LinearMap.neg_apply, neg_mul, neg_eq_iff_eq_neg]

/-- The spectral subspace of `-q` selected by `Ω` is the spectral subspace of `q` selected by
`-Ω`. -/
@[simp]
theorem relativeSpectralSubspace_neg :
    g.relativeSpectralSubspace (-q) Ω = g.relativeSpectralSubspace q (-Ω) := by
  refine le_antisymm (relativeSpectralSubspace_le_iff.mpr fun μ hμ ↦ ?_)
    (relativeSpectralSubspace_le_iff.mpr fun μ hμ ↦ ?_)
  · rw [relativeEigenspace_neg]
    exact relativeEigenspace_le_relativeSpectralSubspace (neg_mem_neg.mpr hμ)
  · simpa only [relativeEigenspace_neg, neg_neg] using
      relativeEigenspace_le_relativeSpectralSubspace (g := g) (q := -q) (mem_neg.mp hμ)

/-- Pulling both forms back along a linear equivalence `e` pulls the relative eigenspaces back
along `e`. -/
theorem relativeEigenspace_compl₁₂ (e : W ≃ₗ[R] V) :
    relativeEigenspace (g.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V))
        (q.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V)) μ =
      (g.relativeEigenspace q μ).comap (e : W →ₗ[R] V) := by
  ext v
  simp only [mem_relativeEigenspace_iff, compl₁₂_apply, LinearEquiv.coe_coe, Submodule.mem_comap]
  exact ⟨fun h w ↦ by simpa using h (e.symm w), fun h w ↦ h (e w)⟩

/-- **Naturality of relative spectral subspaces.** Pulling both forms back along a linear
equivalence `e` and mapping the resulting spectral subspace forward along `e` recovers the
original spectral subspace. -/
theorem map_relativeSpectralSubspace_compl₁₂ (e : W ≃ₗ[R] V) :
    (relativeSpectralSubspace (g.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V))
      (q.compl₁₂ (e : W →ₗ[R] V) (e : W →ₗ[R] V)) Ω).map (e : W →ₗ[R] V) =
      g.relativeSpectralSubspace q Ω := by
  simp only [relativeSpectralSubspace, Submodule.map_iSup, relativeEigenspace_compl₁₂,
    Submodule.map_comap_eq_of_surjective e.surjective]

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {g q : LinearMap.BilinForm K V}
  {Ω Ω' : Set K} {v w : V}

/-- Relative eigenvectors at distinct eigenvalues of symmetric forms are orthogonal for both
forms. -/
theorem apply_eq_zero_of_mem_relativeEigenspace (hg : g.IsSymm) (hq : q.IsSymm)
    {μ ν : K} (hμν : μ ≠ ν) (hv : v ∈ g.relativeEigenspace q μ)
    (hw : w ∈ g.relativeEigenspace q ν) : g v w = 0 ∧ q v w = 0 := by
  rw [mem_relativeEigenspace_iff] at hv hw
  have hgvw : g v w = 0 := by
    have h := (hv w).symm.trans ((hq.eq v w).trans ((hw v).trans (by rw [hg.eq w v])))
    rw [← sub_eq_zero, ← sub_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμν)
  exact ⟨hgvw, by rw [hv w, hgvw, mul_zero]⟩

/-- **Orthogonality of relative spectral subspaces.** For symmetric `g` and `q`, the relative
spectral subspaces selected by disjoint sets are orthogonal for `g` and for `q`. -/
theorem apply_eq_zero_of_mem_relativeSpectralSubspace (hg : g.IsSymm) (hq : q.IsSymm)
    (h : Disjoint Ω Ω') (hv : v ∈ g.relativeSpectralSubspace q Ω)
    (hw : w ∈ g.relativeSpectralSubspace q Ω') : g v w = 0 ∧ q v w = 0 := by
  -- First fix a relative eigenvector `v₀` at `μ ∈ Ω` and vary `w`, then vary `v`.
  have hleft {μ : K} (hμ : μ ∈ Ω) {v₀ : V} (hv₀ : v₀ ∈ g.relativeEigenspace q μ) :
      g.relativeSpectralSubspace q Ω' ≤ LinearMap.ker (g v₀) ⊓ LinearMap.ker (q v₀) :=
    relativeSpectralSubspace_le_iff.mpr fun ν hν w₀ hw₀ ↦
      apply_eq_zero_of_mem_relativeEigenspace hg hq (fun hμν ↦ disjoint_left.mp h hμ (by rwa [hμν]))
        hv₀ hw₀
  have hright : g.relativeSpectralSubspace q Ω ≤
      LinearMap.ker (g.flip w) ⊓ LinearMap.ker (q.flip w) :=
    relativeSpectralSubspace_le_iff.mpr fun μ hμ v₀ hv₀ ↦ hleft hμ hv₀ hw
  exact hright hv

/-- For an anisotropic symmetric `g` (for instance a positive definite one) and a symmetric `q`,
the relative spectral subspaces selected by disjoint sets meet only in `0`. -/
theorem disjoint_relativeSpectralSubspace (hg : g.IsSymm) (hg0 : ∀ v, g v v = 0 → v = 0)
    (hq : q.IsSymm) (h : Disjoint Ω Ω') :
    Disjoint (g.relativeSpectralSubspace q Ω) (g.relativeSpectralSubspace q Ω') :=
  Submodule.disjoint_def.mpr fun v hv hv' ↦
    hg0 v (apply_eq_zero_of_mem_relativeSpectralSubspace hg hq h hv hv').1

/-- For a positive definite symmetric `g` and a symmetric `q`, the relative spectral subspaces
selected by disjoint sets meet only in `0`. -/
theorem disjoint_relativeSpectralSubspace_of_pos [Preorder K] (hg : g.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) (hq : q.IsSymm) (h : Disjoint Ω Ω') :
    Disjoint (g.relativeSpectralSubspace q Ω) (g.relativeSpectralSubspace q Ω') :=
  disjoint_relativeSpectralSubspace hg (fun v h ↦ by_contra fun hv ↦ (hpos v hv).ne' h) hq h

end Field

end LinearMap.BilinForm
