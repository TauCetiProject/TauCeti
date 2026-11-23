/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import TauCeti.LinearAlgebra.Dimension.CardEqFinrank

/-!
# Eigenvalue vectors of a Hermitian form relative to a Hermitian form

Let `E` be a finite-dimensional vector space of dimension `n` over `𝕜 = ℝ` or `ℂ`, `h` a positive
definite Hermitian form on `E` and `a` a Hermitian form. A vector `μ ∈ ℝⁿ` is an *eigenvalue
vector of `a` relative to `h`* (`TauCeti.IsRelEigenvalueVector h a μ`) when there is a family
`b_1, …, b_n` with `h(b_i, b_j) = δ_ij` and `a(b_i, b_j) = μ_i·δ_ij`: an `h`-orthonormal basis
diagonalizing `a`. Such a family exists by simultaneous diagonalization, and the `μ` it gives are
exactly the reorderings of the relative eigenvalue vector `λ[a]` of `a` for the inner product `h`
(`LinearMap.IsSymm.relEigenvalues`). This is how the eigenvalues of `χ + i ∂∂bar φ` relative to
a Hermitian metric enter a complex Hessian equation, where only symmetric functions of `μ` occur.

The forms are plain functions `E → E → 𝕜`, so that the Hermitian form of a real two-form which is
not of type (1,1) still has a meaning; the results take sesquilinear forms.

## Main definitions

* `TauCeti.IsRelEigenvalueVector h a μ`: `μ` is an eigenvalue vector of `a` relative to `h`.

## Main results

* `TauCeti.IsRelEigenvalueVector.comp_perm`: eigenvalue vectors are closed under reordering.
* `TauCeti.IsRelEigenvalueVector.add_smul_self`, `TauCeti.IsRelEigenvalueVector.smul_right` and
  `TauCeti.IsRelEigenvalueVector.smul_left`: the eigenvalue vectors of `a + t·h`, of `s·a`, and
  of `a` relative to `s·h`.
* `TauCeti.exists_isRelEigenvalueVector`: for `h` positive definite Hermitian and `a` Hermitian,
  there is a decreasingly sorted eigenvalue vector.
* `TauCeti.IsRelEigenvalueVector.eq_of_antitone`: it is unique.
* `TauCeti.IsRelEigenvalueVector.exists_perm_eq` and
  `TauCeti.IsRelEigenvalueVector.isRelEigenvalueVector_iff`: any two eigenvalue vectors are
  reorderings of each other, and the eigenvalue vectors are exactly the reorderings of one of them.
* `TauCeti.isRelEigenvalueVector_smul_self_iff`, `TauCeti.isRelEigenvalueVector_self_iff`: `s·h`
  has the eigenvalue vector `s·e`, `e = (1, …, 1)`, relative to `h`, and `h` has `e`.

## Implementation notes

The proofs equip `E` with the inner product `h` (`LinearMap.IsSymm.innerProductCore`) and apply
the spectral theory of `LinearMap.IsSymm.relEigenvalues`. The statements only involve the module
structure of `E`, so they apply to a normed space such as the model space of a complex manifold,
whose own norm plays no role.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), Section 2.
-/

public section

open Module (finrank)
open scoped ComplexConjugate

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- `μ` is an **eigenvalue vector of the form `a` relative to the form `h`**: there is a family
`b_1, …, b_n`, `n = dim E`, with `h(b_i, b_j) = δ_ij` and `a(b_i, b_j) = μ_i·δ_ij`. For a positive
definite Hermitian `h` and a Hermitian `a`, such a family is an `h`-orthonormal basis diagonalizing
`a`, and `μ` is determined up to the order of its entries
(`IsRelEigenvalueVector.isRelEigenvalueVector_iff`). -/
def IsRelEigenvalueVector (h a : E → E → 𝕜) (μ : Fin (finrank 𝕜 E) → ℝ) : Prop :=
  ∃ b : Fin (finrank 𝕜 E) → E, ∀ i j,
    h (b i) (b j) = (if i = j then 1 else 0) ∧ a (b i) (b j) = (if i = j then (μ i : 𝕜) else 0)

/-- Unfolding lemma for `IsRelEigenvalueVector`. -/
theorem isRelEigenvalueVector_def (h a : E → E → 𝕜) (μ : Fin (finrank 𝕜 E) → ℝ) :
    IsRelEigenvalueVector h a μ ↔ ∃ b : Fin (finrank 𝕜 E) → E, ∀ i j,
      h (b i) (b j) = (if i = j then 1 else 0) ∧ a (b i) (b j) = (if i = j then (μ i : 𝕜) else 0) :=
  Iff.rfl

/-- **Eigenvalue vectors are closed under reordering.** -/
theorem IsRelEigenvalueVector.comp_perm {h a : E → E → 𝕜} {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector h a μ) (σ : Equiv.Perm (Fin (finrank 𝕜 E))) :
    IsRelEigenvalueVector h a (μ ∘ σ) := by
  obtain ⟨b, hb⟩ := hμ
  exact ⟨b ∘ σ, fun i j ↦ by simpa [σ.injective.eq_iff] using hb (σ i) (σ j)⟩

/-- **Shifting by a multiple of `h` shifts the eigenvalues**: `a + t·h` has the eigenvalue vector
`μ + t·e` relative to `h`. -/
theorem IsRelEigenvalueVector.add_smul_self {h a : E → E → 𝕜} {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector h a μ) (t : ℝ) :
    IsRelEigenvalueVector h (fun u v ↦ a u v + (t : 𝕜) * h u v) (μ + fun _ ↦ t) := by
  obtain ⟨b, hb⟩ := hμ
  refine ⟨b, fun i j ↦ ⟨(hb i j).1, ?_⟩⟩
  beta_reduce
  rw [(hb i j).1, (hb i j).2]
  split_ifs <;> simp

/-- **Scaling the form scales the eigenvalues**: `s·a` has the eigenvalue vector `s·μ` relative
to `h`. -/
theorem IsRelEigenvalueVector.smul_right {h a : E → E → 𝕜} {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector h a μ) (s : ℝ) :
    IsRelEigenvalueVector h (fun u v ↦ (s : 𝕜) * a u v) (s • μ) := by
  obtain ⟨b, hb⟩ := hμ
  refine ⟨b, fun i j ↦ ⟨(hb i j).1, ?_⟩⟩
  beta_reduce
  rw [(hb i j).2]
  split_ifs <;> simp

variable {h a : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

/-- **Scaling the reference form scales the eigenvalues inversely**: for `s > 0`, `a` has the
eigenvalue vector `s⁻¹·μ` relative to `s·h`, through the family `s^{-1/2}·b`. -/
theorem IsRelEigenvalueVector.smul_left {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) {s : ℝ} (hs : 0 < s) :
    IsRelEigenvalueVector (fun u v ↦ (s : 𝕜) * h u v) (a · ·) (s⁻¹ • μ) := by
  obtain ⟨b, hb⟩ := hμ
  have hc : ((Real.sqrt s)⁻¹ : ℝ) * (Real.sqrt s)⁻¹ = s⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hs.le]
  refine ⟨fun i ↦ (((Real.sqrt s)⁻¹ : ℝ) : 𝕜) • b i, fun i j ↦ ⟨?_, ?_⟩⟩
  · have h₁ := (hb i j).1
    beta_reduce at h₁ ⊢
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      RCLike.conj_ofReal, h₁]
    rw [← mul_assoc, ← mul_assoc, ← RCLike.ofReal_mul, ← RCLike.ofReal_mul, mul_assoc s, hc,
      mul_inv_cancel₀ hs.ne', RCLike.ofReal_one, one_mul]
  · have h₂ := (hb i j).2
    beta_reduce at h₂ ⊢
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      RCLike.conj_ofReal, h₂]
    rw [← mul_assoc, ← RCLike.ofReal_mul, hc]
    split_ifs <;> simp

/-- **Simultaneous diagonalization.** For a positive definite Hermitian `h` and a Hermitian `a`,
there is an `h`-orthonormal basis diagonalizing `a` with decreasing diagonal entries. -/
theorem exists_isRelEigenvalueVector (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v))
    (ha : a.IsSymm) : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector (h · ·) (a · ·) μ := by
  by_cases hE : FiniteDimensional 𝕜 E
  · let : NormedAddCommGroup E := (hh.innerProductCore hpos).toNormedAddCommGroup
    let : InnerProductSpace 𝕜 E := InnerProductSpace.ofCore (hh.innerProductCore hpos).toCore
    refine ⟨ha.relEigenvalues rfl, ha.relEigenvalues_antitone rfl,
      ha.relEigenvectorBasis rfl, fun i j ↦ ⟨?_, ha.apply_relEigenvectorBasis rfl i j⟩⟩
    exact (hh.innerProductCore_inner hpos _ _).symm.trans
      ((ha.relEigenvectorBasis rfl).inner_eq_ite i j)
  · have : IsEmpty (Fin (finrank 𝕜 E)) :=
      Module.isEmpty_of_card_eq_finrank_of_not_finite (Fintype.card_fin _) hE
    exact ⟨isEmptyElim, fun i ↦ isEmptyElim i, isEmptyElim, fun i ↦ isEmptyElim i⟩

/-- A sesquilinear form which is real diagonal in a basis is Hermitian. -/
private theorem isSymm_of_diag {ι : Type*} [DecidableEq ι]
    {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} (bs : Module.Basis ι 𝕜 E) {w : ι → ℝ}
    (hB : ∀ i j, B (bs i) (bs j) = if i = j then (w i : 𝕜) else 0) : B.IsSymm := by
  refine (LinearMap.isSymm_iff_basis bs).2 fun i j ↦ ?_
  rw [hB, hB]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

open scoped ComplexOrder in
/-- An eigenvalue vector forces `h` to be a positive definite Hermitian form and `a` to be
Hermitian: in the basis `b` of the definition, the matrix of `h` is the identity and that of `a`
is real diagonal. -/
private theorem IsRelEigenvalueVector.isSymm_pos [FiniteDimensional 𝕜 E]
    {μ : Fin (finrank 𝕜 E) → ℝ} (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) :
    h.IsSymm ∧ (∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) ∧ a.IsSymm := by
  obtain ⟨b, hb⟩ := hμ
  simp only at hb
  have hli : LinearIndependent 𝕜 b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simpa [map_sum, (hb i _).1] using congrArg (h (b i)) hg
  let bs := Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge
  have hbs (i : Fin (finrank 𝕜 E)) : bs i = b i := Module.Basis.mk_apply _ _ i
  have hh (i j) : h (bs i) (bs j) = if i = j then ((1 : ℝ) : 𝕜) else 0 := by
    simpa [hbs] using (hb i j).1
  refine ⟨isSymm_of_diag bs hh, fun v hv ↦ ?_,
    isSymm_of_diag bs (w := μ) fun i j ↦ by simpa [hbs] using (hb i j).2⟩
  have h1 : LinearMap.toMatrix₂ bs bs h = 1 := by
    ext i j
    rw [LinearMap.toMatrix₂_apply, hh, Matrix.one_apply, RCLike.ofReal_one]
  rw [apply_eq_star_dotProduct_toMatrix₂_mulVec bs, h1]
  exact Matrix.PosDef.one.re_dotProduct_pos (by simpa using hv)

/-- **Uniqueness of the sorted eigenvalue vector.** Two decreasingly sorted eigenvalue vectors of
`a` relative to `h` are equal. -/
theorem IsRelEigenvalueVector.eq_of_antitone {μ ν : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) (hμa : Antitone μ)
    (hν : IsRelEigenvalueVector (h · ·) (a · ·) ν) (hνa : Antitone ν) : μ = ν := by
  by_cases hE : FiniteDimensional 𝕜 E
  swap
  · have : IsEmpty (Fin (finrank 𝕜 E)) :=
      Module.isEmpty_of_card_eq_finrank_of_not_finite (Fintype.card_fin _) hE
    exact funext fun i ↦ isEmptyElim i
  obtain ⟨hh, hpos, ha⟩ := hμ.isSymm_pos
  let : NormedAddCommGroup E := (hh.innerProductCore hpos).toNormedAddCommGroup
  let : InnerProductSpace 𝕜 E := InnerProductSpace.ofCore (hh.innerProductCore hpos).toCore
  have key {μ : Fin (finrank 𝕜 E) → ℝ} (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ)
      (hμa : Antitone μ) : ha.relEigenvalues rfl = μ := by
    obtain ⟨b, hb⟩ := hμ
    have hon : Orthonormal 𝕜 b := orthonormal_iff_ite.2 fun i j ↦
      (hh.innerProductCore_inner hpos _ _).trans (hb i j).1
    refine ha.relEigenvalues_eq_of_orthonormalBasis rfl
      (OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank'
        (Fintype.card_fin _)).ge) hμa fun i j ↦ ?_
    simpa using (hb i j).2
  exact (key hμ hμa).symm.trans (key hν hνa)

/-- **Eigenvalue vectors are unique up to reordering.** Any two eigenvalue vectors of `a`
relative to `h` are reorderings of each other. -/
theorem IsRelEigenvalueVector.exists_perm_eq {μ ν : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ)
    (hν : IsRelEigenvalueVector (h · ·) (a · ·) ν) :
    ∃ σ : Equiv.Perm (Fin (finrank 𝕜 E)), ν = μ ∘ σ := by
  have he := (hμ.comp_perm (Tuple.sortDesc μ)).eq_of_antitone (Tuple.antitone_sortDesc μ)
    (hν.comp_perm (Tuple.sortDesc ν)) (Tuple.antitone_sortDesc ν)
  refine ⟨Tuple.sortDesc μ * (Tuple.sortDesc ν)⁻¹, ?_⟩
  ext i
  simpa using (congrFun he ((Tuple.sortDesc ν)⁻¹ i)).symm

/-- **The eigenvalue vectors are the reorderings of one of them.** -/
theorem IsRelEigenvalueVector.isRelEigenvalueVector_iff {μ ν : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) :
    IsRelEigenvalueVector (h · ·) (a · ·) ν ↔ ∃ σ : Equiv.Perm (Fin (finrank 𝕜 E)), ν = μ ∘ σ := by
  refine ⟨hμ.exists_perm_eq, ?_⟩
  rintro ⟨σ, rfl⟩
  exact hμ.comp_perm σ

/-- **A multiple of a form relative to the form.** For a positive definite Hermitian form `h` and
`s ∈ ℝ`, `s·h` has the eigenvalue vector `s·e` relative to `h`, and no other. -/
theorem isRelEigenvalueVector_smul_self_iff (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (s : ℝ) {μ : Fin (finrank 𝕜 E) → ℝ} :
    IsRelEigenvalueVector (h · ·) (fun u v ↦ (s : 𝕜) * h u v) μ ↔ μ = fun _ ↦ s := by
  constructor
  · rintro ⟨b, hb⟩
    ext i
    obtain ⟨h₁, h₂⟩ := hb i i
    simp only [ite_true] at h₁ h₂
    rw [h₁, mul_one] at h₂
    exact_mod_cast h₂.symm
  · rintro rfl
    obtain ⟨_, _, b, hb⟩ := exists_isRelEigenvalueVector hh hpos hh
    refine ⟨b, fun i j ↦ ⟨(hb i j).1, ?_⟩⟩
    have h₁ := (hb i j).1
    beta_reduce at h₁ ⊢
    rw [h₁]
    split_ifs <;> simp

/-- **A form relative to itself.** A positive definite Hermitian form `h` has the eigenvalue vector
`e = (1, …, 1)` relative to itself, and no other. -/
theorem isRelEigenvalueVector_self_iff (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v))
    {μ : Fin (finrank 𝕜 E) → ℝ} : IsRelEigenvalueVector (h · ·) (h · ·) μ ↔ μ = 1 := by
  simpa [Pi.one_def] using isRelEigenvalueVector_smul_self_iff hh hpos 1 (μ := μ)

end TauCeti
