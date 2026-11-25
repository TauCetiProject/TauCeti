/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Basic
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
* `TauCeti.IsRelEigenvalueVector.isSymm_left`, `TauCeti.IsRelEigenvalueVector.re_apply_self_pos`
  and `TauCeti.IsRelEigenvalueVector.isSymm_right`: conversely, in finite dimension, an eigenvalue
  vector forces `h` to be positive definite Hermitian and `a` to be Hermitian.
* `TauCeti.IsRelEigenvalueVector.exists_perm_eq` and
  `TauCeti.IsRelEigenvalueVector.isRelEigenvalueVector_iff_exists_perm`: any two eigenvalue vectors
  are reorderings of each other, and the eigenvalue vectors are exactly the reorderings of one of
  them.
* `TauCeti.isRelEigenvalueVector_smul_iff`: for any `h`, the eigenvalue vectors of `s·h` relative
  to `h` are `s·e`, where `e = (1, …, 1)` is one for `h` relative to itself.
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
definite Hermitian `h` and a Hermitian `a` on a finite-dimensional `E`, such a family is an
`h`-orthonormal basis diagonalizing `a`, and `μ` is determined up to the order of its entries
(`IsRelEigenvalueVector.isRelEigenvalueVector_iff_exists_perm`). When `E` is
infinite-dimensional, `finrank 𝕜 E = 0`, so the family and `μ` are empty and the condition holds
trivially. -/
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
  -- the family `c • b`, `c = s^{-1/2}`, with `c² = s⁻¹`
  have hc : (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ = s⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hs.le]
  refine ⟨fun i ↦ (((Real.sqrt s)⁻¹ : ℝ) : 𝕜) • b i, fun i j ↦ ⟨?_, ?_⟩⟩
  · split_ifs with hij
    · subst hij
      have hc' : (s : 𝕜) * (((Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ : ℝ) : 𝕜) = 1 := by
        rw [hc, RCLike.ofReal_inv, mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 hs.ne')]
      simpa [(hb i i).1, mul_assoc] using hc'
    · simp [(hb i j).1, hij]
  · split_ifs with hij
    · subst hij
      simp [(hb i i).2, ← mul_assoc, ← hc]
    · simp [(hb i j).2, hij]

/-- **Simultaneous diagonalization.** For a positive definite Hermitian `h` and a Hermitian `a`,
there is, in finite dimension, an `h`-orthonormal basis diagonalizing `a` with decreasing diagonal
entries. When `E` is infinite-dimensional, `finrank 𝕜 E = 0` and the statement is vacuous: the
family and `μ` are empty. -/
theorem exists_isRelEigenvalueVector (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v))
    (ha : a.IsSymm) : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector (h · ·) (a · ·) μ := by
  by_cases hE : FiniteDimensional 𝕜 E
  · let : NormedAddCommGroup E := (hh.innerProductCore hpos).toNormedAddCommGroup
    let : InnerProductSpace 𝕜 E := InnerProductSpace.ofCore (hh.innerProductCore hpos).toCore
    refine ⟨ha.relEigenvalues rfl, ha.relEigenvalues_antitone rfl,
      ha.relEigenvectorBasis rfl, fun i j ↦ ⟨?_, ha.apply_relEigenvectorBasis rfl i j⟩⟩
    exact (hh.inner_ofCore_innerProductCore hpos _ _).symm.trans
      ((ha.relEigenvectorBasis rfl).inner_eq_ite i j)
  · have : IsEmpty (Fin (finrank 𝕜 E)) :=
      Module.isEmpty_of_card_eq_finrank_of_not_finite (Fintype.card_fin _) hE
    exact ⟨isEmptyElim, fun i ↦ isEmptyElim i, isEmptyElim, fun i ↦ isEmptyElim i⟩

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
  let bs := basisOfLinearIndependentOfCardEqFinrank' b hli (Fintype.card_fin _)
  have hh (i j) : h (bs i) (bs j) = if i = j then ((1 : ℝ) : 𝕜) else 0 := by
    simpa [bs] using (hb i j).1
  refine ⟨LinearMap.isSymm_of_basis_diag bs hh, fun v hv ↦ ?_,
    LinearMap.isSymm_of_basis_diag bs (w := μ) fun i j ↦ by simpa [bs] using (hb i j).2⟩
  have h1 : LinearMap.toMatrix₂ bs bs h = 1 := by
    ext i j
    rw [LinearMap.toMatrix₂_apply, hh, Matrix.one_apply, RCLike.ofReal_one]
  rw [apply_eq_star_dotProduct_toMatrix₂_mulVec bs, h1]
  exact Matrix.PosDef.one.re_dotProduct_pos (by simpa using hv)

/-- **An eigenvalue vector forces a Hermitian reference form.** -/
theorem IsRelEigenvalueVector.isSymm_left [FiniteDimensional 𝕜 E] {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) : h.IsSymm :=
  hμ.isSymm_pos.1

/-- **An eigenvalue vector forces a positive definite reference form.** -/
theorem IsRelEigenvalueVector.re_apply_self_pos [FiniteDimensional 𝕜 E]
    {μ : Fin (finrank 𝕜 E) → ℝ} (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) {v : E}
    (hv : v ≠ 0) : 0 < RCLike.re (h v v) :=
  hμ.isSymm_pos.2.1 v hv

/-- **An eigenvalue vector forces a Hermitian form.** -/
theorem IsRelEigenvalueVector.isSymm_right [FiniteDimensional 𝕜 E] {μ : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) : a.IsSymm :=
  hμ.isSymm_pos.2.2

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
      (hh.inner_ofCore_innerProductCore hpos _ _).trans (hb i j).1
    refine ha.relEigenvalues_eq_of_orthonormalBasis rfl
      ((basisOfLinearIndependentOfCardEqFinrank' b hon.linearIndependent
        (Fintype.card_fin _)).toOrthonormalBasis (by simpa using hon)) hμa fun i j ↦ ?_
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
theorem IsRelEigenvalueVector.isRelEigenvalueVector_iff_exists_perm {μ ν : Fin (finrank 𝕜 E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) :
    IsRelEigenvalueVector (h · ·) (a · ·) ν ↔ ∃ σ : Equiv.Perm (Fin (finrank 𝕜 E)), ν = μ ∘ σ := by
  refine ⟨hμ.exists_perm_eq, ?_⟩
  rintro ⟨σ, rfl⟩
  exact hμ.comp_perm σ

/-- **A multiple of a form relative to the form, unbundled.** For any `h`, `s·h` has the eigenvalue
vector `μ` relative to `h` exactly when `h` has the eigenvalue vector `e = (1, …, 1)` relative to
itself and `μ = s·e`. -/
theorem isRelEigenvalueVector_smul_iff {h : E → E → 𝕜} (s : ℝ) {μ : Fin (finrank 𝕜 E) → ℝ} :
    IsRelEigenvalueVector h (fun u v ↦ (s : 𝕜) * h u v) μ ↔
      IsRelEigenvalueVector h h 1 ∧ μ = fun _ ↦ s := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, fun i j ↦ ⟨(hb i j).1, by simpa using (hb i j).1⟩⟩, funext fun i ↦ ?_⟩
    obtain ⟨h₁, h₂⟩ := hb i i
    simp only [ite_true] at h₁ h₂
    rw [h₁, mul_one] at h₂
    exact_mod_cast h₂.symm
  · rintro ⟨⟨b, hb⟩, rfl⟩
    refine ⟨b, fun i j ↦ ⟨(hb i j).1, ?_⟩⟩
    beta_reduce
    rw [(hb i j).1]
    split_ifs <;> simp

/-- **A multiple of a form relative to the form.** For a positive definite Hermitian form `h` and
`s ∈ ℝ`, `s·h` has the eigenvalue vector `s·e` relative to `h`, and no other. -/
theorem isRelEigenvalueVector_smul_self_iff (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (s : ℝ) {μ : Fin (finrank 𝕜 E) → ℝ} :
    IsRelEigenvalueVector (h · ·) (fun u v ↦ (s : 𝕜) * h u v) μ ↔ μ = fun _ ↦ s := by
  rw [isRelEigenvalueVector_smul_iff]
  refine and_iff_right ?_
  obtain ⟨_, _, b, hb⟩ := exists_isRelEigenvalueVector hh hpos hh
  exact ⟨b, fun i j ↦ ⟨(hb i j).1, by simpa using (hb i j).1⟩⟩

/-- **A form relative to itself.** A positive definite Hermitian form `h` has the eigenvalue vector
`e = (1, …, 1)` relative to itself, and no other. -/
theorem isRelEigenvalueVector_self_iff (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v))
    {μ : Fin (finrank 𝕜 E) → ℝ} : IsRelEigenvalueVector (h · ·) (h · ·) μ ↔ μ = 1 := by
  simpa [Pi.one_def] using isRelEigenvalueVector_smul_self_iff hh hpos 1 (μ := μ)

end TauCeti
