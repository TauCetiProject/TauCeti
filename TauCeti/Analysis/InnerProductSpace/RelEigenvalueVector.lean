/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues

/-!
# Eigenvalue vectors of a Hermitian form relative to a Hermitian form

Let `E` be a finite-dimensional complex vector space of dimension `n`, `h` a positive definite
Hermitian form on `E` and `a` a Hermitian form. A vector `μ ∈ ℝⁿ` is an *eigenvalue vector of `a`
relative to `h`* (`TauCeti.IsRelEigenvalueVector h a μ`) when there is a family `b_1, …, b_n`
with `h(b_i, b_j) = δ_ij` and `a(b_i, b_j) = μ_i·δ_ij`: an `h`-orthonormal basis diagonalizing
`a`. Such a family exists by simultaneous diagonalization, and the `μ` it gives are exactly the
reorderings of the relative eigenvalue vector `λ[a]` of `a` for the inner product `h`
(`LinearMap.IsSymm.relEigenvalues`). This is how the eigenvalues of `χ + i ∂∂bar φ` relative to
a Hermitian metric enter a complex Hessian equation, where only symmetric functions of `μ` occur.

The forms are plain functions `E → E → ℂ`, so that the Hermitian form of a real two-form which is
not of type (1,1) still has a meaning; the results take sesquilinear forms.

## Main definitions

* `TauCeti.IsRelEigenvalueVector h a μ`: `μ` is an eigenvalue vector of `a` relative to `h`.

## Main results

* `TauCeti.IsRelEigenvalueVector.comp_perm`: eigenvalue vectors are closed under reordering.
* `TauCeti.exists_isRelEigenvalueVector`: for `h` positive definite Hermitian and `a` Hermitian,
  there is a decreasingly sorted eigenvalue vector.
* `TauCeti.IsRelEigenvalueVector.eq_of_antitone`: it is unique.
* `TauCeti.IsRelEigenvalueVector.exists_perm_eq` and `TauCeti.isRelEigenvalueVector_iff`: any two
  eigenvalue vectors are reorderings of each other, and the eigenvalue vectors are exactly the
  reorderings of one of them.
* `TauCeti.isRelEigenvalueVector_self_iff`, `TauCeti.isRelEigenvalueVector_smul_self_iff`: `h`
  has the eigenvalue vector `e = (1, …, 1)` relative to itself, and `s·h` has `s·e`.

## Implementation notes

The proofs equip `E` with the inner product `h` (`InnerProductSpace.ofCore`) and apply the
spectral theory of `LinearMap.IsSymm.relEigenvalues`. The statements only involve the module
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

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- `μ` is an **eigenvalue vector of the form `a` relative to the form `h`**: there is a family
`b_1, …, b_n`, `n = dim_ℂ E`, with `h(b_i, b_j) = δ_ij` and `a(b_i, b_j) = μ_i·δ_ij`. For a positive
definite Hermitian `h` and a Hermitian `a`, such a family is an `h`-orthonormal basis diagonalizing
`a`, and `μ` is determined up to the order of its entries (`isRelEigenvalueVector_iff`). -/
def IsRelEigenvalueVector (h a : E → E → ℂ) (μ : Fin (finrank ℂ E) → ℝ) : Prop :=
  ∃ b : Fin (finrank ℂ E) → E, ∀ i j,
    h (b i) (b j) = (if i = j then 1 else 0) ∧ a (b i) (b j) = (if i = j then (μ i : ℂ) else 0)

/-- **Eigenvalue vectors are closed under reordering.** -/
theorem IsRelEigenvalueVector.comp_perm {h a : E → E → ℂ} {μ : Fin (finrank ℂ E) → ℝ}
    (hμ : IsRelEigenvalueVector h a μ) (σ : Equiv.Perm (Fin (finrank ℂ E))) :
    IsRelEigenvalueVector h a (μ ∘ σ) := by
  obtain ⟨b, hb⟩ := hμ
  exact ⟨b ∘ σ, fun i j ↦ by simpa [σ.injective.eq_iff] using hb (σ i) (σ j)⟩

variable {h a : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ}

/-- In infinite dimension `finrank ℂ E = 0`, so every eigenvalue vector is empty. -/
private theorem finiteDimensional_or_isEmpty :
    FiniteDimensional ℂ E ∨ IsEmpty (Fin (finrank ℂ E)) := by
  by_cases hE : FiniteDimensional ℂ E
  · exact Or.inl hE
  · right
    rw [Module.finrank_of_not_finite hE]
    infer_instance

/-- The inner product structure given by a positive definite Hermitian form. -/
@[instance_reducible]
private def innerCore (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < (h v v).re) :
    InnerProductSpace.Core ℂ E where
  inner u v := h u v
  conj_inner_symm u v := hh.eq v u
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hpos v hv).le
  add_left u u' v := by simp
  smul_left u v c := by simp
  definite v hv := by
    by_contra hne
    simpa [show h v v = 0 from hv] using hpos v hne

/-- **Simultaneous diagonalization.** For a positive definite Hermitian `h` and a Hermitian `a`,
there is an `h`-orthonormal basis diagonalizing `a` with decreasing diagonal entries. -/
theorem exists_isRelEigenvalueVector (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < (h v v).re)
    (ha : a.IsSymm) : ∃ μ, Antitone μ ∧ IsRelEigenvalueVector (h · ·) (a · ·) μ := by
  rcases finiteDimensional_or_isEmpty (E := E) with hE | hE
  · let : NormedAddCommGroup E := (innerCore hh hpos).toNormedAddCommGroup
    let : InnerProductSpace ℂ E := InnerProductSpace.ofCore (innerCore hh hpos).toCore
    refine ⟨ha.relEigenvalues rfl, ha.relEigenvalues_antitone rfl,
      ha.relEigenvectorBasis rfl, fun i j ↦ ⟨?_, ha.apply_relEigenvectorBasis rfl i j⟩⟩
    exact (ha.relEigenvectorBasis rfl).inner_eq_ite i j
  · exact ⟨isEmptyElim, fun i ↦ isEmptyElim i, isEmptyElim, fun i ↦ isEmptyElim i⟩

/-- A sesquilinear form which is diagonal in a basis, in the coordinates of that basis. -/
private theorem apply_eq_sum_of_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ} (bs : Module.Basis ι ℂ E) {w : ι → ℂ}
    (hB : ∀ i j, B (bs i) (bs j) = if i = j then w i else 0) (u v : E) :
    B u v = ∑ i, conj (bs.repr u i) * bs.repr v i * w i := by
  conv_lhs => rw [← bs.sum_repr u, ← bs.sum_repr v]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, RingHom.id_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- An eigenvalue vector forces `h` to be a positive definite Hermitian form and `a` to be
Hermitian: in the basis `b` of the definition, `h` is the standard inner product and `a` is real
diagonal. -/
private theorem IsRelEigenvalueVector.isSymm_pos [FiniteDimensional ℂ E]
    {μ : Fin (finrank ℂ E) → ℝ} (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) :
    h.IsSymm ∧ (∀ v, v ≠ 0 → 0 < (h v v).re) ∧ a.IsSymm := by
  obtain ⟨b, hb⟩ := hμ
  simp only at hb
  have hli : LinearIndependent ℂ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simpa [map_sum, (hb i _).1] using congrArg (h (b i)) hg
  let bs := Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge
  have hbs (i : Fin (finrank ℂ E)) : bs i = b i := Module.Basis.mk_apply _ _ i
  have hh := apply_eq_sum_of_diag (B := h) bs (w := 1) fun i j ↦ by simpa [hbs] using (hb i j).1
  have ha := apply_eq_sum_of_diag (B := a) bs (w := fun i ↦ (μ i : ℂ)) fun i j ↦ by
    simpa [hbs] using (hb i j).2
  refine ⟨⟨fun u v ↦ ?_⟩, fun v hv ↦ ?_, ⟨fun u v ↦ ?_⟩⟩
  · rw [hh, hh, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.one_apply, mul_one, map_mul, Complex.conj_conj]
    ring
  · have hc : bs.repr v ≠ 0 := by simpa using hv
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hc
    rw [hh]
    simp only [Pi.one_apply, mul_one, Complex.conj_mul', Complex.re_sum]
    refine Finset.sum_pos' (fun j _ ↦ by simp [← Complex.ofReal_pow]) ⟨i, Finset.mem_univ _, ?_⟩
    have hi' : 0 < ‖bs.repr v i‖ ^ 2 := pow_pos (norm_pos_iff.2 hi) 2
    simpa [← Complex.ofReal_pow] using hi'
  · rw [ha, ha, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring

/-- **Uniqueness of the sorted eigenvalue vector.** Two decreasingly sorted eigenvalue vectors of
`a` relative to `h` are equal. -/
theorem IsRelEigenvalueVector.eq_of_antitone {μ ν : Fin (finrank ℂ E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) (hμa : Antitone μ)
    (hν : IsRelEigenvalueVector (h · ·) (a · ·) ν) (hνa : Antitone ν) : μ = ν := by
  rcases finiteDimensional_or_isEmpty (E := E) with hE | hE
  swap
  · exact funext fun i ↦ isEmptyElim i
  obtain ⟨hh, hpos, ha⟩ := hμ.isSymm_pos
  let : NormedAddCommGroup E := (innerCore hh hpos).toNormedAddCommGroup
  let : InnerProductSpace ℂ E := InnerProductSpace.ofCore (innerCore hh hpos).toCore
  have key {μ : Fin (finrank ℂ E) → ℝ} (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ)
      (hμa : Antitone μ) : ha.relEigenvalues rfl = μ := by
    obtain ⟨b, hb⟩ := hμ
    have hon : Orthonormal ℂ b := orthonormal_iff_ite.2 fun i j ↦ (hb i j).1
    refine ha.relEigenvalues_eq_of_orthonormalBasis rfl
      (OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank'
        (Fintype.card_fin _)).ge) hμa fun i j ↦ ?_
    simpa using (hb i j).2
  exact (key hμ hμa).symm.trans (key hν hνa)

/-- **Eigenvalue vectors are unique up to reordering.** Any two eigenvalue vectors of `a`
relative to `h` are reorderings of each other. -/
theorem IsRelEigenvalueVector.exists_perm_eq {μ ν : Fin (finrank ℂ E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ)
    (hν : IsRelEigenvalueVector (h · ·) (a · ·) ν) :
    ∃ σ : Equiv.Perm (Fin (finrank ℂ E)), ν = μ ∘ σ := by
  have he := (hμ.comp_perm (Tuple.sortDesc μ)).eq_of_antitone (Tuple.antitone_sortDesc μ)
    (hν.comp_perm (Tuple.sortDesc ν)) (Tuple.antitone_sortDesc ν)
  refine ⟨Tuple.sortDesc μ * (Tuple.sortDesc ν)⁻¹, ?_⟩
  ext i
  simpa using (congrFun he ((Tuple.sortDesc ν)⁻¹ i)).symm

/-- **The eigenvalue vectors are the reorderings of one of them.** -/
theorem isRelEigenvalueVector_iff {μ ν : Fin (finrank ℂ E) → ℝ}
    (hμ : IsRelEigenvalueVector (h · ·) (a · ·) μ) :
    IsRelEigenvalueVector (h · ·) (a · ·) ν ↔ ∃ σ : Equiv.Perm (Fin (finrank ℂ E)), ν = μ ∘ σ := by
  refine ⟨hμ.exists_perm_eq, ?_⟩
  rintro ⟨σ, rfl⟩
  exact hμ.comp_perm σ

/-- **A form relative to itself.** A positive definite Hermitian form `h` has the eigenvalue vector
`e = (1, …, 1)` relative to itself, and no other. -/
theorem isRelEigenvalueVector_self_iff (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < (h v v).re)
    {μ : Fin (finrank ℂ E) → ℝ} : IsRelEigenvalueVector (h · ·) (h · ·) μ ↔ μ = 1 := by
  constructor
  · rintro ⟨b, hb⟩
    ext i
    have h₁ := (hb i i).1
    rw [(hb i i).2] at h₁
    simpa using h₁
  · rintro rfl
    obtain ⟨_, _, b, hb⟩ := exists_isRelEigenvalueVector hh hpos hh
    exact ⟨b, fun i j ↦ ⟨(hb i j).1, by simpa using (hb i j).1⟩⟩

/-- **A multiple of a form relative to the form.** For a positive definite Hermitian form `h` and
`s ∈ ℝ`, `s·h` has the eigenvalue vector `s·e` relative to `h`, and no other. -/
theorem isRelEigenvalueVector_smul_self_iff (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < (h v v).re)
    (s : ℝ) {μ : Fin (finrank ℂ E) → ℝ} :
    IsRelEigenvalueVector (h · ·) (fun u v ↦ (s : ℂ) * h u v) μ ↔ μ = fun _ ↦ s := by
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
    simp only at h₁ ⊢
    rw [h₁]
    split_ifs <;> simp

end TauCeti
