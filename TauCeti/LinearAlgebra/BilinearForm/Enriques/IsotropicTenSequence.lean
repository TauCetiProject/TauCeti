/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Isotropic 10-sequences and the Reye lattice

Let `M` be a `ℤ`-module with a bilinear form `B`, written `x · y`. An *isotropic 10-sequence*
(`LinearMap.BilinForm.IsotropicTenSequence`) consists of ten vectors `f₁, …, f₁₀` with
`fᵢ · fⱼ = 1 - δᵢⱼ` and a vector `δ` with `3δ = f₁ + ⋯ + f₁₀`. Such sequences are the
coordinates in which the numerical lattice `U ⊕ E₈(-1)` of an Enriques surface is studied: there
`δ` is integral, `δ · δ = 10` and `δ · fᵢ = 3`, and `f₁, …, f₉, δ` is an integral basis.

From such a sequence this file builds the ten roots

`β₀ = δ - f₁ - f₂ - f₃ - f₄`, `βᵢ = fᵢ - fᵢ₊₁` (`1 ≤ i ≤ 9`)

(`LinearMap.BilinForm.IsotropicTenSequence.reyeRoot`) and the vector `r = δ - 2 f₁₀`
(`LinearMap.BilinForm.IsotropicTenSequence.extraRoot`), and proves:

* every `βᵢ` and `r` has square `-2`, and `βᵢ · βⱼ = 1` exactly on the nine edges of the T246
  diagram (the chain `1 - 2 - ⋯ - 9` and the edge `0 - 4`) and `0` off them
  (`apply_reyeRoot_reyeRoot`);
* `r · βᵢ = 0` for `i < 9` and `r · β₉ = -2` (`apply_extraRoot_reyeRoot`);
* the `βᵢ` are linearly independent, so they form a basis of their span, the *Reye lattice* `R`
  (`reyeBasis`);
* `f₁, …, f₉, δ` is a basis of the lattice they span together with `f₁₀ = 3δ - (f₁ + ⋯ + f₉)`
  (`latticeBasis`), and conversely nine vectors and a vector `δ` with the same pairings extend
  to an isotropic 10-sequence (`ofGram`);
* `R` is the set of vectors of that lattice whose pairing with `r` is even
  (`mem_reyeLattice_iff`), so it has index two in it (`relIndex_reyeLattice_lattice`).

No symmetry or nondegeneracy of `B` is assumed: every pairing is computed from the defining
pairings of the `fᵢ` by bilinearity. The concrete sequence `standard` on `ℤ¹⁰`, whose Gram matrix
in the basis `f₁, …, f₉, δ` is `standardGram`, shows that the hypotheses are consistent; it
generates `ℤ¹⁰` (`lattice_standard`).

In Lean the sequence is indexed by `Fin 10`, so `s.f i` is `fᵢ₊₁`, while `s.reyeRoot i` is `βᵢ`.

## Main definitions

* `LinearMap.BilinForm.IsotropicTenSequence`: an isotropic 10-sequence together with `δ`.
* `LinearMap.BilinForm.IsotropicTenSequence.reyeRoot`: the roots `β₀, …, β₉`.
* `LinearMap.BilinForm.IsotropicTenSequence.extraRoot`: the root `r = δ - 2 f₁₀`.
* `LinearMap.BilinForm.IsotropicTenSequence.lattice`: the span of `f₁, …, f₁₀` and `δ`.
* `LinearMap.BilinForm.IsotropicTenSequence.reyeLattice`: the span `R` of `β₀, …, β₉`.
* `LinearMap.BilinForm.IsotropicTenSequence.reyeBasis`, `latticeBasis`: the bases `β` of `R` and
  `f₁, …, f₉, δ` of the lattice.

## Main results

* `apply_reyeRoot_reyeRoot`: the intersection matrix of the `βᵢ`.
* `apply_extraRoot_reyeRoot`, `apply_extraRoot_extraRoot`: the pairings of `r`.
* `mem_reyeLattice_iff`: `R = {x ∈ lattice | x · r is even}`.
* `relIndex_reyeLattice_lattice`, `index_reyeLattice`: `R` has index two.

## References

* C. Peters, H. Sterk, *On K3 double planes covering Enriques surfaces*, Math. Ann. 376 (2020),
  1599–1628, Appendix A.2, Lemma A.5.
* F. Cossec, I. Dolgachev, *On automorphisms of nodal Enriques surfaces*, Bull. Amer. Math. Soc.
  12 (1985), 247–249.
-/

public section

open Module Submodule

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M]

/-- An isotropic 10-sequence for a `ℤ`-valued bilinear form `B`: ten vectors `f₁, …, f₁₀` with
`fᵢ · fⱼ = 1 - δᵢⱼ`, together with a vector `δ` such that `3δ = f₁ + ⋯ + f₁₀`. The vectors are
indexed by `Fin 10`, so `f i` is `fᵢ₊₁`. -/
structure IsotropicTenSequence (B : LinearMap.BilinForm ℤ M) where
  /-- The ten isotropic vectors, `f i` being `fᵢ₊₁`. -/
  f : Fin 10 → M
  /-- The vector `δ` with `3δ = f₁ + ⋯ + f₁₀`. -/
  δ : M
  /-- The defining pairings `fᵢ · fⱼ = 1 - δᵢⱼ`. -/
  apply_f_f (i j : Fin 10) : B (f i) (f j) = if i = j then 0 else 1
  /-- `3δ = f₁ + ⋯ + f₁₀`. -/
  three_smul_δ : (3 : ℤ) • δ = ∑ i, f i

namespace IsotropicTenSequence

variable {B : LinearMap.BilinForm ℤ M} (s : IsotropicTenSequence B)

/-! ### Pairings of `f` and `δ` -/

@[simp]
theorem apply_f_self (i : Fin 10) : B (s.f i) (s.f i) = 0 := by
  simp [s.apply_f_f]

theorem apply_f_f_of_ne {i j : Fin 10} (h : i ≠ j) : B (s.f i) (s.f j) = 1 := by
  simp [s.apply_f_f, h]

private theorem sum_ite_eq_nine (i : Fin 10) :
    ∑ j : Fin 10, (if i = j then (0 : ℤ) else 1) = 9 := by
  fin_cases i <;> decide

private theorem sum_ite_eq_nine' (i : Fin 10) :
    ∑ j : Fin 10, (if j = i then (0 : ℤ) else 1) = 9 := by
  fin_cases i <;> decide

/-- `fᵢ · δ = 3`. -/
@[simp]
theorem apply_f_δ (i : Fin 10) : B (s.f i) s.δ = 3 := by
  have h := congrArg (B (s.f i)) s.three_smul_δ
  simp only [map_smul, map_sum, s.apply_f_f, sum_ite_eq_nine, smul_eq_mul] at h
  omega

/-- `δ · fᵢ = 3`. -/
@[simp]
theorem apply_δ_f (i : Fin 10) : B s.δ (s.f i) = 3 := by
  have h := congrArg (fun x ↦ B x (s.f i)) s.three_smul_δ
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, s.apply_f_f,
    sum_ite_eq_nine', smul_eq_mul] at h
  omega

/-- `δ · δ = 10`. -/
@[simp]
theorem apply_δ_δ : B s.δ s.δ = 10 := by
  have h := congrArg (fun x ↦ B x s.δ) s.three_smul_δ
  simp [map_sum, LinearMap.sum_apply] at h
  omega

/-- `f₁₀ = 3δ - (f₁ + ⋯ + f₉)`. -/
theorem f_nine : s.f 9 = (3 : ℤ) • s.δ - ∑ i : Fin 9, s.f i.castSucc := by
  rw [s.three_smul_δ, Fin.sum_univ_castSucc]
  abel

/-! ### The roots `β₀, …, β₉` and `r` -/

/-- The ten roots `β₀ = δ - f₁ - f₂ - f₃ - f₄` and `βᵢ = fᵢ - fᵢ₊₁` for `1 ≤ i ≤ 9`, whose
intersection matrix is the negative of the Cartan matrix of the T246 diagram
(`apply_reyeRoot_reyeRoot`). -/
def reyeRoot : Fin 10 → M :=
  Fin.cons (s.δ - (s.f 0 + s.f 1 + s.f 2 + s.f 3)) fun i : Fin 9 ↦ s.f i.castSucc - s.f i.succ

/-- `β₀ = δ - f₁ - f₂ - f₃ - f₄`. -/
@[simp]
theorem reyeRoot_zero : s.reyeRoot 0 = s.δ - (s.f 0 + s.f 1 + s.f 2 + s.f 3) := (rfl)

/-- `βᵢ₊₁ = fᵢ₊₁ - fᵢ₊₂`. -/
@[simp]
theorem reyeRoot_succ (i : Fin 9) : s.reyeRoot i.succ = s.f i.castSucc - s.f i.succ := (rfl)

private theorem apply_reyeRoot_zero_zero : B (s.reyeRoot 0) (s.reyeRoot 0) = -2 := by
  simp [s.apply_f_f]

private theorem apply_reyeRoot_zero_succ (j : Fin 9) :
    B (s.reyeRoot 0) (s.reyeRoot j.succ) = if j = 3 then 1 else 0 := by
  simp only [reyeRoot_zero, reyeRoot_succ, map_sub, map_add, LinearMap.sub_apply,
    LinearMap.add_apply, apply_δ_f]
  fin_cases j <;> simp [s.apply_f_f]

private theorem apply_reyeRoot_succ_zero (i : Fin 9) :
    B (s.reyeRoot i.succ) (s.reyeRoot 0) = if i = 3 then 1 else 0 := by
  simp only [reyeRoot_zero, reyeRoot_succ, map_sub, map_add, LinearMap.sub_apply,
    apply_f_δ]
  fin_cases i <;> simp [s.apply_f_f]

private theorem apply_reyeRoot_succ_succ (i j : Fin 9) :
    B (s.reyeRoot i.succ) (s.reyeRoot j.succ) =
      if i = j then -2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 := by
  simp only [reyeRoot_succ, map_sub, LinearMap.sub_apply, s.apply_f_f, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- The intersection matrix of the roots `β₀, …, β₉`: each has square `-2`, the pairing of two
distinct roots is `1` on the nine edges of the T246 diagram, the chain `1 - 2 - ⋯ - 9` and the
edge `0 - 4`, and `0` otherwise. -/
theorem apply_reyeRoot_reyeRoot (i j : Fin 10) :
    B (s.reyeRoot i) (s.reyeRoot j) =
      if i = j then -2
      else if (i, j) ∈ [((0 : Fin 10), (4 : Fin 10)), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6),
          (6, 7), (7, 8), (8, 9)] ∨
        (j, i) ∈ [((0 : Fin 10), (4 : Fin 10)), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7),
          (7, 8), (8, 9)] then 1
      else 0 := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact s.apply_reyeRoot_zero_zero
    | succ j => rw [s.apply_reyeRoot_zero_succ]; fin_cases j <;> decide
  | succ i =>
    cases j using Fin.cases with
    | zero => rw [s.apply_reyeRoot_succ_zero]; fin_cases i <;> decide
    | succ j => rw [s.apply_reyeRoot_succ_succ]; fin_cases i <;> fin_cases j <;> decide

/-- The root `r = δ - 2 f₁₀`. It is orthogonal to `β₀, …, β₈` and has pairing `-2` with `β₉`;
the Reye lattice is the set of lattice vectors whose pairing with `r` is even
(`mem_reyeLattice_iff`). -/
def extraRoot : M := s.δ - (2 : ℤ) • s.f 9

/-- `r = δ - 2 f₁₀`. -/
theorem extraRoot_def : s.extraRoot = s.δ - (2 : ℤ) • s.f 9 := (rfl)

/-- `fᵢ · r` is `1` for `i ≤ 9` and `3` for `i = 10`. -/
@[simp]
theorem apply_f_extraRoot (i : Fin 10) : B (s.f i) s.extraRoot = if i = 9 then 3 else 1 := by
  simp only [extraRoot_def, map_sub, map_smul, apply_f_δ, s.apply_f_f, smul_eq_mul]
  split_ifs <;> simp

/-- `δ · r = 4`. -/
@[simp]
theorem apply_δ_extraRoot : B s.δ s.extraRoot = 4 := by
  simp [extraRoot_def]

/-- `r · r = -2`. -/
@[simp]
theorem apply_extraRoot_extraRoot : B s.extraRoot s.extraRoot = -2 := by
  simp [extraRoot_def]

/-- `βᵢ · r` is `0` for `i < 9` and `-2` for `i = 9`. -/
theorem apply_reyeRoot_extraRoot (i : Fin 10) :
    B (s.reyeRoot i) s.extraRoot = if i = 9 then -2 else 0 := by
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [reyeRoot_succ, map_sub, LinearMap.sub_apply, apply_f_extraRoot]
    fin_cases i <;> simp

/-- `r · βᵢ` is `0` for `i < 9` and `-2` for `i = 9`. -/
theorem apply_extraRoot_reyeRoot (i : Fin 10) :
    B s.extraRoot (s.reyeRoot i) = if i = 9 then -2 else 0 := by
  cases i using Fin.cases with
  | zero => simp [extraRoot_def, s.apply_f_f]
  | succ i =>
    simp only [reyeRoot_succ, extraRoot_def, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, apply_δ_f]
    fin_cases i <;> simp [s.apply_f_f]

/-- The roots `β₀, …, β₉` are linearly independent. -/
theorem linearIndependent_reyeRoot : LinearIndependent ℤ s.reyeRoot := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h (j : Fin 10) : ∑ i, c i * B (s.reyeRoot i) (s.reyeRoot j) = 0 := by
    simpa [map_sum, LinearMap.sum_apply] using congrArg (fun x ↦ B x (s.reyeRoot j)) hc
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  have h9 := h 9
  simp only [s.apply_reyeRoot_reyeRoot, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  intro i
  fin_cases i <;> simp <;> omega

/-! ### The two lattices -/

/-- The Reye lattice `R`, the span of the roots `β₀, …, β₉`. -/
def reyeLattice : Submodule ℤ M := span ℤ (Set.range s.reyeRoot)

theorem reyeRoot_mem_reyeLattice (i : Fin 10) : s.reyeRoot i ∈ s.reyeLattice :=
  subset_span ⟨i, rfl⟩

/-- The basis `β₀, …, β₉` of the Reye lattice. -/
noncomputable def reyeBasis : Basis (Fin 10) ℤ s.reyeLattice :=
  Basis.span s.linearIndependent_reyeRoot

@[simp]
theorem coe_reyeBasis (i : Fin 10) : (s.reyeBasis i : M) = s.reyeRoot i :=
  Basis.coe_span_apply _ _

/-- The lattice spanned by `f₁, …, f₁₀` and `δ`. -/
def lattice : Submodule ℤ M := span ℤ (insert s.δ (Set.range s.f))

theorem δ_mem_lattice : s.δ ∈ s.lattice := subset_span (Set.mem_insert _ _)

theorem f_mem_lattice (i : Fin 10) : s.f i ∈ s.lattice :=
  subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

theorem reyeRoot_mem_lattice (i : Fin 10) : s.reyeRoot i ∈ s.lattice := by
  cases i using Fin.cases with
  | zero =>
    exact sub_mem s.δ_mem_lattice <| add_mem (add_mem (add_mem (s.f_mem_lattice 0)
      (s.f_mem_lattice 1)) (s.f_mem_lattice 2)) (s.f_mem_lattice 3)
  | succ i => exact sub_mem (s.f_mem_lattice _) (s.f_mem_lattice _)

/- `simp` writes `Fin.last 9` as the numeral `9`; these two facts let the `Fin.snoc` and
`Fin.lastCases` lemmas, stated for `Fin.last`, meet that normal form. -/
private theorem last_nine : Fin.last 9 = 9 := rfl

private theorem castSucc_ne_nine (i : Fin 9) : i.castSucc ≠ 9 := Fin.castSucc_ne_last i

/-- The vectors `f₁, …, f₉, δ`. -/
private def latticeBasisVec : Fin 10 → M := Fin.snoc (fun i : Fin 9 ↦ s.f i.castSucc) s.δ

private theorem latticeBasisVec_castSucc (i : Fin 9) :
    s.latticeBasisVec i.castSucc = s.f i.castSucc :=
  Fin.snoc_castSucc (α := fun _ ↦ M) _ _ _

private theorem latticeBasisVec_nine : s.latticeBasisVec 9 = s.δ :=
  Fin.snoc_last (α := fun _ ↦ M) _ _

private theorem linearIndependent_latticeBasisVec : LinearIndependent ℤ s.latticeBasisVec := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_castSucc, last_nine] at hc
  simp only [latticeBasisVec_castSucc, latticeBasisVec_nine] at hc
  have h (j : Fin 9) :
      ∑ i : Fin 9, c i.castSucc * B (s.f i.castSucc) (s.f j.castSucc) + c 9 * 3 = 0 := by
    simpa [map_sum, LinearMap.sum_apply] using congrArg (fun x ↦ B x (s.f j.castSucc)) hc
  have hδ : ∑ i : Fin 9, c i.castSucc * 3 + c 9 * 10 = 0 := by
    simpa [map_sum, LinearMap.sum_apply] using congrArg (fun x ↦ B x s.δ) hc
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  simp [Fin.sum_univ_succ, s.apply_f_f] at h0 h1 h2 h3 h4 h5 h6 h7 h8 hδ
  intro i
  fin_cases i <;> simp <;> omega

private theorem span_range_latticeBasisVec : span ℤ (Set.range s.latticeBasisVec) = s.lattice := by
  apply le_antisymm
  · rw [span_le, Set.range_subset_iff]
    intro i
    cases i using Fin.lastCases with
    | last => rw [last_nine, latticeBasisVec_nine]; exact s.δ_mem_lattice
    | cast i => rw [latticeBasisVec_castSucc]; exact s.f_mem_lattice _
  · have hv (i : Fin 10) : s.latticeBasisVec i ∈ span ℤ (Set.range s.latticeBasisVec) :=
      subset_span ⟨i, rfl⟩
    rw [lattice, span_le, Set.insert_subset_iff, Set.range_subset_iff]
    have hδ : s.δ ∈ span ℤ (Set.range s.latticeBasisVec) := s.latticeBasisVec_nine ▸ hv 9
    refine ⟨hδ, fun i ↦ ?_⟩
    cases i using Fin.lastCases with
    | last =>
      rw [last_nine, f_nine]
      refine sub_mem (smul_mem _ _ hδ) (sum_mem fun i _ ↦ ?_)
      simpa [latticeBasisVec_castSucc] using hv i.castSucc
    | cast i => simpa [latticeBasisVec_castSucc] using hv i.castSucc

/-- The basis `f₁, …, f₉, δ` of the lattice spanned by the sequence. -/
noncomputable def latticeBasis : Basis (Fin 10) ℤ s.lattice :=
  (Basis.span s.linearIndependent_latticeBasisVec).map
    (LinearEquiv.ofEq _ _ s.span_range_latticeBasisVec)

@[simp]
theorem coe_latticeBasis_castSucc (i : Fin 9) :
    (s.latticeBasis i.castSucc : M) = s.f i.castSucc := by
  simp [latticeBasis, latticeBasisVec_castSucc]

@[simp]
theorem coe_latticeBasis_nine : (s.latticeBasis 9 : M) = s.δ := by
  simp [latticeBasis, latticeBasisVec_nine]

theorem reyeLattice_le_lattice : s.reyeLattice ≤ s.lattice :=
  span_le.2 (Set.range_subset_iff.2 s.reyeRoot_mem_lattice)

private theorem f_sub_f_zero_mem_reyeLattice (i : Fin 10) : s.f i - s.f 0 ∈ s.reyeLattice := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := sub_mem ih (s.reyeRoot_mem_reyeLattice i.succ)
    rw [reyeRoot_succ] at h
    convert h using 1
    abel

private theorem δ_sub_mem_reyeLattice : s.δ - (4 : ℤ) • s.f 0 ∈ s.reyeLattice := by
  have h := add_mem (add_mem (add_mem (s.reyeRoot_mem_reyeLattice 0)
    (s.f_sub_f_zero_mem_reyeLattice 1)) (s.f_sub_f_zero_mem_reyeLattice 2))
    (s.f_sub_f_zero_mem_reyeLattice 3)
  convert h using 1
  rw [reyeRoot_zero]
  module

private theorem two_smul_f_zero_mem_reyeLattice : (2 : ℤ) • s.f 0 ∈ s.reyeLattice := by
  have h : (2 : ℤ) • s.f 0 =
      ∑ i, (s.f i - s.f 0) - (3 : ℤ) • (s.δ - (4 : ℤ) • s.f 0) := by
    rw [Finset.sum_sub_distrib, ← s.three_smul_δ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    module
  rw [h]
  exact sub_mem (sum_mem fun i _ ↦ s.f_sub_f_zero_mem_reyeLattice i)
    (smul_mem _ _ s.δ_sub_mem_reyeLattice)

private theorem sub_smul_f_zero_mem_reyeLattice {x : M} (hx : x ∈ s.lattice) :
    x - B x s.extraRoot • s.f 0 ∈ s.reyeLattice := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · rw [apply_δ_extraRoot]
      exact s.δ_sub_mem_reyeLattice
    · rw [apply_f_extraRoot]
      split_ifs with h
      · subst h
        have h := sub_mem (s.f_sub_f_zero_mem_reyeLattice 9) s.two_smul_f_zero_mem_reyeLattice
        convert h using 1
        module
      · simpa using s.f_sub_f_zero_mem_reyeLattice i
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    simp only [map_add, LinearMap.add_apply, add_smul]
    abel
  | smul a x _ hx =>
    convert smul_mem _ a hx using 1
    simp [smul_sub, mul_smul]

/-- The Reye lattice consists of the vectors of the lattice spanned by the sequence whose pairing
with `r` is even. -/
theorem mem_reyeLattice_iff {x : M} :
    x ∈ s.reyeLattice ↔ x ∈ s.lattice ∧ Even (B x s.extraRoot) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨s.reyeRoot_mem_lattice i, ?_⟩
      rw [apply_reyeRoot_extraRoot]
      split_ifs <;> decide
    | zero => simp
    | add x y _ _ hx hy =>
      simpa using ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
    | smul a x _ hx =>
      simpa using ⟨smul_mem _ a hx.1, hx.2.mul_left a⟩
  · rintro ⟨hx, m, hm⟩
    have h := add_mem (s.sub_smul_f_zero_mem_reyeLattice hx)
      (smul_mem _ m s.two_smul_f_zero_mem_reyeLattice)
    convert h using 1
    rw [hm]
    module

/-- No `fᵢ` lies in the Reye lattice, since `fᵢ · r` is odd. -/
theorem f_notMem_reyeLattice (i : Fin 10) : s.f i ∉ s.reyeLattice := by
  rw [mem_reyeLattice_iff, apply_f_extraRoot]
  split_ifs <;> simp [show ¬Even (3 : ℤ) by decide]

/-- The Reye lattice has index two in the lattice spanned by the sequence. -/
theorem relIndex_reyeLattice_lattice :
    s.reyeLattice.toAddSubgroup.relIndex s.lattice.toAddSubgroup = 2 := by
  rw [AddSubgroup.relIndex_eq_two_iff]
  refine ⟨s.f 0, s.f_mem_lattice 0, fun b hb ↦ ?_⟩
  simp only [Submodule.mem_toAddSubgroup] at hb ⊢
  rw [s.mem_reyeLattice_iff, s.mem_reyeLattice_iff]
  simp [hb, add_mem hb (s.f_mem_lattice 0), ← Int.not_even_iff_odd]

/-- When the sequence generates `M`, the Reye lattice has index two in `M`. -/
theorem index_reyeLattice (h : s.lattice = ⊤) : s.reyeLattice.toAddSubgroup.index = 2 := by
  rw [← AddSubgroup.relIndex_top_right, ← s.relIndex_reyeLattice_lattice, h,
    Submodule.top_toAddSubgroup]

private theorem sum_ite_eq_eight (i : Fin 9) :
    ∑ j : Fin 9, (if i = j then (0 : ℤ) else 1) = 8 := by
  fin_cases i <;> decide

private theorem sum_ite_eq_eight' (j : Fin 9) :
    ∑ i : Fin 9, (if i = j then (0 : ℤ) else 1) = 8 := by
  fin_cases j <;> decide

/-! ### Construction from a basis and a model -/

/-- The isotropic 10-sequence `f₁, …, f₉, f₁₀ = 3δ - (f₁ + ⋯ + f₉)` built from nine vectors
`f₁, …, f₉` and a vector `δ` with `fᵢ · fⱼ = 1 - δᵢⱼ`, `fᵢ · δ = δ · fᵢ = 3` and `δ · δ = 10`. -/
def ofGram (g : Fin 9 → M) (δ : M) (hgg : ∀ i j, B (g i) (g j) = if i = j then 0 else 1)
    (hgδ : ∀ i, B (g i) δ = 3) (hδg : ∀ i, B δ (g i) = 3) (hδδ : B δ δ = 10) :
    IsotropicTenSequence B where
  f := Fin.snoc g ((3 : ℤ) • δ - ∑ i, g i)
  δ := δ
  apply_f_f i j := by
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        simp [map_sum, LinearMap.sum_apply, hgg, hgδ, hδg, hδδ, sum_ite_eq_eight]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, (Fin.castSucc_ne_last j).symm, ite_false]
        simp [map_sum, LinearMap.sum_apply, hgg, hδg, sum_ite_eq_eight']
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last i, ite_false]
        simp [map_sum, hgg, hgδ, sum_ite_eq_eight]
      | cast j => simp [hgg]
  three_smul_δ := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    abel

/-- The first nine vectors of `ofGram g δ` are `g`. -/
@[simp]
theorem ofGram_f_castSucc (g : Fin 9 → M) (δ : M) (hgg hgδ hδg hδδ) (i : Fin 9) :
    (ofGram (B := B) g δ hgg hgδ hδg hδδ).f i.castSucc = g i :=
  Fin.snoc_castSucc (α := fun _ ↦ M) _ _ _

/-- The last vector of `ofGram g δ` is `3δ - (g₁ + ⋯ + g₉)`. -/
@[simp]
theorem ofGram_f_nine (g : Fin 9 → M) (δ : M) (hgg hgδ hδg hδδ) :
    (ofGram (B := B) g δ hgg hgδ hδg hδδ).f 9 = (3 : ℤ) • δ - ∑ i, g i := by
  rw [← last_nine]
  unfold ofGram
  dsimp only
  rw [Fin.snoc_last]

/-- The vector `δ` of `ofGram g δ` is `δ`. -/
@[simp]
theorem ofGram_δ (g : Fin 9 → M) (δ : M) (hgg hgδ hδg hδδ) :
    (ofGram (B := B) g δ hgg hgδ hδg hδδ).δ = δ := (rfl)

/-- The Gram matrix of `f₁, …, f₉, δ` for an isotropic 10-sequence: `fᵢ · fⱼ = 1 - δᵢⱼ`,
`fᵢ · δ = 3` and `δ · δ = 10`, with `δ` the last index. -/
def standardGram : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun i j ↦
    if i = 9 ∧ j = 9 then 10 else if i = 9 ∨ j = 9 then 3 else if i = j then 0 else 1

/-- The isotropic 10-sequence on `ℤ¹⁰` with the form `standardGram`, whose first nine vectors and
`δ` are the standard basis vectors. -/
noncomputable def standard : IsotropicTenSequence (Matrix.toBilin' standardGram) :=
  ofGram (fun i ↦ Pi.single i.castSucc 1) (Pi.single 9 1)
    (fun i j ↦ by simp [standardGram, castSucc_ne_nine])
    (fun i ↦ by simp [standardGram, castSucc_ne_nine])
    (fun i ↦ by simp [standardGram, castSucc_ne_nine])
    (by simp [standardGram])

/-- The standard isotropic 10-sequence generates `ℤ¹⁰`. -/
theorem lattice_standard : standard.lattice = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin 10)).span_eq, span_le, Set.range_subset_iff]
  intro i
  cases i using Fin.lastCases with
  | last => simpa [standard, last_nine] using standard.δ_mem_lattice
  | cast i => simpa [standard] using standard.f_mem_lattice i.castSucc

end IsotropicTenSequence

end LinearMap.BilinForm
