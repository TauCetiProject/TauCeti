/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Finiteness of graded pieces of finitely generated graded modules

Let `B = ⨁_{i : ℕ} ℬ i` be a nonnegatively graded `A`-semiring and `M = ⨁_{d : ℤ} ℳ d` a finitely
generated `ℤ`-graded `B`-module (allowing generators of negative degree).

* For any index type `ι`, a finitely generated internally `ι`-graded module is spanned over the
  acting semiring by finitely many homogeneous elements
  (`TauCeti.GradedModule.exists_finset_homogeneous_span`).
* When `b ∈ ℬ i` shifts `ℳ j` into `ℳ (j + i)`, the degree-`d` component of `b • m` (for `m ∈ ℳ j`)
  vanishes for `d < j` (`TauCeti.GradedModule.decompose_smul_eq_zero_of_lt`) and equals
  `(decompose ℬ b (d - j).toNat) • m` for `j ≤ d` (`TauCeti.GradedModule.decompose_smul_of_le`).
* Consequently, the pieces `ℳ d` vanish for all `d` below some integer `d₀`
  (`TauCeti.GradedModule.exists_forall_lt_piece_eq_bot`).
* If every `ℬ i` is a finite `A`-module, then every `ℳ d` is a finite `A`-module
  (`TauCeti.GradedModule.moduleFinite_piece`), without any Noetherian hypothesis on `A`: each `ℳ d`
  is the finite sum of the images of `ℬ (d - deg g)` under right-multiplication by finitely many
  homogeneous generators `g`. Over an Artinian ring `A`, every piece `ℳ d` therefore has finite
  `A`-length (`TauCeti.GradedModule.length_piece_ne_top`).

## Main results

* `TauCeti.GradedModule.exists_finset_homogeneous_span`: a finitely generated internally graded
  module is spanned by finitely many homogeneous elements.
* `TauCeti.GradedModule.decompose_smul_eq_zero_of_lt` and
  `TauCeti.GradedModule.decompose_smul_of_le`: homogeneous components of `b • m` for a `ℤ`-graded
  module over an `ℕ`-graded semiring.
* `TauCeti.GradedModule.exists_forall_lt_piece_eq_bot`: a finitely generated `ℤ`-graded module over
  an `ℕ`-graded semiring vanishes below some degree `d₀`.
* `TauCeti.GradedModule.moduleFinite_piece`: every graded piece of a finitely generated `ℤ`-graded
  module over an `ℕ`-graded semiring with finite pieces is finite over the base.
* `TauCeti.GradedModule.moduleFinite_piece_mvPolynomial`: specialization to modules over
  `MvPolynomial σ A` with `σ` finite.
* `TauCeti.GradedModule.exists_degree_ge_le_span_piece`: for a finitely generated `ℤ`-graded
  `MvPolynomial σ A`-module, every sufficiently high graded piece generates the subsequent tail.
* `TauCeti.GradedModule.length_piece_ne_top`: over an Artinian ring, every graded piece has finite
  length.
-/

public section

open DirectSum

namespace TauCeti.GradedModule

/-- A finitely generated module with an internal `ι`-grading is spanned over the acting semiring by
finitely many homogeneous elements. -/
theorem exists_finset_homogeneous_span {A B M ι : Type*} [DecidableEq ι] [Semiring A] [Semiring B]
    [AddCommMonoid M] [Module A M] [Module B M] [Module.Finite B M]
    (ℳ : ι → Submodule A M) [DirectSum.Decomposition ℳ] :
    ∃ G : Finset (ι × M), (∀ p ∈ G, p.2 ∈ ℳ p.1) ∧
      Submodule.span B (Set.range fun p : G ↦ p.val.2) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := M)
  let G : Finset (ι × M) :=
    S.biUnion fun s ↦ (decompose ℳ s).support.image fun j ↦ (j, (decompose ℳ s j : M))
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    simp only [G, Finset.mem_biUnion, Finset.mem_image] at hp
    rcases hp with ⟨s, -, j, -, rfl⟩
    exact (decompose ℳ s j).property
  · rw [← top_le_iff, ← hS, Submodule.span_le]
    intro s hs
    rw [← sum_support_decompose ℳ s]
    refine Submodule.sum_mem _ fun j hj ↦ Submodule.subset_span ?_
    have hmem : (j, (decompose ℳ s j : M)) ∈ G :=
      Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    exact ⟨⟨(j, (decompose ℳ s j : M)), hmem⟩, rfl⟩

/-- The degree-`d` component of `b • m`, for `m ∈ ℳ j`, vanishes whenever `d < j`. -/
theorem decompose_smul_eq_zero_of_lt {A B M : Type*} [Semiring A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i))
    {j d : ℤ} (hdj : d < j) (b : B) {m : M} (hm : m ∈ ℳ j) :
    (decompose ℳ (b • m) d : M) = 0 := by
  induction b using Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous i b => exact decompose_of_mem_ne ℳ (hgraded i j b b.property m hm) (by omega)
  | add b₁ b₂ hb₁ hb₂ => simp [add_smul, hb₁, hb₂]

/-- The degree-`d` component of `b • m`, for `m ∈ ℳ j` with `j ≤ d`, equals the degree-`(d - j)`
component of `b` acting on `m`. -/
theorem decompose_smul_of_le {A B M : Type*} [Semiring A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i))
    {j d : ℤ} (hjd : j ≤ d) (b : B) {m : M} (hm : m ∈ ℳ j) :
    (decompose ℳ (b • m) d : M) = (decompose ℬ b (d - j).toNat : B) • m := by
  induction b using Decomposition.inductionOn ℬ with
  | zero => simp
  | @homogeneous i b =>
    have hmem : (b : B) • m ∈ ℳ (j + i) := hgraded i j b b.property m hm
    by_cases hi : i = (d - j).toNat
    · subst hi
      rw [decompose_of_mem_same ℬ b.property]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hjd), add_sub_cancel] at hmem
      exact decompose_of_mem_same ℳ hmem
    · rw [decompose_of_mem_ne ℳ hmem (by omega), decompose_of_mem_ne ℬ b.property hi, zero_smul]
  | add b₁ b₂ hb₁ hb₂ => simp [add_smul, hb₁, hb₂]

/-- **Vanishing in sufficiently negative degrees.** A finitely generated `ℤ`-graded module over an
`ℕ`-graded semiring vanishes in all degrees below some integer `d₀`. -/
theorem exists_forall_lt_piece_eq_bot {A B M : Type*} [Semiring A] [Semiring B] [Module A B]
    (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ := by
  classical
  obtain ⟨G, hGmem, hGspan⟩ := exists_finset_homogeneous_span (B := B) ℳ
  let d₀ : ℤ := if h : G.Nonempty then (G.image Prod.fst).min' (h.image _) else 0
  refine ⟨d₀, fun d hd ↦ (Submodule.eq_bot_iff _).mpr fun m hm ↦ ?_⟩
  have hm_span : m ∈ Submodule.span B (Set.range fun p : G ↦ p.val.2) := hGspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hm_span
  rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  have hne : G.Nonempty := ⟨p.val, p.property⟩
  have hd_lt : d < p.val.1 := by
    have hle : d₀ ≤ p.val.1 := by
      simp only [d₀, hne, ↓reduceDIte]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)
    exact hd.trans_le hle
  exact decompose_smul_eq_zero_of_lt ℬ ℳ hgraded hd_lt (c p) (hGmem p.val p.property)

/-- **Finiteness of graded pieces.** Every graded piece of a finitely generated `ℤ`-graded module
over an `ℕ`-graded semiring whose graded pieces are finite `A`-modules is itself a finite
`A`-module. No Noetherian hypothesis on `A` is needed. -/
theorem moduleFinite_piece {A B M : Type*} [Semiring A] [Semiring B] [Module A B]
    (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ] (hℬ : ∀ i, Module.Finite A (ℬ i))
    [AddCommMonoid M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) (d : ℤ) :
    Module.Finite A (ℳ d) := by
  classical
  obtain ⟨G, hGmem, hGspan⟩ := exists_finset_homogeneous_span (B := B) ℳ
  -- For each generator `p ∈ G` with `p.1 ≤ d`, map `ℬ (d - p.1)` into `M` by `b ↦ b • p.2`.
  let φ : ∀ p : G, ℬ (d - p.val.1).toNat →ₗ[A] M := fun p ↦
    { toFun := fun b ↦ (b : B) • p.val.2
      map_add' := fun b₁ b₂ ↦ add_smul _ _ _
      map_smul' := fun a b ↦ by simp [smul_assoc] }
  let U : Submodule A M :=
    (Finset.univ.filter fun p : G ↦ p.val.1 ≤ d).sup fun p ↦ LinearMap.range (φ p)
  have hU_fg : U.FG := Submodule.fg_finset_sup _ _ fun p _ ↦ by
    have : Module.Finite A (ℬ (d - p.val.1).toNat) := hℬ _
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top (R := A)).map (φ p)
  have hU_eq : U = ℳ d := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le fun p hp ↦ ?_
      have hle : p.val.1 ≤ d := (Finset.mem_filter.mp hp).2
      rintro _ ⟨b, rfl⟩
      have h := hgraded (d - p.val.1).toNat p.val.1 b b.property p.val.2 (hGmem p.val p.property)
      rwa [Int.toNat_of_nonneg (sub_nonneg.mpr hle), add_sub_cancel] at h
    · intro m hm
      have hm_span : m ∈ Submodule.span B (Set.range fun p : G ↦ p.val.2) :=
        hGspan ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hm_span
      rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
      refine Submodule.sum_mem U fun p _ ↦ ?_
      by_cases hle : p.val.1 ≤ d
      · rw [decompose_smul_of_le ℬ ℳ hgraded hle (c p) (hGmem p.val p.property)]
        have hpU : LinearMap.range (φ p) ≤ U :=
          Finset.le_sup (f := fun q : G ↦ LinearMap.range (φ q))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hle⟩)
        exact hpU ⟨decompose ℬ (c p) (d - p.val.1).toNat, rfl⟩
      · rw [decompose_smul_eq_zero_of_lt ℬ ℳ hgraded (by omega) (c p) (hGmem p.val p.property)]
        exact U.zero_mem
  exact Module.Finite.of_fg (hU_eq ▸ hU_fg)

/-- Every graded piece of a finitely generated `ℤ`-graded module over `MvPolynomial σ A` (with
finitely many variables `σ`) is a finite `A`-module. -/
theorem moduleFinite_piece_mvPolynomial {A σ M : Type*} [CommSemiring A] [Finite σ]
    [AddCommMonoid M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) (d : ℤ) :
    Module.Finite A (ℳ d) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  exact moduleFinite_piece (MvPolynomial.homogeneousSubmodule σ A)
    (fun i ↦ TauCeti.homogeneousSubmodule_moduleFinite i) ℳ hgraded d

/-- For a finitely generated `ℤ`-graded `MvPolynomial σ A`-module, all pieces from some degree `N₀`
onward are generated over `MvPolynomial σ A` by any single piece `ℳ N₁` with `N₁ ≥ N₀`. -/
theorem exists_degree_ge_le_span_piece {A σ M : Type*} [CommSemiring A]
    [AddCommMonoid M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    ∃ N₀ : ℤ, ∀ N₁ ≥ N₀, ∀ d ≥ N₁,
      ℳ d ≤ (Submodule.span (MvPolynomial σ A) (ℳ N₁ : Set M)).restrictScalars A := by
  classical
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  obtain ⟨G, hGmem, hGspan⟩ := exists_finset_homogeneous_span (B := MvPolynomial σ A) ℳ
  let N₀ : ℤ := if h : G.Nonempty then (G.image Prod.fst).max' (h.image _) else 0
  refine ⟨N₀, fun N₁ hN₁ d hd m hm ↦ ?_⟩
  have hm_span : m ∈ Submodule.span (MvPolynomial σ A) (Set.range fun p : G ↦ p.val.2) :=
    hGspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial σ A)).mp hm_span
  rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  have hp_le : p.val.1 ≤ N₁ := le_trans (by
    have hne : G.Nonempty := ⟨p.val, p.property⟩
    simp only [N₀, hne, ↓reduceDIte]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)) hN₁
  rw [decompose_smul_of_le (MvPolynomial.homogeneousSubmodule σ A) ℳ hgraded
    (hp_le.trans hd) (c p) (hGmem p.val p.property)]
  set q := decompose (MvPolynomial.homogeneousSubmodule σ A) (c p) (d - p.val.1).toNat
  have hdeg : (d - p.val.1).toNat = (d - N₁).toNat + (N₁ - p.val.1).toNat := by omega
  have hq : (q : MvPolynomial σ A) ∈
      MvPolynomial.homogeneousSubmodule σ A (d - N₁).toNat *
        MvPolynomial.homogeneousSubmodule σ A (N₁ - p.val.1).toNat := by
    have hpow1 : MvPolynomial.homogeneousSubmodule σ A (d - N₁).toNat =
        MvPolynomial.homogeneousSubmodule σ A 1 ^ (d - N₁).toNat :=
      (MvPolynomial.homogeneousSubmodule_one_pow A _).symm
    have hpow2 : MvPolynomial.homogeneousSubmodule σ A (N₁ - p.val.1).toNat =
        MvPolynomial.homogeneousSubmodule σ A 1 ^ (N₁ - p.val.1).toNat :=
      (MvPolynomial.homogeneousSubmodule_one_pow A _).symm
    rw [hpow1, hpow2, ← pow_add, MvPolynomial.homogeneousSubmodule_one_pow, ← hdeg]
    exact q.property
  refine Submodule.mul_induction_on hq (fun r₁ _ r₂ hr₂ ↦ ?_) (fun u v hu hv ↦ by
    rw [add_smul]; exact add_mem hu hv)
  rw [mul_smul]
  have hr₂m : r₂ • p.val.2 ∈ ℳ N₁ := by
    have h1 := hgraded (N₁ - p.val.1).toNat p.val.1 r₂ hr₂ p.val.2 (hGmem p.val p.property)
    rwa [Int.toNat_of_nonneg (sub_nonneg.mpr hp_le), add_sub_cancel] at h1
  exact Submodule.smul_mem _ r₁ (Submodule.subset_span hr₂m)

/-- Over an Artinian ring `A`, every graded piece of a finitely generated `ℤ`-graded module over an
`ℕ`-graded semiring with finite pieces has finite `A`-length. -/
theorem length_piece_ne_top {A B M : Type*} [Ring A] [IsArtinianRing A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    (hℬ : ∀ i, Module.Finite A (ℬ i)) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) (d : ℤ) :
    Module.length A (ℳ d) ≠ ⊤ := by
  have : Module.Finite A (ℳ d) := moduleFinite_piece ℬ hℬ ℳ hgraded d
  exact Module.length_ne_top_iff.mpr (TauCeti.isFiniteLength_of_finite A (ℳ d))

end TauCeti.GradedModule
