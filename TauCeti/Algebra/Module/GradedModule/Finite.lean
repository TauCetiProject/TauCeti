/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Length
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.GradedAlgebra.FiniteType

/-!
# Finiteness of graded pieces of finitely generated graded modules

Let `B = ⨁_{i : ℕ} ℬ i` be a nonnegatively graded `A`-semiring and `M = ⨁_{d : ℤ} ℳ d` a finitely
generated `ℤ`-graded `B`-module (allowing generators of negative degree).

* For any index type `ι`, a finitely generated internally `ι`-graded module is spanned over the
  acting semiring by finitely many homogeneous elements
  (`TauCeti.GradedModule.exists_finset_homogeneous_span`).
* Any `m ∈ ℳ d` in the `B`-span of homogeneous elements `G` decomposes as a sum over those
  elements of degree `≤ d` with homogeneous coefficients of degree `(d - p.1).toNat`
  (`TauCeti.GradedModule.exists_eq_sum_filter_decompose_smul`).
* Consequently, the pieces `ℳ d` vanish for all `d` below some integer `d₀`
  (`TauCeti.GradedModule.exists_forall_lt_piece_eq_bot`).
* If every `ℬ i` is a finite `A`-module, then every `ℳ d` is a finite `A`-module
  (`TauCeti.GradedModule.moduleFinite_piece`), without any Noetherian hypothesis on `A`: each `ℳ d`
  is the finite sum of the images of `ℬ (d - deg g)` under right-multiplication by finitely many
  homogeneous generators `g`. Combining this with finite piece size of finite-type `ℕ`-graded
  algebras yields `TauCeti.GradedModule.gradedPiecesFinite`. Over an Artinian ring `A`, every
  piece `ℳ d` therefore has finite `A`-length (`TauCeti.GradedModule.length_piece_ne_top`).

## Main results

* `TauCeti.GradedModule.exists_finset_homogeneous_span`: a finitely generated internally graded
  module is spanned by finitely many homogeneous elements.
* `TauCeti.GradedModule.exists_eq_sum_filter_decompose_smul`: homogeneous-coefficient expansion of
  a graded element lying in the span of finitely many homogeneous elements.
* `TauCeti.GradedModule.exists_forall_lt_piece_eq_bot`: a finitely generated `ℤ`-graded module over
  an `ℕ`-graded semiring vanishes below some degree `d₀`.
* `TauCeti.GradedModule.moduleFinite_piece`: every graded piece of a finitely generated `ℤ`-graded
  module over an `ℕ`-graded semiring with finite pieces is finite over the base.
* `TauCeti.GradedModule.gradedPiecesFinite`: every graded piece of a finitely generated `ℤ`-graded
  module over a finite-type `ℕ`-graded algebra with finite degree-zero part is finite over the
  base, and the pieces vanish below some degree.
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
  obtain ⟨S, hS, hspan⟩ := (InternalGrading.ofDecomposition ℳ).exists_finset_span_eq_top B
  rw [InternalGrading.ofDecomposition_piece] at hS
  let G : Finset (ι × M) := S.attach.image fun x ↦ ((hS x.val x.property).choose, x.val)
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨j, x⟩ hp
    rcases Finset.mem_image.mp hp with ⟨⟨y, hy⟩, -, hxy⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    exact (hS y hy).choose_spec
  · convert hspan using 2
    ext y
    simp [G]

/-- Any `m ∈ ℳ d` in the `B`-span of homogeneous elements `G` decomposes as a sum over those
elements of degree `≤ d` with homogeneous coefficients of degree `(d - p.1).toNat`. -/
theorem exists_eq_sum_filter_decompose_smul {A B M : Type*} [Semiring A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i))
    {G : Finset (ℤ × M)} (hGmem : ∀ p ∈ G, p.2 ∈ ℳ p.1)
    {d : ℤ} {m : M} (hm : m ∈ ℳ d)
    (hm_span : m ∈ Submodule.span B (Set.range fun p : G ↦ p.val.2)) :
    ∃ c : G → B, m = ∑ p ∈ Finset.univ.filter (fun p : G ↦ p.val.1 ≤ d),
      (decompose ℬ (c p) (d - p.val.1).toNat : B) • p.val.2 := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hm_span
  refine ⟨c, ?_⟩
  conv_lhs => rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply,
    Submodule.coe_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : G ↦ p.val.1 ≤ d)]
  have hzero : ∑ p ∈ Finset.univ.filter (fun p : G ↦ ¬ p.val.1 ≤ d),
      (decompose ℳ (c p • p.val.2) d : M) = 0 :=
    Finset.sum_eq_zero fun p hp ↦
      decompose_smul_eq_zero_of_lt ℬ ℳ hgraded (by have := (Finset.mem_filter.mp hp).2; omega)
        (c p) (hGmem p.val p.property)
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  exact decompose_smul_of_le ℬ ℳ hgraded (Finset.mem_filter.mp hp).2 (c p) (hGmem p.val p.property)

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
  obtain ⟨c, rfl⟩ :=
    exists_eq_sum_filter_decompose_smul ℬ ℳ hgraded hGmem hm (hGspan ▸ Submodule.mem_top)
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hne : G.Nonempty := ⟨p.val, p.property⟩
  have hle : d₀ ≤ p.val.1 := by
    simp only [d₀, hne, ↓reduceDIte]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)
  have := (Finset.mem_filter.mp hp).2
  omega

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
      obtain ⟨c, rfl⟩ :=
        exists_eq_sum_filter_decompose_smul ℬ ℳ hgraded hGmem hm (hGspan ▸ Submodule.mem_top)
      refine Submodule.sum_mem U fun p hp ↦ ?_
      exact (Finset.le_sup (f := fun q : G ↦ LinearMap.range (φ q)) hp)
        ⟨decompose ℬ (c p) (d - p.val.1).toNat, rfl⟩
  exact Module.Finite.of_fg (hU_eq ▸ hU_fg)

/-- **Graded piece finiteness.** Every graded piece of a finitely generated `ℤ`-graded module over
a finite-type `ℕ`-graded algebra with finite degree-zero part is a finite `A`-module, and the
pieces vanish below some degree `d₀`. -/
theorem gradedPiecesFinite {A B M : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]
    (ℬ : ℕ → Submodule A B) [GradedAlgebra ℬ] [Algebra.FiniteType (ℬ 0) B]
    [Module.Finite A (ℬ 0)] [AddCommMonoid M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    (∀ d, Module.Finite A (ℳ d)) ∧ ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ :=
  ⟨moduleFinite_piece ℬ (TauCeti.GradedAlgebra.moduleFinite_gradedPiece_of_finiteType ℬ) ℳ
      hgraded,
    exists_forall_lt_piece_eq_bot ℬ ℳ hgraded⟩

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
