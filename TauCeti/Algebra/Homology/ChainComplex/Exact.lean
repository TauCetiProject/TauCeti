/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness of a chain complex assembled from consecutive differentials

Translate exactness of consecutive pairs of specified differentials to `ExactAt` for
`ChainComplex.of`.

In an abelian category, a complex `K` which is exact in positive degrees, with an epimorphic
augmentation `K.X 0 ⟶ X` exact at `K.X 0`, maps quasi-isomorphically to `X` placed in degree `0`
(`ChainComplex.quasiIso_toSingle₀Equiv_symm`). A complex whose differentials factor through short
exact sequences `0 ⟶ A (p + 1) ⟶ K.X p ⟶ A p ⟶ 0` is of this kind
(`ChainComplex.exactAt_succ_of_shortExact`, `ChainComplex.exact_d_one_zero_of_shortExact`,
`ChainComplex.quasiIso_toSingle₀Equiv_symm_of_shortExact`).
-/

public section

namespace ChainComplex

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Exactness of the specified differentials gives exactness in positive degrees of the
chain complex assembled by `ChainComplex.of`. -/
theorem of_exactAt_succ (X : ℕ → C) (d : ∀ n, X (n + 1) ⟶ X n)
    (zero : ∀ n, d (n + 1) ≫ d n = 0) (n : ℕ)
    (h : (ShortComplex.mk (d (n + 1)) (d n) (zero n)).Exact) :
    (ChainComplex.of X d zero).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  exact (ShortComplex.exact_iff_of_iso
    (S₁ := (ChainComplex.of X d zero).sc' (n + 1 + 1) (n + 1) n)
    (S₂ := ShortComplex.mk (d (n + 1)) (d n) (zero n))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa only [HomologicalComplex.shortComplexFunctor'_obj_f, Iso.refl_hom,
        Category.id_comp, Category.comp_id] using (ChainComplex.of_d X d (n + 1)).symm)
      (by simp))).2 h

/-- Exactness of the specified augmentation pair gives exactness at the augmentation of
`ChainComplex.of`. -/
theorem of_exact_d_one_zero (X : ℕ → C) (d : ∀ n, X (n + 1) ⟶ X n)
    (zero : ∀ n, d (n + 1) ≫ d n = 0) {Y : C} (ε : X 0 ⟶ Y)
    (hε : d 0 ≫ ε = 0) {hε' : (ChainComplex.of X d zero).d 1 0 ≫ ε = 0}
    (h : (ShortComplex.mk (d 0) ε hε).Exact) :
    (ShortComplex.mk ((ChainComplex.of X d zero).d 1 0) ε hε').Exact := by
  exact (ShortComplex.exact_iff_of_iso
    (S₁ := ShortComplex.mk ((ChainComplex.of X d zero).d 1 0) ε _)
    (S₂ := ShortComplex.mk (d 0) ε hε)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using (ChainComplex.of_d X d 0).symm) (by simp))).2 h

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {X : C}

/-- **An augmentation which is exact in every degree is a quasi-isomorphism.** If a complex `K`
is exact in positive degrees and its augmentation `ε : K.X 0 ⟶ X` is an epimorphism exact at
`K.X 0`, then the induced map from `K` to `X` placed in degree `0` is a quasi-isomorphism. No
projectivity is needed. -/
lemma quasiIso_toSingle₀Equiv_symm (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X)
    (hε : K.d 1 0 ≫ ε = 0) [Epi ε] (h₀ : (ShortComplex.mk (K.d 1 0) ε hε).Exact)
    (h : ∀ n, K.ExactAt (n + 1)) : QuasiIso ((ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩) :=
  ⟨fun n => by
    cases n with
    | zero =>
      have hπ := ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := K) ε hε
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp) rfl rfl]
      refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (S₂ := ShortComplex.mk _ _ hε) ?_).2 ⟨h₀, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp [hπ])
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      exact h n⟩

/-! ### Splicing short exact sequences

Let `X` be a complex whose differentials factor as `X.X (p + 1) ⟶ A (p + 1) ⟶ X.X p` through
short exact sequences `0 ⟶ A (p + 1) ⟶ X.X p ⟶ A p ⟶ 0`. Then `X` is exact in positive degrees
and its augmentation `X.X 0 ⟶ A 0` is exact, so `X` resolves `A 0`; when its terms are
projective it is a projective resolution. -/

section Splice

variable {K : ChainComplex C ℕ} {A : ℕ → C}
  (ι : ∀ p, A (p + 1) ⟶ K.X p) (ε : ∀ p, K.X p ⟶ A p) (w : ∀ p, ι p ≫ ε p = 0)
  (hS : ∀ p, (ShortComplex.mk _ _ (w p)).ShortExact) (hd : ∀ p, K.d (p + 1) p = ε (p + 1) ≫ ι p)

include hS hd

omit hS in
include w in
/-- The augmentation of a complex spliced from short exact sequences vanishes on boundaries. -/
lemma d_one_zero_comp_of_shortExact : K.d 1 0 ≫ ε 0 = 0 := by
  rw [hd, Category.assoc, w, comp_zero]

/-- A complex spliced from short exact sequences is exact at its augmentation. -/
lemma exact_d_one_zero_of_shortExact :
    (ShortComplex.mk (K.d 1 0) (ε 0) (d_one_zero_comp_of_shortExact ι ε w hd)).Exact := by
  have : Epi (ε 1) := (hS 1).epi_g
  exact ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono _ (ε 1) (ι 0) (ε 0) (𝟙 _)
    (hd 0) (Category.comp_id _).symm (w 0) (hS 0).exact

/-- A complex spliced from short exact sequences is exact in positive degrees. -/
lemma exactAt_succ_of_shortExact (n : ℕ) : K.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  have : Epi (ε (n + 2)) := (hS (n + 2)).epi_g
  have : Mono (ι n) := (hS n).mono_f
  exact ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono _ (ε (n + 2)) (ι (n + 1))
    (ε (n + 1)) (ι n) (hd _) (hd _) (w (n + 1)) (hS (n + 1)).exact

/-- The augmentation of a complex spliced from short exact sequences is a quasi-isomorphism. -/
lemma quasiIso_toSingle₀Equiv_symm_of_shortExact :
    QuasiIso ((ChainComplex.toSingle₀Equiv K (A 0)).symm
      ⟨ε 0, d_one_zero_comp_of_shortExact ι ε w hd⟩) :=
  have : Epi (ε 0) := (hS 0).epi_g
  quasiIso_toSingle₀Equiv_symm K (ε 0) _ (exact_d_one_zero_of_shortExact ι ε w hS hd)
    (exactAt_succ_of_shortExact ι ε w hS hd)

end Splice

end Abelian

end ChainComplex
