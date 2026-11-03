/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Resolution.ChainComplex

/-!
# Finite resolutions from bounded exact complexes

A finite `P`-resolution of `X` in an exact category is recorded recursively, as a chain of
conflations

```text
K₁ ↪ Q₀ ↠ X,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁,
```

and `TauCeti.ExactStructure.FiniteResolution.toChainComplex` splices such a chain into a bounded
augmented chain complex. This file goes the other way for the canonical exact structure of an
abelian category. Let `K` be a chain complex with an augmentation `ε : K₀ ⟶ X` such that

```text
0 = Kₙ₊₁ ⟶ Kₙ ⟶ ⋯ ⟶ K₁ ⟶ K₀ ⟶ X ⟶ 0
```

is exact and every `Kᵢ` with `i ≤ n` satisfies `P`. Cutting it at the kernels
`Zᵢ₊₁ = ker (Kᵢ ⟶ Zᵢ)`, starting from `Z₀ = X`, gives short exact sequences
`Zᵢ₊₁ ↪ Kᵢ ↠ Zᵢ`, and `Kₙ ⟶ Zₙ` is an isomorphism, so `Zₙ` satisfies `P` once `P` is closed
under isomorphisms. The result is a finite `P`-resolution of `X` of length `n`.

When `K` vanishes in all degrees above `n`, the complex of this resolution is isomorphic to `K`,
compatibly with the augmentations, so passing from the complex to the recursive presentation loses
nothing. Alternating sums along the resolution are alternating sums of the terms `K₀, …, Kₙ`.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.ofChainComplex`: the finite resolution obtained from an
  augmented complex exact in degrees `0, …, n` with `Kₙ₊₁ = 0`.
* `TauCeti.ExactStructure.FiniteResolution.toChainComplexOfChainComplexIso`: the complex of that
  resolution is the original complex, when the latter vanishes above the length.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.length_ofChainComplex`: the resolution has length `n`.
* `TauCeti.ExactStructure.FiniteResolution.toChainComplexOfChainComplexIso_hom_f_zero_comp`:
  the identification of complexes carries the augmentation of the resolution to `ε`.
* `TauCeti.ExactStructure.FiniteResolution.foldAlternating_ofChainComplex`: an alternating fold
  along the resolution is the alternating sum over the terms `K₀, …, Kₙ`.

## Implementation notes

The kernels `Zᵢ` are built by recursion from `Z₀ = X`, each together with the map `Kᵢ ⟶ Zᵢ`
induced by the differential, so that no exactness is needed to define them. This recursion is
reducible, so that `Z₀` is `X` up to reducible unfolding and the resolution of `Z₀` built below is
literally a resolution of `X` for `rw` and `simp`. The resolution
itself is assembled by a recursion on the number of remaining conflations, starting from the
deep end `Zₙ`, as `TauCeti.ExactStructure.FiniteResolution` is. Only the exactness of the complex
in degrees `0, …, n` and the vanishing of `Kₙ₊₁` are used; the terms above `n + 1` are
irrelevant to the construction.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 10,
  for acyclic complexes as complexes spliced from conflations, and Section 12 for resolutions.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti.ExactStructure.FiniteResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}
  {X : C} {K : ChainComplex C ℕ} {ε : K.X 0 ⟶ X} {hε : K.d 1 0 ≫ ε = 0}

section Syzygy

variable (K ε hε)

/-- The kernels `Zᵢ` cutting an augmented complex into short complexes, each together with the
map `Kᵢ ⟶ Zᵢ` induced by the differential and the fact that it kills the incoming
differential: `Z₀ = X` with the augmentation, and `Zᵢ₊₁` is the kernel of `Kᵢ ⟶ Zᵢ`. -/
@[reducible] private noncomputable def stage :
    (i : ℕ) → (Z : C) × {g : K.X i ⟶ Z // K.d (i + 1) i ≫ g = 0}
  | 0 => ⟨X, ε, hε⟩
  | i + 1 => ⟨kernel (stage i).2.1, kernel.lift _ (K.d (i + 1) i) (stage i).2.2, by
      ext
      simp⟩

/-- The `i`-th kernel `Zᵢ` of the augmented complex. -/
@[reducible] private noncomputable def syz (i : ℕ) : C := (stage K ε hε i).1

/-- The map `Kᵢ ⟶ Zᵢ` induced by the differential, or by the augmentation for `i = 0`. -/
private noncomputable def syzπ (i : ℕ) : K.X i ⟶ syz K ε hε i := (stage K ε hε i).2.1

private theorem syzπ_zero : syzπ K ε hε 0 = ε := rfl

private theorem d_comp_syzπ (i : ℕ) : K.d (i + 1) i ≫ syzπ K ε hε i = 0 :=
  (stage K ε hε i).2.2

/-- The inclusion `Zᵢ₊₁ ↪ Kᵢ` of the kernel of `Kᵢ ⟶ Zᵢ`. -/
private noncomputable def syzι (i : ℕ) : syz K ε hε (i + 1) ⟶ K.X i :=
  kernel.ι (syzπ K ε hε i)

private instance mono_syzι (i : ℕ) : Mono (syzι K ε hε i) :=
  inferInstanceAs (Mono (kernel.ι (syzπ K ε hε i)))

private theorem syzι_comp_syzπ (i : ℕ) : syzι K ε hε i ≫ syzπ K ε hε i = 0 :=
  kernel.condition _

private theorem syzπ_succ_comp_syzι (i : ℕ) :
    syzπ K ε hε (i + 1) ≫ syzι K ε hε i = K.d (i + 1) i :=
  kernel.lift_ι _ _ _

end Syzygy

section Exactness

variable {n : ℕ}
  (h₀ : (ShortComplex.mk (K.d 1 0) ε hε).Exact)
  (hK : ∀ i < n, (ShortComplex.mk (K.d (i + 2) (i + 1)) (K.d (i + 1) i)
    (K.d_comp_d _ _ _)).Exact)
  (hn : IsZero (K.X (n + 1)))

include h₀ hK in
/-- The differential into `Kᵢ` and the map `Kᵢ ⟶ Zᵢ` form an exact sequence, in the degrees where
the complex is exact. -/
private theorem exact_syzπ {i : ℕ} (hi : i ≤ n) :
    (ShortComplex.mk (K.d (i + 1) i) (syzπ K ε hε i) (d_comp_syzπ K ε hε i)).Exact := by
  cases i with
  | zero => exact h₀
  | succ i =>
    -- Postcomposing `Kᵢ₊₁ ⟶ Zᵢ₊₁` with the monomorphism `Zᵢ₊₁ ↪ Kᵢ` gives the differential.
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk _ (syzπ K ε hε (i + 1)) (d_comp_syzπ K ε hε (i + 1)))
      (S₂ := ShortComplex.mk _ _ (K.d_comp_d (i + 2) (i + 1) i))
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := syzι K ε hε i
        comm₂₃ := by rw [Category.id_comp, syzπ_succ_comp_syzι] }).2 (hK i (by omega))

include h₀ hK in
/-- The map `Kᵢ ⟶ Zᵢ` is an epimorphism in the degrees where the complex is exact. -/
private theorem epi_syzπ [Epi ε] {i : ℕ} (hi : i ≤ n) : Epi (syzπ K ε hε i) := by
  cases i with
  | zero => exact (inferInstance : Epi ε)
  | succ i => exact (exact_syzπ h₀ hK (i := i) (by omega)).epi_kernelLift

include h₀ hK hn in
/-- The last map `Kₙ ⟶ Zₙ` is an isomorphism, because `Kₙ₊₁` vanishes. -/
private theorem isIso_syzπ [Epi ε] : IsIso (syzπ K ε hε n) := by
  have := epi_syzπ h₀ hK (le_refl n)
  have := (exact_syzπ h₀ hK (le_refl n)).mono_g (hn.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

include h₀ hK in
/-- Below the length, `Zᵢ₊₁ ↪ Kᵢ ↠ Zᵢ` is a short exact sequence. -/
private theorem conflation_syz [Epi ε] {i : ℕ} (hi : i < n) :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk (syzι K ε hε i) (syzπ K ε hε i) (syzι_comp_syzπ K ε hε i)) := by
  have := epi_syzπ h₀ hK hi.le
  exact abelian_conflation_of_epi (syzπ K ε hε i)

variable [Epi ε] [P.IsClosedUnderIsomorphisms] (hP : ∀ i ≤ n, P (K.X i))

/-- The resolution of `Zᵢ` by the `m` remaining short exact sequences `Zⱼ₊₁ ↪ Kⱼ ↠ Zⱼ`,
`i ≤ j < n`, ending at `Zₙ ≅ Kₙ`. -/
private noncomputable def go :
    (m i : ℕ) → i + m = n → (ExactStructure.abelian C).FiniteResolution P (syz K ε hε i)
  | 0, i, h => base (by
      obtain rfl : i = n := h
      have := isIso_syzπ h₀ hK hn
      exact P.prop_of_iso (asIso (syzπ K ε hε i)) (hP i le_rfl))
  | m + 1, i, h => step (hP i (by omega)) (syzι K ε hε i) (syzπ K ε hε i)
      (syzι_comp_syzπ K ε hε i) (conflation_syz h₀ hK (by omega)) (go m (i + 1) (by omega))

/-- **The finite resolution of a bounded exact augmented complex.** If
`0 ⟶ Kₙ ⟶ ⋯ ⟶ K₀ ⟶ X ⟶ 0` is exact, with `Kₙ₊₁ = 0` and every `Kᵢ` for `i ≤ n` satisfying `P`,
then cutting it at the kernels of its maps gives a finite `P`-resolution of `X` for the
canonical exact structure, of length `n`. -/
noncomputable def ofChainComplex : (ExactStructure.abelian C).FiniteResolution P X :=
  go h₀ hK hn hP n 0 (zero_add n)

private theorem length_go (m i : ℕ) (h : i + m = n) : (go h₀ hK hn hP m i h).length = m := by
  induction m generalizing i with
  | zero => rw [go, length_base]
  | succ m ih => rw [go, length_step, ih]

/-- The resolution of an exact augmented complex with `Kₙ₊₁ = 0` has length `n`, the truncation
degree; the terms of the complex above `n + 1` play no role. -/
@[simp]
theorem length_ofChainComplex : (ofChainComplex h₀ hK hn hP).length = n :=
  length_go h₀ hK hn hP n 0 (zero_add n)

private theorem foldAlternating_go {A : Type*} [AddCommGroup A] (f : ∀ Z : C, P Z → A)
    (hf : ∀ {Y Z : C} (_ : Y ≅ Z) (hY : P Y) (hZ : P Z), f Y hY = f Z hZ)
    (m i : ℕ) (h : i + m = n) :
    (go h₀ hK hn hP m i h).foldAlternating f =
      ∑ j : Fin (m + 1),
        (-1 : ℤ) ^ (j : ℕ) • f (K.X (i + j)) (hP _ (by have := j.isLt; omega)) := by
  induction m generalizing i with
  | zero =>
    obtain rfl : i = n := h
    have := isIso_syzπ h₀ hK hn
    rw [go, foldAlternating_base, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simpa using hf (asIso (syzπ K ε hε i)).symm _ _
  | succ m ih =>
    rw [go, foldAlternating_step, ih, Fin.sum_univ_succ (n := m + 1), sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, neg_inj]
      congr 3
      omega

/-- **Alternating sums along the resolution of a bounded exact complex** are the alternating sums
`f K₀ - f K₁ + ⋯ + (-1)ⁿ f Kₙ` over the terms of the complex, for any `f` invariant under
isomorphism. -/
theorem foldAlternating_ofChainComplex {A : Type*} [AddCommGroup A] (f : ∀ Z : C, P Z → A)
    (hf : ∀ {Y Z : C} (_ : Y ≅ Z) (hY : P Y) (hZ : P Z), f Y hY = f Z hZ) :
    (ofChainComplex h₀ hK hn hP).foldAlternating f =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (K.X i) (hP i (Nat.le_of_lt_succ i.isLt)) := by
  rw [ofChainComplex, foldAlternating_go h₀ hK hn hP f hf]
  simp only [zero_add]

section Complex

variable (hzero : ∀ i, n < i → IsZero (K.X i))

/-- The terms of the resolution of `Zᵢ` are the terms `Kᵢ₊ⱼ` of the complex: the identity below
the last syzygy, the inverse of `Kₙ ≅ Zₙ` at it, and the unique isomorphism of zero objects
beyond. -/
private noncomputable def goTermIso :
    (m i : ℕ) → (h : i + m = n) → (j : ℕ) → (go h₀ hK hn hP m i h).term j ≅ K.X (i + j)
  | 0, i, h, 0 =>
    haveI : IsIso (syzπ K ε hε i) := by
      obtain rfl : i = n := h
      exact isIso_syzπ h₀ hK hn
    (asIso (syzπ K ε hε i)).symm
  | 0, i, h, j + 1 => (isZero_zero C).iso (hzero _ (by omega))
  | m + 1, i, _, 0 => Iso.refl _
  | m + 1, i, h, j + 1 => goTermIso m (i + 1) (by omega) j ≪≫ K.XIsoOfEq (by omega)

private theorem goTermIso_hom_comp_syzπ (m i : ℕ) (h : i + m = n) :
    (goTermIso h₀ hK hn hP hzero m i h 0).hom ≫ syzπ K ε hε i = (go h₀ hK hn hP m i h).aug := by
  cases m with
  | zero => simp [goTermIso, go]
  | succ m => simp [goTermIso, go]

private theorem goTermIso_comm (m i : ℕ) (h : i + m = n) (j : ℕ) :
    (goTermIso h₀ hK hn hP hzero m i h (j + 1)).hom ≫ K.d (i + (j + 1)) (i + j) =
      (go h₀ hK hn hP m i h).d j ≫ (goTermIso h₀ hK hn hP hzero m i h j).hom := by
  induction m generalizing i j with
  | zero => exact (isZero_zero C).eq_of_src _ _
  | succ m ih =>
    cases j with
    | zero =>
      simp only [goTermIso, go, d_step_zero, Iso.trans_hom, Category.assoc,
        HomologicalComplex.XIsoOfEq_hom_comp_d, Iso.refl_hom, Category.comp_id]
      rw [← goTermIso_hom_comp_syzπ h₀ hK hn hP hzero m (i + 1) (by omega), Category.assoc,
        syzπ_succ_comp_syzι]
      -- The two sides differ only by the indices `i + 1 + 0` and `i + 0` of the differential.
      rfl
    | succ j =>
      simp only [goTermIso, go, d_step_succ, Iso.trans_hom, Category.assoc,
        HomologicalComplex.XIsoOfEq_hom_comp_d]
      rw [← HomologicalComplex.d_comp_XIsoOfEq_hom K (by omega : i + 1 + j = i + (j + 1)),
        ← Category.assoc, ih, Category.assoc]

/-- The terms of the resolution are the terms of the complex. -/
private noncomputable def termIso (j : ℕ) :
    (go h₀ hK hn hP n 0 (zero_add n)).term j ≅ K.X j :=
  goTermIso h₀ hK hn hP hzero n 0 (zero_add n) j ≪≫ K.XIsoOfEq (zero_add j)

private theorem termIso_comm (j : ℕ) :
    (termIso h₀ hK hn hP hzero (j + 1)).hom ≫ K.d (j + 1) j =
      (go h₀ hK hn hP n 0 (zero_add n)).toChainComplex.d (j + 1) j ≫
        (termIso h₀ hK hn hP hzero j).hom := by
  rw [toChainComplex_d]
  simp only [termIso, Iso.trans_hom, Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d]
  rw [← HomologicalComplex.d_comp_XIsoOfEq_hom K (zero_add j), ← Category.assoc,
    goTermIso_comm, Category.assoc]

private theorem termIso_hom_zero_comp :
    (termIso h₀ hK hn hP hzero 0).hom ≫ ε = (go h₀ hK hn hP n 0 (zero_add n)).aug := by
  rw [← goTermIso_hom_comp_syzπ h₀ hK hn hP hzero n 0 (zero_add n), termIso, Iso.trans_hom,
    Category.assoc, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, syzπ_zero]

/-- **The complex of the resolution of a bounded exact complex is that complex**, when it vanishes
in all degrees above the length: passing from the complex to the recursive presentation of the
resolution loses nothing. -/
noncomputable def toChainComplexOfChainComplexIso :
    (ofChainComplex h₀ hK (hzero _ n.lt_succ_self) hP).toChainComplex ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (termIso h₀ hK (hzero _ n.lt_succ_self) hP hzero) (by
    rintro _ j rfl
    exact termIso_comm h₀ hK (hzero _ n.lt_succ_self) hP hzero j)

/-- The identification of complexes carries the augmentation of the resolution to the
augmentation `ε` of the complex. -/
@[reassoc (attr := simp)]
theorem toChainComplexOfChainComplexIso_hom_f_zero_comp :
    (toChainComplexOfChainComplexIso h₀ hK hP hzero).hom.f 0 ≫ ε =
      (ofChainComplex h₀ hK (hzero _ n.lt_succ_self) hP).aug :=
  termIso_hom_zero_comp h₀ hK (hzero _ n.lt_succ_self) hP hzero

end Complex

end Exactness

end TauCeti.ExactStructure.FiniteResolution
