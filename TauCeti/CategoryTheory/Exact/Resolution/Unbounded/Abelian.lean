/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.Unbounded.Basic
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.ChainComplex.Exact

/-!
# Relative projective resolutions in an abelian category

For the canonical exact structure of an abelian category, splicing a relative projective
resolution gives a projective resolution in Mathlib's sense. Thus constructions made from
conflations can use Mathlib's comparison and Ext APIs, without an enough-projectives assumption
on the entire category.

The exactness argument is the unbounded counterpart of
`TauCeti.ExactStructure.FiniteResolution.toProjectiveResolution`. The quasi-isomorphism
argument follows Mathlib's `CategoryTheory.ProjectiveResolution.of`, by Markus Himmel,
Kim Morrison, Jakob von Raumer and Joël Riou.

## References

* Theo Bühler, *Exact categories*, Section 12.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.2.
-/

public section

namespace TauCeti.ExactStructure.ProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  (r : (ExactStructure.abelian C).ProjectiveResolution)

/-- The syzygy deflations of a relative resolution are epimorphisms. -/
instance epi_π (n : ℕ) : Epi (r.π n) :=
  ((ExactStructure.abelian_conflation _).mp (r.conflation n)).epi_g

/-- The admissible kernel maps of a relative resolution are monomorphisms. -/
instance mono_ι (n : ℕ) : Mono (r.ι n) :=
  ((ExactStructure.abelian_conflation _).mp (r.conflation n)).mono_f

/-- The terms are projective in the ordinary abelian-category sense. -/
instance projective_X (n : ℕ) : Projective (r.X n) :=
  (ExactStructure.abelian_isProjective_iff _).mp (r.projective n)

/-- Splicing preserves exactness at each resolving term before its syzygy deflation. -/
theorem exact_d_π (n : ℕ) :
    (ShortComplex.mk (r.d n) (r.π n) (r.d_comp_π n)).Exact := by
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (r.d n) (r.π n) (r.d_comp_π n))
    (S₂ := ShortComplex.mk (r.ι n) (r.π n) (r.ι_π n))
    { τ₁ := r.π (n + 1), τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [d_def] }).2 ?_
  exact ((ExactStructure.abelian_conflation _).mp (r.conflation n)).exact

/-- The spliced complex is exact in every positive degree. -/
theorem exact_d_succ_d (n : ℕ) :
    (ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n)).Exact := by
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (r.d (n + 1)) (r.π (n + 1)) (r.d_comp_π (n + 1)))
    (S₂ := ShortComplex.mk (r.d (n + 1)) (r.d n) (r.d_comp_d n))
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := r.ι n, comm₂₃ := by simp [d_def] }).1
      (r.exact_d_π (n + 1))

/-- Exactness of the spliced complex, in the vocabulary of homological complexes. -/
theorem exactAt_complex_succ (n : ℕ) : r.complex.ExactAt (n + 1) :=
  ChainComplex.of_exactAt_succ r.X r.d r.d_comp_d n (r.exact_d_succ_d n)

/-- A relative projective resolution for the canonical abelian exact structure is a projective
resolution in Mathlib's sense, with the same spliced complex and augmentation. -/
-- Exposure identifies the domain of the augmentation in the dependent `π` lemma below.
@[expose]
noncomputable def toProjectiveResolution : CategoryTheory.ProjectiveResolution (r.Z 0) :=
  r.complex.toProjectiveResolution (r.π 0) r.complex_d_one_zero_comp_π r.projective_X
    (ChainComplex.of_exact_d_one_zero r.X r.d r.d_comp_d (r.π 0) (r.d_comp_π 0)
      (r.exact_d_π 0))
    r.exactAt_complex_succ

/-- The abelian realization retains the original spliced complex. -/
@[simp]
theorem toProjectiveResolution_complex : r.toProjectiveResolution.complex = r.complex := (rfl)

/-- The abelian realization retains the original augmentation. -/
@[simp]
theorem toProjectiveResolution_π : r.toProjectiveResolution.π = r.augmentation := by
  simp only [toProjectiveResolution, ChainComplex.toProjectiveResolution_π]
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact r.augmentation_f_zero.symm

end TauCeti.ExactStructure.ProjectiveResolution
