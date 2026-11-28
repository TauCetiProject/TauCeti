/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.CategoryTheory.Injective.Envelope
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Minimal injective resolutions

An injective resolution is minimal when its cycles are essential in the corresponding injective
terms. If every object in a class has an injective envelope whose target and cokernel lie in the
class, every object in the class has a minimal injective resolution with all its terms in the
class. This applies, in particular, to finitely generated modules over an Artin algebra. The
construction iterates the same injective-envelope step as
`CategoryTheory.ComposableArrows.exists_isMinimalInjectiveCoresolution` for finite coresolutions.
The complex, its exactness, and the quasi-isomorphism proof adapt Mathlib's
`CategoryTheory.InjectiveResolution.of` from `Mathlib.CategoryTheory.Abelian.Injective.Resolution`,
using chosen injective envelopes in place of `Injective.under`.

For the use of minimal injective resolutions in dominant dimension, see Auslander, Reiten and
Smalø, *Representation Theory of Artin Algebras*, §VI.5, p. 211.
-/

public section

open CategoryTheory Limits TauCeti

namespace CategoryTheory.InjectiveResolution

universe v u

variable {C : Type u} [Category.{v} C]

section HasKernels

variable [HasZeroObject C] [HasZeroMorphisms C] [HasKernels C]

/-- An injective resolution is minimal if the inclusion of the cycles in each degree is an
essential monomorphism. -/
def IsMinimal {X : C} (I : InjectiveResolution X) : Prop :=
  ∀ n : ℕ, IsEssentialMono (kernel.ι (I.cocomplex.d n (n + 1)))

/-- Minimality is equivalent to essentiality of every cycle inclusion. -/
theorem isMinimal_iff {X : C} {I : InjectiveResolution X} :
    I.IsMinimal ↔ ∀ n : ℕ, IsEssentialMono (kernel.ι (I.cocomplex.d n (n + 1))) :=
  (Iff.rfl)

end HasKernels

variable [Abelian C]

/-- The coaugmentation of a minimal injective resolution is an essential monomorphism. -/
theorem IsMinimal.isEssentialMono_ι₀ {X : C} {I : InjectiveResolution X} (h : I.IsMinimal) :
    IsEssentialMono I.ι₀ :=
  (I.exact_ι₀.fIsKernel.isEssentialMono_kernel_ι_iff).1 (h 0)

section Construction

open CochainComplex

variable {Q : ObjectProperty C}
variable (hQ : ∀ X, Q X → ∃ (J : C) (ι : X ⟶ J), Injective J ∧ IsEssentialMono ι ∧
  Q J ∧ Q (cokernel ι))

/-- Choose the next injective envelope and record that both its target and cokernel stay in the
given class. -/
private noncomputable def envelope (X : Subtype Q) :
    {P : InjectivePresentation X.val // IsEssentialMono P.f ∧ Q P.J ∧ Q (cokernel P.f)} := by
  apply Classical.choice
  obtain ⟨J, ι, hJ, hι, hQJ, hQc⟩ := hQ X.val X.property
  exact ⟨⟨⟨J, hJ, ι, hι.mono⟩, hι, hQJ, hQc⟩⟩

/-- Successive cokernels of the chosen injective envelopes, starting at the resolved object. -/
private noncomputable abbrev cosyzygy (X : Subtype Q) : ℕ → Subtype Q
  | 0 => X
  | n + 1 => ⟨cokernel (envelope hQ (cosyzygy X n)).val.f,
      (envelope hQ (cosyzygy X n)).property.2.2⟩

variable (X : Subtype Q)

private noncomputable abbrev presentation (n : ℕ) :
    InjectivePresentation (cosyzygy hQ X n).val :=
  (envelope hQ (cosyzygy hQ X n)).val

private noncomputable def differential (n : ℕ) :
    (presentation hQ X n).J ⟶ (presentation hQ X (n + 1)).J :=
  cokernel.π (presentation hQ X n).f ≫ (presentation hQ X (n + 1)).f

private theorem presentation_comp_differential (n : ℕ) :
    (presentation hQ X n).f ≫ differential hQ X n = 0 := by
  simpa only [differential, zero_comp] using
    cokernel.condition_assoc (presentation hQ X n).f (presentation hQ X (n + 1)).f

private theorem differential_comp_differential (n : ℕ) :
    differential hQ X n ≫ differential hQ X (n + 1) = 0 := by
  simp only [differential, Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]

private noncomputable abbrev cochainComplex : CochainComplex C ℕ :=
  CochainComplex.of (fun n ↦ (presentation hQ X n).J) (differential hQ X)
    (differential_comp_differential hQ X)

private theorem cochainComplex_d (n : ℕ) :
    (cochainComplex hQ X).d n (n + 1) = differential hQ X n :=
  CochainComplex.of_d (fun i ↦ (presentation hQ X i).J) (differential hQ X) n

/-- Each chosen embedding identifies its source with the cycles in its degree. -/
private noncomputable def presentationIsKernel (n : ℕ)
    {d : (presentation hQ X n).J ⟶ (presentation hQ X (n + 1)).J}
    (hd : d = differential hQ X n) :
    IsLimit (KernelFork.ofι (presentation hQ X n).f
      (hd.symm ▸ presentation_comp_differential hQ X n)) :=
  isKernelCompMono (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel
    (presentation hQ X n).f)) (presentation hQ X (n + 1)).f hd

private theorem exactAt_succ (n : ℕ) : (cochainComplex hQ X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  -- Factor each differential through the adjacent cokernel projection and envelope.
  let p := presentation hQ X (n + 1)
  have h := ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono
    (differential_comp_differential hQ X n) (cokernel.π (presentation hQ X n).f) p.f
    (cokernel.π p.f) (presentation hQ X (n + 2)).f rfl rfl (cokernel.condition p.f)
    (ShortComplex.exact_cokernel p.f)
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    CochainComplex.of_d] using h

private noncomputable def augmentation :
    (single₀ C).obj X.val ⟶ cochainComplex hQ X :=
  (fromSingle₀Equiv _ _).symm ⟨(presentation hQ X 0).f, by
    rw [cochainComplex_d, presentation_comp_differential]⟩

private theorem quasiIso_augmentation : QuasiIso (augmentation hQ X) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have h := ShortComplex.exact_of_f_is_kernel
        (ShortComplex.mk _ _ (presentation_comp_differential hQ X 0))
        (presentationIsKernel hQ X 0 rfl)
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h, (presentation hQ X 0).mono⟩
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · simpa [augmentation] using
          (fromSingle₀Equiv_symm_apply_f_zero (C := cochainComplex hQ X)
            (presentation hQ X 0).f _).symm
      · simpa using (cochainComplex_d hQ X 0).symm
    · rfl
    · rfl
    · rfl
  | succ n =>
    exact (quasiIsoAt_iff_exactAt _ _ (exactAt_succ_single_obj _ n)).2 (exactAt_succ hQ X n)

include hQ in
/-- Repeated injective envelopes give a minimal injective resolution whose terms lie in the
given class, provided every object in the class has an envelope with target and cokernel in the
class. -/
theorem _root_.TauCeti.exists_isMinimal_injectiveResolution {Y : C} (hY : Q Y) :
    ∃ I : InjectiveResolution Y, I.IsMinimal ∧ ∀ n, Q (I.cocomplex.X n) := by
  let X : Subtype Q := ⟨Y, hY⟩
  let I : InjectiveResolution Y :=
    { cocomplex := cochainComplex hQ X
      injective := fun n ↦ (presentation hQ X n).injective
      ι := augmentation hQ X
      quasiIso := quasiIso_augmentation hQ X }
  refine ⟨I, fun n ↦ ?_, fun n ↦ (envelope hQ (cosyzygy hQ X n)).property.2.1⟩
  exact ((presentationIsKernel hQ X n (cochainComplex_d hQ X n)).isEssentialMono_kernel_ι_iff).2
    (envelope hQ (cosyzygy hQ X n)).property.1

end Construction

end CategoryTheory.InjectiveResolution
