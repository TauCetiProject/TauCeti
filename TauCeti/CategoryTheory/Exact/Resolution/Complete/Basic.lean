/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Splice
public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Complete resolutions

A complete resolution in an exact category is a bi-infinite sequence of conflations
`Zⁿ ↪ Xⁿ ↠ Zⁿ⁺¹`, indexed by `n : ℤ`, whose middle terms are projective-injective. Splicing the
conflations gives a cochain complex with differential `Xⁿ ↠ Zⁿ⁺¹ ↪ Xⁿ⁺¹`; it is acyclic in the
sense of the exact structure, and its object of cycles in degree zero is `Z⁰`.

In a Frobenius exact category every object has a complete resolution. Its conflations are
injective presentations in nonnegative degrees and projective presentations in negative degrees.
The interface retains the conflations, so an exact functor can transport the sequence before its
maps are spliced. Uniqueness up to homotopy is the comparison theorem in
`TauCeti.CategoryTheory.Exact.Resolution.Complete.Comparison`.

## Main definitions

* `TauCeti.ExactStructure.CompleteResolution`: a complete resolution, as the data of its
  conflations.
* `TauCeti.ExactStructure.CompleteResolution.complex`: the spliced cochain complex.
* `TauCeti.ExactStructure.IsFrobenius.completeResolution`: a complete resolution of an object of
  a Frobenius exact category, with `TauCeti.ExactStructure.IsFrobenius.completeResolutionIso`.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Theo Bühler, *Exact categories*, Sections 11–13.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

variable (E : ExactStructure C)

/-- A **complete resolution** in an exact category: a bi-infinite sequence of conflations
`Zⁿ ↪ Xⁿ ↠ Zⁿ⁺¹` whose middle terms are both relatively projective and relatively injective.
The spliced complex is `TauCeti.ExactStructure.CompleteResolution.complex`; it is a complete
resolution of the object of cycles `Z 0`. -/
structure CompleteResolution where
  /-- The object of cycles `Zⁿ` in degree `n`. -/
  Z : ℤ → C
  /-- The term `Xⁿ` of the complex in degree `n`. -/
  X : ℤ → C
  /-- The inflation `Zⁿ ↪ Xⁿ`. -/
  ι (n : ℤ) : Z n ⟶ X n
  /-- The deflation `Xⁿ ↠ Zⁿ⁺¹`. -/
  π (n : ℤ) : X n ⟶ Z (n + 1)
  ι_π (n : ℤ) : ι n ≫ π n = 0
  /-- The sequences `Zⁿ ↪ Xⁿ ↠ Zⁿ⁺¹` are conflations. -/
  conflation (n : ℤ) : E.Conflation (ShortComplex.mk (ι n) (π n) (ι_π n))
  /-- The terms are projective-injective. -/
  projectiveInjective (n : ℤ) : E.projectiveInjective (X n)

namespace CompleteResolution

attribute [reassoc (attr := simp)] ι_π

variable {E} (r : E.CompleteResolution)

theorem isProjective_X (n : ℤ) : E.isProjective (r.X n) :=
  ((E.projectiveInjective_iff _).mp (r.projectiveInjective n)).1

theorem isInjective_X (n : ℤ) : E.isInjective (r.X n) :=
  ((E.projectiveInjective_iff _).mp (r.projectiveInjective n)).2

theorem isInflation_ι (n : ℤ) : E.IsInflation (r.ι n) := E.isInflation_f (r.conflation n)

theorem isDeflation_π (n : ℤ) : E.IsDeflation (r.π n) := E.isDeflation_g (r.conflation n)

instance (n : ℤ) : Mono (r.ι n) := (E.isKernelCokernelPair _ (r.conflation n)).mono_f

instance (n : ℤ) : Epi (r.π n) := (E.isKernelCokernelPair _ (r.conflation n)).epi_g

/-- The differential `Xⁿ ↠ Zⁿ⁺¹ ↪ Xⁿ⁺¹` of the spliced complex. -/
noncomputable def d (n : ℤ) : r.X n ⟶ r.X (n + 1) := r.π n ≫ r.ι (n + 1)

theorem d_def (n : ℤ) : r.d n = r.π n ≫ r.ι (n + 1) := (rfl)

/-- The differential out of degree `-1`, whose target index `Int.negSucc 0 + 1` reduces to `0`. -/
theorem d_negSucc_zero : r.d (Int.negSucc 0) = r.π (Int.negSucc 0) ≫ r.ι 0 := (rfl)

@[reassoc (attr := simp)]
theorem ι_d (n : ℤ) : r.ι n ≫ r.d n = 0 := by simp [d_def]

@[reassoc (attr := simp)]
theorem d_π (n : ℤ) : r.d n ≫ r.π (n + 1) = 0 := by simp [d_def]

@[reassoc (attr := simp)]
theorem d_d (n : ℤ) : r.d n ≫ r.d (n + 1) = 0 := by simp [d_def]

/-- The `n`-th conflation `Zⁿ ↪ Xⁿ ↠ Zⁿ⁺¹` of a complete resolution, as a short complex. -/
abbrev shortComplex (n : ℤ) : ShortComplex C := ShortComplex.mk (r.ι n) (r.π n) (r.ι_π n)

/-- The cochain complex spliced from the conflations of a complete resolution, through
`CochainComplex.splice`: consecutive conflations share their end terms `Zⁿ⁺¹`, so the connecting
isomorphisms are identities. -/
noncomputable abbrev complex : CochainComplex C ℤ :=
  CochainComplex.splice r.shortComplex fun _ ↦ Iso.refl _

/-- The differential of the complex in consecutive degrees, in the form `rw` can use. It is not a
simp lemma: `simp` already reduces its left-hand side through `CochainComplex.of_d`. -/
theorem complex_d (n : ℤ) : r.complex.d n (n + 1) = r.d n := by
  rw [CochainComplex.splice_d, Iso.refl_hom, Category.id_comp, d_def]

/-- The differential of the complex out of degree `-1`, whose target index is not syntactically
of the form `n + 1`. -/
theorem complex_d_negSucc_zero : r.complex.d (Int.negSucc 0) 0 = r.d (Int.negSucc 0) :=
  r.complex_d _

/-- A map of the spliced complexes commutes with the differentials of the resolutions. -/
@[reassoc]
theorem f_comp_d {r' : E.CompleteResolution} (φ : r.complex ⟶ r'.complex) (n : ℤ) :
    φ.f n ≫ r'.d n = r.d n ≫ φ.f (n + 1) := by
  rw [← complex_d, ← complex_d]
  exact φ.comm n (n + 1)

/-- The `n`-th conflation as an injective presentation of the cycles `Zⁿ`. -/
abbrev injectivePresentation (n : ℤ) : E.InjectivePresentation (r.Z n) where
  I := r.X n
  K := r.Z (n + 1)
  i := r.ι n
  p := r.π n
  zero := r.ι_π n
  conflation := r.conflation n
  isInjective := r.isInjective_X n

/-- The `n`-th conflation as a projective presentation of the cycles `Zⁿ⁺¹`. -/
abbrev projectivePresentation (n : ℤ) : E.ProjectivePresentation (r.Z (n + 1)) where
  K := r.Z n
  P := r.X n
  i := r.ι n
  p := r.π n
  zero := r.ι_π n
  conflation := r.conflation n
  isProjective := r.isProjective_X n

/-- The morphism into the cycles `Zⁿ` induced by a morphism into `Xⁿ` killed by `Xⁿ ↠ Zⁿ⁺¹`. -/
noncomputable def liftZ {A : C} (n : ℤ) (k : A ⟶ r.X n) (hk : k ≫ r.π n = 0) : A ⟶ r.Z n :=
  (E.isKernelCokernelPair _ (r.conflation n)).lift k hk

@[reassoc (attr := simp)]
theorem liftZ_ι {A : C} (n : ℤ) (k : A ⟶ r.X n) (hk : k ≫ r.π n = 0) :
    r.liftZ n k hk ≫ r.ι n = k :=
  (E.isKernelCokernelPair _ (r.conflation n)).lift_f k hk

/-- The morphism out of the cycles `Zⁿ⁺¹` induced by a morphism out of `Xⁿ` killing `Zⁿ ↪ Xⁿ`. -/
noncomputable def descZ {A : C} (n : ℤ) (k : r.X n ⟶ A) (hk : r.ι n ≫ k = 0) : r.Z (n + 1) ⟶ A :=
  (E.isKernelCokernelPair _ (r.conflation n)).desc k hk

@[reassoc (attr := simp)]
theorem π_descZ {A : C} (n : ℤ) (k : r.X n ⟶ A) (hk : r.ι n ≫ k = 0) :
    r.π n ≫ r.descZ n k hk = k :=
  (E.isKernelCokernelPair _ (r.conflation n)).g_desc k hk

end CompleteResolution

namespace IsFrobenius

variable {E} (hE : E.IsFrobenius)

private noncomputable def cosyzygy (X : C) : ℕ → C
  | 0 => X
  | n + 1 => (hE.enoughInjectives.injectivePresentation (cosyzygy X n)).K

private noncomputable def syzygy (X : C) : ℕ → C
  | 0 => X
  | n + 1 => (hE.enoughProjectives.projectivePresentation (syzygy X n)).K

private noncomputable def positiveConflation (X : C) (n : ℕ) : ShortComplex C :=
  let P := hE.enoughInjectives.injectivePresentation (cosyzygy hE X n)
  ShortComplex.mk P.i P.p P.zero

private noncomputable def negativeConflation (X : C) (n : ℕ) : ShortComplex C :=
  let P := hE.enoughProjectives.projectivePresentation (syzygy hE X n)
  ShortComplex.mk P.i P.p P.zero

private noncomputable def conflationSequence (X : C) : ℤ → ShortComplex C
  | .ofNat n => positiveConflation hE X n
  | .negSucc n => negativeConflation hE X n

/-- The cokernel of each conflation of the sequence is the kernel of the next one. In each case
the two objects are the same syzygy or cosyzygy, so the isomorphism is an identity. -/
private noncomputable def conflationSequenceIso (X : C) :
    ∀ n, (conflationSequence hE X n).X₃ ≅ (conflationSequence hE X (n + 1)).X₁
  | .ofNat _ => Iso.refl _
  | .negSucc 0 => Iso.refl _
  | .negSucc (_ + 1) => Iso.refl _

private theorem conflation_conflationSequence (X : C) (n : ℤ) :
    E.Conflation (conflationSequence hE X n) := by
  cases n with
  | ofNat n => exact (hE.enoughInjectives.injectivePresentation _).conflation
  | negSucc n => exact (hE.enoughProjectives.projectivePresentation _).conflation

private theorem isProjective_conflationSequence (X : C) (n : ℤ) :
    E.isProjective (conflationSequence hE X n).X₂ := by
  cases n with
  | ofNat n => exact hE.isProjective_I (hE.enoughInjectives.injectivePresentation _)
  | negSucc n => exact (hE.enoughProjectives.projectivePresentation _).isProjective

/-- A complete resolution of an object of a Frobenius exact category, spliced from injective
presentations in nonnegative degrees and projective presentations in negative degrees. Its object
of cycles in degree zero is the given object, by
`TauCeti.ExactStructure.IsFrobenius.completeResolutionIso`. -/
noncomputable def completeResolution (X : C) : E.CompleteResolution where
  Z n := (conflationSequence hE X n).X₁
  X n := (conflationSequence hE X n).X₂
  ι n := (conflationSequence hE X n).f
  π n := (conflationSequence hE X n).g ≫ (conflationSequenceIso hE X n).hom
  ι_π n := by simp
  conflation n := E.conflation_of_iso
    (ShortComplex.isoMk (S₁ := conflationSequence hE X n) (S₂ := ShortComplex.mk _ _ _)
      (Iso.refl _) (Iso.refl _) (conflationSequenceIso hE X n) (by simp) (by simp))
    (conflation_conflationSequence hE X n)
  projectiveInjective n := (E.projectiveInjective_iff _).mpr
    ⟨isProjective_conflationSequence hE X n,
      (hE.injective_iff_projective _).mpr (isProjective_conflationSequence hE X n)⟩

/-- The object of cycles in degree zero of `TauCeti.ExactStructure.IsFrobenius.completeResolution`
is the given object. -/
noncomputable def completeResolutionIso (X : C) : (hE.completeResolution X).Z 0 ≅ X :=
  Iso.refl X

end IsFrobenius

end TauCeti.ExactStructure
