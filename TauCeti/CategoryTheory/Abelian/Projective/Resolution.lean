/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.ChainComplex.Exact

/-!
# Construction and comparison of projective resolutions

Mathlib compares two projective resolutions `P` and `Q` of the same object `X` by the lift of the
identity of `X` (`CategoryTheory.ProjectiveResolution.homotopyEquiv`), which it constructs
abstractly from the projectivity of the terms. Often one has an explicit chain map
`f : P.complex ⟶ Q.complex` instead, compatible with the augmentations. Such an `f` is itself a
lift of the identity of `X`, so it is homotopic to Mathlib's comparison
(`CategoryTheory.ProjectiveResolution.homotopyOfComm`) and is a homotopy equivalence
(`CategoryTheory.ProjectiveResolution.homotopyEquivOfComm`).

`ChainComplex.toProjectiveResolution` packages an augmented projective chain complex
which is exact in positive degrees and exact at its augmentation. Its quasi-isomorphism proof
is adapted from Mathlib's `CategoryTheory.ProjectiveResolution.of`, by Markus Himmel,
Kim Morrison, Jakob von Raumer and Joël Riou; the quasi-isomorphism itself, which needs no
projectivity, is `ChainComplex.quasiIso_toSingle₀Equiv_symm`.

A complex of projectives whose differentials factor through short exact sequences
`0 ⟶ A (p + 1) ⟶ K.X p ⟶ A p ⟶ 0` is a projective resolution of `A 0`
(`CategoryTheory.ProjectiveResolution.splice`), by the splicing lemmas of
`TauCeti.Algebra.Homology.ChainComplex.Exact`.
-/

public section

noncomputable section

namespace ChainComplex

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] {X : C}


/-- An augmented complex of projectives, exact in positive degrees and at its epimorphic
augmentation, is a projective resolution. -/
-- The body is exposed so the augmentation's domain in `toProjectiveResolution_π` is the
-- supplied complex.
@[expose]
def toProjectiveResolution (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X) (hε : K.d 1 0 ≫ ε = 0)
    (hP : ∀ n, Projective (K.X n)) [Epi ε]
    (h₀ : (ShortComplex.mk (K.d 1 0) ε hε).Exact)
    (h : ∀ n, K.ExactAt (n + 1)) : ProjectiveResolution X where
  complex := K
  projective := hP
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩
  quasiIso := quasiIso_toSingle₀Equiv_symm K ε hε h₀ h

/-- The exact-complex construction retains the given complex. -/
@[simp] theorem toProjectiveResolution_complex (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X) (hε)
    (hP : ∀ n, Projective (K.X n)) [Epi ε] (h₀) (h) :
    (K.toProjectiveResolution ε hε hP h₀ h).complex = K := (rfl)

/-- The exact-complex construction uses the chain map induced by the given augmentation. -/
@[simp] theorem toProjectiveResolution_π (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X) (hε)
    (hP : ∀ n, Projective (K.X n)) [Epi ε] (h₀) (h) :
    (K.toProjectiveResolution ε hε hP h₀ h).π =
      (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩ := (rfl)


end ChainComplex

namespace CategoryTheory.ProjectiveResolution

section Splice

variable {C : Type*} [Category* C] [Abelian C] {K : ChainComplex C ℕ} [∀ p, Projective (K.X p)]
  {A : ℕ → C} (ι : ∀ p, A (p + 1) ⟶ K.X p) (ε : ∀ p, K.X p ⟶ A p) (w : ∀ p, ι p ≫ ε p = 0)
  (hS : ∀ p, (ShortComplex.mk _ _ (w p)).ShortExact) (hd : ∀ p, K.d (p + 1) p = ε (p + 1) ≫ ι p)

/-- **Splicing short exact sequences into a projective resolution.** A complex of projectives
whose differentials factor as `K.X (p + 1) ⟶ A (p + 1) ⟶ K.X p` through short exact sequences
`0 ⟶ A (p + 1) ⟶ K.X p ⟶ A p ⟶ 0` is a projective resolution of `A 0`, with augmentation
`ε 0`. -/
-- The body is exposed so that the complex of the resolution is `K` itself.
@[expose]
def splice : ProjectiveResolution (A 0) :=
  have : Epi (ε 0) := (hS 0).epi_g
  K.toProjectiveResolution (ε 0) (ChainComplex.d_one_zero_comp_of_shortExact ι ε w hd)
    inferInstance (ChainComplex.exact_d_one_zero_of_shortExact ι ε w hS hd)
    (ChainComplex.exactAt_succ_of_shortExact ι ε w hS hd)

@[simp]
lemma splice_complex : (splice ι ε w hS hd).complex = K := (rfl)

@[simp]
lemma splice_π_f_zero : (splice ι ε w hS hd).π.f 0 = ε 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero (ε 0) _

end Splice


variable {C : Type*} [Category* C] [Abelian C] {X : C} (P Q : ProjectiveResolution X)
  (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π)

/-- A chain map between projective resolutions of `X` compatible with the augmentations is
homotopic to the comparison `(homotopyEquiv P Q).hom`, the lift of the identity of `X`. -/
def homotopyOfComm : Homotopy f (homotopyEquiv P Q).hom :=
  liftHomotopy (𝟙 X) _ _ (by simp [hf]) (by simp)

/-- A chain map between projective resolutions of `X` compatible with the augmentations is a
homotopy equivalence; its homotopy inverse is the lift of the identity of `X`. -/
def homotopyEquivOfComm : HomotopyEquiv P.complex Q.complex :=
  (homotopyEquiv P Q).copy (homotopyOfComm P Q f hf).symm

/-- The forward map of the homotopy equivalence is the given chain map. -/
@[simp]
theorem homotopyEquivOfComm_hom : (homotopyEquivOfComm P Q f hf).hom = f :=
  (rfl)

/-- The homotopy inverse is the lift of the identity from `Q` to `P`. -/
@[simp]
theorem homotopyEquivOfComm_inv : (homotopyEquivOfComm P Q f hf).inv = lift (𝟙 X) Q P :=
  (rfl)

end CategoryTheory.ProjectiveResolution
