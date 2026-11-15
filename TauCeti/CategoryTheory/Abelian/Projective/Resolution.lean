/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

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
Kim Morrison, Jakob von Raumer and Joël Riou.

Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₂` projective, prepending `X₂` to a
projective resolution of `X₁` yields a projective resolution of `X₃`
(`CategoryTheory.ShortComplex.ShortExact.augmentProjectiveResolution`), which shifts the degree of
any left derived functor along the sequence.
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
  quasiIso := ⟨fun n => by
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

namespace CategoryTheory.ShortComplex.ShortExact

open Limits

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C}

/-- Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₂` projective and a projective
resolution `P` of `X₁`, prepending `X₂` in degree zero gives a projective resolution of `X₃`. -/
def augmentProjectiveResolution (hS : S.ShortExact) [Projective S.X₂]
    (P : ProjectiveResolution S.X₁) : ProjectiveResolution S.X₃ :=
  let π₀ := P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom
  let p := π₀ ≫ S.f
  have hp : P.complex.d 1 0 ≫ p = 0 := by
    rw [← Category.assoc, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp, zero_comp]
  let K := P.complex.augment p hp
  have hg : K.d 1 0 ≫ S.g = 0 :=
    (Category.assoc π₀ S.f S.g).trans ((congrArg (π₀ ≫ ·) S.zero).trans comp_zero)
  @ChainComplex.toProjectiveResolution _ _ _ _ K S.g hg
    (fun
      | 0 => inferInstanceAs (Projective S.X₂)
      | n + 1 => P.projective n)
    hS.epi_g
    (by
      let φ : ShortComplex.mk (K.d 1 0) S.g hg ⟶ S :=
        { τ₁ := π₀
          τ₂ := 𝟙 S.X₂
          τ₃ := 𝟙 S.X₃
          comm₁₂ := (Category.comp_id _).symm
          comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
      have : Epi φ.τ₁ :=
        @epi_comp _ _ _ _ _ (P.π.f 0) (epi_of_isColimit_cofork P.isColimitCokernelCofork)
          (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom inferInstance
      have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
      have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 S.X₃))
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS.exact)
    (fun n ↦ by
      rw [HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)]
      cases n with
      | zero =>
        let φ : ShortComplex.mk (P.complex.d 1 0) (P.π.f 0) P.complex_d_comp_π_f_zero ⟶
            K.sc' 2 1 0 :=
          { τ₁ := 𝟙 (P.complex.X 1)
            τ₂ := 𝟙 (P.complex.X 0)
            τ₃ := (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom ≫ S.f
            comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
            comm₂₃ := (Category.id_comp _).trans (Category.assoc _ _ _) }
        have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (P.complex.X 1)))
        have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (P.complex.X 0)))
        have : Mono φ.τ₃ :=
          @mono_comp _ _ _ _ _ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom inferInstance
            S.f hS.mono_f
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 P.exact₀
      | succ n => exact P.exact_succ n)

/-- The underlying chain complex of `augmentProjectiveResolution` is `P.complex` augmented by
`S.X₂` along the resolution map followed by `S.f`. -/
@[simp]
theorem augmentProjectiveResolution_complex (hS : S.ShortExact) [Projective S.X₂]
    (P : ProjectiveResolution S.X₁) :
    (hS.augmentProjectiveResolution P).complex =
      P.complex.augment ((P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 S.X₁).hom) ≫ S.f)
        (by rw [← Category.assoc, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp,
          zero_comp]) :=
  (rfl)

end CategoryTheory.ShortComplex.ShortExact
