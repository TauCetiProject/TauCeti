/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

/-!
# Local properties of quadratic forms over number fields

This file defines isotropy, representation, scalar representation, and equivalence at every
finite and real place of a number field.  The predicates always use the canonical scalar
extensions of the global forms, so their witnesses compare actual localizations rather than an
independently chosen family of local quadratic spaces.

Global witnesses base-change to local witnesses.  The resulting API also records invariance
under global equivalence and the rank constraint imposed by local equivalence.  These are the
common hypotheses used in local-to-global statements for quadratic forms.

-/

-- Provenance: TauCetiRoadmap/GlobalQuadraticForms/README.md, Layer 0.2, and Suggested.lean.

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- A quadratic form over a number field is locally isotropic if it is isotropic at every finite
and real place. -/
def IsLocallyIsotropic (Q : _root_.QuadraticForm K V) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), ¬ (Q.atFinitePlace v).Anisotropic) ∧
    ∀ w : {w : InfinitePlace K // w.IsReal}, ¬ (Q.atRealPlace w).Anisotropic

/-- A quadratic form `Q` is locally represented by `R` if every finite and real localization of
`Q` admits an injective isometry into the corresponding localization of `R`. -/
def LocallyRepresents (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K),
      (Q.atFinitePlace v).IsRepresentedBy (R.atFinitePlace v)) ∧
    ∀ w : {w : InfinitePlace K // w.IsReal},
      (Q.atRealPlace w).IsRepresentedBy (R.atRealPlace w)

/-- A quadratic form locally represents a scalar if each finite and real localization represents
the image of that scalar. -/
def LocallyRepresentsScalar (Q : _root_.QuadraticForm K V) (a : K) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K),
      QuadraticMap.Represents (Q.atFinitePlace v)
        (algebraMap K (v.adicCompletion K) a)) ∧
    ∀ w : {w : InfinitePlace K // w.IsReal},
      QuadraticMap.Represents (Q.atRealPlace w) (embedding_of_isReal w.2 a)

/-- Two quadratic forms over a number field are locally equivalent if their localizations are
equivalent at every finite and real place. -/
def LocallyEquivalent (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K),
      (Q.atFinitePlace v).Equivalent (R.atFinitePlace v)) ∧
    ∀ w : {w : InfinitePlace K // w.IsReal},
      (Q.atRealPlace w).Equivalent (R.atRealPlace w)

/-- A globally isotropic quadratic form is locally isotropic. -/
theorem isLocallyIsotropic_of_not_anisotropic (Q : _root_.QuadraticForm K V)
    (hQ : ¬ Q.Anisotropic) : Q.IsLocallyIsotropic := by
  constructor
  · intro v
    rw [QuadraticForm.atFinitePlace_def]
    exact QuadraticForm.not_anisotropic_baseChange (A := v.adicCompletion K) hQ
  · intro w
    let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    rw [QuadraticForm.atRealPlace_def]
    exact QuadraticForm.not_anisotropic_baseChange (A := ℝ) hQ

/-- A global representation of one quadratic form by another induces a representation at every
finite and real place. -/
theorem LocallyRepresents.of_isRepresentedBy {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.IsRepresentedBy R) : Q.LocallyRepresents R := by
  constructor
  · intro v
    rw [QuadraticForm.atFinitePlace_def, QuadraticForm.atFinitePlace_def]
    exact h.baseChange (A := v.adicCompletion K)
  · intro w
    let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    rw [QuadraticForm.atRealPlace_def, QuadraticForm.atRealPlace_def]
    exact h.baseChange (A := ℝ)

/-- A globally represented scalar is represented at every finite and real place. -/
theorem LocallyRepresentsScalar.of_represents {Q : _root_.QuadraticForm K V} {a : K}
    (h : QuadraticMap.Represents Q a) : Q.LocallyRepresentsScalar a := by
  constructor
  · intro v
    rw [QuadraticForm.atFinitePlace_def]
    exact h.baseChange (A := v.adicCompletion K)
  · intro w
    let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    rw [QuadraticForm.atRealPlace_def]
    simpa only [RingHom.algebraMap_toAlgebra] using h.baseChange (A := ℝ)

/-- Globally equivalent quadratic forms are locally equivalent. -/
theorem LocallyEquivalent.of_equivalent {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.Equivalent R) : Q.LocallyEquivalent R := by
  constructor
  · intro v
    rw [QuadraticForm.atFinitePlace_def, QuadraticForm.atFinitePlace_def]
    exact h.baseChange (v.adicCompletion K)
  · intro w
    let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    rw [QuadraticForm.atRealPlace_def, QuadraticForm.atRealPlace_def]
    exact h.baseChange ℝ

/-- Local equivalence is reflexive. -/
@[refl]
theorem LocallyEquivalent.refl (Q : _root_.QuadraticForm K V) : Q.LocallyEquivalent Q := by
  constructor <;> intro place <;> exact QuadraticMap.Equivalent.refl _

/-- Local equivalence is symmetric. -/
@[symm]
theorem LocallyEquivalent.symm {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) : R.LocallyEquivalent Q := by
  exact ⟨fun place ↦ (h.1 place).symm, fun place ↦ (h.2 place).symm⟩

/-- Local equivalence is transitive. -/
@[trans]
theorem LocallyEquivalent.trans {X : Type*} [AddCommGroup X] [Module K X]
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    {S : _root_.QuadraticForm K X} (hQR : Q.LocallyEquivalent R)
    (hRS : R.LocallyEquivalent S) : Q.LocallyEquivalent S := by
  exact ⟨fun place ↦ (hQR.1 place).trans (hRS.1 place),
    fun place ↦ (hQR.2 place).trans (hRS.2 place)⟩

/-- Local representation is reflexive. -/
@[refl]
theorem LocallyRepresents.refl (Q : _root_.QuadraticForm K V) : Q.LocallyRepresents Q := by
  constructor <;> intro place <;> exact QuadraticMap.IsRepresentedBy.refl _

/-- Local representation is transitive. -/
@[trans]
theorem LocallyRepresents.trans {X : Type*} [AddCommGroup X] [Module K X]
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    {S : _root_.QuadraticForm K X} (hQR : Q.LocallyRepresents R)
    (hRS : R.LocallyRepresents S) : Q.LocallyRepresents S := by
  exact ⟨fun place ↦ (hQR.1 place).trans (hRS.1 place),
    fun place ↦ (hQR.2 place).trans (hRS.2 place)⟩

/-- Local equivalence implies local representation. -/
theorem LocallyEquivalent.locallyRepresents {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) : Q.LocallyRepresents R :=
  ⟨fun place ↦ (h.1 place).isRepresentedBy,
    fun place ↦ (h.2 place).isRepresentedBy⟩

/-- Local representation carries local isotropy from the represented form to the ambient form. -/
theorem LocallyRepresents.isLocallyIsotropic {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQR : Q.LocallyRepresents R)
    (hQ : Q.IsLocallyIsotropic) : R.IsLocallyIsotropic :=
  ⟨fun place ↦ (hQR.1 place).not_anisotropic (hQ.1 place),
    fun place ↦ (hQR.2 place).not_anisotropic (hQ.2 place)⟩

/-- Local representation carries represented scalars from the represented form to the ambient
form. -/
theorem LocallyRepresents.locallyRepresentsScalar {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hQR : Q.LocallyRepresents R) {a : K}
    (hQa : Q.LocallyRepresentsScalar a) : R.LocallyRepresentsScalar a :=
  ⟨fun place ↦ (hQR.1 place).represents (hQa.1 place),
    fun place ↦ (hQR.2 place).represents (hQa.2 place)⟩

/-- Locally equivalent forms are locally isotropic simultaneously. -/
theorem LocallyEquivalent.isLocallyIsotropic_iff {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) :
    Q.IsLocallyIsotropic ↔ R.IsLocallyIsotropic :=
  ⟨h.locallyRepresents.isLocallyIsotropic, h.symm.locallyRepresents.isLocallyIsotropic⟩

/-- Locally equivalent forms locally represent the same scalars. -/
theorem LocallyEquivalent.locallyRepresentsScalar_iff {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) (a : K) :
    Q.LocallyRepresentsScalar a ↔ R.LocallyRepresentsScalar a :=
  ⟨h.locallyRepresents.locallyRepresentsScalar,
    h.symm.locallyRepresents.locallyRepresentsScalar⟩

/-- Global equivalence preserves local isotropy. -/
theorem QuadraticMap.Equivalent.isLocallyIsotropic_iff
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (h : Q.Equivalent R) : Q.IsLocallyIsotropic ↔ R.IsLocallyIsotropic :=
  (LocallyEquivalent.of_equivalent h).isLocallyIsotropic_iff

/-- Global equivalence preserves local scalar representation. -/
theorem QuadraticMap.Equivalent.locallyRepresentsScalar_iff
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (h : Q.Equivalent R) (a : K) :
    Q.LocallyRepresentsScalar a ↔ R.LocallyRepresentsScalar a :=
  (LocallyEquivalent.of_equivalent h).locallyRepresentsScalar_iff a

/-- Replacing both global forms by equivalent forms preserves local representation. -/
theorem QuadraticMap.Equivalent.locallyRepresents_congr
    {V' W' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm K V'}
    {R : _root_.QuadraticForm K W} {R' : _root_.QuadraticForm K W'}
    (hQ : Q.Equivalent Q') (hR : R.Equivalent R') :
    Q.LocallyRepresents R ↔ Q'.LocallyRepresents R' := by
  have hQlocal := LocallyEquivalent.of_equivalent hQ
  have hRlocal := LocallyEquivalent.of_equivalent hR
  constructor
  · intro h
    exact ⟨fun place ↦ ((hQlocal.1 place).isRepresentedBy_congr
        (hRlocal.1 place)).mp (h.1 place),
      fun place ↦ ((hQlocal.2 place).isRepresentedBy_congr
        (hRlocal.2 place)).mp (h.2 place)⟩
  · intro h
    exact ⟨fun place ↦ ((hQlocal.1 place).isRepresentedBy_congr
        (hRlocal.1 place)).mpr (h.1 place),
      fun place ↦ ((hQlocal.2 place).isRepresentedBy_congr
        (hRlocal.2 place)).mpr (h.2 place)⟩

/-- Locally equivalent finite-dimensional quadratic forms have the same global rank. -/
theorem LocallyEquivalent.finrank_eq [FiniteDimensional K V] [FiniteDimensional K W]
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (h : Q.LocallyEquivalent R) : Module.finrank K V = Module.finrank K W := by
  let place : HeightOneSpectrum (𝓞 K) :=
    (HeightOneSpectrum.equivMaximalSpectrum (RingOfIntegers.not_isField K)).symm
      (Classical.choice (inferInstance : Nonempty (MaximalSpectrum (𝓞 K))))
  obtain ⟨e⟩ := h.1 place
  simpa only [Module.finrank_baseChange] using LinearEquiv.finrank_eq e.toLinearEquiv

end QuadraticForm
