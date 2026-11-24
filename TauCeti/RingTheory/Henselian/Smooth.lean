/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Smooth.Basic
import TauCeti.RingTheory.Henselian.Ideal
import TauCeti.RingTheory.Henselian.Section
import TauCeti.RingTheory.Smooth.EtaleSlice
import TauCeti.RingTheory.TensorProduct.LiftEquiv

/-!
# Sections of smooth algebras over a Henselian pair

Let `(S, J)` be a Henselian pair and let `A` be a smooth `S`-algebra. Reducing modulo `J` is a
surjection from `S`-algebra maps `A → S` to `S`-algebra maps `A → S ⧸ J`
(`TauCeti.HenselianRing.comp_surjective`): every section of `Spec A → Spec S` over the closed
subscheme `V(J)` lifts to a section over `Spec S`. Neither locality nor Noetherianity of `S` nor
constant relative dimension of `A` is required. Unlike the étale case
(`TauCeti.HenselianRing.comp_bijective`), the lift is not unique in positive relative dimension.

More generally, for a smooth algebra `A` over an arbitrary base `R` and a Henselian pair `(S, J)`
under `R`, every `R`-algebra map `A → S ⧸ J` lifts to an `R`-algebra map `A → S`
(`TauCeti.HenselianRing.comp_surjective_of_algebra`), and more generally still any surjective
`R`-algebra homomorphism `f : S →ₐ[R] T` whose kernel is a Henselian ideal of `S` has the
`R`-algebra lifting property against smooth `R`-algebras
(`TauCeti.HenselianRing.comp_surjective_of_surjective`). Compare
`Algebra.FormallySmooth.comp_surjective`, which lifts formal smoothness along nilpotent kernels.

Applying this to the nonzero powers `J ^ n` (`Ideal.henselianRing_pow`) approximates completed
points of smooth algebras over arbitrary Henselian pairs (`exists_algHom_comp_eq_evalₐ`): for every
`n : ℕ`, every `R`-algebra map `A →ₐ[R] AdicCompletion J S` agrees modulo `J ^ n` with an actual
`R`-algebra map `A →ₐ[R] S`. This is the smooth case (`h = 0`, `V = Spec A`) of Elkik's
approximation theorem, holding without any Noetherian assumption on `S`.

The proof combines `Algebra.Smooth.exists_etale_algHom_comp_eq` — which factors any closed-fibre
point `A →ₐ[S] S ⧸ J` of a smooth `S`-algebra through an étale slice `C` — with the étale section
lifting theorem `TauCeti.HenselianRing.comp_bijective`.

## Main results

* `TauCeti.HenselianRing.comp_surjective`: over a Henselian pair `(S, J)`, every `S`-algebra map
  `A →ₐ[S] S ⧸ J` out of a smooth `S`-algebra lifts to `A →ₐ[S] S` (Stacks, Lemma 15.13.3, 0H74).
* `TauCeti.HenselianRing.comp_surjective_of_algebra`: the relative form for a smooth `R`-algebra
  `A` and a Henselian pair `(S, J)` over `R`.
* `TauCeti.HenselianRing.comp_surjective_of_surjective`: lifting `A →ₐ[R] T` along any surjective
  `f : S →ₐ[R] T` with `HenselianRing S (RingHom.ker f)`.
* `TauCeti.HenselianRing.exists_algHom_comp_eq_evalₐ`: any `J`-adically completed `R`-point
  `A →ₐ[R] AdicCompletion J S` of a smooth `R`-algebra is congruent modulo `J ^ n` to an `S`-point
  `A →ₐ[R] S`.
* `TauCeti.HenselianLocalRing.comp_surjective` and
  `TauCeti.HenselianLocalRing.comp_surjective_of_algebra`: residue-field points of smooth algebras
  lift to Henselian local rings.
* `TauCeti.henselianRing_iff_forall_smooth_comp_surjective`: a pair `(R, I)` is Henselian if and
  only if every smooth `R`-algebra satisfies section lifting modulo `I`.

## References

* [Stacks Project, Lemma 15.13.3](https://stacks.math.columbia.edu/tag/0H74).
* R. Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*, Ann. Sci. École Norm.
  Sup. (4) 6 (1973), 553–603.
-/

public section

open IsLocalRing TensorProduct

universe u v

namespace TauCeti

namespace HenselianRing

section Absolute

variable {S : Type u} [CommRing S] (J : Ideal S) [HenselianRing S J]
  {A : Type v} [CommRing A] [Algebra S A] [Algebra.Smooth S A]

/-- **Elkik's smooth lifting theorem over a Henselian pair.** Over a Henselian pair `(S, J)`,
reduction modulo `J` is surjective from `S`-algebra maps `A →ₐ[S] S` out of a smooth `S`-algebra `A`
to `S`-algebra maps `A →ₐ[S] S ⧸ J`: every section modulo `J` lifts to a section over `S`. -/
@[stacks 0H74]
theorem comp_surjective :
    Function.Surjective ((Ideal.Quotient.mkₐ S J).comp : (A →ₐ[S] S) → A →ₐ[S] S ⧸ J) := by
  intro ψ
  -- Factor `ψ : A →ₐ[S] S ⧸ J` through an étale slice `C` and lift the étale section.
  obtain ⟨C, _, _, _, f, ψC, hψC⟩ :=
    Algebra.Smooth.exists_etale_algHom_comp_eq (R := S) Ideal.Quotient.mk_surjective ψ
  obtain ⟨φC, hφC⟩ := (comp_bijective (S := S) (A := C) J).surjective ψC
  refine ⟨φC.comp f, ?_⟩
  rw [← AlgHom.comp_assoc, hφC, hψC]

end Absolute

section Relative

variable {R : Type*} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] (J : Ideal S)
  [HenselianRing S J] {A : Type v} [CommRing A] [Algebra R A] [Algebra.Smooth R A]

/-- **Relative smooth lifting over a Henselian pair.** For a Henselian pair `(S, J)` with `S` an
`R`-algebra and a smooth `R`-algebra `A`, reduction modulo `J` is surjective from `R`-algebra maps
`A →ₐ[R] S` to `R`-algebra maps `A →ₐ[R] S ⧸ J`. -/
@[stacks 0H74 "relative form over an arbitrary base"]
theorem comp_surjective_of_algebra :
    Function.Surjective ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] S) → A →ₐ[R] S ⧸ J) :=
  -- Base change `A` to the smooth `S`-algebra `S ⊗[R] A` and apply `comp_surjective` over `S`.
  (AlgHom.restrictScalars_comp_surjective_iff R A (Ideal.Quotient.mkₐ S J)).mpr
    (comp_surjective J)

/-- **Approximation of completed points of smooth algebras over a Henselian pair.** For any `n : ℕ`
and any `R`-algebra map `ψ : A →ₐ[R] AdicCompletion J S` out of a smooth `R`-algebra `A`, there is
an `R`-algebra map `φ : A →ₐ[R] S` congruent to `ψ` modulo `J ^ n`. No Noetherian hypothesis on `S`
is required. -/
theorem exists_algHom_comp_eq_evalₐ (n : ℕ) (ψ : A →ₐ[R] AdicCompletion J S) :
    ∃ φ : A →ₐ[R] S,
      (Ideal.Quotient.mkₐ R (J ^ n)).comp φ =
        ((AdicCompletion.evalₐ J n).restrictScalars R).comp ψ := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- At `n = 0`, `S ⧸ J ^ 0 = S ⧸ ⊤` is subsingleton; lift the `n = 1` truncation to witness `φ`.
    obtain ⟨φ, -⟩ := comp_surjective_of_algebra (J ^ 1)
      (((AdicCompletion.evalₐ J 1).restrictScalars R).comp ψ)
    have : Subsingleton (S ⧸ J ^ 0) := by simp
    exact ⟨φ, Subsingleton.elim _ _⟩
  · have : NeZero n := ⟨hn⟩
    exact comp_surjective_of_algebra (J ^ n)
      (((AdicCompletion.evalₐ J n).restrictScalars R).comp ψ)

end Relative

section SurjectiveHom

variable {R : Type*} [CommRing R] {S : Type u} {T : Type*} [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] {A : Type v} [CommRing A] [Algebra R A] [Algebra.Smooth R A]

/-- **Smooth lifting along a surjective homomorphism with Henselian kernel.** Compare
`Algebra.FormallySmooth.comp_surjective` for nilpotent kernels: for a smooth `R`-algebra `A` and a
surjective `R`-algebra map `f : S →ₐ[R] T` with `HenselianRing S (RingHom.ker f)`, every `R`-algebra
map `A →ₐ[R] T` lifts along `f` to `A →ₐ[R] S`. -/
theorem comp_surjective_of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f)
    [HenselianRing S (RingHom.ker f)] :
    Function.Surjective (f.comp : (A →ₐ[R] S) → A →ₐ[R] T) := by
  intro ψ
  let e : (S ⧸ RingHom.ker f) ≃ₐ[R] T := Ideal.quotientKerAlgEquivOfSurjective hf
  obtain ⟨φ, hφ⟩ := comp_surjective_of_algebra (RingHom.ker f) (e.symm.toAlgHom.comp ψ)
  refine ⟨φ, AlgHom.ext fun a ↦ ?_⟩
  have ha := congrArg e (AlgHom.congr_fun hφ a)
  simpa [e] using ha

end SurjectiveHom

end HenselianRing

namespace HenselianLocalRing

/-- Over a Henselian local ring `R`, every `R`-algebra map `S →ₐ[R] ResidueField R` out of a smooth
`R`-algebra `S` lifts to an `R`-point `S →ₐ[R] R`. -/
theorem comp_surjective {R S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] :
    Function.Surjective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  have hker : RingHom.ker (Algebra.ofId R (ResidueField R)) = maximalIdeal R := by
    ext r
    simp [ResidueField.algebraMap_eq, residue_eq_zero_iff]
  have : HenselianRing R (RingHom.ker (Algebra.ofId R (ResidueField R))) :=
    hker ▸ inferInstance
  exact HenselianRing.comp_surjective_of_surjective (Algebra.ofId R (ResidueField R))
    residue_surjective

/-- Relative form of `HenselianLocalRing.comp_surjective`: for a Henselian local `R`-algebra `S`
and a smooth `R`-algebra `A`, every `R`-algebra map `A →ₐ[R] ResidueField S` lifts to an `R`-algebra
map `A →ₐ[R] S`. -/
theorem comp_surjective_of_algebra {R S A : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing S] [Algebra R S] [CommRing A] [Algebra R A] [Algebra.Smooth R A] :
    Function.Surjective
      ((IsScalarTower.toAlgHom R S (ResidueField S)).comp :
        (A →ₐ[R] S) → A →ₐ[R] ResidueField S) :=
  (AlgHom.restrictScalars_comp_surjective_iff R A (Algebra.ofId S (ResidueField S))).mpr
    comp_surjective

end HenselianLocalRing

/-- **Henselian pairs are characterised by lifting sections of smooth algebras.** Extending
`henselianRing_iff_forall_comp_surjective`, a pair `(R, I)` is Henselian if and only if every
smooth `R`-algebra `A` satisfies surjectivity of `(A →ₐ[R] R) → A →ₐ[R] R ⧸ I`. -/
theorem henselianRing_iff_forall_smooth_comp_surjective {R : Type u} [CommRing R] {I : Ideal R} :
    HenselianRing R I ↔ ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Smooth R A],
      Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] R) → A →ₐ[R] R ⧸ I) :=
  ⟨fun _ _ _ _ _ ↦ HenselianRing.comp_surjective I,
    fun h ↦ henselianRing_iff_forall_comp_surjective.mpr fun A _ _ _ ↦ h A⟩

end TauCeti
