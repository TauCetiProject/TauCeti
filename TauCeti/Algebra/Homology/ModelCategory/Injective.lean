/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Factorizations.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import TauCeti.CategoryTheory.Abelian.EpiWithInjectiveKernel
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ModelCategory.Lifting
import TauCeti.Algebra.Homology.Disk
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.Algebra.Homology.HomotopyCofiber
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Kernel

/-!
# Lifting against monomorphic quasi-isomorphisms of unbounded complexes

Let `C` be an abelian category. For a Grothendieck abelian category, the injective model
structure on unbounded cochain complexes in `C` has the monomorphisms as cofibrations, the
quasi-isomorphisms as weak equivalences, and as fibrations the morphisms with the right lifting
property with respect to the monomorphic quasi-isomorphisms. This file identifies that lifting
property without assuming a model structure, so that its fibrations and fibrant objects can be
recognized and used once a model structure or a factorization is available.

## Main results

* `CochainComplex.rlp_monomorphisms_inf_quasiIso_iff`: a morphism `p : X ⟶ Y` has the right
  lifting property with respect to every monomorphism which is a quasi-isomorphism if and only if
  it is degreewise an epimorphism with an injective kernel and its kernel is K-injective.
* `CochainComplex.rlp_monomorphisms_inf_quasiIso_iff_of_isZero`: the morphism from a complex `I`
  to a zero complex has this lifting property if and only if `I` is a K-injective complex of
  injective objects. No boundedness is assumed.

## Implementation notes

The lifting `CochainComplex.hasLiftingProperty_of_quasiIso` corrects degreewise liftings by a
coboundary, using Joël Riou's obstruction cocycle `CochainComplex.Lifting.cocycle₁` and
`CochainComplex.Lifting.hasLift`; it is the unbounded form of the lifting lemma for the model
structure on bounded below complexes in `Mathlib.Algebra.Homology.ModelCategory.Injective`.
Conversely, the terms are tested against the acyclic complexes `M --𝟙--> M` in two consecutive
degrees, which corepresent evaluation in a degree, and K-injectivity is tested against the
inclusion of an acyclic complex into the mapping cone of its identity.

## References

* J. Lurie, *Higher Algebra*, Proposition 1.3.5.3, Proposition 1.3.5.6 and Lemma 1.3.5.11.
-/

public section

namespace CochainComplex

open CategoryTheory Limits ZeroObject MorphismProperty HomComplex Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- A morphism of cochain complexes which is degreewise an epimorphism with an injective kernel,
and whose kernel is K-injective, has the right lifting property with respect to every
monomorphism which is a quasi-isomorphism. -/
theorem hasLiftingProperty_of_quasiIso {A B X Y : CochainComplex C ℤ} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [QuasiIso i] (hp : degreewiseEpiWithInjectiveKernel p) [(kernel p).IsKInjective] :
    HasLiftingProperty i p where
  sq_hasLift {t b} sq := by
    have sq' (n : ℤ) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      sq.map (HomologicalComplex.eval _ _ n)
    have (n : ℤ) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    -- the obstruction to correcting the degreewise liftings into a chain map
    let β : Cocycle (cokernel i) (kernel p) 1 :=
      Lifting.cocycle₁ sq (fun n ↦ { l := (sq' n).lift })
        (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    have hS : (ShortComplex.mk _ _ (cokernel.condition i)).ShortExact :=
      { exact := ShortComplex.exact_cokernel i }
    obtain ⟨α, hα⟩ :=
      IsKInjective.eq_δ_of_cocycle β (hS.acyclic_X₃ (by dsimp; infer_instance)) 0 (by simp)
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _) α hα

/-- If a morphism of cochain complexes has the right lifting property with respect to every
monomorphism which is a quasi-isomorphism, then in each degree it has the right lifting property
with respect to every monomorphism. -/
theorem rlp_monomorphisms_f {X Y : CochainComplex C ℤ} {p : X ⟶ Y}
    (hp : (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp p) (n : ℤ) :
    (monomorphisms C).rlp (p.f n) := by
  intro M N u (_ : Mono u)
  have hn : (ComplexShape.up ℤ).Rel n (n + 1) := rfl
  have hn' : n ≠ n + 1 := by omega
  -- morphisms out of `Z --𝟙--> Z` in degrees `n` and `n + 1` are morphisms out of `Z` in
  -- degree `n`
  let e (Z : C) := HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId hn hn' Z
  let Du : HomologicalComplex.double (𝟙 M) hn ⟶ HomologicalComplex.double (𝟙 N) hn :=
    HomologicalComplex.mkHomFromDouble hn hn'
      (u ≫ (HomologicalComplex.doubleXIso₀ (𝟙 N) hn).inv)
      (u ≫ (HomologicalComplex.doubleXIso₁ (𝟙 N) hn hn').inv)
      (by simp [HomologicalComplex.double_d _ _ hn'])
      (fun k hk ↦ by rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega),
        comp_zero])
  have hDu {K : CochainComplex C ℤ} (g : HomologicalComplex.double (𝟙 N) hn ⟶ K) :
      (e M).homEquiv (Du ≫ g) = u ≫ (e N).homEquiv g := by
    rw [(e M).homEquiv_comp]
    simp only [e, HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId_homEquiv_apply]
    simp [Du]
  have : Mono Du := HomologicalComplex.mono_of_mono_f _ fun k ↦ by
    by_cases h₀ : k = n
    · subst h₀
      simp only [Du, HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    by_cases h₁ : k = n + 1
    · subst h₁
      simp only [Du, HomologicalComplex.mkHomFromDouble_f₁]
      infer_instance
    exact ⟨fun _ _ _ ↦ (HomologicalComplex.isZero_double_X _ hn k h₀ h₁).eq_of_tgt _ _⟩
  have := hp Du ⟨this, HomologicalComplex.quasiIso_of_acyclic Du (acyclic_double_id M hn)
    (acyclic_double_id N hn)⟩
  refine ⟨fun {t b} sq ↦ ?_⟩
  have sq' : CommSq ((e M).homEquiv.symm t) Du p ((e N).homEquiv.symm b) :=
    ⟨(e M).homEquiv.injective (by
      rw [hDu, (e M).homEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact sq.w)⟩
  refine ⟨⟨{ l := (e N).homEquiv sq'.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← hDu, sq'.fac_left, Equiv.apply_symm_apply]
  · have := (e N).homEquiv_comp p sq'.lift
    rw [sq'.fac_right, Equiv.apply_symm_apply] at this
    exact this.symm

/-- If the morphism from a cochain complex `I` to a zero complex has the right lifting property
with respect to every monomorphism which is a quasi-isomorphism, then `I` is K-injective. -/
theorem isKInjective_of_rlp {I Z : CochainComplex C ℤ} {p : I ⟶ Z} (hZ : IsZero Z)
    (hp : (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp p) :
    I.IsKInjective where
  nonempty_homotopy_zero {A} f hA := by
    have hc : ∀ j, ∃ i, (ComplexShape.up ℤ).Rel i j := fun j ↦ ⟨j - 1, by simp⟩
    -- the inclusion of `A` into the contractible mapping cone of its identity
    let ι := HomologicalComplex.homotopyCofiber.inr (𝟙 A)
    have : Mono ι := HomologicalComplex.mono_of_mono_f _ fun k ↦
      mono_of_mono_fac (HomologicalComplex.homotopyCofiber.inrX_sndX (𝟙 A) k)
    have := hp ι ⟨this, HomologicalComplex.quasiIso_of_acyclic ι hA
      (HomologicalComplex.homotopyCofiber.acyclic_id A hc)⟩
    have sq : CommSq f ι p 0 := ⟨hZ.eq_of_tgt _ _⟩
    exact ⟨(Homotopy.ofEq (by simp [ι])).trans
      (((HomologicalComplex.homotopyCofiber.inrCompHomotopy (𝟙 A) hc).compRight sq.lift).trans
        (Homotopy.ofEq (by simp)))⟩

/-- **Fibrations of the injective model structure.** A morphism of cochain complexes has the
right lifting property with respect to every monomorphism which is a quasi-isomorphism if and
only if it is degreewise an epimorphism with an injective kernel and its kernel is K-injective. -/
theorem rlp_monomorphisms_inf_quasiIso_iff {X Y : CochainComplex C ℤ} (p : X ⟶ Y) :
    (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp p ↔
      degreewiseEpiWithInjectiveKernel p ∧ (kernel p).IsKInjective := by
  refine ⟨fun hp ↦ ⟨fun n ↦ (epiWithInjectiveKernel_iff_rlp_monomorphisms _).2
    (rlp_monomorphisms_f hp n), isKInjective_of_rlp (isZero_zero _)
      (IsStableUnderBaseChange.of_isPullback (IsPullback.kernel_ι p) hp)⟩, ?_⟩
  rintro ⟨hp, _⟩ A B i ⟨_ : Mono i, _ : QuasiIso i⟩
  exact hasLiftingProperty_of_quasiIso i p hp

/-- **Fibrant objects of the injective model structure.** The morphism from a cochain complex `I`
to a zero complex has the right lifting property with respect to every monomorphism which is a
quasi-isomorphism if and only if `I` is a K-injective complex of injective objects. -/
theorem rlp_monomorphisms_inf_quasiIso_iff_of_isZero {I Z : CochainComplex C ℤ} (p : I ⟶ Z)
    (hZ : IsZero Z) :
    (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp p ↔
      (∀ n, Injective (I.X n)) ∧ I.IsKInjective := by
  have hZ' (n : ℤ) : IsZero (Z.X n) := (HomologicalComplex.eval C _ n).map_isZero hZ
  refine ⟨fun hp ↦ ⟨fun n ↦ (injective_iff_rlp_monomorphisms_of_isZero _ (hZ' n)).2
    (rlp_monomorphisms_f hp n), isKInjective_of_rlp hZ hp⟩, ?_⟩
  rintro ⟨hI, _⟩
  obtain rfl := hZ.eq_of_tgt p 0
  have : (kernel (0 : I ⟶ Z)).IsKInjective := isKInjective_of_iso (asIso (kernel.ι _)).symm
  refine (rlp_monomorphisms_inf_quasiIso_iff _).2 ⟨fun n ↦ ?_, inferInstance⟩
  rw [epiWithInjectiveKernel_iff_rlp_monomorphisms,
    ← injective_iff_rlp_monomorphisms_of_isZero _ (hZ' n)]
  exact hI n

end CochainComplex
