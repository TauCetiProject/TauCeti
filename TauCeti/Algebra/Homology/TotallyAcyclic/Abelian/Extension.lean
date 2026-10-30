/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Splice
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Ext
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Horseshoe

/-!
# Extensions of Gorenstein-projective objects

In an abelian category `C`, the Gorenstein-projective objects are closed under extensions: the
middle term of a short exact sequence with Gorenstein-projective outer terms is
Gorenstein-projective.

The proof reuses the horseshoe lemma for complete resolutions in an exact category
(`TauCeti.ExactStructure.CompleteResolution.horseshoe`). It is applied to the extension-closed
full subcategory of the objects `X` with `Ext¹(X, Q) = 0` for every projective `Q`, with the exact
structure inherited from `C`. There the projective objects of `C` are projective-injective, so a
totally acyclic complex of projectives is a complete resolution in this exact category; and the
middle resolution produced by the horseshoe has projective terms, since they split as biproducts
of the terms of the outer ones. Conversely a splice of short exact sequences with projective
middle terms and `Ext¹(-, Q)`-orthogonal ends is a totally acyclic complex of projectives
(`CochainComplex.isTotallyAcyclicProjective_splice`).

## Main results

* `CategoryTheory.ShortComplex.ShortExact.exists_f_comp_eq_of_ext_eq_zero`: along a short exact
  sequence whose cokernel has no extensions by `Y`, every morphism to `Y` from the kernel extends.
* `CochainComplex.isTotallyAcyclicProjective_splice`: a splice of short exact sequences with
  projective middle terms and ends without extensions by projectives is totally acyclic.
* `CategoryTheory.isGorensteinProjective_X₂_of_shortExact`: Gorenstein-projective objects are
  closed under extensions.

## References

* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, de Gruyter
  Expositions in Mathematics **30** (2000), Theorem 10.2.8.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory.ShortComplex.ShortExact

variable [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact)
include hS

/-- **Extension along a monomorphism with orthogonal cokernel**: if `S` is short exact and
`Ext¹(S.X₃, Y) = 0`, every morphism `S.X₁ ⟶ Y` extends along `S.f`. -/
lemma exists_f_comp_eq_of_ext_eq_zero {Y : C} (h : ∀ x : Ext.{w} S.X₃ Y 1, x = 0)
    (ψ : S.X₁ ⟶ Y) : ∃ g : S.X₂ ⟶ Y, S.f ≫ g = ψ := by
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ ψ) (n₁ := 1) rfl (h _)
  refine ⟨Ext.addEquiv₀ x, Ext.homEquiv₀.symm.injective ?_⟩
  rw [← Ext.mk₀_addEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
  exact hx

end CategoryTheory.ShortComplex.ShortExact

namespace CochainComplex

variable [HasExt.{w} C] (S : ℤ → ShortComplex C) (e : ∀ n, (S n).X₃ ≅ (S (n + 1)).X₁)
  (hS : ∀ n, (S n).ShortExact)
include hS

/-- **Splices of orthogonal short exact sequences are totally acyclic**: splicing short exact
sequences `Sⁿ` with projective middle terms, whose end terms have no extensions by projective
objects, gives a totally acyclic complex of projectives. -/
lemma isTotallyAcyclicProjective_splice (hproj : ∀ n, Projective (S n).X₂)
    (hext : ∀ n (Q : C) [Projective Q] (x : Ext.{w} (S n).X₃ Q 1), x = 0) :
    (splice S e).IsTotallyAcyclicProjective := by
  refine isTotallyAcyclicProjective_iff_factor.2 ⟨hproj, acyclic_splice S e hS,
    fun i j hij Q _ φ hφ ↦ ?_⟩
  obtain rfl := hij
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by lia⟩
  rw [add_sub_cancel_right, splice_d] at hφ
  -- `φ` vanishes on `Sⁱ.X₁`, which is the image of the incoming differential.
  have h₁ : (S (m + 1)).f ≫ φ = 0 := by
    have := (hS m).epi_g
    rw [← cancel_epi ((S m).g ≫ (e m).hom), comp_zero, Category.assoc]
    simpa only [Category.assoc] using hφ
  -- So `φ` factors through `Sⁱ.X₃`, which embeds into the next term with orthogonal cokernel.
  obtain ⟨ψ, hψ⟩ := CokernelCofork.IsColimit.desc' (hS (m + 1)).gIsCokernel φ h₁
  rw [Cofork.π_ofπ] at hψ
  subst hψ
  obtain ⟨g, hg⟩ := (hS (m + 1 + 1)).exists_f_comp_eq_of_ext_eq_zero (hext (m + 1 + 1) Q)
    ((e (m + 1)).inv ≫ ψ)
  exact ⟨g, by rw [splice_d, Category.assoc, Category.assoc, hg, Iso.hom_inv_id_assoc]⟩

end CochainComplex

namespace CategoryTheory

open TauCeti CochainComplex ZeroObject

section Orthogonal

variable [HasExt.{w} C]

variable (C) in
/-- The objects without extensions by projective objects: `Ext¹(X, Q) = 0` for every projective
`Q`. -/
private def extProjOrth : ObjectProperty C :=
  fun X ↦ ∀ (Q : C) [Projective Q] (x : Ext.{w} X Q 1), x = 0

private lemma extProjOrth_of_projective (X : C) [Projective X] : extProjOrth C X :=
  fun _ _ x ↦ Ext.eq_zero_of_projective (n := 0) x

private lemma isExtensionClosed_extProjOrth :
    (ExactStructure.abelian C).IsExtensionClosed (extProjOrth C) where
  prop_X₂ {S} hS h₁ h₃ Q _ x := by
    obtain ⟨y, rfl⟩ :=
      Ext.contravariant_sequence_exact₂ ((ExactStructure.abelian_conflation S).1 hS) Q x (h₁ Q _)
    rw [h₃ Q y, Ext.comp_zero]

private instance : (extProjOrth C).ContainsZero :=
  ⟨0, isZero_zero C, extProjOrth_of_projective 0⟩

private instance : (extProjOrth C).IsClosedUnderIsomorphisms :=
  isExtensionClosed_extProjOrth.isClosedUnderIsomorphisms

private instance : (extProjOrth C).IsClosedUnderBinaryProducts :=
  isExtensionClosed_extProjOrth.isClosedUnderBinaryProducts

variable (C) in
/-- The exact structure on `extProjOrth C` inherited from the abelian structure of `C`. -/
private noncomputable abbrev extProjOrthExact : ExactStructure (extProjOrth C).FullSubcategory :=
  (ExactStructure.abelian C).fullSubcategory _ isExtensionClosed_extProjOrth

/-- The conflations of `extProjOrthExact C` are the short exact sequences of `C`. -/
private lemma conflation_iff (S : ShortComplex (extProjOrth C).FullSubcategory) :
    (extProjOrthExact C).Conflation S ↔ (S.map (extProjOrth C).ι).ShortExact := by
  rw [ExactStructure.fullSubcategory_conflation_iff, ExactStructure.abelian_conflation]

/-- A conflation of `extProjOrthExact C` is a short exact sequence of `C`. -/
private lemma shortExact_of_conflation {S : ShortComplex (extProjOrth C).FullSubcategory}
    (hS : (extProjOrthExact C).Conflation S) : (S.map (extProjOrth C).ι).ShortExact :=
  (conflation_iff S).1 hS

/-- The projective objects of `C` are projective-injective in `extProjOrthExact C`. -/
private lemma projectiveInjective_extProjOrthExact (Q : C) [Projective Q] :
    (extProjOrthExact C).projectiveInjective ⟨Q, extProjOrth_of_projective Q⟩ := by
  refine (ExactStructure.projectiveInjective_iff _ _).2
    ⟨ExactStructure.isProjective_iff.2 fun X Y p hp f ↦ ?_,
      ExactStructure.isInjective_iff.2 fun X Y i hi f ↦ ?_⟩
  · obtain ⟨Z, i, hz, hc⟩ := (ConflationClass.isDeflation_iff _ p).1 hp
    have : Epi p.hom := (shortExact_of_conflation hc).epi_g
    exact ⟨ObjectProperty.homMk (Projective.factorThru f.hom p.hom),
      ObjectProperty.hom_ext _ (Projective.factorThru_comp f.hom p.hom)⟩
  · obtain ⟨Z, p, hz, hc⟩ := (ConflationClass.isInflation_iff _ i).1 hi
    obtain ⟨g, hg⟩ := (shortExact_of_conflation hc).exists_f_comp_eq_of_ext_eq_zero
      (Z.property Q) f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

/-- A totally acyclic complex of projectives, as a complete resolution in `extProjOrthExact C`.
-/
private noncomputable abbrev toCompleteResolution {P : CochainComplex C ℤ}
    (hP : P.IsTotallyAcyclicProjective) : (extProjOrthExact C).CompleteResolution where
  Z n := ⟨P.cycles n, fun Q _ x ↦ hP.ext_cycles_eq_zero Q 0 n x⟩
  X n := ⟨P.X n, have := hP.projective n; extProjOrth_of_projective _⟩
  ι n := ObjectProperty.homMk (P.iCycles n)
  π n := ObjectProperty.homMk (P.toCycles n (n + 1))
  ι_π n := ObjectProperty.hom_ext _ (P.iCycles_toCycles n (n + 1))
  conflation n := by
    refine (conflation_iff _).2 (ShortComplex.shortExact_of_iso ?_
      (P.cyclesShortComplex_shortExact_of_iso rfl (hP.acyclic (n + 1)) (Iso.refl _) (Iso.refl _)))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  projectiveInjective n := have := hP.projective n; projectiveInjective_extProjOrthExact _

/-- A complete resolution in `extProjOrthExact C` with projective terms, as a totally acyclic
complex of projectives. -/
private lemma isTotallyAcyclicProjective_splice_completeResolution
    (r : (extProjOrthExact C).CompleteResolution) (hr : ∀ n, Projective (r.X n).obj) :
    (splice (fun n ↦ (r.shortComplex n).map (extProjOrth C).ι)
      fun _ ↦ Iso.refl _).IsTotallyAcyclicProjective :=
  isTotallyAcyclicProjective_splice _ _ (fun n ↦ shortExact_of_conflation (r.conflation n)) hr
    fun n Q _ ↦ (r.Z (n + 1)).property Q

end Orthogonal

/-- **Gorenstein-projective objects are closed under extensions**: the middle term of a short
exact sequence whose outer terms are Gorenstein-projective is Gorenstein-projective. -/
theorem isGorensteinProjective_X₂_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : isGorensteinProjective C S.X₁) (h₃ : isGorensteinProjective C S.X₃) :
    isGorensteinProjective C S.X₂ := by
  let := HasExt.standard C
  obtain ⟨P₁, hP₁, ⟨e₁⟩⟩ := (isGorensteinProjective_iff _).1 h₁
  obtain ⟨P₃, hP₃, ⟨e₃⟩⟩ := (isGorensteinProjective_iff _).1 h₃
  let r₁ := toCompleteResolution hP₁
  let r₃ := toCompleteResolution hP₃
  -- The given sequence is a conflation of `extProjOrthExact C` between the cycles.
  have hX₂ : extProjOrth C S.X₂ := isExtensionClosed_extProjOrth.prop_X₂
    ((ExactStructure.abelian_conflation S).2 hS)
    ((extProjOrth C).prop_of_iso e₁ (r₁.Z 0).property)
    ((extProjOrth C).prop_of_iso e₃ (r₃.Z 0).property)
  let f : r₁.Z 0 ⟶ ⟨S.X₂, hX₂⟩ := ObjectProperty.homMk (e₁.hom ≫ S.f)
  let g : (⟨S.X₂, hX₂⟩ : (extProjOrth C).FullSubcategory) ⟶ r₃.Z 0 :=
    ObjectProperty.homMk (S.g ≫ e₃.inv)
  have hfg : f ≫ g = 0 := ObjectProperty.hom_ext _ (by
    dsimp [f, g]
    rw [Category.assoc, S.zero_assoc, zero_comp, comp_zero])
  have hc : (extProjOrthExact C).Conflation (ShortComplex.mk f g hfg) :=
    (conflation_iff _).2 <| ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e₁.symm (Iso.refl _) e₃.symm (by simp [f]) (by simp [g])) hS
  let h := ExactStructure.CompleteResolution.horseshoe r₁ r₃ f g hfg hc
  -- The middle resolution has projective terms: they split as biproducts of projectives.
  have hproj (n : ℤ) : Projective (h.resolution.X n).obj := by
    obtain ⟨s⟩ := h.split n
    have := hP₁.projective n
    have := hP₃.projective n
    exact Projective.of_iso ((s.map (extProjOrth C).ι).isoBinaryBiproduct).symm
      (inferInstance : Projective (P₁.X n ⊞ P₃.X n))
  exact (isGorensteinProjective_iff _).2 ⟨_,
    isTotallyAcyclicProjective_splice_completeResolution h.resolution hproj,
    ⟨(spliceCyclesIso _ _ (fun n ↦ shortExact_of_conflation (h.resolution.conflation n)) 0).symm ≪≫
      (extProjOrth C).ι.mapIso h.iso⟩⟩

/-- Gorenstein-projective objects are extension closed for the abelian exact structure. -/
theorem isGorensteinProjective_isExtensionClosed :
    (ExactStructure.abelian C).IsExtensionClosed (isGorensteinProjective C) where
  prop_X₂ hS h₁ h₃ :=
    isGorensteinProjective_X₂_of_shortExact ((ExactStructure.abelian_conflation _).1 hS) h₁ h₃

end CategoryTheory
