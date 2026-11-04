/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Gorenstein-projective modules have no higher extensions by finite projectives

Let `A` be a ring and `M` a Gorenstein-projective `A`-module, the degree-zero cycles of a totally
acyclic complex `P` of finitely generated projective modules. Then `Ext^{n+1}(M, Q) = 0` for
every finitely generated projective module `Q`.

The cycles of `P` fit into short exact sequences `0 ⟶ Zⁱ ⟶ Pⁱ ⟶ Zⁱ⁺¹ ⟶ 0`, whose middle terms
are projective, so the long exact sequence of `Ext(-, Q)` shifts dimension. In degree `1` the
obstruction is a map `Zⁱ ⟶ Q` which does not extend to `Pⁱ`, and every such map extends
(`CochainComplex.IsTotallyAcyclic.exists_extend_iCycles`). This is the module counterpart of
`CategoryTheory.isGorensteinProjective.ext_eq_zero`, whose complete resolutions are tested
against all projective objects rather than the regular module.

## Main results

* `CochainComplex.IsTotallyAcyclic.ext_cycles_eq_zero`: the cycles of a totally acyclic complex
  have no higher extensions by finitely generated projective modules.
* `TauCeti.IsGorensteinProjective.ext_eq_zero`: `Ext^{n+1}(M, Q) = 0` for `M`
  Gorenstein-projective and `Q` finitely generated projective.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}
  (hS : S.ShortExact) [Projective S.X₂] {Y : C}
include hS

/-- **Extension along a monomorphism kills `Ext¹` of the cokernel**: if `S` is short exact with
projective middle term and every morphism `S.X₁ ⟶ Y` extends along `S.f`, then
`Ext¹(S.X₃, Y) = 0`. This is the converse of `exists_f_comp_eq_of_ext_eq_zero`. -/
lemma ext_eq_zero_of_exists_f_comp_eq (h : ∀ φ : S.X₁ ⟶ Y, ∃ ψ : S.X₂ ⟶ Y, S.f ≫ ψ = φ)
    (e : Ext.{w} S.X₃ Y 1) : e = 0 := by
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
    (n₀ := 0) rfl
  obtain ⟨g, hg⟩ := h (Ext.addEquiv₀ x)
  rw [← Ext.mk₀_addEquiv₀_apply x, ← hg, ← Ext.mk₀_comp_mk₀]
  exact hS.extClass_comp_assoc _

/-- **Dimension shifting to the cokernel**: if `S` is short exact with projective middle term,
then `Ext^{n+2}(S.X₃, Y) = 0` as soon as `Ext^{n+1}(S.X₁, Y) = 0`. -/
lemma ext_X₃_eq_zero_of_ext_X₁_eq_zero {n : ℕ} (h : ∀ e : Ext.{w} S.X₁ Y (n + 1), e = 0)
    (e : Ext.{w} S.X₃ Y (n + 2)) : e = 0 := by
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y e (Ext.eq_zero_of_projective _)
    (n₀ := n + 1) (by lia)
  rw [h x, Ext.comp_zero]

/-- **Dimension shifting to the kernel**: if `S` is short exact with projective middle term,
then `Ext^{n+1}(S.X₁, Y) = 0` as soon as `Ext^{n+2}(S.X₃, Y) = 0`. -/
lemma ext_X₁_eq_zero_of_ext_X₃_eq_zero {n : ℕ} (h : ∀ e : Ext.{w} S.X₃ Y (n + 2), e = 0)
    (e : Ext.{w} S.X₁ Y (n + 1)) : e = 0 := by
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₁ hS Y e (by lia) (h _)
  rw [Ext.eq_zero_of_projective x, Ext.comp_zero]

end CategoryTheory.ShortComplex.ShortExact

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A] {P : CochainComplex (ModuleCat.{v} A) ℤ}
  (hP : P.IsTotallyAcyclic) [HasExt.{w} (ModuleCat.{v} A)]
include hP

/-- The cycles of a totally acyclic complex have no higher extensions by finitely generated
projective modules. -/
theorem ext_cycles_eq_zero (Q : ModuleCat.{v} A) [Module.Finite A Q] [Module.Projective A Q]
    (n : ℕ) : ∀ (m : ℤ) (e : Ext.{w} (P.cycles m) Q (n + 1)), e = 0 := by
  have := hP.projective
  have hS (m : ℤ) : (ShortComplex.mk (P.iCycles (m - 1)) (P.toCycles (m - 1) m)
      (P.iCycles_toCycles _ _)).ShortExact := by
    have := P.cyclesShortComplex_shortExact (m - 1) m (by simp) (hP.acyclic m)
    rwa [HomologicalComplex.cyclesShortComplex_def] at this
  induction n with
  | zero =>
    intro m
    refine (hS m).ext_eq_zero_of_exists_f_comp_eq fun φ ↦ ?_
    obtain ⟨g, hg⟩ := hP.exists_extend_iCycles (m - 1) φ.hom
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  | succ n ih => exact fun m ↦ (hS m).ext_X₃_eq_zero_of_ext_X₁_eq_zero (ih (m - 1))

end CochainComplex.IsTotallyAcyclic

namespace TauCeti

variable {A : Type u} [Ring A] [HasExt.{w} (ModuleCat.{v} A)]

/-- **Gorenstein-projective modules have no higher extensions by finite projectives**:
`Ext^{n+1}(M, Q) = 0` for a Gorenstein-projective module `M` and a finitely generated projective
module `Q`. -/
theorem IsGorensteinProjective.ext_eq_zero {M : ModuleCat.{v} A} (hM : IsGorensteinProjective A M)
    (Q : ModuleCat.{v} A) [Module.Finite A Q] [Module.Projective A Q] {n : ℕ}
    (e : Ext.{w} M Q (n + 1)) : e = 0 := by
  obtain ⟨P, hP, ⟨i⟩⟩ := (isGorensteinProjective_iff M).1 hM
  rw [← Ext.mk₀_id_comp e, ← i.inv_hom_id, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hP.ext_cycles_eq_zero Q n 0 ((Ext.mk₀ i.hom).comp e (zero_add _)), Ext.comp_zero]

end TauCeti
