/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Projective
public import TauCeti.Algebra.Homology.Ext.Presentation

/-!
# Gorenstein-projective modules have no higher extensions by projectives

Let `A` be a ring and `M` a Gorenstein-projective `A`-module, the degree-zero cycles of a totally
acyclic complex `P` of finitely generated projective modules. Then `Ext^{n+1}(M, Q) = 0` for
every projective module `Q`.

The cycles of `P` fit into short exact sequences `0 ⟶ Zⁱ ⟶ Pⁱ ⟶ Zⁱ⁺¹ ⟶ 0` with projective middle
terms, and every map `Zⁱ ⟶ Q` extends to `Pⁱ`
(`CochainComplex.IsTotallyAcyclic.exists_extend_iCycles`), so
`TauCeti.ext_X₃_eq_zero_of_forall_exists_f_comp_eq` applies. This is the module counterpart of
`CategoryTheory.isGorensteinProjective.ext_eq_zero`, whose complete resolutions are tested
against all projective objects rather than the regular module.

## Main results

* `CochainComplex.IsTotallyAcyclic.ext_cycles_eq_zero`: the cycles of a totally acyclic complex
  have no higher extensions by projective modules.
* `TauCeti.IsGorensteinProjective.ext_eq_zero`: `Ext^{n+1}(M, Q) = 0` for `M`
  Gorenstein-projective and `Q` projective.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A] {P : CochainComplex (ModuleCat.{v} A) ℤ}
  (hP : P.IsTotallyAcyclic) [HasExt.{w} (ModuleCat.{v} A)]
include hP

/-- The cycles of a totally acyclic complex have no higher extensions by projective modules. -/
theorem ext_cycles_eq_zero (Q : ModuleCat.{v} A) [Module.Projective A Q] (n : ℕ) (m : ℤ)
    (e : Ext.{w} (P.cycles m) Q (n + 1)) : e = 0 := by
  have := hP.projective
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  exact TauCeti.ext_X₃_eq_zero_of_forall_exists_f_comp_eq
    (S := fun m ↦ ShortComplex.mk (P.iCycles m) (P.toCycles m (m + 1)) (P.iCycles_toCycles _ _))
    (fun m ↦ P.shortExact_mk_iCycles_toCycles m (m + 1) (by simp) (hP.acyclic (m + 1)))
    (fun _ ↦ Iso.refl _) (fun m φ ↦ let ⟨g, hg⟩ := hP.exists_extend_iCycles m φ.hom
      ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩) n k e

end CochainComplex.IsTotallyAcyclic

namespace TauCeti

variable {A : Type u} [Ring A] [HasExt.{w} (ModuleCat.{v} A)]

/-- **Gorenstein-projective modules have no higher extensions by projectives**:
`Ext^{n+1}(M, Q) = 0` for a Gorenstein-projective module `M` and a projective module `Q`. -/
theorem IsGorensteinProjective.ext_eq_zero {M : ModuleCat.{v} A} (hM : IsGorensteinProjective A M)
    (Q : ModuleCat.{v} A) [Module.Projective A Q] {n : ℕ} (e : Ext.{w} M Q (n + 1)) : e = 0 := by
  obtain ⟨P, hP, ⟨i⟩⟩ := (isGorensteinProjective_iff M).1 hM
  exact ext_eq_zero_of_iso i.symm (hP.ext_cycles_eq_zero Q n 0) e

end TauCeti
