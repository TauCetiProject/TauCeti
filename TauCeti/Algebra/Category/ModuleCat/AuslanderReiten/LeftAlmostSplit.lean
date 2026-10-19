/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.ExtensionClass
public import TauCeti.CategoryTheory.AlmostSplit.Ext
import TauCeti.Algebra.Homology.Ext.Realization
import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation

/-!
# Left almost-split sequences from Auslander–Reiten duality

If the translate `T = D Tr(f)` of a finite projective presentation over a finite-dimensional
algebra is noninjective and has local endomorphism ring, there is a nonsplit short exact
sequence `0 → T → E → coker f → 0` whose first map is left almost split. Its middle term
is finitely generated. The factorization property holds against all modules, not just
finitely generated ones.

The extension class supplied by `LinearMap.exists_auslanderReitenExt_ne_zero` is realized
by pushing out the image presentation of `f`. Vanishing of its pushforwards gives the
left almost-split property. The result does not assert that the first map is left minimal
or that the second map is right almost split.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.2 and V.1.
-/

public section

namespace LinearMap

open TauCeti CategoryTheory CategoryTheory.Abelian

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  [Module.Finite k A] {P₀ P₁ : Type max u v w}
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]

/-- A noninjective Auslander–Reiten translate with local endomorphism ring starts a
short exact sequence with finitely generated middle term and a left almost-split first
map. The presentation need not be minimal, and the field need not be algebraically closed. -/
theorem exists_isLeftAlmostSplit_translate (f : P₁ →ₗ[A] P₀)
    [IsLocalRing (End (ModuleCat.of A (AuslanderReitenTranslate k f)))]
    (hi : ¬ Injective (ModuleCat.of A (AuslanderReitenTranslate k f))) :
    ∃ (E : ModuleCat.{max u v w} A)
      (i : ModuleCat.of A (AuslanderReitenTranslate k f) ⟶ E)
      (p : E ⟶ ModuleCat.of A (P₀ ⧸ range f)) (h : i ≫ p = 0),
      (ShortComplex.mk i p h).ShortExact ∧ Module.Finite A E ∧ IsLeftAlmostSplit i := by
  obtain ⟨α, hα, hkill⟩ := exists_auslanderReitenExt_ne_zero (k := k) f hi
  obtain ⟨E, i, p, h, hS, heq⟩ :=
    (range f).shortExact_quotientShortComplex.exists_extClass_eq _ α
  have hleft : IsLeftAlmostSplit i :=
    hS.isLeftAlmostSplit_f_iff_extClass.mpr ⟨heq ▸ hα, by simpa only [heq] using hkill⟩
  have : Module.Finite A E := Module.Finite.of_exact (f := i.hom) (g := p.hom)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g
  exact ⟨E, i, p, h, hS, inferInstance, hleft⟩

end LinearMap
