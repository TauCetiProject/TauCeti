/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Basic
import TauCeti.CategoryTheory.Preadditive.Radical.Basic
import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation

/-!
# Extension classes for almost-split sequences

For a map `f : P₁ → P₀` between finite projectives over a finite-dimensional algebra,
assume that `T = D Tr(f)` has local endomorphism ring and is not injective. There is a
nonzero class in `Ext¹(coker f,T)` killed by pushforward along every map out of `T`
which is not a split monomorphism.

Such a class is the extension-theoretic input for constructing a left almost-split
sequence: vanishing of its pushout is equivalent to factorization through the first
map of a representing short exact sequence. The result constructs the class itself;
it does not choose a representing sequence or assert the right lifting property.

The construction combines `LinearMap.auslanderReitenExtEquiv` with a functional on
injective stable endomorphisms that vanishes on the image of the radical and takes
the value one on the identity. Finite-dimensional biduality turns this functional
into an extension class. The test modules need not be finite-dimensional.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.2 and V.1.
-/

public section

namespace LinearMap

open TauCeti CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  [Module.Finite k A] {P₀ P₁ : Type max u v w}
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]

omit [Module.Finite A P₀] in
private theorem finite_ext_translate (f : P₁ →ₗ[A] P₀) :
    Module.Finite k (Ext (ModuleCat.of A (P₀ ⧸ range f))
      (ModuleCat.of A (AuslanderReitenTranslate k f)) 1) := by
  let T := ModuleCat.of A (AuslanderReitenTranslate k f)
  let := Module.restrictScalars k A P₁
  have := IsScalarTower.restrictScalars k A P₁
  let := Module.Finite.trans (R := k) A P₁
  have : Module.Finite k (AuslanderReitenTranspose f) := Module.Finite.trans Aᵐᵒᵖ _
  have : FiniteDimensional k T :=
    inferInstanceAs (Module.Finite k (Module.Dual k (AuslanderReitenTranspose f)))
  have : Module.Finite A T := Module.Finite.of_restrictScalars_finite k A T
  -- Bundle the inherited dual action before using ModuleCat's algebra scalars.
  -- Its compHom scalar instance must also be selected for the unbundled SMul class.
  let : Module A T := T.isModule
  let : Module k T := Module.compHom T (algebraMap k A)
  let : SMul k T := (Module.compHom T (algebraMap k A)).toSMul
  have : IsScalarTower k A T :=
    ModuleCat.Algebra.instIsScalarTowerCarrier (S₀ := k) (S := A) (M := T)
  have : Module.Finite k T := Module.Finite.trans A T
  exact finiteDimensional_ext_cokernel (K := k) f T

/-- A noninjective translate with local endomorphism ring admits a nonzero extension
class annihilated by every pushforward along a map that is not a split monomorphism.
No minimality of the presentation or algebraic closedness of the field is required. -/
theorem exists_auslanderReitenExt_ne_zero (f : P₁ →ₗ[A] P₀)
    [IsLocalRing (End (ModuleCat.of A (AuslanderReitenTranslate k f)))]
    (hi : ¬ Injective (ModuleCat.of A (AuslanderReitenTranslate k f))) :
    ∃ α : Ext (ModuleCat.of A (P₀ ⧸ range f))
        (ModuleCat.of A (AuslanderReitenTranslate k f)) 1,
      α ≠ 0 ∧ ∀ (N : ModuleCat.{max u v w} A)
        (g : ModuleCat.of A (AuslanderReitenTranslate k f) ⟶ N),
        ¬ IsSplitMono g → α.comp (Ext.mk₀ g) (add_zero 1) = 0 := by
  classical
  let T := ModuleCat.of A (AuslanderReitenTranslate k f)
  let F := (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor
  let : Module k (T ⟶ T) := Linear.homModule (R := k) T T
  let q := F.mapLinearMap k (X := T) (Y := T)
  let R := (jacobsonRadicalSubmodule k T T).map q
  -- The stable identity cannot be radical: identity minus a radical endomorphism
  -- is invertible, and an invertible map killed by the quotient makes T injective.
  have hid : R.mkQ (F.map (𝟙 T)) ≠ 0 := by
    intro hzero
    obtain ⟨r, hr, heq⟩ := Submodule.mem_map.mp ((Submodule.Quotient.mk_eq_zero R).mp hzero)
    have hiso : IsIso (𝟙 T - r) := by
      simpa using
        (mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp
          (mem_jacobsonRadicalSubmodule.mp hr)) (𝟙 T)
    have hmap : F.map (𝟙 T - r) = 0 :=
      F.map_sub.trans (sub_eq_zero.mpr heq.symm)
    have : IsIso (0 : F.obj T ⟶ F.obj T) := hmap ▸ F.map_isIso (𝟙 T - r)
    apply hi
    apply (ExactStructure.abelian_isInjective_iff T).mp
    apply (ExactStructure.isZero_injectiveStableFunctor_obj_iff _ T).mp
    exact (Limits.IsZero.iff_id_eq_zero _).mpr (Limits.isIsoZeroSelfEquiv _ this)
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_eq_one k hid
  let φ := χ.comp R.mkQ
  have hφ (r : T ⟶ T) (hr : r ∈ jacobsonRadical T T) : φ (F.map r) = 0 := by
    have hmem : F.map r ∈ R := ⟨r, mem_jacobsonRadicalSubmodule.mpr hr, rfl⟩
    simp only [φ, comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero R).mpr hmem, map_zero]
  -- All the Hom cocycles, and hence Ext¹, are finite-dimensional. This is the
  -- finiteness needed to realize the functional by an actual extension class.
  let E := Ext (ModuleCat.of A (P₀ ⧸ range f)) T 1
  have := finite_ext_translate (k := k) f
  let e := auslanderReitenExtEquiv (k := k) f T
  let α := (Module.evalEquiv k E).symm (φ.comp e.symm.toLinearMap)
  have hα (h : F.obj T ⟶ F.obj T) : e h α = φ h := by
    exact (Module.apply_evalEquiv_symm_apply k E (e h) (φ.comp e.symm.toLinearMap)).trans
      (by simp)
  refine ⟨α, ?_, ?_⟩
  · intro hz
    have h := hα (F.map (𝟙 T))
    simp only [hz, map_zero] at h
    exact zero_ne_one (h.trans hχ)
  · intro N g hg
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro ψ
    let eN := auslanderReitenExtEquiv (k := k) f N
    let h := eN.symm ψ
    have hh : eN h = ψ := eN.apply_symm_apply ψ
    rw [← hh, ← auslanderReitenExtEquiv_naturality, hα]
    obtain ⟨a, ha⟩ := F.map_surjective h
    rw [← ha, ← Functor.map_comp]
    exact hφ _ (comp_mem_jacobsonRadical_right
      (mem_jacobsonRadical_iff_not_isSplitMono.mpr hg) a)

end LinearMap
