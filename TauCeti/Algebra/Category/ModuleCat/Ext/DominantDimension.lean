/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.RingTheory.DominantDimension
import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.RingTheory.Artinian.Module

/-!
# The Ext criterion for dominant dimension

Over a left Artinian ring `A` of positive left dominant dimension, a finitely generated module
`M` has dominant dimension at least `n` exactly when `Extⁱ(T, M) = 0` for every `i < n` and
every finitely generated `T` with `Hom(T, A) = 0`. In degree zero this tests whether `M` embeds
into a finite power of a projective-injective module containing the regular module.
The higher degrees follow by dimension shifting along a projective-injective coresolution.

For the regular module the degree-zero test already holds. This gives the projective version of
Hoshino's criterion used in the proof of left-right symmetry of dominant dimension.

## References

* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280,
  Lemma 2.2, in its left Artinian case.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TauCeti

universe u v

namespace ModuleCat

/-- All Ext groups from a module with zero regular-module dual to a projective-injective module
vanish, including in degree zero. -/
theorem subsingleton_ext_of_projective_of_injective {A : Type u} [Ring A] [Small.{v} A]
    {T I : ModuleCat.{v} A} [Projective I] [Injective I]
    (hT : Subsingleton (T →ₗ[A] A)) (i : ℕ) : Subsingleton (Ext T I i) := by
  cases i with
  | succ i => exact Ext.subsingleton_of_injective T I i
  | zero =>
    apply Ext.addEquiv₀.subsingleton_congr.mpr
    have : Module.Projective A I := ModuleCat.projective_of_module_projective I
    obtain ⟨s, hs⟩ := (Module.projective_def (R := A) (P := I)).mp inferInstance
    refine subsingleton_of_forall_eq 0 fun f ↦ ?_
    ext x
    apply hs.injective
    ext j
    have h := hT.elim ((Finsupp.lapply j).comp (s.comp f.hom)) 0
    simpa using LinearMap.congr_fun h x

variable {A : Type u} [Ring A]

/-- A projective-injective embedding of the regular module lets the degree-zero case of the
Ext criterion detect which finitely generated modules admit a projective-injective embedding. -/
private theorem exists_mono_projective_injective_of_hom [IsArtinianRing A]
    (hA : 1 ≤ TauCeti.dominantDimension A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : ∀ (T : ModuleCat.{u} A) [Module.Finite A T],
      Subsingleton (T →ₗ[A] A) → Subsingleton (T ⟶ M)) :
    ∃ (I : ModuleCat.{u} A) (j : M ⟶ I), Mono j ∧ Module.Finite A I ∧
      Projective I ∧ Injective I := by
  obtain ⟨J, j, hj, hJ, hP, hI⟩ := ObjectProperty.isSyzygy_one_iff.mp
    ((TauCeti.natCast_le_dominantDimension_iff A 1).mp (by simpa using hA))
  have : Module.Injective A J := Module.injective_module_of_injective_object A J
  have : Module.Projective A J := ModuleCat.projective_of_module_projective J
  obtain ⟨k, g, hg⟩ := IsArtinian.exists_injective_linearMap_pi (R := A) (M := M) (E := J)
    fun x hx ↦ by
      let S : Submodule A M := A ∙ x
      let T := ModuleCat.of A S
      have : Module.Finite A T := Module.Finite.span_singleton A x
      let ι : T ⟶ M := ModuleCat.ofHom S.subtype
      let y : S := ⟨x, Submodule.mem_span_singleton_self x⟩
      have hnz : ∃ f : T →ₗ[A] A, f ≠ 0 := by
        by_contra! h
        have hι := (hM T (subsingleton_of_forall_eq 0 h)).elim ι 0
        apply hx
        calc
          x = ι.hom y := rfl
          _ = 0 := by simpa using congrArg (fun g : T ⟶ M ↦ g.hom y) hι
      obtain ⟨f, hf⟩ := hnz
      have hj' := (ModuleCat.mono_iff_injective j).mp hj
      obtain ⟨g, hg⟩ := Module.Injective.extension_property A J S M S.subtype
        S.injective_subtype (j.hom.comp f)
      refine ⟨g, fun hgx ↦ hf ?_⟩
      apply (Submodule.linearMap_eq_zero_iff_of_eq_span f (S := {x}) (rfl : S = A ∙ x)).mpr
      rintro ⟨z, hz⟩
      have hz' : z = x := hz
      subst z
      apply hj'
      simpa [hgx, y] using (LinearMap.congr_fun hg y).symm
  exact ⟨ModuleCat.of A (Fin k → J), ModuleCat.ofHom g,
    (ModuleCat.mono_iff_injective _).mpr hg, inferInstance,
    (IsProjective.iff_projective (R := A) _).mp inferInstance,
    Module.injective_object_of_injective_module _ _⟩

/-- Dimension shifting for the Ext test, starting in degree zero since the middle module is
both projective and injective. -/
private theorem subsingleton_ext_cokernel_iff {T M I : ModuleCat.{u} A} (f : M ⟶ I)
    [Mono f] [Projective I] [Injective I] (hT : Subsingleton (T →ₗ[A] A)) (i : ℕ) :
    Subsingleton (Ext T (cokernel f) i) ↔ Subsingleton (Ext T M (i + 1)) := by
  -- Use the explicit short complex to keep its middle object reducibly equal to `I`.
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have h : S.ShortExact := cokernelSequence_shortExact f
  have : Injective S.X₂ := ‹Injective I›
  refine ⟨fun h₀ ↦ subsingleton_ext_succ_of_comp_extClass_eq_zero h T i
    (fun x ↦ by rw [h₀.elim x 0, Ext.zero_comp]), fun h₁ ↦ ?_⟩
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ T h x rfl (h₁.elim _ _)
  have hmid := subsingleton_ext_of_projective_of_injective (I := I) hT i
  rw [hmid.elim y 0, Ext.zero_comp]

/-- Over a left Artinian ring of positive dominant dimension, the cutoff `n` for a finitely
generated module is equivalent to Ext vanishing in degrees below `n` against all finitely
generated modules with zero regular-module dual. -/
theorem natCast_le_dominantDimension_iff_ext [IsArtinianRing A]
    (hA : 1 ≤ TauCeti.dominantDimension A) (M : ModuleCat.{u} A) [Module.Finite A M] (n : ℕ) :
    (n : ℕ∞) ≤ dominantDimension M ↔
      ∀ (T : ModuleCat.{u} A) [Module.Finite A T], Subsingleton (T →ₗ[A] A) →
        ∀ i < n, Subsingleton (Ext T M i) := by
  rw [natCast_le_dominantDimension_iff_of_finite]
  induction n generalizing M with
  | zero => simp [ObjectProperty.isSyzygy_zero]
  | succ n ih =>
    rw [ObjectProperty.isSyzygy_succ_iff_exists_mono]
    have finiteCokernel {M I : ModuleCat.{u} A} [Module.Finite A I] (f : M ⟶ I) :
        Module.Finite A (cokernel f : ModuleCat.{u} A) :=
      Module.Finite.of_surjective (cokernel.π f).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    constructor
    · rintro ⟨I, f, hf, ⟨hfin, hP, hI⟩, hc⟩ T hfinT hT (i | i) hi
      · have := subsingleton_ext_of_projective_of_injective (I := I) hT 0
        exact ⟨fun x y ↦ Ext.postcomp_mk₀_injective_of_mono T f (Subsingleton.elim _ _)⟩
      · have := finiteCokernel f
        exact (subsingleton_ext_cokernel_iff f hT i).mp
          ((ih _).mp hc T hT i (Nat.lt_of_succ_lt_succ hi))
    · intro h
      obtain ⟨I, f, hf, hfin, hP, hI⟩ := exists_mono_projective_injective_of_hom hA M
        fun T _ hT ↦ Ext.addEquiv₀.subsingleton_congr.mp (h T hT 0 (Nat.zero_lt_succ n))
      have := finiteCokernel f
      exact ⟨I, f, hf, ⟨hfin, hP, hI⟩, (ih _).mpr fun T _ hT i hi ↦
        (subsingleton_ext_cokernel_iff f hT i).mpr (h T hT (i + 1) (Nat.succ_lt_succ hi))⟩

end ModuleCat

namespace TauCeti

/-- **Hoshino's criterion for left Artinian rings.** If the left dominant dimension is positive,
the cutoff `n + 1` holds exactly when `Extⁱ(T, A)` vanishes for `1 ≤ i ≤ n` and every finitely
generated left module `T` with zero regular-module dual. -/
theorem succ_le_dominantDimension_iff_ext {A : Type u} [Ring A] [IsArtinianRing A]
    (hA : 1 ≤ dominantDimension A) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ dominantDimension A ↔
      ∀ (T : ModuleCat.{u} A) [Module.Finite A T], Subsingleton (T →ₗ[A] A) →
        ∀ i < n, Subsingleton (Ext T (ModuleCat.of A A) (i + 1)) := by
  rw [dominantDimension_eq_dominantDimension_of, ModuleCat.natCast_le_dominantDimension_iff_ext hA]
  refine ⟨fun h T _ hT i hi ↦ h T hT (i + 1) (Nat.succ_lt_succ hi), ?_⟩
  rintro h T hfin hT (i | i) hi
  · exact Ext.addEquiv₀.subsingleton_congr.mpr
      (ModuleCat.homEquiv.subsingleton_congr.mpr hT)
  · exact h T hT i (Nat.lt_of_succ_lt_succ hi)

end TauCeti
