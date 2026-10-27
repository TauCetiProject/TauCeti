/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.RingTheory.FiniteLength
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Projective dimension bounds for modules

A common bound on the projective dimensions of simple modules also bounds every
module of finite length. This lets short resolutions of simple modules control higher
Ext groups of arbitrary finite-length modules, without choosing resolutions of their
successive extensions.

Over a principal ideal ring without zero divisors, every module has projective dimension at most
one: a submodule of a projective module is free, and hence projective. This supplies the
hereditary condition in terms of Mathlib's projective-dimension predicate.

For a module of projective dimension at most one, the standard free presentation has
projective kernel and hence is a projective resolution of length one.

The projective dimensions of the cyclic modules `R ⧸ I` bound those of all modules: by Baer's
criterion they bound every injective dimension, and the vanishing of all `Ext^{n+1}(-, N)` then
bounds every projective dimension (Stacks, Lemma 10.109.12 (065T)). This is how a bound on finite
modules over a Noetherian ring becomes a bound on its global dimension.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A bound on the projective dimension of every simple module bounds every module
of finite length. Neither Artinianity of the ring nor finite generation of the ring
over a field is needed. -/
theorem _root_.ModuleCat.hasProjectiveDimensionLT_of_isFiniteLength
    (X : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ S : ModuleCat.{v} R, IsSimpleModule R S → HasProjectiveDimensionLT S n)
    (hX : IsFiniteLength R X) : HasProjectiveDimensionLT X n := by
  -- The induction adapts the proof of `TauCeti.isEulerAdmissible_of_isFiniteLength`
  -- in `TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.FiniteLength`.
  suffices key : ∀ (M : Type v) [AddCommGroup M] [Module R M], IsFiniteLength R M →
      HasProjectiveDimensionLT (ModuleCat.of R M) n from key X hX
  intro M _ _ hM
  induction hM with
  | @of_subsingleton M _ _ _ =>
    let _ := (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le n)
  | @of_simple_quotient M _ _ N _ _ ih =>
    let T : ShortComplex (ModuleCat.{v} R) :=
      ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by
        ext x
        exact (LinearMap.exact_subtype_mkQ N).apply_apply_eq_zero x)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
      (LinearMap.exact_subtype_mkQ N) N.injective_subtype N.mkQ_surjective
    exact hT.hasProjectiveDimensionLT_X₂ n ih
      (h (ModuleCat.of R (M ⧸ N)) inferInstance)

/-- **Global dimension is attained on cyclic modules.** If every cyclic module `R ⧸ I` has
projective dimension at most `n`, then every `R`-module has projective dimension at most `n`.
Stacks, Lemma 10.109.12 (065T). -/
theorem _root_.ModuleCat.hasProjectiveDimensionLE_of_quotients [Small.{v} R] (n : ℕ)
    (h : ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ I))) n)
    (M : ModuleCat.{v} R) : HasProjectiveDimensionLE M n := by
  -- By Baer's criterion every module has injective dimension at most `n` ...
  have hinj (N : ModuleCat.{v} R) : HasInjectiveDimensionLE N n :=
    ModuleCat.hasInjectiveDimensionLE_of_quotients N n fun I ↦
      HasProjectiveDimensionLT.subsingleton _ (n + 1) (n + 1) le_rfl N
  -- ... so every `Ext^{n+1}(M, N)` vanishes.
  exact hasProjectiveDimensionLT_of_enoughInjectives M (n + 1) fun N ↦
    HasInjectiveDimensionLT.subsingleton _ (n + 1) (n + 1) le_rfl M

/-- The standard free presentation of a module of projective dimension at most one
has projective kernel, so it is a projective resolution of length one. -/
theorem projective_projectiveShortComplex_X₁ [Small.{v} R] {M : ModuleCat.{v} R}
    (hM : HasProjectiveDimensionLT M 2) : Projective M.projectiveShortComplex.X₁ := by
  have h₂ : Projective M.projectiveShortComplex.X₂ := inferInstance
  have h₁ := (M.shortExact_projectiveShortComplex.hasProjectiveDimensionLT_X₃_iff 0 h₂).mp hM
  exact projective_iff_hasProjectiveDimensionLT_one.mpr h₁

end TauCeti

namespace ModuleCat

open CategoryTheory

universe u v

/-- Every module over a principal ideal ring without zero divisors has projective dimension at
most one. -/
instance hasProjectiveDimensionLE_one_of_isPrincipalIdealRing {R : Type u} [CommRing R]
    [NoZeroDivisors R] [IsPrincipalIdealRing R] [Small.{v} R] (M : ModuleCat.{v} R) :
    HasProjectiveDimensionLE M 1 := by
  apply (forall_hasProjectiveDimensionLE_one_iff_projective_of_mono (ModuleCat.{v} R)).mpr ?_ M
  intro X Y f _ _
  have : Module.Free R X := Module.Free.of_injective_of_projective_of_isPrincipalIdealRing f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  have : Module.Projective R X := Module.Projective.of_free
  exact ModuleCat.projective_of_categoryTheory_projective X

end ModuleCat
