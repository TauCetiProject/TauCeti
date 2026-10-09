/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Projection

/-!
# Recovering isomorphisms from the projective stable category

The projective stable quotient detects invertibility and isomorphism classes between
finite-length modules with no nonzero projective retracts. Indecomposability is not required:
the modules may be sums of non-projective indecomposables. This lets stable inverse
comparisons recover actual modules after projective summands have been excluded.

The argument uses Mathlib's Fitting decomposition
`LinearMap.eventually_isCompl_ker_pow_range_pow`. If an endomorphism becomes the identity
in the quotient, its eventual kernel is a projective retract and hence vanishes.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v

variable {A : Type u} [Ring A]

local notation "S" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))

private theorem isIso_of_projectiveStableFunctor_map_eq_id (M : ModuleCat.{v} A)
    (hM : IsFiniteLength A M)
    (hP : ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P)
    (f : End M) (hf : (S).map f = 𝟙 ((S).obj M)) : IsIso f := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (LinearMap.eventually_isCompl_ker_pow_range_pow f.hom)
  let K := LinearMap.ker (f.hom ^ (n + 1))
  have hc := hn (n + 1) (Nat.le_succ n)
  let r : Retract (ModuleCat.of A K) M :=
    { i := ofHom K.subtype
      r := ofHom (K.projectionOnto _ hc)
      retract := by
        ext x
        exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hc x) }
  have hpow : (S).map (f ^ (n + 1)) = 𝟙 ((S).obj M) := by
    have hfe : (S).mapEnd M f = 1 := hf
    have he : (S).mapEnd M (f ^ (n + 1)) = 1 := by rw [map_pow, hfe, one_pow]
    exact he
  have hhom : (f ^ (n + 1)).hom = f.hom ^ (n + 1) :=
    map_pow M.endRingEquiv f (n + 1)
  have hkill : r.i ≫ f ^ (n + 1) = 0 := by
    ext x
    simp [r, hhom]
  have hi : (S).map r.i = 0 := by
    have := congrArg (S).map hkill
    simpa [Functor.map_comp, hpow] using this
  have hzero : IsZero ((S).obj (ModuleCat.of A K)) :=
    (IsZero.iff_id_eq_zero _).mpr (by
      rw [← (S).map_id, ← r.retract, Functor.map_comp, hi, zero_comp])
  have hK : IsZero (ModuleCat.of A K) := hP r
    ((ExactStructure.abelian_isProjective_iff _).mp
      ((ExactStructure.isZero_projectiveStableFunctor_obj_iff _ _).mp hzero))
  have hk : K = ⊥ := Submodule.subsingleton_iff_eq_bot.mp
    (ModuleCat.isZero_iff_subsingleton.mp hK)
  have hu : IsUnit (f.hom ^ (n + 1)) := (Module.End.isUnit_iff _).mpr
    (IsArtinian.bijective_of_injective_endomorphism _ (LinearMap.ker_eq_bot.mp hk))
  exact (isUnit_iff_isIso f).mp
    ((isUnit_pow_succ_iff (n := n)).mp hu |>.map M.endRingEquiv.symm)

/-- The projective stable quotient detects invertibility between finite-length modules
whose projective retracts are all zero. The modules need not be indecomposable. -/
theorem isIso_projectiveStableFunctor_map_iff_of_isZero_projective_retract
    {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hPM : ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P)
    (hPN : ∀ {P : ModuleCat.{v} A}, Retract P N → Projective P → IsZero P) :
    IsIso ((S).map f) ↔ IsIso f := by
  constructor
  · intro hf
    let := hf
    obtain ⟨g, hg⟩ := (S).map_surjective (CategoryTheory.inv ((S).map f))
    have hfg : IsIso (f ≫ g) := isIso_of_projectiveStableFunctor_map_eq_id M hM hPM _ (by
      simp [Functor.map_comp, hg])
    have hgf : IsIso (g ≫ f) := isIso_of_projectiveStableFunctor_map_eq_id N hN hPN _ (by
      simp [Functor.map_comp, hg])
    let := hfg
    let := hgf
    have : Mono f := mono_of_mono f g
    have : Epi f := epi_of_epi g f
    exact isIso_of_mono_of_epi f
  · intro hf
    let := hf
    infer_instance

/-- Stable isomorphism is equivalent to actual isomorphism for finite-length modules
with no nonzero projective retracts. In particular this removes projective ambiguity
without assuming that either module is indecomposable. -/
theorem nonempty_iso_projectiveStableFunctor_obj_iff_of_isZero_projective_retract
    (M N : ModuleCat.{v} A) (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hPM : ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P)
    (hPN : ∀ {P : ModuleCat.{v} A}, Retract P N → Projective P → IsZero P) :
    Nonempty ((S).obj M ≅ (S).obj N) ↔ Nonempty (M ≅ N) := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨f, hf⟩ := (S).map_surjective e.hom
    have : IsIso ((S).map f) := hf.symm ▸ e.isIso_hom
    have : IsIso f :=
      (isIso_projectiveStableFunctor_map_iff_of_isZero_projective_retract
        f hM hN hPM hPN).mp inferInstance
    exact ⟨asIso f⟩
  · exact fun ⟨e⟩ ↦ ⟨(S).mapIso e⟩

end ModuleCat
