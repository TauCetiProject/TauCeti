/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Projection

/-!
# Recovering isomorphisms from a quotient of finite-length modules

Let `F` be a full functor out of `ModuleCat A` that preserves zero morphisms, such as the quotient
functor to the projective or the injective stable category. Suppose that for finite-length modules
`M` and `N`, every retract of `M` or of `N` that `F` sends to zero is zero. Then `F` detects
invertibility of maps `M ⟶ N`, and `M ≅ N` as soon as `F M ≅ F N`. Indecomposability is not
required.

The argument uses Mathlib's Fitting decomposition `LinearMap.eventually_isCompl_ker_pow_range_pow`.
If an endomorphism `f` of `M` becomes the identity under `F`, the eventual kernel of `f` is a
retract of `M` killed by `F`, hence zero, so `f` is invertible.

## Main results

* `ModuleCat.isIso_map_iff_of_isZero_retract`: `F` detects invertibility.
* `ModuleCat.nonempty_iso_obj_iff_of_isZero_retract`: `F` detects isomorphism classes.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {A : Type u} [Ring A] {D : Type*} [Category* D] [HasZeroMorphisms D]
  (F : ModuleCat.{v} A ⥤ D)

private theorem isIso_of_map_eq_id [F.PreservesZeroMorphisms] (M : ModuleCat.{v} A)
    (hM : IsFiniteLength A M)
    (hZ : ∀ {K : ModuleCat.{v} A}, Retract K M → IsZero (F.obj K) → IsZero K) (f : End M)
    (hf : F.map f.asHom = 𝟙 (F.obj M)) : IsIso f.asHom := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (LinearMap.eventually_isCompl_ker_pow_range_pow f.asHom.hom)
  let K := LinearMap.ker (f.asHom.hom ^ (n + 1))
  have hc := hn (n + 1) (Nat.le_succ n)
  let r : Retract (ModuleCat.of A K) M :=
    { i := ofHom K.subtype
      r := ofHom (K.projectionOnto _ hc)
      retract := by
        ext x
        exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hc x) }
  have hpow : F.map (f ^ (n + 1)).asHom = 𝟙 (F.obj M) := by
    have hfe : F.mapEnd M f = 1 := End.ext hf
    have he : F.mapEnd M (f ^ (n + 1)) = 1 := by rw [map_pow, hfe, one_pow]
    exact congrArg End.asHom he
  have hhom : (f ^ (n + 1)).asHom.hom = f.asHom.hom ^ (n + 1) :=
    map_pow M.endRingEquiv f (n + 1)
  have hkill : r.i ≫ (f ^ (n + 1)).asHom = 0 := by
    ext x
    simp [r, hhom]
  have hi : F.map r.i = 0 := by
    have := congrArg F.map hkill
    simpa [Functor.map_comp, hpow] using this
  have hK : IsZero (ModuleCat.of A K) := hZ r ((IsZero.iff_id_eq_zero _).mpr (by
    rw [← F.map_id, ← r.retract, Functor.map_comp, hi, zero_comp]))
  have hk : K = ⊥ := Submodule.subsingleton_iff_eq_bot.mp
    (ModuleCat.isZero_iff_subsingleton.mp hK)
  have hu : IsUnit (f.asHom.hom ^ (n + 1)) := (Module.End.isUnit_iff _).mpr
    (IsArtinian.bijective_of_injective_endomorphism _ (LinearMap.ker_eq_bot.mp hk))
  exact (isUnit_iff_isIso f).mp
    ((isUnit_pow_succ_iff (n := n)).mp hu |>.map M.endRingEquiv.symm)

variable [F.Full] [F.PreservesZeroMorphisms]

/-- **A quotient detects invertibility between finite-length modules**: if a full functor `F`
preserving zero morphisms sends no nonzero retract of `M` or of `N` to zero, a map `M ⟶ N` is
invertible exactly when its image under `F` is. -/
theorem isIso_map_iff_of_isZero_retract {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hZM : ∀ {K : ModuleCat.{v} A}, Retract K M → IsZero (F.obj K) → IsZero K)
    (hZN : ∀ {K : ModuleCat.{v} A}, Retract K N → IsZero (F.obj K) → IsZero K) :
    IsIso (F.map f) ↔ IsIso f := by
  refine ⟨fun hf ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨g, hg⟩ := F.map_surjective (inv (F.map f))
  have := isIso_of_map_eq_id F M hM hZM (End.of (f ≫ g)) (by simp [hg])
  have := isIso_of_map_eq_id F N hN hZN (End.of (g ≫ f)) (by simp [hg])
  have : Mono f := mono_of_mono f g
  have : Epi f := epi_of_epi g f
  exact isIso_of_mono_of_epi f

/-- **A quotient detects isomorphism classes of finite-length modules**: under the hypotheses of
`ModuleCat.isIso_map_iff_of_isZero_retract`, `F M ≅ F N` exactly when `M ≅ N`. -/
theorem nonempty_iso_obj_iff_of_isZero_retract (M N : ModuleCat.{v} A)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hZM : ∀ {K : ModuleCat.{v} A}, Retract K M → IsZero (F.obj K) → IsZero K)
    (hZN : ∀ {K : ModuleCat.{v} A}, Retract K N → IsZero (F.obj K) → IsZero K) :
    Nonempty (F.obj M ≅ F.obj N) ↔ Nonempty (M ≅ N) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ⟨F.mapIso e⟩⟩
  obtain ⟨f, hf⟩ := F.map_surjective e.hom
  have : IsIso (F.map f) := hf.symm ▸ e.isIso_hom
  have := (isIso_map_iff_of_isZero_retract F f hM hN hZM hZN).1 this
  exact ⟨asIso f⟩

end ModuleCat
