/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.RingTheory.Deformation.ArtinLocalAlg
public import TauCeti.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Factoring surjections into small extensions

A small extension of the Artinian coefficient category `C_Λ` is a surjection `A' → A` whose
kernel is a nonzero principal ideal annihilated by the maximal ideal of `A'`. Equivalently, its
kernel is a minimal nonzero ideal of `A'` (`isSmallExtension_iff_isAtom_ker`), that is, a simple
`A'`-module. In particular the kernel of a small extension has square zero
(`IsSmallExtension.ker_sq_eq_bot`).

Every surjection `f : B → A` of `C_Λ` with nonzero kernel is a finite composite of small
extensions (Stacks, Lemma 90.3.3 (06GE)). We state this as membership of `f` in the
multiplicative closure of the class `smallExtension` of small extensions
(`multiplicativeClosure_smallExtension`); conversely, every morphism in this closure is
surjective. This is how properties of deformation functors are reduced from arbitrary surjections
to small extensions, for instance Schlessinger's condition `(H1)` (Stacks, Lemma 90.10.2 (06HX)).

## Main definitions

* `TauCeti.Deformation.ArtinLocalAlg.smallExtension`: the class of small extensions, as a
  morphism property of `C_Λ`.

## Main results

* `TauCeti.Deformation.ArtinLocalAlg.isSmallExtension_iff_isAtom_ker`: a morphism of `C_Λ` is a
  small extension exactly when it is surjective and its kernel is a minimal nonzero ideal.
* `TauCeti.Deformation.ArtinLocalAlg.IsSmallExtension.ker_sq_eq_bot`: the kernel of a small
  extension has square zero.
* `TauCeti.Deformation.ArtinLocalAlg.isSmallExtension_quotientLift`: if `J` is covered by the
  kernel of a surjection `f : B ⟶ A`, the induced map `B ⧸ J ⟶ A` is a small extension.
* `TauCeti.Deformation.ArtinLocalAlg.multiplicativeClosure_smallExtension`: every surjection of
  `C_Λ` with nonzero kernel is a composite of small extensions.
* `TauCeti.Deformation.ArtinLocalAlg.multiplicativeClosure_smallExtension_iff`: a morphism with
  nonzero kernel is a composite of small extensions exactly when it is surjective.

## Implementation notes

The factorisation is built from the target end: if `J` is an ideal of `B` covered by
`I = ker f`, then `f` factors as the quotient map `B → B ⧸ J` followed by the map
`B ⧸ J → A`, and the latter is a small extension because its kernel `I ⧸ J` is a minimal nonzero
ideal of `B ⧸ J`. Such `J` exists since `B` is Noetherian, and the induction on `I` terminates
since `B` is Artinian.

## References

* [Stacks Project, Lemma 90.3.3 (06GE)](https://stacks.math.columbia.edu/tag/06GE)
* M. Schlessinger, *Functors of Artin rings*, Trans. Amer. Math. Soc. 130 (1968), 208–222, §1.
-/

public section

open CategoryTheory IsLocalRing

universe u v

namespace TauCeti.Deformation.ArtinLocalAlg

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]

/-- A morphism of `C_Λ` is a small extension exactly when it is surjective and its kernel is a
minimal nonzero ideal, that is, a simple module. -/
theorem isSmallExtension_iff_isAtom_ker {A' A : ArtinLocalAlg Λ k} (f : A' ⟶ A) :
    IsSmallExtension f ↔
      Function.Surjective f.hom.left.hom ∧ IsAtom (RingHom.ker f.hom.left.hom) := by
  rw [isSmallExtension_iff]
  refine and_congr_right fun _ ↦ ⟨fun ⟨t, ht0, hker, hmul⟩ ↦ ?_, fun hatom ↦ ?_⟩
  · rw [hker, isAtom_iff_le_of_ge]
    refine ⟨by rwa [Ne, Ideal.span_singleton_eq_bot], fun L hL hLt ↦ ?_⟩
    -- A nonzero element `c * t` of `L` has `c` a unit, since `𝔪` kills `t`; so `t ∈ L`.
    obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hLt hxL)
    have hc : IsUnit c := notMem_maximalIdeal.mp fun hc ↦ hx0 (hmul c hc)
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [← mul_assoc] using L.mul_mem_left (↑hc.unit⁻¹ : A'.obj.left) hxL
  · obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hatom.1
    have hspan : Ideal.span {t} = RingHom.ker f.hom.left.hom :=
      (hatom.le_iff.mp ((Ideal.span_singleton_le_iff_mem _).mpr ht)).resolve_left
        (by rwa [Ideal.span_singleton_eq_bot])
    refine ⟨t, ht0, hspan.symm, fun x hx ↦ ?_⟩
    rw [← Ideal.mem_bot, ← hatom.maximalIdeal_mul_eq_bot]
    exact Ideal.mul_mem_mul hx ht

/-- The kernel of a small extension is a minimal nonzero ideal. -/
theorem IsSmallExtension.isAtom_ker {A' A : ArtinLocalAlg Λ k} {f : A' ⟶ A}
    (hf : IsSmallExtension f) : IsAtom (RingHom.ker f.hom.left.hom) :=
  ((isSmallExtension_iff_isAtom_ker f).mp hf).2

/-- The kernel of a small extension has square zero. -/
theorem IsSmallExtension.ker_sq_eq_bot {A' A : ArtinLocalAlg Λ k} {f : A' ⟶ A}
    (hf : IsSmallExtension f) : RingHom.ker f.hom.left.hom ^ 2 = ⊥ := by
  have hle : RingHom.ker f.hom.left.hom ≤ maximalIdeal A'.obj.left :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  rw [eq_bot_iff, ← hf.maximalIdeal_mul_ker, sq]
  exact Ideal.mul_mono_left hle

/-- If the kernel of a surjection `f : B ⟶ A` of `C_Λ` covers an ideal `J` of `B`, the induced
morphism `B ⧸ J ⟶ A` is a small extension: its kernel `ker f ⧸ J` is a minimal nonzero ideal. -/
theorem isSmallExtension_quotientLift {A B : ArtinLocalAlg Λ k} {f : B ⟶ A}
    (hf : Function.Surjective f.hom.left.hom) {J : Ideal B.obj.left}
    (hJ : J ⋖ RingHom.ker f.hom.left.hom) :
    IsSmallExtension (quotientLift (hI := hJ.lt.ne_top) f hJ.le) := by
  rw [isSmallExtension_iff_isAtom_ker, ker_quotientLift, toQuotient_hom_left_hom]
  exact ⟨quotientLift_surjective _ hf, (Ideal.isAtom_map_mk_iff_covBy hJ.le).mpr hJ⟩

variable (Λ k) in
/-- The class of small extensions, as a morphism property of `C_Λ`. -/
def smallExtension : MorphismProperty (ArtinLocalAlg Λ k) :=
  fun _ _ f ↦ IsSmallExtension f

/-- A morphism belongs to `smallExtension Λ k` exactly when it is a small extension. -/
@[simp]
theorem smallExtension_iff {A' A : ArtinLocalAlg Λ k} (f : A' ⟶ A) :
    smallExtension Λ k f ↔ IsSmallExtension f :=
  Iff.rfl

/-- **Factorisation into small extensions.** Every surjection `f : B ⟶ A` of `C_Λ` with nonzero
kernel is a finite composite of small extensions. Stacks, Lemma 90.3.3 (06GE). -/
theorem multiplicativeClosure_smallExtension {A B : ArtinLocalAlg Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom.left.hom) (hker : RingHom.ker f.hom.left.hom ≠ ⊥) :
    (smallExtension Λ k).multiplicativeClosure f := by
  -- Well-founded induction on the kernel, among the ideals of the Artinian ring `B`.
  induction hI : RingHom.ker f.hom.left.hom using WellFoundedLT.induction generalizing A with
  | ind I ih =>
  subst hI
  -- Choose `J` covered by `ker f`, which exists as `B` is Noetherian.
  obtain ⟨J, -, hJ⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr hker)
  obtain rfl | hJ0 := eq_or_ne J ⊥
  · exact .of _ ((isSmallExtension_iff_isAtom_ker f).mpr ⟨hf, bot_covBy_iff.mp hJ⟩)
  · -- `f` factors as `B ⟶ B ⧸ J`, of kernel `J < ker f`, followed by a small extension.
    rw [← toQuotient_comp_quotientLift (hI := hJ.lt.ne_top) f hJ.le]
    exact .comp_of _ _ (ih J hJ.lt _ (toQuotient_surjective _ _ _)
      (by rwa [ker_toQuotient]) (ker_toQuotient _ _ _)) (isSmallExtension_quotientLift hf hJ)

/-- Every composite of small extensions is surjective. -/
theorem surjective_of_multiplicativeClosure_smallExtension {A B : ArtinLocalAlg Λ k} {f : B ⟶ A}
    (hf : (smallExtension Λ k).multiplicativeClosure f) : Function.Surjective f.hom.left.hom := by
  induction hf with
  | of _ hf => exact hf.surjective
  | id _ => exact Function.surjective_id
  | comp_of _ _ _ hg ih => exact hg.surjective.comp ih

/-- A morphism of `C_Λ` with nonzero kernel is a composite of small extensions exactly when it is
surjective. -/
theorem multiplicativeClosure_smallExtension_iff {A B : ArtinLocalAlg Λ k} (f : B ⟶ A)
    (hker : RingHom.ker f.hom.left.hom ≠ ⊥) :
    (smallExtension Λ k).multiplicativeClosure f ↔ Function.Surjective f.hom.left.hom :=
  ⟨surjective_of_multiplicativeClosure_smallExtension,
    fun hf ↦ multiplicativeClosure_smallExtension f hf hker⟩

end TauCeti.Deformation.ArtinLocalAlg
