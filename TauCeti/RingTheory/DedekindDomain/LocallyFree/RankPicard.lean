/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Ring
public import TauCeti.RingTheory.DedekindDomain.LocallyFree.K0
public import TauCeti.RingTheory.PicardGroup.ClassGroup
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Invertible
import TauCeti.LinearAlgebra.Dimension.Pi
import TauCeti.RingTheory.FractionalIdeal.Operations

/-!
# The ring structure of projective `K₀` of a Dedekind domain

For a Dedekind domain `A`, rank and Steinitz class identify projective `K₀(A)` additively with
`ℤ × Cl(A)` (`TauCeti.FiniteProjectiveModules.rankSteinitzEquiv`). The tensor product makes
`K₀(A)` a commutative ring, and this file identifies that ring: it is the trivial square-zero
extension of `ℤ` by the ideal class group,

```text
K₀(A) ≃+* ℤ ⋉ Cl(A),   [P] ↦ (rank P, st(P)),   (n, c) ↦ n + ([I] - [A]) for I of class c,
```

so `(m, c) * (n, d) = (mn, m d + n c)`. Through `ClassGroup.equivPic` the same ring is
`ℤ ⋉ Pic(A)`, where the class of an invertible module `L` goes to `(1, L)`.

The only new input is that the reduced classes multiply to zero:
`([I] - [A]) ([J] - [A]) = 0` for invertible fractional ideals `I` and `J`, over any Noetherian
domain of dimension at most one. Indeed
`I ⊗[A] J ≃ IJ`, so the left side is `[IJ] - [I] - [J] + [A]`, which vanishes by the product
identity `I ⊕ J ≃ A ⊕ IJ` (`TauCeti.FiniteProjectiveModules.classOf_mul`). Hence the rank-zero
part of `K₀(A)` squares to zero. As a consequence the Steinitz class of a tensor product is
`st(M ⊗ N) = st(M) ^ rank N * st(N) ^ rank M` (`Module.steinitzClass_tensorProduct`).

The Picard coordinates are natural for every ring homomorphism `f : A →+* B` of Dedekind domains,
not only for injective ones: extension of scalars is `(n, L) ↦ (n, f* L)`, with
`f* L = CommRing.Pic.mapRingHom f L` the extended line. Indeed `(n, L)` is the class
`(n - 1) [A] + [L]`, and extension of scalars sends `[A]` to `[B]` and `[L]` to `[f* L]`; this
description of the extended class holds for any commutative ring `B`. For instance, along the
map to a residue field, every Picard class dies and only the rank survives.

The ring structure of `TrivSqZeroExt ℤ M` uses a right action of `ℤ` on `M`, which Mathlib does
not provide for an arbitrary abelian group `M` (for `M = ℤ` it would compete with the action by
right multiplication). The ring isomorphisms below therefore take this action as an instance
argument, together with `IsCentralScalar ℤ M`. Any two such actions agree, since an additive group
carries only one module structure over `ℤᵐᵒᵖ`, as over `ℤ`; `Module.compHom` along
`RingHom.fromOpposite` supplies one.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankSteinitzRingEquiv`: the ring isomorphism
  `K₀(A) ≃+* TrivSqZeroExt ℤ (Additive (ClassGroup A))`.
* `TauCeti.FiniteProjectiveModules.rankPicRingEquiv`: the ring isomorphism
  `K₀(A) ≃+* TrivSqZeroExt ℤ (Additive (CommRing.Pic A))`.

## Main results

* `TauCeti.FiniteProjectiveModules.idealClassHom_mul_idealClassHom`: reduced ideal classes
  multiply to zero.
* `TauCeti.FiniteProjectiveModules.mul_eq_zero_of_rankSteinitz_fst_eq_zero`: classes of rank zero
  multiply to zero.
* `TauCeti.FiniteProjectiveModules.rankPicRingEquiv_of_fin` and
  `TauCeti.FiniteProjectiveModules.rankPicRingEquiv_of_pic`: the normalizations `[Aⁿ] ↦ (n, 1)` and
  `[L] ↦ (1, L)`.
* `TauCeti.FiniteProjectiveModules.rankPicRingEquiv_map_extendScalars`: naturality of the
  rank–Picard isomorphism along any ring homomorphism of Dedekind domains.
* `TauCeti.FiniteProjectiveModules.map_extendScalars_rankPicRingEquiv_symm`: extension of scalars
  to any commutative ring sends the class with coordinates `(n, L)` to `(n - 1) [B] + [f* L]`.
* `TauCeti.FiniteProjectiveModules.map_extendScalars_eq_rankSteinitz_fst`: extension of scalars
  to a commutative ring with trivial Picard group only remembers the rank.
* `Module.steinitzClass_tensorProduct`: the Steinitz class of a tensor product.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter II, Corollary 2.6.3,
  and Chapter I, Proposition 3.4.
-/

public section

open scoped nonZeroDivisors TensorProduct
open CategoryTheory CommRing

namespace TauCeti

universe u

namespace FiniteProjectiveModules

variable {A : Type u} [CommRing A]

section OneDimensional

variable [IsNoetherianRing A] [Ring.DimensionLEOne A]

/-- The reduced classes `[I] - [A]` and `[J] - [A]` of invertible fractional ideals multiply to
zero in projective `K₀`. -/
theorem classOf_mul_classOf {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (I J : (FractionalIdeal A⁰ K)ˣ) :
    classOf A (I : FractionalIdeal A⁰ K) 1 * classOf A (J : FractionalIdeal A⁰ K) 1 = 0 := by
  have : IsDomain A := IsDomain.of_faithfulSMul A K
  let : Module.Finite A (↑I * ↑J : FractionalIdeal A⁰ K) :=
    inferInstanceAs (Module.Finite A ((I * J : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
  let : Module.Projective A (↑I * ↑J : FractionalIdeal A⁰ K) :=
    inferInstanceAs (Module.Projective A ((I * J : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
  -- `[I] [J] = [I ⊗ J] = [IJ]`.
  have hIJ : SplitK0.of.{u} (of A (I : FractionalIdeal A⁰ K)) *
      SplitK0.of.{u} (of A (J : FractionalIdeal A⁰ K)) =
      SplitK0.of.{u} (of A ((I * J : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) := by
    rw [← splitK0_of_tensorProduct]
    exact SplitK0.of_congr
      (ObjectProperty.isoMk _ (FractionalIdeal.tensorEquivMul I J).toModuleIso)
  -- `[IJ] - [A] = ([I] - [A]) + ([J] - [A])`.
  have h := classOf_mul I J
  simp only [classOf_def, one_smul, splitK0_of_self] at h ⊢
  linear_combination hIJ + h

variable (A) [IsDomain A] in
/-- **Reduced ideal classes multiply to zero.** For ideal classes `c` and `d`, the product of the
reduced classes `[I] - [A]` and `[J] - [A]` in projective `K₀(A)` is zero. -/
theorem idealClassHom_mul_idealClassHom (c d : Additive (ClassGroup A)) :
    idealClassHom A c * idealClassHom A d = 0 := by
  induction c using Additive.rec with | ofMul c =>
  induction d using Additive.rec with | ofMul d =>
  refine ClassGroup.induction (FractionRing A) (fun I ↦ ?_) c
  refine ClassGroup.induction (FractionRing A) (fun J ↦ ?_) d
  rw [idealClassHom_mk, idealClassHom_mk]
  exact classOf_mul_classOf I J

end OneDimensional

variable (A) [IsDedekindDomain A]

variable {A} in
/-- Classes of rank zero in projective `K₀` of a Dedekind domain multiply to zero. -/
theorem mul_eq_zero_of_rankSteinitz_fst_eq_zero
    {x y : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory}
    (hx : (rankSteinitz A x).1 = 0) (hy : (rankSteinitz A y).1 = 0) : x * y = 0 := by
  obtain ⟨c, rfl⟩ := (mem_range_idealClassHom_iff A).mpr hx
  obtain ⟨d, rfl⟩ := (mem_range_idealClassHom_iff A).mpr hy
  exact idealClassHom_mul_idealClassHom A c d

section RingEquiv

variable {M : Type*} [AddCommGroup M] [Module ℤᵐᵒᵖ M] [IsCentralScalar ℤ M]

/-- The ring isomorphism `K₀(A) ≃+* ℤ ⋉ M` for an abelian group `M` identified with the ideal class
group by `φ`. Its inverse sends `(n, m)` to `n + idealClassHom A (φ m)`. -/
private noncomputable def ringEquivOfAddEquiv (φ : M ≃+ Additive (ClassGroup A)) :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+* TrivSqZeroExt ℤ M :=
  .symm <| .ofBijective (TrivSqZeroExt.liftEquivOfComm
    ⟨((idealClassHom A).comp φ.toAddMonoidHom).toIntLinearMap,
      fun _ _ ↦ idealClassHom_mul_idealClassHom A _ _⟩) <| by
    -- As a map of sets, the inverse is `(n, m) ↦ (rankSteinitzEquiv A).symm (n, φ m)`.
    have : ⇑(TrivSqZeroExt.liftEquivOfComm
        ⟨((idealClassHom A).comp φ.toAddMonoidHom).toIntLinearMap,
          fun _ _ ↦ idealClassHom_mul_idealClassHom A _ _⟩) =
        (rankSteinitzEquiv A).symm ∘ fun x : TrivSqZeroExt ℤ M ↦ (x.fst, φ x.snd) := by
      ext x
      simp [TrivSqZeroExt.lift_def]
    rw [this]
    refine (rankSteinitzEquiv A).symm.bijective.comp ⟨fun x y h ↦ ?_, fun p ↦
      ⟨TrivSqZeroExt.inl p.1 + TrivSqZeroExt.inr (φ.symm p.2), by simp⟩⟩
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact TrivSqZeroExt.ext h.1 h.2

private theorem ringEquivOfAddEquiv_symm_apply (φ : M ≃+ Additive (ClassGroup A))
    (x : TrivSqZeroExt ℤ M) :
    (ringEquivOfAddEquiv A φ).symm x = x.fst + idealClassHom A (φ x.snd) := by
  simp [ringEquivOfAddEquiv, TrivSqZeroExt.lift_def]

private theorem rankSteinitz_eq_ringEquivOfAddEquiv (φ : M ≃+ Additive (ClassGroup A))
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    rankSteinitz A x = ((ringEquivOfAddEquiv A φ x).fst, φ (ringEquivOfAddEquiv A φ x).snd) := by
  conv_lhs => rw [← (ringEquivOfAddEquiv A φ).symm_apply_apply x]
  -- `rankSteinitz` sends the unit `[A]` to `(1, 0)`, hence an integer `n` to `(n, 0)`.
  have h1 : rankSteinitz A 1 = (1, 0) := by
    rw [← splitK0_of_finiteProjectiveModulesRegular]
    exact rankSteinitz_of_finiteProjectiveModulesRegular A
  have hcast (n : ℤ) : rankSteinitz A n = (n, 0) := by
    simpa [h1] using map_zsmul (rankSteinitz A) n 1
  rw [ringEquivOfAddEquiv_symm_apply]
  simp [hcast]

/-- **Projective `K₀` of a Dedekind domain as a ring.** Rank and Steinitz class identify projective
`K₀(A)` with the trivial square-zero extension `ℤ ⋉ Cl(A)`, so that
`(m, c) * (n, d) = (mn, m d + n c)`. -/
noncomputable def rankSteinitzRingEquiv [Module ℤᵐᵒᵖ (Additive (ClassGroup A))]
    [IsCentralScalar ℤ (Additive (ClassGroup A))] :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+*
      TrivSqZeroExt ℤ (Additive (ClassGroup A)) :=
  ringEquivOfAddEquiv A (.refl _)

/-- **Projective `K₀` of a Dedekind domain as a ring, in Picard coordinates.** Rank and Picard
class identify projective `K₀(A)` with the trivial square-zero extension `ℤ ⋉ Pic(A)`; the class of
`Aⁿ` goes to `(n, 1)` and the class of an invertible module `L` to `(1, L)`. -/
noncomputable def rankPicRingEquiv [Module ℤᵐᵒᵖ (Additive (Pic A))]
    [IsCentralScalar ℤ (Additive (Pic A))] :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+*
      TrivSqZeroExt ℤ (Additive (Pic A)) :=
  ringEquivOfAddEquiv A (ClassGroup.equivPic A).symm.toAdditive

section ClassGroup

variable [Module ℤᵐᵒᵖ (Additive (ClassGroup A))] [IsCentralScalar ℤ (Additive (ClassGroup A))]

/-- The rank coordinate of `TauCeti.FiniteProjectiveModules.rankSteinitzRingEquiv`. -/
@[simp]
theorem fst_rankSteinitzRingEquiv (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    (rankSteinitzRingEquiv A x).fst = (rankSteinitz A x).1 := by
  simp [rankSteinitzRingEquiv, rankSteinitz_eq_ringEquivOfAddEquiv A (.refl _) x]

/-- The Steinitz class coordinate of `TauCeti.FiniteProjectiveModules.rankSteinitzRingEquiv`. -/
@[simp]
theorem snd_rankSteinitzRingEquiv (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    (rankSteinitzRingEquiv A x).snd = (rankSteinitz A x).2 := by
  simp [rankSteinitzRingEquiv, rankSteinitz_eq_ringEquivOfAddEquiv A (.refl _) x]

/-- The inverse of `TauCeti.FiniteProjectiveModules.rankSteinitzRingEquiv` sends `(n, c)` to
`n` plus the reduced ideal class `c`. -/
@[simp]
theorem rankSteinitzRingEquiv_symm_apply (x : TrivSqZeroExt ℤ (Additive (ClassGroup A))) :
    (rankSteinitzRingEquiv A).symm x = x.fst + idealClassHom A x.snd :=
  ringEquivOfAddEquiv_symm_apply A (.refl _) x

end ClassGroup

section Pic

variable [Module ℤᵐᵒᵖ (Additive (Pic A))] [IsCentralScalar ℤ (Additive (Pic A))]

/-- The rank coordinate of `TauCeti.FiniteProjectiveModules.rankPicRingEquiv`. -/
@[simp]
theorem fst_rankPicRingEquiv (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    (rankPicRingEquiv A x).fst = (rankSteinitz A x).1 := by
  simp [rankPicRingEquiv, rankSteinitz_eq_ringEquivOfAddEquiv A
    (ClassGroup.equivPic A).symm.toAdditive x]

/-- The Picard coordinate of `TauCeti.FiniteProjectiveModules.rankPicRingEquiv` is the Picard
class corresponding to the Steinitz class. -/
@[simp]
theorem snd_rankPicRingEquiv (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    (rankPicRingEquiv A x).snd =
      Additive.ofMul (ClassGroup.equivPic A (rankSteinitz A x).2.toMul) := by
  rw [rankSteinitz_eq_ringEquivOfAddEquiv A (ClassGroup.equivPic A).symm.toAdditive]
  simp [rankPicRingEquiv, -ClassGroup.equivPic_apply, -ClassGroup.equivPic_symm_apply]

/-- The inverse of `TauCeti.FiniteProjectiveModules.rankPicRingEquiv` sends `(n, L)` to `n` plus
the reduced class of the ideal class of `L`. -/
@[simp]
theorem rankPicRingEquiv_symm_apply (x : TrivSqZeroExt ℤ (Additive (Pic A))) :
    (rankPicRingEquiv A).symm x =
      x.fst + idealClassHom A (Additive.ofMul ((ClassGroup.equivPic A).symm x.snd.toMul)) :=
  ringEquivOfAddEquiv_symm_apply A _ x

/-- The free module `Aⁿ` has rank `n` and trivial Picard class. -/
theorem rankPicRingEquiv_of_fin (n : ℕ) :
    rankPicRingEquiv A (SplitK0.of.{u} (freeProjective A n)) = n := by
  rw [splitK0_of_fin, map_natCast]

/-- An invertible module `L` has rank one and Picard class `L`. -/
theorem rankPicRingEquiv_of_pic (L : Pic A) :
    rankPicRingEquiv A (SplitK0.of.{u} (of A L)) =
      TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Additive.ofMul L) := by
  obtain ⟨I, ⟨e⟩⟩ := Module.Invertible.exists_linearEquiv_nonZeroDivisors (A := A) L
  have hL : Module.finrank A L = 1 :=
    e.finrank_eq.trans
      (Ideal.finrank_eq_one_of_ne_bot (mem_nonZeroDivisors_iff_ne_zero.mp I.property))
  ext
  · simp [hL]
  · simp [ClassGroup.equivPic_steinitzClass, -ClassGroup.equivPic_apply]

/-- The reduced class `[L] - [A]` of an invertible module `L` has rank zero and Picard class
`L`. -/
theorem rankPicRingEquiv_of_pic_sub_one (L : Pic A) :
    rankPicRingEquiv A (SplitK0.of.{u} (of A L) - 1) = TrivSqZeroExt.inr (Additive.ofMul L) := by
  rw [map_sub, rankPicRingEquiv_of_pic, map_one, ← TrivSqZeroExt.inl_one, add_sub_cancel_left]

/-- **Extension of scalars of rank–Picard coordinates.** Along a ring homomorphism `f : A →+* B`
from a Dedekind domain to any commutative ring, the class with rank–Picard coordinates `(n, L)`
goes to `(n - 1) [B] + [f* L]`, where `f* L = CommRing.Pic.mapRingHom f L` is the extended line. -/
theorem map_extendScalars_rankPicRingEquiv_symm {B : Type u} [CommRing B] (f : A →+* B)
    (y : TrivSqZeroExt ℤ (Additive (Pic A))) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars ((rankPicRingEquiv A).symm y) =
      (y.fst - 1 : ℤ) + SplitK0.of.{u} (of B (Pic.mapRingHom f y.snd.toMul)) := by
  -- `(n, L)` is the class `(n - 1) [A] + [L]`.
  have hy : (rankPicRingEquiv A).symm y =
      (y.fst - 1 : ℤ) • 1 + SplitK0.of.{u} (of A y.snd.toMul) := by
    rw [RingEquiv.symm_apply_eq, map_add, map_zsmul, map_one, rankPicRingEquiv_of_pic,
      ofMul_toMul, zsmul_one]
    ext <;> simp
  rw [hy, map_add, map_zsmul, SplitK0.map_extendScalars_one, map_extendScalars_of_pic, zsmul_one]

end Pic

end RingEquiv

section ExtendScalars

variable {A} {B : Type u} [CommRing B]

/-- **Naturality of the rank–Picard isomorphism.** Along any ring homomorphism `f : A →+* B` of
Dedekind domains, injective or not, extension of scalars is `(n, L) ↦ (n, f* L)` in rank–Picard
coordinates, where `f* L = CommRing.Pic.mapRingHom f L`. -/
@[simp]
theorem rankPicRingEquiv_map_extendScalars [IsDedekindDomain B]
    [Module ℤᵐᵒᵖ (Additive (Pic A))] [IsCentralScalar ℤ (Additive (Pic A))]
    [Module ℤᵐᵒᵖ (Additive (Pic B))] [IsCentralScalar ℤ (Additive (Pic B))] (f : A →+* B)
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    rankPicRingEquiv B (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      TrivSqZeroExt.map (Pic.mapRingHom f).toAdditive.toIntLinearMap (rankPicRingEquiv A x) := by
  conv_lhs => rw [← (rankPicRingEquiv A).symm_apply_apply x]
  rw [map_extendScalars_rankPicRingEquiv_symm, map_add, map_intCast, rankPicRingEquiv_of_pic]
  ext <;> simp

/-- **Extension of scalars to a ring with trivial Picard group**, such as a residue field of `A`
or a local ring: every Picard class of the Dedekind domain `A` dies, and a class `x` of projective
`K₀(A)` goes to the integer `rank x`, its first rank–Steinitz coordinate. -/
theorem map_extendScalars_eq_rankSteinitz_fst [Subsingleton (Pic B)] (f : A →+* B)
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x = (rankSteinitz A x).1 := by
  -- Any central right action of `ℤ` serves to form the square-zero extension.
  let : Module ℤᵐᵒᵖ (Additive (Pic A)) := Module.compHom _ ((RingHom.id ℤ).fromOpposite mul_comm)
  have : IsCentralScalar ℤ (Additive (Pic A)) := ⟨fun _ _ ↦ rfl⟩
  -- The line `f* L` of `B` is trivial.
  have hL : SplitK0.of.{u} (of B (Pic.mapRingHom f ((rankPicRingEquiv A x).snd.toMul))) = 1 := by
    rw [Subsingleton.elim (Pic.mapRingHom f _) 1, splitK0_of_pic_one]
  conv_lhs => rw [← (rankPicRingEquiv A).symm_apply_apply x]
  rw [map_extendScalars_rankPicRingEquiv_symm, hL, fst_rankPicRingEquiv]
  push_cast
  ring

end ExtendScalars

end FiniteProjectiveModules

/-- The Steinitz class of a tensor product of finite flat modules in the universe of the base
ring, computed in projective `K₀`. -/
private theorem steinitzClass_tensorProduct_aux {A : Type u} [CommRing A] [IsDedekindDomain A]
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Flat A N] :
    Module.steinitzClass A (M ⊗[A] N) =
      Module.steinitzClass A M ^ Module.finrank A N *
        Module.steinitzClass A N ^ Module.finrank A M := by
  have := Module.finitePresentation_of_finite A M
  have := Module.finitePresentation_of_finite A N
  have : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  have : Module.Projective A N := Module.Flat.projective_of_finitePresentation
  -- Any central right action of `ℤ` serves to form the square-zero extension.
  let : Module ℤᵐᵒᵖ (Additive (ClassGroup A)) :=
    Module.compHom _ ((RingHom.id ℤ).fromOpposite mul_comm)
  have : IsCentralScalar ℤ (Additive (ClassGroup A)) := ⟨fun _ _ ↦ rfl⟩
  have h := congrArg (fun x ↦ (FiniteProjectiveModules.rankSteinitzRingEquiv A x).snd)
    (FiniteProjectiveModules.splitK0_of_tensorProduct M N)
  simp only [map_mul, TrivSqZeroExt.snd_mul, FiniteProjectiveModules.snd_rankSteinitzRingEquiv,
    FiniteProjectiveModules.fst_rankSteinitzRingEquiv, FiniteProjectiveModules.rankSteinitz_of,
    op_smul_eq_smul] at h
  apply_fun Additive.ofMul
  rw [h]
  simp [ofMul_mul, ofMul_pow, add_comm]

/-- **The Steinitz class of a tensor product.** For finite flat modules `M` and `N` over a
Dedekind domain, `st(M ⊗ N) = st(M) ^ rank N * st(N) ^ rank M`. -/
theorem _root_.Module.steinitzClass_tensorProduct {A : Type u} [CommRing A] [IsDedekindDomain A]
    (M N : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Flat A N] :
    Module.steinitzClass A (M ⊗[A] N) =
      Module.steinitzClass A M ^ Module.finrank A N *
        Module.steinitzClass A N ^ Module.finrank A M := by
  -- Replace `M` and `N` by isomorphic products of ideals, which live in the universe of `A`.
  obtain ⟨m, I, ⟨eM⟩⟩ := Module.exists_linearEquiv_pi_nonZeroDivisors A M
  obtain ⟨n, J, ⟨eN⟩⟩ := Module.exists_linearEquiv_pi_nonZeroDivisors A N
  have : Module.Finite A ((i : Fin m) → (I i : Ideal A)) := .equiv eM
  have : Module.Flat A ((i : Fin m) → (I i : Ideal A)) := .of_linearEquiv eM.symm
  have : Module.Finite A ((i : Fin n) → (J i : Ideal A)) := .equiv eN
  have : Module.Flat A ((i : Fin n) → (J i : Ideal A)) := .of_linearEquiv eN.symm
  rw [Module.steinitzClass_congr (TensorProduct.congr eM eN), Module.steinitzClass_congr eM,
    Module.steinitzClass_congr eN, eM.finrank_eq, eN.finrank_eq]
  exact steinitzClass_tensorProduct_aux _ _

end TauCeti
