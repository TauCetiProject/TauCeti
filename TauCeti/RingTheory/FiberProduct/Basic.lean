/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Fiber products along a surjection

For `B → C ← D`, if `B → C` is surjective, the fiber product square is also a
pushout in commutative rings. The projection to `B` is finite when `D → C` is
finite, and is an isomorphism after inverting an element of the kernel of
the projection to `D`.

## References

* [D. Ferrand, *Conducteur, descente et pincement*][ferrand], Lemma 1.3.
* Stacks Project, [Lemma 15.5.3][stacks-01Z8] and the proof of [Lemma 15.6.2][stacks-0B7J].

[ferrand]: https://www.numdam.org/articles/10.24033/bsmf.2455/
[stacks-01Z8]: https://stacks.math.columbia.edu/tag/01Z8
[stacks-0B7J]: https://stacks.math.columbia.edu/tag/0B7J
-/

public section

open CategoryTheory

namespace RingHom

/-- The first projection identifies the second projection's kernel with `ker p`.
The latter carries scalars through the first projection. This is the elementwise
counterpart of `RingHom.map_pullbackSnd_ker_pullbackFst_eq`, with the factors swapped. -/
def pullbackSndKerEquiv {B C D : Type*} [CommRing B] [Semiring C] [CommRing D]
    (p : B →+* C) (q : D →+* C) :
    letI : Algebra (p.pullback q) B := (p.pullbackFst q).toAlgebra
    ker (p.pullbackSnd q) ≃ₗ[p.pullback q] ker p := by
  letI : Algebra (p.pullback q) B := (p.pullbackFst q).toAlgebra
  refine
    { toFun := fun x ↦ ⟨p.pullbackFst q x, ?_⟩
      invFun := fun b ↦ ⟨⟨(b, 0), ?_⟩, rfl⟩
      left_inv := ?_
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  · exact (x.val.property.trans (congrArg q (mem_ker.mp x.property))).trans q.map_zero
  · exact (mem_ker.mp b.property).trans q.map_zero.symm
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (mem_ker.mp x.property).symm

@[simp]
theorem pullbackSndKerEquiv_apply_coe {B C D : Type*}
    [CommRing B] [Semiring C] [CommRing D]
    (p : B →+* C) (q : D →+* C) (x : ker (p.pullbackSnd q)) :
    (pullbackSndKerEquiv p q x : B) = p.pullbackFst q x := by rfl

@[simp]
theorem pullbackSndKerEquiv_symm_fst {B C D : Type*}
    [CommRing B] [Semiring C] [CommRing D]
    (p : B →+* C) (q : D →+* C) (b : ker p) :
    p.pullbackFst q ((pullbackSndKerEquiv p q).symm b) = b := by rfl

@[simp]
theorem pullbackSndKerEquiv_symm_snd {B C D : Type*}
    [CommRing B] [Semiring C] [CommRing D]
    (p : B →+* C) (q : D →+* C) (b : ker p) :
    p.pullbackSnd q ((pullbackSndKerEquiv p q).symm b) = 0 := by rfl

/-- The first projection carries the kernel of the second projection onto the kernel
of the map out of the first factor. This is the factor-swapped counterpart of
`RingHom.map_pullbackSnd_ker_pullbackFst_eq`. -/
@[simp]
theorem map_pullbackFst_ker_pullbackSnd_eq {B C D : Type*} [Ring B] [Semiring C] [Ring D]
    (p : B →+* C) (q : D →+* C) :
    (ker (p.pullbackSnd q)).map (p.pullbackFst q) = ker p := by
  let e : p.pullback q ≃+* q.pullback p :=
    (RingEquiv.prodComm : B × D ≃+* D × B).restrict _ _ (fun _ ↦ eq_comm)
  have hker : ker (p.pullbackSnd q) = (ker (q.pullbackFst p)).comap e.toRingHom := rfl
  have hfst : p.pullbackFst q = (q.pullbackSnd p).comp e.toRingHom := rfl
  rw [hfst, ← Ideal.map_map, hker,
    Ideal.map_comap_of_surjective e.toRingHom e.surjective, map_pullbackSnd_ker_pullbackFst_eq]

universe u in
/-- For a surjective map out of the first factor, the ring fiber product square is
also a pushout. -/
theorem isPushout_pullback {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (p : B →+* C) (q : D →+* C) (hp : Function.Surjective p) :
    IsPushout (CommRingCat.ofHom (p.pullbackFst q)) (CommRingCat.ofHom (p.pullbackSnd q))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q) := by
  refine IsPushout.mk' (CommRingCat.hom_ext (p.pullback_comm_sq q)) ?_ ?_
  · intro T f g h _
    have : Epi (CommRingCat.ofHom p) := ConcreteCategory.epi_of_surjective _ hp
    exact (cancel_epi (CommRingCat.ofHom p)).mp h
  · intro T f g h
    have hfg (x : p.pullback q) : f (p.pullbackFst q x) = g (p.pullbackSnd q x) := by
      have hx : (CommRingCat.ofHom (p.pullbackFst q) ≫ f).hom x =
          (CommRingCat.ofHom (p.pullbackSnd q) ≫ g).hom x :=
        ConcreteCategory.congr_hom h x
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using hx
    have hker : ker p ≤ ker f.hom := by
      rw [← map_pullbackFst_ker_pullbackSnd_eq p q, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, mem_ker]
      rw [hfg, mem_ker.mp hx, map_zero]
    let l := p.liftOfSurjective hp ⟨f.hom, hker⟩
    have hl : l.comp p = f.hom := p.liftOfSurjective_comp hp _
    refine ⟨CommRingCat.ofHom l, CommRingCat.hom_ext hl, ?_⟩
    apply CommRingCat.hom_ext
    ext d
    obtain ⟨x, rfl⟩ := p.surjective_pullbackSnd_of_surjective q hp d
    have hx : p (p.pullbackFst q x) = q (p.pullbackSnd q x) := x.property
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact (congrArg l hx).symm.trans
      ((congrArg (fun k : B →+* T ↦ k (p.pullbackFst q x)) hl).trans (hfg x))

universe u in
/-- If `p` is surjective, the canonical map `B ⊗[B ×_C D] D → C` is an isomorphism.
The algebra and tower data are determined by the four ring maps. -/
theorem isPushout_pullback_algebra {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (p : B →+* C) (q : D →+* C) (hp : Function.Surjective p) :
    letI : Algebra (p.pullback q) B := (p.pullbackFst q).toAlgebra
    letI : Algebra (p.pullback q) D := (p.pullbackSnd q).toAlgebra
    letI : Algebra (p.pullback q) C := (p.comp (p.pullbackFst q)).toAlgebra
    letI : Algebra B C := p.toAlgebra
    letI : Algebra D C := q.toAlgebra
    letI : IsScalarTower (p.pullback q) B C := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (p.pullback q) D C :=
      IsScalarTower.of_algebraMap_eq' (p.pullback_comm_sq q)
    Algebra.IsPushout (p.pullback q) B D C := by
  let : Algebra (p.pullback q) B := (p.pullbackFst q).toAlgebra
  let : Algebra (p.pullback q) D := (p.pullbackSnd q).toAlgebra
  let : Algebra (p.pullback q) C := (p.comp (p.pullbackFst q)).toAlgebra
  let : Algebra B C := p.toAlgebra
  let : Algebra D C := q.toAlgebra
  let : IsScalarTower (p.pullback q) B C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (p.pullback q) D C :=
    IsScalarTower.of_algebraMap_eq' (p.pullback_comm_sq q)
  exact CommRingCat.isPushout_iff_isPushout.mp (isPushout_pullback p q hp)

universe u v w

variable {B : Type u} {C : Type v} {D : Type w} [CommRing B] [CommRing C] [CommRing D]
variable (p : B →+* C) (q : D →+* C)

/-- For `t ∈ ker (p.pullbackSnd q)`, the induced map `(B ×_C D)[1/t] → B[1/(p.pullbackFst q t)]`
is bijective for arbitrary ring maps `p` and `q`. -/
theorem bijective_awayMap_pullbackFst {t : p.pullback q} (ht : t ∈ ker (p.pullbackSnd q)) :
    Function.Bijective (Localization.awayMap (p.pullbackFst q) t) := by
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    refine ⟨1, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (p.pullbackFst q) (t ^ 1 * a) = 0
      rw [map_mul, map_pow, pow_one, ha, mul_zero]
    · change (p.pullbackSnd q) (t ^ 1 * a) = 0
      rw [map_mul, map_pow, pow_one, mem_ker.mp ht, zero_mul]
  · apply Localization.awayMap_surjective_iff.mpr
    intro b
    have hzero : p (p.pullbackFst q t) = 0 :=
      (pullbackSndKerEquiv p q ⟨t, ht⟩).property
    have hb : p.pullbackFst q t * b ∈ ker p := by
      rw [mem_ker, map_mul, hzero, zero_mul]
    exact ⟨(pullbackSndKerEquiv p q).symm ⟨_, hb⟩, 1, by simp⟩

/-- If the first coordinate of `a` is the first coordinate of `t` times `b`, the
inverse of the localized first projection sends the image of `b` to the fraction `a / t`. -/
theorem awayMap_pullbackFst_symm_algebraMap {t : p.pullback q}
    (ht : t ∈ ker (p.pullbackSnd q)) {a : p.pullback q} {b : B}
    (ha : p.pullbackFst q a = p.pullbackFst q t * b) :
    (RingEquiv.ofBijective (Localization.awayMap (p.pullbackFst q) t)
      (bijective_awayMap_pullbackFst p q ht)).symm
        (algebraMap B (Localization.Away (p.pullbackFst q t)) b) =
      IsLocalization.mk' (Localization.Away t) a ⟨t, Submonoid.mem_powers t⟩ := by
  apply (RingEquiv.ofBijective (Localization.awayMap (p.pullbackFst q) t)
    (bijective_awayMap_pullbackFst p q ht)).injective
  simp only [RingEquiv.apply_symm_apply, RingEquiv.ofBijective_apply,
    Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  rw [← map_mul]
  exact congrArg (algebraMap B (Localization.Away (p.pullbackFst q t)))
    (ha.trans (mul_comm _ _)).symm

/-- If the map from the first factor is surjective and the map from the second
factor is finite, the first projection is finite. -/
theorem finite_pullbackFst_of_surjective (hp : Function.Surjective p) (hq : q.Finite) :
    (p.pullbackFst q).Finite := by
  let A := ↥(p.pullback q)
  let : Algebra A B := (p.pullbackFst q).toAlgebra
  let : Algebra A D := (p.pullbackSnd q).toAlgebra
  let : Algebra A C := (p.comp (p.pullbackFst q)).toAlgebra
  let : Algebra B C := p.toAlgebra
  let : Algebra D C := q.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq' (p.pullback_comm_sq q)
  have hfinite : Module.Finite D C := hq
  have : Module.Finite A C := ⟨by
    simpa only [Submodule.restrictScalars_top] using
      hfinite.fg_top.restrictScalars_of_surjective (p.surjective_pullbackSnd_of_surjective q hp)⟩
  let reduce := (IsScalarTower.toAlgHom A B C).toLinearMap
  let coefficients := (Algebra.linearMap A B).range
  -- The quotient by the coefficient image is already a quotient of C.
  have hker : LinearMap.ker reduce ≤ LinearMap.ker coefficients.mkQ := by
    rw [Submodule.ker_mkQ]
    intro b hb
    have hb' : b ∈ ker p := by
      simpa only [reduce, LinearMap.mem_ker, AlgHom.toLinearMap_apply,
        IsScalarTower.toAlgHom_apply, mem_ker, RingHom.algebraMap_toAlgebra] using hb
    exact ⟨(pullbackSndKerEquiv p q).symm ⟨b, hb'⟩,
      pullbackSndKerEquiv_symm_fst p q ⟨b, hb'⟩⟩
  let descend := reduce.liftOfSurjective hp ⟨coefficients.mkQ, hker⟩
  have hdescend : Function.Surjective descend := by
    intro b
    obtain ⟨x, rfl⟩ := coefficients.mkQ_surjective b
    exact ⟨reduce x, LinearMap.equivOfSurjective_apply hp hker⟩
  have : Module.Finite A (B ⧸ coefficients) := Module.Finite.of_surjective descend hdescend
  exact Module.Finite.of_submodule_quotient coefficients

end RingHom
