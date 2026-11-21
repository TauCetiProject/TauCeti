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

import TauCeti.RingTheory.Localization.Pullback
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
/-- The tensor comparison for the native fiber-product projections is an isomorphism.
The algebra and tower data are the ones determined by the four ring maps. -/
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

private theorem bijective_awayMap_pullbackFst_sameUniverse
    {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (p : B →+* C) (q : D →+* C) {t : p.pullback q}
    (ht : t ∈ ker (p.pullbackSnd q)) :
    Function.Bijective (Localization.awayMap (p.pullbackFst q) t) := by
  let B' := CommRingCat.of.{u} (Localization.Away (p.pullbackFst q t))
  let D' := CommRingCat.of.{u} (Localization.Away (p.pullbackSnd q t))
  let C' := CommRingCat.of.{u} (Localization.Away (p (p.pullbackFst q t)))
  have hzero : p (p.pullbackFst q t) = 0 :=
    ((pullbackSndKerEquiv p q ⟨t, ht⟩).property : _)
  have hcomm : q (p.pullbackSnd q t) = p (p.pullbackFst q t) := t.property.symm
  let : IsLocalization.Away (q (p.pullbackSnd q t)) C' := hcomm.symm ▸ inferInstance
  let g' : D' ⟶ C' := CommRingCat.ofHom
    (IsLocalization.Away.map D' C' q (p.pullbackSnd q t))
  let : Subsingleton D' := IsLocalization.subsingleton
    (show 0 ∈ Submonoid.powers (p.pullbackSnd q t) from ⟨1, by simpa using mem_ker.mp ht⟩)
  let : Subsingleton C' := IsLocalization.subsingleton
    (show 0 ∈ Submonoid.powers (p (p.pullbackFst q t)) from ⟨1, by simpa using hzero⟩)
  have hg' : IsIso g' := (ConcreteCategory.isIso_iff_bijective g').mpr
    ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  have hpull : IsPullback (CommRingCat.ofHom (p.pullbackFst q))
      (CommRingCat.ofHom (p.pullbackSnd q)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) :=
    IsPullback.of_isLimit
      (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom p) (CommRingCat.ofHom q))
  have h := hpull.localizationAway
      (A' := CommRingCat.of.{u} (Localization.Away t)) (B' := B') (C' := D') (D' := C') t
      (i' := CommRingCat.ofHom (Localization.awayMap (p.pullbackFst q) t))
      (j' := CommRingCat.ofHom (Localization.awayMap (p.pullbackSnd q) t))
      (f' := CommRingCat.ofHom (Localization.awayMap p (p.pullbackFst q t))) (g' := g')
      (fun x ↦ by simp only [B', ConcreteCategory.hom_ofHom, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq])
      (fun x ↦ by simp only [D', ConcreteCategory.hom_ofHom, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq])
      (fun x ↦ by simp only [B', C', ConcreteCategory.hom_ofHom, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq])
      (fun x ↦ by simp only [g', C', D', ConcreteCategory.hom_ofHom,
        IsLocalization.Away.map, IsLocalization.map_eq])
  exact (ConcreteCategory.isIso_iff_bijective _).mp (h.isIso_fst_of_isIso hg')

variable {B : Type u} {C : Type v} {D : Type w} [CommRing B] [CommRing C] [CommRing D]
variable (p : B →+* C) (q : D →+* C)

/-- The first projection is an isomorphism after inverting an element in the kernel
of the second projection. This follows by localizing the pullback square: the other
horizontal map becomes a map between trivial rings. -/
theorem bijective_awayMap_pullbackFst {t : p.pullback q} (ht : t ∈ ker (p.pullbackSnd q)) :
    Function.Bijective (Localization.awayMap (p.pullbackFst q) t) := by
  -- The categorical square lives in one universe. Lift the three rings there and
  -- transport the algebraic injectivity and surjectivity criteria back down.
  let p' : ULift.{max u v w} B →+* ULift.{max u v w} C :=
    (ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom
  let q' : ULift.{max u v w} D →+* ULift.{max u v w} C :=
    (ULift.ringEquiv.symm.toRingHom.comp q).comp ULift.ringEquiv.toRingHom
  let t' : p'.pullback q' := ⟨(ULift.up (p.pullbackFst q t), ULift.up (p.pullbackSnd q t)),
    congrArg ULift.up t.property⟩
  have ht' : t' ∈ ker (p'.pullbackSnd q') := congrArg ULift.up (mem_ker.mp ht)
  have h := bijective_awayMap_pullbackFst_sameUniverse p' q' ht'
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro x hx
    let x' : p'.pullback q' :=
      ⟨(ULift.up (p.pullbackFst q x), ULift.up (p.pullbackSnd q x)),
        congrArg ULift.up x.property⟩
    obtain ⟨n, hn⟩ := Localization.awayMap_injective_iff.mp h.1 x' (congrArg ULift.up hx)
    exact ⟨n, Subtype.ext (Prod.ext (congrArg (fun y : p'.pullback q' ↦ y.val.1.down) hn)
      (congrArg (fun y : p'.pullback q' ↦ y.val.2.down) hn))⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro b
    obtain ⟨x, n, hn⟩ := Localization.awayMap_surjective_iff.mp h.2 (ULift.up b)
    refine ⟨⟨(x.val.1.down, x.val.2.down), congrArg ULift.down x.property⟩, n, ?_⟩
    exact congrArg ULift.down hn

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
