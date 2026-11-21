/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

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

/-- The first projection carries the kernel of the second projection onto the kernel
of the map out of the first factor. -/
theorem map_pullbackFst_ker_pullbackSnd_eq {B C D : Type*} [Ring B] [Semiring C] [Ring D]
    (p : B →+* C) (q : D →+* C) :
    (ker (p.pullbackSnd q)).map (p.pullbackFst q) = ker p := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    apply Ideal.mem_comap.mpr
    rw [mem_ker]
    calc
      p (p.pullbackFst q x) = q (p.pullbackSnd q x) := x.property
      _ = 0 := by rw [mem_ker.mp hx, map_zero]
  · intro b hb
    exact Ideal.mem_map_of_mem (p.pullbackFst q)
      (I := ker (p.pullbackSnd q))
      (x := ⟨(b, 0), (mem_ker.mp hb).trans q.map_zero.symm⟩) (by rfl)

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
    have hker : ker p ≤ ker f.hom := by
      rw [← map_pullbackFst_ker_pullbackSnd_eq p q, Ideal.map_le_iff_le_comap]
      intro x hx
      change f (p.pullbackFst q x) = 0
      have heq := congrArg (fun k : CommRingCat.of ↥(p.pullback q) ⟶ T ↦ k x) h
      change f (p.pullbackFst q x) = g (p.pullbackSnd q x) at heq
      rw [heq, mem_ker.mp hx, map_zero]
    let l := p.liftOfSurjective hp ⟨f.hom, hker⟩
    have hl : l.comp p = f.hom := p.liftOfSurjective_comp hp _
    refine ⟨CommRingCat.ofHom l, CommRingCat.hom_ext hl, ?_⟩
    apply CommRingCat.hom_ext
    ext d
    obtain ⟨x, rfl⟩ := p.surjective_pullbackSnd_of_surjective q hp d
    have heq := congrArg (fun k : CommRingCat.of ↥(p.pullback q) ⟶ T ↦ k x) h
    change f (p.pullbackFst q x) = g (p.pullbackSnd q x) at heq
    change l (q (p.pullbackSnd q x)) = g (p.pullbackSnd q x)
    have hx : p (p.pullbackFst q x) = q (p.pullbackSnd q x) := x.property
    rw [← hx]
    exact congrArg (fun k : B →+* T ↦ k (p.pullbackFst q x)) hl |>.trans heq

variable {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
variable (p : B →+* C) (q : D →+* C)

/-- The first projection is an isomorphism after inverting an element in the kernel
of the second projection. -/
theorem bijective_awayMap_pullbackFst {t : p.pullback q} (ht : t ∈ ker (p.pullbackSnd q)) :
    Function.Bijective (Localization.awayMap (p.pullbackFst q) t) := by
  refine ⟨Localization.awayMap_injective_iff.mpr ?_, Localization.awayMap_surjective_iff.mpr ?_⟩
  · intro x hx
    refine ⟨1, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (p.pullbackFst q t) ^ 1 * p.pullbackFst q x = 0
      rw [hx, mul_zero]
    · change (p.pullbackSnd q t) ^ 1 * p.pullbackSnd q x = 0
      rw [pow_one, mem_ker.mp ht, zero_mul]
  · intro b
    have ht' : p (p.pullbackFst q t) = 0 := by
      calc
        p (p.pullbackFst q t) = q (p.pullbackSnd q t) := t.property
        _ = 0 := by rw [mem_ker.mp ht, map_zero]
    refine ⟨⟨(p.pullbackFst q t * b, 0), ?_⟩, 1, ?_⟩
    · change p (p.pullbackFst q t * b) = q 0
      rw [map_mul, ht', zero_mul, map_zero]
    · change p.pullbackFst q t * b = (p.pullbackFst q t) ^ 1 * b
      rw [pow_one]

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
    change p b = 0 at hb
    exact ⟨⟨(b, 0), hb.trans q.map_zero.symm⟩, rfl⟩
  let descend := reduce.liftOfSurjective hp ⟨coefficients.mkQ, hker⟩
  have hdescend : Function.Surjective descend := by
    intro b
    obtain ⟨x, rfl⟩ := coefficients.mkQ_surjective b
    exact ⟨reduce x, LinearMap.equivOfSurjective_apply hp hker⟩
  have : Module.Finite A (B ⧸ coefficients) := Module.Finite.of_surjective descend hdescend
  exact Module.Finite.of_submodule_quotient coefficients

end RingHom
