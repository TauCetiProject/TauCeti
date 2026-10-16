/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Diagonal
public import TauCeti.RingTheory.Henselization.Neighbourhood
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Filteredness of étale neighbourhoods

The étale neighbourhoods of a ring–ideal pair form a filtered category. In addition to tensor
products providing common targets, parallel maps are equalized after localizing the target at the
complement of the idempotent that cuts out their equalizer. This filtered category indexes the
construction of the henselization of a pair.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Two maps out of a neighbourhood agree after quotienting their target by the extended ideal. -/
theorem quotient_mk_eq_of_isNeighbourhood {B C : Type v} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (hB : IsNeighbourhood I (CommAlgCat.of R B))
    (f g : B →ₐ[R] C) (b : B) :
    Ideal.Quotient.mk (I.map (algebraMap R C)) (f b) =
      Ideal.Quotient.mk (I.map (algebraMap R C)) (g b) := by
  have hmap (h : B →ₐ[R] C) :
      I.map (algebraMap R B) ≤ (I.map (algebraMap R C)).comap h.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap]
    calc
      (I.map (algebraMap R B)).map h.toRingHom =
          I.map (h.toRingHom.comp (algebraMap R B)) := Ideal.map_map _ _
      _ = I.map (algebraMap R C) := by
        congr 1
        exact RingHom.ext h.commutes
      _ ≤ I.map (algebraMap R C) := le_rfl
  let qf := Ideal.quotientMap (I.map (algebraMap R C)) f.toRingHom (hmap f)
  let qg := Ideal.quotientMap (I.map (algebraMap R C)) g.toRingHom (hmap g)
  obtain ⟨_, hBij⟩ := (isNeighbourhood_iff I _).mp hB
  obtain ⟨r, hr⟩ := hBij.2 (Ideal.Quotient.mk (I.map (algebraMap R B)) b)
  have : qf (Ideal.Quotient.mk (I.map (algebraMap R B)) b) =
      qg (Ideal.Quotient.mk (I.map (algebraMap R B)) b) := calc
    qf (Ideal.Quotient.mk (I.map (algebraMap R B)) b) = qf (reducedMap I B r) :=
      congrArg qf hr.symm
    _ = reducedMap I C r := by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [qf, Ideal.quotientMap_mk, reducedMap_mk]
      congr 1
      exact f.commutes r
    _ = qg (reducedMap I B r) := by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [qg, Ideal.quotientMap_mk, reducedMap_mk]
      congr 1
      exact (g.commutes r).symm
    _ = qg (Ideal.Quotient.mk (I.map (algebraMap R B)) b) := congrArg qg hr
  simp only [qf, qg, Ideal.quotientMap_mk] at this
  change Ideal.Quotient.mk (I.map (algebraMap R C)) (f b) =
    Ideal.Quotient.mk (I.map (algebraMap R C)) (g b) at this
  exact this

/-- Two parallel maps of étale neighbourhoods become equal after a further étale
neighbourhood. -/
theorem parallel_equalization {B C : Neighbourhood.{u, v} I} (f g : B ⟶ C) :
    ∃ (D : Neighbourhood.{u, v} I) (h : C ⟶ D), f ≫ h = g ≫ h := by
  let f' : B.obj →ₐ[R] C.obj := f.hom.hom
  let g' : B.obj →ₐ[R] C.obj := g.hom.hom
  let d : B.obj ⊗[R] B.obj →ₐ[R] C.obj := Algebra.TensorProduct.productMap f' g'
  have : Algebra.Etale R B.obj := ((isNeighbourhood_iff I _).mp B.property).1
  obtain ⟨e, he, hker⟩ :=
    Algebra.Etale.exists_isIdempotentElem_ker_lmul_eq_span R B.obj
  let s : C.obj := 1 - d e
  let D₀ := Localization.Away s
  have heker : e ∈ RingHom.ker
      (Algebra.TensorProduct.lmul' R : B.obj ⊗[R] B.obj →ₐ[R] B.obj).toRingHom := by
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton e)
  let q := Ideal.Quotient.mkₐ R (I.map (algebraMap R C.obj))
  have hfg (b : B.obj) : q (f' b) = q (g' b) := by
    change Ideal.Quotient.mk (I.map (algebraMap R C.obj)) (f' b) =
      Ideal.Quotient.mk (I.map (algebraMap R C.obj)) (g' b)
    exact quotient_mk_eq_of_isNeighbourhood I B.property f' g' b
  have hprod : q.comp d = (q.comp f').comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext
    · simp only [AlgHom.comp_assoc, d, Algebra.TensorProduct.productMap_left,
        Algebra.TensorProduct.lmul'_comp_includeLeft, AlgHom.comp_id]
    · apply AlgHom.ext
      intro b
      change q (d (1 ⊗ₜ[R] b)) = q (f' ((Algebra.TensorProduct.lmul' R) (1 ⊗ₜ[R] b)))
      simpa only [d, AlgHom.comp_apply, AlgHom.coe_restrictScalars,
        Algebra.TensorProduct.productMap_right_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, one_mul] using (hfg b).symm
  have hdzero : Ideal.Quotient.mk (I.map (algebraMap R C.obj)) (d e) = 0 := by
    change q (d e) = 0
    change (Algebra.TensorProduct.lmul' R) e = 0 at heker
    calc
      q (d e) = ((q.comp f').comp (Algebra.TensorProduct.lmul' R)) e :=
        DFunLike.congr_fun hprod e
      _ = 0 := by simpa only [AlgHom.comp_apply, map_zero] using congrArg (q.comp f') heker
  have hs : IsUnit (Ideal.Quotient.mk (I.map (algebraMap R C.obj)) s) := by
    rw [show Ideal.Quotient.mk (I.map (algebraMap R C.obj)) s = 1 by
      simp only [s, map_sub, map_one, hdzero, sub_zero]]
    exact isUnit_one
  have hD₀ : IsNeighbourhood I (CommAlgCat.of R D₀) :=
    isNeighbourhood_localization_of_isNeighbourhood I C.obj C.property hs
  let D : Neighbourhood.{u, v} I := ⟨CommAlgCat.of R D₀, hD₀⟩
  let h₀ : C.obj →ₐ[R] D₀ := IsScalarTower.toAlgHom R C.obj D₀
  let h : C ⟶ D := ObjectProperty.homMk (CommAlgCat.ofHom h₀)
  refine ⟨D, h, ?_⟩
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro b
  change h₀ (f' b) = h₀ (g' b)
  rw [← sub_eq_zero, ← map_sub]
  have hdiff : f' b - g' b = d (b ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b) := by simp [d]
  rw [hdiff]
  have hmem : b ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b ∈
      RingHom.ker (Algebra.TensorProduct.lmul' R :
        B.obj ⊗[R] B.obj →ₐ[R] B.obj).toRingHom := by simp
  rw [hker] at hmem
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [← ha]
  suffices h₀ (d e) = 0 by simp only [map_mul, this, mul_zero]
  have hunit : IsUnit (h₀ s) := IsLocalization.Away.algebraMap_isUnit s
  have hidem : IsIdempotentElem (h₀ (d e)) := (he.map d).map h₀
  have hmul : h₀ (d e) * h₀ s = 0 := by
    simp only [s, map_sub, map_one, mul_sub, mul_one, hidem.eq, sub_self]
  obtain ⟨y, hy⟩ := hunit
  rw [← hy] at hmul
  calc
    h₀ (d e) = h₀ (d e) * 1 := (mul_one _).symm
    _ = h₀ (d e) * ((y : D₀) * ((y⁻¹ : D₀ˣ) : D₀)) := by rw [Units.mul_inv]
    _ = (h₀ (d e) * (y : D₀)) * ((y⁻¹ : D₀ˣ) : D₀) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hmul, zero_mul]

/-- The category of étale neighbourhoods of a ring–ideal pair is filtered. -/
instance neighbourhood_isFiltered : IsFiltered (Neighbourhood.{u, max u v} I) where
  cocone_objs B C := by
    obtain ⟨D, ⟨f⟩, ⟨g⟩⟩ := exists_common_target I B C
    exact ⟨D, f, g, trivial⟩
  cocone_maps := fun {_ _} f g ↦ parallel_equalization I f g
  nonempty := ⟨⟨CommAlgCat.of R (ULift.{v} R),
    isNeighbourhood_of_algEquiv I (ULift.algEquiv (R := R)).symm⟩⟩

end TauCeti.Henselization
