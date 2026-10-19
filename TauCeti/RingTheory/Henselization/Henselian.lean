/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Jacobson
public import TauCeti.RingTheory.Henselization.Residue
public import TauCeti.RingTheory.Etale.StandardEtaleQuotient
public import Mathlib.RingTheory.Henselian

/-!
# The henselization of a pair is henselian

For a ring `R` and an ideal `I`, the henselization `algebra I`, the filtered colimit of the étale
neighbourhoods of `(R, I)`, is henselian along the extended ideal `extended I`.

The proof descends a monic polynomial with a simple root modulo the extended ideal to a single
étale neighbourhood `B`. Every stage `B` has the same closed fibre as the henselization, so the
simple-root hypotheses hold modulo `I B`. Adjoining a root of the polynomial to `B` and inverting
its derivative and the cofactor of the root gives a standard étale `B`-algebra. Its closed fibre is
still `R ⧸ I`, so it is a further neighbourhood, and it contains an actual root.

## Main results

* `TauCeti.Henselization.quotientMap_stage_bijective`: each stage map induces an isomorphism of
  closed fibres.
* `TauCeti.Henselization.exists_hom_isRoot_sub_mem`: a simple root modulo `I` at an étale
  neighbourhood becomes a root at a further étale neighbourhood.
* `TauCeti.Henselization.henselian`: the pair `(algebra I, extended I)` is henselian.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02), the henselization of
  a pair is a henselian pair.
-/

public section

open CategoryTheory Polynomial

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Finitely many elements of the henselization come from a common étale neighbourhood. -/
theorem exists_stage_family {ι : Type*} [Finite ι] (x : ι → algebra I) :
    ∃ (B : Neighbourhood.{u, u} I) (b : ι → B.obj), ∀ i, stage I B (b i) = x i := by
  classical
  choose B b hb using fun i ↦ exists_stage_eq I (x i)
  cases nonempty_fintype ι
  let O : Finset (Neighbourhood.{u, u} I) := Finset.univ.image B
  have hO (i : ι) : B i ∈ O := Finset.mem_image_of_mem B (Finset.mem_univ i)
  refine ⟨IsFiltered.sup O ∅, fun i ↦ (IsFiltered.toSup O ∅ (hO i)).hom.hom (b i), fun i ↦ ?_⟩
  rw [stage_hom_apply, hb]

/-- The stage map of an étale neighbourhood carries its extended ideal into the extended ideal of
the henselization. -/
theorem map_le_comap_stage_extended (B : Neighbourhood.{u, u} I) :
    I.map (algebraMap R B.obj) ≤ (extended I).comap (stage I B : B.obj →+* algebra I) :=
  Ideal.map_le_iff_le_comap.mp (map_stage_map_algebraMap I B).le

/-- Every étale neighbourhood has the same closed fibre as the henselization: its stage map
induces an isomorphism modulo the extended ideals. -/
theorem quotientMap_stage_bijective (B : Neighbourhood.{u, u} I) :
    Function.Bijective (Ideal.quotientMap (extended I) (stage I B : B.obj →+* algebra I)
      (map_le_comap_stage_extended I B)) := by
  have hcomp : (Ideal.quotientMap (extended I) (stage I B : B.obj →+* algebra I)
      (map_le_comap_stage_extended I B)).comp (reducedMap I B.obj) = reducedMap I (algebra I) := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp
  refine (Function.Bijective.of_comp_iff _
    ((isNeighbourhood_iff I B.obj).mp B.property).2).mp ?_
  rw [← RingHom.coe_comp, hcomp]
  exact quotient_bijective I

/-- An element of an étale neighbourhood lies in its extended ideal exactly when its image in the
henselization lies in the extended ideal. -/
theorem comap_stage_extended (B : Neighbourhood.{u, u} I) :
    (extended I).comap (stage I B : B.obj →+* algebra I) = I.map (algebraMap R B.obj) := by
  refine le_antisymm (fun b hb ↦ ?_) (map_le_comap_stage_extended I B)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (quotientMap_stage_bijective I B).1
  rw [map_zero, Ideal.quotientMap_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hb

/-- An element of an étale neighbourhood is a unit modulo its extended ideal exactly when its
image in the henselization is a unit modulo the extended ideal. -/
theorem isUnit_quotient_stage_iff (B : Neighbourhood.{u, u} I) (b : B.obj) :
    IsUnit (Ideal.Quotient.mk (extended I) (stage I B b)) ↔
      IsUnit (Ideal.Quotient.mk (I.map (algebraMap R B.obj)) b) := by
  let e := RingEquiv.ofBijective (Ideal.quotientMap (extended I)
    (stage I B : B.obj →+* algebra I) (map_le_comap_stage_extended I B))
    (quotientMap_stage_bijective I B)
  have he : e (Ideal.Quotient.mk (I.map (algebraMap R B.obj)) b) =
      Ideal.Quotient.mk (extended I) (stage I B b) := by
    simp [e]
  rw [← he, isUnit_map_iff]

/-- A simple root modulo the extended ideal at an étale neighbourhood becomes an actual root at a
further étale neighbourhood, congruent to it modulo the extended ideal. -/
theorem exists_hom_isRoot_sub_mem (B : Neighbourhood.{u, u} I) {p : B.obj[X]} (hp : p.Monic)
    {a : B.obj} (hpa : p.eval a ∈ I.map (algebraMap R B.obj))
    (hu : IsUnit (Ideal.Quotient.mk (I.map (algebraMap R B.obj)) (p.derivative.eval a))) :
    ∃ (C : Neighbourhood.{u, u} I) (f : B ⟶ C) (c : C.obj),
      (p.map (f.hom.hom : B.obj →+* C.obj)).IsRoot c ∧
        c - f.hom.hom a ∈ I.map (algebraMap R C.obj) := by
  let J := I.map (algebraMap R B.obj)
  obtain ⟨hBEtale, hBBij⟩ := (isNeighbourhood_iff I B.obj).mp B.property
  -- The cofactor `q` of the approximate root: `p = p(a) + (X - a) q`, so that `q(a) = p'(a)`.
  obtain ⟨q, hq⟩ : ∃ q : B.obj[X], p = C (p.eval a) + (X - C a) * q :=
    ⟨p /ₘ (X - C a), by
      conv_lhs => rw [← modByMonic_add_div p (X - C a), modByMonic_X_sub_C_eq_C_eval]⟩
  have hqa : q.eval a = p.derivative.eval a := by
    conv_rhs => rw [hq]
    simp
  let P : StandardEtalePair B.obj :=
    { f := p, monic_f := hp, g := p.derivative * q, cond := ⟨q, 0, 1, by ring⟩ }
  let x : P.Ring := P.X
  have hpx : aeval x p = 0 := P.hasMap_X.1
  have hqx : IsUnit (aeval x q) :=
    isUnit_of_mul_isUnit_right (by simpa only [P, map_mul] using P.hasMap_X.2)
  -- The adjoined root is congruent to `a` modulo the extended ideal.
  have hxa : x - algebraMap B.obj P.Ring a ∈ J.map (algebraMap B.obj P.Ring) := by
    have h := congrArg (aeval x) hq
    simp only [hpx, map_add, map_mul, map_sub, aeval_C, aeval_X] at h
    have h' : (x - algebraMap B.obj P.Ring a) * aeval x q =
        -algebraMap B.obj P.Ring (p.eval a) := by
      linear_combination -h
    rw [← Ideal.mul_unit_mem_iff_mem _ hqx, h']
    exact neg_mem (Ideal.mem_map_of_mem _ hpa)
  -- The defining equations hold modulo `I B` at `a`, so the closed fibre is unchanged.
  have hmk (r : B.obj[X]) : aeval (Ideal.Quotient.mk J a) r = Ideal.Quotient.mk J (r.eval a) := by
    rw [aeval_def, Ideal.Quotient.algebraMap_eq, eval₂_hom]
  have hσ : P.HasMap (Ideal.Quotient.mk J a) := by
    refine ⟨?_, ?_⟩
    · rw [hmk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpa
    · rw [hmk, eval_mul, hqa, map_mul]
      exact hu.mul hu
  have hPbij : Function.Bijective (reducedMap J P.Ring) := by
    convert P.algebraMap_quotient_bijective_of_hasMap J hσ hxa
    exact Ideal.Quotient.ringHom_ext (RingHom.ext (reducedMap_mk J P.Ring))
  -- The standard étale algebra is an étale neighbourhood of `(R, I)` over `B`.
  let : Algebra R P.Ring := ((algebraMap B.obj P.Ring).comp (algebraMap R B.obj)).toAlgebra
  have : IsScalarTower R B.obj P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R P.Ring := Algebra.Etale.comp R B.obj P.Ring
  let D : Neighbourhood.{u, u} I :=
    ⟨CommAlgCat.of R P.Ring, (isNeighbourhood_iff I _).mpr
      ⟨inferInstance, reducedMap_bijective_of_tower I B.obj P.Ring hBBij hPbij⟩⟩
  refine ⟨D, ObjectProperty.homMk (CommAlgCat.ofHom (IsScalarTower.toAlgHom R B.obj P.Ring)), x,
    ?_, ?_⟩
  · rw [IsRoot, eval_map]
    exact hpx
  · have hJ : J.map (algebraMap B.obj P.Ring) = I.map (algebraMap R P.Ring) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hJ ▸ hxa

/-- **The henselization of a pair is henselian.** The pair formed by the henselization of
`(R, I)` and the extended ideal is a henselian pair, with no hypothesis on `R` or `I`. -/
instance henselian : HenselianRing (algebra I) (extended I) where
  jac := extended_le_jacobson I
  is_henselian f hf a₀ hfa₀ hu := by
    -- Descend `a₀` and the coefficients of `f` below its leading term to a common stage `B`.
    obtain ⟨B, b, hb⟩ := exists_stage_family I
      (fun i : Option (Fin f.natDegree) ↦ i.elim a₀ fun j ↦ f.coeff j)
    have hb₀ : stage I B (b none) = a₀ := hb none
    have hbj (j : Fin f.natDegree) : stage I B (b (some j)) = f.coeff j := hb (some j)
    let g : B.obj[X] := X ^ f.natDegree + ∑ j : Fin f.natDegree, C (b (some j)) * X ^ (j : ℕ)
    have hg : g.Monic := monic_X_pow_add (degree_sum_fin_lt _)
    have hgf : g.map (stage I B : B.obj →+* algebra I) = f := by
      conv_rhs => rw [hf.as_sum, ← Fin.sum_univ_eq_sum_range (fun j ↦ C (f.coeff j) * X ^ j)]
      simp [g, Polynomial.map_sum, hbj]
    have hga (r : B.obj[X]) :
        stage I B (r.eval (b none)) = (r.map (stage I B : B.obj →+* algebra I)).eval a₀ := by
      rw [← hb₀]
      exact (eval_map_apply ..).symm
    -- At the stage `B`, the simple-root hypotheses hold modulo the extended ideal of `B`.
    obtain ⟨D, φ, c, hroot, hc⟩ := exists_hom_isRoot_sub_mem I B hg (a := b none)
      (by rw [← comap_stage_extended I B, Ideal.mem_comap, RingHom.coe_coe, hga, hgf]; exact hfa₀)
      (by rw [← isUnit_quotient_stage_iff, hga, ← derivative_map, hgf]; exact hu)
    have hφ : (stage I D : D.obj →+* algebra I).comp (φ.hom.hom : B.obj →+* D.obj) =
        (stage I B : B.obj →+* algebra I) := by
      ext y
      exact stage_hom_apply I φ y
    refine ⟨stage I D c, ?_, ?_⟩
    · simpa only [Polynomial.map_map, hφ, hgf, RingHom.coe_coe] using
        hroot.map (stage I D : D.obj →+* algebra I)
    · rw [← hb₀, ← stage_hom_apply I φ (b none), ← map_sub, ← map_stage_map_algebraMap I D]
      exact Ideal.mem_map_of_mem _ hc

end TauCeti.Henselization
