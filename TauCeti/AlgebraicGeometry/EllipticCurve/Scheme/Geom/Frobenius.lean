/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.RingTheory.LocalRing.Frobenius

/-!
# High Frobenius twists over Artinian local rings

Let `E` be an elliptic curve over an Artinian local `k`-algebra `R` of characteristic `p`,
with residue field identified with `k` by the coefficient map. Every sufficiently high
Frobenius twist of `E` is a constant family: it is pointed-isomorphic over `R` to the base
change of an elliptic curve over `k`.
The coefficient ring `k` needs no specified field structure.

The curve over `k` is the corresponding Frobenius twist of the special fibre. It may vary
with the iterate; no claim that Frobenius fixes its coefficients is made. The nilpotence
bound depends only on `R`, and neither perfection nor algebraic closedness of `k` is required.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, proof of 5.3.6.
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {k R : Type u} [CommRing k] [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [Algebra k R] (E : EllipticCurveGeom (Spec (.of R)))
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP R p]

/-- Every sufficiently high Frobenius twist of an elliptic curve over an Artinian local
algebra with residue field `k` is pointed-isomorphic over the base to a curve defined over `k`.
The curve over `k` is allowed to depend on the iterate. -/
theorem exists_iso_baseChange_iterateFrobenius
    (hres : Function.Bijective (algebraMap k (ResidueField R))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ E₀ : EllipticCurveGeom (Spec (.of k)),
      ∃ e : (E.baseChange (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)))).carrier ≅
          (E₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).carrier,
        e.hom ≫ (E₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).structureMap =
            (E.baseChange (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)))).structureMap ∧
          (E.baseChange (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)))).zero ≫ e.hom =
            (E₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).zero := by
  obtain ⟨N, hN⟩ := TauCeti.exists_iterateFrobenius_eq_algebraMap_comp (R := R) p hres
  refine ⟨N, fun n hn ↦ ?_⟩
  let f := (iterateFrobenius k p n).comp
    ((RingEquiv.ofBijective (algebraMap k (ResidueField R)) hres).symm.toRingHom.comp (residue R))
  let a : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom f)
  let b : Spec (.of R) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let F : Spec (.of R) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (iterateFrobenius R p n))
  have hF : b ≫ a = F := by
    rw [← Spec.map_comp]
    exact congrArg (fun g : R →+* R ↦ Spec.map (CommRingCat.ofHom g)) (hN n hn).symm
  let E₀ := E.baseChange a
  let E' := E₀.baseChange b
  let E'' := E.baseChange F
  let g₀ := (E.baseChangeIso a).hom ≫ pullback.fst E.structureMap a
  let g' := (E₀.baseChangeIso b).hom ≫ pullback.fst E₀.structureMap b
  let g'' := (E.baseChangeIso F).hom ≫ pullback.fst E.structureMap F
  have h' : IsPullback (g' ≫ g₀) E'.structureMap E.structureMap F := by
    simpa only [hF] using
      (E₀.isPullback_baseChange b).paste_horiz (E.isPullback_baseChange a)
  have h'' : IsPullback g'' E''.structureMap E.structureMap F := E.isPullback_baseChange F
  let e := h''.isoIsPullback _ _ h'
  refine ⟨E₀, e, h''.isoIsPullback_hom_snd _ _ h', ?_⟩
  apply h'.hom_ext
  · rw [Category.assoc, h''.isoIsPullback_hom_fst _ _ h']
    simp only [g'', g', g₀, E₀, F, b, Category.assoc, zero_baseChangeIso_hom_assoc,
      pullbackSection_fst, pullbackSection_fst_assoc, ← hF]
  · rw [Category.assoc, h''.isoIsPullback_hom_snd _ _ h']
    exact E''.zero_comp.trans E'.zero_comp.symm

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
