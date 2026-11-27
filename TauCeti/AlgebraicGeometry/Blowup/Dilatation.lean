/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor

/-!
# The universal property of the affine dilatation

Let `I` be an ideal of `R` containing `a`. The affine blowup chart `Spec R[I/a]` is the
dilatation of `Spec R` with centre `V(I) ⊆ V(a)`. For a test scheme on which the inverse image
of `V(a)` is an effective Cartier divisor, a morphism into `Spec R` lifts uniquely to this chart
exactly when its restriction to that divisor factors scheme-theoretically through `V(I)`.
For models over a discrete valuation ring, taking `a` to be the uniformizer gives the
lifting criterion for sections whose reductions land in the centre of a smoothening step.

We use Mathlib's `Scheme.IdealSheafData.ofIdealTop` and the Tau Ceti results
`Ideal.affineBlowupLift`, `comap_affineBlowupι_eq_ofIdealTop`, and
`projReesAlgebra_hom_ext`.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §3.2, Proposition 1.
* The Stacks Project, [Lemma 31.33.2](https://stacks.math.columbia.edu/tag/0804).
-/

public section

open CategoryTheory AlgebraicGeometry reesAlgebra Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {a : R}
  (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away a S]

/-- A morphism `f : T ⟶ Spec R` on which `V(a)` pulls back to an effective Cartier divisor
lifts uniquely to `Spec R[I/a]` exactly when the inverse images of `V(I)` and `V(a)` agree.
This is the affine case of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.2, Proposition 1. -/
theorem existsUnique_comp_affineBlowup_eq_iff (ha : a ∈ I) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of R))
    (hD : ((ofIdealTop ((Ideal.span {a}).map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
      f).IsEffectiveCartier) :
    (∃! g : T ⟶ Spec (.of (I.affineBlowup a S)),
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (I.affineBlowup a S))) = f) ↔
    (ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap f =
      (ofIdealTop ((Ideal.span {a}).map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap f := by
  let π := Spec.map (CommRingCat.ofHom (algebraMap R (I.affineBlowup a S)))
  let J := ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)
  let D := ofIdealTop ((Ideal.span {a}).map (Scheme.ΓSpecIso (.of R)).inv.hom)
  let ι := affineBlowupι S ha
  let β := Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom
  have hι : ι ≫ β = π := affineBlowupι_toSpecZero S ha
  refine (⟨?_, ?_⟩ : (∃! g, g ≫ π = f) ↔ J.comap f = D.comap f)
  · rintro ⟨g, hg, -⟩
    rw [← hg, comap_comp, comap_comp, ← hι]
    exact congrArg (fun K ↦ K.comap g) ((comap_affineBlowupι_eq_ofIdealTop S ha).trans
      (comap_affineBlowupι_ofIdealTop_span_singleton S ha a).symm)
  intro h
  have hJ : (J.comap f).IsEffectiveCartier := h.symm ▸ hD
  obtain ⟨g, hg, huniq⟩ : ∃! g, g ≫ β = f :=
    existsUnique_comp_toSpecZero_reesAlgebra_eq_of_isEffectiveCartier hJ
  have hrange : Set.range g ⊆ Set.range ι := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨U, hx, b, hb, hU⟩ := (isEffectiveCartier_iff _).mp hD x
    let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top
    have hD' : (D.comap f).ideal U = Ideal.span {ψ a} := by
      dsimp only [D]
      rw [ideal_comap_ofIdealTop_map_ΓSpecIso_inv, Ideal.map_span, Set.image_singleton]
    have hI : I.map ψ.hom = Ideal.span {ψ a} := by
      rw [← hD', ← h, ideal_comap_ofIdealTop_map_ΓSpecIso_inv]
    obtain ⟨c, rfl⟩ := Ideal.span_singleton_le_span_singleton.mp (hU.symm.trans hD').le
    let : Algebra R Γ(T, U) := ψ.hom.toAlgebra
    let φ := Ideal.affineBlowupLift I a S hI.le (IsSMulRegular.mul_iff.mp hb).1.isLeftRegular
    let k := U.property.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
    have hk : k ≫ π = U.val.ι ≫ f := by
      dsimp only [k, π]
      rw [Category.assoc, ← Spec.map_comp, ← U.property.isoSpec.eq_inv_comp,
        ← Category.assoc, U.property.isoSpec_inv_ι,
        IsAffineOpen.fromSpec_comp_eq_SpecMap f U.property]
      exact congrArg Spec.map (CommRingCat.hom_ext φ.comp_algebraMap)
    have hcomp : (U.val.ι ≫ g) ≫ β = (k ≫ ι) ≫ β := by simp only [Category.assoc, hg, hι, hk]
    have heq := projReesAlgebra_hom_ext hcomp (by
      rw [Category.assoc, hg, comap_comp]
      exact hJ.comap _)
    exact ⟨k ⟨x, hx⟩, congrArg (fun m : U.val.toScheme ⟶ Proj (grade I) ↦
      m ⟨x, hx⟩) heq.symm⟩
  refine ⟨IsOpenImmersion.lift ι g hrange, ?_, ?_⟩
  · suffices IsOpenImmersion.lift ι g hrange ≫ π = f from this
    rw [← hι, IsOpenImmersion.lift_fac_assoc, hg]
  · exact fun l hl ↦ IsOpenImmersion.lift_uniq ι g hrange l
      (huniq (l ≫ ι) ((Category.assoc _ _ _).trans (hι ▸ hl)))

end TauCeti.AlgebraicGeometry
