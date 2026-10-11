/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import TauCeti.Topology.JacobsonSpace

/-!
# Multiplication by a nonzero integer is finite

Let `E` be an elliptic curve over a scheme `S` and let `n` be a nonzero integer. This file proves
that multiplication by `n`, `[n] : E ⟶ E`, is a finite morphism of schemes. It is proper, since `E`
is proper and separated over `S`, so by Zariski's main theorem it suffices that `[n]` is locally
quasi-finite, that is, that each of its fibres is finite.

The fibre of `[n]` over a point `y` of `E` is contained in the image of a fibre of multiplication
by `n` on the base change of `E` to an algebraic closure `Ω` of the residue field of `y`, namely
the fibre over the `Ω`-point given by `y`, since that multiplication by `n` is the base change of
`[n]`. Over the algebraically closed field `Ω`, the closed points of a scheme locally of finite
type are its `Ω`-points. The `Ω`-points in a fibre of `[n]` over an `Ω`-point form a coset of the
group of `Ω`-points of `E` killed by `n`, which is finite, and a closed subset of a Jacobson space
with finitely many closed points is finite.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.locallyQuasiFinite_mulBy_left`: multiplication by a
  nonzero integer is locally quasi-finite.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFinite_mulBy_left`: multiplication by a nonzero
  integer is finite.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

-- Over an algebraically closed field `K`, the fibre of `[n]` over a `K`-point `σ` of `E` is
-- finite: its closed points are `K`-points `x` with `x ^ n = σ`, which form a coset of the finite
-- group of `K`-points killed by `n`.
private theorem finite_preimage_range_mulBy_left {K : Type u} [Field K] [IsAlgClosed K]
    (E : EllipticCurveGeom (Spec (.of K))) {n : ℤ} (hn : n ≠ 0) (σ : Spec (.of K) ⟶ E.carrier)
    (hσ : σ ≫ E.structureMap = 𝟙 _) :
    ((E.mulBy n).left ⁻¹' Set.range σ).Finite := by
  have : JacobsonSpace E.carrier := LocallyOfFiniteType.jacobsonSpace E.structureMap
  have hσc : IsClosed (Set.range σ) :=
    have := isClosedImmersion_of_comp_eq_id _ σ hσ
    σ.isClosedEmbedding.isClosed_range
  refine IsClosed.finite_of_finite_inter_closedPoints (X := E.carrier)
    (hσc.preimage (E.mulBy n).left.continuous) ?_
  let s : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap := Over.homMk σ (by simpa using hσ)
  have hfin : Finite {x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap // x ^ n = s} := by
    have := E.finite_comp_mulBy_eq_one hn
    simp only [comp_mulBy] at this
    by_cases h : ∃ x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap, x₀ ^ n = s
    · obtain ⟨x₀, hx₀⟩ := h
      exact .of_injective (β := {x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap //
        x ^ n = 1}) (fun x ↦ ⟨x.1 / x₀, by rw [div_zpow, x.2, hx₀, div_self']⟩)
        fun x y hxy ↦ Subtype.ext (div_left_injective (congrArg Subtype.val hxy))
    · have : IsEmpty {x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap // x ^ n = s} :=
        ⟨fun x ↦ h ⟨x.1, x.2⟩⟩
      infer_instance
  -- a closed point `z` of the fibre is the image of the `K`-point `pointOfClosedPoint z`, and
  -- `[n]` sends that point to `σ`, as both are `K`-points with the same image
  refine Set.finite_coe_iff.mp (Finite.of_injective (β := {x : 𝟙_ (Over (Spec (.of K))) ⟶
    Over.mk E.structureMap // x ^ n = s})
    (fun z ↦ ⟨Over.homMk (pointOfClosedPoint E.structureMap z.1 z.2.2)
      (by simpa using pointOfClosedPoint_comp E.structureMap z.1 z.2.2), ?_⟩) ?_)
  · have hsec (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap) :
        x.left ≫ E.structureMap = 𝟙 _ := by simpa using x.w
    rw [← comp_mulBy]
    ext1
    refine ext_of_apply_closedPoint_eq E.structureMap (hsec _) (hsec s) ?_
    simp only [Over.comp_left, Over.homMk_left, s]
    obtain ⟨a, ha⟩ := z.2.1
    exact (Scheme.Hom.comp_apply ..).trans ((congrArg _ (pointOfClosedPoint_apply ..)).trans
      (ha.symm.trans (congrArg σ (Subsingleton.elim _ _))))
  · intro z z' h
    have := congrArg (fun x ↦ x.1.left (IsLocalRing.closedPoint K)) h
    simp only [Over.homMk_left] at this
    exact Subtype.ext ((pointOfClosedPoint_apply ..).symm.trans
      (this.trans (pointOfClosedPoint_apply ..)))

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **Multiplication by a nonzero integer is locally quasi-finite**: every fibre of
`[n] : E ⟶ E` is finite. -/
theorem locallyQuasiFinite_mulBy_left {n : ℤ} (hn : n ≠ 0) :
    LocallyQuasiFinite (E.mulBy n).left := by
  refine locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun y ↦ ?_
  -- the geometric point `t` of `E` at `y`, with values in an algebraic closure of `κ(y)`
  let t : Spec (.of (AlgebraicClosure (E.carrier.residueField y))) ⟶ E.carrier :=
    Spec.map (CommRingCat.ofHom (algebraMap (E.carrier.residueField y) _)) ≫
      E.carrier.fromSpecResidueField y
  -- the base change `E'` of `E` along `t`, with the section `σ` induced by `t`
  let E' := E.baseChange (t ≫ E.structureMap)
  let g : E'.carrier ⟶ E.carrier := (E.baseChangeIso _).hom ≫ pullback.fst _ _
  let σ : Spec (.of (AlgebraicClosure (E.carrier.residueField y))) ⟶ E'.carrier :=
    pullback.lift t (𝟙 _) (by simp) ≫ (E.baseChangeIso _).inv
  have hσ : σ ≫ E'.structureMap = 𝟙 _ := by simp [σ, E', ← baseChangeIso_hom_snd]
  have hσg (a) : g (σ a) = y := by
    have : σ ≫ g = t := by simp [g, σ]
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  -- `[n]` on `E'` is the base change of `[n]` on `E` along `g`, so the fibre of `[n]` over `y` is
  -- the image under `g` of the fibre of `[n]` on `E'` over `σ`
  have hsq := isPullback_mulBy_left_of_isPullback (E.isPullback_baseChange (t ≫ E.structureMap))
    (by simp) n
  refine ((finite_preimage_range_mulBy_left E' hn σ hσ).image g).subset fun x hx ↦ ?_
  obtain ⟨a⟩ : Nonempty (Spec (.of (AlgebraicClosure (E.carrier.residueField y)))) :=
    inferInstance
  obtain ⟨p, hpx, hp⟩ := Scheme.exists_preimage_of_isPullback hsq x (σ a) (by rw [hσg]; exact hx)
  exact ⟨p, ⟨a, hp.symm⟩, hpx⟩

/-- **Multiplication by a nonzero integer is finite** (Katz–Mazur 2.3.1): it is proper and locally
quasi-finite. -/
theorem isFinite_mulBy_left {n : ℤ} (hn : n ≠ 0) : IsFinite (E.mulBy n).left :=
  have := E.locallyQuasiFinite_mulBy_left hn
  .of_isProper_of_locallyQuasiFinite _

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
