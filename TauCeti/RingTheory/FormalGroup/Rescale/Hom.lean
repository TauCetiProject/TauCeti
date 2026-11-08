/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Rescale.Basic
import TauCeti.RingTheory.MvPowerSeries.Equiv

/-!
# Rescaling homomorphisms of formal group laws

For a homomorphism `f : F → G`, rescaling both formal groups by `s` gives the
homomorphism with coefficients `s ^ (n - 1) * fₙ`. Its linear coefficient is unchanged,
and it satisfies `s fˢ(T) = f(s T)`. This construction works over any commutative ring,
even when `s` is a zero divisor: prove the homomorphism equation with an indeterminate
scale and specialize it.

Rescaling allows homomorphisms to be studied on small formal neighbourhoods without
inverting the scale in the coefficient ring. In particular, it retains the linear
coefficient that controls local indices after linearisation by a formal logarithm.

## References

* J. Silverman, *The Arithmetic of Elliptic Curves*, IV.2 and IV.6.
* M. Hazewinkel, *Formal Groups and Applications*, Chapter I, §1.
-/

public section

noncomputable section

open MvPowerSeries

namespace TauCeti.FormalGroupHom

variable {R S : Type*} [CommRing R] [CommRing S] {F G H : FormalGroup R}

private def scaledSeries (f : FormalGroupHom F G) (s : R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ s ^ (n - 1) * PowerSeries.coeff n f.toPowerSeries

private theorem coeff_scaledSeries (f : FormalGroupHom F G) (s : R) (n : ℕ) :
    PowerSeries.coeff n (scaledSeries f s) =
      s ^ (n - 1) * PowerSeries.coeff n f.toPowerSeries :=
  PowerSeries.coeff_mk _ _

private theorem constantCoeff_scaledSeries (f : FormalGroupHom F G) (s : R) :
    PowerSeries.constantCoeff (scaledSeries f s) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_scaledSeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, f.zero_constantCoeff, mul_zero]

private theorem smul_scaledSeries (f : FormalGroupHom F G) (s : R) :
    s • scaledSeries f s = PowerSeries.rescale s f.toPowerSeries := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_scaledSeries, f.zero_constantCoeff]
  | succ n => simp [coeff_scaledSeries, PowerSeries.coeff_rescale, ← mul_assoc, pow_succ']

private theorem map_scaledSeries (f : FormalGroupHom F G) (s : R) (φ : R →+* S) :
    (scaledSeries f s).map φ = scaledSeries (f.map φ) (φ s) := by
  ext n
  simp [coeff_scaledSeries]

private theorem eval_scaledSeries (f : FormalGroupHom F G) (s : R) :
    (scaledSeries (f.map Polynomial.C) Polynomial.X).map (Polynomial.evalRingHom s) =
      scaledSeries f s := by
  ext n
  simpa [coeff_scaledSeries] using
    mul_comm (PowerSeries.coeff n f.toPowerSeries) (s ^ (n - 1))

private theorem smul_subst_scaledSeries (f : FormalGroupHom F G) (s : R)
    {σ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a) :
    s • PowerSeries.subst a (scaledSeries f s) =
      PowerSeries.subst (s • a) f.toPowerSeries := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def]
  exact smul_subst_of_smul_eq_rescale
    ((smul_scaledSeries f s).trans (PowerSeries.rescale_eq s f.toPowerSeries)) ha.const

private theorem scaledSeries_hom_of_regular (f : FormalGroupHom F G) {s : R}
    (hs : IsLeftRegular s) :
    PowerSeries.subst (F.rescale s).toPowerSeries (scaledSeries f s) =
      subst (fun i ↦ (scaledSeries f s).toMvPowerSeries i) (G.rescale s).toPowerSeries := by
  have hreg : IsSMulRegular (MvPowerSeries (Fin 2) R) s := .pi fun _ ↦ hs.isSMulRegular
  have hcoords : s • (fun i : Fin 2 ↦ (scaledSeries f s).toMvPowerSeries i) =
      fun i ↦ PowerSeries.subst (s • X i) f.toPowerSeries := by
    funext i
    simpa only [Pi.smul_apply, PowerSeries.toMvPowerSeries_eq_subst] using
      smul_subst_scaledSeries f s (.X i)
  refine hreg (?_ : s • _ = s • _)
  rw [smul_subst_scaledSeries f s
      (.of_constantCoeff_zero (F.rescale s).zero_constantCoeff),
    F.smul_rescale, smul_subst_of_smul_eq_rescale (G.smul_rescale s)
      (.toMvPowerSeries (constantCoeff_scaledSeries f s)), hcoords,
    rescale_eq_subst]
  exact f.hom_subst (HasSubst.smul_X (fun _ ↦ s))

private theorem scaledSeries_hom (f : FormalGroupHom F G) (s : R) :
    PowerSeries.subst (F.rescale s).toPowerSeries (scaledSeries f s) =
      subst (fun i ↦ (scaledSeries f s).toMvPowerSeries i) (G.rescale s).toPowerSeries := by
  have h := congrArg (MvPowerSeries.map (Polynomial.evalRingHom s))
    (scaledSeries_hom_of_regular (f.map Polynomial.C) Polynomial.isRegular_X.left)
  rw [PowerSeries.map_subst
      (.of_constantCoeff_zero ((F.map Polynomial.C).rescale Polynomial.X).zero_constantCoeff),
    MvPowerSeries.map_subst (.toMvPowerSeries
      (constantCoeff_scaledSeries (f.map Polynomial.C) Polynomial.X))] at h
  have hlaw (L : FormalGroup R) :
      MvPowerSeries.map (Polynomial.evalRingHom s)
        ((L.map Polynomial.C).rescale Polynomial.X).toPowerSeries =
      (L.rescale s).toPowerSeries := by
    rw [← FormalGroup.map_toPowerSeries, FormalGroup.map_rescale, FormalGroup.map_comp]
    simp only [Polynomial.evalRingHom, Polynomial.eval₂RingHom_comp_C, FormalGroup.map_id,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  simpa only [eval_scaledSeries, hlaw, PowerSeries.map_toMvPowerSeries] using h

/-- Rescale a formal group homomorphism together with its source and target. Its coefficient
of degree `n` is multiplied by `s ^ (n - 1)`, so its linear coefficient does not change. -/
def rescale (f : FormalGroupHom F G) (s : R) :
    FormalGroupHom (F.rescale s) (G.rescale s) where
  toPowerSeries := scaledSeries f s
  zero_constantCoeff := constantCoeff_scaledSeries f s
  hom := scaledSeries_hom f s

/-- The coefficients of the rescaled homomorphism. -/
@[simp]
theorem coeff_rescale (f : FormalGroupHom F G) (s : R) (n : ℕ) :
    PowerSeries.coeff n (f.rescale s).toPowerSeries =
      s ^ (n - 1) * PowerSeries.coeff n f.toPowerSeries :=
  coeff_scaledSeries f s n

/-- Multiplying the rescaled homomorphism by the scale recovers `f(s T)`. -/
theorem smul_rescale (f : FormalGroupHom F G) (s : R) :
    s • (f.rescale s).toPowerSeries = PowerSeries.rescale s f.toPowerSeries :=
  smul_scaledSeries f s

/-- Rescaling commutes with base change, expressed on the series to avoid transports of
source and target along `FormalGroup.map_rescale`. -/
@[simp]
theorem map_rescale_toPowerSeries (f : FormalGroupHom F G) (s : R) (φ : R →+* S) :
    (f.rescale s).toPowerSeries.map φ = ((f.map φ).rescale (φ s)).toPowerSeries := by
  simpa only [rescale] using map_scaledSeries f s φ

/-- Rescaling by one leaves the homomorphism unchanged. -/
@[simp]
theorem rescale_one_toPowerSeries (f : FormalGroupHom F G) :
    (f.rescale 1).toPowerSeries = f.toPowerSeries := by
  ext n
  simp

/-- Successive rescalings multiply their scales. -/
theorem rescale_rescale_toPowerSeries (f : FormalGroupHom F G) (s t : R) :
    ((f.rescale s).rescale t).toPowerSeries = (f.rescale (s * t)).toPowerSeries := by
  ext n
  simp only [coeff_rescale]
  ring

/-- The rescaled identity is the identity of the rescaled formal group. -/
@[simp]
theorem rescale_id (F : FormalGroup R) (s : R) :
    (id F).rescale s = id (F.rescale s) := by
  ext n
  simp only [coeff_rescale, id_toPowerSeries, PowerSeries.coeff_X]
  split_ifs with h <;> simp_all

private theorem rescale_comp_of_regular (g : FormalGroupHom G H) (f : FormalGroupHom F G)
    {s : R} (hs : IsLeftRegular s) :
    ((g.comp f).rescale s).toPowerSeries =
      ((g.rescale s).comp (f.rescale s)).toPowerSeries := by
  have hreg : IsSMulRegular (PowerSeries R) s := .pi fun _ ↦ hs.isSMulRegular
  refine hreg (?_ : s • _ = s • _)
  rw [smul_rescale, comp_toPowerSeries, comp_toPowerSeries]
  dsimp only [rescale]
  rw [smul_subst_scaledSeries g s
    (.of_constantCoeff_zero (constantCoeff_scaledSeries f s)), smul_scaledSeries,
    PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply f.hasSubst (PowerSeries.HasSubst.smul_X' s)]

/-- Rescaling commutes with composition of homomorphisms. -/
@[simp]
theorem rescale_comp (g : FormalGroupHom G H) (f : FormalGroupHom F G) (s : R) :
    (g.comp f).rescale s = (g.rescale s).comp (f.rescale s) := by
  have h := congrArg (PowerSeries.map (Polynomial.evalRingHom s))
    (rescale_comp_of_regular (g.map Polynomial.C) (f.map Polynomial.C)
      Polynomial.isRegular_X.left)
  have hscaled {L M : FormalGroup R} (f : FormalGroupHom L M) :
      ((f.map Polynomial.C).rescale Polynomial.X).toPowerSeries.map
        (Polynomial.evalRingHom s) = (f.rescale s).toPowerSeries := by
    exact eval_scaledSeries f s
  apply FormalGroupHom.ext
  rw [← map_comp] at h
  simp only [comp_toPowerSeries] at h
  rw [comp_toPowerSeries]
  exact (hscaled (g.comp f)).symm.trans <| h.trans <|
    (PowerSeries.map_subst (.of_constantCoeff_zero
      ((f.map Polynomial.C).rescale Polynomial.X).zero_constantCoeff) _).trans <|
        congrArg₂ PowerSeries.subst (hscaled f) (hscaled g)

end TauCeti.FormalGroupHom

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- Multiplication of the coordinate by `s` maps the rescaled formal group `Fˢ` to `F`.
Unlike a change of coordinates, this homomorphism does not require `s` to be a unit. -/
noncomputable def rescaleHom (F : FormalGroup R) (s : R) :
    TauCeti.FormalGroupHom (F.rescale s) F where
  toPowerSeries := s • PowerSeries.X
  zero_constantCoeff := by simp
  hom := by
    rw [PowerSeries.subst_smul (.of_constantCoeff_zero (F.rescale s).zero_constantCoeff),
      PowerSeries.subst_X (.of_constantCoeff_zero (F.rescale s).zero_constantCoeff), smul_rescale,
      MvPowerSeries.rescale_eq_subst]
    congr 1
    funext i
    simp [PowerSeries.toMvPowerSeries_eq_subst,
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

@[simp]
theorem rescaleHom_toPowerSeries (F : FormalGroup R) (s : R) :
    (F.rescaleHom s).toPowerSeries = s • PowerSeries.X := (rfl)

end FormalGroup

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] {F G : FormalGroup R}

/-- The scaling maps intertwine a homomorphism and its rescaling. -/
theorem rescaleHom_comp_rescale (f : FormalGroupHom F G) (s : R) :
    (G.rescaleHom s).comp (f.rescale s) = f.comp (F.rescaleHom s) := by
  ext : 1
  rw [comp_toPowerSeries, comp_toPowerSeries, FormalGroup.rescaleHom_toPowerSeries,
    FormalGroup.rescaleHom_toPowerSeries, PowerSeries.subst_smul (f.rescale s).hasSubst,
    PowerSeries.subst_X (f.rescale s).hasSubst, smul_rescale,
    PowerSeries.rescale_eq_subst]

end TauCeti.FormalGroupHom
