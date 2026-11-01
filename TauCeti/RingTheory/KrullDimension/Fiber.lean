/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Nakayama

/-!
# Krull dimension and the fibres of a ring homomorphism

Let `S` be a Noetherian algebra over a Noetherian ring `R`. For a prime `P` of `S` lying over a
prime `p` of `R`, the height of `P` is at most the height of `p` plus the Krull dimension of the
fibre `p.Fiber S = κ(p) ⊗[R] S`. Consequently the Krull dimension of `S` is at most the Krull
dimension of `R` plus any common bound on the Krull dimensions of the fibres.

This is the algebraic input for the fibrewise dimension inequality of morphisms of schemes: the
Krull dimension of a locally Noetherian scheme is at most the dimension of the target plus the
maximal dimension of a fibre, so relative dimension bounds add up under composition.

The key input is Mathlib's `Ideal.height_le_height_add_of_liesOver`, which bounds the height of
`P` using the height of its image in `S ⧸ pS`. A chain of primes of `S ⧸ pS` ending at the image
of `P` consists of primes lying over `p`, so its length is bounded by the Krull dimension of the
set-theoretic fibre of `Spec S → Spec R` over `p`. Mathlib's
`PrimeSpectrum.preimageOrderIsoFiber` identifies that fibre with `Spec (p.Fiber S)`.

## Main results

* `Ideal.height_map_quotientMk_le_ringKrullDim_fiber`: the height of the image in `S ⧸ pS` of a
  prime `P` lying over `p` is at most the Krull dimension of the fibre over `p`.
* `Ideal.height_le_height_add_ringKrullDim_fiber`: the height of a prime `P` lying over `p` is
  at most the height of `p` plus the Krull dimension of the fibre over `p`.
* `Ideal.height_eq_height_under_of_quasiFinite`: along a quasi-finite algebra satisfying going
  down, for instance an étale algebra, the height of a prime equals the height of the prime
  below it.
* `Ideal.ringKrullDim_localization_atPrime_eq_height_under`: under the same hypotheses, the
  localization of `S` at a prime `P` has Krull dimension the height of the prime below `P`.
* `Ideal.ringKrullDim_localization_atPrime_quotient_map_eq_zero`: for a quasi-finite algebra and
  a prime `P` over `p`, the fibre `S_P ⧸ p S_P` of the local ring `S_P` has Krull dimension zero.
* `TauCeti.ringKrullDim_le_ringKrullDim_add_of_ringKrullDim_fiber_le`: the Krull dimension of `S`
  is at most that of `R` plus a bound on the Krull dimensions of all fibres.
* `TauCeti.ringKrullDim_quotient_map_maximalIdeal_eq_zero`: the closed fibre `S ⧸ 𝔪S` of a finite
  nonzero algebra over a local ring `(R, 𝔪)` has Krull dimension zero.
* `TauCeti.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq`: a flat local homomorphism whose
  closed fibre is a field, such as the completion of a Noetherian local ring, preserves the Krull
  dimension.
* `TauCeti.ringKrullDim_le_ringKrullDim_add_ringKrullDim_quotient_map_maximalIdeal`: for a local
  homomorphism of Noetherian local rings, `dim S ≤ dim R + dim S ⧸ 𝔪_R S`.
* `TauCeti.ringKrullDim_quotient_map_maximalIdeal_quotient`: dividing the base by an ideal `J`
  with `R ⧸ J` local does not change the closed fibre.

## References

* [Stacks Project, Tag 00OM](https://stacks.math.columbia.edu/tag/00OM)
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
-/

public section

open Order

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Ideal

/-- The height of the image in `S ⧸ pS` of a prime `P` of `S` lying over `p` is at most the
Krull dimension of the fibre `κ(p) ⊗[R] S`. -/
theorem height_map_quotientMk_le_ringKrullDim_fiber (p : Ideal R) [p.IsPrime] (P : Ideal S)
    [P.IsPrime] [P.LiesOver p] :
    ((P.map (Quotient.mk (p.map (algebraMap R S)))).height : WithBot ℕ∞) ≤
      ringKrullDim (p.Fiber S) := by
  set I := p.map (algebraMap R S)
  have hIP : I ≤ P := map_le_iff_le_comap.mpr (over_def P p).le
  have : (P.map (Quotient.mk I)).IsPrime := isPrime_map_quotientMk_of_isPrime hIP
  have hcomap : (P.map (Quotient.mk I)).comap (Quotient.mk I) = P := comap_map_mk hIP
  -- The fibre of `Spec S → Spec R` over `p`, as a set of points of `Spec S`.
  let F := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨p, ‹_›⟩}
  -- Every prime of `S ⧸ pS` contained in the image of `P` lies over `p`.
  have hmem (Q : PrimeSpectrum (S ⧸ I)) (hQ : Q.asIdeal ≤ P.map (Quotient.mk I)) :
      PrimeSpectrum.comap (Quotient.mk I) Q ∈ F := by
    refine PrimeSpectrum.ext (le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_)
    · exact (mem_of_liesOver P p x).mpr (hcomap ▸ hQ hx)
    · have h0 : algebraMap R (S ⧸ I) x = 0 := by
        rw [← Quotient.mk_algebraMap]
        exact Quotient.eq_zero_iff_mem.mpr (mem_map_of_mem _ hx)
      simp [h0]
  have hP : (⟨P, ‹_›⟩ : PrimeSpectrum S) ∈ F := PrimeSpectrum.ext (over_def P p).symm
  rw [ringKrullDim, ← krullDim_eq_of_orderIso (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p, ‹_›⟩)]
  refine le_trans ?_ (height_le_krullDim (⟨⟨P, ‹_›⟩, hP⟩ : F))
  rw [PrimeSpectrum.height_eq_orderHeight ⟨_, this⟩]
  refine WithBot.coe_le_coe.mpr (height_le_iff'.mpr fun l hl ↦ ?_)
  have hle (i : Fin (l.length + 1)) : (l i).asIdeal ≤ P.map (Quotient.mk I) :=
    ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (l.monotone (Fin.le_last i))).trans
      (congrArg PrimeSpectrum.asIdeal hl).le
  -- Pull the chain back to `Spec S`; it stays inside the fibre over `p`.
  let l' : LTSeries F :=
    { length := l.length
      toFun i := ⟨PrimeSpectrum.comap (Quotient.mk I) (l i), hmem _ (hle i)⟩
      step i := RingHom.strictMono_comap_of_surjective Quotient.mk_surjective (l.step i) }
  have hlast : l'.last = ⟨⟨P, ‹_›⟩, hP⟩ :=
    Subtype.ext (PrimeSpectrum.ext ((congrArg (fun Q ↦ (PrimeSpectrum.asIdeal Q).comap
      (Quotient.mk I)) hl).trans hcomap))
  exact hlast ▸ length_le_height_last (p := l')

/-- Let `S` be a Noetherian algebra over a Noetherian ring `R`. The height of a prime `P` of `S`
lying over `p` is at most the height of `p` plus the Krull dimension of the fibre
`κ(p) ⊗[R] S`. -/
@[stacks 00OM]
theorem height_le_height_add_ringKrullDim_fiber [IsNoetherianRing R] [IsNoetherianRing S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (P.height : WithBot ℕ∞) ≤ p.height + ringKrullDim (p.Fiber S) :=
  (WithBot.coe_le_coe.mpr (height_le_height_add_of_liesOver p P)).trans <| by
    rw [WithBot.coe_add]
    gcongr
    exact height_map_quotientMk_le_ringKrullDim_fiber p P

/-- Let `S` be a Noetherian `R`-algebra which is quasi-finite and satisfies going down, for
instance a flat quasi-finite algebra. Then the height of a prime `P` of `S` is the height of the
prime of `R` below it. -/
@[stacks 00ON]
theorem height_eq_height_under_of_quasiFinite [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.HasGoingDown R S] [Algebra.QuasiFinite R S] (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  rw [height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  -- The fibre over `P.under R` is Artinian, so the image of `P` in it has height zero.
  have h := (height_map_quotientMk_le_ringKrullDim_fiber (P.under R) P).trans
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 ((P.under R).Fiber S)))
  have h0 : (P.map (Quotient.mk ((P.under R).map (algebraMap R S)))).height = 0 :=
    nonpos_iff_eq_zero.mp (by exact_mod_cast h)
  rw [h0, add_zero]

variable (R) in
/-- Let `S` be a Noetherian `R`-algebra which is quasi-finite and satisfies going down, for
instance a finite torsion-free algebra over a Noetherian integrally closed domain. Then the
localization of `S` at a prime `P` has Krull dimension the height of the prime of `R` below `P`. -/
theorem ringKrullDim_localization_atPrime_eq_height_under [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra.HasGoingDown R S] [Algebra.QuasiFinite R S] (P : Ideal S)
    [P.IsPrime] : ringKrullDim (Localization.AtPrime P) = (P.under R).height := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P,
    height_eq_height_under_of_quasiFinite (R := R)]

/-- Let `S` be a quasi-finite `R`-algebra and `P` a prime of `S` lying over `p`. The fibre
`S_P ⧸ p S_P` of the local ring `S_P` over `p` has Krull dimension zero. -/
theorem ringKrullDim_localization_atPrime_quotient_map_eq_zero [Algebra.QuasiFinite R S]
    (p : Ideal R) (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    ringKrullDim (Localization.AtPrime P ⧸ p.map (algebraMap R (Localization.AtPrime P))) = 0 := by
  have hle : p.map (algebraMap R (Localization.AtPrime P)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [map_le_iff_le_comap, ← under_def, ← under_under (B := S),
      Localization.AtPrime.under_maximalIdeal, ← over_def P p]
  have : Nontrivial (Localization.AtPrime P ⧸ p.map (algebraMap R (Localization.AtPrime P))) :=
    Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top IsPrime.ne_top' hle)
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

end Ideal

namespace TauCeti

/-- The Krull dimension of a Noetherian algebra `S` over a Noetherian ring `R` is at most the
Krull dimension of `R` plus any common bound on the Krull dimensions of the fibres
`κ(p) ⊗[R] S`. -/
theorem ringKrullDim_le_ringKrullDim_add_of_ringKrullDim_fiber_le [IsNoetherianRing R]
    [IsNoetherianRing S] {d : WithBot ℕ∞}
    (h : ∀ (p : Ideal R) [p.IsPrime], ringKrullDim (p.Fiber S) ≤ d) :
    ringKrullDim S ≤ ringKrullDim R + d := by
  refine (ringKrullDim_le_iff_height_le _).mpr fun P hP ↦ ?_
  have : (P.under R).IsPrime := Ideal.IsPrime.under R P
  refine (Ideal.height_le_height_add_ringKrullDim_fiber (P.under R) P).trans ?_
  gcongr
  · exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · exact h _

open IsLocalRing in
/-- The closed fibre `S ⧸ 𝔪S` of a finite nonzero algebra `S` over a local ring `(R, 𝔪)` has Krull
dimension zero: it is a nonzero finite algebra over the residue field, hence Artinian. -/
theorem ringKrullDim_quotient_map_maximalIdeal_eq_zero [IsLocalRing R] [Module.Finite R S]
    [Nontrivial S] : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 := by
  set I := (maximalIdeal R).map (algebraMap R S) with hIdef
  -- By Nakayama's lemma `𝔪S ≠ S`, since `S` is a finite nonzero `R`-module.
  have : Nontrivial (S ⧸ I) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun hI ↦
      Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson (Module.annihilator R S)) ?_
    rw [Ideal.smul_top_eq_map, ← hIdef, hI, Submodule.restrictScalars_top]
  have : Module.Finite R (S ⧸ I) :=
    .of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ I) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (R ⧸ maximalIdeal R) :=
    letI := Ideal.Quotient.field (maximalIdeal R)
    inferInstance
  have : IsArtinianRing (S ⧸ I) := .of_finite (R ⧸ maximalIdeal R) _
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

open IsLocalRing in
/-- Along a flat homomorphism of local rings under which the maximal ideal of `R` generates the
maximal ideal of `S`, so that the closed fibre is a field, the Krull dimensions of `R` and `S`
agree. -/
theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    ringKrullDim S = ringKrullDim R := by
  have : IsLocalHom (algebraMap R S) := ((local_hom_TFAE (algebraMap R S)).out 1 3).mpr h.le
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S), h,
    Ideal.map_quotient_self, Ideal.height_bot, add_zero]

open IsLocalRing in
/-- For a local homomorphism of Noetherian local rings `R → S`, the Krull dimension of `S` is at
most the Krull dimension of `R` plus that of the closed fibre `S ⧸ 𝔪_R S`. -/
@[stacks 00OM "for the maximal ideals"]
theorem ringKrullDim_le_ringKrullDim_add_ringKrullDim_quotient_map_maximalIdeal [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] :
    ringKrullDim S ≤ ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have h := WithBot.coe_le_coe.mpr
    (Ideal.height_le_height_add_of_liesOver (maximalIdeal R) (maximalIdeal S))
  rw [maximalIdeal_height_eq_ringKrullDim, WithBot.coe_add,
    maximalIdeal_height_eq_ringKrullDim] at h
  refine h.trans (add_le_add_right (Ideal.height_le_ringKrullDim_of_ne_top ?_) _)
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap (algebraMap R S)).ge
  exact (Ideal.isPrime_map_quotientMk_of_isPrime hle).ne_top

open IsLocalRing in
/-- Dividing the base of a local `R`-algebra `S` by an ideal `J`, with `R ⧸ J` local, does not
change the closed fibre: the closed fibre of `R ⧸ J → S ⧸ J S` has the Krull dimension of the
closed fibre `S ⧸ 𝔪_R S` of `R → S`. -/
theorem ringKrullDim_quotient_map_maximalIdeal_quotient [IsLocalRing R] (J : Ideal R)
    [IsLocalRing (R ⧸ J)] :
    ringKrullDim ((S ⧸ J.map (algebraMap R S)) ⧸
        (maximalIdeal (R ⧸ J)).map (algebraMap (R ⧸ J) (S ⧸ J.map (algebraMap R S)))) =
      ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have hJ : J ≤ maximalIdeal R := le_maximalIdeal fun h ↦ by
    subst h
    exact not_nontrivial (R ⧸ (⊤ : Ideal R)) inferInstance
  have hcomp : (algebraMap (R ⧸ J) (S ⧸ J.map (algebraMap R S))).comp (Ideal.Quotient.mk J) =
      (Ideal.Quotient.mk _).comp (algebraMap R S) :=
    RingHom.ext Ideal.Quotient.algebraMap_quotient_map_quotient
  rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.map_map, hcomp,
    ← Ideal.map_map]
  exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hJ))

end TauCeti
