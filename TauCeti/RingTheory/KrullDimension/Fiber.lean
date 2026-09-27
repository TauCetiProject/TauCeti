/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

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
* `TauCeti.ringKrullDim_le_ringKrullDim_add_of_ringKrullDim_fiber_le`: the Krull dimension of `S`
  is at most that of `R` plus a bound on the Krull dimensions of all fibres.

## References

* [Stacks Project, Tag 00OM](https://stacks.math.columbia.edu/tag/00OM)
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

end TauCeti
