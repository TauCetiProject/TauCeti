/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.Depth.Flat
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Cohen–Macaulay rings along flat homomorphisms

For a flat local homomorphism `R → S` of Noetherian local rings, both the depth and the Krull
dimension are additive: `depth S = depth R + depth (S ⧸ 𝔪_R S)` and
`dim S = dim R + dim (S ⧸ 𝔪_R S)`. Since depth never exceeds dimension, `S` is Cohen–Macaulay
exactly when `R` and the closed fibre `S ⧸ 𝔪_R S` are. Applied at every prime, a flat Noetherian
algebra over a Cohen–Macaulay ring whose fibres `κ(p) ⊗[R] S` have Cohen–Macaulay local rings is
Cohen–Macaulay.

The fibres of a polynomial ring over `R` are polynomial rings over the residue fields of `R`,
which are regular, so polynomial rings in finitely many variables over a Cohen–Macaulay ring are
Cohen–Macaulay. This is what makes Cohen–Macaulay rings universally catenary.

Here a Noetherian ring is Cohen–Macaulay when its localizations at all primes are Cohen–Macaulay
over themselves (Stacks, Definition 10.103.12 (0AAH)).

## Main results

* `Module.isCohenMacaulay_self_iff_of_flat`: for a flat local homomorphism `R → S` of Noetherian
  local rings, `S` is Cohen–Macaulay if and only if `R` and the closed fibre `S ⧸ 𝔪_R S` are.
* `Module.isCohenMacaulay_localization_atPrime_of_flat`: for a flat Noetherian `R`-algebra `S` and
  a prime `q` of `S` over `p`, the local ring `S_q` is Cohen–Macaulay when `R_p` is and the local
  ring of the fibre `κ(p) ⊗[R] S` at the point corresponding to `q` is.
* `Polynomial.isCohenMacaulay_localization_atPrime` and
  `MvPolynomial.isCohenMacaulay_localization_atPrime`: polynomial rings in finitely many variables
  over a Noetherian Cohen–Macaulay ring are Cohen–Macaulay (Stacks, Lemma 10.103.13 (0AAI)).

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.3 and its Corollary.
* [Stacks Project, Lemma 10.103.13](https://stacks.math.columbia.edu/tag/0AAI)
-/

public section

universe u v

open IsLocalRing Algebra.TensorProduct

namespace Module

section Local

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

/-- **Cohen–Macaulay rings along a flat local homomorphism.** For a flat local homomorphism
`R → S` of Noetherian local rings, `S` is Cohen–Macaulay if and only if `R` and the closed fibre
`S ⧸ 𝔪_R S` are. The closed fibre is taken as an `S`-module; by
`Module.isCohenMacaulay_iff_isCohenMacaulay_self_of_surjective` this is the same as asking the
local ring `S ⧸ 𝔪_R S` to be Cohen–Macaulay over itself. H. Matsumura, *Commutative Ring Theory*,
Corollary of Theorem 23.3. -/
theorem isCohenMacaulay_self_iff_of_flat :
    IsCohenMacaulay S S ↔ IsCohenMacaulay R R ∧
      IsCohenMacaulay S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  set I := (maximalIdeal R).map (algebraMap R S)
  have : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top (algebraMap R S)).ne
  have : IsLocalRing (S ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  -- Going down for the flat map `R → S` gives `dim S = dim R + dim (S ⧸ I)`, where the image of
  -- `𝔪_S` is the maximal ideal of the closed fibre.
  have hdim : supportDim S S = supportDim R R + supportDim S (S ⧸ I) := by
    have h :=
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)
    rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
    rw [supportDim_self_eq_ringKrullDim, supportDim_self_eq_ringKrullDim,
      supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient,
      ← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
      ← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add]
  -- All dimensions and depths are natural numbers, with each depth at most its dimension.
  have hnat {d : ℕ∞} {n : ℕ} (h : (d : WithBot ℕ∞) ≤ n) : ∃ c : ℕ, c ≤ n ∧ d = c := by
    obtain ⟨c, hc, hcn⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp h)
    exact ⟨c, hcn, hc⟩
  obtain ⟨a, ha⟩ := exists_supportDim_eq_natCast (R := R) (M := R)
  obtain ⟨b, hb⟩ := exists_supportDim_eq_natCast (R := S) (M := S ⧸ I)
  obtain ⟨c, hca, hc⟩ := hnat (ha ▸ depth_le_supportDim (R := R) (M := R))
  obtain ⟨d, hdb, hd⟩ := hnat (hb ▸ depth_le_supportDim (R := S) (M := S ⧸ I))
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    hdim, IsLocalRing.depth_eq_add_of_flat (R := R) (S := S), ha, hb, hc, hd]
  norm_cast
  omega

end Local

section Global

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  [IsNoetherianRing S] [Module.Flat R S]

/-- **Cohen–Macaulay local rings of a flat algebra.** Let `S` be a flat Noetherian algebra over a
Noetherian ring `R`, and `q` a prime of `S` lying over `p`. If `R_p` is Cohen–Macaulay, and so is
the local ring of the fibre `κ(p) ⊗[R] S` at the prime corresponding to `q`, then `S_q` is
Cohen–Macaulay. H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.3. -/
theorem isCohenMacaulay_localization_atPrime_of_flat (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] [q.LiesOver p]
    (hp : IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p))
    (hq : ∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime], Q.comap includeRight = q →
      IsCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) :
    IsCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) := by
  -- `q` corresponds to a prime `Q` of the fibre over `p`.
  obtain ⟨Q, _, rfl⟩ : ∃ Q : Ideal (p.Fiber S), Q.IsPrime ∧ Q.comap includeRight = q :=
    ⟨_, ((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).isPrime,
      congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply _)⟩
  set r := Q.comap (includeRight : S →ₐ[R] p.Fiber S)
  let := Localization.AtPrime.algebraOfLiesOver p r
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  refine (isCohenMacaulay_self_iff_of_flat (R := Localization.AtPrime p)).2 ⟨hp, ?_⟩
  -- The closed fibre of `R_p → S_r` is the local ring of `κ(p) ⊗[R] S` at `Q`.
  have hI : p.map (algebraMap R (Localization.AtPrime r)) =
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  set I := (maximalIdeal (Localization.AtPrime p)).map
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime r))
  have : Nontrivial (Localization.AtPrime r ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (map_maximalIdeal_lt_top (algebraMap (Localization.AtPrime p) (Localization.AtPrime r))).ne
  have : IsLocalRing (Localization.AtPrime r ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let e : Localization.AtPrime r ⧸ I ≃+* Localization.AtPrime Q :=
    (Ideal.quotEquivOfEq hI.symm).trans
      (Ideal.Fiber.localizationAlgEquivQuotient p Q).toRingEquiv.symm
  exact (isCohenMacaulay_iff_isCohenMacaulay_self_of_surjective Ideal.Quotient.mk_surjective).2
    (e.isCohenMacaulay_self_iff.2 (hq Q rfl))

end Global

end Module

open Module

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **Polynomial rings over Cohen–Macaulay rings.** If every local ring of a Noetherian ring `R`
is Cohen–Macaulay, then so is every local ring of `R[X]`. The fibres of `R → R[X]` are the
polynomial rings `κ(p)[X]`, which are regular. Stacks, Lemma 10.103.13 (0AAI). -/
@[stacks 0AAI]
theorem Polynomial.isCohenMacaulay_localization_atPrime
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p))
    (q : Ideal (Polynomial R)) [q.IsPrime] :
    IsCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) :=
  isCohenMacaulay_localization_atPrime_of_flat (q.under R) q (h _) fun _ _ _ ↦
    have : IsRegularRing ((q.under R).Fiber (Polynomial R)) :=
      .of_ringEquiv (polyEquivTensor R (q.under R).ResidueField).toRingEquiv
    TauCeti.IsRegularLocalRing.isCohenMacaulay

/-- **Polynomial rings over Cohen–Macaulay rings.** If every local ring of a Noetherian ring `R`
is Cohen–Macaulay, then so is every local ring of a polynomial ring over `R` in finitely many
variables. The fibres of `R → R[X₁, …, Xₙ]` are the polynomial rings `κ(p)[X₁, …, Xₙ]`, which are
regular. Stacks, Lemma 10.103.13 (0AAI). -/
@[stacks 0AAI]
theorem MvPolynomial.isCohenMacaulay_localization_atPrime {σ : Type v} [Finite σ]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p))
    (q : Ideal (MvPolynomial σ R)) [q.IsPrime] :
    IsCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) := by
  -- Reduce to the variables `Fin n`, so that the polynomial ring lies in the universe of `R`.
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin σ
  let e := (MvPolynomial.renameEquiv R f).toRingEquiv
  refine (Localization.localRingEquiv (q.comap e.symm) q e.symm rfl).isCohenMacaulay_self_iff.1 ?_
  exact isCohenMacaulay_localization_atPrime_of_flat (R := R) (S := MvPolynomial (Fin n) R)
    ((q.comap e.symm).under R) _ (h _) fun _ _ _ ↦
      have : IsRegularRing (((q.comap e.symm).under R).Fiber (MvPolynomial (Fin n) R)) :=
        .of_ringEquiv (AlgEquiv.toRingEquiv
          (MvPolynomial.algebraTensorAlgEquiv R ((q.comap e.symm).under R).ResidueField).symm)
      TauCeti.IsRegularLocalRing.isCohenMacaulay
