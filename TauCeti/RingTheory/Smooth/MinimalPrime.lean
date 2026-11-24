/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import TauCeti.RingTheory.Kaehler.Separable

import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import TauCeti.RingTheory.Ideal.GoingDown
import TauCeti.RingTheory.Kaehler.UnramifiedBase
import TauCeti.RingTheory.Unramified.LocalRing

/-!
# Generic residue fields of a smooth algebra of relative dimension one

Let `K` be a field and `B` a `K`-algebra which is smooth of relative dimension one: `Spec B` is
covered by basic opens `D(t)` on which `B_t` is standard smooth of relative dimension one over `K`
(`RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)`). This is the ring of sections
of a scheme smooth of relative dimension one over `K` on any affine open. This file proves that at
every minimal prime `p` of `B` the residue field `κ(p)`, the function field of an irreducible
component of `Spec B`, is transcendental over `K` and has one-dimensional Kähler differentials.

These are the conditions on the generic fibre under which the normalization of a model of a curve
over a possibly non-excellent discrete valuation ring is finite
(`TauCeti.finite_integralClosure_of_forall_transcendental_and_finrank_kaehlerDifferential_eq_one`).

Choose `t ∉ p` with `B_t` standard smooth of relative dimension one. Then `B_t` is étale over a
polynomial ring `K[X]` (`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`).
The kernel of `B_t → κ(p)` is a minimal prime of `B_t`; by going down along the flat map
`K[X] → B_t` it contracts to the zero ideal of `K[X]`. So the image of `X` in `κ(p)` is
transcendental over `K`. Since `κ(p)` is formally unramified over `K[X]`, the module
`Ω[κ(p)⁄K]` is spanned by the image of `d X`
(`KaehlerDifferential.mapBaseChange_surjective_of_formallyUnramified`), so its dimension is at
most one, and it is nonzero because `κ(p)` is not algebraic over `K`
(`TauCeti.finrank_kaehlerDifferential_pos`).

## Main results

All in the namespace `TauCeti`:

* `finrank_kaehlerDifferential_le_of_formallyUnramified_mvPolynomial`: a field formally
  unramified over a polynomial ring `K[X_i]` has Kähler differentials over `K` of dimension at most
  the number of variables.
* `transcendental_and_finrank_kaehlerDifferential_eq_one_of_formallyUnramified`: a field which
  contains `K[X]` and is formally unramified over it is transcendental over `K`, with
  one-dimensional Kähler differentials.
* `transcendental_and_finrank_kaehlerDifferential_eq_one_of_isStandardSmoothOfRelativeDimension`:
  the same for a field formally unramified over a standard smooth algebra `S` of relative
  dimension one, when the kernel of `S → L` is a minimal prime of `S`.
* `transcendental_and_finrank_kaehlerDifferential_residueField_eq_one`: the residue field
  of a minimal prime of a `K`-algebra smooth of relative dimension one is transcendental over `K`,
  with one-dimensional Kähler differentials.

## References

* The Stacks Project, Tag 00T7 (standard smooth algebras).
* The Stacks Project, Lemma 55.8.2 (0C2T), where these conditions are used.
-/

public section

open KaehlerDifferential
open scoped TensorProduct

namespace TauCeti

universe u

/-- **Differentials of a field unramified over a polynomial ring.** If a field `L` over a ring `K`
is a formally unramified algebra over the polynomial ring `K[X_i]`, then `Ω[L⁄K]` is spanned by the
images of the `d X_i`, so its dimension is at most the number of variables. -/
theorem finrank_kaehlerDifferential_le_of_formallyUnramified_mvPolynomial {σ K L : Type*}
    [Finite σ] [CommRing K] [Field L] [Algebra K L] [Algebra (MvPolynomial σ K) L]
    [IsScalarTower K (MvPolynomial σ K) L] [Algebra.FormallyUnramified (MvPolynomial σ K) L] :
    Module.finrank L Ω[L⁄K] ≤ Nat.card σ := by
  have hsurj := mapBaseChange_surjective_of_formallyUnramified K (MvPolynomial σ K) L
  have b := (mvPolynomialBasis K σ).baseChange L
  have : Module.Finite L (L ⊗[MvPolynomial σ K] Ω[MvPolynomial σ K⁄K]) := .of_basis b
  calc Module.finrank L Ω[L⁄K]
      ≤ Module.finrank L (L ⊗[MvPolynomial σ K] Ω[MvPolynomial σ K⁄K]) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Nat.card σ := by rw [Module.finrank_eq_nat_card_basis b]

/-- **A field unramified over a polynomial ring in one variable.** Let `L` be a field over `K`,
essentially of finite type, which contains the polynomial ring `K[X]` and is formally unramified
over it. Then `L` is transcendental over `K` and `Ω[L⁄K]` is one-dimensional. -/
theorem transcendental_and_finrank_kaehlerDifferential_eq_one_of_formallyUnramified
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    [Algebra (MvPolynomial (Fin 1) K) L] [IsScalarTower K (MvPolynomial (Fin 1) K) L]
    [Algebra.FormallyUnramified (MvPolynomial (Fin 1) K) L]
    (h : Function.Injective (algebraMap (MvPolynomial (Fin 1) K) L)) :
    Algebra.Transcendental K L ∧ Module.finrank L Ω[L⁄K] = 1 := by
  have : Algebra.Transcendental K L := by
    -- The image of the variable is transcendental, since `K[X] → L` is injective.
    have hind : AlgebraicIndependent K
        fun i : Fin 1 ↦ algebraMap (MvPolynomial (Fin 1) K) L (.X i) := by
      rw [algebraicIndependent_iff_injective_aeval]
      convert h
      exact congrArg DFunLike.coe (MvPolynomial.algHom_ext (f := MvPolynomial.aeval _)
        (g := IsScalarTower.toAlgHom K _ L) fun i ↦ by
          rw [MvPolynomial.aeval_X, IsScalarTower.toAlgHom_apply])
    exact Algebra.transcendental_def.mpr ⟨_, hind.transcendental 0⟩
  refine ⟨this, le_antisymm ?_ (finrank_kaehlerDifferential_pos (k := K))⟩
  simpa using finrank_kaehlerDifferential_le_of_formallyUnramified_mvPolynomial
    (σ := Fin 1) (K := K) (L := L)

/-- **Generic points of a standard smooth algebra of relative dimension one.** Let `S` be a
standard smooth `K`-algebra of relative dimension one and `L` a field over `S`, essentially of
finite type over `K` and formally unramified over `S`, such that the kernel of `S → L` is a minimal
prime of `S`; for instance the residue field at a minimal prime. Then `L` is transcendental over
`K` and `Ω[L⁄K]` is one-dimensional. -/
theorem transcendental_and_finrank_kaehlerDifferential_eq_one_of_isStandardSmoothOfRelativeDimension
    {K S : Type u} {L : Type*} [Field K] [CommRing S] [Field L] [Algebra K S] [Algebra K L]
    [Algebra S L] [IsScalarTower K S L] [Algebra.IsStandardSmoothOfRelativeDimension 1 K S]
    [Algebra.FormallyUnramified S L] [Algebra.EssFiniteType K L]
    (hker : RingHom.ker (algebraMap S L) ∈ minimalPrimes S) :
    Algebra.Transcendental K L ∧ Module.finrank L Ω[L⁄K] = 1 := by
  -- `S` is étale over `P = K[X]`, and `L` is formally unramified over `P`.
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K S
  let P := MvPolynomial (Fin 1) K
  let : Algebra P S := g.toAlgebra
  have : IsScalarTower K P S := .of_algebraMap_eq' g.comp_algebraMap.symm
  have : Algebra.Etale P S := hg
  let : Algebra P L := ((algebraMap S L).comp g.toRingHom).toAlgebra
  have : IsScalarTower P S L := .of_algebraMap_eq' rfl
  have : IsScalarTower K P L := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P S, ← IsScalarTower.algebraMap_apply K P S,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.FormallyUnramified P L := .comp P S L
  -- By going down along the flat map `P → S`, the kernel of `S → L` contracts to `0` in `P`.
  refine transcendental_and_finrank_kaehlerDifferential_eq_one_of_formallyUnramified ?_
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hbot := Ideal.under_mem_minimalPrimes (R := P) hker
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hbot
  have hf' : f ∈ (RingHom.ker (algebraMap S L)).under P := by
    rwa [Ideal.mem_under, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
  rwa [hbot] at hf'

/-- **Generic residue fields of a smooth algebra of relative dimension one.** Let `B` be a
`K`-algebra over a field `K` which is locally standard smooth of relative dimension one. Then at
every minimal prime `p` of `B`, the residue field `κ(p)` is transcendental over `K` and its module
of Kähler differentials over `K` is one-dimensional. -/
theorem transcendental_and_finrank_kaehlerDifferential_residueField_eq_one {K B : Type u}
    [Field K] [CommRing B] [Algebra K B]
    (hB : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap K B))
    (p : Ideal B) [p.IsPrime] (hp : p ∈ minimalPrimes B) :
    Algebra.Transcendental K p.ResidueField ∧
      Module.finrank p.ResidueField Ω[p.ResidueField⁄K] = 1 := by
  have : Algebra.Smooth K B := RingHom.smooth_algebraMap.mp
    (RingHom.smooth_iff_locally_isStandardSmooth.mpr (RingHom.locally_of_locally
      (fun hf ↦ RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1 _ hf) hB))
  -- Choose `t ∉ p` such that `B_t` is standard smooth of relative dimension one.
  obtain ⟨s, hs, hst⟩ := hB
  obtain ⟨t, hts, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra! h
    exact Ideal.IsPrime.ne_top ‹_› (eq_top_iff.mpr (hs ▸ Ideal.span_le.mpr h))
  let Bt := Localization.Away t
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 K Bt := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq K B Bt]
    exact hst t hts
  -- Since `t ∉ p`, the map `B → κ(p)` factors through `B_t`.
  have hunit : IsUnit (algebraMap B p.ResidueField t) := by
    rwa [isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]
  let : Algebra Bt p.ResidueField := (IsLocalization.Away.lift t hunit).toAlgebra
  have : IsScalarTower B Bt p.ResidueField := .of_algebraMap_eq fun b ↦
    (IsLocalization.Away.lift_eq t hunit b).symm
  have : IsScalarTower K Bt p.ResidueField := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K B Bt, ← IsScalarTower.algebraMap_apply B Bt,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.FormallyUnramified Bt p.ResidueField := .of_restrictScalars B _ _
  have : Algebra.EssFiniteType K p.ResidueField := .comp K B _
  -- The kernel of `B_t → κ(p)` lies over the minimal prime `p`, so it is a minimal prime of `B_t`.
  refine
    transcendental_and_finrank_kaehlerDifferential_eq_one_of_isStandardSmoothOfRelativeDimension
      (S := Bt) ?_
  have hunder : (RingHom.ker (algebraMap Bt p.ResidueField)).under B = p := by
    rw [Ideal.under_def, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq,
      Ideal.ker_algebraMap_residueField]
  have := IsLocalization.minimalPrimes_map (.powers t) Bt (⊥ : Ideal B)
  rw [Ideal.map_bot] at this
  -- `minimalPrimes Bt` is the set of minimal primes over `⊥` by definition.
  exact (Set.ext_iff.mp this _).mpr (by rwa [Set.mem_preimage, hunder])

end TauCeti
