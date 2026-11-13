/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.EulerCharacteristic
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# Multiplicativity of the Euler characteristic in fibre bundles

Every locally trivial map `p : E → B` with model fibre `F` is continuous
(`TauCeti.continuous_of_forall_exists_trivialization`), is a Serre fibration
(`TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`), and has every fibre `p ⁻¹' {b}`
homeomorphic to `F` (`Bundle.Trivialization.preimageSingletonHomeomorph`). Applying the Serre
spectral sequence finiteness and Euler characteristic theorems of
`TauCeti.AlgebraicTopology.Singular.Fibration.EulerCharacteristic` therefore gives, over any
(possibly disconnected and non-paracompact) base `B` of finite CW type:

* **Homological finiteness for locally trivial maps and fibre bundles.** If `H_*(F; R)` vanishes in
  large degrees, then so does `H_*(E; R)` over any ring `R`
  (`TauCeti.eventually_isZero_singularHomology_of_exists_trivialization`,
  `TauCeti.eventually_isZero_singularHomology_fiberBundle`); if `R` is Noetherian and `H_q(F; R)` is
  finitely generated in every degree `q`, then `H_n(E; R)` is finitely generated in every degree `n`
  (`TauCeti.finite_singularHomology_of_exists_trivialization`,
  `TauCeti.finite_singularHomology_fiberBundle`).
* **Multiplicativity of the homological Euler characteristic.** Over any division ring `k`, when `B`
  and `F` have finite CW type,
  `∑ᶠ i : ℕ, (-1)ⁱ dim H_i(E; k) = χ(B) · χ(F)`
  without assuming that the total space itself has finite CW type
  (`TauCeti.finsum_finrank_singularHomology_of_exists_trivialization`,
  `TauCeti.finsum_finrank_singularHomology_fiberBundle`), and more generally whenever `F` has
  finite-dimensional singular homology vanishing in large degrees
  (`TauCeti.finsum_finrank_singularHomology_of_exists_trivialization_of_finite`).
* **Multiplicativity of `eulerChar` on total spaces of finite CW type.** When the total space also
  has finite CW type, `χ(E) = χ(B) · χ(F)` (`TauCeti.eulerChar_eq_mul_of_exists_trivialization`,
  `TauCeti.eulerChar_totalSpace`).

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4, Proposition 3.
* Allen Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1.
-/

public section

noncomputable section

universe u

open Bundle CategoryTheory Limits Module Topology AlgebraicTopology

namespace TauCeti

section LocallyTrivial

variable {E B F : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
  {p : E → B} (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet)

include h

/-- A locally trivial map `p : E → B` packaged as a morphism in `TopCat`. -/
private abbrev locallyTrivialHom : TopCat.of E ⟶ TopCat.of B :=
  TopCat.ofHom ⟨p, continuous_of_forall_exists_trivialization h⟩

private lemma mem_serreFibrations_locallyTrivialHom :
    TopCat.serreFibrations (locallyTrivialHom h) :=
  TopCat.mem_serreFibrations_of_exists_trivialization h

/-- Every fibre of a locally trivial map with model fibre `F` is isomorphic in `TopCat` to `F`. -/
private def locallyTrivialFiberIso (b : B) :
    (locallyTrivialHom h).fiber b ≅ TopCat.of F :=
  TopCat.isoOfHomeo ((h b).choose.preimageSingletonHomeomorph (h b).choose_spec)

/-- Every fibre of a locally trivial map with model fibre `F` is singular-homologically isomorphic
to `F` in every degree. -/
private def locallyTrivialFiberSingularHomologyIso (R : Type u) [Ring R] (b : B) (q : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        ((locallyTrivialHom h).fiber b)) ≅
      (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (TopCat.of F)) :=
  ((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).mapIso
    (locallyTrivialFiberIso h b)

variable [FiniteCWType B]

/-- If `p : E → B` is locally trivial with model fibre `F` over a space `B` of finite CW type and
`H_*(F; R)` vanishes in all large degrees, then `H_*(E; R)` vanishes in all large degrees. -/
theorem eventually_isZero_singularHomology_of_exists_trivialization_of_eventually_isZero
    (R : Type u) [Ring R]
    (hF : ∀ᶠ q in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (TopCat.of F))) :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj
        (TopCat.of E)) :=
  TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations_of_forall
    (mem_serreFibrations_locallyTrivialHom h) R fun b ↦
      hF.mono fun q hq ↦ hq.of_iso (locallyTrivialFiberSingularHomologyIso h R b q)

/-- Over a Noetherian ring `R`, if `p : E → B` is locally trivial with model fibre `F` over a space
`B` of finite CW type and `H_q(F; R)` is finitely generated in every degree `q`, then `H_n(E; R)` is
finitely generated in every degree `n`. -/
theorem finite_singularHomology_of_exists_trivialization_of_finite
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (hF : ∀ q : ℕ, Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (TopCat.of F)))
    (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj (TopCat.of E)) :=
  TopCat.finite_singularHomology_of_mem_serreFibrations_of_forall
    (mem_serreFibrations_locallyTrivialHom h) R
    (fun b q ↦
      have := hF q
      Module.Finite.equiv (locallyTrivialFiberSingularHomologyIso h R b q).symm.toLinearEquiv)
    n

/-- Over a division ring `k`, if `p : E → B` is locally trivial with model fibre `F` over a space
`B` of finite CW type and `F` has finite-dimensional singular homology vanishing in large degrees,
then the homological Euler characteristic of `E` equals `χ(B)` times that of `F`. -/
theorem finsum_finrank_singularHomology_of_exists_trivialization_of_finite
    (k : Type u) [DivisionRing k]
    (hfin : ∀ q : ℕ, Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (TopCat.of F)))
    (hvanish : ∀ᶠ q in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (TopCat.of F))) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of E)) : ℤ) =
      eulerChar B * ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
          (TopCat.of F)) : ℤ) :=
  TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations_of_forall
    (mem_serreFibrations_locallyTrivialHom h) k
    (fun b q ↦
      have := hfin q
      Module.Finite.equiv (locallyTrivialFiberSingularHomologyIso h k b q).symm.toLinearEquiv)
    (fun b ↦ hvanish.mono fun q hq ↦
      hq.of_iso (locallyTrivialFiberSingularHomologyIso h k b q))
    (fun b ↦ finsum_congr fun q ↦ by
      rw [(locallyTrivialFiberSingularHomologyIso h k b q).toLinearEquiv.finrank_eq])

/-- If `p : E → B` is locally trivial with model fibre `F` and both `B` and `F` have finite CW type,
then `H_n(E; R)` vanishes in all large degrees over any ring `R`. -/
theorem eventually_isZero_singularHomology_of_exists_trivialization [FiniteCWType F]
    (R : Type u) [Ring R] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj
        (TopCat.of E)) :=
  eventually_isZero_singularHomology_of_exists_trivialization_of_eventually_isZero h R
    (eventually_isZero_singularHomology_of_finiteCWType F (ModuleCat.of R R))

/-- Over a Noetherian ring `R`, if `p : E → B` is locally trivial with model fibre `F` and both `B`
and `F` have finite CW type, then `H_n(E; R)` is finitely generated in every degree `n`. -/
theorem finite_singularHomology_of_exists_trivialization [FiniteCWType F]
    (R : Type u) [Ring R] [IsNoetherianRing R] (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj (TopCat.of E)) :=
  finite_singularHomology_of_exists_trivialization_of_finite h R
    (fun q ↦ finite_singularHomology_of_finiteCWType F (ModuleCat.of R R) q) n

/-- **Multiplicativity of the Euler characteristic for a locally trivial map.** Over any division
ring `k`, if `p : E → B` is locally trivial with model fibre `F` and both `B` and `F` have finite CW
type, then `∑ᶠ i : ℕ, (-1)ⁱ dim H_i(E; k) = χ(B) · χ(F)`. -/
theorem finsum_finrank_singularHomology_of_exists_trivialization (k : Type u) [DivisionRing k]
    [FiniteCWType F] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of E)) : ℤ) =
      eulerChar B * eulerChar F := by
  rw [finsum_finrank_singularHomology_of_exists_trivialization_of_finite h k
    (fun q ↦ finite_singularHomology_of_finiteCWType F (ModuleCat.of k k) q)
    (eventually_isZero_singularHomology_of_finiteCWType F (ModuleCat.of k k)),
    ← eulerChar_eq_finsum_finrank_singularHomology F k]

/-- **Multiplicativity of `eulerChar` for a locally trivial map** when `E`, `B`, and `F` all have
finite CW type: `χ(E) = χ(B) · χ(F)`. -/
theorem eulerChar_eq_mul_of_exists_trivialization [FiniteCWType F] [FiniteCWType E] :
    eulerChar E = eulerChar B * eulerChar F := by
  rw [eulerChar_eq_finsum_finrank_singularHomology E (ULift.{u} ℚ),
    finsum_finrank_singularHomology_of_exists_trivialization h (ULift.{u} ℚ)]

end LocallyTrivial

section FiberBundle

/-- For a fibre bundle with base `B` and model fibre `F` of finite CW type, the singular homology of
the total space vanishes in all large degrees over any ring `R`. -/
theorem eventually_isZero_singularHomology_fiberBundle (R : Type u) [Ring R]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj
        (TopCat.of (TotalSpace F E))) :=
  eventually_isZero_singularHomology_of_exists_trivialization
    (FiberBundle.exists_trivialization_mem_baseSet F E) R

/-- Over a Noetherian ring `R`, for a fibre bundle with base `B` and model fibre `F` of finite CW
type, the singular homology of the total space is finitely generated in every degree `n`. -/
theorem finite_singularHomology_fiberBundle (R : Type u) [Ring R] [IsNoetherianRing R]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj
        (TopCat.of (TotalSpace F E))) :=
  finite_singularHomology_of_exists_trivialization
    (FiberBundle.exists_trivialization_mem_baseSet F E) R n

/-- **Multiplicativity of the Euler characteristic in a fibre bundle.** Let `E` be a fibre bundle
with model fibre `F` over a base `B`, where `B` and `F` have finite CW type (with no connectedness
or paracompactness assumption on `B`, and without assuming that `TotalSpace F E` has finite CW
type). Over any division ring `k`, the alternating sum of the singular homology dimensions of
`TotalSpace F E` equals `χ(B) · χ(F)`. -/
theorem finsum_finrank_singularHomology_fiberBundle (k : Type u) [DivisionRing k]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj
        (ModuleCat.of k k)).obj (TopCat.of (TotalSpace F E))) : ℤ) =
      eulerChar B * eulerChar F :=
  finsum_finrank_singularHomology_of_exists_trivialization
    (FiberBundle.exists_trivialization_mem_baseSet F E) k

/-- **Multiplicativity of `eulerChar` for the total space of a fibre bundle** when `B`, `F`, and
`TotalSpace F E` all have finite CW type: `χ(TotalSpace F E) = χ(B) · χ(F)`. -/
theorem eulerChar_totalSpace {B F : Type u} [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type u) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [FiniteCWType B] [FiniteCWType F] [FiniteCWType (TotalSpace F E)] :
    eulerChar (TotalSpace F E) = eulerChar B * eulerChar F :=
  eulerChar_eq_mul_of_exists_trivialization (FiberBundle.exists_trivialization_mem_baseSet F E)

end FiberBundle

end TauCeti
