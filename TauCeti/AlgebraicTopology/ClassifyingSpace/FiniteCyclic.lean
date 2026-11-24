/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Cohomology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import TauCeti.RepresentationTheory.Homological.GroupHomology.FiniteCyclic

/-!
# The homology and cohomology of the classifying space of a finite cyclic group

Let `G` be a finite cyclic group of order `n`. The singular homology of Milnor's classifying space
`classifyingSpace G` with coefficients in a commutative ring `k` is

* `Hᵢ(BG; k) ≅ k / n k` for odd `i`
  (`TauCeti.classifyingSpaceSingularHomologyLinearEquivOdd`);
* `Hᵢ(BG; k) ≅ k[n]`, the elements of `k` killed by `n`, for positive even `i`
  (`TauCeti.classifyingSpaceSingularHomologyLinearEquivEven`).

With integral coefficients, `Hᵢ(BG; ℤ) ≅ ℤ/n` in odd degree
(`TauCeti.classifyingSpaceSingularHomologyIntLinearEquivOdd`), and `Hᵢ(BG; ℤ) = 0` in positive
even degree (`TauCeti.subsingleton_classifyingSpace_singularHomology_int_of_even`); in particular
`H₂(BG; ℤ) = 0`. If `n` vanishes in `k`, then `Hᵢ(BG; k)` has `finrank` one in every degree
(`TauCeti.finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero`), and it is
finite-dimensional when `k` is a field
(`TauCeti.finite_classifyingSpace_singularHomology_of_natCast_card_eq_zero`).

Dually, the singular cohomology of `BG` with coefficients in a `k`-module `M` is

* `Hⁱ(BG; M) ≅ M[n]` for odd `i` (`TauCeti.classifyingSpaceSingularCohomologyLinearEquivOdd`);
* `Hⁱ(BG; M) ≅ M / n M` for positive even `i`
  (`TauCeti.classifyingSpaceSingularCohomologyLinearEquivEven`).

When `n` kills `M`, both are `M`, and so is `H⁰(BG; M)`; hence `Hⁱ(BG; M)` has the same `finrank`
as `M` in every degree (`TauCeti.finrank_classifyingSpace_singularCohomology_of_isTorsionBy`). In
particular, if `p` divides `n`, then `Hⁱ(BG; ℤ/p)` has `finrank` one over `ℤ/p` in every degree
(`TauCeti.finrank_classifyingSpace_singularCohomology_zmod`); for a cyclic group of prime order
`p`, its mod `p` cohomology is one-dimensional in every degree. Together with the Künneth formula,
this computes the mod `p` cohomology of `B(ℤ/p × ℤ/p)` in
`TauCeti.AlgebraicTopology.ClassifyingSpace.FiniteCyclic.Prod`.

These are computed by transport, not topologically. The singular homology and cohomology of the
classifying space are the group homology and cohomology of `G` with trivial coefficients
(`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`,
`TauCeti.classifyingSpaceSingularCohomologyIsoGroupCohomology`), and those of a finite cyclic
group are computed from its two-periodic resolution
(`Rep.FiniteCyclicGroup.groupHomologyTrivialLinearEquivOdd`,
`Rep.FiniteCyclicGroup.groupHomologyTrivialLinearEquivEven`,
`Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivOdd`,
`Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivEven`). The explicit identifications, in
odd and even degree, use a generator `g` of `G`; the vanishing and rank results only use that `G`
is cyclic.

## Main definitions

* `TauCeti.classifyingSpaceSingularHomologyLinearEquivOdd`: `Hᵢ(BG; k) ≃ₗ[k] k / |G| k` for odd
  `i`.
* `TauCeti.classifyingSpaceSingularHomologyLinearEquivEven`: `Hᵢ(BG; k) ≃ₗ[k] k[|G|]` for positive
  even `i`.
* `TauCeti.classifyingSpaceSingularHomologyIntLinearEquivOdd`: `Hᵢ(BG; ℤ) ≃ₗ[ℤ] ZMod |G|` for odd
  `i`.
* `TauCeti.classifyingSpaceSingularCohomologyLinearEquivOdd`: `Hⁱ(BG; M) ≃ₗ[k] M[|G|]` for odd
  `i`.
* `TauCeti.classifyingSpaceSingularCohomologyLinearEquivEven`: `Hⁱ(BG; M) ≃ₗ[k] M / |G| M` for
  positive even `i`.

## Main results

* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_even`: if `|G|` is a nonzerodivisor of
  `k`, then `Hᵢ(BG; k) = 0` for positive even `i`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_int_of_even`: `Hᵢ(BG; ℤ) = 0` for
  positive even `i`.
* `TauCeti.finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero`: if `|G|` vanishes in
  `k`, then `Hᵢ(BG; k)` has `finrank` one for every `i`.
* `TauCeti.finite_classifyingSpace_singularHomology_of_natCast_card_eq_zero`: if `|G|` vanishes in
  the field `k`, then `Hᵢ(BG; k)` is finite-dimensional for every `i`.
* `TauCeti.finrank_classifyingSpace_singularCohomology_of_isTorsionBy`: if `|G|` kills `M`, then
  `Hⁱ(BG; M)` has the same `finrank` as `M` for every `i`.
* `TauCeti.finrank_classifyingSpace_singularCohomology_zmod`: if `p` divides `|G|`, then
  `Hⁱ(BG; ℤ/p)` has `finrank` one over `ℤ/p` for every `i`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter II, Section 4, and
  Chapter III, Section 1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.43, the homology of
  lens spaces, which are finite-dimensional approximations of `B(ℤ/n)`, and Section 4.2,
  Exercise 28, on free actions of `ℤ/p × ℤ/p` on spheres.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

section Generator

variable (k : Type u) [CommRing k] {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
  (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- **Odd-degree homology of the classifying space of a finite cyclic group.** If `G` is a finite
group generated by `g`, then `Hᵢ(BG; k) ≃ k / |G| k` for every odd `i`. -/
def classifyingSpaceSingularHomologyLinearEquivOdd (i : ℕ) (hi : Odd i) :
    ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology i ≃ₗ[k]
      QuotSMulTop (Nat.card G : k) k :=
  (classifyingSpaceSingularHomologyIsoGroupHomology k G i).toLinearEquiv.trans
    (Rep.FiniteCyclicGroup.groupHomologyTrivialLinearEquivOdd k k g hg i hi)

/-- **Even-degree homology of the classifying space of a finite cyclic group.** If `G` is a finite
group generated by `g`, then `Hᵢ(BG; k)` is the `|G|`-torsion `k[|G|]` of `k` for every positive
even `i`. -/
def classifyingSpaceSingularHomologyLinearEquivEven (i : ℕ) [NeZero i] (hi : Even i) :
    ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology i ≃ₗ[k]
      Submodule.torsionBy k k (Nat.card G : k) :=
  (classifyingSpaceSingularHomologyIsoGroupHomology k G i).toLinearEquiv.trans
    (Rep.FiniteCyclicGroup.groupHomologyTrivialLinearEquivEven k k g hg i hi)

/-- **Odd-degree integral homology of the classifying space of a finite cyclic group.** If `G` is a
finite group generated by `g`, then `Hᵢ(BG; ℤ) ≃ ZMod |G|` for every odd `i`. -/
def classifyingSpaceSingularHomologyIntLinearEquivOdd {G : Type} [CommGroup G] [Fintype G]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    ((singularChains ℤ).obj (TopCat.of (classifyingSpace G))).homology i ≃ₗ[ℤ]
      ZMod (Nat.card G) :=
  (classifyingSpaceSingularHomologyIsoGroupHomology ℤ G i).toLinearEquiv.trans
    (Rep.FiniteCyclicGroup.groupHomologyTrivialIntLinearEquivOdd g hg i hi)

end Generator

section IsCyclic

variable (k : Type u) [CommRing k] {G : Type u} [Group G] [Finite G] [IsCyclic G]

/-- **The even-degree homology of the classifying space of a finite cyclic group vanishes when
`|G|` is a nonzerodivisor of the coefficients**: then `Hᵢ(BG; k) = 0` for every positive even
`i`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_even
    (hk : IsSMulRegular k (Nat.card G : k)) (i : ℕ) [NeZero i] (hi : Even i) :
    Subsingleton (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology i) :=
  have := Rep.FiniteCyclicGroup.subsingleton_groupHomology_trivial_of_even k k hk i hi
  (classifyingSpaceSingularHomologyIsoGroupHomology k G i).toLinearEquiv.toEquiv.subsingleton

/-- **The even-degree integral homology of the classifying space of a finite cyclic group
vanishes**: `Hᵢ(BG; ℤ) = 0` for every positive even `i`. In particular `H₂(BG; ℤ) = 0`, as the
group homology `H₂(G, ℤ)` of a finite cyclic group is. -/
theorem subsingleton_classifyingSpace_singularHomology_int_of_even {G : Type} [Group G] [Finite G]
    [IsCyclic G] (i : ℕ) [NeZero i] (hi : Even i) :
    Subsingleton (((singularChains ℤ).obj (TopCat.of (classifyingSpace G))).homology i) :=
  subsingleton_classifyingSpace_singularHomology_of_even ℤ
    (IsSMulRegular.of_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')) i hi

/-- **The homology of the classifying space of a finite cyclic group with coefficients in a ring
of characteristic dividing its order.** If the order of `G` vanishes in the commutative ring `k`,
then `Hᵢ(BG; k)` has `finrank` one over `k` for every `i`. -/
theorem finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero
    (hk : (Nat.card G : k) = 0) (i : ℕ) :
    Module.finrank k (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology i) =
      1 :=
  (classifyingSpaceSingularHomologyIsoGroupHomology k G i).toLinearEquiv.finrank_eq.trans <|
    (Rep.FiniteCyclicGroup.finrank_groupHomology_trivial_of_isTorsionBy k k
      (fun x ↦ by rw [hk, zero_smul]) i).trans (CommSemiring.finrank_self k)

end IsCyclic

/-- Over a field in which the order of a finite cyclic group `G` vanishes, the homology of `BG` is
finite-dimensional in every degree. -/
theorem finite_classifyingSpace_singularHomology_of_natCast_card_eq_zero (k : Type u) [Field k]
    {G : Type u} [Group G] [Finite G] [IsCyclic G] (hk : (Nat.card G : k) = 0) (i : ℕ) :
    Module.Finite k (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology i) :=
  Module.finite_of_finrank_eq_succ
    (finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero k hk i)

/-! ### Cohomology -/

section CohomologyGenerator

variable (k : Type u) [CommRing k] {G : Type u} [CommGroup G] [Fintype G] (g : G)
  (hg : ∀ x, x ∈ Subgroup.zpowers g) (M : Type u) [AddCommGroup M] [Module k M]

/-- **Odd-degree cohomology of the classifying space of a finite cyclic group.** If `G` is a
finite group generated by `g` and `M` is a `k`-module, then `Hⁱ(BG; M)` is the `|G|`-torsion
`M[|G|]` of `M` for every odd `i`. -/
def classifyingSpaceSingularCohomologyLinearEquivOdd (i : ℕ) (hi : Odd i) :
    (TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k M) i
      ≃ₗ[k] Submodule.torsionBy k M (Nat.card G : k) :=
  (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).toLinearEquiv.trans
    (Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivOdd k g hg M i hi)

/-- The odd-degree identification is the comparison with group cohomology followed by the
odd-degree computation of the group cohomology of `G`. -/
@[simp]
theorem classifyingSpaceSingularCohomologyLinearEquivOdd_apply (i : ℕ) (hi : Odd i)
    (x : (TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k M) i) :
    classifyingSpaceSingularCohomologyLinearEquivOdd k g hg M i hi x =
      Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivOdd k g hg M i hi
        ((classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).hom x) :=
  (rfl)

/-- The inverse of the odd-degree identification sends `x ∈ M[|G|]` to the singular cohomology
class corresponding to the group cohomology class of `x`. -/
@[simp]
theorem classifyingSpaceSingularCohomologyLinearEquivOdd_symm_apply (i : ℕ) (hi : Odd i)
    (x : Submodule.torsionBy k M (Nat.card G : k)) :
    (classifyingSpaceSingularCohomologyLinearEquivOdd k g hg M i hi).symm x =
      (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).inv
        ((Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivOdd k g hg M i hi).symm x) :=
  (rfl)

/-- **Even-degree cohomology of the classifying space of a finite cyclic group.** If `G` is a
finite group generated by `g` and `M` is a `k`-module, then `Hⁱ(BG; M) ≃ M / |G| M` for every
positive even `i`. -/
def classifyingSpaceSingularCohomologyLinearEquivEven (i : ℕ) [NeZero i]
    (hi : Even i) :
    (TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k M) i
      ≃ₗ[k] QuotSMulTop (Nat.card G : k) M :=
  (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).toLinearEquiv.trans
    (Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivEven k g hg M i hi)

/-- The even-degree identification is the comparison with group cohomology followed by the
even-degree computation of the group cohomology of `G`. -/
@[simp]
theorem classifyingSpaceSingularCohomologyLinearEquivEven_apply (i : ℕ) [NeZero i] (hi : Even i)
    (x : (TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k M) i) :
    classifyingSpaceSingularCohomologyLinearEquivEven k g hg M i hi x =
      Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivEven k g hg M i hi
        ((classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).hom x) :=
  (rfl)

/-- The inverse of the even-degree identification sends a residue class in `M / |G| M` to the
singular cohomology class corresponding to its group cohomology class. -/
@[simp]
theorem classifyingSpaceSingularCohomologyLinearEquivEven_symm_apply (i : ℕ) [NeZero i]
    (hi : Even i) (x : QuotSMulTop (Nat.card G : k) M) :
    (classifyingSpaceSingularCohomologyLinearEquivEven k g hg M i hi).symm x =
      (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).inv
        ((Rep.FiniteCyclicGroup.groupCohomologyTrivialLinearEquivEven k g hg M i hi).symm x) :=
  (rfl)

end CohomologyGenerator

section CohomologyIsCyclic

variable (k : Type u) [CommRing k] {G : Type u} [Group G] [Finite G] [IsCyclic G]
  (M : Type u) [AddCommGroup M] [Module k M]

/-- **The cohomology of the classifying space of a finite cyclic group with coefficients killed
by its order.** If multiplication by `|G|` vanishes on the `k`-module `M`, then `Hⁱ(BG; M)` has
the same `finrank` over `k` as `M` in every degree `i`. -/
theorem finrank_classifyingSpace_singularCohomology_of_isTorsionBy
    (hM : Module.IsTorsionBy k M (Nat.card G : k)) (i : ℕ) :
    Module.finrank k
        ((TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of k k) k
          (ModuleCat.of k M) i) =
      Module.finrank k M :=
  (classifyingSpaceSingularCohomologyIsoGroupCohomology k G M i).toLinearEquiv.finrank_eq.trans
    (Rep.FiniteCyclicGroup.finrank_groupCohomology_trivial_of_isTorsionBy k M hM i)

/-- **The mod `p` cohomology of the classifying space of `ℤ/p`**: if `G` is a finite cyclic group
whose order is divisible by `p`, then `Hⁱ(BG; ℤ/p)` has `finrank` one over `ℤ/p` in every
degree `i`; for `p` prime, it is one-dimensional over the field `𝔽_p`. -/
theorem finrank_classifyingSpace_singularCohomology_zmod {p : ℕ} {G : Type}
    [Group G] [Finite G] [IsCyclic G] (hG : p ∣ Nat.card G) (i : ℕ) :
    Module.finrank (ZMod p)
        ((TopCat.of (classifyingSpace G)).singularCohomology (ModuleCat.of (ZMod p) (ZMod p))
          (ZMod p) (ModuleCat.of (ZMod p) (ZMod p)) i) = 1 := by
  rw [finrank_classifyingSpace_singularCohomology_of_isTorsionBy (ZMod p) (ZMod p)
    (fun x ↦ by rw [(ZMod.natCast_eq_zero_iff _ _).2 hG, zero_smul]) i,
    CommSemiring.finrank_self]

end CohomologyIsCyclic

end TauCeti
