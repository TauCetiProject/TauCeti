/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.RepresentationTheory.GroupAlgebra.RelativeTrace

/-!
# Orbit sums and reduction of fixed points in group algebras

For a subgroup `H` of a group `G`, conjugation by `H` partitions `G` into orbits
(`TauCeti.conjOrbitRel H`). When `H` is finite, the **orbit sum** of an orbit `O` is the element
`∑_{g ∈ O} g` of `R[G]` (`TauCeti.conjOrbitSum`), and the orbit sums form a basis of the fixed
points `R[G]^H` of conjugation by `H` (`TauCeti.conjInvariantsBasis`): an element of `R[G]^H` has
coefficients constant on the orbits.

A ring homomorphism `π : R →+* S` (for instance the reduction `O → k` of a `p`-modular system)
induces `R[G]^H → S[G]^H` (`TauCeti.conjInvariantsMap`), which commutes with the relative traces
`Tr_Q^P` (`TauCeti.conjInvariantsMap_relTrace`), sends orbit sums to orbit sums
(`TauCeti.conjInvariantsMap_conjInvariantsBasis`), and is onto when `π` is onto
(`TauCeti.conjInvariantsMap_surjective`).

## Main definitions

* `TauCeti.conjOrbitRel H`: the orbit relation of conjugation by `H` on `G`.
* `TauCeti.conjOrbitSum R O`: the sum in `R[G]` of the elements of an orbit `O`, for finite `H`.
* `TauCeti.conjInvariantsBasis R H`: the orbit sums, as a basis of `R[G]^H`.
* `TauCeti.conjInvariantsMap π H`: the map `R[G]^H →+* S[G]^H` induced by `π : R →+* S`.

## Main results

* `TauCeti.coe_conjInvariantsBasis`: the basis vectors are the orbit sums.
* `TauCeti.conjInvariantsMap_relTrace`: reduction commutes with `Tr_Q^P`.
* `TauCeti.conjInvariantsMap_surjective`: for surjective `π`, reduction maps `R[G]^H` onto
  `S[G]^H`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Lemma 11.3.1, pp. 194–195.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {G : Type*} [Group G]

section Orbit

/-- The orbit relation of conjugation by a subgroup `H` on `G`: `a` is related to `b` when
`h a h⁻¹ = b` for some `h ∈ H`. -/
def conjOrbitRel (H : Subgroup G) : Setoid G where
  r a b := ∃ h ∈ H, h * a * h⁻¹ = b
  iseqv :=
    ⟨fun _ ↦ ⟨1, H.one_mem, by simp⟩,
      fun ⟨h, hh, e⟩ ↦ ⟨h⁻¹, H.inv_mem hh, by rw [← e]; group⟩,
      fun ⟨h, hh, e⟩ ⟨k, hk, e'⟩ ↦ ⟨k * h, H.mul_mem hk hh, by rw [← e', ← e]; group⟩⟩

theorem conjOrbitRel_iff {H : Subgroup G} {a b : G} :
    conjOrbitRel H a b ↔ ∃ h ∈ H, h * a * h⁻¹ = b :=
  Iff.rfl

/-- The orbits of conjugation by all of `G` are the conjugacy classes. -/
theorem conjOrbitRel_top_iff {a b : G} : conjOrbitRel ⊤ a b ↔ IsConj a b := by
  simp [conjOrbitRel_iff, isConj_iff]

/-- `h g h⁻¹` lies in the orbit of `g`, for `h ∈ H`. -/
@[simp]
theorem conjOrbitRel_mk_conj {H : Subgroup G} {h : G} (hh : h ∈ H) (g : G) :
    (Quotient.mk (conjOrbitRel H) (h * g * h⁻¹)) = Quotient.mk (conjOrbitRel H) g :=
  Quotient.sound ⟨h⁻¹, H.inv_mem hh, by group⟩

/-- The orbits of conjugation by a finite subgroup are finite. -/
theorem finite_setOf_mk_conjOrbitRel_eq (H : Subgroup G) [Finite H]
    (O : Quotient (conjOrbitRel H)) :
    {g : G | Quotient.mk _ g = O}.Finite := by
  refine (Set.finite_range fun h : H ↦ (h : G)⁻¹ * O.out * h).subset fun g hg ↦ ?_
  obtain ⟨h, hh, e⟩ := Quotient.exact (hg.trans O.out_eq.symm)
  exact ⟨⟨h, hh⟩, by rw [← e]; group⟩

/-- The coefficients of an element of `R[G]^H` are constant on the orbits of conjugation by `H`. -/
theorem coeff_eq_of_conjOrbitRel {R : Type*} [CommSemiring R] {H : Subgroup G}
    {x : MonoidAlgebra R G} (hx : x ∈ conjInvariants R H) {a b : G} (hab : conjOrbitRel H a b) :
    x.coeff a = x.coeff b := by
  obtain ⟨h, hh, rfl⟩ := hab
  exact (mem_conjInvariants_iff_coeff.1 hx h hh a).symm

end Orbit

section OrbitSum

variable (R : Type*) [CommSemiring R] {H : Subgroup G} [Finite H]

open Classical in
/-- The **orbit sum** `∑_{g ∈ O} g ∈ R[G]` of an orbit `O` of conjugation by a finite subgroup
`H`: its coefficient at `g` is `1` if `g ∈ O` and `0` otherwise. -/
noncomputable def conjOrbitSum (O : Quotient (conjOrbitRel H)) : MonoidAlgebra R G :=
  ofCoeff <| Finsupp.ofSupportFinite (fun g ↦ if Quotient.mk _ g = O then 1 else 0)
    ((finite_setOf_mk_conjOrbitRel_eq H O).subset fun g hg ↦ by
      by_contra h
      exact hg (ite_eq_right_iff.2 fun h' ↦ (h h').elim))

variable {R}

/-- The coefficient of the orbit sum of `O` at `g` is `1` if `g ∈ O` and `0` otherwise. -/
@[simp]
theorem coeff_conjOrbitSum (O : Quotient (conjOrbitRel H)) (g : G)
    [Decidable (Quotient.mk _ g = O)] :
    (conjOrbitSum R O).coeff g = if Quotient.mk _ g = O then 1 else 0 := by
  rw [conjOrbitSum, coeff_ofCoeff, Finsupp.ofSupportFinite_coe]
  congr

/-- The orbit sum of `O` is the sum of the elements of `O`. -/
theorem conjOrbitSum_eq_sum (O : Quotient (conjOrbitRel H)) :
    conjOrbitSum R O = ∑ g ∈ (finite_setOf_mk_conjOrbitRel_eq H O).toFinset, single g 1 := by
  classical
  ext g
  simp [coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply, eq_comm]

/-- Orbit sums are fixed by conjugation by `H`. -/
theorem conjOrbitSum_mem_conjInvariants (O : Quotient (conjOrbitRel H)) :
    conjOrbitSum R O ∈ conjInvariants R H :=
  mem_conjInvariants_iff_coeff.2 fun h hh g ↦ by
    classical
    rw [coeff_conjOrbitSum, coeff_conjOrbitSum, conjOrbitRel_mk_conj hh]

/-- The coefficient at `g` of `∑_O c_O • conjOrbitSum O` is `c_{[g]}`. -/
theorem coeff_sum_smul_conjOrbitSum (c : Quotient (conjOrbitRel H) →₀ R) (g : G) :
    (c.sum fun O r ↦ r • conjOrbitSum R O).coeff g = c (Quotient.mk _ g) := by
  classical
  rw [coeff_finsuppSum, Finsupp.sum]
  simp only [Finset.sum_apply', coeff_smul_apply, coeff_conjOrbitSum, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

variable (R H) in
/-- **The orbit sums form a basis of `R[G]^H`**, for a finite subgroup `H`: an element of
`R[G]^H` is `∑_O c_O • conjOrbitSum O`, where `c_O` is its coefficient at any element of `O`. -/
noncomputable def conjInvariantsBasis : Module.Basis (Quotient (conjOrbitRel H)) R
    (conjInvariants R H) :=
  .ofRepr
    { toFun x := Finsupp.ofSupportFinite (fun O ↦ (x : MonoidAlgebra R G).coeff O.out)
        (((x : MonoidAlgebra R G).coeff.support.finite_toSet.image (Quotient.mk _)).subset
          fun O hO ↦ ⟨O.out, by simpa using hO, O.out_eq⟩)
      invFun c := ⟨c.sum fun O r ↦ r • conjOrbitSum R O,
        Subalgebra.toSubmodule (conjInvariants R H) |>.finsuppSum_mem _ _ _
          fun O _ ↦ Submodule.smul_mem _ _ (conjOrbitSum_mem_conjInvariants O)⟩
      map_add' x y := by ext; simp [Finsupp.ofSupportFinite_coe]
      map_smul' r x := by ext; simp [Finsupp.ofSupportFinite_coe]
      left_inv x := by
        ext g
        rw [coeff_sum_smul_conjOrbitSum, Finsupp.ofSupportFinite_coe]
        exact coeff_eq_of_conjOrbitRel x.property (Quotient.mk_out g)
      right_inv c := by
        ext O
        rw [Finsupp.ofSupportFinite_coe, coeff_sum_smul_conjOrbitSum, O.out_eq] }

/-- The basis vector of `conjInvariantsBasis R H` at an orbit `O` is the orbit sum of `O`. -/
@[simp]
theorem coe_conjInvariantsBasis (O : Quotient (conjOrbitRel H)) :
    (conjInvariantsBasis R H O : MonoidAlgebra R G) = conjOrbitSum R O := by
  simp [conjInvariantsBasis]

/-- The coordinate of `x ∈ R[G]^H` at an orbit `O` is the coefficient of `x` at any `g ∈ O`. -/
@[simp]
theorem conjInvariantsBasis_repr_mk (x : conjInvariants R H) (g : G) :
    (conjInvariantsBasis R H).repr x (Quotient.mk _ g) = (x : MonoidAlgebra R G).coeff g := by
  simp only [conjInvariantsBasis, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finsupp.ofSupportFinite_coe]
  exact coeff_eq_of_conjOrbitRel x.property (Quotient.mk_out g)

end OrbitSum

section Reduction

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (π : R →+* S)

/-- Mapping coefficients along `π` commutes with conjugation. -/
theorem mapRingHom_conjRepresentation (g : G) (x : MonoidAlgebra R G) :
    mapRingHom G π (conjRepresentation R G g x) =
      conjRepresentation S G g (mapRingHom G π x) := by
  ext h
  simp [coeff_mapRingHom]

/-- Mapping coefficients along `π` preserves fixed points of conjugation. -/
theorem mapRingHom_mem_conjInvariants {H : Subgroup G} {x : MonoidAlgebra R G}
    (hx : x ∈ conjInvariants R H) : mapRingHom G π x ∈ conjInvariants S H :=
  mem_conjInvariants_iff.2 fun h hh ↦ by
    rw [← mapRingHom_conjRepresentation, mem_conjInvariants_iff.1 hx h hh]

/-- The map `R[G]^H → S[G]^H` induced by a ring homomorphism `π : R →+* S` on coefficients, for
instance the reduction `O[G]^H → k[G]^H` of a `p`-modular system. -/
noncomputable def conjInvariantsMap (H : Subgroup G) : conjInvariants R H →+* conjInvariants S H :=
  (mapRingHom G π).restrict (conjInvariants R H).toSubsemiring (conjInvariants S H).toSubsemiring
    fun _ hx ↦ mapRingHom_mem_conjInvariants π hx

/-- `conjInvariantsMap π H` maps coefficients along `π`. -/
@[simp]
theorem coe_conjInvariantsMap (H : Subgroup G) (x : conjInvariants R H) :
    (conjInvariantsMap π H x : MonoidAlgebra S G) = mapRingHom G π x :=
  (rfl)

/-- `conjInvariantsMap π H` is `π`-semilinear. -/
theorem conjInvariantsMap_smul (H : Subgroup G) (r : R) (x : conjInvariants R H) :
    conjInvariantsMap π H (r • x) = π r • conjInvariantsMap π H x := by
  ext g
  simp [coeff_mapRingHom]

/-- **Reduction commutes with relative traces**: `π(Tr_Q^P(a)) = Tr_Q^P(π(a))`. -/
theorem conjInvariantsMap_relTrace {Q P : Subgroup G} [(Q.subgroupOf P).FiniteIndex]
    (a : conjInvariants R Q) :
    conjInvariantsMap π P (relTrace R Q P a) = relTrace S Q P (conjInvariantsMap π Q a) := by
  ext1
  rw [coe_conjInvariantsMap, coe_relTrace, coe_relTrace, map_sum]
  simp [mapRingHom_conjRepresentation]

/-- Reduction sends orbit sums to orbit sums. -/
@[simp]
theorem mapRingHom_conjOrbitSum {H : Subgroup G} [Finite H] (O : Quotient (conjOrbitRel H)) :
    mapRingHom G π (conjOrbitSum R O) = conjOrbitSum S O := by
  classical
  ext g
  simp only [coeff_mapRingHom, coeff_conjOrbitSum]
  split_ifs <;> simp

/-- Reduction sends the basis vector of `R[G]^H` at an orbit `O` to that of `S[G]^H` at `O`. -/
@[simp]
theorem conjInvariantsMap_conjInvariantsBasis {H : Subgroup G} [Finite H]
    (O : Quotient (conjOrbitRel H)) :
    conjInvariantsMap π H (conjInvariantsBasis R H O) = conjInvariantsBasis S H O := by
  ext1
  simp

/-- In the orbit-sum bases, reduction applies `π` to each coordinate. -/
@[simp]
theorem conjInvariantsBasis_repr_conjInvariantsMap {H : Subgroup G} [Finite H]
    (x : conjInvariants R H) (O : Quotient (conjOrbitRel H)) :
    (conjInvariantsBasis S H).repr (conjInvariantsMap π H x) O =
      π ((conjInvariantsBasis R H).repr x O) := by
  induction O using Quotient.inductionOn with
  | h g => simp [coeff_mapRingHom]

/-- **Reduction maps `R[G]^H` onto `S[G]^H`** when `π` is surjective. -/
theorem conjInvariantsMap_surjective (hπ : Function.Surjective π) (H : Subgroup G) :
    Function.Surjective (conjInvariantsMap π H) := by
  classical
  -- lift each coefficient of `y` along a section of `π` sending `0` to `0`; the lift is constant
  -- on orbits since the coefficients of `y` are
  let σ : S → R := fun s ↦ if s = 0 then 0 else Function.surjInv hπ s
  have hσ (s : S) : π (σ s) = s := by
    by_cases hs : s = 0 <;> simp [σ, hs, Function.surjInv_eq hπ]
  intro y
  refine ⟨⟨ofCoeff ((y : MonoidAlgebra S G).coeff.mapRange σ (by simp [σ])),
    mem_conjInvariants_iff_coeff.2 fun h hh g ↦ ?_⟩, ?_⟩
  · simp [mem_conjInvariants_iff_coeff.1 y.property h hh g]
  · ext g
    simp [coeff_mapRingHom, hσ]

end Reduction

end TauCeti
