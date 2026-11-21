/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Basic
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty
import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.LinearAlgebra.Pi
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The genus drop under a constant field extension, place by place

Let `F / k` be an algebraic function field with exact constant field `k`, let `k' / k` be a finite
extension and let `F' = F · k'` be the compositum, with `[F' : F] = [k' : k]`, so that `F` and
`k'` are linearly disjoint over `k` and `F' = F ⊗_k k'`. Over an imperfect field `k`, the full
constant field `k''` of `F'` can grow strictly beyond `k'` and the genus can drop
(`TauCeti.genus_le_genus_of_constantCompositum_eq_top`, `TauCeti.GenusDrop.genus_lt_genus`). This
file locates both effects at finitely many places of `F`.

For a place `P` of `F / k`, the ring `𝒪_P ⊗_k k'` is the `k'`-span `𝒪_P · k'` of the valuation ring
inside `F'` (`TauCeti.Place.constantSpanIntegers`). It is contained in the integral closure
`𝒪'_P` of `𝒪_P` in `F'` (`TauCeti.Place.integralClosureSubmodule`), the functions regular at all
places of `F'` over `P`. Geometrically, `𝒪_P ⊗_k k'` is the semilocal ring of the base-changed
curve along the fiber over `P`, which may consist of several points, and `𝒪'_P` is its
normalization. Their quotient has finite `k'`-dimension, the **singularity degree**

`δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P ⊗_k k')`

(`TauCeti.Place.singularityDegree`), which vanishes at all but finitely many places without any
exactness assumption on `k'` in `F'`. For any algebraic extension `k'' / k'` inside `F'` that is
exact in `F'` (in particular `k'' = algebraicClosure k' F'`), Schröer's genus-change formula gives

`g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P`,

and when `k'` is already exact in `F'`,

`g(F / k) = g(F' / k') + ∑_P δ_P`.

At `D = 0`, the local maps embed `k'' ⧸ k'` into `⨁_P (𝒪'_P ⧸ 𝒪_P · k')`, giving the constant-growth
bound `[k'' : k'] ≤ ∑_P δ_P + 1`. In particular, if no place becomes singular (`δ_P = 0`
everywhere), then `k'` is automatically exact in `F'`; conversely, for any algebraic constant field
extension `F' = F · k'` in genus `g(F / k) ≥ 1`, if `g(F' / k'') = g(F / k)` for some algebraic
extension `k'' / k'` inside `F'` that is exact in `F'`, then `𝒪_P · k' = 𝒪'_P` at every place `P`
and `k'` is exact in `F'`.

For genus stabilization under arbitrary algebraic constant field extensions, see
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Stabilization`.

## Main definitions

The rings `𝒪_P · k'` and `𝒪'_P` come from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.IntegralBasis`.

* `TauCeti.Place.singularityQuotient`: the quotient `𝒪'_P ⧸ 𝒪_P · k'`.
* `TauCeti.Place.singularityDegree`: its `k'`-dimension `δ_P`.

## Main results

* `TauCeti.Place.finiteDimensional_singularityQuotient`: `𝒪'_P ⧸ 𝒪_P · k'` is finite-dimensional.
* `TauCeti.Place.singularityDegree_eq_zero_iff`: when `𝒪'_P ⧸ 𝒪_P · k'` is finite-dimensional,
  `δ_P = 0` exactly when `𝒪_P · k'` is integrally closed in `F'`.
* `TauCeti.finite_setOf_singularityDegree_ne_zero`: `δ_P = 0` at all but finitely many places.
* `TauCeti.genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree` and
  `TauCeti.genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree_add_one`:
  **`g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P`.**
* `TauCeti.genus_eq_genus_add_finsum_singularityDegree`: **`g(F / k) = g(F' / k') + ∑_P δ_P`** when
  `k'` is exact in `F'`.
* `TauCeti.finrank_le_finsum_singularityDegree_add_one` and
  `TauCeti.isIntegrallyClosedIn_of_forall_constantSpanIntegers_eq`: constant growth is bounded by
  `∑_P δ_P + 1`, so `δ_P = 0` everywhere implies `IsIntegrallyClosedIn k' F'`.
* `TauCeti.forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq` and
  `TauCeti.isIntegrallyClosedIn_of_one_le_genus_of_genus_eq`: for any algebraic constant field
  extension `F' = F · k'` in genus at least `1`, having `g(F' / k'') = g(F / k)` for an algebraic
  extension `k'' / k'` inside `F'` exact in `F'` forces `𝒪_P · k' = 𝒪'_P` everywhere and exactness
  of `k'` in `F'`.
* `TauCeti.genus_eq_genus_iff_forall_constantSpanIntegers_eq`: over exact constants, the genus is
  unchanged iff `𝒪_P · k'` is integrally closed at every place.
* `TauCeti.riemannRochSpace_conorm_eq_span_of_forall_constantSpanIntegers_eq` and
  `TauCeti.Divisor.dim_conorm_of_forall_constantSpanIntegers_eq`: if `𝒪_P · k'` is integrally
  closed at every place, then `L(Con D) = L(D) · k'` and `ℓ(Con D) = ℓ(D)`.
* `TauCeti.riemannRochSpace_conorm_eq_span_of_genus_eq`, `TauCeti.Divisor.dim_conorm_of_genus_eq`,
  `TauCeti.conormClassGroup_canonicalClass_of_genus_eq` and
  `TauCeti.conormClassGroup_injective_of_genus_eq`: when the genus does not drop, the conorm
  preserves Riemann–Roch spaces and the canonical class and is injective on divisor classes.

## References

* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243, Theorem 2.1, for the genus formula with growing constants and
  δ-invariants.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.5 and III.6.
-/

public section

open Module
open scoped IntermediateField

namespace TauCeti

universe u u' v v' w

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

namespace Place

variable (k' F') (P : Place k F)

variable [Algebra.IsIntegral k k']

/-- The quotient `𝒪'_P ⧸ 𝒪_P · k'`, which measures how far `𝒪_P ⊗_k k'` is from being integrally
closed in `F'`. -/
abbrev singularityQuotient : Type v' :=
  ↥(integralClosureSubmodule k' F' P) ⧸
    (constantSpanIntegers k' F' P).submoduleOf (integralClosureSubmodule k' F' P)

/-- The **singularity degree** `δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P · k')` of `P` in `F' = F · k'`: the
total `k'`-dimensional normalization defect along the fiber over `P` of the curve of `F / k` after
extending the constants to `k'`. The fiber may consist of several points, and `δ_P` sums their
contributions. It is finite (`TauCeti.Place.finiteDimensional_singularityQuotient`). When `k'`
remains exact in `F'`, `g(F / k) = g(F' / k') + ∑_P δ_P`
(`TauCeti.genus_eq_genus_add_finsum_singularityDegree`); in the general case with constant growth,
see `TauCeti.genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree`. -/
noncomputable def singularityDegree : ℕ :=
  finrank k' (singularityQuotient k' F' P)

theorem singularityDegree_def :
    singularityDegree k' F' P = finrank k' (singularityQuotient k' F' P) :=
  (rfl)

/-- **A place has singularity degree zero exactly when `𝒪_P · k'` is integrally closed**: when
`𝒪'_P ⧸ 𝒪_P · k'` is finite-dimensional, `δ_P = 0` if and only if `𝒪_P ⊗_k k'` is the integral
closure of `𝒪_P` in `F'`. The finiteness holds at every place in the setting of the genus drop
(`TauCeti.Place.finiteDimensional_singularityQuotient`). -/
theorem singularityDegree_eq_zero_iff [FiniteDimensional k' (singularityQuotient k' F' P)] :
    singularityDegree k' F' P = 0 ↔
      constantSpanIntegers k' F' P = integralClosureSubmodule k' F' P := by
  rw [singularityDegree_def, Module.finrank_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.submoduleOf_eq_top]
  exact ⟨fun hle ↦ le_antisymm (constantSpanIntegers_le_integralClosureSubmodule k' F' P) hle,
    fun heq ↦ heq.ge⟩

end Place

/-! ### The local comparison -/

section Local

variable [FiniteDimensional k k']

variable (h : constantCompositum F k' F' = ⊤) (hn : finrank F F' = finrank k k')

variable [FiniteDimensional F F']

/-- **`L(Con D)` place by place**: if `s P` has order `D P` at each place `P` of `F`, then a
function of `F'` lies in `L(Con D)` exactly when `s P` times it is integral over `𝒪_P` for
every `P`. -/
private theorem mem_riemannRochSpace_conorm_iff_forall_smul_mem (hF' : IsFunctionField k' F')
    {D : Divisor k F} {s : Place k F → F} (hs0 : ∀ P, s P ≠ 0)
    (hs : ∀ P, P.ord (s P) = D.coeff P) {z : F'} :
    z ∈ riemannRochSpace (Divisor.conorm k' F' D) ↔
      ∀ P : Place k F, s P • z ∈ P.integralClosureSubmodule k' F' := by
  have key (P : Place k F) : s P • z ∈ P.integralClosureSubmodule k' F' ↔
      ∀ P' : Place k' F', P'.restrict k F = P →
        P'.valuation z ≤ WithZero.exp ((Divisor.conorm k' F' D).coeff P') := by
    rw [Place.mem_integralClosureSubmodule_iff_forall_restrict_eq _ _ _ hF']
    refine forall_congr' fun P' ↦ forall_congr' fun hP' ↦ ?_
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    have hs' : algebraMap F F' (s P) ≠ 0 := (map_ne_zero _).2 (hs0 P)
    rw [Algebra.smul_def, Place.mem_integers_iff_ord_nonneg, P'.ord_mul hs' hz,
      Place.ord_algebraMap_restrict k F P', P'.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp,
      Divisor.coeff_conorm, hP', hs]
    omega
  simp only [key, mem_riemannRochSpace_iff]
  exact ⟨fun hz P P' _ ↦ hz P', fun hz P' ↦ hz _ P' rfl⟩

variable (hF' : IsFunctionField k' F') {D : Divisor k F} {s : Place k F → F}
  (hs0 : ∀ P, s P ≠ 0) (hs : ∀ P, P.ord (s P) = D.coeff P)

/-- The local map `L(Con D) → 𝒪'_P ⧸ 𝒪_P · k'`, `z ↦ s P · z`, for `s P` of order `D P` at `P`. -/
private noncomputable def localMap (P : Place k F) :
    riemannRochSpace (Divisor.conorm k' F' D) →ₗ[k'] P.singularityQuotient k' F' :=
  (Submodule.mkQ _).comp <|
    ((LinearMap.mulLeft k' (algebraMap F F' (s P))).comp
      (riemannRochSpace (Divisor.conorm k' F' D)).subtype).codRestrict _ fun z ↦ by
        simpa [Algebra.smul_def] using
          (mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs).1 z.property P

private theorem localMap_apply (P : Place k F) (z : riemannRochSpace (Divisor.conorm k' F' D)) :
    localMap hF' hs0 hs P z = Submodule.Quotient.mk ⟨algebraMap F F' (s P) * z, by
      simpa [Algebra.smul_def] using
        (mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs).1 z.property P⟩ :=
  (rfl)

private theorem localMap_eq_zero_iff (P : Place k F) (z : riemannRochSpace
    (Divisor.conorm k' F' D)) :
    localMap hF' hs0 hs P z = 0 ↔ s P • (z : F') ∈ P.constantSpanIntegers k' F' := by
  rw [localMap_apply, Submodule.Quotient.mk_eq_zero]
  simp only [Algebra.smul_def]
  exact Iff.rfl

include h hn in
/-- **The local maps are jointly surjective** on any finite set of places, as soon as `A_F(D) + F`
is all of `A_F`. -/
private theorem pi_localMap_surjective
    (hD : adeleFiltration D ⊔ diagonalRepartitions k F = repartitionSpace k F)
    (S : Finset (Place k F)) :
    Function.Surjective (LinearMap.pi fun P : S ↦ localMap hF' hs0 hs (P : Place k F)) := by
  classical
  intro y
  choose y' hy' using fun P : S ↦ Submodule.Quotient.mk_surjective _ (y P)
  set c := constantBasisOfFinrankEq h hn (finBasis k k')
  -- the coordinates of the targets, with the pole allowed by `D` restored, as repartitions of `F`
  let a : Fin (finrank k k') → Place k F → F := fun j P ↦
    if hP : P ∈ S then (s P)⁻¹ * c.repr (y' ⟨P, hP⟩ : F') j else 0
  have ha (j) : a j ∈ adeleFiltration D ⊔ diagonalRepartitions k F := by
    rw [hD, mem_repartitionSpace_iff_finite]
    refine S.finite_toSet.subset fun P hP ↦ ?_
    by_contra hPS
    have hPS' : P ∉ S := by simpa using hPS
    exact hP (by simp [a, hPS'])
  choose α hα f hf hsum using fun j ↦ Submodule.mem_sup.1 (ha j)
  choose g hg using fun j ↦ mem_diagonalRepartitions_iff.1 (hf j)
  set z : F' := ∑ j, g j • c j
  have hzrepr (j) : c.repr z j = g j := by rw [Basis.repr_sum_self]
  -- at every place, `s P • z` differs from the target by an element of `𝒪_P · k'`
  have hloc (P : Place k F) : s P • z - (if hP : P ∈ S then (y' ⟨P, hP⟩ : F') else 0) ∈
      P.constantSpanIntegers k' F' := by
    rw [Place.mem_constantSpanIntegers_iff h hn (finBasis k k')]
    intro j
    have hαP : α j P + g j = a j P := by
      have := congrFun (hsum j) P
      rwa [← hg j, Pi.add_apply, Function.const_apply] at this
    have hint : s P * α j P ∈ P.integers :=
      (Place.mul_mem_integers_iff (hs0 P) (hs P)).2 ((mem_adeleFiltration_iff.1 (hα j)) P)
    have hcoord : c.repr (s P • z - (if hP : P ∈ S then (y' ⟨P, hP⟩ : F') else 0)) j =
        -(s P * α j P) := by
      rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hzrepr]
      by_cases hP : P ∈ S
      · simp only [a, hP, dite_true] at hαP
        rw [dite_eq_left hP, ← mul_inv_cancel_left₀ (hs0 P) (c.repr (y' ⟨P, hP⟩ : F') j), ← hαP]
        ring
      · simp only [a, hP, dite_false] at hαP
        rw [dite_eq_right hP, map_zero, Finsupp.zero_apply, eq_neg_of_add_eq_zero_left hαP]
        ring
    rw [hcoord]
    exact neg_mem hint
  have hzmem : z ∈ riemannRochSpace (Divisor.conorm k' F' D) := by
    rw [mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs]
    intro P
    have hle := P.constantSpanIntegers_le_integralClosureSubmodule k' F' (hloc P)
    by_cases hP : P ∈ S
    · rw [dite_eq_left hP] at hle
      simpa using add_mem hle (y' ⟨P, hP⟩).property
    · rwa [dite_eq_right hP, sub_zero] at hle
  refine ⟨⟨z, hzmem⟩, funext fun P ↦ ?_⟩
  have hP := hloc P
  rw [dite_eq_left P.property] at hP
  rw [LinearMap.pi_apply, ← hy' P]
  simp only [localMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  simpa [Submodule.submoduleOf, Algebra.smul_def] using hP

/-- The common kernel of the local maps contains `L(D) · k'`. -/
private theorem span_le_ker_pi_localMap (S : Finset (Place k F)) :
    (Submodule.span k' (algebraMap F F' '' riemannRochSpace D)).comap
        (riemannRochSpace (Divisor.conorm k' F' D)).subtype ≤
      LinearMap.ker (LinearMap.pi fun P : S ↦ localMap hF' hs0 hs (P : Place k F)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext P
  rw [LinearMap.pi_apply, Pi.zero_apply, localMap_eq_zero_iff]
  have hspan : Submodule.span k' (algebraMap F F' '' riemannRochSpace D) ≤
      (P.val.constantSpanIntegers k' F').comap (LinearMap.mulLeft k' (algebraMap F F' (s P))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, ← map_mul]
    exact Place.algebraMap_mem_constantSpanIntegers k' F'
      ((Place.mul_mem_integers_iff (hs0 P) (hs P)).2 (mem_riemannRochSpace_iff.1 hf P))
  simpa [Algebra.smul_def] using hspan hz

include h hn in
/-- If every place outside `S` is regular, the common kernel of the local maps on `S` is exactly
`L(D) · k'`. -/
private theorem ker_pi_localMap_le_span (S : Finset (Place k F))
    (hreg : ∀ P ∉ S, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F') :
    LinearMap.ker (LinearMap.pi fun P : S ↦ localMap hF' hs0 hs (P : Place k F)) ≤
      (Submodule.span k' (algebraMap F F' '' riemannRochSpace D)).comap
        (riemannRochSpace (Divisor.conorm k' F' D)).subtype := by
  intro z hz
  rw [LinearMap.mem_ker] at hz
  set c := constantBasisOfFinrankEq h hn (finBasis k k')
  -- at every place, `s P • z` lies in `𝒪_P · k'`
  have hmem (P : Place k F) : s P • (z : F') ∈ P.constantSpanIntegers k' F' := by
    by_cases hP : P ∈ S
    · rw [← localMap_eq_zero_iff hF' hs0 hs]
      simpa using congrFun hz ⟨P, hP⟩
    · rw [hreg P hP]
      exact (mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs).1 z.property P
  -- so the coordinates of `z` lie in `L(D)`
  have hcoord (j) : c.repr z j ∈ riemannRochSpace D := by
    refine mem_riemannRochSpace_iff.2 fun P ↦ (Place.mul_mem_integers_iff (hs0 P) (hs P)).1 ?_
    have := (Place.mem_constantSpanIntegers_iff h hn (finBasis k k') P).1 (hmem P) j
    rwa [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
  rw [Submodule.mem_comap, Submodule.subtype_apply, ← c.sum_repr z]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [constantBasisOfFinrankEq_apply, Algebra.smul_def, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hcoord j, rfl⟩)

end Local

/-! ### The genus drop -/

section Genus

variable [FiniteDimensional k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  (h : constantCompositum F k' F' = ⊤)

include hF hex h

/-- A divisor `E` of `F` with `A_F(E) + F = A_F` whose Riemann–Roch dimensions in `F` and, after
the conorm, in `F'` are determined via Riemann's theorem over any exact algebraic enlargement
`k'' / k'` inside `F'`. -/
private theorem exists_divisor_adeleFiltration_sup_eq_of_isAlgebraic
    (hn : finrank F F' = finrank k k') [FiniteDimensional F F']
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    ∃ E : Divisor k F, adeleFiltration E ⊔ diagonalRepartitions k F = repartitionSpace k F ∧
      (E.dim : ℤ) = Divisor.degree E + 1 - genus k F ∧
      ((Divisor.conorm k' F' E).dim : ℤ) =
        Divisor.degree E + finrank k' k'' * (1 - (genus k'' F' : ℤ)) := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
  have hF'' : IsFunctionField k'' F' := hF'.of_isAlgebraic
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus hF'' hex''
  obtain ⟨P₀⟩ := Place.nonempty hF
  obtain ⟨m, hm⟩ := Divisor.exists_le_degree_add_nsmul_ofPoint hF 0 P₀ (finrank k' k'' * c)
  obtain ⟨E, hle, hiE, hEeq⟩ :=
    exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace hF hex
      (0 + m • AlgebraicGeometry.WeilDivisor.ofPoint P₀)
  have hdeg' : Divisor.degree (Divisor.conorm k' F' E) = Divisor.degree E :=
    Divisor.degree_conorm_of_finrank_eq_finrank k' F' hF h hn E
  have hdeg'' : (finrank k' k'' : ℤ) *
      Divisor.degree (Divisor.conorm k'' F' (Divisor.conorm k' F' E)) = Divisor.degree E := by
    simpa [hdeg'] using Divisor.finrank_mul_degree_conorm k'' F' hF' (Divisor.conorm k' F' E)
  have hpos : (0 : ℤ) < finrank k' k'' := Nat.cast_pos.2 finrank_pos
  have hc_le : c ≤ Divisor.degree (Divisor.conorm k'' F' (Divisor.conorm k' F' E)) := by
    have h1 : (finrank k' k'' : ℤ) * c ≤ Divisor.degree E :=
      hm.trans (Divisor.degree_le_of_le hle)
    nlinarith
  have hdim'' := hc _ hc_le
  have hdim' : (Divisor.conorm k' F' E).dim =
      finrank k' k'' * (Divisor.conorm k'' F' (Divisor.conorm k' F' E)).dim :=
    Divisor.dim_eq_finrank_mul_dim_conorm (Divisor.conorm k' F' E)
  refine ⟨E, hEeq, ?_, ?_⟩
  · rw [Divisor.indexOfSpecialty_def] at hiE
    omega
  · have : ((Divisor.conorm k' F' E).dim : ℤ) =
        (finrank k' k'' : ℤ) *
          ((Divisor.conorm k'' F' (Divisor.conorm k' F' E)).dim : ℤ) := by
      exact_mod_cast hdim'
    nlinarith

omit hex in
/-- The `k'`-dimension of the preimage of `L(D) · k'` inside `L(Con D)` equals `D.dim`. -/
private theorem finrank_span_comap_eq_dim (hn : finrank F F' = finrank k k')
    [FiniteDimensional F F'] (D : Divisor k F) :
    finrank k' ((Submodule.span k' (algebraMap F F' '' riemannRochSpace D)).comap
      (riemannRochSpace (Divisor.conorm k' F' D)).subtype) = D.dim := by
  have hF' := hF.of_constantCompositum_eq_top h
  have hspan_le : Submodule.span k' (algebraMap F F' '' riemannRochSpace D) ≤
      riemannRochSpace (Divisor.conorm k' F' D) :=
    Submodule.span_le.2 fun _ ⟨f, hf, hfz⟩ ↦ hfz ▸ (mem_riemannRochSpace_conorm_iff hF' D f).2 hf
  rw [(Submodule.comapSubtypeEquivOfLe hspan_le).finrank_eq,
    finrank_span_image_riemannRochSpace_of_linearDisjoint hF
      (linearDisjoint_fieldRange_of_finrank_constantCompositum_eq
        (by rw [h, IntermediateField.finrank_top', hn])) D]

omit hex in
/-- When every place outside `S` is regular, the common kernel of the local maps on `S` has
`k'`-dimension `D.dim`. -/
private theorem finrank_ker_pi_localMap_eq_dim (hn : finrank F F' = finrank k k')
    [FiniteDimensional F F'] {D : Divisor k F} {s : Place k F → F} (hs0 : ∀ P, s P ≠ 0)
    (hs : ∀ P, P.ord (s P) = D.coeff P) (S : Finset (Place k F))
    (hreg : ∀ P ∉ S, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F') :
    finrank k' (LinearMap.ker (LinearMap.pi fun P : S ↦
      localMap (hF.of_constantCompositum_eq_top h) hs0 hs (P : Place k F))) = D.dim := by
  have hker := le_antisymm
    (ker_pi_localMap_le_span h hn (hF.of_constantCompositum_eq_top h) hs0 hs S hreg)
    (span_le_ker_pi_localMap (hF.of_constantCompositum_eq_top h) hs0 hs S)
  rw [hker]
  exact finrank_span_comap_eq_dim hF h hn D

/-- The core count with constant growth: on a finite set `S` of places, the local quotients are
finite-dimensional and `∑_{P ∈ S} δ_P + [k'' : k'] (g(F' / k'') - 1) ≤ g(F / k) - 1`, with
equality when every place outside `S` is regular. -/
private theorem sum_singularityDegree_le_and_eq (hn : finrank F F' = finrank k k')
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (S : Finset (Place k F)) :
    (∀ P ∈ S, FiniteDimensional k' (P.singularityQuotient k' F')) ∧
      (∑ P ∈ S, (P.singularityDegree k' F' : ℤ)) +
          finrank k' k'' * ((genus k'' F' : ℤ) - 1) ≤ (genus k F : ℤ) - 1 ∧
      ((∀ P ∉ S, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F') →
        (∑ P ∈ S, (P.singularityDegree k' F' : ℤ)) +
          finrank k' k'' * ((genus k'' F' : ℤ) - 1) = (genus k F : ℤ) - 1) := by
  classical
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' := hF.of_constantCompositum_eq_top h
  obtain ⟨E, hEeq, hdimE, hdimE'⟩ :=
    exists_divisor_adeleFiltration_sup_eq_of_isAlgebraic hF hex h hn hex''
  choose s hs0 hs using fun P : Place k F ↦ P.exists_ne_zero_ord_eq (E.coeff P)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : riemannRochSpace (Divisor.conorm k' F' E) →ₗ[k']
      ((P : S) → (P : Place k F).singularityQuotient k' F'),
      Φ = LinearMap.pi fun P : S ↦ localMap hF' hs0 hs (P : Place k F) :=
    ⟨_, rfl⟩
  have hsurj : Function.Surjective Φ := hΦ ▸ pi_localMap_surjective h hn hF' hs0 hs hEeq S
  have := finiteDimensional_riemannRochSpace hF' (Divisor.conorm k' F' E)
  have hfin (P : S) : FiniteDimensional k' ((P : Place k F).singularityQuotient k' F') :=
    LinearMap.finite_of_surjective_pi Φ hsurj P
  have hrank := LinearMap.sum_finrank_add_finrank_ker_of_surjective
    (Q := fun P : S ↦ (P : Place k F).singularityQuotient k' F') Φ hsurj
  simp only [← Place.singularityDegree_def] at hrank
  have hrank' : (∑ P ∈ S, (P.singularityDegree k' F' : ℤ)) + finrank k' (LinearMap.ker Φ) =
      finrank k' (riemannRochSpace (Divisor.conorm k' F' E)) := by
    rw [← Finset.sum_coe_sort S fun P ↦ (P.singularityDegree k' F' : ℤ)]
    exact_mod_cast hrank
  have hWker : E.dim ≤ finrank k' (LinearMap.ker Φ) := by
    rw [← finrank_span_comap_eq_dim hF h hn E]
    exact Submodule.finrank_mono (hΦ ▸ span_le_ker_pi_localMap hF' hs0 hs S)
  rw [Divisor.dim_def] at hdimE'
  refine ⟨fun P hP ↦ hfin ⟨P, hP⟩, by linarith, fun hreg ↦ ?_⟩
  have hker_dim : finrank k' (LinearMap.ker Φ) = E.dim :=
    hΦ ▸ finrank_ker_pi_localMap_eq_dim hF h hn hs0 hs S hreg
  rw [hker_dim] at hrank'
  linarith

/-- **The singularity quotient is finite-dimensional**: `𝒪'_P ⧸ 𝒪_P · k'` has finite
`k'`-dimension at every place `P` of `F / k`, without assuming `k'` is exact in `F'`. -/
theorem Place.finiteDimensional_singularityQuotient (hn : finrank F F' = finrank k k')
    (P : Place k F) :
    FiniteDimensional k' (P.singularityQuotient k' F') :=
  (sum_singularityDegree_le_and_eq hF hex h hn
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F')) {P}).1 P
    (Finset.mem_singleton_self P)

/-- **The singularity degree vanishes at almost every place**: only finitely many places `P` of
`F / k` have `𝒪_P ⊗_k k'` not integrally closed in `F'`, without assuming `k'` is exact in `F'`. -/
theorem finite_setOf_singularityDegree_ne_zero (hn : finrank F F' = finrank k k') :
    {P : Place k F | P.singularityDegree k' F' ≠ 0}.Finite := by
  have hF' := hF.of_constantCompositum_eq_top h
  have := hF'.finiteDimensional_algebraicClosure
  by_contra hinf
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (genus k F + finrank k' (algebraicClosure k' F'))
  have hle := (sum_singularityDegree_le_and_eq hF hex h hn
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F')) S).2.1
  have hsum : (S.card : ℤ) ≤ ∑ P ∈ S, (P.singularityDegree k' F' : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun P hP ↦ ?_
    exact_mod_cast Nat.pos_of_ne_zero (hS hP)
  rw [hcard] at hsum
  push_cast at hsum
  have hnonneg : (0 : ℤ) ≤ finrank k' (algebraicClosure k' F') *
      (genus (algebraicClosure k' F') F' : ℤ) := by positivity
  linarith

/-- **Schröer's genus-change formula** (Schröer 2009, Theorem 2.1): if `k` is the exact constant
field of `F`, `[F' : F] = [k' : k]` for `F' = F · k'`, and `k'' / k'` is any algebraic extension
inside `F'` that is exact in `F'`, then

`g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P`. -/
theorem genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree
    (hn : finrank F F' = finrank k k') {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F']
    [IsScalarTower k' k'' F'] [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    (genus k F : ℤ) - 1 = finrank k' k'' * ((genus k'' F' : ℤ) - 1) +
      ∑ᶠ P : Place k F, (P.singularityDegree k' F' : ℤ) := by
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have hreg (P : Place k F) (hP : P ∉ hfin.toFinset) :
      P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
    have := P.finiteDimensional_singularityQuotient hF hex h hn
    rw [← P.singularityDegree_eq_zero_iff k' F']
    simpa using hP
  have heq := (sum_singularityDegree_le_and_eq hF hex h hn hex'' hfin.toFinset).2.2 hreg
  have hsupp : (Function.support fun P : Place k F ↦ (P.singularityDegree k' F' : ℤ)) ⊆
      hfin.toFinset := by
    intro P hP
    simpa [Function.mem_support] using hP
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  linarith

/-- **Schröer's genus-change formula in `ℕ`**: subtraction-free form of
`TauCeti.genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree`, stating
`g(F / k) + [k'' : k'] = [k'' : k'] * g(F' / k'') + ∑_P δ_P + 1`. -/
theorem genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree_add_one
    (hn : finrank F F' = finrank k k') {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F']
    [IsScalarTower k' k'' F'] [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k F + finrank k' k'' =
      finrank k' k'' * genus k'' F' + ∑ᶠ P : Place k F, P.singularityDegree k' F' + 1 := by
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have heq := genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree
    hF hex h hn hex''
  have hsupp₁ : (Function.support fun P : Place k F ↦ P.singularityDegree k' F') ⊆
      hfin.toFinset := by simp [Function.support]
  have hsupp₂ : (Function.support fun P : Place k F ↦ (P.singularityDegree k' F' : ℤ)) ⊆
      hfin.toFinset := by
    intro P hP
    simpa [Function.mem_support] using hP
  rw [finsum_eq_sum_of_support_subset _ hsupp₁]
  rw [finsum_eq_sum_of_support_subset _ hsupp₂] at heq
  exact_mod_cast (by linarith : (genus k F : ℤ) + finrank k' k'' =
    finrank k' k'' * genus k'' F' +
      ∑ P ∈ hfin.toFinset, (P.singularityDegree k' F' : ℤ) + 1)

/-- **Schröer's genus-change formula for `algebraicClosure k' F'`**: specialization of
`TauCeti.genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree` to the full
constant field of `F'`. -/
theorem genus_sub_one_eq_finrank_algebraicClosure_mul_genus_sub_one_add_finsum_singularityDegree
    (hn : finrank F F' = finrank k k') :
    (genus k F : ℤ) - 1 =
      finrank k' (algebraicClosure k' F') * ((genus (algebraicClosure k' F') F' : ℤ) - 1) +
        ∑ᶠ P : Place k F, (P.singularityDegree k' F' : ℤ) :=
  genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree hF hex h hn
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))

/-- **Constant-growth bound**: if `k` is the exact constant field of `F`, `[F' : F] = [k' : k]` for
a finite constant field extension `F' = F · k'`, and `k'' / k'` is any algebraic extension inside
`F'` (with no exactness hypothesis on `k''`), then `[k'' : k'] ≤ ∑_P δ_P + 1`. -/
theorem finrank_le_finsum_singularityDegree_add_one (hn : finrank F F' = finrank k k')
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] :
    finrank k' k'' ≤ ∑ᶠ P : Place k F, P.singularityDegree k' F' + 1 := by
  classical
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' := hF.of_constantCompositum_eq_top h
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  let S := hfin.toFinset
  have hreg (P : Place k F) (hP : P ∉ S) :
      P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
    have := P.finiteDimensional_singularityQuotient hF hex h hn
    rw [← P.singularityDegree_eq_zero_iff k' F']
    simpa [S] using hP
  have hs0 : ∀ _ : Place k F, (1 : F) ≠ 0 := fun _ ↦ one_ne_zero
  have hs : ∀ P : Place k F, P.ord (1 : F) = (0 : Divisor k F).coeff P := fun P ↦ P.ord_one
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : riemannRochSpace (Divisor.conorm k' F' (0 : Divisor k F)) →ₗ[k']
      ((P : S) → (P : Place k F).singularityQuotient k' F'),
      Φ = LinearMap.pi fun P : S ↦ localMap hF' hs0 hs (P : Place k F) :=
    ⟨_, rfl⟩
  have := finiteDimensional_riemannRochSpace hF' (Divisor.conorm k' F' (0 : Divisor k F))
  have (P : S) := (P : Place k F).finiteDimensional_singularityQuotient hF hex h hn
  have hrn := LinearMap.finrank_le_sum_finrank_add_finrank_ker
    (Q := fun P : S ↦ (P : Place k F).singularityQuotient k' F') Φ
  simp only [← Place.singularityDegree_def] at hrn
  rw [Finset.sum_coe_sort S fun P ↦ P.singularityDegree k' F'] at hrn
  have hker_dim : finrank k' (LinearMap.ker Φ) = 1 := by
    rw [hΦ, finrank_ker_pi_localMap_eq_dim hF h hn hs0 hs S hreg,
      Divisor.dim_zero_of_isIntegrallyClosedIn hF hex]
  have hdom_dim :
      finrank k' (riemannRochSpace (Divisor.conorm k' F' (0 : Divisor k F))) =
        finrank k' (algebraicClosure k' F') := by
    rw [← Divisor.dim_def, map_zero, Divisor.dim_zero hF']
  have := hF'.finiteDimensional_algebraicClosure
  let f : k'' →ₐ[k'] algebraicClosure k' F' :=
    { toFun := fun c ↦ ⟨algebraMap k'' F' c, mem_algebraicClosure_iff'.2
        ((Algebra.IsIntegral.isIntegral c).map (IsScalarTower.toAlgHom k' k'' F'))⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b ↦ Subtype.ext (map_add _ _ _)
      commutes' := fun r ↦ Subtype.ext (IsScalarTower.algebraMap_apply k' k'' F' r).symm }
  have hk''_le : finrank k' k'' ≤ finrank k' (algebraicClosure k' F') :=
    LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.injective
  rw [finsum_eq_sum_of_support_subset _ (s := S) (by simp [S, Function.support])]
  omega

/-- **Local normality everywhere forces exactness of `k'` in `F'`**: if `k` is the exact constant
field of `F`, `[F' : F] = [k' : k]` for a finite constant field extension `F' = F · k'`, and
`𝒪_P ⊗_k k'` is integrally closed in `F'` at every place `P` of `F / k`, then `k'` is the exact
constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_forall_constantSpanIntegers_eq (hn : finrank F F' = finrank k k')
    (hreg : ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F') :
    IsIntegrallyClosedIn k' F' := by
  have hF' := hF.of_constantCompositum_eq_top h
  have := hF'.finiteDimensional_algebraicClosure
  have hle := finrank_le_finsum_singularityDegree_add_one hF hex h hn
    (k'' := algebraicClosure k' F')
  have h0 (P : Place k F) : P.singularityDegree k' F' = 0 := by
    have := P.finiteDimensional_singularityQuotient hF hex h hn
    exact (P.singularityDegree_eq_zero_iff k' F').2 (hreg P)
  simp only [h0, finsum_zero, zero_add] at hle
  have hpos : 0 < finrank k' (algebraicClosure k' F') := finrank_pos
  exact isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.2 (by omega)

/-- Finite-step helper: under `[F' : F] = [k' : k]`, `1 ≤ g(F / k)`, and `g(F' / k'') = g(F / k)`
for an exact algebraic extension `k'' / k'`, every place `P` has `𝒪_P · k' = 𝒪'_P`. -/
private theorem forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq_of_finrank_eq
    (hn : finrank F F' = finrank k k') (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
  have hF' := hF.of_constantCompositum_eq_top h
  have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have heq := genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree_add_one
    hF hex h hn hex''
  have hle := finrank_le_finsum_singularityDegree_add_one hF hex h hn (k'' := k'')
  have hm : 1 ≤ finrank k' k'' := finrank_pos
  rw [hg] at heq
  have hsum0 : ∑ᶠ P : Place k F, P.singularityDegree k' F' = 0 := by nlinarith
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [Function.support]),
    Finset.sum_eq_zero_iff] at hsum0
  intro P
  have := P.finiteDimensional_singularityQuotient hF hex h hn
  rw [← P.singularityDegree_eq_zero_iff k' F']
  by_cases hP : P ∈ hfin.toFinset
  · exact hsum0 P hP
  · simpa using hP

/-- Finite-step helper: under `[F' : F] = [k' : k]`, `1 ≤ g(F / k)`, and `g(F' / k'') = g(F / k)`
for an exact algebraic extension `k'' / k'`, `k'` is exact in `F'`. -/
private theorem isIntegrallyClosedIn_of_one_le_genus_of_genus_eq_of_finrank_eq
    (hn : finrank F F' = finrank k k') (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    IsIntegrallyClosedIn k' F' :=
  isIntegrallyClosedIn_of_forall_constantSpanIntegers_eq hF hex h hn
    (forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq_of_finrank_eq
      hF hex h hn hg1 hex'' hg)

/-- **The genus drop is the sum of the singularity degrees**: if `k` is the exact constant field of
`F`, `k'` the exact constant field of `F' = F · k'` and `[F' : F] = [k' : k]`, then

`g(F / k) = g(F' / k') + ∑_P δ_P`,

where `δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P ⊗_k k')` vanishes at all but finitely many places. -/
theorem genus_eq_genus_add_finsum_singularityDegree (hex' : IsIntegrallyClosedIn k' F')
    (hn : finrank F F' = finrank k k') :
    genus k F = genus k' F' + ∑ᶠ P : Place k F, P.singularityDegree k' F' := by
  have heq := genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree_add_one
    hF hex h hn (k'' := k') hex'
  rw [Module.finrank_self, one_mul] at heq
  omega

/-- **The genus is unchanged exactly when no place becomes singular**: if `k` is the exact constant
field of `F`, `k'` is the exact constant field of a finite constant field extension `F' = F · k'`,
and `[F' : F] = [k' : k]`, then `g(F' / k') = g(F / k)` if and only if `𝒪_P ⊗_k k'` is integrally
closed in `F'` at every place `P` of `F / k`. -/
theorem genus_eq_genus_iff_forall_constantSpanIntegers_eq (hex' : IsIntegrallyClosedIn k' F')
    (hn : finrank F F' = finrank k k') :
    genus k' F' = genus k F ↔
      ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have (P : Place k F) := P.finiteDimensional_singularityQuotient hF hex h hn
  simp_rw [← Place.singularityDegree_eq_zero_iff k' F']
  rw [genus_eq_genus_add_finsum_singularityDegree hF hex h hex' hn, left_eq_add,
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [Function.support]),
    Finset.sum_eq_zero_iff]
  refine ⟨fun h0 P ↦ ?_, fun h0 P _ ↦ h0 P⟩
  by_cases hP : P ∈ hfin.toFinset
  · exact h0 P hP
  · simpa using hP

end Genus

section GenusAlgebraic

/-- Cutting out the exact constant field `M₁ = (E · M) ∩ k''` inside `k''` over any intermediate
field `M` of an algebraic constant extension `k' / K`: when `g(F' / k'') = g(E / K)`, both
`g(E · M / M₁)` and `g(E · M / M)` are sandwiched equal to `g(E / K)`. -/
private theorem exists_intermediate_exact_genus_eq {K E : Type*} {k'' : Type w} [Field K] [Field E]
    [Field k''] [Algebra K k'] [Algebra K E] [Algebra K F'] [Algebra E F']
    [IsScalarTower K k' F'] [IsScalarTower K E F'] [Algebra.IsAlgebraic K k']
    [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F'] [Algebra.IsAlgebraic k' k'']
    (hE : IsFunctionField K E) (h : constantCompositum E k' F' = ⊤)
    (hex'' : IsIntegrallyClosedIn k'' F') (hg : genus k'' F' = genus K E)
    (M : IntermediateField K k') :
    let EM := constantCompositum E M F'
    letI := constantCompositumAlgebra E M F'
    ∃ (M₁ : Type w) (_ : Field M₁) (_ : Algebra M M₁) (_ : Algebra M₁ EM)
      (_ : IsScalarTower M M₁ EM) (_ : Algebra.IsAlgebraic M M₁),
      IsIntegrallyClosedIn M₁ EM ∧ genus M₁ EM = genus K E ∧ genus M EM = genus K E := by
  let EM := constantCompositum E M F'
  let := constantCompositumAlgebra E M F'
  have := isScalarTower_constantCompositum E M F'
  have := isScalarTower_base_constantCompositum K E M F'
  have hEM : constantCompositum E M EM = ⊤ := (constantCompositum_eq_top_iff E M F' EM).2 rfl
  have hFEM : IsFunctionField M EM := hE.of_constantCompositum_eq_top hEM
  let _ : Algebra K k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap K k'))
  have : IsScalarTower K k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply K k' F']
  have : Algebra.IsAlgebraic K k'' := Algebra.IsAlgebraic.trans K k' k''
  let M₁ : IntermediateField K k'' := (EM.restrictScalars K).comap (IsScalarTower.toAlgHom K k'' F')
  have hmemM₁ (c : k'') : c ∈ M₁ ↔ algebraMap k'' F' c ∈ EM := Iff.rfl
  have hM_mem (m : M) : (algebraMap k' k'').comp (algebraMap M k') m ∈ M₁ := by
    rw [hmemM₁, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k' k'' F',
      IntermediateField.algebraMap_apply]
    exact algebraMap_mem_constantCompositum E M F' m
  let _ : Algebra M M₁ :=
    (((algebraMap k' k'').comp (algebraMap M k')).codRestrict M₁ hM_mem).toAlgebra
  have hmEM (c : M₁) : algebraMap M₁ F' c ∈ EM := by
    rw [IsScalarTower.algebraMap_apply M₁ k'' F', IntermediateField.algebraMap_apply]
    exact c.property
  let _ : Algebra M₁ EM := ((algebraMap M₁ F').codRestrict EM hmEM).toAlgebra
  have : IsScalarTower M₁ EM F' := .of_algebraMap_eq fun c ↦ by
    rw [IntermediateField.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]
  have hstM : IsScalarTower M M₁ EM := .of_algebraMap_eq fun m ↦ (algebraMap EM F').injective <| by
    rw [← IsScalarTower.algebraMap_apply M EM F', ← IsScalarTower.algebraMap_apply M₁ EM F',
      IsScalarTower.algebraMap_apply M₁ k'' F', IntermediateField.algebraMap_apply,
      RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply M k' F']
  have : IsScalarTower K M M₁ := .of_algebraMap_eq fun c ↦ Subtype.ext <| by
    simp only [IntermediateField.coe_algebraMap_apply, RingHom.algebraMap_toAlgebra,
      RingHom.codRestrict_apply, RingHom.comp_apply, IntermediateField.algebraMap_apply]
  have : Algebra.IsAlgebraic K M₁ := Algebra.IsAlgebraic.tower_bot K M₁ k''
  have halgM₁ : Algebra.IsAlgebraic M M₁ := .tower_top (K := K) M
  have : Algebra.IsAlgebraic M₁ k'' := .tower_top (K := K) M₁
  have hexM₁ : IsIntegrallyClosedIn M₁ EM :=
    isIntegrallyClosedIn_iff.2 ⟨(algebraMap M₁ EM).injective, fun {y} hy ↦ by
      have hy'' : IsIntegral k'' (y : F') := (hy.map (IsScalarTower.toAlgHom M₁ EM F')).tower_top
      obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hy''
      refine ⟨⟨c, (hmemM₁ c).2 (hc.symm ▸ y.property)⟩, Subtype.ext ?_⟩
      rw [RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply,
        IsScalarTower.algebraMap_apply M₁ k'' F', IntermediateField.algebraMap_apply]
      exact hc⟩
  have hEMk'' : constantCompositum EM k'' F' = ⊤ := by
    rw [eq_top_iff, ← constantCompositum_eq_top_of_eq_top E k' F' EM h]
    refine (constantCompositum_le_iff EM k' F').2 fun c ↦ ?_
    rw [IsScalarTower.algebraMap_apply k' k'' F']
    exact algebraMap_mem_constantCompositum EM k'' F' (algebraMap k' k'' c)
  have hEM_self : constantCompositum EM M₁ EM = ⊤ :=
    eq_top_iff.2 fun x _ ↦ IntermediateField.algebraMap_mem _ x
  have hg1 : genus k'' F' ≤ genus M₁ EM :=
    genus_le_genus_of_constantCompositum_eq_top hFEM.of_isAlgebraic hEMk''
  have hg2 : genus M₁ EM ≤ genus M EM := genus_le_genus_of_constantCompositum_eq_top hFEM hEM_self
  have hg3 : genus M EM ≤ genus K E := genus_le_genus_of_constantCompositum_eq_top hE hEM
  have hgM₁ : genus M₁ EM = genus K E := by omega
  have hgM : genus M EM = genus K E := by omega
  exact ⟨M₁, inferInstance, inferInstance, inferInstance, hstM, halgM₁, hexM₁, hgM₁, hgM⟩

/-- Strong induction on `[k' : K]` along simple steps `L = K⟮α⟯`: when `1 ≤ g(E / K)` and
`g(F' / k'') = g(E / K)` for an exact algebraic extension `k'' / k'`, `k'` is exact in `F'` and
`[F' : E] = [k' : K]`. -/
private theorem finite_exact_and_finrank_eq_of_one_le_genus_aux {k'' : Type*} [Field k'']
    [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F'] [Algebra.IsAlgebraic k' k'']
    (hex'' : IsIntegrallyClosedIn k'' F') (n : ℕ) :
    ∀ (K : Type u') (E : Type v') [Field K] [Field E] [Algebra K k'] [Algebra K E]
      [Algebra K F'] [Algebra E F'] [IsScalarTower K k' F'] [IsScalarTower K E F']
      [FiniteDimensional K k'], finrank K k' = n → IsFunctionField K E →
      IsIntegrallyClosedIn K E → 1 ≤ genus K E → constantCompositum E k' F' = ⊤ →
      genus k'' F' = genus K E → IsIntegrallyClosedIn k' F' ∧ finrank E F' = finrank K k' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K E _ _ _ _ _ _ _ _ _ hn hE hexK hg1 h hg
  by_cases hsurj : Function.Surjective (algebraMap K k')
  · have : Algebra.IsSeparable K k' := AlgEquiv.Algebra.isSeparable
      (AlgEquiv.ofBijective (Algebra.ofId K k') ⟨(algebraMap K k').injective, hsurj⟩)
    refine ⟨hexK.of_constantCompositum_eq_top h, ?_⟩
    rw [← IntermediateField.finrank_top' (F := E) (E := F'), ← h]
    exact finrank_constantCompositum_eq_finrank_of_isSeparable E k' F' hexK
  simp only [Function.Surjective, not_forall] at hsurj
  obtain ⟨α, hα⟩ := hsurj
  let L : IntermediateField K k' := K⟮α⟯
  have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral α)
  have : FiniteDimensional L k' := FiniteDimensional.right K L k'
  have hKL_ne1 : finrank K L ≠ 1 := fun h1 ↦ by
    have hmem : α ∈ (⊥ : IntermediateField K k') :=
      (IntermediateField.finrank_eq_one_iff.1 h1).le (IntermediateField.mem_adjoin_simple_self K α)
    exact hα (IntermediateField.mem_bot.1 hmem)
  have hlt : finrank L k' < n := by
    have hmul := finrank_mul_finrank K L k'
    have : 0 < finrank K L := finrank_pos
    have : 0 < finrank L k' := finrank_pos
    have : 2 ≤ finrank K L := by omega
    nlinarith
  let EL := constantCompositum E L F'
  let := constantCompositumAlgebra E L F'
  have := isScalarTower_constantCompositum E L F'
  have := isScalarTower_base_constantCompositum K E L F'
  have hEL : constantCompositum E L EL = ⊤ := (constantCompositum_eq_top_iff E L F' EL).2 rfl
  have hα_top : K⟮(⟨α, IntermediateField.mem_adjoin_simple_self K α⟩ : L)⟯ = ⊤ := by
    apply IntermediateField.map_injective L.val
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    rfl
  have hEEL : finrank E EL = finrank K L := by
    rw [← IntermediateField.finrank_top' (F := E) (E := EL), ← hEL]
    exact finrank_constantCompositum_eq_finrank_of_adjoin_simple_eq_top E L EL hexK
      (Algebra.IsIntegral.isIntegral _) hα_top
  obtain ⟨L₁, _, _, _, _, _, hexL₁, hgL₁, hgL⟩ :=
    exists_intermediate_exact_genus_eq hE h hex'' hg L
  have hexL : IsIntegrallyClosedIn L EL :=
    isIntegrallyClosedIn_of_one_le_genus_of_genus_eq_of_finrank_eq hE hexK hEL hEEL hg1
      hexL₁ hgL₁
  have hFEL : IsFunctionField L EL := hE.of_constantCompositum_eq_top hEL
  have hEL_top : constantCompositum EL k' F' = ⊤ := constantCompositum_eq_top_of_eq_top E k' F' EL h
  obtain ⟨hex', hELF'⟩ := ih _ hlt L EL rfl hFEL hexL (hgL.symm ▸ hg1) hEL_top (hg.trans hgL.symm)
  have := finiteDimensional_of_constantCompositum_eq_top (k := K) hEL
  have := finiteDimensional_of_constantCompositum_eq_top (k := L) hEL_top
  refine ⟨hex', ?_⟩
  rw [← finrank_mul_finrank E EL F', hEEL, hELF', finrank_mul_finrank K L k']

/-- Universe-polymorphic finite case: for any finite constant field extension `F' = F · k'` with
`1 ≤ g(F / k)` and `g(F' / k'') = g(F / k)` for an exact algebraic extension `k'' / k'`, `k'` is
exact in `F'` and `[F' : F] = [k' : k]`. -/
private theorem finite_exact_and_finrank_eq_of_one_le_genus [FiniteDimensional k k']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    IsIntegrallyClosedIn k' F' ∧ finrank F F' = finrank k k' := by
  let L₀ : IntermediateField k k' := ⊥
  let E₀ := constantCompositum F L₀ F'
  let := constantCompositumAlgebra F L₀ F'
  have := isScalarTower_constantCompositum F L₀ F'
  have := isScalarTower_base_constantCompositum k F L₀ F'
  have hE₀ : constantCompositum F L₀ E₀ = ⊤ := (constantCompositum_eq_top_iff F L₀ F' E₀).2 rfl
  have hbot : E₀ = ⊥ := constantCompositum_bot
  let eK := (IntermediateField.botEquiv k k').symm
  let eF := (IntermediateField.botEquiv F F').symm.trans (IntermediateField.equivOfEq hbot.symm)
  have hστ (c : k) : eF.toRingEquiv (algebraMap k F c) =
      algebraMap L₀ E₀ (eK.toRingEquiv c) := by
    apply Subtype.ext
    have h1 : eF (algebraMap k F c) = algebraMap F E₀ (algebraMap k F c) := by
      simpa using eF.commutes (algebraMap k F c)
    have h2 : eK c = algebraMap k L₀ c := by simpa using eK.commutes c
    rw [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv, h1, h2,
      ← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply F E₀ F',
      ← IsScalarTower.algebraMap_apply k F F', ← IntermediateField.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply L₀ E₀ F', ← IsScalarTower.algebraMap_apply k L₀ F']
  have hex₀ : IsIntegrallyClosedIn L₀ E₀ := hex.of_ringEquiv eK.toRingEquiv eF.toRingEquiv hστ
  have hg₀ : genus L₀ E₀ = genus k F := genus_eq_of_ringEquiv eK.toRingEquiv eF.toRingEquiv hστ
  have : FiniteDimensional L₀ k' := FiniteDimensional.right k L₀ k'
  obtain ⟨hex', hdeg⟩ := finite_exact_and_finrank_eq_of_one_le_genus_aux hex'' _ L₀ E₀ rfl
    (hF.of_constantCompositum_eq_top hE₀) hex₀ (hg₀.symm ▸ hg1)
    (constantCompositum_eq_top_of_eq_top F k' F' E₀ h) (hg.trans hg₀.symm)
  have hE₀_fin : finrank F E₀ = 1 := by rw [hbot]; exact IntermediateField.finrank_bot
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) hE₀
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : FiniteDimensional E₀ F' := FiniteDimensional.right F E₀ F'
  refine ⟨hex', ?_⟩
  rw [← finrank_mul_finrank F E₀ F', hE₀_fin, one_mul, hdeg, IntermediateField.finrank_bot']

/-- **In genus at least `1`, preserving the genus forces every place to stay regular**: if `k` is
the exact constant field of `F`, `F' = F · k'` is an algebraic constant field extension (finite or
infinite), `1 ≤ g(F / k)`, and `g(F' / k'') = g(F / k)` for some algebraic extension `k'' / k'`
inside `F'` that is exact in `F'`, then `𝒪_P · k'` is integrally closed in `F'` at every place
`P` of `F / k`. -/
theorem forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
  intro P
  refine le_antisymm (P.constantSpanIntegers_le_integralClosureSubmodule k' F') fun z hz ↦ ?_
  obtain ⟨M, _, hzM⟩ := exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
    (k := k) (F := F) (h ▸ IntermediateField.mem_top : z ∈ constantCompositum F k' F')
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have := isScalarTower_base_constantCompositum k F M F'
  have hFM : constantCompositum F M FM = ⊤ := (constantCompositum_eq_top_iff F M F' FM).2 rfl
  obtain ⟨M₁, _, _, _, _, _, hexM₁, hgM₁, hgM⟩ := exists_intermediate_exact_genus_eq hF h hex'' hg M
  obtain ⟨hexM, hnM⟩ := finite_exact_and_finrank_eq_of_one_le_genus hF hex hFM hg1 hexM₁ hgM₁
  have hregM := (genus_eq_genus_iff_forall_constantSpanIntegers_eq hF hex hFM hexM hnM).1 hgM P
  have : IsScalarTower P.integers FM F' := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      IsScalarTower.algebraMap_apply P.integers F FM, IsScalarTower.algebraMap_apply F FM F']
  have hzM_int : IsIntegral P.integers (⟨z, hzM⟩ : FM) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom P.integers FM F')
      (algebraMap FM F').injective).1 ((P.mem_integralClosureSubmodule_iff k' F').1 hz)
  have hzM_span : (⟨z, hzM⟩ : FM) ∈ P.constantSpanIntegers M FM := by
    rw [hregM, P.mem_integralClosureSubmodule_iff M FM]
    exact hzM_int
  rw [Place.constantSpanIntegers_def] at hzM_span
  refine Submodule.span_induction (p := fun (y : FM) _ ↦ (y : F') ∈ P.constantSpanIntegers k' F')
    ?_ ?_ ?_ ?_ hzM_span
  · rintro _ ⟨f, hf, rfl⟩
    rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply F FM F']
    exact Place.algebraMap_mem_constantSpanIntegers k' F' hf
  · exact zero_mem _
  · intro x y _ _ hx hy
    exact add_mem hx hy
  · intro c x _ hx
    have hsmul : ((c • x : FM) : F') = (c : k') • (x : F') := by
      rw [Algebra.smul_def, Algebra.smul_def, MulMemClass.coe_mul,
        ← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply M FM F',
        IsScalarTower.algebraMap_apply M k' F', IntermediateField.algebraMap_apply]
    rw [hsmul]
    exact Submodule.smul_mem _ _ hx

/-- **In genus at least `1`, preserving the genus forces `k'` to stay exact in `F'`**: if `k` is
the exact constant field of `F`, `F' = F · k'` is an algebraic constant field extension (finite or
infinite), `1 ≤ g(F / k)`, and `g(F' / k'') = g(F / k)` for some algebraic extension `k'' / k'`
inside `F'` that is exact in `F'`, then `k'` is exact in `F'`. -/
theorem isIntegrallyClosedIn_of_one_le_genus_of_genus_eq [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    IsIntegrallyClosedIn k' F' := by
  refine isIntegrallyClosedIn_iff.2 ⟨(algebraMap k' F').injective, fun {z} hz ↦ ?_⟩
  obtain ⟨M, _, hzM⟩ := exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
    (k := k) (F := F) (h ▸ IntermediateField.mem_top : z ∈ constantCompositum F k' F')
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have := isScalarTower_base_constantCompositum k F M F'
  have hFM : constantCompositum F M FM = ⊤ := (constantCompositum_eq_top_iff F M F' FM).2 rfl
  obtain ⟨M₁, _, _, _, _, _, hexM₁, hgM₁, -⟩ := exists_intermediate_exact_genus_eq hF h hex'' hg M
  obtain ⟨hexM, -⟩ := finite_exact_and_finrank_eq_of_one_le_genus hF hex hFM hg1 hexM₁ hgM₁
  have hz_k : IsIntegral k z := isIntegral_trans z hz
  have hz_FM : IsIntegral k (⟨z, hzM⟩ : FM) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom k FM F') (algebraMap FM F').injective).1 hz_k
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 (hz_FM.tower_top (A := M))
  refine ⟨c.val, ?_⟩
  have hval := congrArg Subtype.val hc
  rwa [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply M FM F',
    IsScalarTower.algebraMap_apply M k' F', IntermediateField.algebraMap_apply] at hval

end GenusAlgebraic

/-! ### Constant field extensions without genus drop -/

section NoDrop

variable [FiniteDimensional k k'] [FiniteDimensional F F']
  (h : constantCompositum F k' F' = ⊤) (hn : finrank F F' = finrank k k')

include h hn

/-- **`L(Con D)` when no place becomes singular**: for a finite constant field extension
`F' = F · k'` with `[F' : F] = [k' : k]`, if `𝒪_P ⊗_k k'` is integrally closed in `F'` at every
place `P` of `F / k`, then for every divisor `D` of `F / k` the Riemann–Roch space `L(Con D)` is
the `k'`-span of the image of `L(D)`. Neither separability of `k' / k` nor exactness of the
constants is assumed. -/
theorem riemannRochSpace_conorm_eq_span_of_forall_constantSpanIntegers_eq
    (hF' : IsFunctionField k' F')
    (hreg : ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F')
    (D : Divisor k F) :
    riemannRochSpace (Divisor.conorm k' F' D) =
      Submodule.span k' (algebraMap F F' '' riemannRochSpace D) := by
  choose s hs0 hs using fun P : Place k F ↦ P.exists_ne_zero_ord_eq (D.coeff P)
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.2 ?_)
  · -- the common kernel of the local maps on the empty set of places is all of `L(Con D)`
    refine ker_pi_localMap_le_span h hn hF' hs0 hs ∅ (fun P _ ↦ hreg P)
      (x := ⟨z, hz⟩) (LinearMap.mem_ker.2 ?_)
    ext ⟨P, hP⟩
    simp at hP
  · rintro _ ⟨f, hf, rfl⟩
    exact (mem_riemannRochSpace_conorm_iff hF' D f).2 hf

/-- **`ℓ(Con D) = ℓ(D)` when no place becomes singular**: for a finite constant field extension
`F' = F · k'` with `[F' : F] = [k' : k]`, if `𝒪_P ⊗_k k'` is integrally closed in `F'` at every
place `P` of `F / k`, then the conorm of every divisor `D` of `F / k` has the dimension of `D`.
Neither separability of `k' / k` nor exactness of the constants is assumed. -/
theorem Divisor.dim_conorm_of_forall_constantSpanIntegers_eq (hF : IsFunctionField k F)
    (hreg : ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F')
    (D : Divisor k F) : (Divisor.conorm k' F' D).dim = D.dim := by
  rw [Divisor.dim_def, riemannRochSpace_conorm_eq_span_of_forall_constantSpanIntegers_eq h hn
    (hF.of_constantCompositum_eq_top h) hreg D]
  exact finrank_span_image_riemannRochSpace_of_linearDisjoint hF
    (linearDisjoint_fieldRange_of_finrank_constantCompositum_eq
      (by rw [h, IntermediateField.finrank_top', hn])) D

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  (hex' : IsIntegrallyClosedIn k' F') (hg : genus k' F' = genus k F)

include hF hex hex' hg

/-- **`L(Con D)` when the genus does not drop**: if `k` is the exact constant field of `F`, `k'`
that of `F' = F · k'`, `[F' : F] = [k' : k]` and `g(F' / k') = g(F / k)`, then for every divisor
`D` of `F / k` the Riemann–Roch space `L(Con D)` is the `k'`-span of the image of `L(D)`
(Stichtenoth, Theorem 3.6.3(d), without separability of `k' / k`). -/
theorem riemannRochSpace_conorm_eq_span_of_genus_eq (D : Divisor k F) :
    riemannRochSpace (Divisor.conorm k' F' D) =
      Submodule.span k' (algebraMap F F' '' riemannRochSpace D) :=
  riemannRochSpace_conorm_eq_span_of_forall_constantSpanIntegers_eq h hn
    (hF.of_constantCompositum_eq_top h)
    ((genus_eq_genus_iff_forall_constantSpanIntegers_eq hF hex h hex' hn).1 hg) D

/-- **`ℓ(Con D) = ℓ(D)` when the genus does not drop**: under a finite constant field extension
`F' = F · k'` with exact constants on both sides, `[F' : F] = [k' : k]` and
`g(F' / k') = g(F / k)`, the conorm of every divisor `D` of `F / k` has the dimension of `D`. -/
theorem Divisor.dim_conorm_of_genus_eq (D : Divisor k F) :
    (Divisor.conorm k' F' D).dim = D.dim :=
  Divisor.dim_conorm_of_forall_constantSpanIntegers_eq h hn hF
    ((genus_eq_genus_iff_forall_constantSpanIntegers_eq hF hex h hex' hn).1 hg) D

/-- **The conorm of the canonical class is the canonical class when the genus does not drop**
(Stichtenoth, Theorem 3.6.3(e), without separability of `k' / k`): under a finite constant field
extension `F' = F · k'` with exact constants on both sides, `[F' : F] = [k' : k]` and
`g(F' / k') = g(F / k)`, the conorm on divisor classes sends the canonical class of `F / k` to the
canonical class of `F' / k'`. -/
theorem conormClassGroup_canonicalClass_of_genus_eq :
    Divisor.conormClassGroup k' F' hF (hF.of_constantCompositum_eq_top h) (canonicalClass hF hex) =
      canonicalClass (hF.of_constantCompositum_eq_top h) hex' :=
  conormClassGroup_canonicalClass_of_forall_dim_conorm_eq hF _
    (Divisor.degree_conorm_of_finrank_eq_finrank k' F' hF h hn)
    (Divisor.dim_conorm_of_genus_eq h hn hF hex hex' hg) hex hex'

/-- **The conorm is injective on divisor classes when the genus does not drop** (Stichtenoth,
Theorem 3.6.3(f), without separability of `k' / k`): under a finite constant field extension
`F' = F · k'` with exact constants on both sides, `[F' : F] = [k' : k]` and
`g(F' / k') = g(F / k)`, a divisor of `F / k` whose conorm is principal is itself principal. -/
theorem conormClassGroup_injective_of_genus_eq :
    Function.Injective (Divisor.conormClassGroup k' F' hF (hF.of_constantCompositum_eq_top h)) :=
  conormClassGroup_injective_of_forall_dim_conorm_eq hF _
    (Divisor.degree_conorm_of_finrank_eq_finrank k' F' hF h hn)
    (Divisor.dim_conorm_of_genus_eq h hn hF hex hex' hg)

end NoDrop

end TauCeti
