/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Basic
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty
import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
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

At `D = 0`, the local maps embed `k'' / k'` into `⨁_P (𝒪'_P ⧸ 𝒪_P · k')`, giving the constant-growth
bound `[k'' : k'] ≤ ∑_P δ_P + 1`. In particular, if no place becomes singular (`δ_P = 0`
everywhere), then `k'` is automatically exact in `F'`; conversely, in genus `g(F / k) ≥ 1`,
preserving the normalized genus (`g(F' / k'') = g(F / k)`) forces both `[k'' : k'] = 1` and
`δ_P = 0` everywhere.

Passing to an arbitrary algebraic constant field extension `F' = F · k'` with `k'` exact in `F'`,
descending first until linear disjointness stabilizes and then until a nonspecial multiple of a pole
divisor is spanned over a finite constant subextension shows that some finite subextension `L` of
`k' / k` already has `L` exact in `F · L` and `g(F · L / L) = g(F' / k')`
(`TauCeti.exists_finiteDimensional_isIntegrallyClosedIn_genus_eq`).

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
  `TauCeti.genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree`:
  **`g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P`.**
* `TauCeti.genus_eq_genus_add_finsum_singularityDegree`: **`g(F / k) = g(F' / k') + ∑_P δ_P`** when
  `k'` is exact in `F'`.
* `TauCeti.finrank_le_finsum_singularityDegree_add_one` and
  `TauCeti.isIntegrallyClosedIn_of_forall_constantSpanIntegers_eq`: constant growth is bounded by
  `∑_P δ_P + 1`, so `δ_P = 0` everywhere implies `IsIntegrallyClosedIn k' F'`.
* `TauCeti.forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq` and
  `TauCeti.isIntegrallyClosedIn_of_one_le_genus_of_genus_eq`: in genus at least `1`, preserving the
  normalized genus forces `δ_P = 0` everywhere and exactness of `k'` in `F'`.
* `TauCeti.genus_eq_genus_iff_forall_constantSpanIntegers_eq`: over exact constants, the genus is
  unchanged iff `𝒪_P · k'` is integrally closed at every place.
* `TauCeti.riemannRochSpace_conorm_eq_span_of_forall_constantSpanIntegers_eq` and
  `TauCeti.Divisor.dim_conorm_of_forall_constantSpanIntegers_eq`: if `𝒪_P · k'` is integrally
  closed at every place, then `L(Con D) = L(D) · k'` and `ℓ(Con D) = ℓ(D)`.
* `TauCeti.riemannRochSpace_conorm_eq_span_of_genus_eq`, `TauCeti.Divisor.dim_conorm_of_genus_eq`,
  `TauCeti.conormClassGroup_canonicalClass_of_genus_eq` and
  `TauCeti.conormClassGroup_injective_of_genus_eq`: when the genus does not drop, the conorm
  preserves Riemann–Roch spaces and the canonical class and is injective on divisor classes.
* `TauCeti.exists_finiteDimensional_isIntegrallyClosedIn_genus_eq`: for any algebraic constant
  extension `F' = F · k'` with `k'` exact in `F'`, the genus already stabilizes at a finite
  constant subextension `L` exact in `F · L`.

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

universe u u' v v'

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
contributions. It is finite (`TauCeti.Place.finiteDimensional_singularityQuotient`), and the genus
drops by the sum of the singularity degrees (`TauCeti.genus_eq_genus_add_finsum_singularityDegree`).
-/
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

/-- Rank–nullity bound for a linear map into a finite dependent product. -/
private theorem finrank_le_sum_finrank_add_finrank_ker {K M ι : Type*} [DivisionRing K]
    [Fintype ι] [AddCommGroup M] [Module K M] [FiniteDimensional K M] {Q : ι → Type*}
    [∀ i, AddCommGroup (Q i)] [∀ i, Module K (Q i)] [∀ i, FiniteDimensional K (Q i)]
    (Φ : M →ₗ[K] (i : ι) → Q i) :
    finrank K M ≤ ∑ i, finrank K (Q i) + finrank K (LinearMap.ker Φ) := by
  rw [← LinearMap.finrank_range_add_finrank_ker Φ, add_le_add_iff_right]
  exact (Submodule.finrank_le (LinearMap.range Φ)).trans (Module.finrank_pi_fintype K).le

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
          (mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs).1 z.2 P

private theorem localMap_apply (P : Place k F) (z : riemannRochSpace (Divisor.conorm k' F' D)) :
    localMap hF' hs0 hs P z = Submodule.Quotient.mk ⟨algebraMap F F' (s P) * z, by
      simpa [Algebra.smul_def] using
        (mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs).1 z.2 P⟩ :=
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
      simpa using add_mem hle (y' ⟨P, hP⟩).2
    · rwa [dite_eq_right hP, sub_zero] at hle
  refine ⟨⟨z, hzmem⟩, funext fun P ↦ ?_⟩
  have hP := hloc P
  rw [dite_eq_left P.2] at hP
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
      (P.1.constantSpanIntegers k' F').comap (LinearMap.mulLeft k' (algebraMap F F' (s P))) := by
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
      exact (mem_riemannRochSpace_conorm_iff_forall_smul_mem hF' hs0 hs).1 z.2 P
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
    Divisor.dim_eq_finrank_mul_dim_conorm hF'' (Divisor.conorm k' F' E)
  refine ⟨E, hEeq, ?_, ?_⟩
  · rw [Divisor.indexOfSpecialty_def] at hiE
    omega
  · have : ((Divisor.conorm k' F' E).dim : ℤ) =
        (finrank k' k'' : ℤ) *
          ((Divisor.conorm k'' F' (Divisor.conorm k' F' E)).dim : ℤ) := by
      exact_mod_cast hdim'
    nlinarith

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
  set W := (Submodule.span k' (algebraMap F F' '' riemannRochSpace E)).comap
    (riemannRochSpace (Divisor.conorm k' F' E)).subtype
  have hspan_le : Submodule.span k' (algebraMap F F' '' riemannRochSpace E) ≤
      riemannRochSpace (Divisor.conorm k' F' E) :=
    Submodule.span_le.2 fun _ ⟨f, hf, hfz⟩ ↦ hfz ▸ (mem_riemannRochSpace_conorm_iff hF' E f).2 hf
  have hW : finrank k' W = E.dim := by
    rw [(Submodule.comapSubtypeEquivOfLe hspan_le).finrank_eq,
      finrank_span_image_riemannRochSpace_of_linearDisjoint hF
        (linearDisjoint_fieldRange_of_finrank_constantCompositum_eq
          (by rw [h, IntermediateField.finrank_top', hn])) E]
  have hWker : finrank k' W ≤ finrank k' (LinearMap.ker Φ) :=
    Submodule.finrank_mono (hΦ ▸ span_le_ker_pi_localMap hF' hs0 hs S)
  rw [Divisor.dim_def] at hdimE'
  refine ⟨fun P hP ↦ hfin ⟨P, hP⟩, by linarith, fun hreg ↦ ?_⟩
  have hker : LinearMap.ker Φ = W :=
    hΦ ▸ le_antisymm (ker_pi_localMap_le_span h hn hF' hs0 hs S hreg)
      (span_le_ker_pi_localMap hF' hs0 hs S)
  rw [hker, hW] at hrank'
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
`TauCeti.genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree`. -/
theorem genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree
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

/-- **Constant-growth bound**: at `D = 0`, the local maps embed `L(0) / k'` into the direct sum of
the singularity quotients, so `[k'' : k'] ≤ ∑_P δ_P + 1`. -/
theorem finrank_le_finsum_singularityDegree_add_one (hn : finrank F F' = finrank k k')
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
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
  have hrn := finrank_le_sum_finrank_add_finrank_ker
    (Q := fun P : S ↦ (P : Place k F).singularityQuotient k' F') Φ
  simp only [← Place.singularityDegree_def] at hrn
  rw [Finset.sum_coe_sort S fun P ↦ P.singularityDegree k' F'] at hrn
  have hker : LinearMap.ker Φ =
      (Submodule.span k' (algebraMap F F' '' riemannRochSpace (0 : Divisor k F))).comap
        (riemannRochSpace (Divisor.conorm k' F' (0 : Divisor k F))).subtype :=
    hΦ ▸ le_antisymm (ker_pi_localMap_le_span h hn hF' hs0 hs S hreg)
      (span_le_ker_pi_localMap hF' hs0 hs S)
  have hspan_le : Submodule.span k' (algebraMap F F' '' riemannRochSpace (0 : Divisor k F)) ≤
      riemannRochSpace (Divisor.conorm k' F' (0 : Divisor k F)) :=
    Submodule.span_le.2 fun _ ⟨f, hf, hfz⟩ ↦ hfz ▸ (mem_riemannRochSpace_conorm_iff hF' 0 f).2 hf
  have hker_dim : finrank k' (LinearMap.ker Φ) = 1 := by
    rw [hker, (Submodule.comapSubtypeEquivOfLe hspan_le).finrank_eq,
      finrank_span_image_riemannRochSpace_of_linearDisjoint hF
        (linearDisjoint_fieldRange_of_finrank_constantCompositum_eq
          (by rw [h, IntermediateField.finrank_top', hn])) (0 : Divisor k F),
      Divisor.dim_def, riemannRochSpace_zero_of_isIntegrallyClosedIn hF hex,
      LinearMap.finrank_range_of_inj (algebraMap k F).injective, Module.finrank_self]
  have hdom_dim :
      finrank k' (riemannRochSpace (Divisor.conorm k' F' (0 : Divisor k F))) = finrank k' k'' := by
    have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
    have hF'' : IsFunctionField k'' F' := hF'.of_isAlgebraic
    rw [← Divisor.dim_def, map_zero, Divisor.dim_eq_finrank_mul_dim_conorm hF'' (0 : Divisor k' F'),
      map_zero, Divisor.dim_def, riemannRochSpace_zero_of_isIntegrallyClosedIn hF'' hex'',
      LinearMap.finrank_range_of_inj (algebraMap k'' F').injective, Module.finrank_self, mul_one]
  rw [finsum_eq_sum_of_support_subset _ (s := S) (by simp [S, Function.support])]
  omega

/-- **Local normality everywhere forces exactness of `k'` in `F'`**: if `[F' : F] = [k' : k]` and
`𝒪_P ⊗_k k'` is integrally closed in `F'` at every place `P` of `F / k`, then `k'` is the exact
constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_forall_constantSpanIntegers_eq (hn : finrank F F' = finrank k k')
    (hreg : ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F') :
    IsIntegrallyClosedIn k' F' := by
  have hF' := hF.of_constantCompositum_eq_top h
  have := hF'.finiteDimensional_algebraicClosure
  have hle := finrank_le_finsum_singularityDegree_add_one hF hex h hn
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))
  have h0 (P : Place k F) : P.singularityDegree k' F' = 0 := by
    have := P.finiteDimensional_singularityQuotient hF hex h hn
    exact (P.singularityDegree_eq_zero_iff k' F').2 (hreg P)
  simp only [h0, finsum_zero, zero_add] at hle
  have hpos : 0 < finrank k' (algebraicClosure k' F') := finrank_pos
  exact isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.2 (by omega)

/-- **In genus at least `1`, preserving the normalized genus forces every place to stay regular**:
if `1 ≤ g(F / k)` and `g(F' / k'') = g(F / k)`, then `δ_P = 0` at every place `P` of `F / k`. -/
theorem forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq
    (hn : finrank F F' = finrank k k') (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
  have hF' := hF.of_constantCompositum_eq_top h
  have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have heq := genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree
    hF hex h hn hex''
  have hle := finrank_le_finsum_singularityDegree_add_one hF hex h hn hex''
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

/-- **In genus at least `1`, preserving the normalized genus forces `k'` to stay exact in `F'`.** -/
theorem isIntegrallyClosedIn_of_one_le_genus_of_genus_eq
    (hn : finrank F F' = finrank k k') (hg1 : 1 ≤ genus k F)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F')
    (hg : genus k'' F' = genus k F) :
    IsIntegrallyClosedIn k' F' :=
  isIntegrallyClosedIn_of_forall_constantSpanIntegers_eq hF hex h hn
    (forall_constantSpanIntegers_eq_of_one_le_genus_of_genus_eq hF hex h hn hg1 hex'' hg)

/-- **The genus drop is the sum of the singularity degrees**: if `k` is the exact constant field of
`F`, `k'` the exact constant field of `F' = F · k'` and `[F' : F] = [k' : k]`, then

`g(F / k) = g(F' / k') + ∑_P δ_P`,

where `δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P ⊗_k k')` vanishes at all but finitely many places. -/
theorem genus_eq_genus_add_finsum_singularityDegree (hex' : IsIntegrallyClosedIn k' F')
    (hn : finrank F F' = finrank k k') :
    genus k F = genus k' F' + ∑ᶠ P : Place k F, P.singularityDegree k' F' := by
  have heq := genus_add_finrank_eq_finrank_mul_genus_add_finsum_singularityDegree
    hF hex h hn (k'' := k') hex'
  rw [Module.finrank_self, one_mul] at heq
  omega

/-- **The genus is unchanged exactly when no place becomes singular**: `g(F' / k') = g(F / k)` if
and only if `𝒪_P ⊗_k k'` is integrally closed in `F'` at every place `P` of `F / k`. -/
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

/-! ### Stabilization under algebraic constant field extensions -/

section Stabilization

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Forming the constant compositum in two steps `(F · L) · N` gives the same subfield of `F'` as
forming `F · N` directly after restricting `N` to an intermediate field over `k`. -/
private theorem restrictScalars_constantCompositum_eq (L : IntermediateField k k')
    (N : IntermediateField L k') :
    letI := constantCompositumAlgebra F L F'
    (constantCompositum (constantCompositum F L F') N F').restrictScalars F =
      constantCompositum F (N.restrictScalars k) F' := by
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
  have hFL : FL ≤ constantCompositum F (N.restrictScalars k) F' :=
    constantCompositum_mono fun a ha ↦ N.algebraMap_mem ⟨a, ha⟩
  refine le_antisymm ((IntermediateField.le_extendScalars_iff hFL _).1
    ((constantCompositum_le_iff FL N F').2 fun c ↦ ?_))
    ((constantCompositum_le_iff F (N.restrictScalars k) F').2 fun c ↦ ?_)
  · rw [IntermediateField.mem_extendScalars, IsScalarTower.algebraMap_apply N k' F']
    exact algebraMap_mem_constantCompositum F (N.restrictScalars k) F' ⟨c.1, c.2⟩
  · rw [IntermediateField.mem_restrictScalars,
      IsScalarTower.algebraMap_apply (N.restrictScalars k) k' F']
    exact algebraMap_mem_constantCompositum FL N F' ⟨c.1, c.2⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Transport exactness of constants and the genus from `(N, (F · L) · N)` to
`(N.restrictScalars k, F · (N.restrictScalars k))`. -/
private theorem isIntegrallyClosedIn_and_genus_restrictScalars (L : IntermediateField k k')
    [FiniteDimensional k L] (N : IntermediateField L k') [FiniteDimensional L N] {g : ℕ}
    (hexN : letI := constantCompositumAlgebra F L F'
      letI := constantCompositumAlgebra (constantCompositum F L F') N F'
      IsIntegrallyClosedIn N (constantCompositum (constantCompositum F L F') N F'))
    (hgN : letI := constantCompositumAlgebra F L F'
      letI := constantCompositumAlgebra (constantCompositum F L F') N F'
      genus N (constantCompositum (constantCompositum F L F') N F') = g) :
    let M := N.restrictScalars k
    FiniteDimensional k M ∧
      letI := constantCompositumAlgebra F M F'
      IsIntegrallyClosedIn M (constantCompositum F M F') ∧
        genus M (constantCompositum F M F') = g := by
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
  let FLN := constantCompositum FL N F'
  let := constantCompositumAlgebra FL N F'
  have := isScalarTower_constantCompositum FL N F'
  let M := N.restrictScalars k
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have : FiniteDimensional k N := Module.Finite.trans L N
  let eN := (IntermediateField.restrictScalarsAlgEquiv k N).symm
  have hfin : FiniteDimensional k M := eN.toLinearEquiv.finiteDimensional
  let σ : N ≃+* M := eN.toRingEquiv
  let eF := (IntermediateField.restrictScalarsAlgEquiv F FLN).symm.trans
    (IntermediateField.equivOfEq (restrictScalars_constantCompositum_eq L N))
  let τ : FLN ≃+* FM := eF.toRingEquiv
  have hστ (c : N) : τ (algebraMap N FLN c) = algebraMap M FM (σ c) := by
    apply Subtype.ext
    have hτ : (eF (algebraMap N FLN c) : F') = algebraMap N FLN c := by
      simp [eF, IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply]
    have hσ : (σ c : k') = c := IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply k N c
    rw [AlgEquiv.coe_toRingEquiv, hτ, ← IntermediateField.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply N FLN F', IsScalarTower.algebraMap_apply N k' F',
      ← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply M FM F',
      IsScalarTower.algebraMap_apply M k' F', IntermediateField.algebraMap_apply,
      IntermediateField.algebraMap_apply, hσ]
  exact ⟨hfin, hexN.of_ringEquiv σ τ hστ, (genus_eq_of_ringEquiv σ τ hστ).trans hgN⟩

omit [Algebra k k'] [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- If an intermediate function field `(M, E)` contains a `k'`-basis of `L(l • (z)_∞)` in `F'`,
then `ℓ(l • (z)_∞)` over `(M, E)` is at least `ℓ(l • (z)_∞)` over `(k', F')`. -/
private theorem dim_nsmul_poles_le_of_forall_exists {M E : Type*} [Field M] [Field E]
    [Algebra M k'] [Algebra M E] [Algebra M F'] [Algebra E F'] [IsScalarTower M k' F']
    [IsScalarTower M E F'] [Algebra F E] [IsScalarTower F E F'] [Algebra.IsIntegral E F']
    (hFE : IsFunctionField M E) (hF' : IsFunctionField k' F') (z : Fˣ) (l : ℕ)
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι k' (riemannRochSpace
      (l • Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z))))
    (hb : ∀ i, ∃ y : E, algebraMap E F' y = b i) :
    (l • Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z)).dim ≤
      (l • Divisor.poles hFE (Units.map (algebraMap F E : F →* E) z)).dim := by
  classical
  cases nonempty_fintype ι
  choose y hy using hb
  have hz_eq : Units.map (algebraMap E F' : E →* F') (Units.map (algebraMap F E : F →* E) z) =
      Units.map (algebraMap F F' : F →* F') z :=
    Units.ext (IsScalarTower.algebraMap_apply F E F' z).symm
  let v : ι → riemannRochSpace (l • Divisor.poles hFE (Units.map (algebraMap F E : F →* E) z)) :=
    fun i ↦ ⟨y i, (mem_riemannRochSpace_nsmul_poles_map_iff hFE hF' l
      (Units.map (algebraMap F E : F →* E) z) (y i)).1 (by rw [hy i, hz_eq]; exact (b i).2)⟩
  have hcomp : ((IsScalarTower.toAlgHom M E F').toLinearMap.comp
      (riemannRochSpace _).subtype) ∘ v = (riemannRochSpace _).subtype ∘ b :=
    funext fun i ↦ hy i
  have hli : LinearIndependent M v :=
    .of_comp ((IsScalarTower.toAlgHom M E F').toLinearMap.comp (riemannRochSpace _).subtype) <|
      hcomp.symm ▸ ((b.linearIndependent.map' (riemannRochSpace _).subtype
        (Submodule.ker_subtype _)).restrict_scalars' M)
  have := finiteDimensional_riemannRochSpace hFE
    (l • Divisor.poles hFE (Units.map (algebraMap F E : F →* E) z))
  rw [Divisor.dim_def, Divisor.dim_def, Module.finrank_eq_card_basis b]
  exact hli.fintype_card_le_finrank

/-- Under linear disjointness, a single finite constant subextension containing a `k'`-basis of a
nonspecial multiple of a pole divisor already stabilizes the genus and keeps exact constants. -/
private theorem exists_finiteDimensional_isIntegrallyClosedIn_genus_eq_of_linearDisjoint
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') :
    ∃ M : IntermediateField k k', FiniteDimensional k M ∧
      letI := constantCompositumAlgebra F M F'
      IsIntegrallyClosedIn M (constantCompositum F M F') ∧
        genus M (constantCompositum F M F') = genus k' F' := by
  classical
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  have hx' : Transcendental k' (algebraMap F F' x) := hx.algebraMap_of_isAlgebraic
  have := hF'.finiteDimensional_adjoin hx'
  set z := Units.mk0 x hx.ne_zero
  set B' := Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z)
  have hdegB' : Divisor.degree B' = finrank k⟮x⟯ F :=
    (Divisor.degree_poles hF' _ (by simpa [z, Transcendental] using hx')).trans
      (by exact_mod_cast finrank_over_adjoin_simple_eq_of_linearDisjoint H h x)
  have hpos : 1 ≤ Divisor.degree B' := by
    rw [hdegB']
    exact_mod_cast Nat.succ_le_of_lt (finrank_pos (R := k⟮x⟯) (M := F))
  let l : ℕ := 2 * genus k F
  have := finiteDimensional_riemannRochSpace hF' (l • B')
  let b := Module.finBasis k' (riemannRochSpace (l • B'))
  obtain ⟨M, _, hbM⟩ :=
    exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum (k := k) (F := F)
      (Finset.univ.image fun i ↦ (b i : F')) fun _ _ ↦ h ▸ IntermediateField.mem_top
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have := isScalarTower_base_constantCompositum k F M F'
  have hFM : constantCompositum F M FM = ⊤ := (constantCompositum_eq_top_iff F M F' FM).2 rfl
  have hFFM : IsFunctionField M FM := hF.of_constantCompositum_eq_top hFM
  have : Algebra.IsAlgebraic M k' := .tower_top (K := k) M
  have hFM_top := constantCompositum_eq_top_of_eq_top F k' F' FM h
  have := (isAlgebraic_of_constantCompositum_eq_top (k := M) hFM_top).isIntegral
  have hexM := isIntegrallyClosedIn_constantCompositum_of_linearDisjoint H hex' M
  set BM := Divisor.poles hFFM (Units.map (algebraMap F FM : F →* FM) z)
  have hxM : Transcendental M (algebraMap F FM x) := hx.algebraMap_of_isAlgebraic
  have := hFFM.finiteDimensional_adjoin hxM
  have hHM : (IsScalarTower.toAlgHom k M FM).fieldRange.LinearDisjoint F :=
    linearDisjoint_fieldRange_of_finrank_constantCompositum_eq (by
      rw [hFM, IntermediateField.finrank_top']
      exact finrank_constantCompositum_eq_finrank_of_linearDisjoint F M F'
        (H.fieldRange_intermediateField M))
  have hdegBM : Divisor.degree BM = Divisor.degree B' := by
    rw [hdegB', Divisor.degree_poles hFFM _ (by simpa [z, Transcendental] using hxM)]
    exact_mod_cast finrank_over_adjoin_simple_eq_of_linearDisjoint hHM hFM x
  have hdim_le : (l • B').dim ≤ (l • BM).dim :=
    dim_nsmul_poles_le_of_forall_exists hFFM hF' z l b fun i ↦
      ⟨⟨b i, hbM _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩, rfl⟩
  have hgM_le : genus M FM ≤ genus k F := genus_le_genus_of_constantCompositum_eq_top hF hFM
  have hg'_le : genus k' F' ≤ genus M FM := genus_le_genus_of_constantCompositum_eq_top hFFM hFM_top
  have hl_deg : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree (l • B') := by
    rw [map_nsmul, nsmul_eq_mul]
    push_cast [l]
    nlinarith
  have hdim' := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF' hex'
    (D := l • B') (by omega)
  have hdimM := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hFFM hexM
    (D := l • BM) (by rw [map_nsmul, hdegBM, ← map_nsmul]; omega)
  rw [map_nsmul, hdegBM, ← map_nsmul] at hdimM
  exact ⟨M, ‹_›, hexM, by change genus M FM = genus k' F'; omega⟩

/-- Strong induction on `[E : K(x)]`: either `E` and `k'` are already linearly disjoint over `K`,
or a finite constant subextension strictly lowers `[E · M : M(x)]`. -/
private theorem exists_finiteDimensional_isIntegrallyClosedIn_genus_eq_aux
    (hex' : IsIntegrallyClosedIn k' F') (n : ℕ) :
    ∀ (K : Type u') (E : Type v') [Field K] [Field E] [Algebra K k'] [Algebra K E]
      [Algebra K F'] [Algebra E F'] [IsScalarTower K k' F'] [IsScalarTower K E F']
      [Algebra.IsAlgebraic K k'], IsFunctionField K E → constantCompositum E k' F' = ⊤ →
      ∀ x : E, Transcendental K x → finrank K⟮x⟯ E = n →
      ∃ M : IntermediateField K k', FiniteDimensional K M ∧
        letI := constantCompositumAlgebra E M F'
        IsIntegrallyClosedIn M (constantCompositum E M F') ∧
          genus M (constantCompositum E M F') = genus k' F' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K E _ _ _ _ _ _ _ _ _ hE h x hx hn
  by_cases hdisj : ∀ M : IntermediateField K k', FiniteDimensional K M →
      finrank E (constantCompositum E M F') = finrank K M
  · exact exists_finiteDimensional_isIntegrallyClosedIn_genus_eq_of_linearDisjoint hE h
      (linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq hdisj) hex'
  push Not at hdisj
  obtain ⟨M, _, hM⟩ := hdisj
  let EM := constantCompositum E M F'
  let := constantCompositumAlgebra E M F'
  have := isScalarTower_constantCompositum E M F'
  have := isScalarTower_base_constantCompositum K E M F'
  have hEM : constantCompositum E M EM = ⊤ := (constantCompositum_eq_top_iff E M F' EM).2 rfl
  have := finiteDimensional_of_constantCompositum_eq_top (k := K) hEM
  have hFEM : IsFunctionField M EM := hE.of_constantCompositum_eq_top hEM
  have : Algebra.IsAlgebraic M k' := .tower_top (K := K) M
  set z := Units.mk0 x hx.ne_zero
  have hx' : Transcendental M (algebraMap E EM x) := hx.algebraMap_of_isAlgebraic
  have hlt : finrank M⟮algebraMap E EM x⟯ EM < n := by
    have hconorm := Divisor.finrank_mul_degree_conorm M EM hE (Divisor.poles hE z)
    rw [Divisor.conorm_poles M EM hE hFEM, Divisor.degree_poles hFEM _
      (by simpa [z, Transcendental] using hx'), Divisor.degree_poles hE z hx] at hconorm
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, z] at hconorm
    have hconorm' : finrank K M * finrank M⟮algebraMap E EM x⟯ EM =
        finrank E EM * finrank K⟮x⟯ E := by exact_mod_cast hconorm
    have hle : finrank E EM < finrank K M :=
      lt_of_le_of_ne (finrank_le_finrank_of_constantCompositum_eq_top hEM) hM
    have := hE.finiteDimensional_adjoin hx
    have hpos : 0 < finrank K⟮x⟯ E := finrank_pos
    rw [← hn]
    by_contra! hcon
    nlinarith
  obtain ⟨N, _, hexN, hgN⟩ :=
    ih _ hlt M EM hFEM (constantCompositum_eq_top_of_eq_top E k' F' EM h) _ hx' rfl
  obtain ⟨hfin, hexM', hgM'⟩ := isIntegrallyClosedIn_and_genus_restrictScalars M N hexN hgN
  exact ⟨N.restrictScalars K, hfin, hexM', hgM'⟩

/-- **Genus stabilization under an algebraic constant field extension**: if `F' = F · k'` for an
algebraic extension `k' / k`, finite or not, and `k'` is the exact constant field of `F'`, then
some finite subextension `L` of `k' / k` already has `L` exact in `F · L` and
`g(F · L / L) = g(F' / k')`. -/
theorem exists_finiteDimensional_isIntegrallyClosedIn_genus_eq [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (hex' : IsIntegrallyClosedIn k' F') :
    ∃ L : IntermediateField k k', FiniteDimensional k L ∧
      letI := constantCompositumAlgebra F L F'
      IsIntegrallyClosedIn L (constantCompositum F L F') ∧
        genus L (constantCompositum F L F') = genus k' F' := by
  let L₀ : IntermediateField k k' := ⊥
  let E₀ := constantCompositum F L₀ F'
  let := constantCompositumAlgebra F L₀ F'
  have := isScalarTower_constantCompositum F L₀ F'
  have := isScalarTower_base_constantCompositum k F L₀ F'
  have hE₀ : constantCompositum F L₀ E₀ = ⊤ := (constantCompositum_eq_top_iff F L₀ F' E₀).2 rfl
  have hFE₀ : IsFunctionField L₀ E₀ := hF.of_constantCompositum_eq_top hE₀
  have : Algebra.IsAlgebraic L₀ k' := .tower_top (K := k) L₀
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have hx₀ : Transcendental L₀ (algebraMap F E₀ x) := hx.algebraMap_of_isAlgebraic
  obtain ⟨N, _, hexN, hgN⟩ := exists_finiteDimensional_isIntegrallyClosedIn_genus_eq_aux hex' _
    L₀ E₀ hFE₀ (constantCompositum_eq_top_of_eq_top F k' F' E₀ h) _ hx₀ rfl
  obtain ⟨hfin, hexL, hgL⟩ := isIntegrallyClosedIn_and_genus_restrictScalars L₀ N hexN hgN
  exact ⟨N.restrictScalars k, hfin, hexL, hgL⟩

end Stabilization

end TauCeti
