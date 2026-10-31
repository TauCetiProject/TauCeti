/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.RiemannRoch
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty
import TauCeti.LinearAlgebra.Pi

/-!
# The genus drop under a constant field extension, place by place

Let `F / k` be an algebraic function field with exact constant field `k`, let `k' / k` be a finite
extension and let `F' = F · k'` be the compositum, with `[F' : F] = [k' : k]`, so that `F` and
`k'` are linearly disjoint over `k` and `F' = F ⊗_k k'`. Suppose `k'` is the exact constant field
of `F'`. Over an imperfect field `k` the genus can drop
(`TauCeti.genus_le_genus_of_constantCompositum_eq_top`, `TauCeti.GenusDrop.genus_lt_genus`). This
file locates the drop at finitely many places of `F`.

For a place `P` of `F / k`, the ring `𝒪_P ⊗_k k'` is the `k'`-span `𝒪_P · k'` of the valuation ring
inside `F'` (`TauCeti.Place.constantSpanIntegers`). It is contained in the integral closure
`𝒪'_P` of `𝒪_P` in `F'` (`TauCeti.Place.integralClosureSubmodule`), the functions regular at all
places of `F'` over `P`. Geometrically, `𝒪_P ⊗_k k'` is the semilocal ring of the base-changed
curve along the fiber over `P`, which may consist of several points, and `𝒪'_P` is its
normalization. Their quotient has finite `k'`-dimension, the **singularity degree**

`δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P ⊗_k k')`

(`TauCeti.Place.singularityDegree`), which vanishes at all but finitely many places, and

`g(F / k) = g(F' / k') + ∑_P δ_P`.

So the genus drops exactly when `𝒪_P ⊗_k k'` fails to be integrally closed at some place.

The proof compares Riemann–Roch spaces. For a nonspecial divisor `E` of large degree, write
elements of `F'` in an `F`-basis of constants. Clearing the pole allowed by `E` at a place `P`
gives a `k'`-linear map from `L(Con E)` to the quotient `𝒪'_P ⧸ 𝒪_P ⊗_k k'`. On finitely many
places these maps are jointly surjective, since `A_F(E) + F` is every repartition of `F`. Their
common kernel contains `L(E) · k'`, of dimension `ℓ(E)`, with equality once every place outside
the chosen finite set is regular. Riemann's theorem in `F` and in `F'` evaluates
`ℓ(Con E) - ℓ(E) = g(F / k) - g(F' / k')`.

This is the δ-invariant formula for the genus change under inseparable base extension. Tate's
theorem refines it: for a purely inseparable `k' / k` of degree `p`, the drop is divisible by
`(p - 1) / 2`.

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
* `TauCeti.genus_eq_genus_add_finsum_singularityDegree`: **`g(F / k) = g(F' / k') + ∑_P δ_P`.**
* `TauCeti.genus_eq_genus_iff_forall_constantSpanIntegers_eq`: the genus is unchanged exactly
  when `𝒪_P · k'` is integrally closed at every place.

## References

* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243, for the genus drop as a sum of δ-invariants.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.5 and III.6.
-/

public section

open Module

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
  exact ⟨fun hz P P' hP' ↦ hz P', fun hz P' ↦ hz _ P' rfl⟩

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
  (h : constantCompositum F k' F' = ⊤) (hex' : IsIntegrallyClosedIn k' F')
  (hn : finrank F F' = finrank k k')

include hF hex h hex' hn

/-- A divisor `E` of `F` with `A_F(E) + F = A_F` whose Riemann–Roch dimensions in `F` and, after
the conorm, in `F'` are given by Riemann's theorem. -/
private theorem exists_divisor_adeleFiltration_sup_eq [FiniteDimensional F F'] :
    ∃ E : Divisor k F, adeleFiltration E ⊔ diagonalRepartitions k F = repartitionSpace k F ∧
      (E.dim : ℤ) = Divisor.degree E + 1 - genus k F ∧
      ((Divisor.conorm k' F' E).dim : ℤ) = Divisor.degree E + 1 - genus k' F' := by
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus
    (hF.of_constantCompositum_eq_top h) hex'
  obtain ⟨P₀⟩ := Place.nonempty hF
  obtain ⟨m, hm⟩ := Divisor.exists_le_degree_add_nsmul_ofPoint hF 0 P₀ c
  obtain ⟨E, hle, hiE, hEeq⟩ :=
    exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace hF hex
      (0 + m • AlgebraicGeometry.WeilDivisor.ofPoint P₀)
  have hdeg : Divisor.degree (Divisor.conorm k' F' E) = Divisor.degree E := by
    have hmul := Divisor.finrank_mul_degree_conorm k' F' hF E
    rw [hn] at hmul
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 finrank_pos.ne') hmul
  refine ⟨E, hEeq, ?_, ?_⟩
  · rw [Divisor.indexOfSpecialty_def] at hiE
    omega
  · rw [hc _ (hdeg ▸ hm.trans (Divisor.degree_le_of_le hle)), hdeg]

/-- The core count: on a finite set `S` of places, the local quotients are finite-dimensional and
`∑_{P ∈ S} δ_P + g(F' / k') ≤ g(F / k)`, with equality when every place outside `S` is regular. -/
private theorem sum_singularityDegree_add_genus_le (S : Finset (Place k F)) :
    (∀ P ∈ S, FiniteDimensional k' (P.singularityQuotient k' F')) ∧
      (∑ P ∈ S, (P.singularityDegree k' F' : ℤ)) + genus k' F' ≤ genus k F ∧
      ((∀ P ∉ S, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F') →
        (∑ P ∈ S, (P.singularityDegree k' F' : ℤ)) + genus k' F' = genus k F) := by
  classical
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' := hF.of_constantCompositum_eq_top h
  obtain ⟨E, hEeq, hdimE, hdimE'⟩ := exists_divisor_adeleFiltration_sup_eq hF hex h hex' hn
  choose s hs0 hs using fun P : Place k F ↦ P.exists_ne_zero_ord_eq (E.coeff P)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : riemannRochSpace (Divisor.conorm k' F' E) →ₗ[k']
      ((P : S) → (P : Place k F).singularityQuotient k' F'),
      Φ = LinearMap.pi fun P : S ↦ localMap hF' hs0 hs (P : Place k F) :=
    ⟨_, rfl⟩
  have hsurj : Function.Surjective Φ := by
    rw [hΦ]
    exact pi_localMap_surjective h hn hF' hs0 hs hEeq S
  have := finiteDimensional_riemannRochSpace hF' (Divisor.conorm k' F' E)
  -- rank–nullity for `Φ`, whose range is everything
  have hfin (P : S) : FiniteDimensional k' ((P : Place k F).singularityQuotient k' F') :=
    LinearMap.finite_of_surjective_pi Φ hsurj P
  have hrank := LinearMap.sum_finrank_add_finrank_ker_of_surjective
    (Q := fun P : S ↦ (P : Place k F).singularityQuotient k' F') Φ hsurj
  simp only [← Place.singularityDegree_def] at hrank
  have hrank' : (∑ P ∈ S, (P.singularityDegree k' F' : ℤ)) + finrank k' (LinearMap.ker Φ) =
      finrank k' (riemannRochSpace (Divisor.conorm k' F' E)) := by
    rw [← Finset.sum_coe_sort S fun P ↦ (P.singularityDegree k' F' : ℤ)]
    exact_mod_cast hrank
  -- the kernel contains `L(E) · k'`, of dimension `ℓ(E)`
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
  refine ⟨fun P hP ↦ hfin ⟨P, hP⟩, by omega, fun hreg ↦ ?_⟩
  have hker : LinearMap.ker Φ = W :=
    hΦ ▸ le_antisymm (ker_pi_localMap_le_span h hn hF' hs0 hs S hreg)
      (span_le_ker_pi_localMap hF' hs0 hs S)
  rw [hker, hW] at hrank'
  omega

/-- **The singularity quotient is finite-dimensional**: `𝒪'_P ⧸ 𝒪_P · k'` has finite
`k'`-dimension at every place `P` of `F / k`. -/
theorem Place.finiteDimensional_singularityQuotient (P : Place k F) :
    FiniteDimensional k' (P.singularityQuotient k' F') :=
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  (sum_singularityDegree_add_genus_le hF hex h hex' hn {P}).1 P (Finset.mem_singleton_self P)

/-- **The singularity degree vanishes at almost every place**: only finitely many places `P` of
`F / k` have `𝒪_P ⊗_k k'` not integrally closed in `F'`. -/
theorem finite_setOf_singularityDegree_ne_zero :
    {P : Place k F | P.singularityDegree k' F' ≠ 0}.Finite := by
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  by_contra hinf
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (genus k F + 1)
  have hle := (sum_singularityDegree_add_genus_le hF hex h hex' hn S).2.1
  have hsum : (S.card : ℤ) ≤ ∑ P ∈ S, (P.singularityDegree k' F' : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun P hP ↦ ?_
    have := Nat.pos_of_ne_zero (hS hP)
    push_cast
    omega
  rw [hcard] at hsum
  push_cast at hsum
  omega

/-- **The genus drop is the sum of the singularity degrees**: if `k` is the exact constant field of
`F`, `k'` the exact constant field of `F' = F · k'` and `[F' : F] = [k' : k]`, then

`g(F / k) = g(F' / k') + ∑_P δ_P`,

where `δ_P = dim_{k'} (𝒪'_P ⧸ 𝒪_P ⊗_k k')` vanishes at all but finitely many places. -/
theorem genus_eq_genus_add_finsum_singularityDegree :
    genus k F = genus k' F' + ∑ᶠ P : Place k F, P.singularityDegree k' F' := by
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hex' hn
  have hreg (P : Place k F) (hP : P ∉ hfin.toFinset) :
      P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
    have := P.finiteDimensional_singularityQuotient hF hex h hex' hn
    rw [← P.singularityDegree_eq_zero_iff k' F']
    simpa using hP
  have heq := (sum_singularityDegree_add_genus_le hF hex h hex' hn hfin.toFinset).2.2 hreg
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [Function.support])]
  have heq' : ((∑ P ∈ hfin.toFinset, P.singularityDegree k' F' : ℕ) : ℤ) + genus k' F' =
      genus k F := by
    push_cast
    exact heq
  omega

/-- **The genus is unchanged exactly when no place becomes singular**: `g(F' / k') = g(F / k)` if
and only if `𝒪_P ⊗_k k'` is integrally closed in `F'` at every place `P` of `F / k`. -/
theorem genus_eq_genus_iff_forall_constantSpanIntegers_eq :
    genus k' F' = genus k F ↔
      ∀ P : Place k F, P.constantSpanIntegers k' F' = P.integralClosureSubmodule k' F' := by
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hex' hn
  have (P : Place k F) := P.finiteDimensional_singularityQuotient hF hex h hex' hn
  simp_rw [← Place.singularityDegree_eq_zero_iff k' F']
  rw [genus_eq_genus_add_finsum_singularityDegree hF hex h hex' hn, left_eq_add,
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [Function.support]),
    Finset.sum_eq_zero_iff]
  refine ⟨fun h0 P ↦ ?_, fun h0 P _ ↦ h0 P⟩
  by_cases hP : P ∈ hfin.toFinset
  · exact h0 P hP
  · simpa using hP

end Genus

end TauCeti
