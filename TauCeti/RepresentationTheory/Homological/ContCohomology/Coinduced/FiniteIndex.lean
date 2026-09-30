/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete

/-!
# Coinduction along a subgroup of finite index

For a subgroup `U` of a topological group `G` and a `U`-module `A`, an element of the coinduced
module `Coind_U^G A` of `TauCeti.DiscreteCoind` is determined by its values on a right transversal
of `U`, since `f (u * g) = u • f g`. When `U` has finite index and `A` is finite this makes
`Coind_U^G A` finite. When moreover `U` is open and acts trivially on `A`, every function on the
coset space extends: `Coind_U^G A` is the module of *all* functions `G ⧸ U → A`, read through
`g ↦ g⁻¹` because the coinduced functions are constant on right cosets while `G ⧸ U` is the space
of left cosets. This is the permutation module `A[G ⧸ U]`, of order `|A| ^ [G : U]`.

## Main definitions

* `TauCeti.DiscreteCoind.quotientPiAddEquiv`: for an open `U` acting trivially on `A`, the
  additive equivalence `Coind_U^G A ≃+ (G ⧸ U → A)`; `quotientPiAddEquiv_smul_apply` records that
  it carries the action of `G` on `Coind_U^G A` to the permutation action on `G ⧸ U → A`.

## Main results

* `TauCeti.DiscreteCoind.instFinite`: `Coind_U^G A` is finite for finite `A` and finite-index
  `U`, since restriction to a right transversal is injective.
* `TauCeti.DiscreteCoind.natCard_of_isOpen`: `|Coind_U^G A| = |A| ^ [G : U]` for an open
  finite-index `U` acting trivially on `A`.
* `TauCeti.DiscreteCoind.trace_surjective`: for an open finite-index `U` and a discrete
  `G`-module `M`, the trace `Coind_U^G M → M` is surjective.
-/

public section

namespace TauCeti

universe u v

namespace DiscreteCoind

section Transversal

variable {G : Type u} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

/-- **Restriction to a right transversal is injective.** An element of `Coind_U^G A` is determined
by its values at the representatives `(Quotient.out x)⁻¹`, `x : G ⧸ U`, which form a right
transversal of `U` in `G`. -/
private theorem apply_out_inv_injective :
    Function.Injective fun (f : DiscreteCoind G U A) (x : G ⧸ U) => f (Quotient.out x)⁻¹ := by
  intro f f' h
  ext g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g⁻¹
  have hg : g = (u : G) * ((QuotientGroup.mk g⁻¹ : G ⧸ U).out)⁻¹ := by
    rw [hu, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have h' := congrFun h (QuotientGroup.mk g⁻¹)
  simp only at h'
  rw [hg, apply_mul, apply_mul, h']

/-- `Coind_U^G A` is finite when `A` is finite and `U` has finite index. -/
instance instFinite [Finite A] [U.FiniteIndex] : Finite (DiscreteCoind G U A) :=
  Finite.of_injective _ apply_out_inv_injective

end Transversal

section Trivial

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

variable (G U A) in
/-- **The coinduced module of a trivial module along an open subgroup is the permutation
module.** For an open subgroup `U` acting trivially on `A`, the coinduced module `Coind_U^G A` is
the module of all functions `G ⧸ U → A`: a coinduced function is constant on the right cosets of
`U`, and `g ↦ g⁻¹` matches right cosets with the left cosets that make up `G ⧸ U`. -/
def quotientPiAddEquiv (hU : IsOpen (U : Set G)) (htriv : ∀ (u : U) (a : A), u • a = a) :
    DiscreteCoind G U A ≃+ (G ⧸ U → A) where
  toFun f := Quotient.lift (fun g : G => f g⁻¹) fun a b hab => by
    have hab' : a⁻¹ * b ∈ U := QuotientGroup.leftRel_apply.1 hab
    have hb : b⁻¹ = ((⟨(a⁻¹ * b)⁻¹, U.inv_mem hab'⟩ : U) : G) * a⁻¹ := by
      rw [Subgroup.coe_mk, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [hb, apply_mul, htriv]
  invFun φ := mk G U A (fun g => φ (QuotientGroup.mk g⁻¹))
    (by
      have := QuotientGroup.discreteTopology hU
      exact ((IsLocallyConstant.iff_continuous fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ U)).2
        (continuous_quot_mk.comp continuous_inv)).comp φ)
    (fun u g => by rw [mul_inv_rev, QuotientGroup.mk_mul_of_mem _ (U.inv_mem u.2), htriv])
  left_inv f := ext fun g => by
    rw [mk_apply]
    exact congrArg f (inv_inv g)
  right_inv φ := funext fun x => by
    induction x using QuotientGroup.induction_on with
    | H g => exact congrArg φ (congrArg _ (inv_inv g))
  map_add' f f' := funext fun x => by
    induction x using QuotientGroup.induction_on with
    | H g => exact congrFun (coe_add f f') g⁻¹

variable (hU : IsOpen (U : Set G)) (htriv : ∀ (u : U) (a : A), u • a = a)

/-- `quotientPiAddEquiv` reads a coinduced function at the inverse of a coset representative. -/
@[simp]
theorem quotientPiAddEquiv_apply_mk (f : DiscreteCoind G U A) (g : G) :
    quotientPiAddEquiv G U A hU htriv f (QuotientGroup.mk g) = f g⁻¹ := (rfl)

/-- The inverse of `quotientPiAddEquiv` sends `φ : G ⧸ U → A` to the coinduced function
`g ↦ φ (g⁻¹ U)`. -/
@[simp]
theorem quotientPiAddEquiv_symm_apply (φ : G ⧸ U → A) (g : G) :
    (quotientPiAddEquiv G U A hU htriv).symm φ g = φ (QuotientGroup.mk g⁻¹) := (rfl)

/-- **`quotientPiAddEquiv` is `G`-equivariant.** The action `(g • f) x = f (x * g)` of `G` on
`Coind_U^G A` corresponds to the permutation action `(g • φ) y = φ (g⁻¹ • y)` on `G ⧸ U → A`, for
the translation action of `G` on the coset space `G ⧸ U`. -/
@[simp]
theorem quotientPiAddEquiv_smul_apply (g : G) (f : DiscreteCoind G U A) (y : G ⧸ U) :
    quotientPiAddEquiv G U A hU htriv (g • f) y =
      quotientPiAddEquiv G U A hU htriv f (g⁻¹ • y) := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, quotientPiAddEquiv_apply_mk,
      quotientPiAddEquiv_apply_mk, coe_smul, mul_inv_rev, inv_inv]

include hU htriv in
/-- **The order of the coinduced module of a trivial module.** For an open subgroup `U` of finite
index acting trivially on `A`, `Coind_U^G A` has `|A| ^ [G : U]` elements. -/
theorem natCard_of_isOpen [U.FiniteIndex] :
    Nat.card (DiscreteCoind G U A) = Nat.card A ^ U.index := by
  rw [Nat.card_congr (quotientPiAddEquiv G U A hU htriv).toEquiv, Nat.card_fun, U.index_eq_card]

end Trivial

section Trace

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  [U.FiniteIndex] {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The trace `Coind_U^G M → M` of an open subgroup is surjective.** An element `m` of the
discrete `G`-module `M` is the trace of the function that is `g ↦ g • m` on `U` and `0` off `U`:
that function is locally constant because `U` is clopen and `g ↦ g • m` is continuous into the
discrete module `M`, and in the trace only the coset of `1` contributes. -/
theorem trace_surjective (hU : IsOpen (U : Set G)) : Function.Surjective (trace G U M) := by
  classical
  intro m
  have hf : IsLocallyConstant fun g : G ↦ g • m :=
    (IsLocallyConstant.iff_continuous _).2 (continuous_id.smul continuous_const)
  have hclopen : IsClopen (U : Set G) := ⟨U.isClosed_of_isOpen hU, hU⟩
  have hlc : IsLocallyConstant ((U : Set G).indicator fun g ↦ g • m) :=
    (LocallyConstant.indicator ⟨_, hf⟩ hclopen).isLocallyConstant
  refine ⟨mk G U M ((U : Set G).indicator fun g ↦ g • m) hlc fun u g ↦ ?_, ?_⟩
  · by_cases hg : g ∈ U
    · rw [Set.indicator_of_mem (U.mul_mem u.2 hg), Set.indicator_of_mem hg, mul_smul,
        Subgroup.smul_def]
    · have hug : (u : G) * g ∉ U := fun h ↦ hg (by simpa using U.mul_mem (U.inv_mem u.2) h)
      rw [Set.indicator_of_notMem hug, Set.indicator_of_notMem hg, smul_zero]
  · rw [trace_apply, Finset.sum_eq_single ((1 : G) : G ⧸ U)]
    · have h1 : ((1 : G) : G ⧸ U).out⁻¹ ∈ U := by
        simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ U))
      rw [coe_mk, Set.indicator_of_mem h1, smul_inv_smul]
    · intro x _ hx
      have hx' : x.out⁻¹ ∉ U := fun h ↦
        hx (by rw [← QuotientGroup.out_eq' x]; exact QuotientGroup.eq.2 (by simpa using h))
      rw [coe_mk, Set.indicator_of_notMem hx', smul_zero]
    · exact fun h ↦ (h (Finset.mem_univ _)).elim

end Trace

end DiscreteCoind

end TauCeti
