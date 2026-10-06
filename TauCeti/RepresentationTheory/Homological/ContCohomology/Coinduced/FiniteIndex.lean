/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
import TauCeti.GroupTheory.Coset.Basic

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
* `TauCeti.DiscreteCoind.sum_single`: for an open finite-index `U`, a coinduced function is the
  sum of its singles `TauCeti.DiscreteCoind.single` over a right transversal, so `Coind_U^G A` is
  the direct sum of `[G : U]` copies of `A`.
* `TauCeti.DiscreteCoind.natCard_of_isOpen`: `|Coind_U^G A| = |A| ^ [G : U]` for an open
  finite-index `U` acting trivially on `A`.
* `TauCeti.DiscreteCoind.trace_eq_inv_smul_apply`: the trace of a coinduced function supported
  on the single right coset `U * g` is `g⁻¹ • f g`.
* `TauCeti.DiscreteCoind.trace_single` and `TauCeti.DiscreteCoind.trace_surjective`: for an open
  finite-index `U` and a discrete `G`-module `M`, the trace of `single g m` is `g⁻¹ • m`, so the
  trace `Coind_U^G M → M` is surjective.
* `TauCeti.DiscreteCoind.trace_eq_relIndex_nsmul_of_forall_smul_eq`,
  `TauCeti.DiscreteCoind.trace_eq_zero_of_forall_smul_eq`: on the `G`-invariants of `Coind_V^G M`,
  for `V ≤ U` with `U` acting trivially on `M`, the trace is `[U : V]` times the norm along `G ⧸ U`;
  in particular it vanishes when `[U : V]` kills `M`. This is the co-effaceability of `H⁰` that
  Tate's duality argument for the cohomological dimension of a Demushkin group uses (Serre,
  *Structure de certains pro-p-groupes*, §9.1).
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

omit [TopologicalSpace G] in
/-- A coset `x : G ⧸ U` is the class of `h⁻¹` exactly when `h * x.out ∈ U`: the right coset
`U * x.out⁻¹` of the transversal element `x.out⁻¹` contains `h` exactly when `x = h⁻¹ U`. -/
private theorem mk_inv_eq_iff (h : G) (x : G ⧸ U) :
    (QuotientGroup.mk h⁻¹ : G ⧸ U) = x ↔ h * x.out ∈ U := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [QuotientGroup.eq, inv_inv]

end Transversal

section Single

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  [U.FiniteIndex] {A : Type v} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A] (hU : IsOpen (U : Set G))

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **A coinduced function is the sum of its singles over a right transversal.** For an open
subgroup `U` of finite index, `f = ∑_{x : G ⧸ U} single x.out⁻¹ (f x.out⁻¹)`: the right cosets
`U * x.out⁻¹` partition `G`, and on each of them `f` agrees with the single of its value at the
representative. -/
theorem sum_single (f : DiscreteCoind G U A) :
    ∑ x : G ⧸ U, single G U A hU x.out⁻¹ (f x.out⁻¹) = f := by
  ext h
  rw [sum_apply, Finset.sum_eq_single (QuotientGroup.mk h⁻¹)]
  · set x : G ⧸ U := QuotientGroup.mk h⁻¹
    have hx : h * x.out ∈ U := (mk_inv_eq_iff h x).1 rfl
    have hh : h = ((⟨h * x.out, hx⟩ : U) : G) * x.out⁻¹ := by simp
    rw [hh, single_apply_mul, ← apply_mul]
  · intro x _ hx
    refine single_apply_of_notMem hU _ fun hmem => hx ?_
    rw [inv_inv] at hmem
    exact ((mk_inv_eq_iff h x).2 hmem).symm
  · exact fun h => (h (Finset.mem_univ _)).elim

end Single

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
  [U.FiniteIndex] {M : Type v} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The trace of a function supported on one right coset**: if `f` vanishes off `U * g`, then
`tr f = g⁻¹ • f g`. In the trace `∑_{x : G ⧸ U} x.out • f x.out⁻¹` only the coset `x = g⁻¹ U`
contributes, and there `x.out⁻¹ = u * g` with `u = x.out⁻¹ * g⁻¹`, so the term is
`x.out • u • f g = g⁻¹ • f g`. -/
theorem trace_eq_inv_smul_apply (f : DiscreteCoind G U M) (g : G)
    (hf : ∀ x, x * g⁻¹ ∉ U → f x = 0) : trace G U M f = g⁻¹ • f g := by
  rw [trace_apply, Finset.sum_eq_single (QuotientGroup.mk g⁻¹)]
  · set x : G ⧸ U := QuotientGroup.mk g⁻¹
    have hx : g * x.out ∈ U := (mk_inv_eq_iff g x).1 rfl
    have hout : x.out⁻¹ = ((⟨(g * x.out)⁻¹, U.inv_mem hx⟩ : U) : G) * g := by
      simp [mul_inv_rev]
    rw [hout, apply_mul, Subgroup.smul_def, ← mul_smul]
    congr 1
    simp [mul_inv_rev]
  · intro x _ hx
    have hmem : x.out⁻¹ * g⁻¹ ∉ U := fun hmem =>
      hx ((mk_inv_eq_iff g x).2 (by simpa [mul_inv_rev] using U.inv_mem hmem)).symm
    rw [hf _ hmem, smul_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The trace of a single**: `tr (single g m) = g⁻¹ • m`, since `single g m` is supported on
the right coset `U * g` with value `m` at `g`. Not a `simp` lemma, because
`TauCeti.DiscreteCoind.trace_apply` already takes its left-hand side apart. -/
theorem trace_single (hU : IsOpen (U : Set G)) (g : G) (m : M) :
    trace G U M (single G U M hU g m) = g⁻¹ • m := by
  rw [trace_eq_inv_smul_apply _ g fun _ hx => single_apply_of_notMem hU m hx, single_apply_self]

/-- **The trace `Coind_U^G M → M` of an open subgroup is surjective**: `m` is the trace of
`single 1 m`, the function that is `g ↦ g • m` on `U` and `0` off `U`. -/
theorem trace_surjective (hU : IsOpen (U : Set G)) : Function.Surjective (trace G U M) :=
  fun m => ⟨single G U M hU 1 m, by rw [trace_single, inv_one, one_smul]⟩

end Trace

section TraceInvariants

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] {V U : Subgroup G}
  [V.FiniteIndex] [U.FiniteIndex] {M : Type v} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The trace on invariants is a multiple of the norm.** For finite-index subgroups `V ≤ U` with
`U` acting trivially on `M`, the trace of a `G`-invariant element `f` of `Coind_V^G M` is
`[U : V]` times the norm `∑_{q ∈ G ⧸ U} q.out • f 1` of its constant value. -/
theorem trace_eq_relIndex_nsmul_of_forall_smul_eq (hVU : V ≤ U)
    (htriv : ∀ u ∈ U, ∀ m : M, u • m = m) {f : DiscreteCoind G V M} (hf : ∀ g : G, g • f = f) :
    trace G V M f = V.relIndex U • ∑ q : G ⧸ U, q.out • f 1 := by
  rw [trace_apply]
  simp only [apply_eq_apply_one_of_forall_smul_eq hf]
  exact Subgroup.sum_out_smul_eq_relIndex_nsmul hVU fun u hu ↦ htriv u hu _

/-- **The trace kills the invariants once the relative index kills the module.** For finite-index
subgroups `V ≤ U` with `U` acting trivially on `M` and `[U : V] • m = 0` for every `m`, the trace
`Coind_V^G M → M` vanishes on the `G`-invariants: the map `H⁰(G, Coind_V^G M) → H⁰(G, M)` induced
by `trace` is zero. -/
theorem trace_eq_zero_of_forall_smul_eq (hVU : V ≤ U) (htriv : ∀ u ∈ U, ∀ m : M, u • m = m)
    (hkill : ∀ m : M, V.relIndex U • m = 0) {f : DiscreteCoind G V M} (hf : ∀ g : G, g • f = f) :
    trace G V M f = 0 := by
  rw [trace_eq_relIndex_nsmul_of_forall_smul_eq hVU htriv hf, hkill]

end TraceInvariants

end DiscreteCoind

end TauCeti
