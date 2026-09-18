/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.GroupTheory.Index.Basic
public import TauCeti.GroupTheory.Coset.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Transitivity of low-degree corestriction

For finite-index open subgroups `V ≤ U ≤ G`, corestriction is transitive in degrees zero, one,
and two: `cor_V^G = cor_U^G ∘ cor_V^U`.  The tower of coset spaces is organised by Mathlib's
equivalence `Subgroup.quotientEquivProdOfLE'`, which splits `G ⧸ V` as `(G ⧸ U) × (U ⧸ V)`.

Transitivity is what makes a corestriction computable one step at a time: it may be evaluated
through any chain of intermediate finite-index open subgroups instead of in a single jump from `V`
to `G`, and conversely a corestriction from `V` may be recognised as one from an intermediate `U`.

## Main declarations

* `explicitCor0Le`, `explicitCor1Le`, `explicitCor2Le`: corestriction along a subgroup inclusion
  `V ≤ U`, evaluated by `coe_explicitCor0Le`, `explicitCor1Le_mk`, and `explicitCor2Le_mk`.
* `explicitCor0Le_trans`: transitivity of relative degree-zero corestriction in a subgroup tower.
* `explicitCor0_trans`, `explicitCor1_trans`, `explicitCor2_trans`: transitivity from a subgroup to
  the ambient group in degrees zero, one, and two.
-/

public section

open scoped Pointwise

namespace TauCeti.ContCohomology

universe u v

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (U V : Subgroup G) (hVU : V ≤ U)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private def compositeTransversal (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (s : U ⧸ V.subgroupOf U → U) (q : G ⧸ V) : G :=
  t ((Subgroup.quotientEquivProdOfLE' hVU t ht q).1) *
    s ((Subgroup.quotientEquivProdOfLE' hVU t ht q).2)

private theorem compositeTransversal_spec (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (s : U ⧸ V.subgroupOf U → U)
    (hs : ∀ v : U ⧸ V.subgroupOf U,
      (QuotientGroup.mk (s v) : U ⧸ V.subgroupOf U) = v)
    (q : G ⧸ V) :
    (QuotientGroup.mk (compositeTransversal G U V (hVU := hVU) t ht s q) : G ⧸ V) = q := by
  let e := Subgroup.quotientEquivProdOfLE' hVU t ht
  let hmap : ∀ a b : U, QuotientGroup.leftRel (V.subgroupOf U) a b →
      QuotientGroup.leftRel V (t (e q).1 * (a : G)) (t (e q).1 * (b : G)) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    -- Expose the ambient values of the two subtype elements in the coset relation.
    change ((a : G)⁻¹ * (b : G)) ∈ V at hab
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hab
  calc
    QuotientGroup.mk (compositeTransversal G U V (hVU := hVU) t ht s q) =
        e.symm (e q) := by
      -- Unfold the inverse of the tower equivalence as a quotient map on the inner coset.
      change QuotientGroup.mk (t (e q).1 * s (e q).2) =
        Quotient.map' (fun b : U => t (e q).1 * b) hmap (e q).2
      calc
        QuotientGroup.mk (t (e q).1 * s (e q).2) =
            Quotient.map' (fun b : U => t (e q).1 * b) hmap
              (QuotientGroup.mk (s (e q).2)) := rfl
        _ = Quotient.map' (fun b : U => t (e q).1 * b) hmap (e q).2 :=
          congrArg _ (hs (e q).2)
    _ = q := e.symm_apply_apply q

private theorem quotientEquivProdOfLE'_inv_smul (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (a : G ⧸ U) (b : U ⧸ V.subgroupOf U) (γ : G) :
    Subgroup.quotientEquivProdOfLE' hVU t ht
        (γ⁻¹ • (Subgroup.quotientEquivProdOfLE' hVU t ht).symm (a, b)) =
      (γ⁻¹ • a,
        (⟨lWord U t a γ, lWord_mem U t ht a γ⟩ : U)⁻¹ • b) := by
  let e := Subgroup.quotientEquivProdOfLE' hVU t ht
  apply e.symm.injective
  rw [e.symm_apply_apply]
  induction b using Quotient.inductionOn' with
  | _ b =>
      -- Quotient induction exposes representatives on both sides of the translated coset.
      change QuotientGroup.mk (γ⁻¹ * (t a * (b : G))) =
        QuotientGroup.mk (t (γ⁻¹ • a) *
          ((⟨lWord U t a γ, lWord_mem U t ht a γ⟩ : U)⁻¹ * b : U))
      congr 1
      simp only [lWord_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group

private theorem lWord_composite (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (s : U ⧸ V.subgroupOf U → U) (q : G ⧸ V) (γ : G) :
    lWord V (compositeTransversal G U V (hVU := hVU) t ht s) q γ =
      (lWord (V.subgroupOf U) s
        (Subgroup.quotientEquivProdOfLE' hVU t ht q).2
        ⟨lWord U t (Subgroup.quotientEquivProdOfLE' hVU t ht q).1 γ,
          lWord_mem U t ht _ γ⟩ : U) := by
  let e := Subgroup.quotientEquivProdOfLE' hVU t ht
  let L : U := ⟨lWord U t (e q).1 γ, lWord_mem U t ht _ γ⟩
  have hcoords : e (γ⁻¹ • q) = (γ⁻¹ • (e q).1, L⁻¹ • (e q).2) := by
    calc
      e (γ⁻¹ • q) = e (γ⁻¹ • e.symm (e q)) :=
        congrArg (fun x => e (γ⁻¹ • x)) (e.symm_apply_apply q).symm
      _ = (γ⁻¹ • (e q).1, L⁻¹ • (e q).2) :=
        quotientEquivProdOfLE'_inv_smul G U V hVU t ht (e q).1 (e q).2 γ
  have hfst := congrArg Prod.fst hcoords
  have hsnd := congrArg Prod.snd hcoords
  simp only at hfst hsnd
  rw [lWord_def, lWord_def]
  unfold compositeTransversal
  -- Expose the outer and inner representatives in the two transversal words.
  change (t (e q).1 * (s (e q).2 : G))⁻¹ * γ *
      (t (e (γ⁻¹ • q)).1 * (s (e (γ⁻¹ • q)).2 : G)) =
    ((s (e q).2 : U)⁻¹ * L * s (L⁻¹ • (e q).2) : U)
  rw [hfst, hsnd]
  -- After rewriting the tower coordinates, forget the remaining subgroup coercions.
  change (t (e q).1 * (s (e q).2 : G))⁻¹ * γ *
      (t (γ⁻¹ • (e q).1) * (s (L⁻¹ • (e q).2) : G)) =
    (s (e q).2 : G)⁻¹ * (L : G) * (s (L⁻¹ • (e q).2) : G)
  simp only [L, lWord_def]
  group

section FiniteSums

variable [U.FiniteIndex] [V.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private theorem sum_compositeTransversal (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (s : U ⧸ V.subgroupOf U → U) (m : M) :
    ∑ q : G ⧸ V, compositeTransversal G U V (hVU := hVU) t ht s q • m =
      ∑ a : G ⧸ U, t a • ∑ b : U ⧸ V.subgroupOf U, (s b : U) • m := by
  let e := Subgroup.quotientEquivProdOfLE' hVU t ht
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [compositeTransversal, e, e.apply_symm_apply, mul_smul, Subgroup.smul_def]

private theorem cochainsCor1_composite (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (s : U ⧸ V.subgroupOf U → U)
    (hs : ∀ v : U ⧸ V.subgroupOf U,
      (QuotientGroup.mk (s v) : U ⧸ V.subgroupOf U) = v)
    (f : V → M) :
    cochainsCor1 G M V (compositeTransversal G U V (hVU := hVU) t ht s)
        (compositeTransversal_spec G U V hVU t ht s hs) f =
      cochainsCor1 G M U t ht
        (cochainsCor1 U M (V.subgroupOf U) s hs
          (fun x => f (Subgroup.subgroupOfEquivOfLe hVU x))) := by
  ext γ
  let e := Subgroup.quotientEquivProdOfLE' hVU t ht
  simp only [cochainsCor1_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [compositeTransversal, e, e.apply_symm_apply, mul_smul, Subgroup.smul_def]
  congr 2
  apply congrArg f
  apply Subtype.ext
  -- Both arguments lie in `V`; compare their ambient values using the composite-word identity.
  change lWord V (compositeTransversal G U V (hVU := hVU) t ht s) (e.symm (a, b)) γ =
    (lWord (V.subgroupOf U) s b ⟨lWord U t a γ, lWord_mem U t ht a γ⟩ : U)
  simpa only [e, Equiv.apply_symm_apply] using
    lWord_composite G U V hVU t ht s (e.symm (a, b)) γ

private theorem cochainsCor2_composite (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (s : U ⧸ V.subgroupOf U → U)
    (hs : ∀ v : U ⧸ V.subgroupOf U,
      (QuotientGroup.mk (s v) : U ⧸ V.subgroupOf U) = v)
    (f : V × V → M) :
    cochainsCor2 G M V (compositeTransversal G U V (hVU := hVU) t ht s)
        (compositeTransversal_spec G U V hVU t ht s hs) f =
      cochainsCor2 G M U t ht
        (cochainsCor2 U M (V.subgroupOf U) s hs
          (fun q => f (Subgroup.subgroupOfEquivOfLe hVU q.1,
            Subgroup.subgroupOfEquivOfLe hVU q.2))) := by
  ext q
  obtain ⟨γ, η⟩ := q
  let e := Subgroup.quotientEquivProdOfLE' hVU t ht
  simp only [cochainsCor2_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [compositeTransversal, e, e.apply_symm_apply, mul_smul, Subgroup.smul_def]
  congr 2
  apply congrArg f
  apply Prod.ext
  · apply Subtype.ext
    -- Compare the first `V`-valued word after forgetting its membership proof.
    change lWord V (compositeTransversal G U V (hVU := hVU) t ht s) (e.symm (a, b)) γ =
      (lWord (V.subgroupOf U) s b
        ⟨lWord U t a γ, lWord_mem U t ht a γ⟩ : U)
    simpa only [e, Equiv.apply_symm_apply] using
      lWord_composite G U V hVU t ht s (e.symm (a, b)) γ
  · let L : U := ⟨lWord U t a γ, lWord_mem U t ht a γ⟩
    have hcoords : e (γ⁻¹ • e.symm (a, b)) = (γ⁻¹ • a, L⁻¹ • b) :=
      quotientEquivProdOfLE'_inv_smul G U V hVU t ht a b γ
    apply Subtype.ext
    -- The translated tower coordinates identify the second inner transversal word.
    change lWord V (compositeTransversal G U V (hVU := hVU) t ht s)
        (γ⁻¹ • e.symm (a, b)) η =
      (lWord (V.subgroupOf U) s (L⁻¹ • b)
        ⟨lWord U t (γ⁻¹ • a) η, lWord_mem U t ht (γ⁻¹ • a) η⟩ : U)
    have h := lWord_composite G U V hVU t ht s (γ⁻¹ • e.symm (a, b)) η
    rw [hcoords] at h
    exact h

end FiniteSums

/-! ### Relative corestriction -/

private def h0SubgroupOf : H0 V M →+ H0 (V.subgroupOf U) M where
  toFun m := ⟨m, (FixedPoints.mem_addSubgroup (V.subgroupOf U) M m).2 fun x =>
    (FixedPoints.mem_addSubgroup V M m).1 m.2 (Subgroup.subgroupOfEquivOfLe hVU x)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
private theorem coe_h0SubgroupOf (m : H0 V M) :
    (h0SubgroupOf G M U V hVU m : M) = m :=
  rfl

/-- **Relative degree-zero corestriction** for `V ≤ U`: identify `V` with its copy inside `U`,
then apply degree-zero corestriction there. -/
noncomputable def explicitCor0Le [(V.subgroupOf U).FiniteIndex] : H0 V M →+ H0 U M :=
  (explicitCor0 U M (V.subgroupOf U)).comp
    (h0SubgroupOf G M U V hVU)

/-- The underlying coefficient of relative degree-zero corestriction is the norm over the cosets
of `V` in `U`, taken along the canonical transversal. -/
@[simp]
theorem coe_explicitCor0Le [(V.subgroupOf U).FiniteIndex] (m : H0 V M) :
    (explicitCor0Le G M U V hVU m : M) =
      ∑ b : U ⧸ V.subgroupOf U, (Quotient.out b : U) • (m : M) := by
  rw [explicitCor0Le, AddMonoidHom.comp_apply, coe_explicitCor0, coe_h0SubgroupOf]

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul G M] in
/-- The identity map of `M` is equivariant along Mathlib's topological identification of
`V.subgroupOf U` with `V`: that identification leaves ambient values in `G` unchanged, so the two
subgroups act on `M` through the same elements. -/
private theorem id_subgroupOfContinuousMulEquivOfLe_smul (x : V.subgroupOf U) (m : M) :
    (AddMonoidHom.id M)
        ((Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V) x • m) =
      x • (AddMonoidHom.id M) m :=
  rfl

/-- **Relative degree-one corestriction** for an inclusion `V ≤ U` with `V` open *in `U`*; the
ambient group `U` need not be open in `G`. The source is the cohomology of `V` itself, transported
to the definitionally different subgroup `V.subgroupOf U` along Mathlib's topological
identification `Subgroup.subgroupOfContinuousMulEquivOfLe`, which leaves ambient values -- and
hence the action on `M` -- unchanged. -/
noncomputable def explicitCor1Le [(V.subgroupOf U).FiniteIndex]
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U)) : H1 V M →+ H1 U M :=
  (explicitCor1 U M (V.subgroupOf U) hV).comp
    (explicitMap1 V M (V.subgroupOf U) M
      (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
      (AddMonoidHom.id M) continuous_id (id_subgroupOfContinuousMulEquivOfLe_smul G M U V hVU))

/-- Relative degree-one corestriction sends the class of a continuous `1`-cocycle on `V` to the
class of the degree-one corestriction cochain of its transport to `V.subgroupOf U`, taken over the
canonical transversal. -/
@[simp]
theorem explicitCor1Le_mk [(V.subgroupOf U).FiniteIndex]
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U)) (f : Z1 V M) :
    explicitCor1Le G M U V hVU hV (f : H1 V M) =
      (cocyclesCor1 U M (V.subgroupOf U) Quotient.out Quotient.out_eq hV
        (cocyclesMap1 V M (V.subgroupOf U) M
          (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
          (AddMonoidHom.id M) continuous_id
          (by exact id_subgroupOfContinuousMulEquivOfLe_smul G M U V hVU) f) : H1 U M) := by
  rw [explicitCor1Le, AddMonoidHom.comp_apply, explicitMap1_mk, explicitCor1_mk]

/-- **Relative degree-two corestriction** for an inclusion `V ≤ U` with `V` open *in `U`*; the
ambient group `U` need not be open in `G`. The source is transported along Mathlib's canonical
topological group isomorphism `V.subgroupOf U ≃ₜ* V`. -/
noncomputable def explicitCor2Le [(V.subgroupOf U).FiniteIndex]
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U)) : H2 V M →+ H2 U M :=
  (explicitCor2 U M (V.subgroupOf U) hV).comp
    (explicitMap2 V M (V.subgroupOf U) M
      (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
      (AddMonoidHom.id M) continuous_id (id_subgroupOfContinuousMulEquivOfLe_smul G M U V hVU))

/-- Relative degree-two corestriction sends the class of a continuous `2`-cocycle on `V` to the
class of the degree-two corestriction cochain of its transport to `V.subgroupOf U`, taken over the
canonical transversal. -/
@[simp]
theorem explicitCor2Le_mk [(V.subgroupOf U).FiniteIndex]
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U)) (f : Z2 V M) :
    explicitCor2Le G M U V hVU hV (f : H2 V M) =
      (cocyclesCor2 U M (V.subgroupOf U) Quotient.out Quotient.out_eq hV
        (cocyclesMap2 V M (V.subgroupOf U) M
          (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
          (AddMonoidHom.id M) continuous_id
          (by exact id_subgroupOfContinuousMulEquivOfLe_smul G M U V hVU) f) : H2 U M) := by
  rw [explicitCor2Le, AddMonoidHom.comp_apply, explicitMap2_mk, explicitCor2_mk]

end Topological

/-! ### Transitivity -/

/-- **Transitivity of degree-zero corestriction.** For subgroups `V ≤ U ≤ G` with `V` of finite
index in `U` and `U` of finite index in `G`, `cor⁰_V^G = cor⁰_U^G ∘ cor⁰_V^U`. -/
theorem explicitCor0_trans [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex] :
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    explicitCor0 G M V =
      (explicitCor0 G M U).comp (explicitCor0Le G M U V (hVU := hVU)) := by
  have := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let t : G ⧸ U → G := Quotient.out
  let s : U ⧸ V.subgroupOf U → U := Quotient.out
  let r := compositeTransversal G U V (hVU := hVU) t Quotient.out_eq s
  have hr := compositeTransversal_spec G U V hVU t Quotient.out_eq s Quotient.out_eq
  rw [explicitCor0_eq_transversal G M V r hr]
  ext m
  simp only [AddMonoidHom.comp_apply, explicitCor0Le, coe_explicitCor0Transversal,
    coe_explicitCor0, coe_h0SubgroupOf]
  -- Forget the fixed-point membership proofs and expose the single and iterated norm sums.
  change (∑ q : G ⧸ V, r q • (m : M)) =
    ∑ a : G ⧸ U, t a • ∑ b : U ⧸ V.subgroupOf U, (s b : U) • (m : M)
  exact sum_compositeTransversal G M U V hVU t Quotient.out_eq s (m : M)

private theorem finsum_smul_quotient_trans (hVU : V ≤ U) (W : Subgroup G) (hUW : U ≤ W)
    [(U.subgroupOf W).FiniteIndex] [(V.subgroupOf U).FiniteIndex]
    [(V.subgroupOf W).FiniteIndex] (m : M) (hm : ∀ v ∈ V, v • m = m) :
    ∑ᶠ q : W ⧸ V.subgroupOf W, (q.out : G) • m =
      ∑ᶠ q : W ⧸ U.subgroupOf W, (q.out : G) •
        (∑ᶠ r : U ⧸ V.subgroupOf U, (r.out : G) • m) := by
  let UW := U.subgroupOf W
  let VW := V.subgroupOf W
  have hVWUW : VW ≤ UW := fun v hv ↦ hVU hv
  let mVW : H0 VW M := ⟨m, fun v ↦ hm v (Subgroup.mem_subgroupOf.mp v.2)⟩
  let _ : (VW.subgroupOf UW).FiniteIndex :=
    ⟨(Subgroup.relIndex_subgroupOf hUW).trans_ne Subgroup.FiniteIndex.index_ne_zero⟩
  have h := congrArg (fun f ↦ f mVW) (explicitCor0_trans W M UW VW hVWUW)
  -- Transport the inner sum over cosets of `VW` in `UW` to one over cosets of `V` in `U`.
  let e := Subgroup.quotientSubgroupOfSubgroupOfEquiv (H := V) hUW
  have hsum :
      ∑ r : UW ⧸ VW.subgroupOf UW, ((r.out : UW) : G) • m =
        ∑ r : U ⧸ V.subgroupOf U, (r.out : G) • m := by
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    -- The representative of `e r` differs from that of `r` by an element of `V`.
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf U)
      (Subgroup.subgroupOfEquivOfLe hUW r.out)
    rw [← QuotientGroup.out_eq' r, Subgroup.quotientSubgroupOfSubgroupOfEquiv_apply_mk, hv,
      QuotientGroup.out_eq' r, Subgroup.coe_mul, mul_smul,
      hm _ (Subgroup.mem_subgroupOf.mp v.2), Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype]
  calc
    _ = ∑ q : W ⧸ U.subgroupOf W, (q.out : G) •
          (∑ r : UW ⧸ VW.subgroupOf UW, ((r.out : UW) : G) • m) := by
      simpa only [coe_explicitCor0, coe_explicitCor0Le, AddMonoidHom.comp_apply,
        Subgroup.smul_def] using congrArg Subtype.val h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [hsum]

/-- **Transitivity of relative degree-zero corestriction.** For subgroups `V ≤ U ≤ W`, the
relative corestriction from `V` to `W` is the composite of the relative corestrictions through
`U`. -/
theorem explicitCor0Le_trans (W : Subgroup G) (hUW : U ≤ W)
    [(U.subgroupOf W).FiniteIndex] [(V.subgroupOf U).FiniteIndex] :
    haveI := Subgroup.finiteIndex_subgroupOf_trans V U W
    explicitCor0Le G M W V (hVU.trans hUW) =
      (explicitCor0Le G M W U hUW).comp (explicitCor0Le G M U V hVU) := by
  have := Subgroup.finiteIndex_subgroupOf_trans V U W
  ext m
  simp only [coe_explicitCor0Le, AddMonoidHom.comp_apply, Subgroup.smul_def]
  simpa only [finsum_eq_sum_of_fintype] using
    finsum_smul_quotient_trans G M U V hVU W hUW (m : M) fun v hv ↦
      (FixedPoints.mem_addSubgroup V M m).1 m.2 ⟨v, hv⟩

section TransitivityTopological

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]

/-- **Transitivity of degree-one corestriction.** For open subgroups `V ≤ U ≤ G` with `V` of
finite index in `U` and `U` of finite index in `G`, `cor¹_V^G = cor¹_U^G ∘ cor¹_V^U`. -/
theorem explicitCor1_trans (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G)) :
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    explicitCor1 G M V hV =
      (explicitCor1 G M U hU).comp
        (explicitCor1Le G M U V hVU (Subgroup.subgroupOf_isOpen U V hV)) := by
  have := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let t : G ⧸ U → G := Quotient.out
  let s : U ⧸ V.subgroupOf U → U := Quotient.out
  let r := compositeTransversal G U V (hVU := hVU) t Quotient.out_eq s
  have hr := compositeTransversal_spec G U V hVU t Quotient.out_eq s Quotient.out_eq
  rw [explicitCor1_eq_transversal G M V r hr hV]
  ext f
  -- The quotient extensionality tactic leaves a cocycle representative; restore its class coercion.
  change explicitCor1Transversal G M V r hr hV (f : H1 V M) =
    ((explicitCor1 G M U hU).comp
      (explicitCor1Le G M U V hVU (Subgroup.subgroupOf_isOpen U V hV))) (f : H1 V M)
  rw [AddMonoidHom.comp_apply, explicitCor1Le_mk, explicitCor1Transversal_mk,
    explicitCor1_mk]
  apply congrArg (fun z : Z1 G M => (z : H1 G M))
  apply Subtype.ext
  simp only [coe_cocyclesCor1, cocyclesMap1_coe]
  have hpull :
      cochainsMap1 ((Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V) :
            V.subgroupOf U →* V) (AddMonoidHom.id M) f =
        fun x => (f : V → M) (Subgroup.subgroupOfEquivOfLe hVU x) := by
    ext x
    simp only [cochainsMap1_apply, AddMonoidHom.id_apply, MonoidHom.coe_coe,
      ContinuousMonoidHom.coe_coe, Subgroup.subgroupOfContinuousMulEquivOfLe_apply]
  rw [hpull]
  exact cochainsCor1_composite G M U V hVU t Quotient.out_eq s Quotient.out_eq f

/-- **Transitivity of degree-two corestriction.** For open subgroups `V ≤ U ≤ G` with `V` of
finite index in `U` and `U` of finite index in `G`, `cor²_V^G = cor²_U^G ∘ cor²_V^U`. -/
theorem explicitCor2_trans (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G)) :
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    explicitCor2 G M V hV =
      (explicitCor2 G M U hU).comp
        (explicitCor2Le G M U V hVU (Subgroup.subgroupOf_isOpen U V hV)) := by
  have := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let t : G ⧸ U → G := Quotient.out
  let s : U ⧸ V.subgroupOf U → U := Quotient.out
  let r := compositeTransversal G U V (hVU := hVU) t Quotient.out_eq s
  have hr := compositeTransversal_spec G U V hVU t Quotient.out_eq s Quotient.out_eq
  rw [explicitCor2_eq_transversal G M V r hr hV]
  ext f
  -- As in degree one, state the remaining equality on the class of the chosen cocycle.
  change explicitCor2Transversal G M V r hr hV (f : H2 V M) =
    ((explicitCor2 G M U hU).comp
      (explicitCor2Le G M U V hVU (Subgroup.subgroupOf_isOpen U V hV))) (f : H2 V M)
  rw [AddMonoidHom.comp_apply, explicitCor2Le_mk, explicitCor2Transversal_mk,
    explicitCor2_mk]
  apply congrArg (fun z : Z2 G M => (z : H2 G M))
  apply Subtype.ext
  simp only [coe_cocyclesCor2, cocyclesMap2_coe]
  have hpull :
      cochainsMap2 ((Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V) :
            V.subgroupOf U →* V) (AddMonoidHom.id M) f =
        fun q => (f : V × V → M) (Subgroup.subgroupOfEquivOfLe hVU q.1,
          Subgroup.subgroupOfEquivOfLe hVU q.2) := by
    ext q
    obtain ⟨x, y⟩ := q
    simp only [cochainsMap2_apply, AddMonoidHom.id_apply, MonoidHom.coe_coe,
      ContinuousMonoidHom.coe_coe, Subgroup.subgroupOfContinuousMulEquivOfLe_apply]
  rw [hpull]
  exact cochainsCor2_composite G M U V hVU t Quotient.out_eq s Quotient.out_eq f

end TransitivityTopological

end TauCeti.ContCohomology
