/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Induction.Mackey.Basic

/-!
# The Mackey double-coset formula for low-degree corestriction

Let `U` be a finite-index subgroup of a group `G`, `V` any subgroup, and `M` a `G`-module. The
Mackey double-coset formula computes restriction to `V` of the corestriction from `U`:

```text
res^G_V ∘ cor^G_U = ∑_{VsU ∈ V \ G / U} cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res^U_{U ⊓ s⁻¹Vs},
```

where `(s)_*` is conjugation by `s`, the compatible pair `(x ↦ s⁻¹ x s, m ↦ s • m)`. Each summand
is built from a representative `s = r D` of its double coset `D`, for an arbitrary choice `r` of
representatives, and the subgroup
`V ⊓ sUs⁻¹` is Tau Ceti's `TauCeti.mackeySubgroup s U V`, read inside `V`. The composite
`(s)_* ∘ res^U_{U ⊓ s⁻¹Vs}` is the single compatible-pair pullback along
`TauCeti.mackeyToH s U V : V ⊓ sUs⁻¹ → U`, `y ↦ s⁻¹ y s`, with coefficient map `m ↦ s • m`; the
summand is `TauCeti.ContCohomology.explicitMackeyTerm0` in degree zero and its companions
`explicitMackeyTerm1` and `explicitMackeyTerm2` in degrees one and two.

The proof is a choice of transversal. The left cosets `G ⧸ U` split, along
`TauCeti.mackeyQuotientEquiv`, as the disjoint union over `D ∈ V \ G / U` of the `V`-orbits
`V ⧸ (V ⊓ sUs⁻¹)`, and `Subgroup.mackeyTransversal` picks the representative `v.out * r D` of the
coset indexed by `(D, v)`. For `k ∈ V` its transversal word is the conjugate of the transversal
word of the Mackey subgroup in `V` (`Subgroup.lWord_mackeyTransversal`):

```text
ℓ_{(D, v)}(k) = s⁻¹ ℓ_v(k) s.
```

Sorting the corestriction sum over `G ⧸ U` by double cosets therefore gives the Mackey formula
**exactly on cochains** for this transversal (`cochainsCor1_mackeyTransversal`,
`cochainsCor2_mackeyTransversal`), and independence of the transversal
(`TauCeti.ContCohomology.explicitCor1_eq_transversal` and its degree-zero and degree-two
counterparts) turns that into the statement for the canonical corestriction
(`explicitCor0_mackey`, `explicitCor1_mackey`, `explicitCor2_mackey`). In positive degrees
openness of `U` is what makes the corestrictions continuous, and it makes each Mackey subgroup open
in `V` (`Subgroup.isOpen_mackeySubgroup_subgroupOf`); `V` is arbitrary.

Since the formula holds for every choice of representatives, comparing two choices that differ at a
single double coset shows that each summand depends only on the double coset `VsU`
(`explicitMackeyTerm0_eq_of_mk_eq`, `explicitMackeyTerm1_eq_of_mk_eq`,
`explicitMackeyTerm2_eq_of_mk_eq`).

## Main definitions

* `Subgroup.mackeyTransversal`: the transversal of `G ⧸ U` adapted to the double cosets `V \ G / U`.
* `Subgroup.continuousMackeyToH`: the conjugation `V ⊓ sUs⁻¹ → U` as a continuous homomorphism.
* `TauCeti.ContCohomology.explicitMackeyTerm0`, `explicitMackeyTerm1`, `explicitMackeyTerm2`: the
  summand `cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res` attached to `s` in degrees zero, one and two.

## Main results

* `Subgroup.lWord_mackeyTransversal`: the transversal word of the adapted transversal at an element
  of `V` is the conjugate of a transversal word of the Mackey subgroup in `V`.
* `TauCeti.ContCohomology.cochainsCor1_mackeyTransversal`,
  `TauCeti.ContCohomology.cochainsCor2_mackeyTransversal`: the Mackey formula on cochains.
* `TauCeti.ContCohomology.explicitCor0_mackey`, `explicitCor1_mackey`, `explicitCor2_mackey`: the
  Mackey double-coset formula on `H⁰`, `H¹` and `H²`, for any choice of double-coset
  representatives.
* `TauCeti.ContCohomology.explicitMackeyTerm0_eq_of_mk_eq`, `explicitMackeyTerm1_eq_of_mk_eq`,
  `explicitMackeyTerm2_eq_of_mk_eq`: each summand is independent of the choice of representative of
  its double coset.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.6).
* K. S. Brown, *Cohomology of Groups*, III §9.
-/

public section

open scoped Pointwise

universe u v

namespace Subgroup

open TauCeti

variable {G : Type u} [Group G] (U V : Subgroup G)
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G) (hr : ∀ D, DoubleCoset.mk V U (r D) = D)

/-- The **transversal of `G ⧸ U` adapted to the double cosets `V \ G / U`** and to a choice `r` of
representatives `r D ∈ D`: the coset indexed by `(D, v)` under `TauCeti.mackeyQuotientEquiv` is
represented by `v.out * r D`, the representative `r D` of the double coset translated by the chosen
representative `v.out ∈ V` of a coset of the Mackey subgroup `V ⊓ sUs⁻¹`, `s = r D`. -/
noncomputable def mackeyTransversal (q : G ⧸ U) : G :=
  (((mackeyQuotientEquiv U V r hr).symm q).2.out : G) * r ((mackeyQuotientEquiv U V r hr).symm q).1

/-- The adapted transversal represents the coset indexed by `(D, w)` by `w.out * r D`. -/
theorem mackeyTransversal_mackeyQuotientEquiv
    (p : Σ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) :
    mackeyTransversal U V r hr (mackeyQuotientEquiv U V r hr p) = (p.2.out : G) * r p.1 := by
  rw [mackeyTransversal, Equiv.symm_apply_apply]

/-- `Subgroup.mackeyTransversal` is a transversal: it picks a representative of every coset. -/
@[simp]
theorem mk_mackeyTransversal (q : G ⧸ U) :
    (QuotientGroup.mk (mackeyTransversal U V r hr q) : G ⧸ U) = q := by
  obtain ⟨p, rfl⟩ := (mackeyQuotientEquiv U V r hr).surjective q
  rw [mackeyTransversal_mackeyQuotientEquiv, mackeyQuotientEquiv_apply, mackeyCoset_out]

/-- **The transversal word of the adapted transversal.** At an element `k` of `V` and the coset
indexed by `(D, w)`, the transversal word of `Subgroup.mackeyTransversal` is the conjugate by
`r D` of the transversal word of the Mackey subgroup `V ⊓ (r D) U (r D)⁻¹` in `V`, taken at the
canonical transversal `Quotient.out`. -/
theorem lWord_mackeyTransversal (D : DoubleCoset.Quotient (V : Set G) (U : Set G))
    (w : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) (k : V) :
    lWord U (mackeyTransversal U V r hr) (mackeyQuotientEquiv U V r hr ⟨D, w⟩) k =
      (r D)⁻¹ * ((lWord ((mackeySubgroup (r D) U V).subgroupOf V) Quotient.out w k : V) : G) *
        r D := by
  have hk : ((k : G))⁻¹ • mackeyQuotientEquiv U V r hr ⟨D, w⟩ =
      mackeyQuotientEquiv U V r hr ⟨D, k⁻¹ • w⟩ := by
    rw [← smul_mackeyQuotientEquiv, Subgroup.coe_inv]
  rw [lWord_def, lWord_def, hk, mackeyTransversal_mackeyQuotientEquiv,
    mackeyTransversal_mackeyQuotientEquiv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

section Topological

variable [TopologicalSpace G]

/-- For an open subgroup `U` of a topological group, every Mackey subgroup `V ⊓ sUs⁻¹` is open in
`V`. -/
theorem isOpen_mackeySubgroup_subgroupOf [ContinuousMul G] (hU : IsOpen (U : Set G)) (s : G) :
    IsOpen (((mackeySubgroup s U V).subgroupOf V : Subgroup V) : Set V) := by
  have h : (((mackeySubgroup s U V).subgroupOf V : Subgroup V) : Set V) =
      (fun x : V => s⁻¹ * (x : G) * s) ⁻¹' (U : Set G) := by
    ext x
    simp [Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff]
  rw [h]
  exact hU.preimage (by fun_prop)

/-- The conjugation `TauCeti.mackeyToH s U V : V ⊓ sUs⁻¹ → U`, `y ↦ s⁻¹ y s`, as a continuous
homomorphism. -/
def continuousMackeyToH [ContinuousMul G] (s : G) :
    ((mackeySubgroup s U V).subgroupOf V) →ₜ* U where
  toMonoidHom := mackeyToH s U V
  continuous_toFun := continuous_induced_rng.2 <| by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Function.comp_def,
      coe_mackeyToH_apply]
    fun_prop

/-- `Subgroup.continuousMackeyToH` evaluates as `TauCeti.mackeyToH`. -/
@[simp]
theorem continuousMackeyToH_apply [ContinuousMul G] (s : G)
    (y : (mackeySubgroup s U V).subgroupOf V) :
    continuousMackeyToH U V s y = mackeyToH s U V y :=
  (rfl)

/-- The homomorphism underlying `Subgroup.continuousMackeyToH` is `TauCeti.mackeyToH`. -/
@[simp]
theorem coe_continuousMackeyToH [ContinuousMul G] (s : G) :
    (continuousMackeyToH U V s : (mackeySubgroup s U V).subgroupOf V →* U) = mackeyToH s U V :=
  (rfl)

end Topological

end Subgroup

namespace TauCeti

namespace ContCohomology

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (U V : Subgroup G)

/-- Conjugation by `s` and the action of `s` on the coefficients form a compatible pair from `U`
to the Mackey subgroup `V ⊓ sUs⁻¹`. -/
theorem smul_mackeyToH_smul (s : G) (y : (mackeySubgroup s U V).subgroupOf V) (m : M) :
    DistribSMul.toAddMonoidHom M s (mackeyToH s U V y • m) =
      y • DistribSMul.toAddMonoidHom M s m := by
  rw [DistribSMul.toAddMonoidHom_apply, DistribSMul.toAddMonoidHom_apply,
    Subgroup.smul_def, coe_mackeyToH_apply, Subgroup.smul_def, Subgroup.smul_def, smul_smul,
    smul_smul]
  group

/-- `TauCeti.ContCohomology.smul_mackeyToH_smul` for the continuous conjugation
`Subgroup.continuousMackeyToH`, the form taken by the compatible-pair maps in positive degrees. -/
theorem smul_continuousMackeyToH_smul [TopologicalSpace G] [ContinuousMul G] (s : G)
    (y : (mackeySubgroup s U V).subgroupOf V) (m : M) :
    DistribSMul.toAddMonoidHom M s (U.continuousMackeyToH V s y • m) =
      y • DistribSMul.toAddMonoidHom M s m := by
  rw [Subgroup.continuousMackeyToH_apply]
  exact smul_mackeyToH_smul G M U V s y m

/-- If a sum over the double cosets `V \ G / U` of values at representatives does not depend on
the choice of representatives, then neither does each value: comparing the canonical choice with
the ones that replace the representative of a single double coset by `s`, resp. `s'`, leaves only
the terms at `s` and `s'`. -/
private theorem eq_of_sum_rep_eq {A : Type*} [AddCommGroup A]
    [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))] (T : G → A)
    (hT : ∀ r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G,
      (∀ D, DoubleCoset.mk V U (r D) = D) →
        ∑ D, T (r D) = ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G), T D.out)
    {s s' : G} (h : DoubleCoset.mk V U s = DoubleCoset.mk V U s') : T s = T s' := by
  classical
  have key (t : G) (ht : DoubleCoset.mk V U t = DoubleCoset.mk V U s) :
      T t + ∑ D ∈ {DoubleCoset.mk V U s}ᶜ, T (Quotient.out D) =
        ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G), T D.out := by
    have hr (D : DoubleCoset.Quotient (V : Set G) (U : Set G)) :
        DoubleCoset.mk V U (Function.update
          (fun D' : DoubleCoset.Quotient (V : Set G) (U : Set G) => D'.out)
          (DoubleCoset.mk V U s) t D) = D := by
      rcases eq_or_ne D (DoubleCoset.mk V U s) with rfl | hD
      · rw [Function.update_self, ht]
      · rw [Function.update_of_ne hD]
        exact DoubleCoset.out_eq' D
    rw [← hT _ hr, Fintype.sum_eq_add_sum_compl (DoubleCoset.mk V U s), Function.update_self]
    refine congrArg (T t + ·) (Finset.sum_congr rfl fun D hD => ?_)
    rw [Function.update_of_ne fun hD' => Finset.mem_compl.mp hD (Finset.mem_singleton.mpr hD')]
  exact add_right_cancel ((key s rfl).trans (key s' h.symm).symm)

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)

/-! ### Degree zero -/

/-- **The summand of the degree-zero Mackey formula** attached to `s`:
`cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res`, sending a `U`-invariant `m` to the norm of `s • m` from the
Mackey subgroup up to `V`. -/
noncomputable def explicitMackeyTerm0 (s : G) : H0 U M →+ H0 V M :=
  (explicitCor0 V M ((mackeySubgroup s U V).subgroupOf V)).comp
    (explicitMap0 U M (mackeyToH s U V) (DistribSMul.toAddMonoidHom M s)
      (smul_mackeyToH_smul G M U V s))

/-- The degree-zero Mackey summand is the norm, over the canonical transversal of the Mackey
subgroup in `V`, of the translate `s • m`. -/
@[simp]
theorem coe_explicitMackeyTerm0 (s : G) (m : H0 U M) :
    (explicitMackeyTerm0 G M U V s m : M) =
      ∑ w : V ⧸ (mackeySubgroup s U V).subgroupOf V, ((w.out : V) : G) • s • (m : M) := by
  simp only [explicitMackeyTerm0, AddMonoidHom.comp_apply, coe_explicitCor0, coe_explicitMap0,
    DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def]

include hr in
/-- **The Mackey double-coset formula in degree zero** (NSW (1.5.6)): restricting to `V` the
corestriction of a `U`-invariant is the sum, over the double cosets `V \ G / U`, of the
corestrictions from the Mackey subgroups of its conjugates, for any choice `r` of representatives
of the double cosets. -/
theorem explicitCor0_mackey (m : H0 U M) :
    explicitRes0 G M V (explicitCor0 G M U m) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
      ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G), explicitMackeyTerm0 G M U V (r D) m := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  -- Instance search does not find the fibrewise instances as a family.
  let _ : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) := fun _ => inferInstance
  apply Subtype.ext
  rw [coe_explicitRes0, explicitCor0_eq_transversal G M U (U.mackeyTransversal V r hr)
      (U.mk_mackeyTransversal V r hr), coe_explicitCor0Transversal, AddSubgroup.val_finsetSum,
    sum_mackeyQuotientEquiv U V r hr]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [coe_explicitMackeyTerm0]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Subgroup.mackeyTransversal_mackeyQuotientEquiv, mul_smul]

/-- **The degree-zero Mackey summand depends only on the double coset** `VsU` of `s`. -/
theorem explicitMackeyTerm0_eq_of_mk_eq {s s' : G}
    (h : DoubleCoset.mk V U s = DoubleCoset.mk V U s') :
    explicitMackeyTerm0 G M U V s = explicitMackeyTerm0 G M U V s' := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  refine AddMonoidHom.ext fun m => eq_of_sum_rep_eq G U V
    (fun s => explicitMackeyTerm0 G M U V s m) (fun r hr => ?_) h
  rw [← explicitCor0_mackey G M U V r hr m,
    ← explicitCor0_mackey G M U V Quotient.out DoubleCoset.out_eq' m]

/-! ### Degree one -/

section DegreeOneCochain

/-- **The Mackey formula for the degree-one corestriction cochain.** At the adapted transversal
`Subgroup.mackeyTransversal`, the restriction to `V` of the corestriction of a `1`-cochain `f` on
`U` is, on the nose, the sum over the double cosets `V \ G / U` of the corestrictions, from the
Mackey subgroups to `V` at the canonical transversal, of the conjugates
`y ↦ s • f (s⁻¹ y s)` of `f`. -/
theorem cochainsCor1_mackeyTransversal (f : U → M) (k : V) :
    cochainsCor1 G M U (U.mackeyTransversal V r hr) (U.mk_mackeyTransversal V r hr) f k =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
      ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
        cochainsCor1 V M ((mackeySubgroup (r D) U V).subgroupOf V) Quotient.out
          Quotient.out_eq
          (cochainsMap1 (mackeyToH (r D) U V) (DistribSMul.toAddMonoidHom M (r D)) f) k := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  -- Instance search does not find the fibrewise instances as a family.
  let _ : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) := fun _ => inferInstance
  rw [cochainsCor1_apply, sum_mackeyQuotientEquiv U V r hr]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [cochainsCor1_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cochainsMap1_apply, DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def, ← mul_smul]
  refine congrArg₂ (· • ·) (U.mackeyTransversal_mackeyQuotientEquiv V r hr ⟨D, w⟩)
    (congrArg f (Subtype.ext ?_))
  rw [coe_mackeyToH_apply]
  exact U.lWord_mackeyTransversal V r hr D w k

end DegreeOneCochain

section DegreeOne

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G))

/-- **The summand of the degree-one Mackey formula** attached to `s`:
`cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res : H¹(U, M) → H¹(V, M)`. -/
noncomputable def explicitMackeyTerm1 (s : G) : H1 U M →+ H1 V M :=
  (explicitCor1 V M ((mackeySubgroup s U V).subgroupOf V)
      (U.isOpen_mackeySubgroup_subgroupOf V hU s)).comp
    (explicitMap1 U M ((mackeySubgroup s U V).subgroupOf V) M (U.continuousMackeyToH V s)
      (DistribSMul.toAddMonoidHom M s) ((continuous_const_smul s).congr fun _ => rfl)
      (smul_continuousMackeyToH_smul G M U V s))

/-- The degree-one Mackey summand sends the class of a continuous `1`-cocycle to the class of the
corestriction, at the canonical transversal, of its conjugate. -/
@[simp]
theorem explicitMackeyTerm1_mk (s : G) (f : Z1 U M) :
    explicitMackeyTerm1 G M U V hU s (f : H1 U M) =
      (cocyclesCor1 V M ((mackeySubgroup s U V).subgroupOf V) Quotient.out Quotient.out_eq
        (U.isOpen_mackeySubgroup_subgroupOf V hU s)
        (cocyclesMap1 U M ((mackeySubgroup s U V).subgroupOf V) M (U.continuousMackeyToH V s)
          (DistribSMul.toAddMonoidHom M s) ((continuous_const_smul s).congr fun _ => rfl)
          (smul_continuousMackeyToH_smul G M U V s) f) : H1 V M) := by
  rw [explicitMackeyTerm1, AddMonoidHom.comp_apply, explicitMap1_mk, explicitCor1_mk]

include hr in
/-- **The Mackey double-coset formula in degree one** (NSW (1.5.6)): for an open subgroup `U` of
finite index and any subgroup `V`,
`res^G_V ∘ cor^G_U = ∑_{VsU} cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res` on `H¹(U, M)`, for any choice `r` of
representatives `s = r D` of the double cosets. -/
theorem explicitCor1_mackey (x : H1 U M) :
    explicitRes1 G M V (explicitCor1 G M U hU x) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
      ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
        explicitMackeyTerm1 G M U V hU (r D) x := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  induction x using QuotientAddGroup.induction_on with
  | H f =>
    rw [explicitCor1_eq_transversal G M U (U.mackeyTransversal V r hr)
        (U.mk_mackeyTransversal V r hr) hU,
      explicitCor1Transversal_mk, explicitRes1_mk]
    simp only [explicitMackeyTerm1_mk]
    rw [← QuotientAddGroup.mk_sum]
    congr 1
    refine Subtype.ext (funext fun k => ?_)
    rw [AddSubgroup.val_finsetSum, Finset.sum_apply, cocyclesMap1_apply, AddMonoidHom.id_apply,
      coe_cocyclesCor1]
    refine (cochainsCor1_mackeyTransversal G M U V r hr f k).trans
      (Finset.sum_congr rfl fun D _ => ?_)
    rw [coe_cocyclesCor1, cocyclesMap1_coe, Subgroup.coe_continuousMackeyToH]

/-- **The degree-one Mackey summand depends only on the double coset** `VsU` of `s`. -/
theorem explicitMackeyTerm1_eq_of_mk_eq {s s' : G}
    (h : DoubleCoset.mk V U s = DoubleCoset.mk V U s') :
    explicitMackeyTerm1 G M U V hU s = explicitMackeyTerm1 G M U V hU s' := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  refine AddMonoidHom.ext fun x => eq_of_sum_rep_eq G U V
    (fun s => explicitMackeyTerm1 G M U V hU s x) (fun r hr => ?_) h
  rw [← explicitCor1_mackey G M U V r hr hU x,
    ← explicitCor1_mackey G M U V Quotient.out DoubleCoset.out_eq' hU x]

end DegreeOne

/-! ### Degree two -/

section DegreeTwoCochain

/-- **The Mackey formula for the degree-two corestriction cochain**, the degree-two counterpart of
`TauCeti.ContCohomology.cochainsCor1_mackeyTransversal`: at the adapted transversal the identity
holds on the nose. -/
theorem cochainsCor2_mackeyTransversal (f : U × U → M) (k l : V) :
    cochainsCor2 G M U (U.mackeyTransversal V r hr) (U.mk_mackeyTransversal V r hr) f (k, l) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
      ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
        cochainsCor2 V M ((mackeySubgroup (r D) U V).subgroupOf V) Quotient.out
          Quotient.out_eq
          (cochainsMap2 (mackeyToH (r D) U V) (DistribSMul.toAddMonoidHom M (r D)) f)
          (k, l) := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  -- Instance search does not find the fibrewise instances as a family.
  let _ : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) := fun _ => inferInstance
  rw [cochainsCor2_apply, sum_mackeyQuotientEquiv U V r hr]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [cochainsCor2_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cochainsMap2_apply, DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def, ← mul_smul]
  have hk : ((k : G))⁻¹ • mackeyQuotientEquiv U V r hr ⟨D, w⟩ =
      mackeyQuotientEquiv U V r hr ⟨D, k⁻¹ • w⟩ := by
    rw [← smul_mackeyQuotientEquiv, Subgroup.coe_inv]
  refine congrArg₂ (· • ·) (U.mackeyTransversal_mackeyQuotientEquiv V r hr ⟨D, w⟩)
    (congrArg f (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
  · rw [coe_mackeyToH_apply]
    exact U.lWord_mackeyTransversal V r hr D w k
  · rw [Subtype.coe_mk, hk, coe_mackeyToH_apply]
    exact U.lWord_mackeyTransversal V r hr D (k⁻¹ • w) l

end DegreeTwoCochain

section DegreeTwo

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G))

/-- **The summand of the degree-two Mackey formula** attached to `s`:
`cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res : H²(U, M) → H²(V, M)`. -/
noncomputable def explicitMackeyTerm2 (s : G) : H2 U M →+ H2 V M :=
  (explicitCor2 V M ((mackeySubgroup s U V).subgroupOf V)
      (U.isOpen_mackeySubgroup_subgroupOf V hU s)).comp
    (explicitMap2 U M ((mackeySubgroup s U V).subgroupOf V) M (U.continuousMackeyToH V s)
      (DistribSMul.toAddMonoidHom M s) ((continuous_const_smul s).congr fun _ => rfl)
      (smul_continuousMackeyToH_smul G M U V s))

/-- The degree-two Mackey summand sends the class of a continuous `2`-cocycle to the class of the
corestriction, at the canonical transversal, of its conjugate. -/
@[simp]
theorem explicitMackeyTerm2_mk (s : G) (f : Z2 U M) :
    explicitMackeyTerm2 G M U V hU s (f : H2 U M) =
      (cocyclesCor2 V M ((mackeySubgroup s U V).subgroupOf V) Quotient.out Quotient.out_eq
        (U.isOpen_mackeySubgroup_subgroupOf V hU s)
        (cocyclesMap2 U M ((mackeySubgroup s U V).subgroupOf V) M (U.continuousMackeyToH V s)
          (DistribSMul.toAddMonoidHom M s) ((continuous_const_smul s).congr fun _ => rfl)
          (smul_continuousMackeyToH_smul G M U V s) f) : H2 V M) := by
  rw [explicitMackeyTerm2, AddMonoidHom.comp_apply, explicitMap2_mk, explicitCor2_mk]

include hr in
/-- **The Mackey double-coset formula in degree two** (NSW (1.5.6)): for an open subgroup `U` of
finite index and any subgroup `V`,
`res^G_V ∘ cor^G_U = ∑_{VsU} cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res` on `H²(U, M)`, for any choice `r` of
representatives `s = r D` of the double cosets. -/
theorem explicitCor2_mackey (x : H2 U M) :
    explicitRes2 G M V (explicitCor2 G M U hU x) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
      ∑ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
        explicitMackeyTerm2 G M U V hU (r D) x := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  induction x using QuotientAddGroup.induction_on with
  | H f =>
    rw [explicitCor2_eq_transversal G M U (U.mackeyTransversal V r hr)
        (U.mk_mackeyTransversal V r hr) hU,
      explicitCor2Transversal_mk, explicitRes2_mk]
    simp only [explicitMackeyTerm2_mk]
    rw [← QuotientAddGroup.mk_sum]
    congr 1
    refine Subtype.ext (funext fun q => ?_)
    obtain ⟨k, l⟩ := q
    rw [AddSubgroup.val_finsetSum, Finset.sum_apply, cocyclesMap2_apply, AddMonoidHom.id_apply,
      coe_cocyclesCor2]
    refine (cochainsCor2_mackeyTransversal G M U V r hr f k l).trans
      (Finset.sum_congr rfl fun D _ => ?_)
    rw [coe_cocyclesCor2, cocyclesMap2_coe, Subgroup.coe_continuousMackeyToH]

/-- **The degree-two Mackey summand depends only on the double coset** `VsU` of `s`. -/
theorem explicitMackeyTerm2_eq_of_mk_eq {s s' : G}
    (h : DoubleCoset.mk V U s = DoubleCoset.mk V U s') :
    explicitMackeyTerm2 G M U V hU s = explicitMackeyTerm2 G M U V hU s' := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  refine AddMonoidHom.ext fun x => eq_of_sum_rep_eq G U V
    (fun s => explicitMackeyTerm2 G M U V hU s x) (fun r hr => ?_) h
  rw [← explicitCor2_mackey G M U V r hr hU x,
    ← explicitCor2_mackey G M U V Quotient.out DoubleCoset.out_eq' hU x]

end DegreeTwo

end ContCohomology

end TauCeti
