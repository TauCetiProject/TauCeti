/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation

/-!
# The invariant term in the five-term sequence

Let `N` be a normal subgroup of a topological group `G`, and let `M` be a continuous
`G`-module. Conjugation by `G`, together with the action on `M`, acts on the explicit group
`H¹(N, M)`. This file defines the subgroup fixed by that action and proves that restriction

```text
H¹(G, M) → H¹(N, M)
```

lands in it. Thus restriction acquires the codomain needed for the third arrow of the
inflation-restriction-transgression five-term sequence.

Although the invariant subgroup is defined by quantifying over `G`, it is the `G ⧸ N`-invariant
subgroup: elements of `N` act trivially on `H¹(N, M)`. For a cocycle `c` on `G`, invariance of
its restriction is witnessed before quotienting by the identity

```text
g • c(g⁻¹ng) - c(n) = n • c(g) - c(g).
```

The right-hand side is the coboundary of `c(g)`. This is the low-degree cochain calculation
underlying the conjugation-invariance of restriction.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §5.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

/-- The subgroup of `H¹(N, M)` fixed by conjugation by `G` and the corresponding action on
coefficients. Since elements of `N` act trivially, this is equivalently the invariant subgroup
for the induced `G ⧸ N`-action. -/
def H1ConjInvariants : AddSubgroup (H1 N M) where
  carrier := {x | ∀ g : G, explicitConj1 N g x = x}
  zero_mem' g := map_zero _
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  neg_mem' {x} hx g := by rw [map_neg, hx g]

/-- A class belongs to `H1ConjInvariants` exactly when every conjugation map fixes it. -/
@[simp]
theorem mem_H1ConjInvariants_iff {x : H1 N M} :
    x ∈ H1ConjInvariants G M N ↔ ∀ g : G, explicitConj1 N g x = x :=
  Iff.rfl

variable {G M N} in
/-- A conjugation-invariant class in `H¹(N, M)` is represented by cocycles whose conjugates are
cohomologous to them: for each `g`, conjugating by `g` changes a representative by a
coboundary. -/
theorem exists_smul_conj_sub_eq_d0_of_mem_H1ConjInvariants {c : Z1 N M}
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) (g : G) :
    ∃ m : M, ∀ n : N,
      g • (c : N → M) (N.inverseConjugationHom g n) - (c : N → M) n = d0 N M m n := by
  have h := (mem_H1ConjInvariants_iff G M N).1 hc g
  rw [explicitConj1_apply_eq_smul, smul_mk, H1pi_eq_iff, mem_B1_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun n => ?_⟩
  rw [d0_apply, hm n, Pi.sub_apply, cocyclesMap1_apply, DistribSMul.toAddMonoidHom_apply]

omit [IsTopologicalGroup G] [ContinuousSMul G M] [N.Normal] in
/-- Conjugating the restriction of a continuous `1`-cocycle changes it by the coboundary of its
value at the conjugating element. This is the representative-level identity behind
`explicitRes1_mem_conjInvariants`. -/
theorem smul_inverseConjugation_apply_sub_eq_d0 (c : Z1 G M) (g : G) (n : N) :
    g • (c : G → M) (g⁻¹ * (n : G) * g) - (c : G → M) (n : G) =
      d0 N M ((c : G → M) g) n := by
  have hc₁ : (c : G → M) (g⁻¹ * (n : G) * g) =
      g⁻¹ • (c : G → M) ((n : G) * g) + (c : G → M) g⁻¹ := by
    simpa only [mul_assoc] using (mem_Z1_iff.1 c.2).2 g⁻¹ ((n : G) * g)
  have hc₂ := (mem_Z1_iff.1 c.2).2 (n : G) g
  have hcinv := map_inv_of_mem_Z1 c.2 g
  rw [hc₁, hc₂, smul_add, smul_smul, hcinv]
  simp only [mul_inv_cancel, one_smul, d0_apply, Subgroup.smul_def]
  abel

/-- Restriction of a first cohomology class to a normal subgroup is invariant under conjugation.

On a cocycle representative `c`, conjugation changes the restricted cocycle by the coboundary
of `c g`. -/
theorem explicitRes1_mem_conjInvariants (x : H1 G M) :
    explicitRes1 G M N x ∈ H1ConjInvariants G M N := by
  rw [mem_H1ConjInvariants_iff]
  intro g
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitRes1_mk, explicitConj1_apply_eq_smul, smul_mk, H1pi_eq_iff]
      refine mem_B1_iff.2 ⟨(c : G → M) g, fun n => ?_⟩
      simp only [Pi.sub_apply, cocyclesMap1_apply, ContinuousMonoidHom.subgroupSubtype_apply,
        AddMonoidHom.id_apply, DistribSMul.toAddMonoidHom_apply,
        Subgroup.inverseConjugationHom_apply]
      simpa only [d0_apply] using
        (smul_inverseConjugation_apply_sub_eq_d0 G M N c g n).symm

/-- Restriction in degree one, with codomain restricted to the conjugation-invariant subgroup.
This is the third arrow in the inflation-restriction-transgression five-term sequence. -/
noncomputable def explicitResConj1 : H1 G M →+ H1ConjInvariants G M N :=
  (explicitRes1 G M N).codRestrict (H1ConjInvariants G M N)
    (explicitRes1_mem_conjInvariants G M N)

/-- The invariant-valued restriction map has the usual restriction map as its underlying value. -/
@[simp]
theorem coe_explicitResConj1 (x : H1 G M) :
    (explicitResConj1 G M N x : H1 N M) = explicitRes1 G M N x :=
  by simp only [explicitResConj1, AddMonoidHom.codRestrict_apply]

/-- The inflation-restriction sequence remains exact when restriction is given its natural
conjugation-invariant codomain. -/
theorem explicitInfResConj_exact
    [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] :
    (explicitInfl1 G M N).range = (explicitResConj1 G M N).ker := by
  rw [explicitInfRes_exact]
  ext x
  simp only [AddMonoidHom.mem_ker]
  constructor
  · intro hx
    apply Subtype.ext
    simpa only [coe_explicitResConj1, ZeroMemClass.coe_zero] using hx
  · intro hx
    have := congrArg Subtype.val hx
    simpa only [coe_explicitResConj1, ZeroMemClass.coe_zero] using this

end TauCeti.ContCohomology
