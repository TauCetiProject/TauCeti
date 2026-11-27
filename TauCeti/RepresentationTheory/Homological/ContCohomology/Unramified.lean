/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Unramified local conditions and coefficient injections

For a subgroup `I` of a group `G`, the unramified condition on `H¹(G, M)` is the kernel of
restriction to `H¹(I, M)`. When `I` acts trivially on the coefficients, a cocycle has
unramified class exactly when it vanishes on `I`. Consequently an injective coefficient map
detects unramified classes: the condition on the source is the inverse image of the condition
on the target. This is the cartesian property of the unramified local condition.

The statements use arbitrary subgroups and topological coefficient groups, so they apply to
inertia and to both finite and compact coefficients. Only the target is required to have
trivial inertia action in the coefficient-injection theorem: equivariance and injectivity
then imply the same property for the source. No injectivity on the full `H¹(G, -)` is claimed.

## References

* B. Mazur and K. Rubin, *Kolyvagin systems*, Mem. Amer. Math. Soc. 168 (2004), no. 799,
  Definition 1.1.4 and Lemma 1.1.9.
-/

public section

namespace TauCeti.ContCohomology

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- If `I` acts trivially, a cocycle has unramified class if and only if it vanishes on `I`.
In particular, this condition is independent of the choice of cocycle representative. -/
-- Not a simp lemma: `explicitRes1_mk` already simplifies restriction of a cocycle class.
theorem _root_.Subgroup.explicitRes1_mk_eq_zero_iff_of_smul_eq_self (I : Subgroup G)
    (hI : ∀ (g : I) (m : M), (g : G) • m = m) (z : Z1 G M) :
    explicitRes1 G M I (z : H1 G M) = 0 ↔ ∀ g : I, (z : G → M) (g : G) = 0 := by
  rw [explicitRes1_mk, H1pi_eq_zero_iff, B1_eq_bot_of_smul_eq_self hI]
  simp only [AddSubgroup.mem_bot, funext_iff, cocyclesMap1_apply,
    ContinuousMonoidHom.subgroupSubtype_apply, AddMonoidHom.id_apply, Pi.zero_apply]

variable {N : Type w} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]

/-- An injective coefficient map into a module with trivial `I`-action detects unramified
classes. This is the elementwise cartesian property of the unramified condition. -/
@[simp]
theorem _root_.Subgroup.explicitRes1_explicitCoeff1_eq_zero_iff (I : Subgroup G)
    (f : M →+[G] N) (hf : Continuous f) (hinj : Function.Injective f)
    (hI : ∀ (g : I) (n : N), (g : G) • n = n) (x : H1 G M) :
    explicitRes1 G N I (explicitCoeff1 G M f hf x) = 0 ↔
      explicitRes1 G M I x = 0 := by
  have hIM (g : I) (m : M) : (g : G) • m = m :=
    hinj ((f.map_smul (g : G) m).trans (hI g (f m)))
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [explicitCoeff1_mk, I.explicitRes1_mk_eq_zero_iff_of_smul_eq_self hI,
      I.explicitRes1_mk_eq_zero_iff_of_smul_eq_self hIM]
    apply forall_congr'
    intro g
    -- Apply the evaluation lemma as a term: rewriting cannot align the two coercions of
    -- `f` to an additive map inside the equivariance proof of `explicitCoeff1_mk`.
    exact (congrArg (fun n : N => n = 0)
      (cocyclesMap1_apply G M G N (ContinuousMonoidHom.id G) f.toAddMonoidHom hf
        (fun g m => f.map_smul g m) z (g : G))).to_iff.trans (hinj.eq_iff' (map_zero f))

/-- The unramified local condition is cartesian under injective coefficient maps between
unramified modules: it is the inverse image of the target condition. -/
theorem _root_.Subgroup.comap_ker_explicitRes1_of_injective_of_smul_eq_self (I : Subgroup G)
    (f : M →+[G] N) (hf : Continuous f) (hinj : Function.Injective f)
    (hI : ∀ (g : I) (n : N), (g : G) • n = n) :
    ((explicitRes1 G N I).ker).comap (explicitCoeff1 G M f hf) =
      (explicitRes1 G M I).ker := by
  ext x
  exact I.explicitRes1_explicitCoeff1_eq_zero_iff f hf hinj hI x

end TauCeti.ContCohomology
